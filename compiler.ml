#use "tp_sa.ml";;

let file_to_string input_file =
  let in_channel = open_in input_file in
  let rec run () =
    try 
      let ch = input_char in_channel in ch :: (run ())
    with End_of_file ->
      ( close_in in_channel;
	[] )
  in string_of_list (run ());;

let string_to_file output_file out_string =
  let out_channel = open_out output_file in
  ( output_string out_channel out_string;
    close_out out_channel );;

module type CODE_GENERATION =
  sig
    val compile_scheme_string : string -> string -> unit
    val compile_scheme_file : string -> string -> unit
  end;;

module Code_Generation : CODE_GENERATION= struct

  (* areas that raise this exception are NOT for the
   * final project! please leave these unimplemented,
   * as this will require major additions to your
   * compilers
   *)
  exception X_not_yet_supported;;

  let word_size = 8;;
  let label_start_of_constants_table = "L_constants";;
  let comment_length = 20;;

  let list_and_last =
    let rec run a = function
      | [] -> ([], a)
      | b :: s ->
         let (s, last) = run b s in
         (a :: s, last)
    in function
    | [] -> None
    | a :: s -> Some (run a s);;

  let split_to_sublists n = 
    let rec run = function
      | ([], _, f) -> [f []]
      | (s, 0, f) -> (f []) :: (run (s, n, (fun s -> s)))
      | (a :: s, i, f) ->
         (run (s, i - 1, (fun s -> f (a :: s))))
    in function
    | [] -> []
    | s -> run (s, n, (fun s -> s));;

    let remove_duplicates consts = 
      List.fold_left (fun cur_list const ->
      if (List.mem const cur_list) then cur_list
          else cur_list @ [const]) [] consts;;
  let collect_constants = 
    let rec run = function
      |ScmConst'(sexpr)->(match sexpr with
      (* Troubles with void and nil *)
        |ScmVoid->[]
        |ScmNil->[]
        |ScmBoolean(flag)->[]
        |_->[sexpr])
      |ScmVarGet' _-> []
      |ScmBox' _-> []
      |ScmBoxGet' _-> []
      |ScmIf'(test,dit,diff)->(run test)@(run dit)@(run diff)
      |ScmSeq'(sexprs)->runs sexprs
      |ScmOr'(sexprs)->runs sexprs
      |ScmVarSet'(_,vl)->run vl
      |ScmVarDef'(_,vl)->run vl
      |ScmBoxSet'(_,vl)->run vl
      |ScmLambda'(_,_,expr)->run expr
      |ScmApplic'(proc,args,_)->(run proc)@(runs args)
    and runs exprs'= List.fold_left (fun constbl expr -> constbl @ (run expr)) [] exprs'
      in runs;;

  (* let add_scm_nil lst = 
    let newlst = [ScmNil] @ lst
    in newlst;; *)

  let add_sub_constants =
    let rec run sexpr = match sexpr with
      | ScmVoid ->[]
      | ScmNil ->[]
      | ScmBoolean _ ->[]
      | ScmChar _ | ScmString _ | ScmNumber _ ->[sexpr]
      | ScmSymbol sym -> [ScmString(sym);ScmSymbol sym]
      | ScmPair (car, cdr) -> (run car) @ (run cdr) @ [sexpr]
      | ScmVector sexprs ->(runs sexprs)@[sexpr]
    and runs sexprs =
      List.fold_left (fun full sexpr -> full @ (run sexpr)) [] sexprs
    in fun exprs' ->
       [ScmVoid; ScmNil; ScmBoolean false; ScmBoolean true; ScmChar '\000'] @ (runs exprs');;

  type initialized_data =
    | RTTI of string
    | Byte of int
    | ASCII of string
    | Quad of int
    | QuadFloat of float
    | ConstPtr of int;;

  let search_constant_address = 
    let rec run c = function
    | [] -> raise (X_this_should_not_happen
                    (Printf.sprintf
                      "The %s was not found in the constants table" (string_of_sexpr c)))
    | (c', loc ,repr) :: _ when c = c' -> loc
    | _ :: table -> run c table
  in run;;
  let const_repr sexpr loc table = match sexpr with
    | ScmVoid -> ([RTTI "T_void"], 1)
    | ScmNil -> ([RTTI "T_nil"], 1)
    | ScmBoolean false ->
       ([RTTI "T_boolean_false"], 1)
    | ScmBoolean true ->
       ([RTTI "T_boolean_true"], 1)
    | ScmChar ch ->
       ([RTTI "T_char"; Byte (int_of_char ch)], 2)
    | ScmString str ->
       let count = String.length str in
       ([RTTI "T_string"; Quad count; ASCII str],
        1 + word_size + count)
    | ScmSymbol sym ->
       let addr = search_constant_address (ScmString sym) table in
       ([RTTI "T_symbol"; ConstPtr addr], 1 + word_size)
    | ScmNumber (ScmRational (numerator, denominator)) ->
       ([RTTI "T_rational"; Quad numerator; Quad denominator],
        1 + 2 * word_size)
    | ScmNumber (ScmReal x) ->
       ([RTTI "T_real"; QuadFloat x], 1 + word_size)
    | ScmVector s ->
       let addrs =
         List.map
           (fun si -> ConstPtr (search_constant_address si table)) s in
       let count = List.length s in
       ((RTTI "T_vector") :: (Quad count) :: addrs,
        1 + (count + 1) * word_size)
    | ScmPair (car, cdr) ->
       let (addr_car, addr_cdr) =
         (search_constant_address car table,
          search_constant_address cdr table) in
       ([RTTI "T_pair"; ConstPtr addr_car; ConstPtr addr_cdr],
        1 + 2 * word_size);;

  let make_constants_table =
    let rec run table loc = function
      | [] -> table
      | sexpr :: sexprs ->
         let (repr, len) = const_repr sexpr loc table in
         run (table @ [(sexpr, loc, repr)]) (loc + len) sexprs
    in
    fun exprs' ->
    run [] 0
        (remove_duplicates
          (add_sub_constants
            (remove_duplicates
             (collect_constants exprs')
              )));;    

  let asm_comment_of_sexpr sexpr =
    let str = string_of_sexpr sexpr in
    let str =
      if (String.length str) <= comment_length
      then str
      else (String.sub str 0 comment_length) ^ "..." in
    "; " ^ str;;

  let asm_of_representation sexpr =
    let str = asm_comment_of_sexpr sexpr in
    let run = function
      | [RTTI str] -> Printf.sprintf "\tdb %s" str
      | [RTTI "T_char"; Byte byte] ->
         Printf.sprintf "\tdb T_char, 0x%02X\t%s" byte str
      | [RTTI "T_string"; Quad length; ASCII const_str] ->
         Printf.sprintf "\tdb T_string\t%s\n\tdq %d%s"
           str length
           (let s = list_of_string const_str in
            let s = List.map
                      (fun ch -> Printf.sprintf "0x%02X" (int_of_char ch))
                      s in
            let s = split_to_sublists 8 s in
            let s = List.map (fun si -> "\n\tdb " ^ (String.concat ", " si)) s in
            String.concat "" s)
      | [RTTI "T_symbol"; ConstPtr addr] ->
         Printf.sprintf "\tdb T_symbol\t%s\n\tdq %s + %d"
           str label_start_of_constants_table addr
      | [RTTI "T_rational"; Quad numerator; Quad denominator] ->
         Printf.sprintf "\tdb T_rational\t%s\n\tdq %d, %d"
           str
           numerator denominator
      | [RTTI "T_real"; QuadFloat x] ->
         Printf.sprintf "\tdb T_real\t%s\n\tdq %f" str x
      | (RTTI "T_vector") :: (Quad length) :: addrs ->
         Printf.sprintf "\tdb T_vector\t%s\n\tdq %d%s"
           str length
           (let s = List.map
                      (function
                       | ConstPtr ptr ->
                          Printf.sprintf "%s + %d"
                            label_start_of_constants_table ptr
                       | _ -> raise
                               (X_this_should_not_happen
                                  "incorrect representation for a vector"))
                      addrs in
            let s = split_to_sublists 3 s in
            let s = List.map (fun si -> "\n\tdq " ^ (String.concat ", " si)) s in
            String.concat "" s)
      | [RTTI "T_pair"; ConstPtr car; ConstPtr cdr] ->
         Printf.sprintf "\tdb T_pair\t%s\n\tdq %s + %d, %s + %d"
           str
           label_start_of_constants_table car
           label_start_of_constants_table cdr
      | _ -> raise (X_this_should_not_happen "invalid representation!")
    in run;;

  let asm_of_constants_table =
    let rec run = function
      | [] -> ""
      | (sexpr, _, repr) :: rest ->
         (asm_of_representation sexpr repr) ^ "\n" ^ (run rest)
    in
    fun table ->
    Printf.sprintf "%s:\n%s"
      label_start_of_constants_table (run table);;

  let global_bindings_table =
    [ (* 1-10 *)
      ("null?", "L_code_ptr_is_null");
      ("pair?", "L_code_ptr_is_pair");
      ("void?", "L_code_ptr_is_void");
      ("char?", "L_code_ptr_is_char");
      ("string?", "L_code_ptr_is_string");
      ("symbol?", "L_code_ptr_is_symbol");
      ("vector?", "L_code_ptr_is_vector");
      ("procedure?", "L_code_ptr_is_closure");
      ("real?", "L_code_ptr_is_real");
      ("rational?", "L_code_ptr_is_rational");
      ("boolean?", "L_code_ptr_is_boolean");
      (* 11-20 *)
      ("number?", "L_code_ptr_is_number");
      ("collection?", "L_code_ptr_is_collection");
      ("cons", "L_code_ptr_cons");
      ("display-sexpr", "L_code_ptr_display_sexpr");
      ("write-char", "L_code_ptr_write_char");
      ("car", "L_code_ptr_car");
      ("cdr", "L_code_ptr_cdr");
      ("string-length", "L_code_ptr_string_length");
      ("vector-length", "L_code_ptr_vector_length");
      ("real->integer", "L_code_ptr_real_to_integer");
      (* 21-30*)
      ("exit", "L_code_ptr_exit");
      ("integer->real", "L_code_ptr_integer_to_real");
      ("rational->real", "L_code_ptr_rational_to_real");
      ("char->integer", "L_code_ptr_char_to_integer");
      ("integer->char", "L_code_ptr_integer_to_char");
      ("trng", "L_code_ptr_trng");
      ("zero?", "L_code_ptr_is_zero");
      ("integer?", "L_code_ptr_is_integer");
      ("__bin-apply", "L_code_ptr_bin_apply");
      ("__bin-add-rr", "L_code_ptr_raw_bin_add_rr");
      (* 31-40*)
      ("__bin-sub-rr", "L_code_ptr_raw_bin_sub_rr");
      ("__bin-mul-rr", "L_code_ptr_raw_bin_mul_rr");
      ("__bin-div-rr", "L_code_ptr_raw_bin_div_rr");
      ("__bin-add-qq", "L_code_ptr_raw_bin_add_qq");
      ("__bin-sub-qq", "L_code_ptr_raw_bin_sub_qq");
      ("__bin-mul-qq", "L_code_ptr_raw_bin_mul_qq");
      ("__bin-div-qq", "L_code_ptr_raw_bin_div_qq");
      ("error", "L_code_ptr_error");
      ("__bin-less-than-rr", "L_code_ptr_raw_less_than_rr");
      ("__bin-less-than-qq", "L_code_ptr_raw_less_than_qq");
      (* 41-50 *)
      ("__bin-equal-rr", "L_code_ptr_raw_equal_rr");
      ("__bin-equal-qq", "L_code_ptr_raw_equal_qq");
      ("quotient", "L_code_ptr_quotient");
      ("remainder", "L_code_ptr_remainder");
      ("set-car!", "L_code_ptr_set_car");
      ("set-cdr!", "L_code_ptr_set_cdr");
      ("string-ref", "L_code_ptr_string_ref");
      ("vector-ref", "L_code_ptr_vector_ref");
      ("vector-set!", "L_code_ptr_vector_set");
      ("string-set!", "L_code_ptr_string_set");
      (* 51-60 *)
      ("make-vector", "L_code_ptr_make_vector");
      ("make-string", "L_code_ptr_make_string");
      ("numerator", "L_code_ptr_numerator");
      ("denominator", "L_code_ptr_denominator");
      ("eq?", "L_code_ptr_eq")
    ];;

  let collect_free_vars =
    let rec run = function
      | ScmConst' _ -> []
      | ScmVarGet' (Var' (v, Free)) -> [v]
      | ScmVarGet' _ ->[]
      | ScmIf' (test, dit, dif) -> (run test)@(run dit)@(run dif)
      | ScmSeq' exprs' -> runs exprs'
      | ScmOr' exprs' -> runs exprs'
      | ScmVarSet' (Var' (v, Free), expr') -> [v]@(run expr')
      | ScmVarSet' (_, expr') -> run expr'
      | ScmVarDef' (Var' (v, Free), expr') -> [v]@(run expr')
      | ScmVarDef' (_, expr') -> run expr'
      | ScmBox' (Var' (v, Free)) -> [v]
      | ScmBox' _ -> []
      | ScmBoxGet' (Var' (v, Free)) -> [v]
      | ScmBoxGet' _ -> []
      | ScmBoxSet' (Var' (v, Free), expr') -> [v]@(run expr')
      | ScmBoxSet' (_, expr') -> run expr'
      | ScmLambda' (_, _, expr') -> (run expr')
      | ScmApplic' (expr', exprs', _) -> (run expr')@(runs exprs')
    and runs exprs' =
      List.fold_left
        (fun vars expr' -> vars @ (run expr'))
        []
        exprs'
    in fun exprs' ->
       let primitives =
         List.map
           (fun (scheme_name, _) -> scheme_name)
           global_bindings_table
       and free_vars_in_code = runs exprs' in
       remove_duplicates
         (primitives @ free_vars_in_code);;

  let make_free_vars_table =
    let rec run index = function
      | [] -> []
      | v :: vars ->
         let x86_label = Printf.sprintf "free_var_%d" index in
         (v, x86_label) :: (run (index + 1) vars)
    in fun exprs' -> run 0 (collect_free_vars exprs');;

  let search_free_var_table =
    let rec run v = function
      | [] -> raise (X_this_should_not_happen
                      (Printf.sprintf
                         "The variable %s was not found in the free-var table"
                         v))
      | (v', x86_label) :: _ when v = v' -> x86_label
      | _ :: table -> run v table
    in run;;

  let asm_of_global_bindings global_bindings_table free_var_table =
    String.concat "\n"
      (List.map
         (fun (scheme_name, asm_code_ptr) ->
           let free_var_label =
             search_free_var_table scheme_name free_var_table in
           (Printf.sprintf "\t; building closure for %s\n" scheme_name)
           ^ (Printf.sprintf "\tmov rdi, %s\n" free_var_label)
           ^ (Printf.sprintf "\tmov rsi, %s\n" asm_code_ptr)
           ^ "\tcall bind_primitive\n")
         global_bindings_table);;
  
  let asm_of_free_vars_table table =
    let tmp = 
      List.map
        (fun (scm_var, asm_label) ->
          Printf.sprintf "%s:\t; location of %s\n\tresq 1"
            asm_label scm_var)
        table in
    String.concat "\n" tmp;;

  let make_make_label prefix =
    let index = ref 0 in
    fun () ->
    (index := !index + 1;
     Printf.sprintf "%s_%04x" prefix !index);;

     (* IF labels *)
     let make_if_else = make_make_label ".L_if_else";;
     let make_if_end = make_make_label ".L_if_end";;
     let make_or_end = make_make_label ".L_or_end";;
     (* ScmLambdaSimple labels *)
     let make_lambda_simple_loop_env = make_make_label ".L_lambda_simple_env_loop";;
     let make_lambda_simple_loop_env_end = make_make_label ".L_lambda_simple_env_end";;
     let make_lambda_simple_loop_params = make_make_label ".L_lambda_simple_params_loop";;
     let make_lambda_simple_loop_params_end = make_make_label ".L_lambda_simple_params_end";;
     let make_lambda_simple_code = make_make_label ".L_lambda_simple_code";;
     let make_lambda_simple_end = make_make_label ".L_lambda_simple_end";;
     let make_lambda_simple_arity_ok = make_make_label ".L_lambda_simple_arity_check_ok";;
     let make_lambda_opt_arity_ok = make_make_label ".L_lambda_opt_arity_check_ok";;
     (* ScmLambdaOpt labels *)
     let make_lambda_opt_loop_env = make_make_label ".L_lambda_opt_env_loop";;
     let make_lambda_opt_loop_env_end = make_make_label ".L_lambda_opt_env_end";;
     let make_lambda_opt_loop_params = make_make_label ".L_lambda_opt_params_loop";;
     let make_lambda_opt_loop_params_list = make_make_label ".L_lambda_opt_params_list";;
     
     let make_lambda_opt_loop_params_list_loop = make_make_label ".L_lambda_opt_params_list_loop";;
     
     let make_lambda_opt_loop_params_end = make_make_label ".L_lambda_opt_params_end";;
     let make_lambda_opt_code = make_make_label ".L_lambda_opt_code";;
     let make_lambda_opt_end = make_make_label ".L_lambda_opt_end";;
     let make_lambda_opt_arity_exact = make_make_label ".L_lambda_opt_arity_check_exact";;
     let make_lambda_opt_arity_more = make_make_label ".L_lambda_opt_arity_check_more";;
     let make_lambda_opt_incorrect_arity = make_make_label ".L_lambda_opt_arity_incorrect";;
     let make_lambda_opt_exact_loop =make_make_label ".L_lambda_opt_exact_loop";;
     let make_lambda_opt_exact_loop_end =make_make_label ".L_lambda_opt_exact_loop_end";;
     let make_lambda_opt_more_loop =make_make_label ".L_lambda_opt_more_loop";;
     let make_lambda_opt_more_loop_end =make_make_label ".L_lambda_opt_more_loop_end";;
     let make_lambda_opt_more_loop_2 =make_make_label ".L_lambda_opt_more_loop_2";;
     let make_lambda_opt_more_loop_2_end =make_make_label ".L_lambda_opt_more_loop_2_end";;
     let make_lambda_opt_shift_params_loop_exact = make_make_label ".L_lambda_opt_params_loop_exact";;
     let make_lambda_opt_shift_params_loop_exact_end = make_make_label ".L_lambda_opt_params_loop_exact_end";;
     let make_lambda_opt_shift_params_loop_exact_end_zero = make_make_label ".L_lambda_opt_params_loop_exact_end_zero"
     let make_lambda_opt_stack_ok = make_make_label ".L_lambda_opt_stack_adjusted";;
     let make_lambda_opt_loop = make_make_label ".L_lambda_opt_stack_shrink_loop";;
     let make_lambda_opt_loop_exit =make_make_label ".L_lambda_opt_stack_shrink_loop_exit";;
     (* let make_dummy_label = make_make_label ".L_lambda_opt_dummy_label";; *)
    (* Additional LambdaOpt labels *)
    let make_lambda_opt_shift_stack = make_make_label ".L_lambda_opt_stack_shift_stack";;
    let make_lambda_opt_list_loop = make_make_label ".L_lambda_opt_list_loop";;
    let make_lambda_opt_shift_stack_params_loop = make_make_label ".L_lambda_opt_shift_stack_params_loop";;
    let make_lambda_opt_shift_stack_params_loop_end = make_make_label ".L_lambda_opt_shift_stack_params_loop_end";;
    
    (* TailCall labels *)
     let make_tc_applic_recycle_frame_loop = make_make_label ".L_tc_recycle_frame_loop";;
     let make_tc_applic_recycle_frame_done = make_make_label ".L_tc_recycle_frame_done";;
     let make_tc_applic_recycle_frame_debug = make_make_label ".L_tc_recycle_frame_debug";;
     let make_tc_applic_recycle_frame_loop_end = make_make_label ".L_tc_recycle_frame_loop_end";;

  (* define unique labels index *)
  let lbl_index=ref 0;;
  let get_lbl_index=(fun ()-> lbl_index:=(!lbl_index+1);(lbl_index))

  let code_gen exprs' =
    let consts = make_constants_table exprs' in
    let free_vars = make_free_vars_table exprs' in
    let rec run params env = function
      | ScmConst' sexpr -> 
        "\nmov rax, L_constants + "^(string_of_int(search_constant_address sexpr consts))^";const code_gen \n"
      | ScmVarGet' (Var' (v, Free)) ->
         let label = search_free_var_table v free_vars in
         Printf.sprintf
           "\tmov rax, qword [%s]; free var get code_gen\n"
           label
      | ScmVarGet' (Var' (v, Param minor)) -> 
        (Printf.sprintf "\tmov rax,qword[rbp+8*(4+%d)];param var get code_gen\n"minor)
      | ScmVarGet' (Var' (v, Bound (major, minor))) ->
              "\tmov rax, qword [rbp + 8 * 2];bound var get code_gen \n"
            ^(Printf.sprintf "\tmov rax,qword[rax+8*%d]\n"major)
            ^(Printf.sprintf "\tmov rax,qword[rax+8*%d]\n"minor)
      | ScmIf' (test, dit, dif) -> 
        let test_part=(run params env test) in
        let dit_part=(run params env dit) in
        let dif_part=(run params env dif) in
        let if_end_part=make_if_end()in
        let if_else_part=make_if_else()in
        ";Test part:;if (test) code_gen\n"
        ^test_part^"\n"
        ^"\tcmp rax, sob_boolean_false;if (test) code_gen\n"
        ^"\tje "^if_else_part^";if (test) code_gen\n"
        ^";WHERE IS MY JUMP TO FALSE!?!!?\n"
        ^dit_part^";if (then) code_gen\n"
        ^"\tjmp "^if_end_part^";if (test) code_gen\n"
        ^if_else_part^":;if (else) code_gen\n"
        ^dif_part
        ^if_end_part^":;if (else) code_gen\n"
      | ScmSeq' exprs' ->
         String.concat ";seq code_gen\n"
           (List.map (run params env) exprs')
      | ScmOr' exprs' ->
         let label_end = make_or_end () in
         let asm_code = 
           (match (list_and_last exprs') with
            | Some (exprs', last_expr') ->
               let exprs_code =
                 String.concat ""
                   (List.map
                      (fun expr' ->
                        let expr_code = run params env expr' in
                        expr_code
                        ^ "\tcmp rax, sob_boolean_false\n"
                        ^ (Printf.sprintf "\tjne %s\n" label_end))
                      exprs') in
               let last_expr_code = run params env last_expr' in
               exprs_code
               ^ last_expr_code
               ^ (Printf.sprintf "%s:\n" label_end)
            (* and just in case someone messed up the tag-parser: *)
            | None -> run params env (ScmConst' (ScmBoolean false)))
         in asm_code
         | ScmVarSet' (Var' (v, Free), expr') -> 
          let label = search_free_var_table v free_vars in
            (run params env expr')^
            Printf.sprintf
            "\tmov qword ["^label^"], rax;free var set code_gen\n"^
            "\tmov rax, sob_void\n"
      | ScmVarSet' (Var' (v, Param minor), expr') ->
        (run params env expr')
        ^Printf.sprintf "\tmov qword [rbp+8*(4+%d)],rax;param var set code_gen\n" minor
        ^ "\tmov rax, sob_void\n"
      | ScmVarSet' (Var' (v, Bound (major, minor)), expr') ->
        (run params env expr')
        ^"\tmov rbx, qword[rbp+8*2];bound var set code_gen\n"
        ^"\tmov rbx, qword[rbx+8*"^(string_of_int major)^"]\n)" 
        ^"\tmov qword[rbx+8*"^(string_of_int minor)^"],rax\n)" 
        ^"\tmov rax,sob_void\n"
      | ScmVarDef' (Var' (v, Free), expr') ->
         let label = search_free_var_table v free_vars in
         (run params env expr')
         ^ (Printf.sprintf "\tmov qword [%s], rax;free var def code_gen\n" label)
         ^ "\tmov rax, sob_void\n"
      | ScmVarDef' (Var' (v, Param minor), expr') ->
         raise X_not_yet_supported
      | ScmVarDef' (Var' (v, Bound (major, minor)), expr') ->
         raise X_not_yet_supported
      | ScmBox' (Var' (v, Param minor)) -> 
        "\tmov rdi,8 ;boxing param code_gen\n"
        ^"\tcall malloc\n"
        ^"\tmov r15,rax\n"
        ^(run params env (ScmVarGet' (Var' (v, Param minor))))
        ^"\tmov qword[r15],rax \n"
        ^"\tmov rax,r15 \n"
      | ScmBox' _ -> raise (X_this_should_not_happen (Printf.sprintf
      "ScmBox dontcare-why are we here?"))
      | ScmBoxGet' var' ->
         (run params env (ScmVarGet' var'))
         ^ "\tmov rax, qword [rax];boxing var get(see run code above)\n"
      | ScmBoxSet' (var', expr') -> 
        (run params env expr')
        ^"\tpush rax ;boxing var set\n"
        ^(run params env (ScmVarGet' var'))
        ^"\tpop qword [rax] \n"
        ^"\tmov rax, sob_void \n"
      | ScmLambda' (params', Simple, body) ->
         let label_loop_env = make_lambda_simple_loop_env ()
         and label_loop_env_end = make_lambda_simple_loop_env_end ()
         and label_loop_params = make_lambda_simple_loop_params ()
         and label_loop_params_end = make_lambda_simple_loop_params_end ()
         and label_code = make_lambda_simple_code ()
         and label_arity_ok = make_lambda_simple_arity_ok ()
         and label_end = make_lambda_simple_end ()
         in
         ";ScmLambdaSimple-Start of code \n"
         ^"\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
         ^ "\tcall malloc\n"
         ^ "\tpush rax\n"
         ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
         ^ "\tcall malloc\n"
         ^ "\tpush rax\n"
         ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
         ^ "\tcall malloc\n"
         ^ "\tmov rdi, ENV\n"
         ^ "\tmov rsi, 0\n"
         ^ "\tmov rdx, 1\n"
         ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
              label_loop_env)
         ^ (Printf.sprintf "\tcmp rsi, %d\n" env)
         ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
         ^ "\tmov rcx, qword [rdi + 8 * rsi]\n"
         ^ "\tmov qword [rax + 8 * rdx], rcx\n"
         ^ "\tinc rsi\n"
         ^ "\tinc rdx\n"
         ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
         ^ (Printf.sprintf "%s:\n" label_loop_env_end)
         ^ "\tpop rbx\n"
         ^ "\tmov rsi, 0\n"
         ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
         ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
         ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
         ^ "\tmov rdx, qword [rbp + 8 * rsi + 8 * 4]\n"
         ^ "\tmov qword [rbx + 8 * rsi], rdx\n"
         ^ "\tinc rsi\n"
         ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
         ^ (Printf.sprintf "%s:\n" label_loop_params_end)
         ^ "\tmov qword [rax], rbx\t; ext_env[0] <-- new_rib \n"
         ^ "\tmov rbx, rax\n"
         ^ "\tpop rax\n"
         ^ "\tmov byte [rax], T_closure\n"
         ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
         ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
         ^ (Printf.sprintf "\tjmp %s\n" label_end)
         ^ (Printf.sprintf "%s:\t; lambda-simple body\n" label_code)
         ^ (Printf.sprintf "\tcmp qword [rsp + 8 * 2], %d\n"
              (List.length params'))
         ^ (Printf.sprintf "\tje %s\n" label_arity_ok)
         ^ "\tpush qword [rsp + 8 * 2]\n"
         ^ (Printf.sprintf "\tpush %d\n" (List.length params'))
         ^ "\tjmp L_error_incorrect_arity_simple\n"
         ^ (Printf.sprintf "%s:\n" label_arity_ok)
         ^ "\tenter 0, 0\n"
         ^ (run (List.length params') (env + 1) body)
         ^ "\tleave\n"
         ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (List.length params'))
         ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end)
      | ScmLambda' (params', Opt opt, body) -> 

        (* Add some vars for LamdaOpt implementation *)
        let count = (string_of_int (List.length params'))
        and count' = (string_of_int (List.length params'+1))
        (* Add some labels for LamdaOpt implementation *)
        and label_enlarge_stack = make_lambda_opt_arity_exact ()
        and label_shrink_stack = make_lambda_opt_arity_more ()
        and label_low_args = make_lambda_opt_incorrect_arity ()
        and label_enlarge_loop = make_lambda_opt_exact_loop ()
        and label_enlarge_loop_end = make_lambda_opt_exact_loop_end ()
        and label_shrink_loop_1 = make_lambda_opt_more_loop ()
        and label_shrink_loop_end_1 = make_lambda_opt_more_loop_end ()
        and label_shrink_loop_2 = make_lambda_opt_more_loop_2 ()
        and label_shrink_loop_end_2 = make_lambda_opt_more_loop_2_end ()

        and label_loop_env = make_lambda_simple_loop_env ()
        and label_loop_env_end = make_lambda_simple_loop_env_end ()
        and label_loop_params = make_lambda_simple_loop_params ()
        and label_loop_params_end = make_lambda_simple_loop_params_end ()
        and label_code = make_lambda_simple_code ()
        and label_arity_ok = make_lambda_simple_arity_ok ()
        and label_end = make_lambda_simple_end ()
        in
        ";LambdaOpt-Start of code \n"
        ^"\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
        ^ "\tcall malloc\n"
        ^ "\tmov rdi, ENV\n"
        ^ "\tmov rsi, 0\n"
        ^ "\tmov rdx, 1\n"
        ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
             label_loop_env)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" env)
        ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
        ^ "\tmov rcx, qword [rdi + 8 * rsi]\n"
        ^ "\tmov qword [rax + 8 * rdx], rcx\n"
        ^ "\tinc rsi\n"
        ^ "\tinc rdx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
        ^ (Printf.sprintf "%s:\n" label_loop_env_end)
        ^ "\tpop rbx\n"
        ^ "\tmov rsi, 0\n"
        ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
        ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
        ^ "\tmov rdx, qword [rbp + 8 * rsi + 8 * 4]\n"
        ^ "\tmov qword [rbx + 8 * rsi], rdx\n"
        ^ "\tinc rsi\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
        ^ (Printf.sprintf "%s:\n" label_loop_params_end)
        ^ "\tmov qword [rax], rbx\t; ext_env[0] <-- new_rib \n"
        ^ "\tmov rbx, rax\n"
        ^ "\tpop rax\n"
        ^ "\tmov byte [rax], T_closure\n"
        ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
        ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
        ^ (Printf.sprintf "\tjmp %s\n" label_end)
        ^ (Printf.sprintf "%s:\t; lambda-simple body\n" label_code)
        ^ (Printf.sprintf "\tcmp qword [rsp + 8 * 2], %d\n"
             (List.length params'))
        (* Alternative impl.Opt start *)
        (* Irrelevant line *)

        (* ^ (Printf.sprintf "\tje %s\n" label_arity_ok) *)
        
       ^"je "^label_enlarge_stack^"
       jg "^label_shrink_stack^"
       jb "^label_low_args^"
       "^label_enlarge_stack^": ;(enlarge stack) exact args add empty list and shift down stack

        sub rsp,8 ;fix rsp
        mov rdi,rsp ;cur shift

        mov rax,qword[rdi+8];ret
        mov qword[rdi],rax
        add rdi,8

        mov rax,qword[rdi+8];env
        mov qword[rdi],rax
        add rdi,8

        mov qword[rdi],"^count'^" ;count'-update argc
        add rdi,8

        mov rcx,"^count^" ;original count

       "^label_enlarge_loop^": ;(enlarge stack) shifting down stack loop
         cmp rcx,0
         je "^label_enlarge_loop_end^"
         mov rax,qword[rdi+8]
         mov qword[rdi],rax
         add rdi,8
         dec rcx
         jmp "^label_enlarge_loop^"
       
       "^label_enlarge_loop_end^": ;(enlarge stack) shifting down stack loop
        mov r15,sob_nil
        mov qword[rdi],r15
        jmp "^label_arity_ok^"
       
       "^label_shrink_stack^": ;(shrink stack) more args-add empty list and correct the stack

       mov rcx,qword[rsp+16];arcg
       lea rsi,[rsp+8*(rcx+2)];top frame address
       sub rcx,"^count^" ;original count-opt size
       mov r8,rsi
       mov r9,sob_nil
       "^label_shrink_loop_1^": ;(shrink stack) create opt linkedlist

         cmp rcx,0
         je "^label_shrink_loop_end_1^"
         mov rdi,17
         call malloc
         mov byte[rax],T_pair
         mov rbx,qword[rsi]
         mov SOB_PAIR_CAR(rax),rbx
         mov SOB_PAIR_CDR(rax),r9
         mov r9,rax
         sub rsi,8
         dec rcx
         jmp "^label_shrink_loop_1^"

         "^label_shrink_loop_end_1^": ;(shrink stack) end of first loop now we have opt list

       mov qword[r8],r9 ;place the opt list at top frame
       mov rcx,"^count^" ;original count
       lea rsi,[rsp+8*(rcx+2)] ;rsi points at last param'
       sub r8,8; now r8 points at place for last param' at new stack

       "^label_shrink_loop_2^": ;(shrink stack) shift up the params'
         cmp rcx,0
         je "^label_shrink_loop_end_2^"
         mov rax,qword[rsi]
         mov qword[r8],rax
         sub rsi,8
         sub r8,8
         dec rcx
         jmp "^label_shrink_loop_2^"

         "^label_shrink_loop_end_2^": ;(shrink stack) shift up the params' - end of loop

       mov qword[r8],"^count'^" ;count'
       sub rsi,8
       sub r8,8

       mov rax,qword[rsi]
       mov qword[r8],rax
       sub rsi,8
       sub r8,8

       mov rax,qword[rsi]
       mov qword[r8],rax

       mov rsp,r8
       jmp "^label_arity_ok^"
       "^label_low_args^": ;too few params passed to lambda
       "
           (* Alternative impl.Opt end *)
        ^ "\tpush qword [rsp + 8 * 2]\n"
        ^ (Printf.sprintf "\tpush %d\n" (List.length params'))
        ^ "\tjmp L_error_incorrect_arity_simple\n"
        ^ (Printf.sprintf "%s:\n" label_arity_ok)
        ^ "\tenter 0, 0\n"
        (* Update next line to params' +1 at run *)
        ^ (run (List.length params'+1) (env + 1) body)
        ^ "\tleave\n"
        (* Update next line to params' +1 at ret *)
        ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (List.length params'+1))
        ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end)

      (* Our impl. of LambdaOpt - fails at some tests *)
      
       (* let params_count = (string_of_int (List.length params'))
        and label_loop_env = make_lambda_opt_loop_env ()
        and label_loop_env_end = make_lambda_opt_loop_env_end ()
        and label_loop_params = make_lambda_opt_loop_params ()
        and label_loop_params_end = make_lambda_opt_loop_params_end ()
        and label_code = make_lambda_opt_code ()
        and label_arity_ok = make_lambda_opt_arity_ok ()
        and label_end = make_lambda_opt_end ()
        and label_arity_more = make_lambda_opt_arity_more ()
        and label_incorrect_arity_opt= make_lambda_opt_incorrect_arity ()
        and label_shift_params_loop_exact = make_lambda_opt_shift_params_loop_exact ()
        and label_shift_params_loop_exact_end = make_lambda_opt_shift_params_loop_exact_end ()
        and label_shift_params_loop_exact_end_zero = make_lambda_opt_shift_params_loop_exact_end_zero ()
        (* and dummy_label = make_dummy_label () *)
        (* and label_loop_params_list= make_lambda_opt_loop_params_list () *)
        and label_opt_list_loop=make_lambda_opt_loop_params_list_loop ()
        and label_shift_stack=make_lambda_opt_shift_stack ()
        and label_shift_stack_params_loop=make_lambda_opt_shift_stack_params_loop ()
        and label_shift_stack_params_loop_end=make_lambda_opt_shift_stack_params_loop_end ()
      in
        ";ScmLambdaOpt-Start of code \n"
        ^"\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
        ^ "\tcall malloc\n"
        ^ "\tpush rax\n"
        ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
        ^ "\tcall malloc\n"
        ^ "\tmov rdi, ENV\n"
        ^ "\tmov rsi, 0\n"
        ^ "\tmov rdx, 1\n"
        ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
             label_loop_env)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" env)
        ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
        ^ "\tmov rcx, qword [rdi + 8 * rsi]\n"
        ^ "\tmov qword [rax + 8 * rdx], rcx\n"
        ^ "\tinc rsi\n"
        ^ "\tinc rdx\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
        ^ (Printf.sprintf "%s:\n" label_loop_env_end)
        ^ "\tpop rbx\n"
        ^ "\tmov rsi, 0\n"
        ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
        ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
        ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
        ^ "\tmov rdx, qword [rbp + 8 * rsi + 8 * 4]\n"
        ^ "\tmov qword [rbx + 8 * rsi], rdx\n"
        ^ "\tinc rsi\n"
        ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
        ^ (Printf.sprintf "%s:\n" label_loop_params_end)
        ^ "\tmov qword [rax], rbx\t; ext_env[0] <-- new_rib \n"
        ^ "\tmov rbx, rax\n"
        ^ "\tpop rax\n"
        ^ "\tmov byte [rax], T_closure\n"
        ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
        ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
        ^ (Printf.sprintf "\tjmp %s\n" label_end)
        ^ (Printf.sprintf "%s:\t; lambda-opt body\n" label_code)
        ^ (Printf.sprintf "\tcmp qword [rsp + 8 * 2], %d\n"
             (List.length params'))

        (* Start of Lambda Opt part - checking the argc(params'+opt) and params' *)

        (* ^"\tCHECKP [rsp+16] ;check\n" *)

        ^"\tjg "^label_arity_more^"\n"
        ^"\tjb "^label_incorrect_arity_opt^"\n"
        (* Case of empty Opt - shift stack down by 1 and add empty list *)
          (* ^"\tHERE \n" *)
        ^"\tmov r14, rbp \n ; preserve  old rbp(necessary?)\n "
        ^"\tmov r8,rsp \n"
        ^"\tsub r8,8 ;fixed offset\n"
        ^"\tmov r9,qword[rsp] \n"
        ^"\tmov qword[r8],r9 ;shift ret\n"
        ^"\tadd r8,8 ; \n"
        ^"\tmov r9,qword[rsp+8] \n"
        ^"\tmov qword[r8],r9 ;shift env\n"
        ^"\tadd r8,8 ; \n"
        ^"\tmov r9,qword[rsp+16] \n"
        ^"\tadd r9,1 ;update argc \n"
        ^"\tmov qword[r8],r9 ;shift argc\n"
        ^"\tmov r10,[rsp+16] ;use old argc as a counter to shift the argv down\n"
        ^"\tmov r11,rsp ;\n"
        ^"\tadd r11,16; address of argv[i] for each iteration \n"
        ^"\tmov r13,r11 \n"
        ^"\tsub r13,8 ;fixed offset to shift the argv[i] \n"
        ^"\tcmp r10,0 \n"
        ^"\tje "^label_shift_params_loop_exact_end_zero^" \n"
        ^label_shift_params_loop_exact^" :\n"
        ^"\tadd r11,8  ;step to current argv[i]\n"
        ^"\tadd r13,8 \n"
        ^"\tdec r10 \n"
        ^"\tmov r12,qword[r11] \n"
        ^"\tmov qword[r13],r12 ;rellocate argv[i] \n"
        ^"\tcmp r10,0 \n"
        ^"\tje "^label_shift_params_loop_exact_end^" \n"
        ^"\tjmp "^label_shift_params_loop_exact^"\n"
        ^label_shift_params_loop_exact_end_zero^":\n"
        ^"\tmov r12,sob_nil \n"
        ^"\tmov qword[rsp+16],r12 ;in case of zero params,place empty list in fixed place \n"
        ^"\tsub rsp,8 ;fixed rsp \n"
        ^"jmp "^label_arity_ok^" ;finish fixing\n"
        ^label_shift_params_loop_exact_end^": \n"
        ^"\tmov r12,sob_nil \n"
        ^"\tmov qword[r11],r12; place the empty opt list in the end of frame \n"
        ^"\tsub rsp,8 ;fixed rsp \n"
        ^"jmp "^label_arity_ok^" ;finish fixing\n"
        ^label_arity_more^":\n"
        (* ^"\tHERE \n" *)
        (* ^"\tCHECKP [rsp+16] ;check\n" *)
        ^"\tmov r8,[rsp+16] ;real num of args on stack\n"
        ^"\txor r14,r14 ;r14 is counter of shifts to execute next \n"
        ^"\tmov r12,rsp \n"
        ^"\tmov r9,sob_nil ;r9<-tail of the proper list\n"
        ^"\tmov r15,r8 \n"
        ^"\tshl r15,3 ;offset in bytes \n"
        (* CODE IS OK UNTIL THIS LINE *)
        ^label_opt_list_loop^":\n"
         ^"\tcmp r8,"^params_count^"\n"
         ^"\tje "^label_shift_stack^"\n"
         ^"\tadd r14,8;add shift bytes\n"
         ^"\tmov r10,qword[rsp+16+r15];current param not on list\n"
         ^"\tsub r15,8\n"
         ^"\tdec r8\n"
         ^"\tmov rdi,17 ;17 bytes for pair \n"
         ^"\tcall malloc \n"
         ^"\tmov byte[rax],T_pair ;set pair tag\n"
         ^"\tmov SOB_PAIR_CAR(rax),r10 ;CAR-stack value\n"
         ^"\tmov SOB_PAIR_CDR(rax),r9 ;CAR-stack value\n"
         ^"\tmov r9,rax; go to next tail param backward, keep the pointer \n"
         (* ^"\tmov rax,0 ;debug needs \n" *)
         ^"\tjmp "^label_opt_list_loop^"\n"
         ^label_shift_stack^":\n"
         ^"\tmov r15,[rsp+16] ; argc \n"
         ^"\tshl r15,3 \n"
         ^"\tmov qword[rsp+16+r15],r9 ;place the opt list on bottom of stack\n"
         ^"\tsub r14,8 ;real shift of all the stack\n"
         (* ^"\tCHECKP r14 ;check\n" *)
         (* ^"\tHERE \n" *)
         ^"\tmov r11,rsp \n"
         (* Next line was corrected to 16 instead of 24 *)
         ^"\tadd r11,16 \n"
         ^"\tmov r13,"^params_count^" ;\n"
         ^"\tshl r13,3 ;\n"
         ^"\tadd r11,r13 ;r11 is now an address of last param [r11]->argv[params'-1] \n"
         ^"\tmov r10,r11 \n"
         ^"\tadd r10,r14 ;r10 is now an address of last param-after fixing \n"
         ^"\tmov r13,"^params_count^" ;r13 is a loop counter now \n"
         ^label_shift_stack_params_loop^" :\n"
         ^"\tcmp r13,0\n"
         ^"\tje "^label_shift_stack_params_loop_end^"\n"
         ^"\tmov r12,qword[r11] ;temporary \n"
         ^"\tmov qword[r10],r12 ;rellocate param\n"
         ^"\tsub r11,8 \n"
         ^"\tsub r10,8 \n"
         ^"\tdec r13 ;decrease loop step \n"
         ^"\tjmp "^label_shift_stack_params_loop^"\n"
         ^label_shift_stack_params_loop_end^": \n"
         (* fixing the rsp,argc,shifting the ret,env,argc *)
         (*CODE IS OK UNTIL THIS LINE-to check the pair making macro*)
         (* ^"\tHERE \n" *)
         ^"\tmov r11,rsp \n"
         ^"\tadd r11,16 ;[r11]->argc\n"
         ^"\tmov r12,"^params_count^";\n"
         ^"\tinc r12 ;params+opt list \n"
         ^"\tmov qword[r11],r12;update argc \n"
         (* ^"\tCHECKP [rsp+16] ;check\n"  *)
         ^"\tmov r12,qword[r11] ;new argc-temp\n"
         ^"\tadd r11,r14 ;addr of argc after shift\n"
         ^"\tmov qword[r11],r12;shift argc \n"
         (* ^"\tCHECKP [rsp+32] ;check\n"  *)
         ^"\tmov r11,rsp \n"
         ^"\tadd r11,8 ;[r11]->env\n"
         ^"\tmov r12,qword[r11] ;env temp\n"
         ^"\tadd r11,r14 ;addr of env after shift\n"
         ^"\tmov qword[r11],r12;shift env \n"
         ^"\tmov r11,rsp ;[r11]->ret\n"
         ^"\tmov r12,qword[r11] ;ret temp\n"
         ^"\tadd r11,r14 ;addr of ret after shift\n"
         ^"\tmov qword[r11],r12;shift ret \n"
         ^"\tadd rsp,r14; fix rsp itself \n"
        (* ^dummy_label^":\n" *)
        (* ^"\tCHECKP [rsp+16] ;check\n"  *)
        ^ (Printf.sprintf "\tjmp %s\n" label_arity_ok)
        (*CODE IS OK UNTIL THIS LINE-to check the pair making macro*)
        (* ^ (Printf.sprintf "\tje %s\n" label_arity_ok) *)
        ^label_incorrect_arity_opt^": \n"
        ^ "\tpush qword [rsp + 8 * 2]\n"
        ^ (Printf.sprintf "\tpush %d\n" (List.length params'))
        ^ "\tjmp L_error_incorrect_arity_simple\n"
        ^ (Printf.sprintf "%s:\n" label_arity_ok)
        ^ "\tenter 0, 0\n"
        ^ (run (List.length params'+1) (env + 1) body)
        ^ "\tleave\n"
        ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (List.length params'))
        ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end)   *)

      | ScmApplic' (proc, args, Non_Tail_Call) -> 
        (let n=(string_of_int (List.length args)) in (* number of arguments *)
        let argsPart=List.fold_right
        (fun lst acc->acc^(run params env lst)^"\n push rax \n") args "\n ;Application generation strat of code:\n" in
        let procPart=(run params env proc)in
        let restApplic="push "^n^"\n"^
        procPart^"\n"^
        "assert_closure(rax)\n"^
        "push qword[rax+1] \n"^ (* env *)
        "call qword[rax+9]\n"^ (* code *)
        (* stack is already free for some reason- no need to free it again *)
        (* pop env *)
        (* "add rsp,8 \n"^  *)
        (* pop arg count *)
        (* "pop rbx\n"^  *)
        (* rbx = rbx * 8 *)
        (* "shl rbx,3 \n"^  *)
        (* pop args *)
        (* "add rsp,rbx \n"^  *)
        "; End of Applic code generation \n" in
        argsPart^restApplic
      ) 
      | ScmApplic' (proc, args, Tail_Call) ->
        (* raise (X_this_should_not_happen
           "ApplicTP is not implemented yet") *)
           let n=(string_of_int (List.length args)) in (* number of arguments *)
           let argsPart=List.fold_right
           (fun lst acc->acc^(run params env lst)^"\n push rax \n") args "\n ;(Tail call)Application generation start of code:\n" in
           let procPart=(run params env proc)in
           let label_tc_applic_recycle_frame_loop = make_tc_applic_recycle_frame_loop() in
           let label_tc_applic_recycle_frame_loop_end = make_tc_applic_recycle_frame_loop_end () in
           let label_tc_applic_debug = make_tc_applic_recycle_frame_debug() in
           let restApplic=
           "push "^n^"\n"^
           procPart^"\n"^
           "assert_closure(rax)\n"^
           "push qword[rax+1] \n"^ (* env *)
           "push qword[rbp+8*1]\n"^ (* old return address *)
           "push qword[rbp]\n"^ (* same the old rbp *)
           (* calculating the top frame address *)
           (* how we deal with push\pop rbp? *)
           (* be careful because rsp is different here *)
           label_tc_applic_debug^" :\n"^
           (* WE DON'T KNOW WHAT HAPPENS TO r15 during the code so it's a bad solution *)
           (* "mov r15, qword[rsp] ;save old ret address\n"^  *)
           "mov r14, qword[rsp+24] ;argc of h(e.g argc=2)\n"^
           "shl r14, 3 ;argc in bytes\n"^
           "add r14, 24 ;offset \n"^
           "add r14, rsp ;\n"^
           (* Now we have a first key of applic the address of argvh(n-1) in r14(e.g 40) *)
           "mov r13, qword[r14+32] ;argc of g(e.g argc=1)\n"^
           "shl r13, 3 ;argc in bytes\n"^
           "add r13, 32 ;32 or 24?? \n"^
           "add r13, r14 ;r13 points to top frame of g\n"^
           (* Now we have a second key of applic the address of argvh(n-1) in r13(e.g 80)*)
           "mov r12, r13\n"^
           "sub r12, r14 ;offset\n"^
            (* offset of frame shifting(e.g 40)*)
            (* Now r14 will use us as a counter to shift whole the frame *)
           label_tc_applic_recycle_frame_loop^": \n"^
           "\tmov r11,qword[r14]\n"^
           "\tmov qword[r13],r11 \n"^
           "\tsub r14,8 \n"^
           "\tsub r13,8 \n"^
           "\tcmp r14,rsp ; rsp is a lower bound of shifting-finish \n"^
           "\tje "^label_tc_applic_recycle_frame_loop_end^"\n"^
           "\tjmp "^ label_tc_applic_recycle_frame_loop^"\n"^
           label_tc_applic_recycle_frame_loop_end^":\n"^
          (* unknown issue where is old rbp??? *)
          (* finish shifting the frame ,r14 points to rsp, fix the rsp(update to r13), and done *)
           "\tpop rbp;restore rbp\n"^
           "\tadd r13,8 ;correct bottom offset\n"^
           "\tmov rsp,r13 \n"^
           (* "\tmov rbp,r15\n"^ *)
           "\tjmp SOB_CLOSURE_CODE(rax)\n" in
           argsPart^restApplic
    and runs params env exprs' =
      List.map
        (fun expr' ->
          let code = run params env expr' in
          let code =
            code
            ^ "\n\tmov rdi, rax"
            ^ "\n\tcall print_sexpr_if_not_void\n" in
          code)
        exprs' in
    let codes = runs 0 0 exprs' in
    let code = String.concat "\n" codes in
    let code =
      (file_to_string "prologue-1.asm")
      ^ (asm_of_constants_table consts)
      ^ "\nsection .bss\n"
      ^ (asm_of_free_vars_table free_vars)
      ^ (file_to_string "prologue-2.asm")
      ^ (asm_of_global_bindings global_bindings_table free_vars)
      ^ "\n"
      ^ code
      ^ (file_to_string "epilogue.asm") in
    code;;

  let compile_scheme_string file_out user =
    let init = file_to_string "init.scm" in
    let source_code = init ^ user in
    let sexprs = (PC.star Reader.nt_sexpr source_code 0).found in
    let exprs = List.map Tag_Parser.tag_parse sexprs in
    let exprs' = List.map Semantic_Analysis.semantics exprs in
    let asm_code = code_gen exprs' in
    (string_to_file file_out asm_code;
     Printf.printf "!!! Compilation finished. Time to assemble!\n");;  

  let compile_scheme_file file_in file_out =
    compile_scheme_string file_out (file_to_string file_in);;

end;; (* end of Code_Generation struct *)

(* end-of-input *)


