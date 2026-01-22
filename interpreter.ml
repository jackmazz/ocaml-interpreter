(* ================================================================================ *)

type 'a map = (string * 'a option) list

let map_update (m : 'a map) (k : string) (v : 'a) : 'a map = (k, Some v) :: m
let map_remove (m : 'a map) (k : string) : 'a map = (k, None) :: m

let rec map_lookup (m : 'a map) (k : string) : 'a option =
  match m with
  | [] -> None
  | (k', v) :: tl when k' = k -> v
  | _ :: tl -> map_lookup tl k

let map_lookup_def (m : 'a map) (k : string) (def : 'a) : 'a =
  match (map_lookup m k) with
  | None -> def
  | Some v -> v

(* ================================================================================ *)

type lexicalState =
| LexEmpty
| LexNormal
| LexEnclosed of char

(* ================================================================================ *)

type token =
| DToken of char
| NToken of string
| EToken of (char * string)

(* ================================================================================ *)

type stackElement =
| StkUnit
| StkBool of bool
| StkInt of int
| StkString of string
| StkName of string
| StkClosure of (string * command list * stackElement map * string)
| StkInOutClosure of (string * command list * stackElement map * string)
| StkError and

command =
| NopCmd
| AndCmd
| OrCmd
| IfCmd
| NotCmd
| AddCmd
| SubCmd
| MulCmd
| DivCmd
| RemCmd
| NegCmd
| EqualCmd
| LessThanCmd
| ToStringCmd
| CatCmd
| PrintlnCmd
| PushCmd of stackElement
| PopCmd
| SwapCmd
| BindCmd
| LetCmd
| EndCmd
| FunCmd of string * string
| InOutFunCmd of string * string
| CallCmd
| ReturnCmd
| InOutReturnCmd of string * string
| FunEndCmd
| QuitCmd

(* ================================================================================ *)

let read_file (fn : string) : string =
  let chan = open_in fn in

  let rec read_all fdata lb = 
    try read_all (fdata ^ lb ^ String.trim (input_line chan)) "\n"
    with End_of_file -> fdata in

  let fdata = read_all "" "" in
  close_in chan;
  fdata

let scan_file (fn : string) : token list =
  let fdata = read_file fn in
  let len = String.length fdata in

  let rec scan_all toks str state idx =
    if idx = len then
      match state with
      | LexEmpty ->  toks
      | LexNormal -> toks @ [NToken str]
      | LexEnclosed _ -> [NToken "push"; NToken ":error:"]
    else
      let c = String.get fdata idx in
      let idx = idx + 1 in
      match c with
      | '\n' ->
        (match state with
        | LexEmpty -> scan_all (toks @ [DToken c]) "" state idx
        | LexNormal -> scan_all (toks @ [NToken str; DToken c]) "" LexEmpty idx
        | LexEnclosed ec -> scan_all toks (str ^ String.make 1 c) state idx)
      | '\"' ->
        (match state with
        | LexEmpty -> scan_all toks "" (LexEnclosed c) idx
        | LexNormal -> scan_all (toks @ [NToken str]) "" (LexEnclosed c) idx
        | LexEnclosed ec when ec = c -> scan_all (toks @ [EToken (c, str)]) "" LexEmpty idx
        | LexEnclosed _ -> scan_all toks (str ^ String.make 1 c) state idx)
      | ' ' | '\t' ->
        (match state with
        | LexEmpty -> scan_all toks "" state idx
        | LexNormal -> scan_all (toks @ [NToken str]) "" LexEmpty idx
        | LexEnclosed ec -> scan_all toks (str ^ String.make 1 c) state idx)
      | _ ->
        (match state with
        | LexEmpty -> scan_all toks (str ^ String.make 1 c) LexNormal idx
        | _ -> scan_all toks (str ^ String.make 1 c) state idx) in
  
  scan_all [] "" LexEmpty 0

(* ================================================================================ *)

let parse_tokens (toks : token list) : command list =
  let parse_name str =
    let pred c =
      match c with
      | '0' .. '9'
      | 'A' .. 'Z'
      | 'a' .. 'z'
      | '_' -> true
      | _ -> false in
      
    match str with
    | "" -> raise (Failure str)
    | _ ->
      match String.get str 0 with
      | '0' .. '9' -> raise (Failure str)
      | _ when String.for_all pred str -> StkName str
      | _ -> raise (Failure str) in
  
  let parse_elem tok =
    match tok with
    | NToken v ->
      (match v with
      | ":unit:" -> PushCmd StkUnit
      | ":error:" -> PushCmd StkError
      | ":true:" -> PushCmd (StkBool true)
      | ":false:" -> PushCmd (StkBool false)
      | _ ->
        try PushCmd (StkInt (int_of_string v))
        with Failure _ -> try PushCmd (parse_name v)
        with Failure _ -> PushCmd StkError)
    | EToken ('\"', v) -> PushCmd (StkString v)
    | _ -> PushCmd StkError in

  let rec parse_seg seg =
    match seg with
    | [] -> NopCmd
    | [NToken "and"] -> AndCmd
    | [NToken "or"] -> OrCmd
    | [NToken "not"] -> NotCmd
    | [NToken "if"] -> IfCmd
    | [NToken "add"] -> AddCmd
    | [NToken "sub"] -> SubCmd
    | [NToken "mul"] -> MulCmd
    | [NToken "div"] -> DivCmd
    | [NToken "rem"] -> RemCmd
    | [NToken "neg"] -> NegCmd
    | [NToken "equal"] -> EqualCmd
    | [NToken "lessThan"] -> LessThanCmd
    | [NToken "toString"] -> ToStringCmd
    | [NToken "cat"] -> CatCmd
    | [NToken "println"] -> PrintlnCmd
    | [NToken "push"; tok] -> parse_elem tok
    | [NToken "pop"] -> PopCmd
    | [NToken "swap"] -> SwapCmd
    | [NToken "bind"] -> BindCmd
    | [NToken "let"] -> LetCmd
    | [NToken "end"] -> EndCmd
    | [NToken "fun"; NToken str1; NToken str2] -> FunCmd (str1, str2)
    | [NToken "inOutFun"; NToken str1; NToken str2] -> InOutFunCmd (str1, str2)
    | [NToken "call"] -> CallCmd
    | [NToken "return"] -> ReturnCmd
    | [NToken "funEnd"] -> FunEndCmd
    | [NToken "quit"] -> QuitCmd
    | _ -> PushCmd StkError in

  let rec parse_all cmds seg toks =
    match toks with
    | [] -> cmds @ [parse_seg seg]
    | DToken _ :: toks' -> parse_all (cmds @ [parse_seg seg]) [] toks'
    | tok :: toks' -> parse_all cmds (seg @ [tok]) toks' in

  parse_all [] [] toks

(* ================================================================================ *)

let execute_commands (cmds : command list) (fn : string) : unit =
  let chan = open_out fn in

  let rec extract_subprog prog subprog count =
    match (prog, count) with
    | ([], _) ->
        (subprog, [])
    | (FunEndCmd :: prog', 0) ->
        (subprog, prog')
    | (FunEndCmd :: prog', count) ->
        let count = count - 1 in
        extract_subprog prog' (subprog @ [FunEndCmd]) count
    | (cmd :: prog', _) ->
        let count = match cmd with
        | FunCmd _ | InOutFunCmd _ -> count + 1
        | _ -> count in
        extract_subprog prog' (subprog @ [cmd]) count in

  let rec pop_args args (stk, env) vars =
    match (stk, vars) with
    | ([], _ :: _) -> None
    | (e :: stk', var :: vars') ->
        let arg =
          match (e, var) with
          | (StkName str, true) ->
              map_lookup_def env str e
          | _ -> e in
        pop_args (args @ [arg]) (stk', env) vars'
    | stk, _ -> Some (args, stk) in
  
  let exec_nop (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    (prog' :: progs', stks, envs) in
  
  let exec_and (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkBool b1; StkBool b2], stk') ->
        let stk' = StkBool (b2 && b1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in
  
  let exec_or (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkBool b1; StkBool b2], stk') ->
        let stk' = StkBool (b2 || b1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_not (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkBool b], stk') ->
        let stk' = StkBool (not b) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in
  
  let exec_if (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false; false; true] in
    match pop_args [] (stk, env) vars with
    | Some ([arg1; arg2; StkBool true], stk') ->
        let stk' = arg1 :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | Some ([arg1; arg2; StkBool false], stk') ->
        let stk' = arg2 :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
      let stk = (StkError :: stk) in
      (prog' :: progs', stk :: stks', envs) in

  let exec_add (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') ->
        let stk' = StkInt (i2 + i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_sub (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') ->
        let stk' = StkInt (i2 - i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_mul (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') ->
        let stk' = StkInt (i2 * i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_neg (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i], stk') ->
        let stk' = StkInt (-i) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in
    
  let exec_div (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') when i1 != 0 ->
        let stk' = StkInt (i2 / i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_rem (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') when i1 != 0 ->
        let stk' = StkInt (i2 mod i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in
  
  let exec_equal (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') ->
        let stk' = StkBool (i2 = i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_less_than (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkInt i1; StkInt i2], stk') ->
        let stk' = StkBool (i2 < i1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_to_string (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false] in
    match pop_args [] (stk, env) vars with
    | Some ([e], stk') ->
        let str =
          match e with
          | StkUnit -> ":unit:"
          | StkBool true -> ":true:"
          | StkBool false -> ":false:"
          | StkInt i -> string_of_int i
          | StkString str -> str
          | StkName str -> str
          | StkClosure (name, _, _, _) -> name 
          | StkInOutClosure (name, _, _, _) -> name 
          | StkError -> ":error:" in
        let stk' = StkString str :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_cat (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkString str1; StkString str2], stk') ->
        let stk' = StkString (str2 ^ str1) :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in
  
  let exec_println (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkString str], stk') ->
        output_string chan (str ^ "\n");
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_push (prog', progs, progs', stk, stks, stks', env, envs, envs') e =
    let stk = e :: stk in
    (prog' :: progs', stk :: stks', envs) in
  
  let exec_pop (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false] in
    match pop_args [] (stk, env) vars with
    | Some (args, stk') ->
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_swap (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false; false] in
    match pop_args [] (stk, env) vars with
    | Some ([e1; e2], stk') ->
        let stk' = e2 :: e1 :: stk' in
        (prog' :: progs', stk' :: stks', envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_bind (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; false] in
    match pop_args [] (stk, env) vars with
    | Some ([StkError; e2], stk') | Some ([StkName _; e2], stk') ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs)
    | Some ([e1; StkName str], stk') ->
        let stk' = StkUnit :: stk' in
        let env = map_update env str e1 in
        (prog' :: progs', stk' :: stks', env :: envs')
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_let (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    (prog' :: progs', stk :: stks, env :: envs) in

  let exec_end (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false] in
    match (pop_args [] (stk, env) vars, stks') with
    | (Some ([e], _), stk :: stks'') ->
        let stk = e :: stk in
        (prog' :: progs', stk :: stks'', envs')
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_fun (prog', progs, progs', stk, stks, stks', env, envs, envs') name param =
    match extract_subprog prog' [] 0  with
    | (subprog, prog') ->
        let stk = StkUnit :: stk in
        let env = map_update env name (StkClosure (name, subprog, env, param)) in
        (prog' :: progs', stk :: stks', env :: envs') in
  
  let exec_in_out_fun (prog', progs, progs', stk, stks, stks', env, envs, envs') name param =
    match extract_subprog prog' [] 0  with
    | (subprog, prog') ->
        let stk = StkUnit :: stk in
        let env = map_update env name (StkInOutClosure (name, subprog, env, param)) in
        (prog' :: progs', stk :: stks', env :: envs') in
  
  let exec_fun_call (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkError; _], stk') | Some ([StkName _; _], stk') ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs)
    | Some ([e; StkClosure (name, subprog, subenv, param)], stk') ->
        let stk = [] in
        let subenv = map_update subenv name (StkClosure (name, subprog, subenv, param)) in
        let subenv = map_update subenv param e in
        (subprog :: prog' :: progs', stk :: stk' :: stks', subenv :: envs)
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in
  
  let exec_in_out_fun_call (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false; true] in
    match pop_args [] (stk, env) vars with
    | Some ([StkName str; StkInOutClosure (name, subprog, subenv, param)], stk') ->
        (match map_lookup env str with
        | None | Some StkError | Some (StkName _) ->
            exec_fun_call (prog', progs, progs', stk, stks, stks', env, envs, envs')
        | Some v ->
            let subprog = subprog @ [InOutReturnCmd (str, param)] in
            let stk = [] in
            let subenv = map_update subenv name (StkInOutClosure (name, subprog, subenv, param)) in
            let subenv = map_update subenv param v in
            (subprog :: prog' :: progs', stk :: stk' :: stks', subenv :: envs))
    | _ ->
        exec_fun_call (prog', progs, progs', stk, stks, stks', env, envs, envs') in

  let exec_call (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [false; true] in
    match pop_args [] (stk, env) vars with
    | Some ([_; StkClosure _], _) ->
        exec_fun_call (prog', progs, progs', stk, stks, stks', env, envs, envs')
    | Some ([_; StkInOutClosure _], _) ->
        exec_in_out_fun_call (prog', progs, progs', stk, stks, stks', env, envs, envs')
    | _ ->
        let stk = (StkError :: stk) in
        (prog' :: progs', stk :: stks', envs) in

  let exec_in_out_return (prog', progs, progs', stk, stks, stks', env, envs, envs') str1 str2 =
    match (map_lookup env str2, envs') with
    | (Some v, env :: envs'') ->
        let env = map_update env str1 v in
        ([] :: progs', stks', env :: envs'')
    | _ ->
        ([] :: progs', stks', envs') in

  let exec_return (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    let vars = [true] in
    match (pop_args [] (stk, env) vars, prog', stks') with
    | (Some ([e], _), (InOutReturnCmd (str1, str2)) :: _, stk :: stks'') ->
        exec_in_out_return (prog', progs, progs', stk, stks, stk :: stks'', env, envs, envs') str1 str2
    | (Some ([e], _), _, stk :: stks'') ->
        let stk = e :: stk in
        ([] :: progs', stk :: stks'', envs')
    | _ ->
        ([] :: progs', stks', envs') in
  
  let exec_quit (prog', progs, progs', stk, stks, stks', env, envs, envs') =
    ([[]], [[]], [[]]) in

  let string_of_elem e = 
    match e with
    | StkUnit -> ":unit:"
    | StkBool true -> ":true:"
    | StkBool false -> ":false:"
    | StkInt i -> string_of_int i
    | StkString str -> str
    | StkName str -> str
    | StkClosure (name, _, _, _) -> name 
    | StkInOutClosure (name, _, _, _) -> name 
    | StkError -> ":error:" in

  let exec_cmd cmd cfg =
    let debug_print str b = if b then print_endline str else () in
    let b = false in

    match cmd with
    | AndCmd -> debug_print "exec_and" b; exec_and cfg
    | OrCmd -> debug_print "exec_or" b; exec_or cfg
    | NotCmd -> debug_print "exec_not" b; exec_not cfg
    | IfCmd -> debug_print "exec_if" b; exec_if cfg
    | AddCmd -> debug_print "exec_add" b; exec_add cfg
    | SubCmd -> debug_print "exec_sub" b; exec_sub cfg
    | MulCmd -> debug_print "exec_mul" b; exec_mul cfg
    | DivCmd -> debug_print "exec_div" b; exec_div cfg
    | RemCmd -> debug_print "exec_rem" b; exec_rem cfg
    | NegCmd -> debug_print "exec_neg" b; exec_neg cfg
    | EqualCmd -> debug_print "exec_equal" b; exec_equal cfg
    | LessThanCmd -> debug_print "exec_less_than" b; exec_less_than cfg
    | ToStringCmd -> debug_print "exec_to_string" b; exec_to_string cfg
    | CatCmd -> debug_print "exec_cat" b; exec_cat cfg
    | PrintlnCmd -> debug_print "exec_println" b; exec_println cfg
    | PushCmd e -> debug_print ("exec_push " ^ string_of_elem e) b; exec_push cfg e
    | PopCmd -> debug_print "exec_pop" b; exec_pop cfg
    | SwapCmd -> debug_print "exec_swap" b; exec_swap cfg
    | BindCmd -> debug_print "exec_bind" b; exec_bind cfg
    | LetCmd -> debug_print "exec_let" b; exec_let cfg
    | EndCmd -> debug_print "exec_end" b; exec_end cfg
    | FunCmd (str1, str2) -> debug_print "exec_fun" b; exec_fun cfg str1 str2
    | InOutFunCmd (str1, str2) -> debug_print "exec_in_out_fun" b; exec_in_out_fun cfg str1 str2
    | CallCmd -> debug_print "exec_call\n" b; exec_call cfg
    | ReturnCmd -> debug_print "exec_return\n" b; exec_return cfg
    | InOutReturnCmd (str1, str2) -> debug_print "exec_in_out_return\n" b; exec_in_out_return cfg str1 str2
    | QuitCmd -> debug_print "exec_quit\n" b; exec_quit cfg
    | _ -> exec_nop cfg in
  
  let rec exec_all (progs, stks, envs) =
    match (progs, stks, envs) with
    | (prog :: progs', stk :: stks', env :: envs') ->
        (match prog with
        | [] -> exec_all (progs', stks, envs)
        | cmd :: prog' -> 
            let cfg = (prog', progs, progs', stk, stks, stks', env, envs, envs') in
            exec_all (exec_cmd cmd cfg))
    | _ -> () in

  exec_all ([cmds], [[]], [[]]);
  close_out chan

(* ================================================================================ *)

let interpreter ((infn : string), (outfn : string)) : unit =
  let toks = scan_file infn in
  let cmds = parse_tokens toks in
  execute_commands cmds outfn

(* ================================================================================ *)

(* let test (id : string) (infn : string) (expoutfn : string) : unit =
  let outfn = "output.txt" in
  interpreter (infn, outfn);
  let exp = read_file expoutfn in
  let act = read_file outfn in
  if exp = act then
    print_endline ("test " ^ id ^ " passed")
  else
    (print_endline ("test " ^ id ^ " failed");
    print_endline ("==========");
    print_endline ("expected: \n" ^ exp);
    print_endline ("==========");
    print_endline ("actual: \n" ^ act);
    print_endline ("==========");
    let _ = exit 1 in ())

let () =
  test "1.1" "inputs/part1/input1.txt" "outputs/part1/output1.txt";
  test "1.2" "inputs/part1/input2.txt" "outputs/part1/output2.txt";
  test "1.3" "inputs/part1/input3.txt" "outputs/part1/output3.txt";
  test "1.4" "inputs/part1/input4.txt" "outputs/part1/output4.txt";
  test "1.5" "inputs/part1/input5.txt" "outputs/part1/output5.txt";
  test "1.6" "inputs/part1/input6.txt" "outputs/part1/output6.txt";
  test "1.7" "inputs/part1/input7.txt" "outputs/part1/output7.txt";
  test "1.8" "inputs/part1/input8.txt" "outputs/part1/output8.txt";
  test "1.9" "inputs/part1/input9.txt" "outputs/part1/output9.txt";
  test "1.10" "inputs/part1/input10.txt" "outputs/part1/output10.txt"

let () =
  test "2.1" "inputs/part2/input1.txt" "outputs/part2/output1.txt";
  test "2.2" "inputs/part2/input2.txt" "outputs/part2/output2.txt";
  test "2.3" "inputs/part2/input3.txt" "outputs/part2/output3.txt";
  test "2.4" "inputs/part2/input4.txt" "outputs/part2/output4.txt";
  test "2.5" "inputs/part2/input5.txt" "outputs/part2/output5.txt";
  test "2.6" "inputs/part2/input6.txt" "outputs/part2/output6.txt";
  test "2.7" "inputs/part2/input7.txt" "outputs/part2/output7.txt";
  test "2.8" "inputs/part2/input8.txt" "outputs/part2/output8.txt";
  test "2.9" "inputs/part2/input9.txt" "outputs/part2/output9.txt";
  test "2.10" "inputs/part2/input10.txt" "outputs/part2/output10.txt";
  test "2.11" "inputs/part2/input11.txt" "outputs/part2/output11.txt";
  test "2.12" "inputs/part2/input12.txt" "outputs/part2/output12.txt";
  test "2.13" "inputs/part2/input13.txt" "outputs/part2/output13.txt";
  test "2.14" "inputs/part2/input14.txt" "outputs/part2/output14.txt";
  test "2.15" "inputs/part2/input15.txt" "outputs/part2/output15.txt"

let () =
  test "3.1" "inputs/part3/input1.txt" "outputs/part3/output1.txt";
  test "3.2" "inputs/part3/input2.txt" "outputs/part3/output2.txt";
  test "3.3" "inputs/part3/input3.txt" "outputs/part3/output3.txt";
  test "3.4" "inputs/part3/input4.txt" "outputs/part3/output4.txt";
  test "3.5" "inputs/part3/input5.txt" "outputs/part3/output5.txt";
  test "3.6" "inputs/part3/input6.txt" "outputs/part3/output6.txt";
  test "3.7" "inputs/part3/input7.txt" "outputs/part3/output7.txt";
  test "3.8" "inputs/part3/input8.txt" "outputs/part3/output8.txt";
  test "3.9" "inputs/part3/input9.txt" "outputs/part3/output9.txt";
  test "3.10" "inputs/part3/input10.txt" "outputs/part3/output10.txt"

let () =
  test "t5" "inputs/tests/input5.txt" "outputs/tests/output5.txt";
  test "t6" "inputs/tests/input6.txt" "outputs/tests/output6.txt";
  test "t7" "inputs/tests/input7.txt" "outputs/tests/output7.txt";
  test "t8" "inputs/tests/input8.txt" "outputs/tests/output8.txt";
  test "t9" "inputs/tests/input9.txt" "outputs/tests/output9.txt" *)


(* let () =
  test "ex" "input.txt" "empty.txt";     *)

(* ================================================================================ *)