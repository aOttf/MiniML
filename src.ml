(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
  ("1;", 
   Right (Int 1));
  ("3*(2+4*4);", 
   Right ( Primop
             (Times, [Int(3); Primop
                        (Plus, [Int(2); Primop
                                  (Times, [Int(4);Int(4)]
                                  )])])));
  (valid_program_5, 
   Right ( Let 
             ([Val(Int (1), "x")], 
              Primop 
                (Plus, [Var("x"); Int(5)]))));
  
  (*valid_program_10, 
   Right
     (Let
        ([Val (Let ([Val (Int 10, "ten")], Fn ("y", Some TInt, Var "ten")), "f")],
         Apply (Var "f", Int 55)))*)
  
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, []);
  (Bool true, []);
  (Primop (Plus, [Var("x"); Int 3]), ["x"]);
  
  (Let
     ([Val
         (Rec ("test",
               TArrow(TInt, TArrow (TArrow(TInt, TInt), TInt)),
               Fn
                 ("x", Some TInt,
                  Fn
                    ("f", Some (TArrow (TInt, TInt)), 
                     If (Var ("y"), Var ("z"), Apply (Var "f", Var "x"))))),
          "test")], Int 0), 
   ["y"; "z"]);
                  
  (*progtam 8 *)
  (Let 
     ([Valtuple 
         (Tuple 
            ([Primop (Plus, [Int 2; Int 1]); Primop (Times, [Int 2; Int 50])]),
          ["x"; "y"]
         )
      ], Primop (Times, [Var "y"; Primop (Times, [Var "x"; Var "x"])])
     ), []);
  (*program 10 *)
  (Let
     ([Val 
         (Let 
            ([Val
                (Int 10, "ten")],
             Fn ("y", Some TInt, Var ("ten"))
            ),
          "f")], Apply (Var ("f"), Int 55)
     ), []);
    (* program 9 *)
  (Let
     ([Val
         (Rec ("repeat",
               TArrow (TInt, TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt))),
               Fn
                 ("n", Some TInt,
                  Fn
                    ("f", Some (TArrow (TInt, TInt)),
                     Fn
                       ("x", Some TInt,
                        If (Primop (Equals, [Var "n"; Int 0]), Var "x",
                            Apply
                              (Apply
                                 (Apply (Var "repeat", Primop (Minus, [Var "n"; Int 1])),
                                  Var "f"),
                               Apply (Var "f", Var "x"))))))),
          "repeat")],
      Apply
        (Apply (Apply (Var "repeat", Int 4),
                Fn ("z", Some TInt, Primop (Times, [Var "z"; Int 2]))),
         Int 100)), [])
  
]

(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = 
  let rec fv_d (dl : dec list) (e : exp) : name list = 
    match dl with
    | [] -> free_vars e
            
    | (ByName (e', n))::ds 
    | (Val (e', n))::ds -> 
        union (free_vars e') (delete [n] (fv_d ds e))
          
    | (Valtuple (e', nl))::ds ->
        union (free_vars e') (delete nl (fv_d ds e))
  in
  match e with
  | Int i -> [] 
  | Bool b -> []
  | If (e1, e2, e3) -> 
      union (free_vars e1) (union (free_vars e2) (free_vars e3))
  | Primop (op, elist) -> union_list (List.map free_vars elist)
  | Tuple (elist) -> union_list (List.map free_vars elist)
  | Fn (v, _, e) -> delete [v] (free_vars e)
  | Rec (f, t, e) -> delete [f] (free_vars e)
  | Let (dlist, e) -> fv_d dlist e
  | Apply (e1, e2) -> union (free_vars e1) (free_vars e2)
  | Var (x) -> [x]
  | Anno (e, t) -> free_vars e
             


let unused_vars_tests : (exp * name list) list = [
  
  (*program 9*)
  (Let
     ([Val
         (Rec ("repeat",
               TArrow 
                 (TInt, TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt))),
               Fn
                 ("n", Some TInt,
                  Fn
                    ("f", Some (TArrow (TInt, TInt)),
                     Fn
                       ("x", Some TInt,
                        If (Primop (Equals, [Var "n"; Int 0]), Var "x",
                            Apply
                              (Apply
                                 (Apply 
                                    (Var "repeat", 
                                     Primop (Minus, [Var "n"; Int 1])),
                                  Var "f"),
                               Apply (Var "f", Var "x"))))))),
          "repeat")],
      Apply
        (Apply (Apply (Var "repeat", Int 4),
                Fn ("z", Some TInt, Primop (Times, [Var "z"; Int 2]))),
         Int 100)),
   []);
  
    (*valid program 10*)
  (Let
     ([Val
         (Let ([Val (Int 10, "ten")],
               Anno (Fn ("y", None, Var "ten"), TArrow (TInt, TInt))),
          "f")],
      Apply (Var "f", Int 55)),
   ["y"]); 
  
    (*program 1*)
  (Let
     ([Val
         (Rec ("apply", TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt)),
               Fn
                 ("f", Some (TArrow (TInt, TInt)),
                  Fn ("x", Some TInt, Apply (Var "f", Var "x")))),
          "apply")],
      Apply
        (Apply (Var "apply", Fn ("x", None, Primop (Times, [Var "x"; Int 3]))),
         Int 100)),
   []);
  
   (*program 2*)
  (Primop (Plus, [Primop (Times, [Int 10; Int 10]); Int 33]), []);

  (*program 3*)
  (Let
     ([Val
         (Rec ("fact", TArrow (TInt, TInt),
               Fn
                 ("x", Some TInt,
                  If (Primop (Equals, [Var "x"; Int 0]), Int 1,
                      Primop (Times,
                              [Var "x"; Apply (Var "fact", Primop (Minus, [Var "x"; Int 1]))])))),
          "fact")],
      Apply (Var "fact", Int 5)),
   []);
  
(*program 4*)
  (Anno (If (Bool true, Int 3, Int 5), TInt), []);

  (*program 5*)
  (Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 5])), []);
(*program 6*)

(*program 7*)

(*program 8*)
]

(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = 
  match e with
  
  | Int _ | Bool _ | Var _ -> []
                              
  | If (e1, e2, e3) -> 
      union (unused_vars e1) (union (unused_vars e2) (unused_vars e3))
        
  | Primop (_, elist) 
  | Tuple (elist) -> union_list (List.map unused_vars elist)
                       
  | Fn (n, _, e) -> union (delete (free_vars e) [n]) (unused_vars e)
  | Rec (n, _, e) -> unused_vars e 
        
  | Let (dlist, e) -> begin match dlist with
      | [] -> unused_vars e
                
      | (ByName (e', x))::ds
      | (Val (e', x))::ds -> 
          (union 
             (delete (free_vars e) [x]) 
             (union (unused_vars e') 
                (unused_vars (Let (ds, e)))))
            
      | (Valtuple (e', nl))::ds -> 
          (union 
             (delete (free_vars e) nl) 
             (union (unused_vars e') 
                (unused_vars (Let (ds, e)))))
    end
  | Apply (e1, e2) -> union (unused_vars e1) (unused_vars e2) 
  | Anno (e, _) -> unused_vars e
  
let subst_tests : (((exp * name) * exp) * exp) list = [
]

(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  let set = union [x] (free_vars e') in
  
  let rec fold_left_map (f : 'a -> 'b -> 'a * 'c) (a : 'a) (l : 'b list) : ( 'a * ('c list)) = 
    match l with
    | [] -> (a, [])
    | x::xs -> let (a, c) = f a x in
        let (a, cs) = fold_left_map f a xs in
        (a, c::cs)
  in
  
(* only pass Let (_,_) to e *)
  let s_fold (e : exp) (n : name) : (exp * name) =  
    if member n set then
      let n' = fresh_var n in
      (subst (Var n', n) e, n')
    else (e, n)
         
  in
     
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (op, es) -> Primop (op, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Let (dl, e2) -> 
      begin match dl with
        | [] -> Let ([], subst (e', x) e2)
                  
        | (ByName (e, n))::ds 
        | (Val (e, n))::ds -> if member n set
            then 
              let n' = fresh_var n in
              begin match subst (e', x) (subst (Var n', n) (Let(ds, e2))) with
                | Let(ds', e2') -> Let ((Val (subst (e', x) e, n'))::ds', e2')
                | _ -> stuck "_"
              end
            else 
              begin match subst (e', x) (Let(ds, e2)) with
                | Let(ds', e2') -> Let ((Val (subst (e', x) e, n))::ds', e2')
                | _ -> stuck "_"
              end
              
        | (Valtuple (el, nl))::ds -> 
            let (lete', nl') = 
              fold_left_map s_fold (Let (ds, e2)) nl in
            begin match subst (e', x) lete' with
              | Let (ds', e2') -> 
                  Let ((Valtuple (subst (e', x) el, nl'))::ds', e2')
              | _ -> stuck "_"
            end
      end
  
  | Apply (e1, e2) -> 
      Apply (subst (e', x) e1, subst (e', x) e2)
                        
  | Fn (y, t, e) -> if member y set 
      then let y' = fresh_var y in 
        Fn (y', t, subst (e', x) (subst (Var y', y) e))
      else Fn (y, t, subst (e', x) e) 
          
  | Rec (y, t, e) -> if member y set
      then let y' = fresh_var y in 
        Rec (y', t, subst (e', x) (subst (Var y', y) e))
      else Rec (y, t, subst (e', x) e)
  
let eval_tests : (exp * exp) list = [
  (*valid program 1*)
  (Let
     ([Val
         (Rec ("apply", TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt)),
               Fn
                 ("f", Some (TArrow (TInt, TInt)),
                  Fn ("x", Some TInt, Apply (Var "f", Var "x")))),
          "apply")],
      Apply
        (Apply (Var "apply", Fn ("x", None, Primop (Times, [Var "x"; Int 3]))),
         Int 100)),
   Int 300);
  (*valid program 2*)
  (Primop (Plus, [Primop (Times, [Int 10; Int 10]); Int 33]),
   Int 133);
  (*valid program 3*)
  (Let
     ([Val
         (Rec ("fact", TArrow (TInt, TInt),
               Fn
                 ("x", Some TInt,
                  If (Primop (Equals, [Var "x"; Int 0]), Int 1,
                      Primop (Times,
                              [Var "x"; Apply (Var "fact", Primop (Minus, [Var "x"; Int 1]))])))),
          "fact")],
      Apply (Var "fact", Int 5)),
   Int 120);
  (*valid program 4*)
  (Anno (If (Bool true, Int 3, Int 5), TInt),
   Int 3);
  (*valid program 5*)
  (Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 5])),
   Int 6);
  (*valid program 6*)
  (Let ([Val (Bool true, "x")],
        Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 5]))),
   Int 6);
  (*valid program 7*)
  (Let ([ByName (Int 3, "x")], Primop (Plus, [Var "x"; Int 1])),
   Int 4);
  (*valid program 8*)
  (Let
     ([Valtuple
         (Tuple [Primop (Plus, [Int 2; Int 1]); Primop (Times, [Int 2; Int 50])],
          ["x"; "y"])],
      Primop (Times, [Primop (Times, [Var "x"; Var "x"]); Var "y"])),
   Int 900);
  (*valid program 9*)
  (Let
     ([Val
         (Rec ("repeat",
               TArrow (TInt, TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt))),
               Fn
                 ("n", Some TInt,
                  Fn
                    ("f", Some (TArrow (TInt, TInt)),
                     Fn
                       ("x", Some TInt,
                        If (Primop (Equals, [Var "n"; Int 0]), Var "x",
                            Apply
                              (Apply
                                 (Apply (Var "repeat", Primop (Minus, [Var "n"; Int 1])),
                                  Var "f"),
                               Apply (Var "f", Var "x"))))))),
          "repeat")],
      Apply
        (Apply (Apply (Var "repeat", Int 4),
                Fn ("z", Some TInt, Primop (Times, [Var "z"; Int 2]))),
         Int 100)),
   Int 1600);
  (*valid program 10*)
  (Let
     ([Val
         (Let ([Val (Int 10, "ten")],
               Anno (Fn ("y", None, Var "ten"), TArrow (TInt, TInt))),
          "f")],
      Apply (Var "f", Int 55)),
   Int 10);
]

(* Q4  : Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
  
    let eval_conj op args = 
      match (op, args) with
      | (And, [Bool b1; Bool b2]) -> Some (Bool (b1 && b2))
      | (Or, [Bool b1; Bool b2]) -> Some (Bool (b1 || b2))
      | _ -> None
    in 
    
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn (x, t, e)
      | Apply (e1, e2) -> begin match eval e1 with
          | Fn (x, t, e) -> 
              eval (subst ((eval e2), x) e)
          | _ -> stuck " The first expression for Apply should be a function "
        end
      | (Rec (f, t, e)) as e' -> eval (subst (e', f) e) 

      | Primop (And, es) ->
          let vs = List.map eval es in
          begin match eval_conj And vs with
            | None -> stuck "Wrong arguments to logical operation"
            | Some v -> v
          end 
      | Primop (Or, es) ->
          let vs = List.map eval es in
          begin match eval_conj Or vs with
            | None -> stuck "Wrong arguments to logical operation"
            | Some v -> v
          end
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Wrong arguments to primitive operation"
            | Some v -> v
          end

      | Let (dl, e) -> 
          begin match dl with
            | [] -> eval e
            | (Val (e', n))::ds -> eval (subst (eval e', n) (Let(ds, e)))
            | (ByName (e', n))::ds -> eval (subst (e', n) (Let(ds, e)))
            | (Valtuple (e', nl))::ds -> 
                begin match e' with
                  | Tuple(el) ->
                      if List.length el = List.length nl then
                        eval (List.fold_left 
                                (fun (e:exp) ((e', n'):exp*name) : exp -> subst (e', n') e)
                                (Let (ds, e))
                                (List.combine (List.map eval el) nl) 
                             )
                      else stuck "The form of ValTuple is not correct"
  
                  | _ -> stuck "The form of ValTuple is not correct"
                end
          end
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result

let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let rec unify (ty1 : typ) (ty2 : typ) : unit = 

	(* only pass (ref None) to ty1, 
	meaning ty1 hasn't been assigned any concrete type value
	the goal is to see whether Var(ty1) is in FV(ty2) *)
  let rec notin_fv (ty1 : (typ option) ref) (ty2 : typ) : bool =
    match ty2 with
    | TInt | TBool -> true
      
    | TProduct tl -> List.for_all (notin_fv ty1) tl
    | TArrow (t1, t2) -> (notin_fv ty1 t1)&&(notin_fv ty1 t2)
                                          
    | TVar (x) -> 
        begin match (!ty1, !x) with
          | (None, None) -> not (ty1 == x)
          | (None, Some v) -> notin_fv ty1 v
          | _ -> type_fail "The function is only used for ty1 = (ref None)!"
        end
  in
  
  match (ty1, ty2) with
  | (TInt , TInt) 
  | (TBool, TBool) -> ()
                      
  | (TArrow (t1, t2), TArrow (s1, s2)) -> (unify t1 s1; unify t2 s2) 
  | (TProduct tl1, TProduct tl2) -> 
      begin match (tl1, tl2) with
        | ([], []) -> ()
        | (t1'::tl1, t2'::tl2) -> 
            (unify t1' t2'; 
             unify (TProduct tl1) (TProduct tl2))
        | _ -> type_fail "cannot unify"
      end
    
  | (TVar x, TVar y) -> 
      begin match (!x, !y) with
        |  (None, None) -> if (notin_fv x (TVar y)) then 
              let ftv = fresh_tvar () in
              (x := Some ftv; y := Some ftv)
            else ()
       
        |  (Some v, None) -> if (notin_fv y (TVar x)) then 
              y := Some v
            else type_fail "cannot unify"
        |  (None, Some v) -> if (notin_fv x (TVar y)) then 
              x := Some v
            else type_fail "cannot unify"
    
        |  (Some vx, Some vy) -> unify vx vy
      end

  | (TVar x, t)
  | (t, TVar x) -> 
      begin match !x with
        | None -> if (notin_fv x t) then 
              x := Some t
            else type_fail "cannot unify"
        | Some v -> unify v t
      end
  
  | _ -> type_fail "cannot unify"

 
let infer_tests : ((context * exp) * typ) list = [
  (* valid program 1 *)
  ((Ctx [],Let
      ([Val
          (Rec ("apply", TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt)),
                Fn
                  ("f", Some (TArrow (TInt, TInt)),
                   Fn ("x", Some TInt, Apply (Var "f", Var "x")))),
           "apply")],
       Apply
         (Apply (Var "apply", Fn ("x", Some TInt, Primop (Times, [Var "x"; Int 3]))),
          Int 100))),
   TInt);
  
  (* valid program 2 *)
  ((Ctx [],Primop (Plus, [Primop (Times, [Int 10; Int 10]); Int 33]) ), 
   TInt);
  (* valid program 3 *)
  ((Ctx [], Let
      ([Val
          (Rec ("fact", TArrow (TInt, TInt),
                Fn
                  ("x", Some TInt,
                   If (Primop (Equals, [Var "x"; Int 0]), Int 1,
                       Primop (Times,
                               [Var "x"; Apply (Var "fact", Primop (Minus, [Var "x"; Int 1]))])))),
           "fact")],
       Apply (Var "fact", Int 5))), 
   TInt);
  (* valid program 4 *)
  ((Ctx [], Anno (If (Bool true, Int 3, Int 5), TInt)), 
   TInt);
  (* valid program 5 *)
  ((Ctx [], Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 5])) ), 
   TInt);
  (* valid program 6 *)
  ((Ctx [], Let ([Val (Bool true, "x")],
                 Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 5]))) ), 
   TInt);
  (* valid program 7 *)
  ((Ctx [], Let ([ByName (Int 3, "x")], Primop (Plus, [Var "x"; Int 1]))), 
   TInt);
  (* valid program 8 *)
  ((Ctx [], Let
      ([Valtuple
          (Tuple [Primop (Plus, [Int 2; Int 1]); Primop (Times, [Int 2; Int 50])],
           ["x"; "y"])],
       Primop (Times, [Primop (Times, [Var "x"; Var "x"]); Var "y"]))), 
   TInt);
  (* valid program 9 *)
  ((Ctx [], Let
      ([Val
          (Rec ("repeat",
                TArrow (TInt, TArrow (TArrow (TInt, TInt), TArrow (TInt, TInt))),
                Fn
                  ("n", Some TInt,
                   Fn
                     ("f", Some (TArrow (TInt, TInt)),
                      Fn
                        ("x", Some TInt,
                         If (Primop (Equals, [Var "n"; Int 0]), Var "x",
                             Apply
                               (Apply
                                  (Apply (Var "repeat", Primop (Minus, [Var "n"; Int 1])),
                                   Var "f"),
                                Apply (Var "f", Var "x"))))))),
           "repeat")],
       Apply
         (Apply (Apply (Var "repeat", Int 4),
                 Fn ("z", Some TInt, Primop (Times, [Var "z"; Int 2]))),
          Int 100))), 
   TInt);
  (* valid program 10 *)
  ((Ctx [], Let
      ([Val
          (Let ([Val (Int 10, "ten")],
                Anno (Fn ("y", None, Var "ten"), TArrow (TInt, TInt))),
           "f")],
       Apply (Var "f", Int 55))), 
   TInt);
]

let rec infer (ctx : context) (e : exp) : typ = 

  match e with
  | Int _ -> TInt
  | Bool _ -> TBool
  | Var x -> ctx_lookup ctx x
  | Anno (_,t) -> t
  
  | If (e1, e2, e3) -> 
      (unify (infer ctx e1) TBool; let t = infer ctx e2 in 
       unify t (infer ctx e3);t)  
          
  | Primop (op, el) -> 
      begin match (op, el) with
        | (Negate, [e]) ->(unify (infer ctx e) TInt; TInt)
              
        | (And, [e1; e2])
        | (Or, [e1; e2]) -> 
            (unify (infer ctx e1) TBool; unify (infer ctx e2) TBool; TBool)
              
        | (Plus, [e1; e2])
        | (Minus, [e1; e2])
        | (Times, [e1; e2])
        | (Div, [e1; e2]) -> 
            (unify (infer ctx e1) TInt; unify (infer ctx e2) TInt; TInt)
              
        | (_, [e1; e2]) -> 
            (unify (infer ctx e1) TInt; unify (infer ctx e2) TInt; TBool)
              
        | _ -> type_fail "ill typed"
      end

  | Tuple el -> TProduct (List.map (infer ctx) el)

  | Fn (n, Some t, e) -> TArrow (t, infer (extend ctx (n, t)) e)
  | Fn (n, None, e) -> let tv = fresh_tvar () in 
      TArrow(tv, infer (extend ctx (n, tv)) e) 
  | Rec (f, t, e) -> infer (extend ctx (f, t)) e
  
  | Apply (e1, e2) -> 
      begin match (infer ctx e1) with
        | TArrow (t, t') -> 
            (unify t (infer ctx e2); t')
        | _ -> type_fail "ill typed"
      end
      
  | Let (dl, e) -> 
      begin match dl with
        | [] -> infer ctx e
                
        | (Val (e', x))::ds 
        | (ByName (e', x))::ds -> 
            infer (extend ctx (x, (infer ctx e'))) (Let (ds, e))
                                       
        | (Valtuple (e', nl))::ds -> 
            begin match (infer ctx e') with
              | TProduct tl -> if (List.length tl = List.length nl) then
                    infer (extend_list ctx (List.combine nl tl)) (Let (ds, e))
                  else type_fail "ill typed"
              | _ -> type_fail "ill typed"
            end
      end 
      
(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *             Do not change these functions.               *
 *               They are needed for tests.                 *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output)
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn)
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
