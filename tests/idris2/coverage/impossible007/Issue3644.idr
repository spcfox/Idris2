export infixr 7 :->
data Mono
  = Nat
  | Bool
  | (:->) Mono Mono

data Expr
  = N Nat
  | B Bool
  | If Expr Expr Expr
  | Le Expr Expr

data IsValue : Expr -> Type where
  VN :
    -------------
    IsValue (N n)
  VB :
    -------------
    IsValue (B b)

data Checks : Expr -> Mono -> Type where
  TN :
    ----------------
    Checks (N n) Nat
  TB :
    -----------------
    Checks (B b) Bool
  TIf :
    Checks e0 Bool ->
    Checks e1 t ->
    Checks e2 t ->
    ----------------------
    Checks (If e0 e1 e2) t
  TLe :
    Checks e1 Nat ->
    Checks e2 Nat ->
    -----------------------
    Checks (Le e1 e2) Bool

evaluate :
  (e : Expr) ->
  (Checks e t) ->
  (v : Expr ** (IsValue v, Checks v t))
evaluate (N n) TN = (N n ** (VN, TN))
evaluate (B b) TB = (B b ** (VB, TB))
evaluate (If e0 e1 e2) (TIf d0 d1 d2) with (evaluate e0 d0)
  _ | (B True ** _) = evaluate e1 d1
  _ | (B False ** _) = evaluate e2 d2
  _ | (N _ ** (_, d0')) impossible
  _ | (If _ _ _ ** (p0, _)) impossible
  _ | (Le _ _ ** (p0, _)) impossible
evaluate (Le e1 e2) (TLe d1 d2) with (evaluate e1 d1, evaluate e2 d2)
  _ | ((N v1 ** _), (N v2 ** _)) = (B (v1 <= v2) ** (VB, TB))
  _ | ((N v1 ** _), (B _ ** (_, d2'))) impossible
  _ | ((N v1 ** _), (If _ _ _ ** (p2, _))) impossible
  _ | ((N v1 ** _), (Le _ _ ** (p2, _))) impossible
  _ | ((B _ ** (_, d1')), _) impossible
  _ | ((If _ _ _ ** (p1, _)), _) impossible
  _ | ((Le _ _ ** (p1, _)), _) impossible
