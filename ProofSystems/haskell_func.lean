def cp {p : Type} : (List (List p)) → List (List p)
  | [] => [[]]
  | xs :: xss => do
    let x ← xs
    let ys ← cp xss
    pure (x :: ys)

def zip {p q : Type} : List p → List q → List (Prod p q)
  | (x::xs), (y::ys) => (x,y) :: zip xs ys
  | _, _ => []

def foldr {a b : Type} (cons : a → b → b) (nil : b) : List a → b
  | [] => nil
  | x::xs => cons x (foldr cons nil xs)
