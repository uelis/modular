let cons x xs =
  fun i -> if i = 0 then x else xs (i-1)

let head xs = xs 0

let tail xs = fun i -> xs (i+1)

let rec aux n = fun i -> cons 1 (cons n (cons 1 (aux (n+2)))) i

let eContFrac = cons 2 (aux 2)

let signum x = if x < 0 then 0-1 else if x = 0 then 0 else 1
let abs x =if x < 0 then 0-x else x
let neg x = if x then false else true
let andalso x y =
  if x then (if y then true else false) else false
let orelse x y =
  if x then true else y

let rec ratTrans av bv cv dv xs iv =
             let qv = if dv = 0 then 1 else bv / dv in
             if andalso (orelse (signum cv = signum dv) (abs cv < abs dv))
                      (andalso ((cv+dv)*qv < av+bv+1)
                           (av+bv < (cv+dv)*qv + (cv+dv)))
             then
                  (if iv = 0 then qv else
                      ratTrans cv dv (av-qv*cv) (bv-qv*dv) xs (iv-1))
             else
                 let xv = xs 0 in
                 ratTrans bv (av+xv*bv) dv (cv+xv*dv) (tail xs) iv

let rec toDigits l i =
   if i = 0 then l i else toDigits (ratTrans 10 0 0 1 (tail l)) (i-1)

let e = toDigits eContFrac

let main =
  for i = 0 to 9 do
    print_int (e i)
  done
