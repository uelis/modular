fun cons x xs =
  fn i => if i = 0 then x else xs (i-1)

fun head xs = xs 0

fun tail xs = fn i => xs (i+1)

fun aux n = fn i => cons 1 (cons n (cons 1 (aux (n+2)))) i

val eContFrac = cons 2 (aux 2)

fun signum x = if x < 0 then 0-1 else if x = 0 then 0 else 1
fun abs x =if x < 0 then 0-x else x
fun neg x = if x then false else true

fun ratTrans av bv cv dv xs iv =
             let val qv = if dv = 0 then 1 else bv div dv in
                 if ((signum cv = signum dv) orelse (abs cv < abs dv)) andalso
                    (((cv+dv)*qv < av+bv+1) andalso
                     (av+bv < (cv+dv)*qv + (cv+dv)))
                 then
                     (if iv = 0 then qv else
                      ratTrans cv dv (av-qv*cv) (bv-qv*dv) xs (iv-1))
                 else
                     let val xv = xs 0 in
                         ratTrans bv (av+xv*bv) dv (cv+xv*dv) (tail xs) iv
                     end
                 end

fun toDigits l i =
   if i = 0 then l i else toDigits (ratTrans 10 0 0 1 (tail l)) (i-1)

val e = toDigits eContFrac
                 
val main =
  let fun loop i =        
        if i < 10 then
            let val _ = printi (e i)
            in loop (i+1) end else ()
  in loop 0
  end
