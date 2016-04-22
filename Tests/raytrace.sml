(* Simple direct translation of raytrace.cbv to SML.
 * 
 * Note: Overflow needs to be switched off for operations on int.
 * With MLton this is possible as follows:
 * 
 *  mlton -const 'MLton.detectOverflow false' raytrace.sml 
 * 
*)
val factor =  4096
val sqrfactor =  64
val mul = fn (xy : int * int) =>
             ((#1  xy) * (#2  xy)) div factor

val getX = fn (xyz : int * (int * int)) => #1  xyz
val getY = fn (xyz : int * (int * int)) => #1  (#2  xyz)
val getZ = fn (xyz : int * (int * int)) => #2  (#2  xyz)

val lightX = factor*( 20) div ( 10)
val lightY =  0 - factor*( 30) div ( 10)
val lightZ =  0 - factor*( 50) div ( 10)

val sphereCount =  4
fun printi x =
  (TextIO.output (TextIO.stdOut, Int.toString x);
   TextIO.output (TextIO.stdOut, "\n"))

val main =
    let
        val sphereX = fn i =>
                         if i =  0 then factor*(( ~7)) div ( 10)
                         else if i =  1 then factor*( 12) div ( 10)
                         else if i =  2 then factor*( 5) div ( 10)
                         else  0 
        val sphereY = fn i =>
                          if i =  0 then  0
                          else if i =  1 then factor*( 0) div ( 10)
                          else if i =  2 then factor*( 7) div ( 10)
                          else factor*( 50) div ( 10) 
        val sphereZ = fn i =>
                         if i =  0 then  0
                         else if i =  1 then factor*( 3) div ( 10)
                         else if i =  2 then factor*( (~4)) div ( 10)
                         else factor*( 20) div ( 10) 
        val sphereR = fn i =>
                         if i =  0 then factor*( 11) div ( 10)
                         else if i =  1 then factor*( 6) div ( 10)
                         else if i =  2 then factor*( 5) div ( 10)
                         else factor*( 40) div ( 10)
        val sphereRed = fn i =>
                           if i =  0 then factor*( 5) div ( 10)
                           else if i =  1 then factor*( 0) div ( 10)
                           else if i =  2 then factor*( 0) div ( 10)
                           else factor*( 3) div ( 10) 
        val sphereGreen = fn i =>
                             if i =  0 then factor*( 1) div ( 10)
                             else if i =  1 then factor*( 0) div ( 10)
                             else if i =  2 then factor*( 5) div ( 10)
                             else factor*( 3) div ( 10) 
        val sphereBlue = fn i =>
                            if i =  0 then  0
                            else if i =  1 then factor*( 4) div ( 10)
                            else if i =  2 then factor*( 0) div ( 10)
                            else factor*( 3) div ( 10) 
        val sphereRefl = fn i =>
                            if i =  0 then factor*( 2) div ( 10)
                            else if i =  1 then factor*( 3) div ( 10)
                            else if i =  2 then factor*( 1) div ( 10)
                            else factor*( 2) div ( 10) 

        val sqrt = fn x =>
                      let fun sqrt' v =
                            let val i0 = #1  v 
                                val i = #2  v
                            in
                                if ( 0) < i then
                                    if i < i0 then sqrt' (i, (i + x div i) div ( 2)) else i
                                else i
                            end
                      in
                          sqrt' (x, (x+( 1)) div ( 2))
                      end

        val andalso' = fn (bc : bool * bool) =>
                         if #1  bc then #2  bc else false 

        val closestIntersection =
         fn (v : (int * (int * int)) * (int * (int * int))) =>
            let val base = #1  v 
                val dir = #2  v 
                fun closestIntersection v =
                  let val i = #1  v 
                      val intersectionTime = #1  (#2  v) 
                      val intersectionSphere = #2  (#2  v)
                  in
                      if i < sphereCount then
                          let val a = mul(getX dir, getX dir) + mul(getY dir, getY dir) +
                                  mul(getZ dir, getZ dir) 
                              val b = ( 2) * ((mul(getX dir, (getX base) - (sphereX i)))
                                             + (mul(getY dir, (getY base) - (sphereY i)))
                                             + (mul(getZ dir, (getZ base) - (sphereZ i)))) 
                              val c = mul((getX base) - (sphereX i), (getX base) - (sphereX i))
                                      + mul((getY base) - (sphereY i), (getY base) - (sphereY i))
                                      + mul((getZ base) - (sphereZ i), (getZ base) - (sphereZ i))
                                      - mul(sphereR(i), sphereR(i)) 
                              val discriminant = mul(b,b) - ( 4) * mul(a,c) 
                              val iTS =
                                  if (discriminant <  0) then
                                      (intersectionTime, intersectionSphere)
                                  else
                                      let val t1 = ( 0 - b + sqrfactor * sqrt(discriminant))  div  ( 2)
                                      in
                                          if andalso'( 280 < t1, t1 < intersectionTime) then
                                              let val t2 = ( 0 - b - sqrfactor * sqrt(discriminant))  div  ( 2)
                                              in
                                                  if andalso'( 280 < t2, t2 < t1) then (t2, i)
                                                  else (t1, i)
                                              end
                                          else
                                              let val t2 = ( 0 - b - sqrfactor * sqrt(discriminant))  div  ( 2)
                                              in                                                  
                                                  if andalso'( 280 < t2, t2 < intersectionTime) then (t2, i)
                                                  else (intersectionTime, intersectionSphere)
                                              end
                                      end
                          in
                              closestIntersection (i+( 1), iTS)
                          end
                      else
                          (intersectionTime, intersectionSphere)
                  end
            in
                closestIntersection ( 0, (( 10000) * factor,  ~1)) 
            end

        val normalize =
         fn (v : int * (int * int)) =>
            let val x = #1  v 
                val y = #1  (#2  v) 
                val z = #2  (#2  v) 
                val mag = sqrfactor * sqrt(mul(x,x) + mul(y,y) + mul(z,z))
            in
                if  0 < mag then
                    (mag, (factor*x div mag, (factor*y div mag, factor*z div mag)))
                else
                    ( 0, ( 0, ( 0,  0)))
            end

        val dot =
         fn (vv1 : (int * (int * int)) * (int * (int * int))) =>
            let val v = #1  vv1 
                val v1 = #2  vv1 
                val x = #1  v 
                val y = #1  (#2  v) 
                val z = #2  (#2  v) 
                val x1 = #1  v1 
                val y1 = #1  (#2  v1)
                val z1 = #2  (#2  v1)
            in
                mul(x,x1) + mul(y,y1) + mul(z,z1)
            end

        val reflectedRay =
         fn (v : ((int * (int * int)) * (int * (int * int))) * int ) =>
            let val inBase = #1  (#1  v)
                val inDir = #2  (#1  v)
                val i = #2  v
                val normal = (getX inBase - (sphereX i),
                              (getY inBase - (sphereY i),
                               getZ inBase - (sphereZ i))) 
                val normal1 = #2  (normalize(normal)) 
                val k = ( ~2)*dot(normal1, inDir) 
                val out = (mul(k, getX normal1) + (getX inDir),
                           (mul(k, getY normal1) + (getY inDir),
                            mul(k, getZ normal1) + (getZ inDir))) 
                val out1 = #2  (normalize(out)) in
                (out1, normal1)
            end

        val main = 
            let val u = print "P3\n400\n400\n256\n"                              
                fun y_loop y =
                  if y <  400 then
                      let fun x_loop x =
                            if x <  400 then
                                let val rayBase = ((x * factor)  div  ( 100) - ( 2) * factor, ((y * factor) div ( 100) - ( 2) * factor, ( ~2) * factor)) 
                                    val rayDir = ( 0, ( 0, factor)) 
                                    val ray = (rayBase, rayDir) 
                                    fun clevel (v : int * (int * (int * (int * (int * ((int * (int * int)) * (int * (int * int)))))))) =
                                      let val level = #1  v 
                                          val v1 = #2  v 
                                          val red = #1  v1 
                                          val v2 = #2  v1 
                                          val green = #1  v2 
                                          val v3 = #2  v2 
                                          val blue = #1  v3 
                                          val v4 = #2  v3 
                                          val colourfactor = #1  v4 
                                          val v5 = #2  v4 
                                          val rayBase = #1  v5 
                                          val rayDir = #2  v5
                                      in
                                          if level <  10 then
                                              let val v6 = closestIntersection ray 
                                                  val intersectionTime = #1  v6 
                                                  val intersectionSphere = #2  v6
                                              in
                                                  if intersectionSphere <  0 then 
                                                      let val u = printi (red * ( 256) div  factor) 
                                                          val u = printi (green * ( 256) div  factor)
                                                      in
                                                          printi (blue* ( 256) div  factor)
                                                      end
                                                  else
                                                      let val red = red + mul(( 4)*colourfactor div ( 10), sphereRed(intersectionSphere))
                                                          val green = green + mul(( 4)*colourfactor div ( 10), sphereGreen(intersectionSphere)) 
                                                          val blue = blue + mul(( 4)*colourfactor div ( 10), sphereBlue(intersectionSphere)) 
                                                          val intersectionBase = (getX rayBase + mul(intersectionTime, getX rayDir), (getY rayBase + mul(intersectionTime, getY rayDir), getZ rayBase + mul(intersectionTime, getZ rayDir))) 
                                                          val intersectionDir = rayDir 
                                                          val rayToViewerBase = intersectionBase 
                                                          val rayToViewerDir = ((getX rayBase) - (getX intersectionBase), ((getY rayBase) - (getY intersectionBase), (getZ rayBase) - (getZ intersectionBase))) 
                                                          val v7 = reflectedRay((intersectionBase, intersectionDir), intersectionSphere) 
                                                          val out = #1  v7 
                                                          val normal = #2  v7 
                                                          val rayBase1 = intersectionBase 
                                                          val rayDir1 = out 
                                                          val rayToLightBase = intersectionBase 
                                                          val rayToLightDir = (lightX - (getX intersectionBase), (lightY - (getY intersectionBase), lightZ - (getZ intersectionBase)))
                                                          val v8 = normalize rayToLightDir
                                                          val mag = #1  v8 
                                                          val rayToLightDirNormalised = #2  v8 
                                                          val v9 =
                                                              if  0 < mag then
                                                                  let val v10 = closestIntersection(rayToLightBase, rayToLightDirNormalised) 
                                                                      val intersectionTime1 = #1  v10 
                                                                      val intersectionSphere1 = #2  v10
                                                                  in
                                                                      if intersectionSphere1 <  0 then
                                                                          let val c = dot(rayToLightDirNormalised, normal) 
                                                                              val red = red + mul(mul(c, colourfactor), sphereRed(intersectionSphere)) 
                                                                              val green = green + mul(mul(c, colourfactor), sphereGreen(intersectionSphere)) 
                                                                              val blue = blue + mul(mul(c, colourfactor), sphereBlue(intersectionSphere)) 
                                                                              val rayFromLightBase = intersectionBase 
                                                                              val rayFromLightDir = ((getX intersectionBase) - lightX, ((getY intersectionBase) - lightY, (getZ intersectionBase) - lightZ)) 
                                                                              val rayFromLightDirNormalised = #2  (normalize(rayFromLightDir)) 
                                                                              val out1 = #1  (reflectedRay((rayFromLightBase, rayFromLightDirNormalised), intersectionSphere)) 
                                                                              val rayToViewerDirNormalised = #2  (normalize(rayToViewerDir)) 
                                                                              val out1N = #2  (normalize(out1)) 
                                                                              val spec = dot(rayToViewerDirNormalised, out1N) 
                                                                              val spec1 = if (spec <  0) then  0 else spec 
                                                                              val spec2 = (spec1 * spec1)  div  factor 
                                                                              val spec3 = (spec2 * spec2)  div  factor 
                                                                              val spec4 = (spec3 * spec3)  div  factor 
                                                                              val red = red + mul(mul(spec4, colourfactor), sphereRefl(intersectionSphere)) 
                                                                              val green = green + mul(mul(spec4, colourfactor), sphereRefl(intersectionSphere)) 
                                                                              val blue = blue + mul(mul(spec4, colourfactor), sphereRefl(intersectionSphere))
                                                                          in
                                                                              (red, (green, blue))
                                                                          end
                                                                      else
                                                                          (red, (green, blue))
                                                                  end
                                                              else
                                                                  (red, (green, blue))
                                                          val red = #1  v9 
                                                          val green = #1  (#2  v9) 
                                                          val blue = #2  (#2  v9) 
                                                          val colourfactor1 = mul(colourfactor, sphereRefl(intersectionSphere))
                                                      in
                                                          clevel (level + ( 1), (red, (green, (blue, (colourfactor1, (rayBase1, rayDir1))))))
                                                      end 
                                              end
                                          else
                                              let val u1 = if red <  0 then printi ( 0) else printi (red * ( 256) div  factor) 
                                                  val u2 = if green <  0 then printi ( 0) else printi (green * ( 256) div  factor)
                                              in
                                                  if blue <  0 then printi ( 0) else printi (blue * ( 256) div  factor)
                                              end
                                      end 
                                    val u = clevel ( 0, ( 0, ( 0, ( 0, (factor, (rayBase, rayDir))))))
                                in
                                    x_loop (x+( 1))
                                end 
                            else
                                 42
                          val u = x_loop ( 0 )
                      in
                          y_loop (y + ( 1))
                      end 
                  else ( 42 )
            in
                y_loop ( 0)
            end
    in
         0
    end
