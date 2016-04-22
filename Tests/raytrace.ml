(* Simple direct translation of raytrace.cbv to OCaml *)
let factor = 4096;;
let sqrfactor = 64
let mul = fun xy -> ((fst  xy) * (snd  xy))/factor

let getX = fun xyz -> fst  xyz
let getY = fun xyz -> fst  (snd  xyz)
let getZ = fun xyz -> snd  (snd  xyz)

let lightX = factor*20 / 10
let lightY = 0 - factor*30 /10
let lightZ = 0 - factor*50 /10

let sphereCount = 4
let printi x =
  output_string stdout (string_of_int x);
  output_char stdout '\n'

let main =
  let sphereX = fun i ->
    if i = 0 then factor*(-7)/10
    else if i = 1 then factor*12/10
    else if i = 2 then factor*5/10
    else 0 in
  let sphereY = fun i ->
    if i = 0 then 0
    else if i = 1 then factor*0/10
    else if i = 2 then factor*7/10
    else factor*50/10 in
  let sphereZ = fun i ->
    if i = 0 then 0
    else if i = 1 then factor*3/10
    else if i = 2 then factor*(0-4)/10
    else factor*20/10 in
  let sphereR = fun i ->
    if i = 0 then factor*11/10
    else if i = 1 then factor*6/10
    else if i = 2 then factor*5/10
    else factor*40/10 in
  let sphereRed = fun i ->
    if i = 0 then factor*5/10
    else if i = 1 then factor*0/10
    else if i = 2 then factor*0/10
    else factor*3/10 in
  let sphereGreen = fun i ->
    if i = 0 then factor*1/10
    else if i = 1 then factor*0/10
    else if i = 2 then factor*5/10
    else factor*3/10 in
  let sphereBlue = fun i ->
    if i = 0 then 0
    else if i = 1 then factor*4/10
    else if i = 2 then factor*0/10
    else factor*3/10 in
  let sphereRefl = fun i ->
    if i = 0 then factor*2/10
    else if i = 1 then factor*3/10
    else if i = 2 then factor*1/10
    else factor*2/10 in

  let sqrt = fun x ->
    let rec sqrt' v =
      let i0 = fst  v in
      let i = snd  v in
      if 0 < i then
        if i < i0 then sqrt' (i, (i + x/i)/2) else i
      else i in
    sqrt' (x, (x+1)/2) in

  let andalso = fun bc ->
    if fst  bc then snd  bc else false in

  let closestIntersection = fun v ->
    let base = fst  v in
    let dir = snd  v in
    let rec closestIntersection v =
      let i = fst  v in
      let intersectionTime = fst  (snd  v) in
      let intersectionSphere = snd  (snd  v) in
      if i < sphereCount then
        let a = mul(getX dir, getX dir) + mul(getY dir, getY dir) +
                mul(getZ dir, getZ dir) in
        let b = 2 * (  (mul(getX dir, (getX base) - (sphereX i)))
                       + (mul(getY dir, (getY base) - (sphereY i)))
                       + (mul(getZ dir, (getZ base) - (sphereZ i)))) in
        let c = mul((getX base) - (sphereX i), (getX base) - (sphereX i))
                + mul((getY base) - (sphereY i), (getY base) - (sphereY i))
                + mul((getZ base) - (sphereZ i), (getZ base) - (sphereZ i))
                - mul(sphereR(i), sphereR(i)) in
        let discriminant = mul(b,b) - 4 * mul(a,c) in
        let iTS =
          if (discriminant < 0) then
            (intersectionTime, intersectionSphere)
          else
            let t1 = (0 - b + sqrfactor * sqrt(discriminant)) / 2 in
            if andalso(280 < t1, t1 < intersectionTime) then
              let t2 = (0 - b - sqrfactor * sqrt(discriminant)) / 2 in
              if andalso(280 < t2, t2 < t1) then (t2, i)
              else (t1, i)
            else
              let t2 = (0 - b - sqrfactor * sqrt(discriminant)) / 2 in
              if andalso(280 < t2, t2 < intersectionTime) then (t2, i)
              else (intersectionTime, intersectionSphere) in
        closestIntersection (i+1, iTS)
      else
        (intersectionTime, intersectionSphere) in
    closestIntersection (0, (10000 * factor, 0-1)) in

  let normalise = fun v ->
    let x = fst  v in
    let y = fst  (snd  v) in
    let z = snd  (snd  v) in
    let mag = sqrfactor * sqrt(mul(x,x) + mul(y,y) + mul(z,z)) in
    if 0 < mag then
      (mag, (factor*x/mag, (factor*y/mag, factor*z/mag)))
    else
      (0, (0, (0, 0))) in

  let dot = fun vv1 ->
    let v = fst  vv1 in
    let v1 = snd  vv1 in
    let x = fst  v in
    let y = fst  (snd  v) in
    let z = snd  (snd  v) in
    let x1 = fst  v1 in
    let y1 = fst  (snd  v1) in
    let z1 = snd  (snd  v1) in
    mul(x,x1) + mul(y,y1) + mul(z,z1) in

  let reflectedRay = fun v ->
    let inBase = fst  (fst  v) in
    let inDir = snd  (fst  v) in
    let i = snd  v in
    let normal = (getX inBase - (sphereX i),
                  (getY inBase - (sphereY i),
                   getZ inBase - (sphereZ i))) in
    let normal1 = snd  (normalise(normal)) in
    let k = (0-2)*dot(normal1, inDir) in
    let out = (mul(k, getX normal1) + (getX inDir),
               (mul(k, getY normal1) + (getY inDir),
                mul(k, getZ normal1) + (getZ inDir))) in
    let out1 = snd  (normalise(out)) in
    (out1, normal1) in

  let _ =
    let _ = print_string "P3\n400\n400\n256\n" in
    let rec y_loop y =
      if y < 400 then
        let rec x_loop x =
          if x < 400 then
            let rayBase = ((x * factor) / 100 - 2 * factor,
                           ((y * factor)/ 100 - 2 * factor,
                            (0 - 2) * factor)) in
            let rayDir = (0, (0, factor)) in
            let ray = (rayBase, rayDir) in
            let rec clevel v =
              let level = fst  v in
              let v1 = snd  v in
              let red = fst  v1 in
              let v2 = snd  v1 in
              let green = fst  v2 in
              let v3 = snd  v2 in
              let blue = fst  v3 in
              let v4 = snd  v3 in
              let colourfactor = fst  v4 in
              let v5 = snd  v4 in
              let rayBase = fst  v5 in
              let rayDir = snd  v5 in
              if level < 10 then
                let v6 = closestIntersection ray in
                let intersectionTime = fst  v6 in
                let intersectionSphere = snd  v6 in
                if intersectionSphere < 0 then (
                  let _ = printi (red* 256/ factor) in
                  let _ = printi (green* 256/ factor) in
                  printi (blue* 256/ factor)
                ) else
                  let red = red + mul(4*colourfactor/10,
                                      sphereRed(intersectionSphere)) in
                  let green = green + mul(4*colourfactor/10,
                                          sphereGreen(intersectionSphere)) in
                  let blue = blue + mul(4*colourfactor/10,
                                        sphereBlue(intersectionSphere)) in
                  let intersectionBase =
                    (getX rayBase + mul(intersectionTime, getX rayDir),
                     (getY rayBase + mul(intersectionTime, getY rayDir),
                      getZ rayBase + mul(intersectionTime, getZ rayDir))) in
                  let intersectionDir = rayDir in
                  let _ (* rayToViewerBase *) = intersectionBase in
                  let rayToViewerDir =
                    ((getX rayBase) - (getX intersectionBase),
                     ((getY rayBase) - (getY intersectionBase),
                      (getZ rayBase) - (getZ intersectionBase))) in
                  let v7 = reflectedRay(
                      (intersectionBase, intersectionDir),
                      intersectionSphere) in
                  let out = fst  v7 in
                  let normal = snd  v7 in
                  let rayBase1 = intersectionBase in
                  let rayDir1 = out in
                  let rayToLightBase = intersectionBase in
                  let rayToLightDir =
                    (lightX - (getX intersectionBase),
                     (lightY - (getY intersectionBase),
                      lightZ - (getZ intersectionBase))) in
                  let v8 = normalise(rayToLightDir) in
                  let mag = fst  v8 in
                  let rayToLightDirNormalised = snd  v8 in
                  let v9 =
                    if 0 < mag then
                      let v10 =
                        closestIntersection(rayToLightBase,
                                            rayToLightDirNormalised) in
                      let _ (*intersectionTime1*) = fst v10 in
                      let intersectionSphere1 = snd v10 in
                      if intersectionSphere1 < 0 then
                        let c = dot(rayToLightDirNormalised, normal) in
                        let red = red +
                                  mul(mul(c, colourfactor),
                                      sphereRed(intersectionSphere)) in
                        let green = green +
                                    mul(mul(c, colourfactor),
                                        sphereGreen(intersectionSphere)) in
                        let blue = blue +
                                   mul(mul(c, colourfactor),
                                       sphereBlue(intersectionSphere)) in
                        let rayFromLightBase = intersectionBase in
                        let rayFromLightDir =
                          ((getX intersectionBase) - lightX,
                           ((getY intersectionBase) - lightY,
                            (getZ intersectionBase) - lightZ)) in
                        let rayFromLightDirNormalised = snd  (normalise(rayFromLightDir)) in
                        let out1 = fst  (
                            reflectedRay(
                              (rayFromLightBase, rayFromLightDirNormalised),
                              intersectionSphere)) in
                        let rayToViewerDirNormalised = snd  (normalise(rayToViewerDir)) in
                        let out1N = snd  (normalise(out1)) in
                        let spec = dot(rayToViewerDirNormalised, out1N) in
                        let spec1 = if (spec < 0) then 0 else spec in
                        let spec2 = (spec1 * spec1) / factor in
                        let spec3 = (spec2 * spec2) / factor in
                        let spec4 = (spec3 * spec3) / factor in
                        let red = red +
                                  mul(mul(spec4, colourfactor),
                                      sphereRefl(intersectionSphere)) in
                        let green = green +
                                    mul(mul(spec4, colourfactor),
                                        sphereRefl(intersectionSphere)) in
                        let blue = blue +
                                   mul(mul(spec4, colourfactor),
                                       sphereRefl(intersectionSphere)) in
                        (red, (green, blue))
                      else (red, (green, blue))
                    else (red, (green, blue)) in
                  let red = fst  v9 in
                  let green = fst  (snd  v9) in
                  let blue = snd  (snd  v9) in
                  let colourfactor1 = mul(colourfactor,
                                          sphereRefl(intersectionSphere)) in
                  clevel (level + 1, (red, (green, (blue,
                                                    (colourfactor1, (rayBase1, rayDir1))))))
              else
                let _ = if red < 0 then printi 0 else printi (red * 256/ factor) in
                let _ = if green < 0 then printi 0 else printi (green * 256/ factor) in
                if blue < 0 then printi 0 else printi (blue * 256/ factor) in
            let _ = clevel (0, (0, (0, (0, (factor, (rayBase, rayDir)))))) in
            x_loop (x+1)
          else
            42 in
        let _ = x_loop 0 in
        y_loop (y+1)
      else 42 in
    y_loop 0 in
  0
