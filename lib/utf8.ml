let length s =
  let rec aux n k res =
    if n = 0 then res
    else
      let c = Char.code (String.get s k) in
      let d =
        if c < 0x80 then 1
        else if c < 0xc0 then failwith "bad code"
        else if c < 0xe0 then 2
        else if c < 0xf0 then 3
        else if c < 0xf8 then 4
        else if c < 0xfc then 5
        else if c < 0xfe then 6
        else failwith "bad code"
      in
      aux (n - d) (k + d) (res + 1)
  in
  aux (String.length s) 0 0
