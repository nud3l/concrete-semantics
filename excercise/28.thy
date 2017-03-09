theory 28
  imports Main
begin
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse c [] = []" |
  "intersperse c [v] = [v]" |
  "intersperse c (v#t) = v # c # (intersperse c t)"
  
(*value "intersperse(2,[]) = []"*)

(*value "intersperse(2,[4]) = [4]"*)

value "intersperse(2, [4,1,5,8])"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule:intersperse.induct)
    apply(auto)
  done  
end