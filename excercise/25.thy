theory 25
imports Main
begin
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n)  = Suc n + sum_upto n"

value "sum_upto 4 = 10"
  
lemma discrete_add: "sum_upto n = (n * (n + 1)) div 2"
  apply(induction n)
  apply(auto)
  done   
  
end