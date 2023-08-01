theory DairyFarm
imports Main
begin

(* expand (n+1)^2 *)
lemma plusone_squared:
  "(n+1) * (n+1) = (n*n) + (n + n + 1)" for n::nat
  apply clarsimp
  done

(* expand `(n+1)^2 mod k` to be entirely in terms of `n mod k` *)
lemma n_plus_one_squared_mod_k:
  "(n+1) * (n+1) mod k = (((n mod k) * (n mod k)) mod k + (n mod k) + (n mod k) + 1) mod k" for n::nat
  apply (subst plusone_squared)
  apply (metis (no_types, opaque_lifting) add.assoc mod_add_left_eq mod_add_right_eq
          mod_mult_left_eq mod_mult_right_eq)
  done

(* expand `n^2 mod k` to be entirely in terms of `n mod k` *)
lemma n_squared_mod_k:
  "(n*n) mod k = ((n mod k) * (n mod k)) mod k" for n::nat
  by (simp add: mod_mult_eq)

lemma mod_range:
  "k > 0 \<Longrightarrow>
  n mod k \<in> {0 ..< k}" for n k :: nat
  by simp

lemma range_20_concrete:
  "{(0::nat) ..< (20::nat)} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19}"
  apply (auto, presburger)
  done

(* any square mod 20 is one of these six options *)
lemma n_squared_mod_20:
  "(n*n) mod 20 \<in> {0, 1, 4, 5, 9, 16}" for n::nat
  apply (induct n)
   apply simp
  apply (subst Suc_eq_plus1)+
  apply (subst n_plus_one_squared_mod_k)
  apply (subst (asm) n_squared_mod_k)
  using mod_range [where k=20, simplified range_20_concrete] apply -
  apply (drule_tac x=n in meta_spec)
  apply simp
  apply (elim disjE)
    apply clarsimp+
  done

thm mod_mod_cancel [symmetric, where b=20 and c=10]

lemma mod_10_mod_20:
  "n mod 10 = n mod 20 mod 10" for n :: nat
  apply (subst mod_mod_cancel; simp)
  done

(* a specific (simple) property about dividing an odd number of times *)
lemma n_squared_div_10_odd_mod_20:
  "(n div 10) mod 2 = 1 \<Longrightarrow>
    n mod 20 \<ge> 10" for n :: nat
  apply (metis le_add1 mod_mult2_eq mult.right_neutral mult_2_right numeral_Bit0)
  done


(* the riddle:
  - you sell all your cows, each for the price of the number of cows you have
  - you buy as many sheep as you can, for $10 each
  - you get an odd number of sheep
  - you buy a goat for all the remaining money
  - how much was the goat?
*)

consts num_of_cows :: nat

definition total_money where
  "total_money \<equiv> num_of_cows * num_of_cows"

definition num_of_sheep where
  "num_of_sheep \<equiv> total_money div 10"

definition price_of_goat where
  "price_of_goat = total_money mod 10"

lemma goat_price:
  "num_of_sheep mod 2 = 1 \<Longrightarrow>
  price_of_goat = 6"
  (* unroll definitions *)
  unfolding price_of_goat_def num_of_sheep_def total_money_def

  (* the number of sheep being odd tells us something about the money mod 20 *)
  apply (drule n_squared_div_10_odd_mod_20)

  (* express the price of the goat in terms of mod 20 *)
  apply (subst mod_mod_cancel [symmetric, where b=20 and c=10], simp)

  (* we know the possible values of the total price mod 20 *)
  using n_squared_mod_20 [where n=num_of_cows] apply -

  (* the assumptions combined will simplify into our goal *)
  apply clarsimp

  done

end