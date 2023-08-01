theory KnightsKnaves
imports Main
begin

datatype man =
   Knight
 | Nave

definition ask :: "man \<Rightarrow> bool \<Rightarrow> bool" where
  "ask m t \<equiv> case m of
                Knight \<Rightarrow> t
              | Nave \<Rightarrow> \<not> t"

(* PART ONE
  You are approached by two people. The first one says to you, "we are both knaves."
  What are they actually?
  (We rephrase a man saying X, to me asking the man "X?" and them responding "yes".)
*)

lemma part_one:
  "ask first_man (first_man = Nave \<and> second_man = Nave) \<Longrightarrow>
  first_man = Nave \<and> second_man = Knight"
  apply (clarsimp simp: ask_def split: man.splits)
  apply (rule man.exhaust [of second_man]; simp)
  done











locale fork =
  fixes truth :: 'tr
  fixes left_path_safe :: bool
  fixes first_man_knight :: bool
  fixes second_man_knight :: bool
  defines second_man_knight_def: "second_man_knight \<equiv> \<not>first_man_knight"
begin


end

end