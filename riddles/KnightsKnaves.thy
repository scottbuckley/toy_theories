theory KnightsKnaves
imports Main
begin


(* helpers for brevity *)
lemma exI2: "P x y \<Longrightarrow> \<exists>x y. P x y" by blast
lemma exI3: "P x y z \<Longrightarrow> \<exists>x y z. P x y z" by blast

(* KNIGHTS AND KNAVES *)
locale KnightsKnaves begin

datatype man = Knight | Knave

definition ask :: "bool \<Rightarrow> man \<Rightarrow> bool" where
  "ask q m \<equiv> case m of
               Knight \<Rightarrow> q
             | Knave  \<Rightarrow> \<not> q"

(* ask a question relative to the person being asked (questions about "you") *)
abbreviation ask' where "ask' q m \<equiv> ask (q m) m"


(* PART ONE
  You are approached by two people.
  The first one says to you, "we are both knaves."
    What are they actually?
*)

lemma part_one:
  "\<exists>first_man second_man.
  ask (first_man = Knave \<and> second_man = Knave) first_man"
  apply (rule exI2 [where x=Knave and y=Knight])
  apply (simp add: ask_def)
  done

(* PART TWO
  You are approached by two people.
  The first one points to the second and says, "he is a knave."
  The second one then says, "neither of us are knaves."
    What are they actually?
*)

lemma part_two:
  "\<exists>first_man second_man.
  ask (second_man = Knave) first_man \<and>
  ask (first_man \<noteq> Knave \<and> second_man \<noteq> Knave) second_man"
  apply (rule exI2 [where x=Knight and y=Knave])
  apply (simp add: ask_def)
  done


(* PART THREE
  You are approached by three people, Jim, Jon and Joe.
  Jim says, "at least one of the following is true,
               that Joe is a knave or that I am a knight."
  Jon says, "Jim could claim that I am a knave."
  Joe says, "neither Jim nor Jon are knights."
    Who is a knight and who is a knave?
*)

lemma part_three:
  "\<exists>Jim Jon Joe.
  ask (Joe = Knave \<or> Jim = Knight) Jim \<and>
  ask (ask (Jon = Knave) Jim) Jon \<and>
  ask (Jim \<noteq> Knight \<and> Jon \<noteq> Knight) Joe"
  apply (rule exI3 [where x=Knave and y=Knave and z=Knight])
  apply (simp add: ask_def)
  done


(* PART FOUR
  You come to a fork in the road with one man standing before each path.
  You know that one of them is a knight, and the other is a knave.
  You also know that one path leads to freedom, and the other path leads to certain death.
    You can ask one of the men one question.
    What do you ask to determine the path to freedom?
*)

lemma part_four:
  "\<exists>question.
  first_man \<noteq> second_man \<longrightarrow>
  solution = (ask' question first_man) \<longrightarrow>
  solution = left_path_safe"
  apply (rule exI [where x="ask left_path_safe"])
  apply (clarsimp simp: ask_def split:man.splits)
  done

lemma part_four_alternative_solution:
  "\<exists>question.
  first_man \<noteq> second_man \<longrightarrow>
  (ask' question first_man) = left_path_safe"
  apply (rule exI [where x="\<lambda>_. \<not> ask left_path_safe second_man"])
  apply (clarsimp simp: ask_def split:man.splits)
  done

end

(* KNIGHTS, KNAVES, AND SPIES *)

locale KnightsKnavesSpies begin

datatype man =
   Knight
 | Knave
 | Spy

definition ask :: "bool \<Rightarrow> man \<Rightarrow> bool" where
  "ask q m \<equiv> case m of
                Knight \<Rightarrow> q
              | Knave  \<Rightarrow> \<not> q
              | Spy    \<Rightarrow> True"

(* ask a question relative to the person being asked (questions about "you") *)
abbreviation ask' where "ask' q m \<equiv> ask (q m) m"


(* PART FIVE
  You are approached by three people wearing different colored clothes.
  You know that one is a knight, one is a knave, and one is a spy.
  They speak in the following order:
  - The man wearing blue says, "I am a knight."
  - The man wearing red says, "He speaks the truth."
  - The man wearing green says, "I am a spy."
    Who is the knight, who is the knave, and who is the spy?
*)

lemma part_five:
  "\<exists>blue_man red_man green_man.
  blue_man \<noteq> red_man \<and> red_man \<noteq> green_man \<and> green_man \<noteq> blue_man \<and>
  ask' ((=) Knight) blue_man \<and>
  ask  (blue_man = Knight) red_man \<and>
  ask' ((=) Spy) green_man"
  apply (rule exI3 [where x=Knight and y=Spy and z=Knave])
  apply (simp add:ask_def)
  done


(* PART SIX
  You come across three people. One wears blue, one wears red, and one wears green.
  You know that one is a knight, one is a knave, and one is a spy.
  "Who is the spy?" you ask.
  - The man wearing blue says, "That man in red is the spy."
  - The man wearing red says, "No, the man in green is the spy."
  - The man wearing green says, "No, the man in red is in fact the spy."
    Who is the spy, who is the knight and who is the knave?
*)

lemma part_six:
  "\<exists>blue_man red_man green_man.
  blue_man \<noteq> red_man \<and> red_man \<noteq> green_man \<and> green_man \<noteq> blue_man \<and>
  ask (red_man = Spy) blue_man \<and>
  ask (green_man = Spy) red_man \<and>
  ask (red_man = Spy) green_man"
  apply (rule exI3 [where x=Knave and y=Knight and z=Spy])
  apply (simp add:ask_def)
  done


(* PART SEVEN
  You are approached by three men. One wears blue, one wears red, and one wears green.
  You know that one is a knight, one is a knave, and one is a spy.
  - The man in blue says, "I am not a spy."
  - The man in red says, "I am a knave."
  - The man in green says, "If you asked me, I would say that the man in red is the spy."
    What are the true identities of these three men?
*)

lemma part_seven:
  "\<exists>blue_man red_man green_man.
  blue_man \<noteq> red_man \<and> red_man \<noteq> green_man \<and> green_man \<noteq> blue_man \<and>
  ask' ((\<noteq>) Spy) blue_man \<and>
  ask' ((=) Knave) red_man \<and>
  ask' (ask (red_man = Spy)) green_man"
  apply (rule exI3 [where x=Knight and y=Spy and z=Knave])
  apply (simp add:ask_def)
  done


(* PART EIGHT
  You come across three men. You know that one is a knight, one is a knave, and one is a spy.
  You are allowed to ask these three gentlemen two yes-or-no questions.
  They will all answer you, one at a time, with either a "yes" or a "no."
    How do you determine the true identities of these fellows?
*)

(* just a simple enumerated type to record which man we're talking about *)
datatype tri = triFirst | triSecond | triThird

lemma part_eight:
  "\<exists>(question_one :: man \<Rightarrow> bool)
   (question_two_logic :: bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> man \<Rightarrow> bool)
   (final_logic :: bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> man \<times> man \<times> man).
  \<comment> \<open>they're all different\<close>
  first_man \<noteq> second_man \<and> second_man \<noteq> third_man \<and> third_man \<noteq> first_man \<longrightarrow>
  \<comment> \<open>we ask them all the first question\<close>
  first_a1  = (ask' question_one first_man) \<longrightarrow>
  second_a1 = (ask' question_one second_man) \<longrightarrow>
  third_a1  = (ask' question_one third_man) \<longrightarrow>
  \<comment> \<open>we figure out the second question from this\<close>
  question_two = question_two_logic first_a1 second_a1 third_a1 \<longrightarrow>
  \<comment> \<open>we ask them all the second question\<close>
  first_a2  = (ask' question_two first_man) \<longrightarrow>
  second_a2 = (ask' question_two second_man) \<longrightarrow>
  third_a2  = (ask' question_two third_man) \<longrightarrow>
  \<comment> \<open>we figure out the solution from all the answers\<close>
  solution = final_logic first_a1 second_a1 third_a1 first_a2 second_a2 third_a2 \<longrightarrow>
  solution = (first_man, second_man, third_man)"
  \<comment> \<open>the first question is: are you a Spy?\<close>
  apply (rule exI [where x="(=) Spy"])
  \<comment> \<open>whoever gave an answer different to the others, we know his identity.
      we ask this man if one of the other two is a Spy.\<close>
  apply (rule exI [where x="\<lambda>a1 a2 a3 _.
    if (a1 = a2) then
      (first_man = Spy)
    else if (a1 = a3) then
      (first_man = Spy)
    else if (a2 = a3) then
      (second_man = Spy)
    else
      True"])
  \<comment> \<open>We now know one identity, and whether or not he told the truth about one
      of the other two being a Spy. This is all the info we need.\<close>
  apply (rule exI [where x="\<lambda>a1 a2 a3 a1' a2' a3'.
    let known_type = (\<lambda>b. if b then Knight else Knave) in
    let (known_ind::tri, truth) =
      (if (a1 = a2) then (triThird, a1) else
       if (a1 = a3) then (triSecond, a1) else (triFirst, a2))
    in case known_ind of
      triFirst
      \<Rightarrow> (known_type truth,
         if truth=a1' then Spy else known_type (\<not>truth),
         if truth=a1' then known_type (\<not>truth) else Spy)
    | triSecond
      \<Rightarrow> (if truth=a2' then Spy else known_type (\<not>truth),
         known_type truth,
         if truth=a2' then known_type (\<not>truth) else Spy)
    | triThird
      \<Rightarrow> (if truth=a3' then Spy else known_type (\<not>truth),
         if truth=a3' then known_type (\<not>truth) else Spy,
         known_type truth)
  "])
  apply (clarsimp simp:ask_def split:man.splits)
  done


(* PART NINE
  You come to a fork in the road.
  One path leads to death, the other to salvation.
  At the intersection, you encounter three men.
  You know one is a knight, one is a knave, and one is a spy.
  You may ask two questions.
  Each question must be addressed to only one man, and only he will respond.
    How do you determine the path to freedom?
*)
lemma part_nine:
  \<comment> \<open>they're all different\<close>
  "\<exists>(question_one :: man \<Rightarrow> bool) (target_one :: man)
    (get_question_two :: bool \<Rightarrow> (man \<Rightarrow> bool)) (get_target_two :: bool \<Rightarrow> man)
    (solution_logic :: bool \<Rightarrow> bool \<Rightarrow> bool).
  \<comment> \<open>prepare your questions and logic\<close>
  first_man \<noteq> second_man \<and> second_man \<noteq> third_man \<and> third_man \<noteq> first_man \<longrightarrow>
  \<comment> \<open>ask the first question to the first target man\<close>
  answer_one = ask' question_one target_one \<longrightarrow>
  \<comment> \<open>figure out the second question and target\<close>
  question_two = get_question_two answer_one \<longrightarrow>
  target_two = get_target_two answer_one \<longrightarrow>
  \<comment> \<open>ask the second question to the second target man\<close>
  answer_two = ask' question_two target_two \<longrightarrow>
  \<comment> \<open>figure out the solution\<close>
  solution = solution_logic answer_one answer_two \<longrightarrow>
  solution = safe_path"
  for first_man :: man
  \<comment> \<open>ask the first man if *he would say* that the second man is a Spy.\<close>
  apply (rule exI [where x="ask (second_man = Spy)"])
  apply (rule exI [where x=first_man])
  \<comment> \<open>if you picked a non-Spy, you now know your Spy. If you picked the Spy,
      you're still safe if you move away from him.\<close>
  \<comment> \<open>ask the guaranteed non-Spy if *he would say* the path is safe. \<close>
  apply (rule exI [where x="\<lambda>_. ask safe_path"])
  apply (rule exI [where x="\<lambda>a1. if a1 then third_man else second_man"])
  \<comment> \<open>you can now trust your answer\<close>
  apply (rule exI [where x="\<lambda>_. id"])
  apply (fastforce simp: ask_def split: man.splits)
  done

end

context KnightsKnaves begin

(* PART TEN 
  You are approached by a man.
  He is either a Knight or a Knave.
  He will only respond to you with "Da" or "Ja."
    How do you figure out if he is a knight or knave with just one question?
*)

datatype JaDa = Ja | Da

abbreviation bool_to_jd :: "bool \<Rightarrow> bool \<Rightarrow> JaDa" where
  "bool_to_jd k b \<equiv> if (k = b) then Ja else Da"

abbreviation jd_to_bool :: "bool \<Rightarrow> JaDa \<Rightarrow> bool" where
  "jd_to_bool k j \<equiv> (j = Ja) = k"

lemma part_ten:
  "\<exists>(question :: man \<Rightarrow> bool)
    (logic :: JaDa \<Rightarrow> man).
   \<forall>(key :: bool).
  answer = bool_to_jd key (ask' question unknown_man) \<longrightarrow>
  solution = logic answer \<longrightarrow>
  solution = unknown_man"
  apply (rule exI [where x=""])


(* PART TEN continued
  Down the road, you meet another man.
  Let's say you don't care if he is a knight or knave,
  you just want to know the meanings of "Ja" and "Da."
    How do you figure this out with just one question?
*)


end