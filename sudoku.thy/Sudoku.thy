theory Sudoku
  imports Main
begin

type_synonym 'a group = "'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"

inductive group_member where
  "group_member a (a, b, c, d, e, f, g, h, i)"
| "group_member b (a, b, c, d, e, f, g, h, i)"
| "group_member c (a, b, c, d, e, f, g, h, i)"
| "group_member d (a, b, c, d, e, f, g, h, i)"
| "group_member e (a, b, c, d, e, f, g, h, i)"
| "group_member f (a, b, c, d, e, f, g, h, i)"
| "group_member g (a, b, c, d, e, f, g, h, i)"
| "group_member h (a, b, c, d, e, f, g, h, i)"
| "group_member i (a, b, c, d, e, f, g, h, i)"

notation
  group_member  ("'(\<in>')") and
  group_member  ("(_/ \<in> _)" [51, 51] 50)

datatype cell = 
  Known nat
| Cands "bool group"

type_synonym row = "cell group"
type_synonym col = "cell group"
type_synonym box = "cell group"

type_synonym board = "row group"

type_synonym bcell = "bool group"


fun transpose :: "board \<Rightarrow> board" where
  "transpose ((aa, ab, ac, ad,  ae, af,  ag, ah, ai),
              (ba, bb, bc, bd,  be, bf,  bg, bh, bi),
              (ca, cb, cc, cd,  ce, cf,  cg, ch, ci),
              (da, db, dc, dd,  de, df,  dg, dh, di),
              (ea, eb, ec, ed,  ee, ef,  eg, eh, ei),
              (fa, fb, fc, fd,  fe, ff,  fg, fh, fi),
              (ga, gb, gc, gd,  ge, gf,  gg, gh, gi),
              (ha, hb, hc, hdz, he, hf,  hg, hh, hi),
              (ia, ib, ic, idz, ie, ifz, ig, ih, ii))
  =          ((aa, ba, ca, da, ea, fa, ga, ha, ia),
              (ab, bb, cb, db, eb, fb, gb, hb, ib),
              (ac, bc, cc, dc, ec, fc, gc, hc, ic),
              (ad, bd, cd, dd, ed, fd, gd, hdz, idz),
              (ae, be, ce, de, ee, fe, ge, he, ie),
              (af, bf, cf, df, ef, ff, gf, hf, ifz),
              (ag, bg, cg, dg, eg, fg, gg, hg, ig),
              (ah, bh, ch, dh, eh, fh, gh, hh, ih),
              (ai, bi, ci, di, ei, fi, gi, hi, ii))

"

(* big ugly function to pattern match cells into bcells *)
fun nat_to_bcell :: "nat \<Rightarrow> bcell" where
  "nat_to_bcell (Suc 0) = (True, False, False, False, False, False, False, False, False)"
| "nat_to_bcell (Suc (Suc 0)) = (False, True, False, False, False, False, False, False, False)"
| "nat_to_bcell (Suc (Suc (Suc 0))) = (False, False, True, False, False, False, False, False, False)"
| "nat_to_bcell (Suc (Suc (Suc (Suc 0)))) = (False, False, False, True, False, False, False, False, False)"
| "nat_to_bcell (Suc (Suc (Suc (Suc (Suc 0))))) = (False, False, False, False, True, False, False, False, False)"
| "nat_to_bcell (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = (False, False, False, False, False, True, False, False, False)"
| "nat_to_bcell (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = (False, False, False, False, False, False, True, False, False)"
| "nat_to_bcell (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = (False, False, False, False, False, False, False, True, False)"
| "nat_to_bcell (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) = (False, False, False, False, False, False, False, False, True)"
| "nat_to_bcell _ = (False, False, False, False, False, False, False, False, False)"



fun cell_to_bcell :: "cell \<Rightarrow> bcell" where
  "cell_to_bcell (Cands g) = g"
| "cell_to_bcell (Known x) = nat_to_bcell x"

(* enforces that some relation R holds between each member of two groups *)
inductive groupRel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a group \<Rightarrow> 'b group \<Rightarrow> bool" where
  "R a a' \<Longrightarrow> R b b' \<Longrightarrow> R c c' \<Longrightarrow>
  R d d' \<Longrightarrow> R e e' \<Longrightarrow> R f f' \<Longrightarrow>
  R g g' \<Longrightarrow> R h h' \<Longrightarrow> R i i' \<Longrightarrow>
  groupRel R (a, b, c, d, e, f, g, h, i) (a', b', c', d', e', f', g', h', i')"

inductive groupAll :: "('a \<Rightarrow> bool) \<Rightarrow> 'a group \<Rightarrow> bool" where
  "R a \<Longrightarrow> R b \<Longrightarrow> R b \<Longrightarrow> R c \<Longrightarrow> R d \<Longrightarrow>
  R e \<Longrightarrow> R f \<Longrightarrow> R g \<Longrightarrow> R h \<Longrightarrow> R i \<Longrightarrow>
  groupAll R (a, b, c, d, e, f, g, h, i)"

(* the subset relation for cells / rows / boards *)
inductive cellIn :: "cell \<Rightarrow> cell \<Rightarrow> bool" where
  "groupRel (\<le>) (cell_to_bcell c) (cell_to_bcell c') \<Longrightarrow> cellIn c c'"

inductive groupIn :: "cell group \<Rightarrow> cell group \<Rightarrow> bool" where
  "groupRel cellIn c c' \<Longrightarrow> groupIn c c'"

inductive boardIn :: "board \<Rightarrow> board \<Rightarrow> bool" where
  "groupRel groupIn c c'\<Longrightarrow> boardIn c c'"

fun isKnown :: "cell \<Rightarrow> bool" where
  "isKnown (Known _) = True"
| "isKnown _ = False"

inductive complete :: "board \<Rightarrow> bool" where
  "groupAll (groupAll isKnown) b \<Longrightarrow> complete b"

inductive groupCorrect :: "cell group \<Rightarrow> bool" where
  "\<forall>x\<in>{1..9}. Known x \<in> g \<Longrightarrow> groupCorrect g"

inductive correct :: "board \<Rightarrow> bool" where
  "groupAll groupCorrect b \<Longrightarrow> correct b"

definition solvable :: "board \<Rightarrow> bool" where
  "solvable b \<equiv> \<exists>b'. boardIn b' b \<and> complete b' \<and> correct b'"



(*
datatype cell2 = 
  Known nat
| Cands bool bool bool bool bool bool bool bool bool

fun cell_to_cell2 :: "cell \<Rightarrow> cell2" where
  "cell_to_cell2 (True, False, False, False, False, False, False, False, False) = Known 1"
| "cell_to_cell2 (False, True, False, False, False, False, False, False, False) = Known 2"
| "cell_to_cell2 (False, False, True, False, False, False, False, False, False) = Known 3"
| "cell_to_cell2 (False, False, False, True, False, False, False, False, False) = Known 4"
| "cell_to_cell2 (False, False, False, False, True, False, False, False, False) = Known 5"
| "cell_to_cell2 (False, False, False, False, False, True, False, False, False) = Known 6"
| "cell_to_cell2 (False, False, False, False, False, False, True, False, False) = Known 7"
| "cell_to_cell2 (False, False, False, False, False, False, False, True, False) = Known 8"
| "cell_to_cell2 (False, False, False, False, False, False, False, False, True) = Known 9"
| "cell_to_cell2 (a, b, c, d, e, f, g, h, i) = Cands a b c d e f g h i"
*)









nonterminal cand
syntax
  "_candON" :: "nat \<Rightarrow> cand" ("_")
  "_candOFF" :: "cand" (".")
  "_candUNK" :: "_ \<Rightarrow> cand" ("_")
  "_candX" :: "nat \<Rightarrow> bool \<Rightarrow> cand"
  "_cands" :: "cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cell" ("|_________|")
  "_known" :: "nat \<Rightarrow> cell" ("||-/ / _/ / -||")
translations
  "_known x" \<rightleftharpoons> "CONST Known x"
  "_candOFF" \<leftharpoondown> "_candX n (CONST False)"
  "_candOFF" \<rightharpoonup> "_candX 1 (CONST False)"
  "_candON n" \<leftharpoondown> "_candX n (CONST True)"
  "_candUNK x" \<leftharpoondown> "_candX n x"
  "_candUNK x" \<rightharpoonup> "_candX 1 x"
  "_cands (_candX 1 a) (_candX 2 b) (_candX 3 c) (_candX 4 d) (_candX 5 e)
          (_candX 6 f) (_candX 7 g) (_candX 8 h) (_candX 9 i)" \<rightleftharpoons> "CONST Cands (a, b, c, d, e, f, g, h, i)"


lemma test:
  "Known 5 = Cands (True, True, True, True, False, True, True, A, True)"
  oops











fun cell_to_group :: "cell \<Rightarrow> bool group" where
  "cell_to_group (Cands a b c d e f g h i) = (a, b, c, d, e, f, g, h, i)"
| "cell_to_group (Known (Suc 0)) = (True, False, False, False, False, False, False, False, False)"
| "cell_to_group (Known (Suc (Suc 0))) = (False, True, False, False, False, False, False, False, False)"
| "cell_to_group (Known 3) = (False, False, True, False, False, False, False, False, False)"
| "cell_to_group (Known 4) = (False, False, False, True, False, False, False, False, False)"
| "cell_to_group (Known 5) = (False, False, False, False, True, False, False, False, False)"
| "cell_to_group (Known 6) = (False, False, False, False, False, True, False, False, False)"
| "cell_to_group (Known 7) = (False, False, False, False, False, False, True, False, False)"
| "cell_to_group (Known 8) = (False, False, False, False, False, False, False, True, False)"
| "cell_to_group (Known 9) = (False, False, False, False, False, False, False, False, True)"

inductive cell_can_be where
  "cell_can_be x (Known x)"
| "cell_can_be 1 (Cands True _ _ _ _ _ _ _ _)"
| "cell_can_be 2 (Cands _ True _ _ _ _ _ _ _)"
| "cell_can_be 3 (Cands _ _ True _ _ _ _ _ _)"
| "cell_can_be 4 (Cands _ _ _ True _ _ _ _ _)"
| "cell_can_be 5 (Cands _ _ _ _ True _ _ _ _)"
| "cell_can_be 6 (Cands _ _ _ _ _ True _ _ _)"
| "cell_can_be 7 (Cands _ _ _ _ _ _ True _ _)"
| "cell_can_be 8 (Cands _ _ _ _ _ _ _ True _)"
| "cell_can_be 9 (Cands _ _ _ _ _ _ _ _ True)"

inductive cellIn :: "cell \<Rightarrow> cell \<Rightarrow> bool" where
  cellIn_refl: "cellIn a a"
| "cell_can_be x c \<Longrightarrow> cellIn (Known x) c"
| cell_to_group c





datatype group =
  Group cell cell cell cell cell cell cell cell cell

datatype board = 
  Board group group group group group group group group group

definition rows :: "group \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a" where
  
  "rows (Group a b c d e f g h i) \<equiv> (a, b, c, d, e, f, g, h, i)"

definition sudokuIn :: "board \<Rightarrow> board \<Rightarrow> bool" where
  ""

definition solvable :: "board \<Rightarrow> bool" where
  "solvable b \<equiv> \<exists>b'. includes b b' \<and> complete b'"








datatype cell = 
  Known nat
| Cands bool bool bool bool bool bool bool bool bool

nonterminal cand
syntax
  "_candON" :: "nat \<Rightarrow> cand" ("_")
  "_candOFF" :: "cand" (".")
  "_candUNK" :: "_ \<Rightarrow> cand" ("_")
  "_candX" :: "nat \<Rightarrow> bool \<Rightarrow> cand"
  "_cands" :: "cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cand \<Rightarrow> cell" ("|_________|")
  "_known" :: "nat \<Rightarrow> cell" ("||-/ / _/ / -||")
translations
  "_known x" \<rightleftharpoons> "CONST Known x"
  "_candOFF" \<leftharpoondown> "_candX n (CONST False)"
  "_candOFF" \<rightharpoonup> "_candX 1 (CONST False)"
  "_candON n" \<rightleftharpoons> "_candX n (CONST True)"
  "_candUNK x" \<leftharpoondown> "_candX n x"
  "_candUNK x" \<rightharpoonup> "_candX 1 x"
  "_cands (_candX 1 a) (_candX 2 b) (_candX 3 c) (_candX 4 d) (_candX 5 e)
          (_candX 6 f) (_candX 7 g) (_candX 8 h) (_candX 9 i)" \<rightleftharpoons> "CONST Cands a b c d e f g h i"

lemma test:
  "Known 5 = Cands True True True True False True True A True"
  oops






end