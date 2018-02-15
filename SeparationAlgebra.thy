theory SeparationAlgebra
  imports "Separation_Algebra.Separation_Algebra" "Separation_Algebra.Sep_Heap_Instance"
begin

class sep_ramification = sep_algebra +
  assumes eq_zero_left: "p + q = 0 \<Longrightarrow> p = 0"
  assumes sep_disj_add: "h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<Longrightarrow> h\<^sub>1 ## h\<^sub>2 + h\<^sub>3"
  assumes cross_split: "a+b=z \<and> c+d=z \<Longrightarrow> \<exists>ac ad bc bd. ac+ad=a \<and> bc+bd=b \<and> ac+bc=c \<and> ad+bd=d \<and>
                        ac ## ad \<and> ac ## bc \<and> ac ## bd \<and> ad ## bc \<and> ad ## bd \<and> bc ## bd"
begin

lemma eq_zero_right: "p + q = 0 \<Longrightarrow> q = 0"
  by (metis local.eq_zero_left local.sep_add_commute local.sep_disj_zero)

lemma sep_disj_left: "p ## q + r \<Longrightarrow> p ## q"
  sorry

lemma sep_disj_right: "p ## q + r \<Longrightarrow> p ## r"
  sorry

lemma sep_disj_add2: "h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<Longrightarrow> h\<^sub>1 + h\<^sub>2 ## h\<^sub>3"
  by (simp add: local.sep_disj_add local.sep_disj_addI1)

lemma sep_disj_add3: "s ## p + q + r  \<Longrightarrow> s ## p"
  using sep_disj_commuteI sep_disj_left by blast

definition ovp_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "\<union>*" 51)
  where
    "P \<union>* Q \<equiv> \<lambda>h. \<exists>h\<^sub>1 h\<^sub>2 h\<^sub>3. h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<and>
                             h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3 \<and> 
                             P (h\<^sub>1 + h\<^sub>2) \<and> Q (h\<^sub>2 + h\<^sub>3)"


subsection {* Overlapping Conjunction Properties *}

lemma ovp_conjD:
  "(P \<union>* Q) h \<Longrightarrow> \<exists>h\<^sub>1 h\<^sub>2 h\<^sub>3. h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<and> h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3 \<and> P (h\<^sub>1 + h\<^sub>2) \<and> Q (h\<^sub>2 + h\<^sub>3)"
  by (simp add: ovp_conj_def)

lemma ovp_conjE:
  "\<lbrakk> (P \<union>* Q) h; \<And>h\<^sub>1 h\<^sub>2 h\<^sub>3. \<lbrakk> P (h\<^sub>1 + h\<^sub>2); Q (h\<^sub>2 + h\<^sub>3); h\<^sub>1 ## h\<^sub>2; h\<^sub>2 ## h\<^sub>3; h\<^sub>1 ## h\<^sub>3; h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3 \<rbrakk> \<Longrightarrow> X \<rbrakk> \<Longrightarrow> X"
  by (auto simp: ovp_conj_def)

lemma ovp_conjI:
  "\<lbrakk> P (h\<^sub>1 + h\<^sub>2); Q (h\<^sub>2 + h\<^sub>3); h\<^sub>1 ## h\<^sub>2; h\<^sub>2 ## h\<^sub>3; h\<^sub>1 ## h\<^sub>3; h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3 \<rbrakk> \<Longrightarrow> (P \<union>* Q) h"
  by (auto simp: ovp_conj_def)

lemma ovp_conj_commuteI:
  "(P \<union>* Q) h \<Longrightarrow> (Q \<union>* P) h"
  by (smt local.sep_add_assoc local.sep_add_commute local.sep_disj_commuteI ovp_conjE ovp_conjI)

lemma ovp_conj_impl:
  "\<lbrakk> (P \<union>* Q) h; \<And>h. P h \<Longrightarrow> P' h; \<And>h. Q h \<Longrightarrow> Q' h \<rbrakk> \<Longrightarrow> (P' \<union>* Q') h"
  using ovp_conj_def by fastforce

lemma ovp_conj_sep_true_left:
  assumes "(P \<union>* Q) h"
  shows "(sep_true \<and>* Q) h"
  unfolding ovp_conj_def sep_conj_def
proof -
  have "(P \<union>* Q) h" using assms by blast
  obtain h\<^sub>1 h\<^sub>2 h\<^sub>3 where "h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<and>
    h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3 \<and> P (h\<^sub>1 + h\<^sub>2) \<and> Q (h\<^sub>2 + h\<^sub>3)"
    using assms ovp_conjD by blast
  then have "h\<^sub>1 ## (h\<^sub>2 + h\<^sub>3) \<and> h = h\<^sub>1 + (h\<^sub>2 + h\<^sub>3) \<and> Q (h\<^sub>2 + h\<^sub>3)"
    by (simp add: local.sep_add_assoc local.sep_disj_add)
  then show "\<exists>x y. x ## y \<and> h = x + y \<and> True \<and> Q y" by blast
qed


subsection {* Further properties: Lemma 3.1 (The Ramifications of Sharing in Data Structures) *}

(* Lemma 3.1 (2) *)
lemma ovp_conj_empty:
  "P \<union>* \<box> = P"
  unfolding ovp_conj_def sep_empty_def
proof (rule ext)
qed (metis eq_zero_right local.sep_add_zero local.sep_disj_zero)

(* Lemma 3.1 (3) *)
lemma conj_ovp_conj:
  "(P and Q) h \<Longrightarrow> (P \<union>* Q) h"
  by (metis (no_types, lifting) local.sep_add_zero local.sep_conjE
      local.sep_conj_sep_true' local.sep_disj_zero ovp_conj_def)

(* Lemma 3.1 (4) *)
lemma sep_conj_ovp_conj:
  "(P \<and>* Q) h \<Longrightarrow> (P \<union>* Q) h"
  by (metis local.sep_add_commute local.sep_add_zero local.sep_conjE
      local.sep_disj_commuteI local.sep_disj_zero ovp_conj_def)

(* Lemma 3.1 (5) *)
lemma ovp_conj_sep_true_right:
  assumes "(P \<union>* Q) h"
  shows "(P \<and>* sep_true) h"
  unfolding ovp_conj_def sep_conj_def
proof -
  have "(P \<union>* Q) h" using assms by blast
  obtain h\<^sub>1 h\<^sub>2 h\<^sub>3 where "h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<and>
    h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3 \<and> P (h\<^sub>1 + h\<^sub>2) \<and> Q (h\<^sub>2 + h\<^sub>3)"
    using assms ovp_conjD by blast
  then have "(h\<^sub>1 + h\<^sub>2) ## h\<^sub>3 \<and> h = (h\<^sub>1 + h\<^sub>2) + h\<^sub>3 \<and> P (h\<^sub>1 + h\<^sub>2)"
    by (simp add: local.sep_disj_add local.sep_disj_addI1)
  then show "\<exists>x y. x ## y \<and> h = x + y \<and> P x \<and> True" by blast
qed

(* Lemma 3.1 (6) *)
lemma ovp_conj_sep_imp_conj3:
  "P \<union>* Q = (EXS R. (R \<longrightarrow>* P) \<and>* (R \<longrightarrow>* Q) \<and>* R)"
  unfolding ovp_conj_def sep_impl_def sep_conj_def
  apply rule
  apply safe
  subgoal for h h1 h2 h3
    apply (rule exI[where x="\<lambda>h. h=h2"])
    apply (simp add: sep_conj_def)
    apply (rule exI[where x="h1"])
    apply (rule exI[where x="h2+h3"])
    apply (simp add: sep_disj_add sep_add_assoc)
    apply (rule exI[where x="h3"])
    by (simp add: sep_disj_commuteI sep_add_commute)
  subgoal for h R
    by (metis sep_add_assoc sep_add_commute sep_disj_addD2 sep_disj_commuteI)
  done

(* Lemma 3.1 (7) *)
lemma ovp_conj_commute:
  "(P \<union>* Q) = (Q \<union>* P)"
  by (rule ext) (auto intro: ovp_conj_commuteI)

(* Lemma 3.1 (8) *)
lemma ovp_conj_assoc:
  "P \<union>* (Q \<union>* R) = (P \<union>* Q) \<union>* R" (is "?lhs = ?rhs")
proof (rule ext, rule iffI)
  fix h
  assume a: "?lhs h"
  then obtain h\<^sub>1 h\<^sub>2 h\<^sub>3 h\<^sub>1' h\<^sub>2' h\<^sub>3' where
    "P (h\<^sub>1 + h\<^sub>2)" and
    "h\<^sub>1 ## h\<^sub>2" and "h\<^sub>2 ## h\<^sub>3" and "h\<^sub>1 ## h\<^sub>3" and "h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3" and 
    "Q (h\<^sub>1' + h\<^sub>2')" and "R (h\<^sub>2' + h\<^sub>3')" and
    "h\<^sub>1' ## h\<^sub>2'" and "h\<^sub>2' ## h\<^sub>3'" and "h\<^sub>1' ## h\<^sub>3'" and "h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
    by (metis ovp_conjE)
  moreover
  then obtain ac ad bc bd where
    CS: "ac+ad=h\<^sub>2 \<and> bc+bd=h\<^sub>3 \<and> ac+bc=h\<^sub>1'+h\<^sub>2' \<and> ad+bd=h\<^sub>3' \<and>
     ac ## ad \<and> ac ## bc \<and> ac ## bd \<and> ad ## bc \<and> ad ## bd \<and> bc ## bd"
    using cross_split by blast
  ultimately
  show "?rhs h"
    unfolding ovp_conj_def
    apply safe
    apply (rule exI[where x="h\<^sub>1 + h\<^sub>1'"])
    apply (rule exI[where x="h\<^sub>2' + ad"])
    apply (rule exI[where x="bd"])
  proof (safe, goal_cases)
    case 1
    then show ?case by(metis sep_disj_add sep_disj_addI1 sep_disj_commuteI sep_disj_left)
  next
    case 2
    then show ?case using sep_disj_addI1 by blast
  next
    case 3
    have "h\<^sub>1 ## h\<^sub>2 + h\<^sub>3"
      by (simp add: \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> sep_disj_add)
    then have "h\<^sub>1 ## h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
      by (simp add: \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close>)
    then have "h\<^sub>1 ## h\<^sub>1'"
      using sep_disj_add3 by blast
    then show ?case using CS \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> sep_disj_addD2 sep_disj_add2 by blast
  next
    case 4
    have "h\<^sub>1 ## h\<^sub>2 + h\<^sub>3"
      by (simp add: \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> sep_disj_add)
    then have "h\<^sub>1 ## h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
      by (simp add: \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close>)
    then have A: "h\<^sub>1 ## h\<^sub>1' \<and> h\<^sub>1 ## h\<^sub>2' \<and> h\<^sub>1 ## ad \<and> h\<^sub>1 ## bd"
      using  sep_disj_add3 "4"(2) "4"(4) "4"(7) CS sep_disj_addD sep_disj_left by blast

    have "h\<^sub>1 + (ac + ad) + (bc + bd) = h\<^sub>1 + h\<^sub>2 + h\<^sub>3"
      using CS by blast
    also have "\<dots> = h\<^sub>1 + (h\<^sub>1' + h\<^sub>2' + h\<^sub>3')"
      by (simp add: \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close> sep_add_assoc)
    also have "\<dots> = h\<^sub>1 + (h\<^sub>1' + (h\<^sub>2' + ad) + bd)"
      by (smt CS \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close> \<open>h\<^sub>2' ## h\<^sub>3'\<close>
          sep_add_assoc sep_add_commute sep_disj_commuteI sep_disj_right)
    also have "\<dots> = h\<^sub>1 + h\<^sub>1' + (h\<^sub>2' + ad) + bd"
      using A by (metis (full_types) "4"(20) "4"(7) "4"(8) "4"(9) sep_add_assoc sep_disj_add local.sep_disj_addI1 sep_disj_left)
    finally show ?case by blast
  next
    case 5
    show ?case
      apply (rule exI[where x="ad + h\<^sub>1"])
      apply (rule exI[where x="ac"])
      apply (rule exI[where x="bc"])
    proof (safe, goal_cases)
      case 1
      then show ?case
        by (simp add: "5"(16) "5"(2) local.sep_add_commute local.sep_add_disjI1 local.sep_disj_commuteI)
    next
      case 2
      then show ?case by (simp add: "5"(17))
    next
      case 3
      then show ?case
        by (metis "5"(4) CS \<open>h\<^sub>1 ## h\<^sub>2\<close> local.sep_add_commute sep_disj_add2 sep_disj_left)
    next
      case 4
      have A: "h\<^sub>1' ## h\<^sub>2' \<and> h\<^sub>2' ## ad"
        using "5"(7) "5"(8) sep_disj_left by blast
      have B: "h\<^sub>1' + h\<^sub>2' = ac + bc"
        by (simp add: "5"(14))
      have "h\<^sub>1 + h\<^sub>1' + (h\<^sub>2' + ad) = h\<^sub>1 + (h\<^sub>1' + h\<^sub>2') + ad"
        by (metis A "5"(2) "5"(4) "5"(9) CS local.sep_add_assoc local.sep_disj_add local.sep_disj_addD1 sep_disj_add2 sep_disj_right)
      also have "\<dots> = h\<^sub>1 + (ac + bc) + ad" using B by simp
      also have "\<dots> = h\<^sub>1 + ac + bc + ad"
        by (metis "5"(17) "5"(2) "5"(4) sep_add_assoc sep_disj_left)
      also have "\<dots> = ad + h\<^sub>1 + ac + bc"
        by (smt "5"(2) "5"(4) CS sep_add_assoc sep_add_commute sep_disj_commuteI sep_disj_add2 sep_disj_right)
      finally show ?case by simp
    next
      case 5
      then show ?case
        by (metis CS \<open>P (h\<^sub>1 + h\<^sub>2)\<close> \<open>h\<^sub>1 ## h\<^sub>2\<close> sep_add_assoc sep_add_commute sep_disj_commuteI sep_disj_left)
    next
      case 6
      then show ?case by (simp add: "5"(14) "5"(5))
    qed
  next
    case 6
    then show ?case by (metis sep_add_assoc sep_add_commute sep_disj_left)
  qed
next
  fix h
  assume a: "?rhs h"
  then obtain h\<^sub>1 h\<^sub>2 h\<^sub>3 h\<^sub>1' h\<^sub>2' h\<^sub>3' where
    "R (h\<^sub>2 + h\<^sub>3)" and
    "h\<^sub>1 ## h\<^sub>2" and "h\<^sub>2 ## h\<^sub>3" and "h\<^sub>1 ## h\<^sub>3" and "h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3" and 
    "P (h\<^sub>1' + h\<^sub>2')" and "Q (h\<^sub>2' + h\<^sub>3')" and
    "h\<^sub>1' ## h\<^sub>2'" and "h\<^sub>2' ## h\<^sub>3'" and "h\<^sub>1' ## h\<^sub>3'" and "h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
    by (metis ovp_conjE)
  moreover
  then have "h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + (h\<^sub>2' + h\<^sub>3')"
    by (simp add: local.sep_add_assoc)
  then obtain ac ad bc bd where
    CS: "ac+ad=h\<^sub>1 \<and> bc+bd=h\<^sub>2 \<and> ac+bc=h\<^sub>1' \<and> ad+bd=h\<^sub>2'+h\<^sub>3' \<and>
     ac ## ad \<and> ac ## bc \<and> ac ## bd \<and> ad ## bc \<and> ad ## bd \<and> bc ## bd"
    using cross_split by blast
  ultimately
  show "?lhs h"
    unfolding ovp_conj_def
    apply safe
    apply (rule exI[where x="ac"])
    apply (rule exI[where x="h\<^sub>2' + bc"])
    apply (rule exI[where x="h\<^sub>3 + h\<^sub>3'"])
  proof (safe, goal_cases)
    case 1
    then show ?case
      using sep_add_disjI2 sep_disj_commute by blast
  next
    case 2
    then show ?case 
      by (smt local.sep_add_assoc local.sep_add_commute local.sep_add_disjD local.sep_add_disjI2 local.sep_disj_commuteI sep_disj_add2)
  next
    case 3
    have "h\<^sub>3 ## h\<^sub>1 + h\<^sub>2"
      using \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_disj_add local.sep_disj_commuteI by blast
    then have "h\<^sub>3 ## h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
      by (simp add: \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close>)
    then have "h\<^sub>3 ## h\<^sub>1'"
      using sep_disj_add3 by blast
    then show ?case
      using "3"(16) "3"(17) "3"(4) "3"(9) \<open>h\<^sub>3 ## h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close> local.sep_add_disjD local.sep_disj_add sep_disj_right by blast
  next
    case 4
    have "h\<^sub>3 ## h\<^sub>1 + h\<^sub>2"
      using \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_disj_add local.sep_disj_commuteI by blast
    then have A: "h\<^sub>3 ## h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
      by (simp add: \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close>)

    have "ac + ad + (bc + bd) + h\<^sub>3 = h\<^sub>1 + h\<^sub>2 + h\<^sub>3"
      using "4"(11) \<open>h = h\<^sub>1 + h\<^sub>2 + h\<^sub>3\<close> by blast
    also have "\<dots> = h\<^sub>3 + (h\<^sub>1' + h\<^sub>2' + h\<^sub>3')"
      using \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close> A local.sep_add_commute by fastforce
    also have "\<dots> = ac + (h\<^sub>2' + bc) + (h\<^sub>3 + h\<^sub>3')"
      by (smt "4"(14) "4"(17) "4"(8) \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> A local.sep_add_commute local.sep_add_left_commute local.sep_disj_add local.sep_disj_commuteI sep_disj_right)
    finally show ?case by blast
  next
    case 5
    then show ?case
      by (metis local.sep_add_assoc local.sep_add_commute local.sep_add_disjD)
  next
    case 6
    show ?case
      apply (rule exI[where x="ad"])
      apply (rule exI[where x="bd"])
      apply (rule exI[where x="bc + h\<^sub>3"])
    proof (safe, goal_cases)
      case 1
      then show ?case
        by (simp add: "6"(20))
    next
      case 2
      then show ?case
        using "6"(21) "6"(3) local.sep_add_disjI1 local.sep_disj_commuteI by blast
    next
      case 3
      then show ?case
        by (meson "6"(16) "6"(19) "6"(21) "6"(3) "6"(4) local.sep_add_disjD local.sep_disj_commuteI sep_disj_add2)
    next
      case 4
      have A: "h\<^sub>3 ## bc \<and> bc ## h\<^sub>2' \<and> bc ## h\<^sub>3'"
        using CS \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_add_disjD local.sep_disj_commuteI by blast
      have B: "h\<^sub>3 ## h\<^sub>3'" 
        by (metis "6"(8) \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + (h\<^sub>2' + h\<^sub>3')\<close> \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_add_disjD local.sep_disj_add local.sep_disj_commuteI)
      have C: "h\<^sub>2' ## h\<^sub>3' \<and> h\<^sub>2' ## h\<^sub>3"
        by (metis "6"(8) \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + (h\<^sub>2' + h\<^sub>3')\<close> \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_add_left_commute local.sep_disj_add local.sep_disj_commuteI sep_disj_left)

      have "h\<^sub>2' + bc + (h\<^sub>3 + h\<^sub>3') = h\<^sub>2' + bc + h\<^sub>3 + h\<^sub>3'"
        using A by (metis "6"(8) \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + (h\<^sub>2' + h\<^sub>3')\<close> \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_add_assoc local.sep_add_disjD local.sep_disj_commuteI sep_disj_add2)
      also have "\<dots> = h\<^sub>2' + (bc + h\<^sub>3 + h\<^sub>3')"
        using A by (metis "6"(8) \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>1 + h\<^sub>2 = h\<^sub>1' + (h\<^sub>2' + h\<^sub>3')\<close> \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_add_assoc local.sep_add_disjD local.sep_disj_add local.sep_disj_commuteI)
      also have "\<dots> = h\<^sub>2' + (h\<^sub>3' + bc + h\<^sub>3)"
        using B by (simp add: A local.sep_add_assoc local.sep_add_commute local.sep_disj_commuteI)
      also have "\<dots> = h\<^sub>2' + h\<^sub>3' + bc + h\<^sub>3"
        using B C by (simp add: A local.sep_add_assoc local.sep_disj_commuteI sep_disj_add2)
      also have "\<dots> = ad + bd + (bc + h\<^sub>3)"
        by (simp add: "6"(15) A B C local.sep_add_assoc local.sep_disj_commuteI sep_disj_add2)
      finally show ?case by simp
    next
      case 5
      then show ?case by (simp add: "6"(15) "6"(6))
    next
      case 6
      then show ?case
        by (metis CS \<open>R (h\<^sub>2 + h\<^sub>3)\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> local.sep_add_assoc local.sep_add_commute local.sep_disj_commuteI sep_disj_left)
    qed
  qed
qed

end


instance "fun" :: (type,opt) sep_ramification
  apply standard
  unfolding zero_fun_def plus_fun_def
  apply (rule ext) 
  apply meson
  sorry

end
