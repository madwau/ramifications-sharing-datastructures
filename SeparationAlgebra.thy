theory SeparationAlgebra
  imports "Separation_Algebra.Separation_Algebra" "Separation_Algebra.Sep_Heap_Instance"
begin

class sep_ramification = sep_algebra +
  assumes eq_zero_left: "p + q = 0 \<Longrightarrow> p = 0"
  assumes sep_disj_add: "h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>2 ## h\<^sub>3 \<and> h\<^sub>1 ## h\<^sub>3 \<Longrightarrow> h\<^sub>1 ## h\<^sub>2 + h\<^sub>3"
  assumes disjointness: "x+x=y \<Longrightarrow> x=y"
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


thm sep_disj_add3[of h\<^sub>1 h\<^sub>1' h\<^sub>2' h\<^sub>3']

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
    apply safe
         apply (metis sep_disj_add sep_disj_addI1 sep_disj_commuteI sep_disj_left)
        apply (meson sep_disj_addI1 sep_disj_commuteI sep_disj_right)
    subgoal
    proof -
      have "h\<^sub>1 ## h\<^sub>2 + h\<^sub>3"
        by (simp add: \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> sep_disj_add)
      then have "h\<^sub>1 ## h\<^sub>1' + h\<^sub>2' + h\<^sub>3'"
        by (simp add: \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close>)
      then have "h\<^sub>1 ## h\<^sub>1'"
        using sep_disj_add3 by blast
      then show ?thesis
        using CS \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> sep_disj_addD2 sep_disj_add2 by blast
    qed
    subgoal
    proof -
      have "h\<^sub>1 + (ac + ad) + (bc + bd) = h\<^sub>1 + h\<^sub>2 + h\<^sub>3"
        using CS by blast
      also have "\<dots> = h\<^sub>1 + (h\<^sub>1' + h\<^sub>2' + h\<^sub>3')"
        by (simp add: \<open>h\<^sub>1 ## h\<^sub>2\<close> \<open>h\<^sub>1 ## h\<^sub>3\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close> sep_add_assoc)
      also have "\<dots> = h\<^sub>1 + (h\<^sub>1' + (h\<^sub>2' + ad) + bd)"
        by (smt CS \<open>h\<^sub>1' ## h\<^sub>2'\<close> \<open>h\<^sub>1' ## h\<^sub>3'\<close> \<open>h\<^sub>2 ## h\<^sub>3\<close> \<open>h\<^sub>2 + h\<^sub>3 = h\<^sub>1' + h\<^sub>2' + h\<^sub>3'\<close> \<open>h\<^sub>2' ## h\<^sub>3'\<close>
            sep_add_assoc sep_add_commute sep_disj_commuteI sep_disj_right)
      also have "\<dots> = h\<^sub>1 + h\<^sub>1' + (h\<^sub>2' + ad) + bd"
        sorry
      finally show ?thesis by blast
    qed
    subgoal
      apply (rule exI[where x="ad + h\<^sub>1"])
      apply (rule exI[where x="ac"])
      apply (rule exI[where x="bc"])
      apply safe
      using local.sep_add_commute local.sep_add_disjI1 local.sep_disj_commuteI apply presburger
         apply (meson local.sep_disj_addD1 local.sep_disj_addD2 local.sep_disj_commute sep_disj_add2)
      subgoal
      proof -
        have "h\<^sub>1 + h\<^sub>1' + (h\<^sub>2' + ad) = h\<^sub>1 + h\<^sub>1' + h\<^sub>2' + ad" sorry
        also have "\<dots> = ad + h\<^sub>1 + ac + bc" sorry
        finally show ?thesis sorry
      qed
      subgoal
        by (metis local.sep_add_assoc local.sep_add_commute local.sep_disj_commuteI sep_disj_left)
      subgoal
        by simp
      done
    subgoal
      by (metis local.sep_add_assoc local.sep_add_commute sep_disj_left)
    done
next
  fix h
  assume a: "?rhs h"
  thus "?lhs h" sorry
qed

end


instance "fun" :: (type,opt) sep_ramification
  apply standard
  unfolding zero_fun_def plus_fun_def
     apply (rule ext) 
     apply meson
  sorry

end
