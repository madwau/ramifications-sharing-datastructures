theory SeparationAlgebra
  imports "Separation_Algebra.Separation_Algebra" "Separation_Algebra.Sep_Heap_Instance"
begin

class sep_ramification = sep_algebra +
  assumes eq_zero_left: "p + q = 0 \<Longrightarrow> p = 0"
begin

lemma eq_zero_right: "p + q = 0 \<Longrightarrow> q = 0"
  by (metis local.eq_zero_left local.sep_add_commute local.sep_disj_zero)

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
  "(P \<union>* Q) h \<Longrightarrow> (sep_true \<and>* Q) h"
  unfolding ovp_conj_def
  sorry


subsection {* Further properties: Lemma 3.1 (The Ramifications of Sharing in Data Structures) *}

(* Lemma 3.1 (2) *)
lemma ovp_conj_empty:
  "P \<union>* \<box> = P"
  unfolding ovp_conj_def sep_empty_def
  apply (rule ext)
  by (metis eq_zero_right local.sep_add_zero local.sep_disj_zero)

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
  "(P \<union>* Q) h \<Longrightarrow> (P \<and>* sep_true) h"
  unfolding ovp_conj_def
  sorry

(* Lemma 3.1 (6) *)
lemma ovp_conj_sep_imp_conj3:
  "P \<union>* Q = (EXS R. (R \<longrightarrow>* P) \<and>* (R \<longrightarrow>* Q) \<and>* R)"
  unfolding ovp_conj_def sep_impl_def
  apply (rule ext)
  apply auto
  sorry

(* Lemma 3.1 (7) *)
lemma ovp_conj_commute:
  "(P \<union>* Q) = (Q \<union>* P)"
  by (rule ext) (auto intro: ovp_conj_commuteI)

(* Lemma 3.1 (8) *)
lemma ovp_conj_assoc:
  "P \<union>* (Q \<union>* R) = (P \<union>* Q) \<union>* R"
  unfolding ovp_conj_def
  apply (rule ext)
  sorry

end


instance "fun" :: (type,opt) sep_ramification
  apply standard
  unfolding zero_fun_def plus_fun_def
  apply (rule ext) 
  by meson

end
