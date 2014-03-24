header {* The Simply Typed Lambda Calculus *}
(*<*)
theory Stlc
imports HOLCF Cenv begin
(*>*)

text {* Having examined the untyped lambda calculus and done some rudimentary check of reasonableness, now we consider how to deal with the
        simply-typed calculus with fixed point combinator added. The result is a language superficially similar to PCF as presented in (ref).

        The goal of this section is to give a denotational semantics to this theory much like that described in Milner (ref) and MacQueen et al. (ref) and to prove
        that the typing relation is sound with respect to the semantics, i.e. that "well-typed programs don't go wrong". *}

text {* We can define both our types and our term language as ordinary Isabelle datatypes. *}

datatype ty = TyNat | TyFun ty ty

datatype lam = LVar nat | LApp lam lam | LLam nat ty lam | LNat nat
             | LPlus lam lam | LFix ty lam

text {* We represent our typing environment as a function from naturals to object types and our typing environment
        as an inductive relation in Isabelle *}

type_synonym ty_env = "nat \<Rightarrow> ty"

inductive lam_ty :: "ty_env \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" where
  LVar : "\<lbrakk>tys n = ty\<rbrakk> \<Longrightarrow> lam_ty tys (LVar n) ty" |
  LPlus : "\<lbrakk>lam_ty tys l1 TyNat; lam_ty tys l2 TyNat\<rbrakk> \<Longrightarrow> lam_ty tys (LPlus l1 l2) TyNat" |
  LApp  :"\<lbrakk>lam_ty tys l1 (TyFun t1 t2); lam_ty tys l2 t1\<rbrakk> \<Longrightarrow> lam_ty tys (LApp l1 l2) t2" |
  LNat  : "lam_ty tys (LNat n) TyNat" |
  LLam  : "\<lbrakk>lam_ty (tys (n :=t1)) l1 t2\<rbrakk> \<Longrightarrow> lam_ty tys (LLam n t1 l1) (TyFun t1 t2)" |
  LFix  : "\<lbrakk>lam_ty tys l1 (TyFun t1 t1)\<rbrakk> \<Longrightarrow> lam_ty tys (LFix t1 l1) t1"

text {* Our domain is now slightly more complicated than it was before, not only having functions but also a natural numbers type
        and the Wrong token. This is a good opportunity to explain the use of the lift type constructor. The arguments to constructors as defined
        in the domain command must be pcpos. As nat is an ordinary Isabelle type, the lift type constructor takes this type and constructs the typical
        flat pcpo form that type: bottom is below all other elements, and all elements that are not bottom are incomparable. *}

domain V = VNat (fromNat :: "nat lift") | VFun (lazy "V \<rightarrow> V") | Wrong
(*<*)
fixrec fromFun :: "V \<rightarrow> (V \<rightarrow> V)" where
"fromFun\<cdot>(VFun\<cdot>f) = f" |
"fromFun\<cdot>Wrong = \<bottom>" |
"n \<noteq> \<bottom> \<Longrightarrow> fromFun\<cdot>(VNat\<cdot>n) = \<bottom>" |
"fromFun\<cdot>\<bottom> = \<bottom>"

lemma "fromFun\<cdot>Wrong = \<bottom>"
apply (fixrec_simp)
done
(*>*)

text {* We can define application within the model similarly to how we did before, but now we need to account for the cases where we attempt a type-incorrect application and return Wrong there. (include bit about side conditions) *}

fixrec vApply :: "V \<rightarrow> V \<rightarrow> V" where
"n \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VNat\<cdot>n)\<cdot>x = Wrong" |
"vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"vApply\<cdot>Wrong\<cdot>x = Wrong"

text {* Similarly, we can define the other constants of other theory vFix and vPlus. *}

fixrec vPlus :: "V \<rightarrow> V \<rightarrow> V"(*<*) where
"n \<noteq> \<bottom> \<and> n' \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>n)\<cdot>(VNat\<cdot>n') = VNat\<cdot>((FLIFT x x'. Def (x + x'))\<cdot>n\<cdot>n')" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>n)\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VFun\<cdot>f') = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VNat\<cdot>n) = Wrong" |
"vPlus\<cdot>Wrong\<cdot>(VFun\<cdot>f) = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>Wrong\<cdot>(VNat\<cdot>n) = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>n)\<cdot>Wrong = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>Wrong = Wrong" (*>*)

fixrec vFix :: "V \<rightarrow> V"(*<*) where
"vFix\<cdot>(VFun\<cdot>f) = fix\<cdot>f" |
"vFix\<cdot>Wrong = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vFix\<cdot>(VNat\<cdot>n) = Wrong"

lemma [simp]: "vFix\<cdot>\<bottom> = \<bottom>"
apply fixrec_simp
done

lemma [simp]: "vApply\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply fixrec_simp
done (*>*)

text {* We also use the same abbreviations for application and abstraction
        for the rest of the paper and they will be elided in our examples from here on. *}
(*<*)
abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> V" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

abbreviation vLam :: "(V \<Rightarrow> V) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)" (*>*)

text {* Now we represent our types as sets of V values. The nat type is simply represented as the set of all possible VNat values, which includes $\perp$ because we chose to make VNat a strict constructor. *}

definition natSet :: "V set" where
"natSet \<equiv> {VNat\<cdot>n | n. True}"

text {* Similarly, the meaning of a function between types A and B is the set of functions that take elements of A to elements of B, plus the $\perp$ element wince VFun is not a strict constructor and we need to include this explicitly. *}

definition funSet :: "V set \<Rightarrow> V set \<Rightarrow> V set" where
"funSet A B \<equiv> {VFun\<cdot>f | f. (\<forall> x. x \<in> A \<longrightarrow> (f\<cdot>x) \<in> B)} \<union> {\<bottom>}"

text {* And we can encode the relation between types and their meanings with the following function. *}

fun tyM :: "ty \<Rightarrow> (V set)" where
"tyM TyNat = natSet" |
"tyM (TyFun t1 t2) = funSet (tyM t1) (tyM t2)"

text {* As a simple test of reasonableness, we can then show that no natural can be an element of a set of function type. *}

lemma "n \<noteq> \<bottom> \<Longrightarrow> (VNat\<cdot>n) \<notin> funSet A B"(*<*)
apply (simp add: funSet_def)
done(*>*)

(*<*)
lemma [simp]: "vPlus\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma [simp]: "vPlus\<cdot>\<bottom>\<cdot>(VNat\<cdot>n) = \<bottom>"
apply fixrec_simp
done

lemma [simp]: "vPlus\<cdot>(VNat\<cdot>n)\<cdot>\<bottom> = \<bottom>"
apply (case_tac n)
apply fixrec_simp
apply fixrec_simp
done(*>*)

text {* Now, our denotation for this language is, again, rather straight forward. We match up neatly between the constants we've defined and the cases in our term language. (note: probably need to say something about our different use of environments here)*}

fun lamM :: "lam \<Rightarrow> V cenv \<rightarrow> V" where
"lamM (LNat n) = (\<Lambda> \<sigma>. VNat\<cdot>(Def n))" |
"lamM (LLam n _ e) = (\<Lambda> \<sigma>. (\<Delta> x. lamM e\<cdot>(sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x)))" |
"lamM (LApp e1 e2) = (\<Lambda> \<sigma>. (lamM e1\<cdot>\<sigma>)\<bullet>(lamM e2\<cdot>\<sigma>))" |
"lamM (LPlus e1 e2) = (\<Lambda> \<sigma>. vPlus\<cdot>(lamM e1\<cdot>\<sigma>)\<cdot>(lamM e2\<cdot>\<sigma>))" |
"lamM (LVar n) = (\<Lambda> \<sigma>. slookup n\<cdot>\<sigma>)"|
"lamM (LFix _ f) = (\<Lambda> \<sigma>. vFix\<cdot>(lamM f\<cdot>\<sigma>))"

text {* Of course, a denotation function is only useful if it is, indeed, correctly defined. The first major hurdle to determine if the denotation is correct is to show that it is sound with respect to the typing rules. In our case, soudness is going to be a Milner-style "don't-go-wrong" proof (ref). 

        In order to prove this, we first need to define what it means for the value environment of the denotation and the typing environment of the typing derivation to agree. In this case, we simply state that the two are {\em compatible} when, for all variables, the value in the environment corresponding to that variable is an element of the denotation of the type corresponding to that variable in the typing environment.*}

definition env_compat :: "ty_env \<Rightarrow> V cenv \<Rightarrow> bool" where
"env_compat tys \<sigma> \<equiv> \<forall> n. (slookup n\<cdot>\<sigma>) \<in> tyM (tys n)"
(*<*)
lemma "\<bottom> \<in> natSet"
apply (simp add: natSet_def)
done(*>*)

(*<*)
lemma [simp] : "\<bottom> \<in> tyM t"
apply (induct t)
apply (simp add: natSet_def)
apply simp
apply (simp add: funSet_def)
done

lemma "adm (\<lambda> x. x \<in> (Rep_cfun fromNat) ` natSet)"
apply (simp add: natSet_def)
done

lemma [simp]: "adm (\<lambda> x. x \<in> natSet)"
apply (rule admI)
(* need to show that if you have a chain 
that is in natSet then you should be able
to get a chain in nat lift.

This seems intuitively obvious because you can take a chain
of elements 
*)
apply (simp add: natSet_def)
apply (rule_tac x="\<Squnion> i. fromNat\<cdot>(Y i)" in exI)
apply (subst contlub_cfun_arg)
apply simp
apply (subgoal_tac "(\<lambda> i. VNat\<cdot>(fromNat\<cdot>(Y i))) = Y")
apply force
apply (rule ext)
apply (erule_tac x="i" in allE)
apply force
done (* should have been simpler? *)

lemma [simp]: "\<lbrakk>\<forall> i. Y i = x; chain Y\<rbrakk> \<Longrightarrow> Lub Y = x"
apply (rule lub_chain_maxelem)
apply (erule_tac x="0" in spec)
apply simp
done

lemma chain_app : "chain Y \<Longrightarrow> chain (\<lambda> i. Y i\<cdot>x)"
apply (rule chainI)
apply (rule monofun_cfun)
apply (erule chainE)
apply simp
done

lemma chain_project : "chain Y \<Longrightarrow> chain (\<lambda> i. fromFun\<cdot>(Y i))"
apply (rule chainI)
apply (rule monofun_cfun)
apply simp
apply (erule chainE)
done

lemma chain_vapp : "chain Y \<Longrightarrow> chain (\<lambda> i. Y i\<bullet>x)"
apply (rule chainI)
apply (rule monofun_cfun)
apply (rule monofun_cfun)
apply simp
apply (erule chainE)
apply simp
done
term "\<Lambda> x. (\<Squnion> i. (Y i\<bullet>x))" 

lemma lub_bot:"\<lbrakk>chain Y; (\<Squnion> i. Y i) = \<bottom>\<rbrakk> \<Longrightarrow> Y i = \<bottom>"
apply (subgoal_tac "Y i \<sqsubseteq> (\<Squnion> i. Y i)")
apply simp thm below_lub
apply (rule_tac i="i" in below_lub)
apply simp
apply simp
done

lemma fun_not_bot : "\<lbrakk>chain Y; \<forall> i. \<exists> f. Y i = VFun\<cdot>f\<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<noteq> \<bottom>"
      apply (rule notI)
      apply (drule_tac x="0" in spec)
      apply (erule exE)
      apply (subgoal_tac "Y 0 = \<bottom>")
      apply simp
      apply (erule lub_bot)
      by simp

lemma fun_not_wrong : "\<lbrakk>chain Y; \<forall> i. \<exists> f. Y i = VFun\<cdot>f\<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<noteq> Wrong"
      apply (rule notI)
      apply (drule_tac x="0" in spec)
      apply (erule exE)
      apply (subgoal_tac "Y 0 \<sqsubseteq> (\<Squnion> i. Y i)")
      apply simp
      apply (rule_tac i=0 in below_lub)
      by simp+
      
lemma fun_not_nat : "\<lbrakk>chain Y; \<forall> i. \<exists> f. Y i = VFun\<cdot>f; n\<noteq>\<bottom>\<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<noteq> (VNat\<cdot>n)"
       apply (rule notI)
       apply (drule_tac x="0" in spec)
       apply (erule exE)
       apply (subgoal_tac "Y 0 \<sqsubseteq> (\<Squnion> i. Y i)")
      apply simp
      apply (rule_tac i=0 in below_lub)
      by simp+

lemma chain_fun_ex : "\<lbrakk>chain Y; \<forall> i. \<exists> f. Y i = VFun\<cdot>f\<rbrakk> \<Longrightarrow> \<exists> f. (\<Squnion> i. Y i) = VFun\<cdot>f"
apply (case_tac "\<Squnion> i. Y i")
apply (simp add: fun_not_bot)
apply (simp add: fun_not_nat)
apply simp

apply (simp add: fun_not_wrong)
done

lemma adm_fun_aux: "\<lbrakk>adm (\<lambda> x. x \<in> B); chain Y; \<forall> i. (\<forall> x. x \<in> A \<longrightarrow> (Y i)\<cdot>x \<in> B); a \<in> A\<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i)\<cdot>a \<in> B"
apply (subgoal_tac "(\<Squnion> i. Y i)\<cdot>a = (\<Squnion> i. Y i\<cdot>a)")
apply simp thm admD
apply (drule_tac P="\<lambda> x. x \<in> B" and Y="\<lambda> i. Y i\<cdot>a" in admD)
apply (erule chain_app)
apply simp
apply simp
apply (rule contlub_cfun_fun)
apply simp
done

lemma [simp] : "x = VFun\<cdot>f \<Longrightarrow> VFun\<cdot>(fromFun\<cdot>x) = x"
apply simp
done

lemma [simp] : "\<lbrakk>(\<Squnion> i. Y i) = VFun\<cdot>f; chain Y\<rbrakk>
        \<Longrightarrow> (\<Squnion> i. fromFun\<cdot>(Y i)) = f"
proof -
assume 0: "(\<Squnion> i. Y i) = VFun\<cdot>f" "chain Y"
have 1: "fromFun\<cdot>(\<Squnion> i. Y i) = f" using 0 by simp
have "fromFun\<cdot>(\<Squnion> i. Y i) = (\<Squnion> i. fromFun\<cdot>(Y i))" using 0 apply -
                                                         apply (rule contlub_cfun_arg)
                                                         by simp
thus ?thesis using 0 1 by simp
qed

lemma thingy: "\<lbrakk>chain Y; \<forall>i. \<exists>f. Y i = VFun\<cdot>f \<and> (\<forall>x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B)\<rbrakk> \<Longrightarrow>
             \<forall>i x. x \<in> A \<longrightarrow> fromFun\<cdot>(Y i)\<cdot>x \<in> B"
apply (rule allI)
apply (rule allI)
apply (rule impI)
apply (drule_tac x="i" in spec)
apply (erule exE)
apply force
done

lemma thingy2: "\<lbrakk>(\<Squnion> i. Y i) = VFun\<cdot>f; chain Y; \<forall> i. \<exists> f. Y i = VFun\<cdot>f \<and> (\<forall> x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B); adm (\<lambda> x. x \<in> B)\<rbrakk> \<Longrightarrow>
          \<forall> x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B"
apply (rule allI)
apply (rule impI)
apply (subgoal_tac "(\<Squnion> i. fromFun\<cdot>(Y i)) = f")
apply (subgoal_tac "(\<Squnion> i. fromFun\<cdot>(Y i))\<cdot>x \<in> B")
apply simp
apply (rule adm_fun_aux)
apply simp
apply simp
defer
apply simp
apply simp
apply (rule thingy)
apply simp
apply simp
done

lemma [simp] :"\<lbrakk>adm (\<lambda> x. x \<in> B)\<rbrakk> \<Longrightarrow> adm (\<lambda> x. x \<in> funSet A B)"
proof (rule admI, simp add: funSet_def, case_tac "\<forall> i. Y i = \<bottom>")
  fix Y :: "nat \<Rightarrow> V"
  assume "\<forall> i. Y i = \<bottom>" "chain Y"
  thus "Lub Y = \<bottom> \<or> (\<exists>f. Lub Y = VFun\<cdot>f \<and> (\<forall>x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B))" by auto
next
  fix Y :: "nat \<Rightarrow> V"
  assume 0: "adm (\<lambda>x. x \<in> B)" "chain Y" "\<forall> i. Y i = \<bottom> \<or> (\<exists>f. Y i = VFun\<cdot>f \<and> (\<forall>x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B))" "\<not> (\<forall> i. Y i = \<bottom>)"
  from 0 have "\<exists> j. Y j \<noteq> \<bottom>" by auto
  hence "\<exists> j. (\<exists> f. Y j = VFun\<cdot>f \<and> (\<forall> x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B))" using 0 by force
  then obtain j f where 1: "Y j = VFun\<cdot>f \<and> (\<forall> x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B)" by blast
  then have "\<forall> i. i \<ge> j \<longrightarrow> Y i \<noteq> \<bottom>" using 0 apply -
                                           apply (rule allI)
                                           apply (drule_tac x="i" in spec)
                                           apply (rule impI)
                                           apply (erule disjE)
                                           defer
                                           apply force
                                           apply (erule conjE)
                                           apply (subgoal_tac "Y j \<sqsubseteq> Y i")
                                           apply (force) thm chainE
                                           apply (erule chain_mono)
                                           apply simp
                                           done
  hence 2: "\<forall> i. i \<ge> j \<longrightarrow> (\<exists> f. Y i = VFun\<cdot>f \<and> (\<forall> x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B))" using 0 by force      
  let ?Z = "\<lambda> i. Y (i + j)"  
  have 3: "chain ?Z" using 0 by (force intro: chain_shift)
  from 2 3 have 4: "\<forall> i. \<exists> f. ?Z i = VFun\<cdot>f \<and> (\<forall> x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B)" by force
  from 3 4 have 5: "\<exists> f. (\<Squnion> i. ?Z i) = VFun\<cdot>f" apply -
                                            apply (rule chain_fun_ex)
                                            apply simp
                                            apply force
                                            done
  then obtain lubf where 6: "(\<Squnion> i. ?Z i) = VFun\<cdot>lubf" by blast
  have 7: "(\<Squnion> i. ?Z i) = (\<Squnion> i. Y i)" using 0 3 by (force intro: lub_range_shift)
  hence "(\<Squnion> i. Y i) = VFun\<cdot>lubf" using 6 by simp 
  thus "Lub Y = \<bottom> \<or> (\<exists>f. Lub Y = VFun\<cdot>f \<and> (\<forall>x. x \<in> A \<longrightarrow> f\<cdot>x \<in> B))" apply -
                                                                  apply (rule disjI2)
                                                                  apply (rule_tac x="lubf" in exI)
                                                                  apply (rule conjI)
                                                                  apply simp
             thm thingy2
             apply (rule thingy2 [of "?Z"])
             apply (rule 6)
             apply (rule 3)
             defer
             apply (simp add: 0)
             apply (rule 4)
             done
qed 
(*>*)

text {* (Talk about admissibility here) *}

lemma [simp]: "adm (\<lambda> x. x \<in> tyM t1)"(*<*)
apply (induct t1)
apply simp
apply simp
done

lemma fixy: "\<lbrakk>\<forall> v \<in> P. f\<cdot>v \<in> P; adm (\<lambda> x. x \<in> P); \<bottom> \<in> P\<rbrakk> \<Longrightarrow> fix\<cdot>f \<in> P"
apply (rule fix_ind)
apply simp
apply simp
apply simp
done (* this is a fact we need for the fixed point case *)(*>*)

text {* Now we come to the most important part of our proof of type-soundness, the fact that the meaning of a term well-typed term inhabits the meaning of its type. We elide the proof, but it follows very straight-forwardly from induction on the typing derivation and repeated casing and simplification on the term structure. *}

lemma "\<lbrakk>lam_ty tys l t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> lamM l\<cdot>\<sigma> \<in> tyM t"
(*<*)
apply (induct arbitrary: \<sigma> rule: lam_ty.induct)
apply (force simp: env_compat_def)
apply simp
apply (case_tac "lamM l1\<cdot>\<sigma>")
apply (case_tac "lamM l2\<cdot>\<sigma>")
apply force
apply force
apply (force simp: natSet_def)
apply (force simp: natSet_def)
apply (case_tac "lamM l2\<cdot>\<sigma>")
apply force
apply (case_tac lifta)
apply simp
apply (case_tac lift)
apply simp
apply (simp add: natSet_def)
apply (force simp: natSet_def)
apply (force simp: natSet_def)
apply (force simp: natSet_def)
apply (force simp: natSet_def)
defer
apply (simp add: natSet_def)
defer
apply simp
apply (case_tac "lamM l1\<cdot>\<sigma>")
apply simp
apply simp
apply (force simp: funSet_def)
apply simp
apply (rule fixy)
apply (force simp: funSet_def)
apply simp
apply simp
apply (force simp: funSet_def)
apply (case_tac "lamM l1\<cdot>\<sigma>")
apply simp
apply (force simp: funSet_def)
apply (force simp: funSet_def)
apply (force simp: funSet_def)
apply simp
apply (simp add: funSet_def env_compat_def)
done
(*>*)

text {* Now, the final piece we need is that Wrong inhabits the meaning of no
        type. This, again, is simply a proof by simplification and follows essentially automatically. *}

lemma "Wrong \<notin> tyM ty"
(*<*)
apply (induct ty)
apply (simp add: natSet_def)
apply (simp add: funSet_def)
done(*>*)

text {* We have now examined a first example of how to define a language, write its denotation function, and prove that the denotation and the typing relation are compatible. In terms of proof engineering, this entire effort was fairly simple once the "right" definition of the meaning of types was given. In the process of first completing this exercise, we found a number of simple errors in our definitions in the process of completing the soundness proof. Essentially, any time that a case didn't follow just by simplification there was an actual mistake in the definitions. 

        The only part of the proof that was non-trivial was the lemmas showing that the sets that were the meaning of types were admissable, but in some ways this problem is solved by moving to ideals as we shall see in the next sections.
*}

(*<*)
end
(*>*)