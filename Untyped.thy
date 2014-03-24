
(*<*)
theory Untyped
imports HOLCF Cenv begin
(*>*)

section {* The Untyped Lambda Calculus: A First Example *}

text {* As a first non-trivial example, let's consider the untyped lambda calculus and how to model
        its denotational semantics using domain theory. *}


text {* First, we define the AST of the untyped lambda calculus as an ordinary Isabelle/HOL AST *}
datatype lam = Lam nat lam | App lam lam | Var nat

text {* Note that we have the standard lambda abstractions,
   applications, and variables. This is a pure lambda calculus
   with no ground elements. Functions all the way down! 
   
   Thus, in order to model the untyped lambda calculus we need some kind of 
   mathematical "set" D such that @{text "D \<approx> D \<rightarrow> D"}. 

   Now in set theory this is obviously an impossibility as the set of
   all mathematical functions from a set to itself is always larger
   than the original set; however, if we instead consider domains instead of sets
   and continuous functions instead of all mathematical functions, we can indeed construct
   such a thing. *}

domain D = DFun "D \<rightarrow> D"

text {* The "domain" command allows us to declare, as a new datatype,
   an appropriate domain for modelling lambda terms. 

   This is declared like a datatype in Haskell, with constructors for
   the various cases. The keyword "lazy" means that the constructor itself
   is lazy and that the @{text "\<lambda> x. \<bottom> \<noteq> \<bottom>"} which is what we want for this language,
   as having a function that diverges on all inputs is not the same 
   as diverging while calculating a function 


   We can also define notation to help us write functions in the domain D. @{text "\<Lambda> x. f x"} is 
   an instance of the *continuous* function abstraction present in HOLCF,
   which helps us write continuous functions more conveniently. Isabelle's
   support for binders \& user-defined notation thus lets us define elements of D
   as @{text "(\<Delta> x. body-of-function)"} *}

abbreviation dLam :: "(D \<Rightarrow> D) \<Rightarrow> D" (binder "\<Delta> " 10) where
"dLam f \<equiv> DFun\<cdot>(\<Lambda> x. f x)"

text {* 

   Since this is the untyped lambda calculus and we can always apply
   a term to any other term, we now define as a continuous operation on the domain
   the function application within the domain D, which is essentially just
   deconstructing an element D into either a function or @{text "\<bottom>"}. 

   Here we define a call-by-name evaluation order where @{text "f\<bullet>\<bottom>"} is not necessarily @{text "\<bottom>"}.

   If we wanted instead to define this as call-by-value we'd have an extra case where
   @{text "f\<bullet>\<bottom> = \<bottom>"}.    
*}

fixrec dApply :: "D \<rightarrow> D \<rightarrow> D" where
"dApply\<cdot>(DFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"dApply\<cdot>\<bottom>\<cdot>x = \<bottom>"

abbreviation dapp :: " D \<Rightarrow> D \<Rightarrow> D" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> dApply\<cdot>f\<cdot>x"

text {* As a quick sanity check, let's just try proving @{text "f\<bullet>\<bottom> = \<bottom>"}. This should fail. *}
lemma "f\<bullet>\<bottom> = \<bottom>"
apply (cases f)
apply simp
apply simp
oops


text {* We can write a denotation function fairly simply now.
   Variables become lookups in the environment,
   applications become application in the domain,
   and lambda abstractions become functional abstraction in the domain
   made by putting the argument in the environment in the appropriate
   place.

   Our environments are simply continuous functions from @{text "nat \<rightarrow> D"},
   with continuous operations @{term sfun_upd} and @{term slookup} that act on the environment.
*}

primrec lamDenote :: "lam \<Rightarrow> D cenv \<Rightarrow> D" where
"lamDenote (Lam n l) \<sigma> = (\<Delta> x. (lamDenote l) (sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x))" |
"lamDenote (Var n) \<sigma> = slookup n\<cdot>\<sigma>" |
"lamDenote (App f a) \<sigma> = (lamDenote f \<sigma>)\<bullet>(lamDenote a \<sigma>)"

text {* Simple Church encodings of numbers and booleans, along with proofs that
   the encodings behave appropriately *}

definition C0 :: lam where
"C0 \<equiv> (Lam 0 (Lam 1 (Var 1)))"

definition C1 :: lam where
"C1 \<equiv> (Lam 0 (Lam 1 (App (Var 0) (Var 1))))"

definition CSucc :: lam where
"CSucc \<equiv> (Lam 0 (Lam 1 (Lam 2 (App (Var 1) (App (App (Var 0) (Var 1)) (Var 2))))))"

lemma "lamDenote (App CSucc C0) \<sigma> = lamDenote C1 \<sigma>"
apply (simp add: CSucc_def C1_def C0_def)
done

definition CTrue :: lam where
"CTrue \<equiv> (Lam 0 (Lam 1 (Var 0)))"

definition CFalse :: lam where
"CFalse \<equiv> (Lam 0 (Lam 1 (Var 1)))"

definition CAnd :: lam where
"CAnd \<equiv> (Lam 0 (Lam 1 (App (App (Var 0) (Var 1)) (Var 0))))"

lemma "lamDenote (App (App CAnd CTrue) CTrue) \<sigma> = lamDenote CTrue \<sigma>"
apply (simp add: CAnd_def CTrue_def)
done

lemma "lamDenote (App (App CAnd CFalse) CTrue) \<sigma> = lamDenote CFalse \<sigma>"
apply (simp add: CAnd_def CTrue_def CFalse_def)
done

lemma "lamDenote CFalse \<sigma> = lamDenote C0 \<sigma>"
apply (simp add: CFalse_def C0_def)
done
(*<*)
end
(*<*)
