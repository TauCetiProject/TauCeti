/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of the canonical polynomial presentation

For a commutative `R`-algebra `S`, the two canonical maps `R[R[S]] ⇉ R[S]`
are evaluation of polynomial variables and renaming by their values in `S`.
Their composites with the augmentation agree, and their difference has image
exactly the augmentation kernel. This is exactness at `R[S]` of the underlying
module complex of the standard polynomial resolution (Stacks Project, Tag 08PM).
-/

public noncomputable section

namespace MvPolynomial

/-- Evaluation in `S` coequalizes variable renaming by evaluation and evaluation of
polynomial variables. -/
lemma aeval_id_comp_rename_aeval_id {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] :
    (aeval (R := R) (id : S → S)).comp (rename (aeval (id : S → S))) =
      (aeval (R := R) (id : S → S)).comp
        (aeval (id : MvPolynomial S R → MvPolynomial S R)) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp

/-- The difference of the two canonical polynomial face maps has image exactly the
augmentation kernel. The algebra and coefficient ring may lie in independent universes. -/
theorem exact_aeval_sub_rename {R S : Type*} [CommRing R] [CommSemiring S] [Algebra R S] :
    Function.Exact
      ((aeval (R := R) (id : MvPolynomial S R → MvPolynomial S R)).toLinearMap -
        (rename (R := R) (aeval (R := R) (id : S → S))).toLinearMap)
      (aeval (R := R) (id : S → S)).toLinearMap := by
  let : AddCommGroup S := Module.addCommMonoidToAddCommGroup R
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro p
    have h := DFunLike.congr_fun (aeval_id_comp_rename_aeval_id (R := R) (S := S)) p
    simpa using sub_eq_zero.mpr h.symm
  · intro p hp
    refine ⟨X p - X (0 : MvPolynomial S R), ?_⟩
    have hp' : aeval (R := R) (id : S → S) p = 0 := hp
    simp [hp']

end MvPolynomial
