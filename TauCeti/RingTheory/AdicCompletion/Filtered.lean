/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Completion
public import Mathlib.RingTheory.AdicCompletion.Algebra

import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Ideal-adic and filtered completions

For an ideal `I` of a commutative ring `A`, Mathlib's adic completion `AdicCompletion I A` and the
completion of the ideal-power filtration `I.algFiltration` agree. The filtered completion records
only the quotients by `I ^ (k + 1)`, while the adic completion also records the trivial quotient by
`I ^ 0`; the comparison forgets this redundant coordinate. It commutes with the projections and
with the canonical maps from `A`.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/RingTheory/AdicCompletion/Filtered.lean` (Apache 2.0). The comparison is stated for rings
rather than algebras.
-/

public section

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)

-- The order-`k` quotient of the filtered completion, identified with `A ⧸ I ^ (k + 1)`.
local notation "Q" k => Ideal.quotEquivOfEq (Ideal.algFiltration_ideal I (k + 1))

/-- The order-`k` component of the comparison map: evaluation at `I ^ (k + 1)`. -/
private noncomputable def toAlgFiltrationQuotient (k : ℕ) :
    AdicCompletion I A →+* A ⧸ I.algFiltration.ideal (k + 1) :=
  (Q k).symm.toRingHom.comp (evalₐ I (k + 1)).toRingHom

private theorem toAlgFiltrationQuotient_apply (k : ℕ) (x : AdicCompletion I A) :
    toAlgFiltrationQuotient I k x = (Q k).symm (evalₐ I (k + 1) x) := (rfl)

/-- The ring map from the adic completion to the filtered completion of the ideal-power
filtration. -/
private noncomputable def toAlgFiltrationCompletion :
    AdicCompletion I A →+* I.algFiltration.completion :=
  I.algFiltration.lift (toAlgFiltrationQuotient I)
    (by
      intro k l h
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, toAlgFiltrationQuotient_apply, toAlgFiltrationQuotient_apply]
      rw [← factor_evalₐ (Nat.add_le_add_right h 1) x]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I (l + 1) x)
      rw [← ha]
      simp)

private theorem projection_toAlgFiltrationCompletion (k : ℕ) (x : AdicCompletion I A) :
    I.algFiltration.projection k (toAlgFiltrationCompletion I x) =
      (Q k).symm (evalₐ I (k + 1) x) := by
  simp [toAlgFiltrationCompletion, toAlgFiltrationQuotient_apply]

/-- The order-`n` component of the inverse comparison: the order-`n - 1` projection, followed by
the identification with `A ⧸ I ^ n`. -/
private noncomputable def ofAlgFiltrationQuotient (n : ℕ) :
    I.algFiltration.completion →+* A ⧸ I ^ n :=
  (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp
    ((Q n).toRingHom.comp (I.algFiltration.projection n))

private theorem factorPow_comp_ofAlgFiltrationQuotient {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (ofAlgFiltrationQuotient I n) =
      ofAlgFiltrationQuotient I m := by
  refine RingHom.ext fun x => ?_
  simp only [ofAlgFiltrationQuotient, RingHom.comp_apply]
  rw [← I.algFiltration.factor_projection h x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I.algFiltration.projection n x)
  rw [← ha]
  simp

/-- The ring map from the filtered completion of the ideal-power filtration to the adic
completion. -/
private noncomputable def ofAlgFiltrationCompletion :
    I.algFiltration.completion →+* AdicCompletion I A :=
  liftRingHom I (ofAlgFiltrationQuotient I) (factorPow_comp_ofAlgFiltrationQuotient I)

private theorem evalₐ_ofAlgFiltrationCompletion (n : ℕ) (x : I.algFiltration.completion) :
    evalₐ I (n + 1) (ofAlgFiltrationCompletion I x) = (Q n) (I.algFiltration.projection n x) := by
  rw [ofAlgFiltrationCompletion, evalₐ_liftRingHom]
  simp only [ofAlgFiltrationQuotient, RingHom.comp_apply]
  rw [← I.algFiltration.factor_projection (Nat.le_succ n) x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I.algFiltration.projection (n + 1) x)
  rw [← ha]
  simp

/-- The adic completion is the completion of the ideal-power filtration, with its redundant
order-zero quotient omitted. -/
noncomputable def algFiltrationCompletionEquiv :
    AdicCompletion I A ≃+* I.algFiltration.completion where
  toFun := toAlgFiltrationCompletion I
  invFun := ofAlgFiltrationCompletion I
  left_inv x := by
    refine ext_evalₐ fun n => ?_
    rw [← factor_evalₐ (Nat.le_succ n) x,
      ← factor_evalₐ (Nat.le_succ n) (ofAlgFiltrationCompletion I _),
      evalₐ_ofAlgFiltrationCompletion, projection_toAlgFiltrationCompletion,
      RingEquiv.apply_symm_apply]
  right_inv x := by
    refine I.algFiltration.completion_ext fun k => ?_
    rw [projection_toAlgFiltrationCompletion, evalₐ_ofAlgFiltrationCompletion,
      RingEquiv.symm_apply_apply]
  map_mul' := (toAlgFiltrationCompletion I).map_mul
  map_add' := (toAlgFiltrationCompletion I).map_add

/-- The comparison sends the adic projection to `I ^ (k + 1)` to the order-`k` projection. -/
@[simp]
theorem projection_algFiltrationCompletionEquiv (k : ℕ) (x : AdicCompletion I A) :
    I.algFiltration.projection k (algFiltrationCompletionEquiv I x) =
      (Q k).symm (evalₐ I (k + 1) x) :=
  projection_toAlgFiltrationCompletion I k x

/-- The inverse comparison recovers every positive-order adic projection. -/
@[simp]
theorem evalₐ_algFiltrationCompletionEquiv_symm (k : ℕ) (x : I.algFiltration.completion) :
    evalₐ I (k + 1) ((algFiltrationCompletionEquiv I).symm x) =
      (Q k) (I.algFiltration.projection k x) :=
  evalₐ_ofAlgFiltrationCompletion I k x

/-- The comparison preserves the canonical image of the original ring. -/
@[simp]
theorem algFiltrationCompletionEquiv_of (a : A) :
    algFiltrationCompletionEquiv I (of I A a) = I.algFiltration.toCompletion a := by
  refine I.algFiltration.completion_ext fun k => ?_
  simp

end AdicCompletion
