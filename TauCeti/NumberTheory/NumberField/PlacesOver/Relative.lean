/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.Ramification
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Relative absolute values at finite places

A finite place of an extension restricts to the local-degree power of the base place. Taking
its positive local-degree root therefore gives an absolute value restricting to the base
place exactly. This normalization is needed when measuring algebraic coefficients at a place
of the field of rational points.

The construction follows the local-degree root used in the finite-place classification in
Ralf Stephan's `DiophantineApproximation/PlacesOverFinite.lean` in
`rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3.
-/

public section

namespace NumberField.FinitePlace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- The absolute value of a finite place, raised to the reciprocal of its local degree over
`K`. Unlike the finite place itself, it restricts to the base place without a power. -/
noncomputable def relativeAbsValue (w : FinitePlace F) (K : Type*) [Field K] [NumberField K]
    [Algebra K F] : AbsoluteValue F ℝ :=
  w.1.nonarchRpow w.add_le (inv_pos.mpr (Nat.cast_pos.mpr (w.localDegree_pos (K := K))))

/-- Evaluation of the relative absolute value. The bundled form is retained by the simplifier
so that local-degree cancellation simplifies without expanding real powers. -/
theorem relativeAbsValue_apply (w : FinitePlace F) (x : F) :
    w.relativeAbsValue K x = w x ^ (w.localDegree K : ℝ)⁻¹ := by
  unfold relativeAbsValue
  exact AbsoluteValue.nonarchRpow_apply _ _ _ _

/-- Raising the relative absolute value to the local degree recovers the finite place. -/
@[simp]
theorem relativeAbsValue_pow_localDegree (w : FinitePlace F) (x : F) :
    w.relativeAbsValue K x ^ w.localDegree K = w x := by
  rw [relativeAbsValue_apply]
  exact Real.rpow_inv_natCast_pow (apply_nonneg _ _) w.localDegree_pos.ne'

/-- Taking the local-degree root preserves the equivalence class of a finite place. -/
theorem isEquiv_relativeAbsValue (w : FinitePlace F) :
    w.1.IsEquiv (w.relativeAbsValue K) := by
  rw [relativeAbsValue]
  exact AbsoluteValue.isEquiv_nonarchRpow _ _ _

/-- The relative absolute value restricts to the underlying base place exactly. -/
theorem relativeAbsValue_algebraMap (w : FinitePlace F) (v : FinitePlace K)
    [w.LiesOver v] (x : K) : w.relativeAbsValue K (algebraMap K F x) = v x := by
  rw [relativeAbsValue_apply, apply_algebraMap w v,
    Real.pow_rpow_inv_natCast (apply_nonneg _ _) w.localDegree_pos.ne']

/-- The relative absolute value lies over the underlying absolute value of the base place. -/
instance (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v] :
    (w.relativeAbsValue K).LiesOver v.1 :=
  ⟨AbsoluteValue.ext fun x ↦ by
    rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, relativeAbsValue_algebraMap w v,
      coe_apply]⟩

/-- Distinct finite places give distinct relative absolute values. -/
theorem relativeAbsValue_injective :
    Function.Injective (fun w : FinitePlace F ↦ w.relativeAbsValue K) := by
  intro w u h
  dsimp only at h
  have he : (w.relativeAbsValue K).IsEquiv (u.relativeAbsValue K) := h ▸ .rfl
  exact eq_iff_isEquiv.mpr ((w.isEquiv_relativeAbsValue (K := K)).trans
    (he.trans (u.isEquiv_relativeAbsValue (K := K)).symm))

end NumberField.FinitePlace
