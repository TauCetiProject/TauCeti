/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
import TauCeti.Analysis.Matrix.HermitianSignature.RegularCrossings
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# The crossing form formula for the Maslov index of a path of graphs

Let `t ↦ A t` be a path of real symmetric matrices on `[0, 1]`, and `γ` a path of unitary frames
of the Lagrangian graphs `Λ t = {x + i A t x}`, so that the Souriau maps `γ t γ tᵀ` are the Cayley
transforms of `A t`. The graph `Λ t` meets the fixed Lagrangian `ℝⁿ` in the kernel of `A t`, so
the *crossings* of the path relative to `ℝⁿ` are the parameters at which `A t` is singular. At a
crossing `t` the *crossing form* of Robbin and Salamon is the quadratic form `x ↦ x ⬝ᵥ A' t *ᵥ x`
of the derivative of `A`, restricted to the kernel of `A t` (`Matrix.crossingForm`): for `x` in
that kernel, `x + i (A s - A t) x` is the point of `Λ s` above `x`, and the symplectic form
`Im ⟪·, ·⟫` pairs `x` with its displacement to `x ⬝ᵥ (A s - A t) *ᵥ x`. A crossing is *regular*
when its crossing form is nondegenerate.

If every crossing is regular, the Maslov index of `γ` is the sum of the signatures of the
crossing forms, the crossings at the endpoints `0` and `1` counting one half
(`Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`):

`μ(γ) = (sign Γ(0) + sign Γ(1)) / 2 + ∑ᶠ t ∈ (0, 1), sign Γ(t)`.

This compares the definition of the Maslov index for paths by crossing forms (Robbin–Salamon,
§2) with the spectral definition `Matrix.UnitaryGroup.maslovIndex`, for the paths of Lagrangians
transverse to `iℝⁿ`, which are exactly the graphs `{x + i A x}` of symmetric matrices. The proof
combines the localization axiom
`Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley`, which gives the index as
half the change of the signature of `A`, with the regular-crossing formula for the signature of a
path of symmetric forms,
`ContinuousLinearMap.sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum`,
applied to the bilinear forms `(x, y) ↦ x ⬝ᵥ A t *ᵥ y` (`Matrix.toContinuousLinearMap₂'`).

Matrices carry no preferred norm, so the derivative of `A` at a crossing is asked for entry by
entry.

## Main results

* `Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`: the crossing
  form formula for the Maslov index of a path of graphs with regular crossings.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Section 2 (crossing forms, and the Maslov index of a path with regular crossings as the sum of
  their signatures, with half weights at the endpoints).
-/

public section

open Set
open scoped unitInterval

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace UnitaryGroup

/-- **The crossing form formula for the Maslov index of a path of graphs.** Let `t ↦ A t` be a
path of real symmetric matrices, continuous on `[0, 1]`, and `γ` a path of unitary frames of their
graphs `{x + i A t x}`, that is, with Souriau maps `γ t γ tᵀ` the Cayley transforms of `A t`.
Suppose that at every crossing `t ∈ [0, 1]`, where `A t` is singular, `A` has entrywise derivative
`A' t` within `[0, 1]` and the crossing form `Matrix.crossingForm (A t) (A' t)` is nondegenerate.
Then the Maslov index of `γ` relative to `ℝⁿ` is the sum of the signatures of the crossing forms,
the crossings at the endpoints counting one half. Parameters where `A t` is invertible contribute
zero. -/
theorem maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley {U V : unitaryGroup n ℂ}
    (γ : Path U V) {A A' : ℝ → Matrix n n ℝ} (hAc : ContinuousOn A (Icc 0 1))
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, (A t).IsHermitian)
    (hγ : ∀ t : I, (souriau (γ t) : Matrix n n ℂ) = cayley ((A t).map ((↑) : ℝ → ℂ)))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 → (crossingForm (A t) (A' t)).Nondegenerate) :
    maslovIndex γ =
      (((sigPos (crossingForm (A 0) (A' 0)) : ℤ) - sigNeg (crossingForm (A 0) (A' 0)) +
        ((sigPos (crossingForm (A 1) (A' 1)) : ℤ) - sigNeg (crossingForm (A 1) (A' 1))) : ℤ) :
          ℝ) / 2 +
      ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) : ℤ) :
          ℝ) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  -- The localization axiom: the index is half the change of the signature of `A`.
  have hloc := maslovIndex_eq_signature_sub_of_souriau_eq_cayley γ (A := fun t : I ↦ A t)
    (hAc.comp_continuous continuous_subtype_val fun t ↦ t.2) (fun t ↦ hA t t.2) hγ
  simp only [Icc.coe_one, Icc.coe_zero] at hloc
  -- The signature formula for the bilinear forms of `A`.
  have hsig :=
    ContinuousLinearMap.sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum
    (V := fun t ↦ (A t).toContinuousLinearMap₂') (V' := fun t ↦ (A' t).toContinuousLinearMap₂')
    zero_lt_one (continuousOn_toContinuousLinearMap₂' hAc)
    (fun t ht ↦ isSymm_toBilinForm_toContinuousLinearMap₂' (hA t ht).isSymm)
    (fun t ht hnt ↦ hasDerivWithinAt_toContinuousLinearMap₂' (hd t ht (not_not.1 fun h ↦
      hnt ((nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero _).2 h))))
    (fun t ht hnt ↦ (crossingFormIsometryEquiv (hA t ht).isSymm (A' t)).nondegenerate_iff.2
      (hreg t ht (not_not.1 fun h ↦
        hnt ((nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero _).2 h))))
  have hΓ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (sigPos (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
          (A' t).toContinuousLinearMap₂') : ℤ) -
          sigNeg (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
            (A' t).toContinuousLinearMap₂') =
        (sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t)) := by
    have h : QuadraticMap.Equivalent _ _ := ⟨crossingFormIsometryEquiv (hA t ht).isSymm (A' t)⟩
    rw [h.sigPos_eq, h.sigNeg_eq]
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
            (A' t).toContinuousLinearMap₂') : ℤ) -
          sigNeg (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
            (A' t).toContinuousLinearMap₂')) =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) :=
    finsum_mem_congr rfl fun t ht ↦ hΓ t (Ioo_subset_Icc_self ht)
  simp only [toQuadraticMap_toBilinForm_toContinuousLinearMap₂', hΓ 0 h0, hΓ 1 h1, hsum] at hsig
  rw [hloc, signature_def, signature_def, ← Int.cast_sub, hsig]
  push_cast
  ring

end UnitaryGroup

end Matrix
