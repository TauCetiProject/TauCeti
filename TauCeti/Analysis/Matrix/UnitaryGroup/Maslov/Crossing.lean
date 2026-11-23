/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization

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
path of symmetric matrices,
`Matrix.signature_sub_signature_eq_crossingForm_add_two_mul_finsum`.

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
  -- The localization axiom: the index is half the change of the signature of `A`.
  have hloc := maslovIndex_eq_signature_sub_of_souriau_eq_cayley γ (A := fun t : I ↦ A t)
    (hAc.comp_continuous continuous_subtypeVal fun t ↦ t.property) (fun t ↦ hA t t.property) hγ
  simp only [Icc.coe_one, Icc.coe_zero] at hloc
  rw [hloc, ← Int.cast_sub, signature_sub_signature_eq_crossingForm_add_two_mul_finsum zero_lt_one
    hAc (fun t ht ↦ (hA t ht).isSymm) hd hreg]
  push_cast
  ring

end UnitaryGroup

end Matrix
