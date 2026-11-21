/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.BracketWedge
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import Mathlib.Analysis.Matrix.Normed

/-!
# Commutator wedges and curvature normalization

For forms with values in a normed real algebra, the wedge paired with the commutator is
exactly the graded commutator of the multiplication wedges. In particular, for an
algebra-valued one-form `A`, half of its bracket wedge with itself is `A ∧ A`.
This identifies the quadratic terms in the curvature conventions
`F = dA + A ∧ A` and `F = dA + ½[A ∧ A]`, including noncommutative coefficients.
Multiplication of endomorphisms means composition in the order appropriate to column
section coefficients.

The products are the existing `TauCeti.bracketWedge` and
`ContinuousAlternatingMap.wedgeMul`; no additional product or form carrier is introduced.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I,
  Chapter II (structure equation and Lie-algebra-valued forms).
* Loring W. Tu, *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  Graduate Texts in Mathematics 275, Springer, 2017, §21.
-/

public section

noncomputable section

open TauCeti

namespace ContinuousAlternatingMap

variable {E A : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] {k l : ℕ}

/-- The wedge paired with the algebra commutator is the graded commutator of multiplication
wedges. The cast identifies the degrees of the two orders of multiplication. -/
theorem bracketWedge_commutator_apply
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A)
    (v : Fin (k + l) → E) :
    bracketWedge (ContinuousLinearMap.mul ℝ A - (ContinuousLinearMap.mul ℝ A).flip) φ ψ v =
      wedgeMul φ ψ v - (-1 : ℝ) ^ (k * l) •
        wedgeMul ψ φ (v ∘ Fin.cast (Nat.add_comm l k)) := by
  have hflip : ((ContinuousLinearMap.mul ℝ A).flip).pairingFlip
      ((ContinuousLinearMap.mul ℝ A).flip.continuous₂) = ContinuousLinearMap.mul ℝ A := by
    ext a b
    simp [ContinuousLinearMap.pairingFlip_apply]
  rw [bracketWedge_def, ← pairedWedgeCLM_apply, map_sub]
  simp only [_root_.sub_apply, sub_apply, pairedWedgeCLM_apply]
  rw [pairedWedge_flip (ContinuousLinearMap.mul ℝ A).flip]
  simp only [hflip, wedgeMul_def]

/-- For an odd-degree algebra-valued form, its bracket square is twice its multiplication
square. This applies to connection one-forms without a commutativity assumption. -/
theorem bracketWedge_commutator_self_of_odd (φ : E [⋀^Fin k]→L[ℝ] A) (hk : Odd k) :
    bracketWedge (ContinuousLinearMap.mul ℝ A - (ContinuousLinearMap.mul ℝ A).flip) φ φ =
      (2 : ℝ) • wedgeMul φ φ := by
  ext v
  rw [bracketWedge_commutator_apply]
  simp [(hk.mul hk).neg_one_pow, two_smul ℝ]

/-- The bracket square of an even-degree algebra-valued form vanishes. Its multiplication
square need not vanish. -/
@[simp]
theorem bracketWedge_commutator_self_of_even (φ : E [⋀^Fin k]→L[ℝ] A) (hk : Even k) :
    bracketWedge (ContinuousLinearMap.mul ℝ A - (ContinuousLinearMap.mul ℝ A).flip) φ φ = 0 := by
  ext v
  rw [bracketWedge_commutator_apply]
  simp [hk.mul_right k]

/-- Half the bracket square of an algebra-valued one-form is its multiplication wedge square,
fixing the factor in the two usual curvature structure equations. -/
@[simp]
theorem half_bracketWedge_commutator_self (φ : E [⋀^Fin 1]→L[ℝ] A) :
    (2 : ℝ)⁻¹ •
        bracketWedge (ContinuousLinearMap.mul ℝ A - (ContinuousLinearMap.mul ℝ A).flip) φ φ =
      wedgeMul φ φ := by
  rw [bracketWedge_commutator_self_of_odd φ (by decide), smul_smul]
  norm_num

section Matrix

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι]

open Classical in
/-- Half the bracket square of a matrix-valued one-form has the entrywise matrix-wedge
formula. The order `i,t` followed by `t,j` is the convention for column section coefficients. -/
theorem half_bracketWedge_commutator_matrix_apply
    (φ : E [⋀^Fin 1]→L[ℝ] Matrix ι ι A) (v w : E) (i j : ι) :
    ((2 : ℝ)⁻¹ • bracketWedge
        (ContinuousLinearMap.mul ℝ (Matrix ι ι A) -
          (ContinuousLinearMap.mul ℝ (Matrix ι ι A)).flip) φ φ) ![v, w] i j =
      ∑ t, (φ ![v] i t * φ ![w] t j - φ ![w] i t * φ ![v] t j) := by
  -- The scoped matrix norm induces the native additive/module structures only after reduction.
  erw [half_bracketWedge_commutator_self, wedgeMul_apply_one_one]
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  rfl

end Matrix

end ContinuousAlternatingMap
