/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
public import TauCeti.LinearAlgebra.ExteriorPower.NumberOperator
import Mathlib.Data.Nat.Choose.Cast

/-!
# Contraction norm sums

For an orthonormal basis `(eᵢ)`, the squared norms of all single contractions of a
`p`-vector sum to `p` times its squared norm. The squared norms of the double
contractions, summed over `i < j`, sum to `p.choose 2` times its squared norm.
The corresponding identities on continuous alternating forms use the Gram inner
product `TauCeti.alternatingFormInner`, rather than the operator norm.

These are the pointwise counting identities for curvature estimates on forms.
They follow from the algebraic number operators in
`Module.Basis.sum_wedgeLeft_comp_koszulDifferential_coord` and
`Module.Basis.sum_wedgeLeft_comp_wedgeLeft_comp_koszulDifferential_comp_koszulDifferential_coord`,
using the adjoint identity `TauCeti.inner_wedgeLeft_eq_inner_koszulDifferential`.
The form statements use the existing musical identification `TauCeti.alternatingFormEquiv`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, §6.1.
-/

public section

noncomputable section

open TauCeti
open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- The squared norms of the coordinate contractions of a positive-degree vector sum
to its degree times its squared norm. -/
@[simp]
theorem sum_norm_koszulDifferential_sq (n : ℕ) (x : ⋀[ℝ]^(n + 1) V) :
    ∑ i, ‖koszulDifferential (innerₗ V (b i)) n x‖ ^ 2 =
      (n + 1 : ℝ) * ‖x‖ ^ 2 := by
  have h := congrArg (fun A : Module.End ℝ (⋀[ℝ]^(n + 1) V) ↦ ⟪A x, x⟫)
    (b.toBasis.sum_wedgeLeft_comp_koszulDifferential_coord n)
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, b.coe_toBasis,
    b.toBasis_coord_real,
    sum_inner, inner_wedgeLeft_eq_inner_koszulDifferential, real_inner_self_eq_norm_sq,
    ← Nat.cast_smul_eq_nsmul ℝ, LinearMap.smul_apply, LinearMap.id_apply,
    real_inner_smul_left, Nat.cast_add, Nat.cast_one] using h

/-- Summing double-contraction squared norms over all ordered pairs gives the
degree times one less than the degree, times the squared norm of the vector. Diagonal
contractions vanish automatically. -/
theorem sum_sum_norm_koszulDifferential_sq (n : ℕ) (x : ⋀[ℝ]^(n + 2) V) :
    ∑ j, ∑ i, ‖koszulDifferential (innerₗ V (b i)) n
      (koszulDifferential (innerₗ V (b j)) (n + 1) x)‖ ^ 2 =
      (n + 2 : ℝ) * (n + 1 : ℝ) * ‖x‖ ^ 2 := by
  simp_rw [b.sum_norm_koszulDifferential_sq n]
  rw [← Finset.mul_sum, b.sum_norm_koszulDifferential_sq (n + 1)]
  push_cast
  ring

/-- The squared norms of the double contractions, over increasing pairs, sum to the
binomial coefficient of the degree times the squared norm. -/
@[simp]
theorem sum_norm_koszulDifferential_koszulDifferential_sq [LinearOrder ι] (n : ℕ)
    (x : ⋀[ℝ]^(n + 2) V) :
    ∑ ij ∈ Finset.univ.filter (fun ij : ι × ι ↦ ij.1 < ij.2),
      ‖koszulDifferential (innerₗ V (b ij.1)) n
        (koszulDifferential (innerₗ V (b ij.2)) (n + 1) x)‖ ^ 2 =
      ((n + 2).choose 2 : ℝ) * ‖x‖ ^ 2 := by
  have h := congrArg (fun A : Module.End ℝ (⋀[ℝ]^(n + 2) V) ↦ ⟪A x, x⟫)
    (b.toBasis.sum_wedgeLeft_comp_wedgeLeft_comp_koszulDifferential_comp_koszulDifferential_coord n)
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, b.coe_toBasis,
    b.toBasis_coord_real,
    sum_inner, inner_wedgeLeft_eq_inner_koszulDifferential, real_inner_self_eq_norm_sq,
    ← Nat.cast_smul_eq_nsmul ℝ, LinearMap.smul_apply, LinearMap.id_apply,
    real_inner_smul_left] using h

/-- The Gram squared norms of the contractions of a positive-degree alternating form
sum to its degree times its Gram squared norm. -/
@[simp]
theorem sum_alternatingFormInner_curryLeft {n : ℕ}
    (α : V [⋀^Fin (n + 1)]→L[ℝ] ℝ) :
    ∑ i, alternatingFormInner V n (α.curryLeft (b i)) (α.curryLeft (b i)) =
      (n + 1 : ℝ) * alternatingFormInner V (n + 1) α α := by
  obtain ⟨x, rfl⟩ := (alternatingFormEquiv V (n + 1)).surjective α
  simp only [← alternatingFormEquiv_koszulDifferential,
    alternatingFormInner_alternatingFormEquiv, real_inner_self_eq_norm_sq]
  exact b.sum_norm_koszulDifferential_sq n x

/-- The Gram squared norms of double contractions over all ordered pairs sum to the
degree times one less than the degree times the Gram squared norm of the form. -/
theorem sum_sum_alternatingFormInner_curryLeft_curryLeft {n : ℕ}
    (α : V [⋀^Fin (n + 2)]→L[ℝ] ℝ) :
    ∑ j, ∑ i, alternatingFormInner V n ((α.curryLeft (b j)).curryLeft (b i))
      ((α.curryLeft (b j)).curryLeft (b i)) =
      (n + 2 : ℝ) * (n + 1 : ℝ) * alternatingFormInner V (n + 2) α α := by
  obtain ⟨x, rfl⟩ := (alternatingFormEquiv V (n + 2)).surjective α
  simp only [← alternatingFormEquiv_koszulDifferential,
    alternatingFormInner_alternatingFormEquiv, real_inner_self_eq_norm_sq]
  exact b.sum_sum_norm_koszulDifferential_sq n x

/-- The Gram squared norms of double contractions of a form, over increasing pairs,
sum to the binomial coefficient of its degree times its Gram squared norm. -/
@[simp]
theorem sum_alternatingFormInner_curryLeft_curryLeft [LinearOrder ι]
    {n : ℕ} (α : V [⋀^Fin (n + 2)]→L[ℝ] ℝ) :
    ∑ ij ∈ Finset.univ.filter (fun ij : ι × ι ↦ ij.1 < ij.2),
      alternatingFormInner V n ((α.curryLeft (b ij.2)).curryLeft (b ij.1))
        ((α.curryLeft (b ij.2)).curryLeft (b ij.1)) =
      ((n + 2).choose 2 : ℝ) * alternatingFormInner V (n + 2) α α := by
  obtain ⟨x, rfl⟩ := (alternatingFormEquiv V (n + 2)).surjective α
  simp only [← alternatingFormEquiv_koszulDifferential,
    alternatingFormInner_alternatingFormEquiv, real_inner_self_eq_norm_sq]
  exact b.sum_norm_koszulDifferential_koszulDifferential_sq n x

/-- The ordered double-contraction Gram norm sum is twice the increasing-pair sum.
Thus the two curvature-contraction conventions have an explicit factor of two. -/
theorem sum_sum_alternatingFormInner_curryLeft_curryLeft_eq_two_mul [LinearOrder ι]
    {n : ℕ} (α : V [⋀^Fin (n + 2)]→L[ℝ] ℝ) :
    (∑ j, ∑ i, alternatingFormInner V n ((α.curryLeft (b j)).curryLeft (b i))
      ((α.curryLeft (b j)).curryLeft (b i))) =
      2 * ∑ ij ∈ Finset.univ.filter (fun ij : ι × ι ↦ ij.1 < ij.2),
        alternatingFormInner V n ((α.curryLeft (b ij.2)).curryLeft (b ij.1))
          ((α.curryLeft (b ij.2)).curryLeft (b ij.1)) := by
  rw [sum_sum_alternatingFormInner_curryLeft_curryLeft,
    sum_alternatingFormInner_curryLeft_curryLeft, Nat.cast_choose_two]
  push_cast
  ring

end OrthonormalBasis
