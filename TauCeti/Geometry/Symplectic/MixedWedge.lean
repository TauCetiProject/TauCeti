/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import TauCeti.Geometry.Symplectic.Volume
public import TauCeti.LinearAlgebra.Orientation.Basis
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.TwoForm

/-!
# The four-dimensional mixed-wedge lemma

Let `E` be a real vector space containing two planes, spanned by `e₁, f₁` and by `e₂, f₂` and
oriented by these pairs, and let `ω₀` be a two-form that is a product for this splitting: it pairs
the two planes trivially, `ω₀(x, y) = 0` for `x ∈ {e₁, f₁}` and `y ∈ {e₂, f₂}`. If `ω₀` and a
second two-form `β` are both positive on each plane, `ω₀(eᵢ, fᵢ) > 0` and `β(eᵢ, fᵢ) > 0`, then
the four-form `ω₀ ∧ β` is positive on `(e₁, f₁, e₂, f₂)`
(`ContinuousAlternatingMap.pairedWedge_mul_apply_pos_of_cross_eq_zero`). Its value there is
`ω₀(e₁, f₁) β(e₂, f₂) + ω₀(e₂, f₂) β(e₁, f₁)`: the other four terms of the six-term formula
`ContinuousAlternatingMap.pairedWedge_mul_apply_two_two` each contain a value of `ω₀` on a pair
from different planes. No condition is imposed on `β` across the planes.

The square of `ω₀` is positive there as well, with value `2 ω₀(e₁, f₁) ω₀(e₂, f₂)`. If also
`β² > 0` on `(e₁, f₁, e₂, f₂)`, the binomial formula `(a ω₀ + b β)² = a² ω₀² + 2 a b ω₀ ∧ β + b² β²`
shows that every form on the segment from `ω₀` to `β` has positive square there
(`ContinuousAlternatingMap.wedgePow_two_apply_pos_of_mem_segment`). On a four-dimensional space
the volume criterion `ContinuousAlternatingMap.wedgePow_ne_zero_iff` then makes every form on that
segment nondegenerate (`ContinuousAlternatingMap.nondegenerate_of_mem_segment`): the linear
interpolation from `ω₀` to `β` is a path of linear symplectic forms.

Positivity of a top-degree form is a property of an orientation rather than of a basis: its values
on two bases differ by their change-of-basis determinant. When `(e₁, f₁, e₂, f₂)` is a basis,
`ω₀ ∧ β` and the squares along the segment are therefore positive on every basis inducing the
product orientation (`ContinuousAlternatingMap.pairedWedge_mul_apply_basis_pos_of_cross_eq_zero`
and `ContinuousAlternatingMap.wedgePow_two_apply_basis_pos_of_mem_segment`), so the hypotheses and
conclusions are unchanged by orientation-preserving linear changes of coordinates. Pulling all
forms back along a linear map commutes with the wedge
(`ContinuousAlternatingMap.pairedWedge_compContinuousLinearMap`), so the statements may equally be
read for the pullbacks along a linear map of the vectors.

This is the pointwise linear algebra of the interpolation step in Gromov's recognition of the
standard symplectic structures on `ℝ⁴` and on `S² × S²`: for an orientation-preserving map `F`
whose differential carries the two coordinate planes to positive symplectic planes of `ω`, so
that also `(F^* ω)² > 0`, the forms `(1 - t) ω₀ + t F^* ω` are symplectic. This nondegeneracy is
the pointwise input to Moser's argument along that path, which further needs the forms to be
cohomologous and the resulting time-dependent vector field to integrate, for instance by
compactness or compact support of the deformation.

## Main results

* `ContinuousAlternatingMap.pairedWedge_mul_apply_of_cross_eq_zero`: the value of `ω₀ ∧ β` on
  `(e₁, f₁, e₂, f₂)` for a product form `ω₀`.
* `ContinuousAlternatingMap.pairedWedge_mul_apply_pos_of_cross_eq_zero`: the mixed-wedge lemma,
  `ω₀ ∧ β > 0`.
* `ContinuousAlternatingMap.wedgePow_two_apply_of_cross_eq_zero`: the value of `ω₀²`.
* `ContinuousAlternatingMap.wedgePow_two_apply_pos_of_mem_segment`: positivity of the squares
  along the segment from `ω₀` to `β`.
* `ContinuousAlternatingMap.nondegenerate_of_mem_segment`: nondegeneracy of every form on that
  segment, in dimension four.
* `ContinuousAlternatingMap.pairedWedge_mul_apply_basis_pos_of_cross_eq_zero` and
  `ContinuousAlternatingMap.wedgePow_two_apply_basis_pos_of_mem_segment`: the same positivity on
  every basis of the product orientation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, Section 9.4.
-/

public section

open Module

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {ω₀ β : E [⋀^Fin 2]→L[ℝ] ℝ} {e₁ f₁ e₂ f₂ : E}

/-- For a two-form `ω₀` pairing the planes spanned by `e₁, f₁` and by `e₂, f₂` trivially, the
four-form `ω₀ ∧ β` takes on `(e₁, f₁, e₂, f₂)` the value
`ω₀(e₁, f₁) β(e₂, f₂) + ω₀(e₂, f₂) β(e₁, f₁)`, for every two-form `β`. -/
theorem pairedWedge_mul_apply_of_cross_eq_zero (h₁ : ω₀ ![e₁, e₂] = 0) (h₂ : ω₀ ![e₁, f₂] = 0)
    (h₃ : ω₀ ![f₁, e₂] = 0) (h₄ : ω₀ ![f₁, f₂] = 0) (β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ ω₀ β
        ![e₁, f₁, e₂, f₂] =
      ω₀ ![e₁, f₁] * β ![e₂, f₂] + ω₀ ![e₂, f₂] * β ![e₁, f₁] := by
  rw [pairedWedge_mul_apply_two_two, h₁, h₂, h₃, h₄]
  ring

/-- **The mixed-wedge lemma.** Let `ω₀` pair the planes spanned by `e₁, f₁` and by `e₂, f₂`
trivially and be positive on both, `ω₀(eᵢ, fᵢ) > 0`. If a two-form `β` is positive on both planes
as well, then `ω₀ ∧ β` is positive on `(e₁, f₁, e₂, f₂)`. -/
theorem pairedWedge_mul_apply_pos_of_cross_eq_zero (h₁ : ω₀ ![e₁, e₂] = 0)
    (h₂ : ω₀ ![e₁, f₂] = 0) (h₃ : ω₀ ![f₁, e₂] = 0) (h₄ : ω₀ ![f₁, f₂] = 0)
    (hω₁ : 0 < ω₀ ![e₁, f₁]) (hω₂ : 0 < ω₀ ![e₂, f₂]) (hβ₁ : 0 < β ![e₁, f₁])
    (hβ₂ : 0 < β ![e₂, f₂]) :
    0 < pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ ω₀ β
      ![e₁, f₁, e₂, f₂] := by
  rw [pairedWedge_mul_apply_of_cross_eq_zero h₁ h₂ h₃ h₄]
  positivity

/-- For a two-form `ω₀` pairing the planes spanned by `e₁, f₁` and by `e₂, f₂` trivially, the
square `ω₀²` takes on `(e₁, f₁, e₂, f₂)` the value `2 ω₀(e₁, f₁) ω₀(e₂, f₂)`. -/
theorem wedgePow_two_apply_of_cross_eq_zero (h₁ : ω₀ ![e₁, e₂] = 0) (h₂ : ω₀ ![e₁, f₂] = 0)
    (h₃ : ω₀ ![f₁, e₂] = 0) (h₄ : ω₀ ![f₁, f₂] = 0) :
    wedgePow ω₀ 2 ![e₁, f₁, e₂, f₂] = 2 * (ω₀ ![e₁, f₁] * ω₀ ![e₂, f₂]) := by
  rw [wedgePow_two_eq, pairedWedge_mul_apply_of_cross_eq_zero h₁ h₂ h₃ h₄]
  ring

/-- Let `ω₀` pair the planes spanned by `e₁, f₁` and by `e₂, f₂` trivially, and let `ω₀` and `β`
both be positive on both planes. If `β²` is positive on `(e₁, f₁, e₂, f₂)`, then so is the square
of every two-form on the segment from `ω₀` to `β`. -/
theorem wedgePow_two_apply_pos_of_mem_segment (h₁ : ω₀ ![e₁, e₂] = 0) (h₂ : ω₀ ![e₁, f₂] = 0)
    (h₃ : ω₀ ![f₁, e₂] = 0) (h₄ : ω₀ ![f₁, f₂] = 0) (hω₁ : 0 < ω₀ ![e₁, f₁])
    (hω₂ : 0 < ω₀ ![e₂, f₂]) (hβ₁ : 0 < β ![e₁, f₁]) (hβ₂ : 0 < β ![e₂, f₂])
    (hβ : 0 < wedgePow β 2 ![e₁, f₁, e₂, f₂]) {γ : E [⋀^Fin 2]→L[ℝ] ℝ}
    (hγ : γ ∈ segment ℝ ω₀ β) :
    0 < wedgePow γ 2 ![e₁, f₁, e₂, f₂] := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hγ
  have hmix := pairedWedge_mul_apply_pos_of_cross_eq_zero h₁ h₂ h₃ h₄ hω₁ hω₂ hβ₁ hβ₂
  have hω : 0 < wedgePow ω₀ 2 ![e₁, f₁, e₂, f₂] := by
    rw [wedgePow_two_apply_of_cross_eq_zero h₁ h₂ h₃ h₄]
    positivity
  rw [wedgePow_two_add, wedgePow_smul, wedgePow_smul, pairedWedge_smul_left,
    pairedWedge_smul_right]
  simp only [add_apply, smul_apply, smul_eq_mul]
  -- All three terms are nonnegative, and the first or the last is positive since `a + b = 1`.
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    nlinarith
  · nlinarith [mul_pos (mul_pos ha' ha') hω, mul_nonneg (mul_nonneg ha hb) hmix.le,
      mul_nonneg (mul_nonneg hb hb) hβ.le]

/-- On a four-dimensional space, let `ω₀` pair the planes spanned by `e₁, f₁` and by `e₂, f₂`
trivially, and let `ω₀` and `β` both be positive on both planes. If `β²` is positive on
`(e₁, f₁, e₂, f₂)`, then every two-form `γ` on the segment from `ω₀` to `β` is nondegenerate: the
only vector `v` with `γ(v, w) = 0` for every `w` is zero. -/
theorem nondegenerate_of_mem_segment [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4)
    (h₁ : ω₀ ![e₁, e₂] = 0) (h₂ : ω₀ ![e₁, f₂] = 0) (h₃ : ω₀ ![f₁, e₂] = 0)
    (h₄ : ω₀ ![f₁, f₂] = 0) (hω₁ : 0 < ω₀ ![e₁, f₁]) (hω₂ : 0 < ω₀ ![e₂, f₂])
    (hβ₁ : 0 < β ![e₁, f₁]) (hβ₂ : 0 < β ![e₂, f₂]) (hβ : 0 < wedgePow β 2 ![e₁, f₁, e₂, f₂])
    {γ : E [⋀^Fin 2]→L[ℝ] ℝ} (hγ : γ ∈ segment ℝ ω₀ β) (v : E) (hv : ∀ w, γ ![v, w] = 0) :
    v = 0 := by
  refine (wedgePow_ne_zero_iff (n := 2) hE γ).1 (fun h ↦ ?_) v hv
  have hpos := wedgePow_two_apply_pos_of_mem_segment h₁ h₂ h₃ h₄ hω₁ hω₂ hβ₁ hβ₂ hβ hγ
  rw [h] at hpos
  exact lt_irrefl _ hpos

/-- **The mixed-wedge lemma, for an orientation.** Let `(e₁, f₁, e₂, f₂)` be a basis `b₀`, let
`ω₀` pair the planes spanned by `e₁, f₁` and by `e₂, f₂` trivially, and let `ω₀` and `β` both be
positive on both planes. Then `ω₀ ∧ β` is positive on every basis with the orientation of `b₀`. -/
theorem pairedWedge_mul_apply_basis_pos_of_cross_eq_zero {b₀ : Basis (Fin 4) ℝ E}
    (hb₀ : ⇑b₀ = ![e₁, f₁, e₂, f₂]) (h₁ : ω₀ ![e₁, e₂] = 0) (h₂ : ω₀ ![e₁, f₂] = 0)
    (h₃ : ω₀ ![f₁, e₂] = 0) (h₄ : ω₀ ![f₁, f₂] = 0) (hω₁ : 0 < ω₀ ![e₁, f₁])
    (hω₂ : 0 < ω₀ ![e₂, f₂]) (hβ₁ : 0 < β ![e₁, f₁]) (hβ₂ : 0 < β ![e₂, f₂])
    {b : Basis (Fin 4) ℝ E} (hb : b.orientation = b₀.orientation) :
    0 < pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ ω₀ β
      b := by
  refine (toAlternatingMap _).apply_pos_of_orientation_eq hb ?_
  rw [coe_toAlternatingMap, hb₀]
  exact pairedWedge_mul_apply_pos_of_cross_eq_zero h₁ h₂ h₃ h₄ hω₁ hω₂ hβ₁ hβ₂

/-- Let `(e₁, f₁, e₂, f₂)` be a basis `b₀`, let `ω₀` pair the planes spanned by `e₁, f₁` and by
`e₂, f₂` trivially, and let `ω₀` and `β` both be positive on both planes. If `β²` is positive on
`b₀`, then the square of every two-form on the segment from `ω₀` to `β` is positive on every basis
with the orientation of `b₀`. -/
theorem wedgePow_two_apply_basis_pos_of_mem_segment {b₀ : Basis (Fin 4) ℝ E}
    (hb₀ : ⇑b₀ = ![e₁, f₁, e₂, f₂]) (h₁ : ω₀ ![e₁, e₂] = 0) (h₂ : ω₀ ![e₁, f₂] = 0)
    (h₃ : ω₀ ![f₁, e₂] = 0) (h₄ : ω₀ ![f₁, f₂] = 0) (hω₁ : 0 < ω₀ ![e₁, f₁])
    (hω₂ : 0 < ω₀ ![e₂, f₂]) (hβ₁ : 0 < β ![e₁, f₁]) (hβ₂ : 0 < β ![e₂, f₂])
    (hβ : 0 < wedgePow β 2 b₀) {γ : E [⋀^Fin 2]→L[ℝ] ℝ} (hγ : γ ∈ segment ℝ ω₀ β)
    {b : Basis (Fin 4) ℝ E} (hb : b.orientation = b₀.orientation) :
    0 < wedgePow γ 2 b := by
  refine (toAlternatingMap (wedgePow γ 2)).apply_pos_of_orientation_eq hb ?_
  rw [coe_toAlternatingMap, hb₀]
  rw [hb₀] at hβ
  exact wedgePow_two_apply_pos_of_mem_segment h₁ h₂ h₃ h₄ hω₁ hω₂ hβ₁ hβ₂ hβ hγ

end ContinuousAlternatingMap
