/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Torus
public import TauCeti.Topology.Constructions.DoubleAlong.Annulus
public import TauCeti.Topology.Constructions.DoubleAlong.Disc

/-!
# Euler characteristics of the doubled disc and the doubled annulus

The Euler characteristic of the double of a compact surface along its whole boundary is twice the
Euler characteristic of the surface. This file checks this on the two basic examples, using the
homeomorphisms of `TauCeti.DoubleAlong.discDoubleHomeomorph` and
`TauCeti.DoubleAlong.annulusDoubleHomeomorph`:

* the closed unit disc is contractible, so `χ = 1`, and its double is the Riemann sphere
  `OnePoint ℂ`, so `χ = 2 = 2 · 1`;
* the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁ ≤ r₂` is homeomorphic to `Circle × [r₁, r₂]`
  by polar coordinates, so `χ = 0 · 1 = 0`, and for `r₁ < r₂` its double is the torus
  `Circle × Circle`, so `χ = 0 = 2 · 0`.

In both cases the fixed set of the sheet exchange is the boundary: one circle for the disc
(`TauCeti.DoubleAlong.discDoubleHomeomorph_image_fixed_eq_sphere`) and two circles for the annulus
(`TauCeti.DoubleAlong.annulusDoubleHomeomorph_image_fixed`).

The Euler characteristic is `TauCeti.eulerChar`, defined for spaces of finite CW type. The closed
balls of a real normed space and the closed annuli in `ℂ` have finite CW type for all radii (the
degenerate ones are empty or a closed ball), so these are instances.

## Main declarations

* `TauCeti.finiteCWType_closedBall`, `TauCeti.eulerChar_closedBall`: a closed ball of nonnegative
  radius in a real normed space has `χ = 1`.
* `TauCeti.finiteCWType_closedAnnulus`, `TauCeti.eulerChar_closedAnnulus`: a closed annulus with
  `0 < r₁ ≤ r₂` has `χ = 0`.
* `TauCeti.DoubleAlong.eulerChar_discDouble`, `TauCeti.DoubleAlong.eulerChar_discDouble_eq_two_mul`:
  the doubled disc has `χ = 2 = 2 · χ(disc)`.
* `TauCeti.DoubleAlong.eulerChar_annulusDouble`,
  `TauCeti.DoubleAlong.eulerChar_annulusDouble_eq_two_mul`: the doubled annulus has
  `χ = 0 = 2 · χ(annulus)`; its finite CW type is `TauCeti.DoubleAlong.finiteCWType_annulusDouble`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, the double of a
  bordered Riemann surface.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Complex Metric Set

namespace TauCeti

/-! ### The closed ball -/

section ClosedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed ball in a real normed space has finite CW type: it is contractible for a nonnegative
radius and empty otherwise. -/
instance finiteCWType_closedBall (x : E) (r : ℝ) : FiniteCWType (closedBall x r) := by
  rcases le_or_gt 0 r with hr | hr
  · have := contractibleSpace_closedBall (x := x) hr
    infer_instance
  · have : IsEmpty (closedBall x r) := by
      rw [isEmpty_coe_sort, closedBall_eq_empty]
      exact hr
    exact FiniteCWType.of_discreteTopology _

/-- A closed ball of nonnegative radius in a real normed space has Euler characteristic one. -/
theorem eulerChar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) : eulerChar (closedBall x r) = 1 :=
  have := contractibleSpace_closedBall (x := x) hr
  eulerChar_of_contractibleSpace

end ClosedBall

/-! ### The closed annulus -/

section ClosedAnnulus

variable {r₁ r₂ : ℝ}

/-- Polar coordinates on the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁`: the direction
`z / ‖z‖` and the modulus `‖z‖`. -/
private noncomputable def closedAnnulusHomeomorph (h₀ : 0 < r₁) :
    closedAnnulus r₁ r₂ ≃ₜ Circle × Icc r₁ r₂ where
  toFun z :=
    have hz : (z : ℂ) ≠ 0 := norm_pos_iff.1 (h₀.trans_le (mem_closedAnnulus.1 z.2).1)
    (Circle.homeomorphSphere.symm (homeomorphUnitSphereProd ℂ ⟨z, hz⟩).1,
      ⟨‖(z : ℂ)‖, mem_closedAnnulus.1 z.2⟩)
  invFun p := ⟨(p.2 : ℝ) • (p.1 : ℂ), by
    have h2 := p.2.2
    rw [mem_closedAnnulus, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg
      (h₀.le.trans h2.1)]
    exact h2⟩
  left_inv z := by
    have hz : (z : ℂ) ≠ 0 := norm_pos_iff.1 (h₀.trans_le (mem_closedAnnulus.1 z.2).1)
    ext1
    simp [hz]
  right_inv p := by
    have ht : 0 < (p.2 : ℝ) := h₀.trans_le p.2.2.1
    ext
    · simp [abs_of_pos ht, ht.ne']
    · simp [abs_of_pos ht]
  continuous_toFun := by
    refine .prodMk (Circle.homeomorphSphere.symm.continuous.comp (continuous_fst.comp
      ((homeomorphUnitSphereProd ℂ).continuous.comp (continuous_subtype_val.subtype_mk _))))
      (continuous_subtype_val.norm.subtype_mk _)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- A closed annulus in `ℂ` has finite CW type: for `0 < r₁ ≤ r₂` it is homeomorphic to
`Circle × [r₁, r₂]`, for `r₁ ≤ 0 ≤ r₂` it is the closed ball of radius `r₂`, and otherwise it is
empty. -/
instance finiteCWType_closedAnnulus (r₁ r₂ : ℝ) : FiniteCWType (closedAnnulus r₁ r₂) := by
  rcases le_or_gt r₁ 0 with h₀ | h₀
  · have : closedAnnulus r₁ r₂ = closedBall 0 r₂ := by
      ext z
      rw [mem_closedAnnulus, mem_closedBall_zero_iff]
      exact ⟨And.right, fun h ↦ ⟨h₀.trans (norm_nonneg _), h⟩⟩
    rw [this]
    infer_instance
  rcases le_or_gt r₁ r₂ with h | h
  · have := (convex_Icc r₁ r₂).contractibleSpace (nonempty_Icc.2 h)
    exact (closedAnnulusHomeomorph h₀).finiteCWType
  · have : IsEmpty (closedAnnulus r₁ r₂) :=
      ⟨fun z ↦ (mem_closedAnnulus.1 z.2).1.trans (mem_closedAnnulus.1 z.2).2 |>.not_gt h⟩
    exact FiniteCWType.of_discreteTopology _

/-- A closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁ ≤ r₂` has Euler characteristic zero, that of
`Circle × [r₁, r₂]`. -/
theorem eulerChar_closedAnnulus (h₀ : 0 < r₁) (h : r₁ ≤ r₂) :
    eulerChar (closedAnnulus r₁ r₂) = 0 := by
  have := (convex_Icc r₁ r₂).contractibleSpace (nonempty_Icc.2 h)
  rw [(closedAnnulusHomeomorph h₀).eulerChar_eq, eulerChar_prod, eulerChar_circle, zero_mul]

end ClosedAnnulus

namespace DoubleAlong

/-! ### The doubled disc -/

/-- The doubled closed disc has finite CW type, being homeomorphic to the Riemann sphere. -/
instance finiteCWType_discDouble : FiniteCWType (DoubleAlong discBoundary) :=
  discDoubleHomeomorph.finiteCWType

/-- **Euler characteristic of the doubled disc.** The closed unit disc doubled along its boundary
circle is the Riemann sphere, with Euler characteristic `2`. -/
@[simp]
theorem eulerChar_discDouble : eulerChar (DoubleAlong discBoundary) = 2 := by
  rw [discDoubleHomeomorph.eulerChar_eq, eulerChar_onePoint, finrank_real_complex]
  norm_num

/-- The Euler characteristic of the doubled disc is twice that of the disc: `2 = 2 · 1`. -/
theorem eulerChar_discDouble_eq_two_mul :
    eulerChar (DoubleAlong discBoundary) = 2 * eulerChar (closedBall (0 : ℂ) 1) := by
  rw [eulerChar_discDouble, eulerChar_closedBall _ zero_le_one, mul_one]

/-! ### The doubled annulus -/

variable {r₁ r₂ : ℝ}

/-- For `0 < r₁ < r₂`, the doubled closed annulus has finite CW type, being homeomorphic to the
torus `Circle × Circle`. -/
theorem finiteCWType_annulusDouble (h₀ : 0 < r₁) (h : r₁ < r₂) :
    FiniteCWType (DoubleAlong (annulusBoundary r₁ r₂)) :=
  (annulusDoubleHomeomorph h₀ h).finiteCWType

/-- **Euler characteristic of the doubled annulus.** For `0 < r₁ < r₂`, the closed annulus
`r₁ ≤ ‖z‖ ≤ r₂` doubled along its two boundary circles is the torus, with Euler characteristic `0`.
The finite CW type of the double is `TauCeti.DoubleAlong.finiteCWType_annulusDouble`. -/
theorem eulerChar_annulusDouble [FiniteCWType (DoubleAlong (annulusBoundary r₁ r₂))]
    (h₀ : 0 < r₁) (h : r₁ < r₂) : eulerChar (DoubleAlong (annulusBoundary r₁ r₂)) = 0 := by
  rw [(annulusDoubleHomeomorph h₀ h).eulerChar_eq, eulerChar_prod, eulerChar_circle, zero_mul]

/-- For `0 < r₁ < r₂`, the Euler characteristic of the doubled closed annulus is twice that of the
annulus: `0 = 2 · 0`. -/
theorem eulerChar_annulusDouble_eq_two_mul [FiniteCWType (DoubleAlong (annulusBoundary r₁ r₂))]
    (h₀ : 0 < r₁) (h : r₁ < r₂) :
    eulerChar (DoubleAlong (annulusBoundary r₁ r₂)) = 2 * eulerChar (closedAnnulus r₁ r₂) := by
  rw [eulerChar_annulusDouble h₀ h, eulerChar_closedAnnulus h₀ h.le, mul_zero]

end DoubleAlong

end TauCeti
