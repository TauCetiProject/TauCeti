/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# Spheres and open subsets of closed balls

On a sphere of nonzero radius in a torsion-free seminormed additive group, a point and its
antipode are distinct. Their complements therefore cover the sphere. This cover is useful for
decomposing spheres into punctured spheres. Two points of a sphere centred at zero that are not
antipodal have nonzero sum (`TauCeti.coe_add_coe_ne_zero`).

An open subset of a closed ball contained in the corresponding open ball embeds openly into the
ambient space.

A map lifting every vector of norm less than `r` to a vector of norm less than `r` lifts each `y`
to a vector of norm less than `‖y‖ + ε` (`TauCeti.exists_apply_eq_norm_lt_add`).

Under an injective map, the image of `v` lies outside the image of the closed ball of radius `r`
centred at zero exactly when `r < ‖v‖`
(`Function.Injective.apply_notMem_image_closedBall_zero_iff`).

A bijection of the closed unit ball preserving the unit sphere restricts to a bijection of the
unit sphere (`Equiv.restrictUnitSphere`).
-/

public section

open Metric Set Topology

namespace TauCeti

/-- The complements of two antipodal points cover any sphere of nonzero radius in a torsion-free
seminormed additive group. -/
lemma compl_singleton_union_compl_singleton_neg {E : Type*} [SeminormedAddCommGroup E]
    [IsAddTorsionFree E] {r : ℝ} (hr : r ≠ 0) (p : sphere (0 : E) r) :
    ({p}ᶜ ∪ {-p}ᶜ : Set (sphere (0 : E) r)) = Set.univ := by
  rw [← Set.compl_inter, Set.singleton_inter_of_notMem]
  · exact Set.compl_empty
  · intro h
    apply ne_zero_of_mem_sphere hr p
    apply self_eq_neg.mp
    simpa only [coe_neg_sphere] using congrArg Subtype.val h

/-- Two points of a sphere centred at zero that are not antipodal have nonzero sum. -/
theorem coe_add_coe_ne_zero {E : Type*} [SeminormedAddCommGroup E] {r : ℝ}
    {b y : sphere (0 : E) r} (h : y ≠ -b) : (b : E) + (y : E) ≠ 0 := fun h0 ↦
  h (Subtype.ext (by rw [coe_neg_sphere]; exact eq_neg_of_add_eq_zero_right h0))

/-- An open subset of a closed ball centered at zero whose points have norm strictly less than
the radius embeds openly into the ambient space. -/
theorem _root_.IsOpen.isOpenEmbedding_coe_openSubset_closedBall
    {E : Type*} [SeminormedAddCommGroup E]
    {r : ℝ} {U : Set (closedBall (0 : E) r)} (hU : IsOpen U)
    (h : ∀ z ∈ U, ‖(z : E)‖ < r) :
    IsOpenEmbedding fun z : U => ((z : closedBall (0 : E) r) : E) := by
  refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hU
  have hrange : range (fun z : (Subtype.val ⁻¹' O : Set (closedBall (0 : E) r)) =>
      ((z : closedBall (0 : E) r) : E)) = O ∩ ball 0 r := by
    ext v
    refine ⟨?_, fun hv => ⟨⟨⟨v, ball_subset_closedBall hv.2⟩, hv.1⟩, rfl⟩⟩
    rintro ⟨z, rfl⟩
    exact ⟨z.2, mem_ball_zero_iff.2 (h z z.2)⟩
  rw [hrange]
  exact hO.inter isOpen_ball

/-- If `f` lifts every vector of norm less than `r` to a vector of norm less than `r`, then every
`y` is `f x` for some `x` with `‖x‖ < ‖y‖ + ε`, for each `ε > 0`. -/
theorem exists_apply_eq_norm_lt_add {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {f : E → F} (hf : ∀ r, ball (0 : F) r ⊆ f '' ball 0 r) (y : F)
    {ε : ℝ} (hε : 0 < ε) : ∃ x, f x = y ∧ ‖x‖ < ‖y‖ + ε := by
  obtain ⟨x, hx, rfl⟩ := hf _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖y‖ hε))
  exact ⟨x, rfl, mem_ball_zero_iff.1 hx⟩

/-- Under an injective map `e`, the image of `v` lies outside the image of the closed ball of
radius `r` centred at zero exactly when `r < ‖v‖`. -/
theorem _root_.Function.Injective.apply_notMem_image_closedBall_zero_iff {E X : Type*}
    [SeminormedAddGroup E] {e : E → X} (he : Function.Injective e) {r : ℝ} {v : E} :
    e v ∉ e '' closedBall 0 r ↔ r < ‖v‖ := by
  rw [he.mem_set_image, mem_closedBall_zero_iff, not_le]

/-! ### Bijections of the closed ball preserving the unit sphere -/

section RestrictUnitSphere

variable {V : Type*} [SeminormedAddCommGroup V] (D : closedBall (0 : V) 1 ≃ closedBall (0 : V) 1)
  (hD : ∀ x, ‖(D x : V)‖ = 1 ↔ ‖(x : V)‖ = 1)
include hD

/-- If a bijection of the closed unit ball preserves the unit sphere, so does its inverse. -/
theorem _root_.Equiv.norm_symm_apply_eq_one_iff (x : closedBall (0 : V) 1) :
    ‖(D.symm x : V)‖ = 1 ↔ ‖(x : V)‖ = 1 := by
  rw [← hD, D.apply_symm_apply]

/-- A bijection of the closed unit ball which preserves the unit sphere restricts to a bijection of
the unit sphere. -/
def _root_.Equiv.restrictUnitSphere : sphere (0 : V) 1 ≃ sphere (0 : V) 1 where
  toFun z := ⟨D (inclusion sphere_subset_closedBall z),
    mem_sphere_zero_iff_norm.2 ((hD _).2 (norm_eq_of_mem_sphere z))⟩
  invFun z := ⟨D.symm (inclusion sphere_subset_closedBall z),
    mem_sphere_zero_iff_norm.2 ((D.norm_symm_apply_eq_one_iff hD _).2 (norm_eq_of_mem_sphere z))⟩
  left_inv z := Subtype.ext <| by simp
  right_inv z := Subtype.ext <| by simp

@[simp]
theorem _root_.Equiv.coe_restrictUnitSphere_apply (z : sphere (0 : V) 1) :
    (D.restrictUnitSphere hD z : V) = D (inclusion sphere_subset_closedBall z) :=
  (rfl)

@[simp]
theorem _root_.Equiv.coe_restrictUnitSphere_symm_apply (z : sphere (0 : V) 1) :
    ((D.restrictUnitSphere hD).symm z : V) = D.symm (inclusion sphere_subset_closedBall z) :=
  (rfl)

/-- The inverse of `D` on the unit sphere, read in the closed unit ball. -/
theorem _root_.Equiv.inclusion_restrictUnitSphere_symm_apply (z : sphere (0 : V) 1) :
    inclusion sphere_subset_closedBall ((D.restrictUnitSphere hD).symm z) =
      D.symm (inclusion sphere_subset_closedBall z) :=
  Subtype.ext (D.coe_restrictUnitSphere_symm_apply hD z)

/-- If `D` is `σ` on the unit sphere, then `σ` undoes the restriction of the inverse of `D`. -/
theorem _root_.Equiv.apply_restrictUnitSphere_symm {σ : sphere (0 : V) 1 → sphere (0 : V) 1}
    (hσ : ∀ z, D (inclusion sphere_subset_closedBall z) = inclusion sphere_subset_closedBall (σ z))
    (z : sphere (0 : V) 1) :
    σ ((D.restrictUnitSphere hD).symm z) = z := by
  have h := hσ ((D.restrictUnitSphere hD).symm z)
  rw [D.inclusion_restrictUnitSphere_symm_apply hD, D.apply_symm_apply] at h
  exact Subtype.ext (congrArg Subtype.val h).symm

end RestrictUnitSphere

end TauCeti
