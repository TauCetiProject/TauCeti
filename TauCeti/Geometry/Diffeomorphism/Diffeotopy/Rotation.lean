/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Rotation diffeotopies of a unit sphere

A smooth path `R` of linear isometries of a finite-dimensional real inner product space `E`,
starting at the identity, moves the unit sphere of `E` through diffeomorphisms:
`TauCeti.unitSphereDiffeotopy R` is the diffeotopy of the sphere which at time `t` applies `R t`.
Its inverse at time `t` is `(R t)⁻¹`, which depends smoothly on `t` as well
(`ContDiff.linearIsometryEquiv_symm_apply`). The construction follows the boost diffeotopy
`TauCeti.sphereBoostDiffeotopy`, with the boosts replaced by the linear isometries `R t`.

A linear isometry `e` acts on a point `x` of the sphere and on a vector `v` tangent to the sphere at
`x` by `(x, v) ↦ (e x, e v)`. Composing the plane rotations of
`TauCeti.exists_contDiff_path_apply_eq`, the rotations reached by diffeotopies of a sphere of
dimension at least two act transitively on the pairs `(x, v)` with `x` and `v` orthonormal
(`TauCeti.exists_diffeotopy_final_apply_eq_and_apply_eq`). So the diffeotopies of such a sphere
can move a point and a unit tangent vector there to any other point and unit tangent vector, as
needed to match the first-order data of two curves in the sphere. On the circle this fails: a
rotation of the circle cannot reverse the direction of a tangent vector.

## Main definitions

* `TauCeti.unitSphereDiffeotopy R hR hR₀`: the diffeotopy of the unit sphere applying the linear
  isometry `R t` at time `t`.

## Main results

* `TauCeti.coe_unitSphereDiffeotopy_apply`, `TauCeti.coe_unitSphereDiffeotopy_final_apply`: the
  rotation diffeotopy at time `t` is `R t`, and it ends at `R 1`.
* `TauCeti.exists_diffeotopy_final_apply_eq_and_apply_eq`: in a sphere of dimension at least two,
  any orthonormal pair `(x, v)` is carried to any other orthonormal pair `(y, w)` by a linear
  isometry which is the final map of a diffeotopy of the sphere.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for diffeotopies.
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff RealInnerProductSpace unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {m : ℕ∞ω}

/-- The **rotation diffeotopy** of the unit sphere along a smooth path `R` of linear isometries
starting at the identity: at time `t` it applies `R t`. -/
def unitSphereDiffeotopy (R : ℝ → E ≃ₗᵢ[ℝ] E) (hR : ContDiff ℝ m fun p : ℝ × E => R p.1 p.2)
    (hR₀ : ∀ x, R 0 x = x) : Diffeotopy (𝓡 n) m (sphere (0 : E) 1) where
  toDiffeomorph :=
    { toFun := fun p => (p.1, (R p.1).unitSphereEquiv p.2)
      invFun := fun p => (p.1, (R p.1).symm.unitSphereEquiv p.2)
      left_inv := fun p => Prod.ext rfl (Subtype.ext (by simp))
      right_inv := fun p => Prod.ext rfl (Subtype.ext (by simp))
      contMDiff_toFun := contMDiff_fst.prodMk
        (contMDiff_unitSphereEquiv_apply hR (contMDiff_subtypeVal_Icc.comp contMDiff_fst)
          contMDiff_snd)
      contMDiff_invFun :=
        have := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
        contMDiff_fst.prodMk
          (contMDiff_unitSphereEquiv_apply (R := fun t => (R t).symm)
            hR.linearIsometryEquiv_symm_apply (contMDiff_subtypeVal_Icc.comp contMDiff_fst)
            contMDiff_snd) }
  fst_apply _ := rfl
  snd_apply_zero' x := Subtype.ext (by
    -- The total map is a structure literal, which `simp` does not unfold; `change` exposes its
    -- value at time `0`.
    change ((R ((0 : I) : ℝ)).unitSphereEquiv x : E) = x
    rw [LinearIsometryEquiv.coe_unitSphereEquiv_apply, Set.Icc.coe_zero, hR₀])

variable (R : ℝ → E ≃ₗᵢ[ℝ] E) (hR : ContDiff ℝ m fun p : ℝ × E => R p.1 p.2)
  (hR₀ : ∀ x, R 0 x = x)

/-- At time `t` the rotation diffeotopy applies `R t`. -/
@[simp]
theorem coe_unitSphereDiffeotopy_apply (p : I × sphere (0 : E) 1) :
    (unitSphereDiffeotopy (n := n) R hR hR₀ p : E) = R p.1 p.2 :=
  LinearIsometryEquiv.coe_unitSphereEquiv_apply (R p.1) p.2

/-- The rotation diffeotopy ends at `R 1`. -/
theorem coe_unitSphereDiffeotopy_final_apply (x : sphere (0 : E) 1) :
    ((unitSphereDiffeotopy (n := n) R hR hR₀).final x : E) = R 1 x := by
  rw [Diffeotopy.final_apply, coe_unitSphereDiffeotopy_apply, Set.Icc.coe_one]

/-! ### Transitivity on orthonormal pairs -/

/-- The linear isometry `e` restricts on the unit sphere to the final map of a diffeotopy. -/
private def IsFinalRotation (n : ℕ) [Fact (finrank ℝ E = n + 1)] (m : ℕ∞ω) (e : E ≃ₗᵢ[ℝ] E) :
    Prop :=
  ∃ Φ : Diffeotopy (𝓡 n) m (sphere (0 : E) 1), ∀ z, (Φ.final z : E) = e z

private theorem IsFinalRotation.trans {e₁ e₂ : E ≃ₗᵢ[ℝ] E} (h₁ : IsFinalRotation n m e₁)
    (h₂ : IsFinalRotation n m e₂) : IsFinalRotation n m (e₁.trans e₂) := by
  obtain ⟨Φ, hΦ⟩ := h₁
  obtain ⟨Ψ, hΨ⟩ := h₂
  refine ⟨Φ.trans Ψ, fun z => ?_⟩
  rw [Diffeotopy.final_trans, _root_.Diffeomorph.coe_trans, Function.comp_apply, hΨ, hΦ,
    LinearIsometryEquiv.trans_apply]

/-- A plane rotation sending the unit vector `a` to the unit vector `b ≠ -a` and fixing every
vector orthogonal to both is the final map of a rotation diffeotopy. -/
private theorem exists_isFinalRotation_apply_eq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a ≠ -b) :
    ∃ e : E ≃ₗᵢ[ℝ] E, IsFinalRotation n m e ∧ e a = b ∧
      ∀ x, ⟪a, x⟫ = 0 → ⟪b, x⟫ = 0 → e x = x := by
  obtain ⟨R, hR, hR₀, h₁, h₂⟩ := exists_contDiff_path_apply_eq ha hb hab
  exact ⟨R 1, ⟨unitSphereDiffeotopy R (hR.of_le le_top) hR₀,
    coe_unitSphereDiffeotopy_final_apply R _ hR₀⟩, h₁, h₂⟩

/-- **Diffeotopies of a sphere act transitively on orthonormal pairs.** In a unit sphere of
dimension at least two, for orthonormal pairs `(x, v)` and `(y, w)` there is a diffeotopy of the
sphere whose final map is the restriction of a linear isometry `e` with `e x = y` and `e v = w`. -/
theorem exists_diffeotopy_final_apply_eq_and_apply_eq (hn : 2 ≤ n) {x v y w : E}
    (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) (hxv : ⟪x, v⟫ = 0) (hy : ‖y‖ = 1) (hw : ‖w‖ = 1)
    (hyw : ⟪y, w⟫ = 0) :
    ∃ (Φ : Diffeotopy (𝓡 n) m (sphere (0 : E) 1)) (e : E ≃ₗᵢ[ℝ] E),
      (∀ z, (Φ.final z : E) = e z) ∧ e x = y ∧ e v = w := by
  classical
  -- In dimension at least three, any two vectors have a common orthogonal unit vector.
  have hperp (a b : E) : ∃ q : E, ‖q‖ = 1 ∧ ⟪a, q⟫ = 0 ∧ ⟪b, q⟫ = 0 := by
    obtain ⟨q, hq, h⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
      {a, b} (Finset.card_le_two.trans_lt (by rw [(Fact.out : finrank ℝ E = n + 1)]; omega))
    exact ⟨q, hq, h a (by simp), h b (by simp)⟩
  have hne {u : E} (hu : ‖u‖ = 1) : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  -- First rotate `x` to `y` through a unit vector `q` orthogonal to both.
  obtain ⟨q, hq, hxq, hyq⟩ := hperp x y
  obtain ⟨e₁, he₁, he₁x, -⟩ :=
    exists_isFinalRotation_apply_eq (n := n) (m := m) hx hq (ne_neg_of_inner_eq_zero (hne hq) hxq)
  obtain ⟨e₂, he₂, he₂q, -⟩ := exists_isFinalRotation_apply_eq (n := n) (m := m) hq hy
    (ne_neg_of_inner_eq_zero (hne hy) (by rwa [real_inner_comm]))
  set f := e₁.trans e₂
  have hfx : f x = y := by simp [f, he₁x, he₂q]
  -- Then rotate `f v`, a unit vector orthogonal to `y`, to `w` while fixing `y`.
  set v₁ := f v
  have hv₁ : ‖v₁‖ = 1 := by simp [v₁, hv]
  have hyv₁ : ⟪y, v₁⟫ = 0 := by rw [← hfx, LinearIsometryEquiv.inner_map_map, hxv]
  suffices ∃ g : E ≃ₗᵢ[ℝ] E, IsFinalRotation n m g ∧ g y = y ∧ g v₁ = w by
    obtain ⟨g, hg, hgy, hgv⟩ := this
    obtain ⟨Φ, hΦ⟩ := (he₁.trans he₂).trans hg
    exact ⟨Φ, f.trans g, hΦ, by simp [hfx, hgy], hgv⟩
  by_cases h : v₁ = -w
  · -- Rotating `v₁` to `w = -v₁` directly is impossible; go through a unit vector `q'`
    -- orthogonal to `y` and `w`.
    obtain ⟨q', hq', hyq', hwq'⟩ := hperp y w
    have hv₁q' : ⟪v₁, q'⟫ = 0 := by rw [h, inner_neg_left, hwq', neg_zero]
    obtain ⟨g₁, hg₁, hg₁v, hg₁y⟩ := exists_isFinalRotation_apply_eq (n := n) (m := m) hv₁ hq'
      (ne_neg_of_inner_eq_zero (hne hq') hv₁q')
    obtain ⟨g₂, hg₂, hg₂q, hg₂y⟩ := exists_isFinalRotation_apply_eq (n := n) (m := m) hq' hw
      (ne_neg_of_inner_eq_zero (hne hw) (by rwa [real_inner_comm]))
    refine ⟨g₁.trans g₂, hg₁.trans hg₂, ?_, by simp [hg₁v, hg₂q]⟩
    rw [LinearIsometryEquiv.trans_apply, hg₁y y (by rwa [real_inner_comm])
      (by rwa [real_inner_comm]), hg₂y y (by rwa [real_inner_comm]) (by rwa [real_inner_comm])]
  · obtain ⟨g, hg, hgv, hgy⟩ := exists_isFinalRotation_apply_eq (n := n) (m := m) hv₁ hw h
    exact ⟨g, hg, hgy y (by rwa [real_inner_comm]) (by rwa [real_inner_comm]), hgv⟩

end TauCeti
