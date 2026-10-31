/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
public import TauCeti.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The de Rham cohomology of a punctured space and of the complement of a ball

Let `E` be a real inner product space of dimension `n + 1`. The punctured space `E \ {0}`, an
open subset of `E`, deformation retracts onto the unit sphere `Sⁿ` of `E`: the inclusion
`ι : Sⁿ → E \ {0}` and the radial projection `x ↦ x / ‖x‖` compose to the identity of the sphere
in one order, and in the other order to a map joined to the identity of `E \ {0}` by the smooth
straight-line homotopy `(x, t) ↦ ((1 - t) / ‖x‖ + t) • x`. Homotopy invariance therefore makes
restriction to the sphere a linear equivalence
`H^k_dR(E \ {0}) ≃ H^k_dR(Sⁿ)` in every degree
(`TauCeti.deRhamCohomology.puncturedSpaceEquivSphere`).

This is the input the Mayer–Vietoris computation of the cohomology of spheres needs: for the
cover of `Sⁿ⁺¹` by the complements of the two poles, stereographic projection identifies the
intersection with the punctured space `ℝⁿ⁺¹ \ {0}`, whose cohomology is that of `Sⁿ`.

More generally, for `r ≥ 0` the complement `E \ closedBall 0 r` of a closed ball deformation
retracts onto the sphere of radius `r + 1`, so `H^k_dR(E \ closedBall 0 r) ≃ H^k_dR(Sⁿ)` as well
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere`). This is the region near infinity on which
the primitive of a compactly supported closed form on `E` is examined.

## Main declarations

* `TauCeti.deRhamCohomology.puncturedSpaceEquivSphere`: restriction to the unit sphere is a
  linear equivalence from the de Rham cohomology of `E \ {0}` to that of the unit sphere, with
  inverse pullback along the radial projection `NormedSpace.normalize`.
* `TauCeti.deRhamCohomology.closedBallComplEquivSphere`: pullback along the scaling
  `x ↦ (r + 1) • x` of the unit sphere is a linear equivalence from the de Rham cohomology of
  `E \ closedBall 0 r` to that of the unit sphere.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, Theorem 17.21 (the
  cohomology of spheres).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set TopologicalSpace Metric Module
open scoped ContDiff Manifold

namespace TauCeti

namespace deRhamCohomology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The straight-line homotopy `(x, t) ↦ (1 - t) • (x / ‖x‖) + t • x` in `E \ {0}` from the
radial projection onto the unit sphere to the identity. It equals
`((1 - t) / ‖x‖ + t) • x`, whose scalar factor is positive. -/
private def puncturedHomotopy
    (p : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) × Icc (0 : ℝ) 1) :
    (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) :=
  ⟨(1 - (p.2 : ℝ)) • NormedSpace.normalize (p.1 : E) + (p.2 : ℝ) • (p.1 : E), by
    have h₁ : 0 < ‖(p.1 : E)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 p.1.2)
    have : 0 < (1 - (p.2 : ℝ)) * ‖(p.1 : E)‖⁻¹ + p.2 := by
      rcases eq_or_lt_of_le p.2.2.1 with h | h
      · simpa [← h] using h₁
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 p.2.2.2) h₁.le) h
    rw [NormedSpace.normalize, smul_smul, ← add_smul]
    exact smul_ne_zero this.ne' p.1.2⟩

private theorem contMDiff_puncturedHomotopy :
    ContMDiff (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ (puncturedHomotopy (E := E)) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  have ht : ContMDiff (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      (fun p : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) × Icc (0 : ℝ) 1 ↦ (p.2 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_snd
  exact ((contMDiff_const.sub ht).smul (contMDiff_normalize_compl_zero.comp contMDiff_fst)).add
    (ht.smul (contMDiff_subtype_val.comp contMDiff_fst))

variable (E n) in
/-- **The de Rham cohomology of a punctured space is that of the sphere.** For a real inner
product space `E` of dimension `n + 1`, restriction to the unit sphere `Sⁿ` is a linear
equivalence `H^k_dR(E \ {0}) ≃ H^k_dR(Sⁿ)` in every degree `k`; its inverse is pullback along the
radial projection `x ↦ x / ‖x‖` (`TauCeti.deRhamCohomology.puncturedSpaceEquivSphere_symm_apply`).
-/
def puncturedSpaceEquivSphere (k : ℕ) :
    deRhamCohomology 𝓘(ℝ, E) (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) k ≃ₗ[ℝ]
      deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k :=
  equivOfHomotopy contMDiff_coe_sphere_compl_zero contMDiff_normalize_sphere contMDiff_fst
    (fun x ↦ Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (by simp)).symm)
    (fun _ ↦ rfl)
    contMDiff_puncturedHomotopy (fun _ ↦ Subtype.ext (by simp [puncturedHomotopy]))
    (fun _ ↦ Subtype.ext (by simp [puncturedHomotopy])) k

/-- The equivalence `TauCeti.deRhamCohomology.puncturedSpaceEquivSphere` is restriction to the unit
sphere, that is, pullback along its inclusion into `E \ {0}`. -/
@[simp]
theorem puncturedSpaceEquivSphere_apply (k : ℕ)
    (c : deRhamCohomology 𝓘(ℝ, E) (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) k) :
    puncturedSpaceEquivSphere E n k c =
      map (fun x : sphere (0 : E) 1 ↦
          (⟨x, ne_zero_of_mem_unit_sphere x⟩ : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E)))
        contMDiff_coe_sphere_compl_zero k c :=
  equivOfHomotopy_apply ..

/-- The inverse of `TauCeti.deRhamCohomology.puncturedSpaceEquivSphere` is pullback along the
radial projection `x ↦ x / ‖x‖` of `E \ {0}` onto the unit sphere. -/
@[simp]
theorem puncturedSpaceEquivSphere_symm_apply (k : ℕ)
    (c : deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k) :
    (puncturedSpaceEquivSphere E n k).symm c =
      map (fun x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) ↦
          (⟨NormedSpace.normalize (x : E),
            mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize_eq_one_iff.2 x.2)⟩ :
              sphere (0 : E) 1))
        contMDiff_normalize_sphere k c :=
  equivOfHomotopy_symm_apply ..

/-! ### The complement of a closed ball

For `r ≥ 0`, the complement `E \ closedBall 0 r` of the closed ball of radius `r` also deformation
retracts onto a sphere, through the radial projection onto the sphere of radius `r + 1`: the
straight-line homotopy `(x, t) ↦ ((1 - t) (r + 1)) • (x / ‖x‖) + t • x` has norm
`(1 - t) (r + 1) + t ‖x‖ > r`. -/

section ClosedBallCompl

variable {r : ℝ}

omit [Fact (finrank ℝ E = n + 1)] in
/-- A point of the segment from `(r + 1) • (x / ‖x‖)` to `x` stays outside the closed ball of
radius `r`, when `x` does. -/
private theorem homotopy_mem_compl_closedBall {x : E} (hx : r < ‖x‖) (hr : 0 ≤ r) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ((1 - t) * (r + 1)) • NormedSpace.normalize x + t • x ∈ (closedBall (0 : E) r)ᶜ := by
  have hx0 : ‖x‖ ≠ 0 := (hr.trans_lt hx).ne'
  have hc : 0 ≤ (1 - t) * (r + 1) * ‖x‖⁻¹ + t :=
    add_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ht₁) (by linarith)) (by positivity)) ht₀
  -- The point is the nonnegative multiple `((1 - t) (r + 1) / ‖x‖ + t) • x` of `x`.
  rw [NormedSpace.normalize, smul_smul, ← add_smul, mem_compl_iff, mem_closedBall_zero_iff,
    not_le, norm_smul, Real.norm_of_nonneg hc, add_mul, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  rcases ht₁.lt_or_eq with ht₁ | rfl
  · nlinarith [mul_nonneg ht₀ (sub_nonneg.2 hx.le)]
  · linarith

/-- The straight-line homotopy `(x, t) ↦ ((1 - t) (r + 1)) • (x / ‖x‖) + t • x` in
`E \ closedBall 0 r` from the radial projection onto the sphere of radius `r + 1` to the
identity. -/
private def closedBallComplHomotopy (hr : 0 ≤ r)
    (p : (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) ×
      Icc (0 : ℝ) 1) :
    (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) :=
  ⟨((1 - (p.2 : ℝ)) * (r + 1)) • NormedSpace.normalize (p.1 : E) + (p.2 : ℝ) • (p.1 : E),
    homotopy_mem_compl_closedBall (not_le.1 fun h ↦ p.1.2 (mem_closedBall_zero_iff.2 h)) hr
      p.2.2.1 p.2.2.2⟩

private theorem contMDiff_closedBallComplHomotopy (hr : 0 ≤ r) :
    ContMDiff (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ (closedBallComplHomotopy (E := E) hr) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  have ht : ContMDiff (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      (fun p : (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) ×
        Icc (0 : ℝ) 1 ↦ (p.2 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_snd
  have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun x : (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) ↦
        NormedSpace.normalize (x : E)) :=
    contMDiff_normalize_compl_zero.comp
      (contMDiff_inclusion (compl_subset_compl.2 (singleton_subset_iff.2 (mem_closedBall_self hr))))
  exact (((contMDiff_const.sub ht).mul contMDiff_const).smul (hn.comp contMDiff_fst)).add
    (ht.smul (contMDiff_subtype_val.comp contMDiff_fst))

variable (E n) in
/-- **The de Rham cohomology of the complement of a closed ball is that of the sphere.** For a
real inner product space `E` of dimension `n + 1` and `r ≥ 0`, pullback along the scaling
`x ↦ (r + 1) • x` of the unit sphere `Sⁿ` into `E \ closedBall 0 r` is a linear equivalence
`H^k_dR(E \ closedBall 0 r) ≃ H^k_dR(Sⁿ)` in every degree `k`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere_apply`); its inverse is pullback along the
radial projection `x ↦ x / ‖x‖`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere_symm_apply`). -/
def closedBallComplEquivSphere (hr : 0 ≤ r) (k : ℕ) :
    deRhamCohomology 𝓘(ℝ, E)
        (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) k ≃ₗ[ℝ]
      deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k :=
  equivOfHomotopy
    (f := fun x : sphere (0 : E) 1 ↦
      (⟨(r + 1) • (x : E), by simp [norm_smul, abs_of_nonneg (by linarith : 0 ≤ r + 1)]⟩ :
        (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E)))
    (by
      rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
      exact (contMDiff_const (I' := 𝓘(ℝ)) (c := r + 1)).smul contMDiff_coe_sphere)
    (contMDiff_normalize_sphere.comp <| contMDiff_inclusion <|
      compl_subset_compl.2 <| singleton_subset_iff.2 <| mem_closedBall_self hr)
    contMDiff_fst
    (fun x ↦ Subtype.ext <| by
      simp [NormedSpace.normalize_smul_of_pos (by linarith : (0 : ℝ) < r + 1),
        NormedSpace.normalize_eq_self_of_norm_eq_one])
    (fun _ ↦ rfl)
    (contMDiff_closedBallComplHomotopy hr) (fun _ ↦ Subtype.ext (by simp [closedBallComplHomotopy]))
    (fun _ ↦ Subtype.ext (by simp [closedBallComplHomotopy])) k

/-- The equivalence `TauCeti.deRhamCohomology.closedBallComplEquivSphere` is pullback along the
scaling `x ↦ (r + 1) • x` of the unit sphere into the complement of the closed ball. -/
@[simp]
theorem closedBallComplEquivSphere_apply (hr : 0 ≤ r) (k : ℕ)
    (c : deRhamCohomology 𝓘(ℝ, E)
      (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) k) :
    closedBallComplEquivSphere E n hr k c =
      map (fun x : sphere (0 : E) 1 ↦
          (⟨(r + 1) • (x : E), by simp [norm_smul, abs_of_nonneg (by linarith : 0 ≤ r + 1)]⟩ :
            (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E)))
        (by
          rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
          exact (contMDiff_const (I' := 𝓘(ℝ)) (c := r + 1)).smul contMDiff_coe_sphere)
        k c :=
  equivOfHomotopy_apply ..

/-- The inverse of `TauCeti.deRhamCohomology.closedBallComplEquivSphere` is pullback along the
radial projection `x ↦ x / ‖x‖` of the complement of the closed ball onto the unit sphere. -/
@[simp]
theorem closedBallComplEquivSphere_symm_apply (hr : 0 ≤ r) (k : ℕ)
    (c : deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k) :
    (closedBallComplEquivSphere E n hr k).symm c =
      map (fun x : (⟨(closedBall (0 : E) r)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) ↦
          (⟨NormedSpace.normalize (x : E), mem_sphere_zero_iff_norm.2
            (NormedSpace.norm_normalize_eq_one_iff.2 fun h0 ↦ x.2 (by simp [h0, hr]))⟩ :
            sphere (0 : E) 1))
        (contMDiff_normalize_sphere.comp <| contMDiff_inclusion <|
          compl_subset_compl.2 <| singleton_subset_iff.2 <| mem_closedBall_self hr) k c :=
  equivOfHomotopy_symm_apply ..

end ClosedBallCompl

end deRhamCohomology

end TauCeti
