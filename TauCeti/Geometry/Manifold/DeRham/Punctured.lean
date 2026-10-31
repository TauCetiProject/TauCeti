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
# The de Rham cohomology of a punctured space

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

## Main declarations

* `TauCeti.deRhamCohomology.puncturedSpaceEquivSphere`: restriction to the unit sphere is a
  linear equivalence from the de Rham cohomology of `E \ {0}` to that of the unit sphere, with
  inverse pullback along the radial projection `NormedSpace.normalize`.

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

end deRhamCohomology

end TauCeti
