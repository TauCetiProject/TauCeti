/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Pullback

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# The cylinder over a sphere is the punctured space

Let `V` be a real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`. Polar coordinates
`(u, t) ↦ exp t • u` identify the cylinder `Sⁿ × ℝ` with the punctured space `V ∖ {0}`; the inverse
sends `v` to `(v / ‖v‖, log ‖v‖)`. Both maps are smooth, so this is a diffeomorphism
(`TauCeti.sphereProdRealDiffeomorph`) from the cylinder, modelled on `ℝⁿ × ℝ`, onto the open subset
`V ∖ {0}` of `V`, modelled on `V`. It is the smooth counterpart of Mathlib's
`homeomorphUnitSphereProd`, with the radius read logarithmically.

Pulling back the orientation of `V` along it shows that the cylinder `Sⁿ × ℝ` is orientable,
in particular the cylinder `S¹ × ℝ` over the unit circle of `ℂ`. Mathlib's atlas of the sphere
consists of stereographic charts which are not coherently oriented, so this is not visible from the
charts of the sphere directly.

## Main definitions

* `TauCeti.puncturedSpace V`: the punctured space `V ∖ {0}`, as an open subset of `V`.
* `TauCeti.sphereProdRealDiffeomorph`: polar coordinates, the diffeomorphism
  `Sⁿ × ℝ ≃ V ∖ {0}`, `(u, t) ↦ exp t • u`.

## Main results

* `TauCeti.orientable_sphere_prod_real`, `TauCeti.orientable_circle_prod_real`: the cylinders
  `Sⁿ × ℝ` and `S¹ × ℝ` are orientable.
-/

public section

noncomputable section

open Set TopologicalSpace Manifold Metric Module
open scoped Manifold ContDiff

namespace TauCeti

section Punctured

variable (V : Type*) [TopologicalSpace V] [T1Space V] [Zero V]

/-- The punctured space `V ∖ {0}`, as an open subset of `V`. -/
def puncturedSpace : Opens V :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

variable {V}

@[simp]
theorem mem_puncturedSpace {v : V} : v ∈ puncturedSpace V ↔ v ≠ 0 :=
  Iff.rfl

end Punctured

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- **Polar coordinates** on the punctured space: the diffeomorphism `(u, t) ↦ exp t • u` from the
cylinder `Sⁿ × ℝ` onto `V ∖ {0}`, with inverse `v ↦ (v / ‖v‖, log ‖v‖)`. -/
def sphereProdRealDiffeomorph :
    (sphere (0 : V) 1 × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ), 𝓘(ℝ, V)⟯ puncturedSpace V where
  toFun p := ⟨Real.exp p.2 • (p.1 : V), by
    simp [ne_zero_of_mem_unit_sphere p.1, (Real.exp_pos p.2).ne']⟩
  invFun v := (⟨‖(v : V)‖⁻¹ • (v : V), by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_puncturedSpace.1 v.2))]⟩,
    Real.log ‖(v : V)‖)
  left_inv p := by
    obtain ⟨u, t⟩ := p
    have hu : ‖(u : V)‖ = 1 := norm_eq_of_mem_sphere u
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [norm_smul, hu, smul_smul, (Real.exp_pos t).ne']
    · simp [norm_smul, hu]
  right_inv v := by
    have hv : ‖(v : V)‖ ≠ 0 := norm_ne_zero_iff.2 (mem_puncturedSpace.1 v.2)
    refine Subtype.ext ?_
    simp [Real.exp_log (lt_of_le_of_ne (norm_nonneg _) hv.symm), smul_smul, mul_inv_cancel₀ hv]
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff (puncturedSpace V) _).1 ?_
    exact (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ ?_
    · refine ContMDiff.codRestrict_sphere (f := fun v : puncturedSpace V => ‖(v : V)‖⁻¹ • (v : V))
        (fun v => (contMDiffAt_subtype_iff (f := fun x : V => ‖x‖⁻¹ • x)).2 ?_) _
      have hv : (v : V) ≠ 0 := v.2
      exact (((contDiffAt_norm ℝ hv).inv (norm_ne_zero_iff.2 hv)).smul contDiffAt_id).contMDiffAt
    · refine fun v => (contMDiffAt_subtype_iff (f := fun x : V => Real.log ‖x‖)).2 ?_
      have hv : (v : V) ≠ 0 := v.2
      exact ((contDiffAt_norm ℝ hv).log (norm_ne_zero_iff.2 hv)).contMDiffAt

@[simp]
theorem coe_sphereProdRealDiffeomorph_apply (p : sphere (0 : V) 1 × ℝ) :
    (sphereProdRealDiffeomorph (n := n) p : V) = Real.exp p.2 • (p.1 : V) :=
  (rfl)

@[simp]
theorem coe_sphereProdRealDiffeomorph_symm_apply_fst (v : puncturedSpace V) :
    ((sphereProdRealDiffeomorph (n := n) |>.symm v).1 : V) = ‖(v : V)‖⁻¹ • (v : V) :=
  (rfl)

@[simp]
theorem sphereProdRealDiffeomorph_symm_apply_snd (v : puncturedSpace V) :
    (sphereProdRealDiffeomorph (n := n) |>.symm v).2 = Real.log ‖(v : V)‖ :=
  (rfl)

/-- **The cylinder `Sⁿ × ℝ` is orientable**: pull back the orientation of `V` along polar
coordinates `TauCeti.sphereProdRealDiffeomorph`. -/
instance orientable_sphere_prod_real :
    Orientable ((𝓡 n).prod 𝓘(ℝ)) (sphere (0 : V) 1 × ℝ) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  have hk : finrank ℝ V = finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) := by
    simp [Fact.out (p := finrank ℝ V = n + 1)]
  have hι : Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ))) = finrank ℝ V :=
    (Fintype.card_fin _).trans hk.symm
  -- The constant orientation of `V`, restricted to the punctured space.
  let o : Manifold.Orientation 𝓘(ℝ, V) (puncturedSpace V) _ :=
    (Manifold.Orientation.model (I := 𝓘(ℝ, V)) (finBasisOfFinrankEq ℝ V hk).orientation hι).pullback
      contMDiff_subtype_val (fun x => ⟨_, (Manifold.mfderiv_subtype_val x).symm⟩) hι
  exact ⟨⟨o.pullback (sphereProdRealDiffeomorph.contMDiff.of_le (by simp))
    (fun x => sphereProdRealDiffeomorph.isInvertible_mfderiv (x := x) (by simp))
    (Fintype.card_fin _)⟩⟩

attribute [local instance] finrank_real_complex_fact' in
/-- **The cylinder `S¹ × ℝ` is orientable**, the case of the unit circle of `ℂ`. -/
instance orientable_circle_prod_real : Orientable ((𝓡 1).prod 𝓘(ℝ)) (Circle × ℝ) :=
  inferInstanceAs (Orientable ((𝓡 1).prod 𝓘(ℝ)) (sphere (0 : ℂ) 1 × ℝ))

end TauCeti
