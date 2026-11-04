/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

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

* `TauCeti.contMDiff_exp_smul_coe_sphere`: polar coordinates `(u, t) ↦ exp t • u` are smooth.
* `TauCeti.mvfderiv_smul_coe_sphere_apply`: the differential of `(u, t) ↦ f(t) u` sends `(v, a)`
  at `(u, t)` to `f(t) v + a f'(t) u`.
* `TauCeti.inner_mvfderiv_smul_coe_sphere`: the map `(u, t) ↦ f(t) u` pulls the inner product of
  `V` back to `f(t)² g_(Sⁿ) + f'(t)² dt²`.
* `TauCeti.mvfderiv_exp_smul_coe_sphere_apply`: the differential of polar coordinates sends
  `(v, a)` at `(u, t)` to `e^t (v + a u)`.
* `TauCeti.isInvertible_mfderiv_exp_smul_coe_sphere`: polar coordinates have invertible
  differentials.
* `TauCeti.orientable_sphere_prod_real`, `TauCeti.orientable_circle_prod_real`: the cylinders
  `Sⁿ × ℝ` and `S¹ × ℝ` are orientable.
-/

public section

noncomputable section

open Set TopologicalSpace Manifold Metric Module
open scoped Manifold ContDiff InnerProductSpace

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

/-- Polar coordinates `(u, t) ↦ exp t • u`, read in `V`, are smooth. -/
theorem contMDiff_exp_smul_coe_sphere {m : ℕ∞ω} :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V) m
      (fun p : sphere (0 : V) 1 × ℝ ↦ Real.exp p.2 • (p.1 : V)) :=
  (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul (contMDiff_coe_sphere.comp contMDiff_fst)

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
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (puncturedSpace V) _).1 contMDiff_exp_smul_coe_sphere
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

/-- The differential of the map `(u, t) ↦ f(t) u` from `Sⁿ × ℝ` to `V`: a tangent vector `(v, a)` at
`(u, t)` is sent to `f(t) v + a f'(t) u`, where `v` is read in `V`. -/
theorem mvfderiv_smul_coe_sphere_apply {f : ℝ → ℝ} (p : sphere (0 : V) 1 × ℝ)
    (hf : DifferentiableAt ℝ f p.2) (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ f q.2 • (q.1 : V)) p v =
      f p.2 • mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1
          (Manifold.tangentSpaceProdEquiv p v).1 +
        (deriv f p.2 * NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2) •
          (p.1 : V) := by
  have hι := (contMDiff_coe_sphere (E := V) (n := n) (m := 1) p.1).mdifferentiableAt one_ne_zero
  -- The factors are the compositions `(↑) ∘ Prod.fst` and `f ∘ Prod.snd`, and the components of
  -- `Manifold.tangentSpaceProdEquiv p v` are those of `v` by definition.
  have h₁ : mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ (q.1 : V)) p v =
      mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1 (Manifold.tangentSpaceProdEquiv p v).1 := by
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_fst_apply _ p v
  have h₂ : mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ f q.2) p v =
      deriv f p.2 * NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 := by
    rw [Manifold.tangentSpaceProdEquiv_apply, mul_comm]
    exact mvfderiv_comp_snd_apply_eq_smul_deriv f p v
  have hd₁ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V)
      (fun q : sphere (0 : V) 1 × ℝ ↦ (q.1 : V)) p := hι.comp p mdifferentiableAt_fst
  have hd₂ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun q : sphere (0 : V) 1 × ℝ ↦ f q.2) p :=
    hf.mdifferentiableAt.comp p mdifferentiableAt_snd
  rw [mvfderiv_fun_smul hd₂ hd₁]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, h₁, h₂]

/-- The map `(u, t) ↦ f(t) u` from `Sⁿ × ℝ` to `V` pulls the inner product of `V` back to
`f(t)² g_(Sⁿ) + f'(t)² dt²`: tangent vectors `(v, a)` and `(v', a')` at `(u, t)` are paired to
`f(t)² ⟪v, v'⟫ + f'(t)² a a'`, where `v` and `v'` are read in `V`. -/
theorem inner_mvfderiv_smul_coe_sphere {f : ℝ → ℝ} (p : sphere (0 : V) 1 × ℝ)
    (hf : DifferentiableAt ℝ f p.2) (v v' : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    ⟪mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ f q.2 • (q.1 : V)) p v,
      mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ f q.2 • (q.1 : V)) p v'⟫_ℝ =
      f p.2 ^ 2 * ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1
          (Manifold.tangentSpaceProdEquiv p v).1,
        mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1 (Manifold.tangentSpaceProdEquiv p v').1⟫_ℝ +
        deriv f p.2 ^ 2 * (NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 *
          NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v').2) := by
  have hu : ⟪(p.1 : V), (p.1 : V)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p.1, one_pow]
  have h₁ : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1 (Manifold.tangentSpaceProdEquiv p v).1,
      (p.1 : V)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_coe_mvfderiv_subtypeVal_sphere p.1 _
  have h₂ := inner_coe_mvfderiv_subtypeVal_sphere p.1 (Manifold.tangentSpaceProdEquiv p v').1
  rw [mvfderiv_smul_coe_sphere_apply p hf, mvfderiv_smul_coe_sphere_apply p hf]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right, h₁, h₂,
    hu]
  ring

/-- The differential of polar coordinates `(u, t) ↦ e^t u`, the map underlying
`TauCeti.sphereProdRealDiffeomorph`: a tangent vector `(v, a)` at `(u, t)` is sent to
`e^t (v + a u)`, where `v` is read in `V`. -/
theorem mvfderiv_exp_smul_coe_sphere_apply (p : sphere (0 : V) 1 × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ Real.exp q.2 • (q.1 : V)) p v =
      Real.exp p.2 • (mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1
          (Manifold.tangentSpaceProdEquiv p v).1 +
        NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 • (p.1 : V)) := by
  rw [mvfderiv_smul_coe_sphere_apply p (Real.differentiable_exp p.2), Real.deriv_exp, smul_add,
    smul_smul]

/-- The differential of polar coordinates `(u, t) ↦ e^t u` is invertible. -/
theorem isInvertible_mfderiv_exp_smul_coe_sphere (p : sphere (0 : V) 1 × ℝ) :
    (mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V)
      (fun q : sphere (0 : V) 1 × ℝ ↦ Real.exp q.2 • (q.1 : V)) p).IsInvertible := by
  -- Polar coordinates are the diffeomorphism `sphereProdRealDiffeomorph` onto the punctured space,
  -- followed by its inclusion into `V`, whose differential is the identification
  -- `tangentSpaceOpenEquiv`.
  rw [show (fun q : sphere (0 : V) 1 × ℝ ↦ Real.exp q.2 • (q.1 : V)) =
    Subtype.val ∘ sphereProdRealDiffeomorph (n := n) from rfl]
  exact isInvertible_mfderiv_comp (by rw [Manifold.mfderiv_subtype_val]; exact ⟨_, rfl⟩)
    (sphereProdRealDiffeomorph.isInvertible_mfderiv (by simp))

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
