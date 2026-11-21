/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# The Legendre map and the energy in bundle charts

Let `L : TM → 𝕜` be a Lagrangian on a manifold `M`. Fix a point `z₀` of `TM` and read `TM` in the
preferred chart at `z₀`, with coordinates `p = (q, v)`; write `ℓ(q, v) = L(φ⁻¹(q, v))` for the
Lagrangian in these coordinates, where `φ = extChartAt I.tangent z₀`. Its partial derivative in
the velocity, the *momentum* `P(q, v) = ∂_v ℓ(q, v)`, is a covector on the model space.

This file proves that in the preferred chart of `T*M` at `FL(z₀)` the Legendre map is
`(q, v) ↦ (q, ∂_v ℓ(q, v))` (`TauCeti.extChartAt_legendreMap_extChartAt_symm`), and the energy is
`E_L = ∂_v ℓ(q, v)(v) - ℓ(q, v)` (`TauCeti.lagrangianEnergy_extChartAt_symm`), on the whole chart
target. On a boundaryless manifold and for a `C²` Lagrangian, the differentials at `z₀` follow:

* `dFL_(z₀) = (fst, DP)`, where `DP` is the derivative of the momentum at the chart image `p₀` of
  `z₀` (`TauCeti.hasMFDerivAt_legendreMap`);
* `dE_L(Y) = DP(Y)(v₀) - ∂_q ℓ(p₀)(Y.1)` for `p₀ = (q₀, v₀)`
  (`TauCeti.mvfderiv_lagrangianEnergy_apply`): the derivative of `ℓ` along the velocity cancels
  against that of `P(q, v)(v)`.

These are the coordinate expressions through which the Lagrangian vector field of
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.LagrangianVectorField` is compared with the
Euler–Lagrange equations `d/dt ∂_v ℓ = ∂_q ℓ` in charts.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5 (the Legendre transformation and the energy in local coordinates).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- The fibre derivative of `L` at a point of the chart at `z₀`, read in the trivialization at
`z₀.proj`, is the velocity derivative of the coordinate expression of `L`. -/
private theorem fderiv_comp_symmL_eq_fderiv_extChartAt_symm (L : TangentBundle I M → 𝕜)
    (z₀ : TangentBundle I M) {p : E × E} (hp : p ∈ (extChartAt I.tangent z₀).target) :
    fderiv 𝕜 (fun u : E ↦ L (TotalSpace.mk' E ((extChartAt I.tangent z₀).symm p).proj u))
        ((extChartAt I.tangent z₀).symm p).2 ∘L
      (trivializationAt E (TangentSpace I) z₀.proj).symmL 𝕜
        ((extChartAt I.tangent z₀).symm p).proj =
      fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2 := by
  set w := (extChartAt I.tangent z₀).symm p
  have hwp : (extChartAt I z₀.proj).symm p.1 = w.proj := (proj_extChartAt_symm z₀ hp).symm
  have hb := proj_extChartAt_symm_mem_baseSet z₀ hp
  have h := legendreMap_snd_comp_symmL L hb
  rw [legendreMap_snd] at h
  refine h.trans ?_
  rw [← trivializationAt_extChartAt_symm_snd z₀ hp]
  congr 1
  funext u
  rw [extChartAt_symm_apply_of_mem_baseSet z₀ (hwp ▸ hb) u, hwp, Trivialization.symmL_apply _ hb]

/-- **The Legendre map in bundle charts.** In the preferred charts at `z₀` and at `FL(z₀)`, the
Legendre map is `(q, v) ↦ (q, ∂_v ℓ(q, v))`, where `ℓ` is `L` read in the chart at `z₀`. -/
theorem extChartAt_legendreMap_extChartAt_symm (L : TangentBundle I M → 𝕜) (z₀ : TangentBundle I M)
    {p : E × E} (hp : p ∈ (extChartAt I.tangent z₀).target) :
    extChartAt (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L z₀)
        (legendreMap L ((extChartAt I.tangent z₀).symm p)) =
      (p.1, fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2) := by
  set w := (extChartAt I.tangent z₀).symm p
  rw [CotangentBundle.extChartAt_apply, legendreMap_def L w, legendreMap_def L z₀]
  exact Prod.ext (extChartAt_proj_extChartAt_symm z₀ hp)
    (fderiv_comp_symmL_eq_fderiv_extChartAt_symm L z₀ hp)

/-- **The energy in bundle charts.** In the preferred chart at `z₀`, the energy of `L` is
`∂_v ℓ(q, v)(v) - ℓ(q, v)`, where `ℓ` is `L` read in that chart. -/
theorem lagrangianEnergy_extChartAt_symm (L : TangentBundle I M → 𝕜) (z₀ : TangentBundle I M)
    {p : E × E} (hp : p ∈ (extChartAt I.tangent z₀).target) :
    lagrangianEnergy L ((extChartAt I.tangent z₀).symm p) =
      fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2 p.2 -
        L ((extChartAt I.tangent z₀).symm p) := by
  set e := trivializationAt E (TangentSpace I) z₀.proj
  set w := (extChartAt I.tangent z₀).symm p
  have hb := proj_extChartAt_symm_mem_baseSet z₀ hp
  have hv : e.symmL 𝕜 w.proj p.2 = w.2 := by
    rw [← trivializationAt_extChartAt_symm_snd z₀ hp, Trivialization.symmL_apply _ hb,
      e.symm_proj_apply w hb]
  have h : fderiv 𝕜 (fun u : E ↦ L (TotalSpace.mk' E w.proj u)) w.2 w.2 =
      fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2 p.2 := by
    have h' : fderiv 𝕜 (fun u : E ↦ L (TotalSpace.mk' E w.proj u)) w.2 (e.symmL 𝕜 w.proj p.2) =
        fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2 p.2 :=
      DFunLike.congr_fun (fderiv_comp_symmL_eq_fderiv_extChartAt_symm L z₀ hp) p.2
    rwa [hv] at h'
  rw [lagrangianEnergy_apply, legendreMap_snd]
  exact congrArg (· - L w) h

variable [I.Boundaryless] {L : TangentBundle I M → 𝕜} {n : WithTop ℕ∞}

/-- On a boundaryless manifold, the momentum `(q, v) ↦ ∂_v ℓ(q, v)` of a `C²` Lagrangian `L`, read
in the preferred chart at `z₀`, is `C¹` at the chart image of `z₀`. -/
theorem contDiffAt_momentum_extChartAt (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hn : 2 ≤ n)
    (z₀ : TangentBundle I M) :
    ContDiffAt 𝕜 1 (fun p : E × E ↦ fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u)))
      p.2) (extChartAt I.tangent z₀ z₀) := by
  set p₀ := extChartAt I.tangent z₀ z₀
  have hℓ : ContDiffAt 𝕜 n (fun p ↦ L ((extChartAt I.tangent z₀).symm p)) (p₀.1, p₀.2) :=
    (hL z₀).contDiffAt_comp_extChartAt_symm
  have hg : ContDiffAt 𝕜 n (fun a : (E × E) × E ↦ (a.1.1, a.2)) (p₀, p₀.2) :=
    (contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd
  have hn' : (1 : WithTop ℕ∞) + 1 ≤ n := by simpa [one_add_one_eq_two] using hn
  exact ContDiffAt.fderiv (f := fun p u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u)))
    (ContDiffAt.comp (g := fun p : E × E ↦ L ((extChartAt I.tangent z₀).symm p)) (p₀, p₀.2) hℓ hg)
    contDiffAt_snd hn'

variable [IsManifold I 2 M]

/-- **The differential of the Legendre map in bundle charts.** On a boundaryless manifold, the
differential at `z₀` of the Legendre map of a `C²` Lagrangian is `(δq, δv) ↦ (δq, DP(δq, δv))`,
where `DP` is the derivative at the chart image of `z₀` of the momentum `(q, v) ↦ ∂_v ℓ(q, v)` of
`L` read in the chart at `z₀`. -/
theorem hasMFDerivAt_legendreMap (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hn : 2 ≤ n)
    (z₀ : TangentBundle I M) :
    HasMFDerivAt I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L) z₀
      ((ContinuousLinearMap.fst 𝕜 E E).prod (fderiv 𝕜 (fun p : E × E ↦
        fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2)
          (extChartAt I.tangent z₀ z₀))) := by
  refine ⟨(contMDiff_legendreMap (m := 1) hL (by simpa [one_add_one_eq_two] using hn)
    z₀).continuousAt, ?_⟩
  rw [ModelWithCorners.Boundaryless.range_eq_univ, hasFDerivWithinAt_univ]
  refine (hasFDerivAt_fst.prodMk ((contDiffAt_momentum_extChartAt hL hn z₀).differentiableAt
    one_ne_zero).hasFDerivAt).congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_target_mem_nhds z₀] with p hp
  exact extChartAt_legendreMap_extChartAt_symm L z₀ hp

/-- **The differential of the energy in bundle charts.** On a boundaryless manifold, the
differential at `z₀ = φ⁻¹(q₀, v₀)` of the energy of a `C²` Lagrangian sends `Y` to
`DP(Y)(v₀) - ∂_q ℓ(q₀, v₀)(Y.1)`, where `ℓ` is `L` read in the chart `φ` at `z₀` and `DP` is the
derivative at `(q₀, v₀)` of its momentum `(q, v) ↦ ∂_v ℓ(q, v)`. -/
theorem mvfderiv_lagrangianEnergy_apply (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hn : 2 ≤ n)
    (z₀ : TangentBundle I M) (Y : E × E) :
    mvfderiv I.tangent (lagrangianEnergy L) z₀ Y =
      fderiv 𝕜 (fun p : E × E ↦
        fderiv 𝕜 (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2)
          (extChartAt I.tangent z₀ z₀) Y (extChartAt I.tangent z₀ z₀).2 -
        fderiv 𝕜 (fun q ↦ L ((extChartAt I.tangent z₀).symm (q, (extChartAt I.tangent z₀ z₀).2)))
          (extChartAt I.tangent z₀ z₀).1 Y.1 := by
  set p₀ := extChartAt I.tangent z₀ z₀
  set ℓ : E × E → 𝕜 := fun p ↦ L ((extChartAt I.tangent z₀).symm p)
  set P : E × E → E →L[𝕜] 𝕜 := fun p ↦ fderiv 𝕜 (fun u ↦ ℓ (p.1, u)) p.2
  have hT : (extChartAt I.tangent z₀).target ∈ 𝓝 p₀ := extChartAt_target_mem_nhds z₀
  have hℓ : DifferentiableAt 𝕜 ℓ (p₀.1, p₀.2) :=
    ((hL z₀).contDiffAt_comp_extChartAt_symm.differentiableAt
      (ne_bot_of_le_ne_bot two_ne_zero hn))
  have hP : HasFDerivAt P (fderiv 𝕜 P p₀) p₀ :=
    ((contDiffAt_momentum_extChartAt hL hn z₀).differentiableAt one_ne_zero).hasFDerivAt
  -- In the chart, the energy is `p ↦ P p p.2 - ℓ p`.
  have hE : HasFDerivAt (fun p : E × E ↦ P p p.2 - ℓ p)
      ((fderiv 𝕜 P p₀).flip p₀.2 + (P p₀).comp (ContinuousLinearMap.snd 𝕜 E E) -
        fderiv 𝕜 ℓ p₀) p₀ := by
    refine ((hP.clm_apply hasFDerivAt_snd).sub hℓ.hasFDerivAt).congr_fderiv ?_
    ext Y <;> simp [add_comm]
  have hmd : MDifferentiableAt I.tangent 𝓘(𝕜, 𝕜) (lagrangianEnergy L) z₀ :=
    (contMDiff_lagrangianEnergy (m := 1) hL (by simpa [one_add_one_eq_two] using hn) z₀
      ).mdifferentiableAt one_ne_zero
  have heq : lagrangianEnergy L ∘ (extChartAt I.tangent z₀).symm =ᶠ[𝓝 p₀]
      fun p : E × E ↦ P p p.2 - ℓ p := by
    filter_upwards [hT] with p hp
    exact lagrangianEnergy_extChartAt_symm L z₀ hp
  rw [mvfderiv_eq_fderivWithin_extChartAt_target hmd, fderivWithin_of_mem_nhds hT]
  refine (congrArg (fun T : E × E →L[𝕜] 𝕜 ↦ T Y) (heq.fderiv_eq.trans hE.fderiv)).trans ?_
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd']
  rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hℓ]
  simp only [P]
  abel

end TauCeti
