/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Distance.Energy
import TauCeti.Analysis.InnerProductSpace.Laplacian.UpperSupport.Sqrt
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Intrinsic distance upper supports from approximate curve energies

Families of `C¹` curves from `q` to `exp_p v` majorize the distance by the square root of twice
their energy. Uniform one-sided quadratic energy expansions whose scales tend to `dist q p`
therefore give a smooth touching upper support on an open neighbourhood of `p`. The normalized
linear and trace bounds become bounds for the intrinsic gradient and Laplace–Beltrami operator
at `p`, using normal-coordinate transport. No smooth dependence of the curves on `v` or on the
approximation index is needed.

This constructs the barrier from approximate energy data even when no one comparison curve
attains the distance. It supplies the chart-transport step in the cut-locus support arguments for
localized Shi estimates.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorems 3.27–3.29.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace TauCeti.Manifold

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M]
  {p : M} {U : Set (TangentSpace I p)}

private theorem transport_upper_support (h : IsNormalDomain I M p U)
    (f : M → ℝ) {P : TangentSpace I p → ℝ} (hP : ContDiff ℝ ∞ P)
    (hP0 : P 0 = f p) (hmajor : ∀ᶠ v in 𝓝 0, f (riemannianExp I M p v) ≤ P v)
    {K Λ : ℝ} (hK : ‖fderiv ℝ P 0‖ ≤ K) (hΛ : Laplacian.laplacian P 0 ≤ Λ) :
    ∃ (V : Set M) (g : M → ℝ), IsOpen V ∧ p ∈ V ∧ ContMDiffOn I 𝓘(ℝ) ∞ g V ∧
      g p = f p ∧ (∀ x ∈ V, f x ≤ g x) ∧ ‖mgradient I g p‖ ≤ K ∧
      laplaceBeltrami I g p ≤ Λ := by
  have hlog := h.contMDiffOn_riemannianLog.contMDiffAt
    (h.isOpen_image.mem_nhds h.self_mem_image)
  have htend : Tendsto (riemannianLog I M p U) (𝓝 p) (𝓝 0) := by
    simpa only [h.riemannianLog_self] using hlog.continuousAt.tendsto
  have hlocal : ∀ᶠ x in 𝓝 p, f x ≤ (P ∘ riemannianLog I M p U) x := by
    filter_upwards [h.isOpen_image.mem_nhds h.self_mem_image, htend hmajor] with x hx hxP
    -- Expose the composed majorant so the exponential-logarithm identity applies.
    change f (riemannianExp I M p (riemannianLog I M p U x)) ≤
      P (riemannianLog I M p U x) at hxP
    simpa only [Function.comp_apply, riemannianExp_riemannianLog hx] using hxP
  have hboth : ∀ᶠ x in 𝓝 p, x ∈ riemannianExp I M p '' U ∧
      f x ≤ (P ∘ riemannianLog I M p U) x := by
    filter_upwards [h.isOpen_image.mem_nhds h.self_mem_image, hlocal] with x hx hxP
    exact ⟨hx, hxP⟩
  obtain ⟨V, hV, hVo, hVp⟩ := mem_nhds_iff.mp hboth
  refine ⟨V, P ∘ riemannianLog I M p U, hVo, hVp, ?_,
    by simpa only [Function.comp_apply, h.riemannianLog_self] using hP0,
    fun x hx ↦ (hV hx).2, ?_, ?_⟩
  · exact (hP.contMDiff.comp_contMDiffOn h.contMDiffOn_riemannianLog).mono
      (fun x hx ↦ (hV hx).1)
  · simpa only [norm_mgradient_eq_norm_mvfderiv,
      h.mvfderiv_comp_riemannianLog_self P] using hK
  · simpa only [h.laplaceBeltrami_comp_riemannianLog_self
      (hP.contDiffAt.of_le (by simp))] using hΛ

end Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M]
  {p : M} {U : Set (TangentSpace I p)}

namespace IsNormalDomain

/-- The canonical operator norm on cotangent vectors for bilinear coefficient bounds. -/
local instance : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical scalar action on cotangent vectors. -/
local instance : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Approximate energies of curves from `q` to `exp_p v` give a smooth touching upper support
for `dist q` on an open neighbourhood of `p`. Its intrinsic gradient norm at `p` is at most `K`
and its Laplace–Beltrami operator there is at most `Λ + ε`. -/
theorem exists_contMDiffOn_apply_eq_ge_norm_mgradient_le_laplaceBeltrami_le_of_energy
    [IsRiemannianManifold I M] (h : IsNormalDomain I M p U) (q : M)
    {κ : Type*} {l : Filter κ} [l.NeBot]
    (Γ : κ → TangentSpace I p → ℝ → M) (c b : κ → ℝ)
    (L : κ → TangentSpace I p →L[ℝ] ℝ)
    (Q : κ → TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (K B ρ₀ C₀ Λ : ℝ) (hqp : 0 < dist q p) (hρ₀ : 0 < ρ₀)
    (hc : Tendsto c l (𝓝 (dist q p))) (hb : Tendsto b l (𝓝 Λ))
    (hL : ∀ᶠ j in l, ‖L j‖ ≤ 2 * K * c j) (hQ : ∀ᶠ j in l, ‖Q j‖ ≤ B)
    (htrace : ∀ᶠ j in l,
      traceL ((2 * c j)⁻¹ • Q j - (4 * c j ^ 3)⁻¹ • (L j).smulRight (L j)) ≤ b j)
    (hcurves : ∀ᶠ j in l, ∀ v, ‖v‖ < ρ₀ →
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (Γ j v) (Icc 0 1) ∧
        Γ j v 0 = q ∧ Γ j v 1 = riemannianExp I M p v)
    (herror : ∀ᶠ j in l, ∀ v, ‖v‖ < ρ₀ →
      2 * energy I (Γ j v) 0 1 ≤ c j ^ 2 + L j v + Q j v v / 2 + C₀ * ‖v‖ ^ 3)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : Set M) (g : M → ℝ), IsOpen V ∧ p ∈ V ∧ ContMDiffOn I 𝓘(ℝ) ∞ g V ∧
      g p = dist q p ∧ (∀ x ∈ V, dist q x ≤ g x) ∧ ‖mgradient I g p‖ ≤ K ∧
      laplaceBeltrami I g p ≤ Λ + ε := by
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  let f := fun v : TangentSpace I p ↦ dist q (riemannianExp I M p v)
  let F := fun j v ↦ 2 * energy I (Γ j v) 0 1
  have hf0 : f 0 = dist q p := by simp only [f, riemannianExp_zero]
  have hmajor : ∀ᶠ j in l, ∀ v, dist v 0 < ρ₀ → f v ≤ Real.sqrt (F j v) := by
    filter_upwards [hcurves] with j hj
    intro v hv
    obtain ⟨hγ, h0, h1⟩ := hj v (by simpa only [dist_zero_right] using hv)
    simpa only [h0, h1, f, F, sub_zero, mul_one] using
      TauCeti.IsRiemannianManifold.dist_le_sqrt_two_mul_energy hγ zero_le_one (Subset.refl _)
  obtain ⟨P, hP, hP0, hPf, hPd, hPΔ⟩ :=
    exists_contDiff_apply_eq_ge_norm_fderiv_le_laplacian_le_of_le_sqrt f 0 F c b L Q
      K B ρ₀ C₀ Λ (by simpa only [hf0] using hqp) hρ₀
      (by simpa only [hf0] using hc) hb hL hQ htrace
      (by simpa only [F, sub_zero, dist_zero_right] using herror) hmajor hε
  exact transport_upper_support h (fun x ↦ dist q x) hP
    (by simpa only [hf0] using hP0) hPf hPd hPΔ

end IsNormalDomain

end TauCeti.Manifold
