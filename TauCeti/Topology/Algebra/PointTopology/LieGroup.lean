/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.PointTopology.Group
import TauCeti.Topology.Algebra.PointTopology.SubmersiveChart
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analytic Lie groups of points of smooth affine groups

Over a complete nontrivially normed field, the points of a smooth affine group scheme, with
their evaluation topology and convolution group law, carry a finite-dimensional analytic Lie
group structure. This works in every characteristic. A chart at the identity comes from a
submersive presentation on a principal open. Its forward coordinates are fractions of
evaluations and its inverse parametrizes all evaluations analytically. Left translations
give charts of the same dimension at every point.

The convolution product evaluates as a finite sum of products of coordinates, and inversion
evaluates by pulling back along the antipode. These formulas give analytic group operations
and analytic coordinate evaluations in the resulting manifold structure.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §4, p. 11.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1,
  second edition, §3.1.
-/

open Set Filter Topology Coalgebra WithConv
open scoped ContDiff Manifold

namespace TauCeti.PointTopology

variable {K H : Type*} [NontriviallyNormedField K] [CommRing H] [_root_.HopfAlgebra K H]

local notation "G" => WithConv (H →ₐ[K] K)

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {x : E} {f g : E → WithConv (H →ₐ[K] K)}

/-- Convolution preserves analyticity of the coordinate evaluations. -/
private theorem analyticAt_eval_mul
    (hf : ∀ a : H, AnalyticAt K (fun z ↦ (f z).ofConv a) x)
    (hg : ∀ a : H, AnalyticAt K (fun z ↦ (g z).ofConv a) x) (a : H) :
    AnalyticAt K (fun z ↦ (f z * g z).ofConv a) x := by
  have heq (z : E) : (f z * g z).ofConv a =
      ∑ i ∈ (ℛ K a).index,
        (f z).ofConv ((ℛ K a).left i) * (g z).ofConv ((ℛ K a).right i) := by
    have h := (ℛ K a).convMul_apply
      (toConv (f z).ofConv.toLinearMap) (toConv (g z).ofConv.toLinearMap)
    rw [← AlgHom.toLinearMap_convMul] at h
    exact h
  simp_rw [heq]
  exact Finset.analyticAt_fun_sum _ fun i _ ↦ (hf _).mul (hg _)

end Analytic

variable {n : ℕ}
local notation "V" => (Fin n → K)

section Chart

variable (e : OpenPartialHomeomorph (WithConv (H →ₐ[K] K)) (Fin n → K))

/-- The translation of the identity chart to the point `p`. -/
private noncomputable def translatedChart (p : G) : OpenPartialHomeomorph G V :=
  (Homeomorph.mulLeft p⁻¹).toOpenPartialHomeomorph.trans e

private theorem translatedChart_apply (p q : G) :
    translatedChart e p q = e (p⁻¹ * q) := by
  rw [translatedChart, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_mulLeft]

private theorem translatedChart_symm_apply (p : G) (z : V) :
    (translatedChart e p).symm z = p * e.symm z := by
  rw [translatedChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply, ← Homeomorph.symm_toOpenPartialHomeomorph,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.mulLeft_symm, inv_inv,
    Homeomorph.coe_mulLeft]

private theorem translatedChart_target (p : G) : (translatedChart e p).target = e.target := by
  rw [translatedChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ]

/-- The atlas obtained by left translating an identity chart. -/
@[instance_reducible]
private noncomputable def chartedSpaceOfOne (h₁ : (1 : G) ∈ e.source) : ChartedSpace V G where
  atlas := range (translatedChart e)
  chartAt := translatedChart e
  mem_chart_source p := by
    simpa [translatedChart, OpenPartialHomeomorph.trans_source, Homeomorph.coe_mulLeft] using h₁
  chart_mem_atlas p := mem_range_self p

end Chart

variable {e : OpenPartialHomeomorph (WithConv (H →ₐ[K] K)) (Fin n → K)}
  {s : H} {a : Fin n → H} {m : Fin n → ℕ}

/-- The forward chart with fraction coordinates preserves analyticity of evaluations. -/
private theorem analyticAt_chart_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    {x : E} {f : E → G} (hs : ∀ (p : G), p ∈ e.source → p.ofConv s ≠ 0)
    (he : ∀ (p : G), p ∈ e.source → ∀ i, e p i = p.ofConv (a i) / p.ofConv s ^ m i)
    (hx : f x ∈ e.source) (hc : ContinuousAt f x)
    (hf : ∀ b : H, AnalyticAt K (fun z ↦ (f z).ofConv b) x) :
    AnalyticAt K (e ∘ f) x := by
  apply AnalyticAt.pi
  intro i
  refine ((hf (a i)).div ((hf s).pow (m i)) (pow_ne_zero _ (hs _ hx))).congr ?_
  filter_upwards [hc (e.open_source.mem_nhds hx)] with z hz
  exact (he (f z) hz i).symm

private theorem analyticAt_translatedChart_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    {x : E} {f : E → G} {p : G} (hs : ∀ (q : G), q ∈ e.source → q.ofConv s ≠ 0)
    (he : ∀ (q : G), q ∈ e.source → ∀ i, e q i = q.ofConv (a i) / q.ofConv s ^ m i)
    (hx : f x ∈ (translatedChart e p).source) (hc : ContinuousAt f x)
    (hf : ∀ b : H, AnalyticAt K (fun z ↦ (f z).ofConv b) x) :
    AnalyticAt K (translatedChart e p ∘ f) x := by
  have hx' : p⁻¹ * f x ∈ e.source := by
    simpa [translatedChart, OpenPartialHomeomorph.trans_source, Homeomorph.coe_mulLeft] using hx
  simp only [Function.comp_def, translatedChart_apply]
  exact analyticAt_chart_comp hs he hx' (continuousAt_const.mul hc)
    (analyticAt_eval_mul (fun _ ↦ analyticAt_const) hf)

private theorem analyticAt_eval_translatedChart_symm
    (ha : ∀ b : H, AnalyticOnNhd K (fun z ↦ (e.symm z).ofConv b) e.target)
    {p : G} {z : V} (hz : z ∈ (translatedChart e p).target) (b : H) :
    AnalyticAt K (fun w ↦ ((translatedChart e p).symm w).ofConv b) z := by
  simp only [translatedChart_symm_apply]
  exact analyticAt_eval_mul (fun _ ↦ analyticAt_const)
    (fun b ↦ ha b z ((translatedChart_target e p) ▸ hz)) b

section Manifold

variable [CompleteSpace K] (h₁ : (1 : WithConv (H →ₐ[K] K)) ∈ e.source)
  (hs : ∀ (p : WithConv (H →ₐ[K] K)), p ∈ e.source → p.ofConv s ≠ 0)
  (he : ∀ (p : WithConv (H →ₐ[K] K)), p ∈ e.source → ∀ i, e p i = p.ofConv (a i) / p.ofConv s ^ m i)
  (ha : ∀ b : H, AnalyticOnNhd K (fun z ↦ (e.symm z).ofConv b) e.target)

include hs he ha in
private theorem isManifold_chartedSpaceOfOne : letI := chartedSpaceOfOne e h₁
    IsManifold 𝓘(K, V) ω G := by
  let := chartedSpaceOfOne e h₁
  refine isManifold_of_contDiffOn 𝓘(K, V) ω G fun c d hc hd ↦ ?_
  obtain ⟨p, rfl⟩ : c ∈ range (translatedChart e) := hc
  obtain ⟨q, rfl⟩ : d ∈ range (translatedChart e) := hd
  simp only [mfld_simps]
  refine AnalyticOnNhd.contDiffOn_of_completeSpace ?_
  intro z hz
  exact analyticAt_translatedChart_comp hs he hz.2
    ((translatedChart e p).continuousAt_symm hz.1)
    (analyticAt_eval_translatedChart_symm ha hz.1)

include ha in
private theorem contMDiff_eval_chartedSpaceOfOne (b : H) : letI := chartedSpaceOfOne e h₁
    ContMDiff 𝓘(K, V) 𝓘(K) ω (fun p : G ↦ p.ofConv b) := by
  let := chartedSpaceOfOne e h₁
  intro p
  apply contMDiffAt_iff.2
  refine ⟨(continuous_eval_ofConv b).continuousAt, ?_⟩
  simp only [mfld_simps]
  exact (analyticAt_eval_translatedChart_symm ha
    ((translatedChart e p).map_source (mem_chart_source V p)) b).contDiffAt.contDiffWithinAt

include hs he ha in
private theorem contMDiff_mul_chartedSpaceOfOne : letI := chartedSpaceOfOne e h₁
    ContMDiff ((𝓘(K, V)).prod (𝓘(K, V))) 𝓘(K, V) ω (fun p : G × G ↦ p.1 * p.2) := by
  let := chartedSpaceOfOne e h₁
  intro p
  apply contMDiffAt_iff.2
  refine ⟨continuous_mul.continuousAt, ?_⟩
  simp only [mfld_simps]
  have hp₁ := mem_chart_source V p.1
  have hp₂ := mem_chart_source V p.2
  have hz₁ := (translatedChart e p.1).map_source hp₁
  have hz₂ := (translatedChart e p.2).map_source hp₂
  have hx : (translatedChart e p.1).symm (translatedChart e p.1 p.1) *
      (translatedChart e p.2).symm (translatedChart e p.2 p.2) ∈
        (translatedChart e (p.1 * p.2)).source := by
    rw [(translatedChart e p.1).left_inv hp₁, (translatedChart e p.2).left_inv hp₂]
    exact mem_chart_source V (p.1 * p.2)
  let z₀ : V × V := (translatedChart e p.1 p.1, translatedChart e p.2 p.2)
  let f : V × V → G := fun z ↦ (translatedChart e p.1).symm z.1
  let g : V × V → G := fun z ↦ (translatedChart e p.2).symm z.2
  have hf (b : H) : AnalyticAt K (fun z ↦ (f z).ofConv b) z₀ :=
    AnalyticAt.comp (x := z₀) (f := Prod.fst)
      (analyticAt_eval_translatedChart_symm ha hz₁ b) analyticAt_fst
  have hg (b : H) : AnalyticAt K (fun z ↦ (g z).ofConv b) z₀ :=
    AnalyticAt.comp (x := z₀) (f := Prod.snd)
      (analyticAt_eval_translatedChart_symm ha hz₂ b) analyticAt_snd
  have hc₁ : ContinuousAt f z₀ :=
    ContinuousAt.comp (x := z₀) (f := Prod.fst)
      ((translatedChart e p.1).continuousAt_symm hz₁) continuousAt_fst
  have hc₂ : ContinuousAt g z₀ :=
    ContinuousAt.comp (x := z₀) (f := Prod.snd)
      ((translatedChart e p.2).continuousAt_symm hz₂) continuousAt_snd
  have h := analyticAt_translatedChart_comp (f := fun z ↦ f z * g z) (x := z₀)
    hs he hx (hc₁.mul hc₂) (analyticAt_eval_mul hf hg)
  exact h.contDiffAt.contDiffWithinAt

include hs he ha in
private theorem lieGroup_chartedSpaceOfOne : letI := chartedSpaceOfOne e h₁
    LieGroup 𝓘(K, V) ω G := by
  let := chartedSpaceOfOne e h₁
  exact {
    toIsManifold := isManifold_chartedSpaceOfOne h₁ hs he ha
    contMDiff_inv := by
      intro p
      apply contMDiffAt_iff.2
      refine ⟨continuous_inv.continuousAt, ?_⟩
      simp only [mfld_simps]
      have hp := mem_chart_source V p
      have hz := (translatedChart e p).map_source hp
      have hx : ((translatedChart e p).symm (translatedChart e p p))⁻¹ ∈
          (translatedChart e p⁻¹).source := by
        rw [(translatedChart e p).left_inv hp]
        exact mem_chart_source V p⁻¹
      have hinv (b : H) : AnalyticAt K
          (fun z : V ↦ (((translatedChart e p).symm z)⁻¹).ofConv b)
          (translatedChart e p p) := by
        simp only [WithConv.algHom_inv_apply]
        exact analyticAt_eval_translatedChart_symm ha hz (HopfAlgebraStruct.antipode K b)
      have h := analyticAt_translatedChart_comp (f := fun z ↦ ((translatedChart e p).symm z)⁻¹)
        hs he hx ((translatedChart e p).continuousAt_symm hz).inv hinv
      exact h.contDiffAt.contDiffWithinAt
    contMDiff_mul := contMDiff_mul_chartedSpaceOfOne h₁ hs he ha }

end Manifold

public section

/-- **Analytic Lie group of points of a smooth affine group.** Over a complete nontrivially
normed field, a smooth commutative Hopf algebra has a finite-dimensional analytic Lie group of
points for the evaluation topology and convolution group law. Every coordinate evaluation is
analytic in the same manifold structure. -/
theorem exists_lieGroup [CompleteSpace K] [Algebra.Smooth K H] :
    ∃ (d : ℕ) (C : ChartedSpace (Fin d → K) G), letI := C
      LieGroup 𝓘(K, Fin d → K) ω G ∧
        ∀ a : H, ContMDiff 𝓘(K, Fin d → K) 𝓘(K) ω (fun p : G ↦ p.ofConv a) := by
  obtain ⟨n, E, s, b, h₁, -, hsource, he, ha⟩ :=
    Algebra.Smooth.exists_openPartialHomeomorph_points (1 : G).ofConv
  let j : G ≃ₜ (H →ₐ[K] K) := isHomeomorph_ofConv.homeomorph
  have hj (p : G) : j p = p.ofConv := IsHomeomorph.homeomorph_apply ..
  let e := j.toOpenPartialHomeomorph.trans E
  have h₁' : (1 : G) ∈ e.source := by
    simpa [e, OpenPartialHomeomorph.trans_source, hj] using h₁
  have hs (p : G) (hp : p ∈ e.source) : p.ofConv s ≠ 0 :=
    isUnit_iff_ne_zero.1 (hsource (hj p ▸ hp.2))
  have ha' (a : H) : AnalyticOnNhd K (fun z ↦ (e.symm z).ofConv a) e.target := by
    have hsymm (z : Fin n → K) : (e.symm z).ofConv = E.symm z := by
      simp only [e, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply, ← Homeomorph.symm_toOpenPartialHomeomorph,
        Homeomorph.toOpenPartialHomeomorph_apply, ← hj, Homeomorph.apply_symm_apply]
    intro z hz
    simpa only [hsymm] using ha a z hz.1
  classical
  choose m a hm using fun i ↦ IsLocalization.Away.surj s (b i)
  have he' (p : G) (hp : p ∈ e.source) (i : Fin n) :
      e p i = p.ofConv (a i) / p.ofConv s ^ m i := by
    let ι : H →ₐ[K] Localization.Away s := IsScalarTower.toAlgHom K H (Localization.Away s)
    have hmem : p.ofConv ∈ Set.range (fun y : Localization.Away s →ₐ[K] K ↦ y.comp ι) := by
      rw [IsLocalization.Away.range_comp_toAlgHom s]
      exact isUnit_iff_ne_zero.2 (hs p hp)
    obtain ⟨y, hy⟩ := hmem
    have hy' (c : H) : y (algebraMap H (Localization.Away s) c) = p.ofConv c :=
      DFunLike.congr_fun hy c
    simp only [e, OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply, hj]
    have hforward : E p.ofConv i = y (b i) := (congrArg (fun z ↦ E z i) hy).symm.trans (he y i)
    rw [hforward, eq_div_iff (pow_ne_zero _ (hs p hp)), ← hy' s, ← hy' (a i)]
    simpa only [map_mul, map_pow] using congrArg y (hm i)
  exact ⟨n, chartedSpaceOfOne e h₁', lieGroup_chartedSpaceOfOne h₁' hs he' ha',
    contMDiff_eval_chartedSpaceOfOne h₁' ha'⟩

end

end TauCeti.PointTopology
