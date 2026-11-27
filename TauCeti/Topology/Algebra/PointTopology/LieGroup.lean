/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Topology.Algebra.PointTopology.Group
public import TauCeti.Geometry.Manifold.Algebra.TranslatedChart
import TauCeti.Analysis.Analytic.AlgHomConvolution
import TauCeti.Topology.Algebra.PointTopology.SubmersiveChart

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

open Set Filter Topology WithConv
open OpenPartialHomeomorph
open scoped ContDiff Manifold

namespace TauCeti.PointTopology

variable {K H : Type*} [NontriviallyNormedField K] [CommRing H] [_root_.HopfAlgebra K H]

local notation "G" => WithConv (H →ₐ[K] K)

variable {n : ℕ}
local notation "V" => (Fin n → K)

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
  have hx' := (mem_translatedChart_source_iff e p (f x)).1 hx
  simp only [Function.comp_def, translatedChart_apply]
  exact analyticAt_chart_comp hs he hx' (continuousAt_const.mul hc)
    (analyticAt_eval_convMul (fun _ ↦ analyticAt_const) hf)

private theorem analyticAt_eval_translatedChart_symm
    (ha : ∀ b : H, AnalyticOnNhd K (fun z ↦ (e.symm z).ofConv b) e.target)
    {p : G} {z : V} (hz : z ∈ (translatedChart e p).target) (b : H) :
    AnalyticAt K (fun w ↦ ((translatedChart e p).symm w).ofConv b) z := by
  simp only [translatedChart_symm_apply]
  exact analyticAt_eval_convMul (fun _ ↦ analyticAt_const)
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
  simp only [atlas_chartedSpaceOfOne] at hc hd
  obtain ⟨p, rfl⟩ := hc
  obtain ⟨q, rfl⟩ := hd
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
  have hp := e.mem_translatedChart_source_self h₁ p
  exact (analyticAt_eval_translatedChart_symm ha ((translatedChart e p).map_source hp)
    b).contDiffAt.contDiffWithinAt

include hs he ha in
private theorem contMDiff_mul_chartedSpaceOfOne : letI := chartedSpaceOfOne e h₁
    ContMDiff ((𝓘(K, V)).prod (𝓘(K, V))) 𝓘(K, V) ω (fun p : G × G ↦ p.1 * p.2) := by
  let := chartedSpaceOfOne e h₁
  intro p
  apply contMDiffAt_iff.2
  refine ⟨continuous_mul.continuousAt, ?_⟩
  simp only [mfld_simps]
  have hp₁ := e.mem_translatedChart_source_self h₁ p.1
  have hp₂ := e.mem_translatedChart_source_self h₁ p.2
  have hz₁ := (translatedChart e p.1).map_source hp₁
  have hz₂ := (translatedChart e p.2).map_source hp₂
  have hx : (translatedChart e p.1).symm (translatedChart e p.1 p.1) *
      (translatedChart e p.2).symm (translatedChart e p.2 p.2) ∈
        (translatedChart e (p.1 * p.2)).source := by
    rw [(translatedChart e p.1).left_inv hp₁, (translatedChart e p.2).left_inv hp₂]
    exact e.mem_translatedChart_source_self h₁ _
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
    hs he hx (hc₁.mul hc₂) (analyticAt_eval_convMul hf hg)
  exact h.contDiffAt.contDiffWithinAt

include hs he ha in
private theorem contMDiff_inv_chartedSpaceOfOne : letI := chartedSpaceOfOne e h₁
    ContMDiff 𝓘(K, V) 𝓘(K, V) ω (fun p : G ↦ p⁻¹) := by
  let := chartedSpaceOfOne e h₁
  intro p
  apply contMDiffAt_iff.2
  refine ⟨continuous_inv.continuousAt, ?_⟩
  simp only [mfld_simps]
  have hp := e.mem_translatedChart_source_self h₁ p
  have hz := (translatedChart e p).map_source hp
  have hx : ((translatedChart e p).symm (translatedChart e p p))⁻¹ ∈
      (translatedChart e p⁻¹).source := by
    rw [(translatedChart e p).left_inv hp]
    exact e.mem_translatedChart_source_self h₁ _
  have hinv (b : H) : AnalyticAt K
      (fun z : V ↦ (((translatedChart e p).symm z)⁻¹).ofConv b)
      (translatedChart e p p) := by
    simp only [WithConv.algHom_inv_apply]
    exact analyticAt_eval_translatedChart_symm ha hz (HopfAlgebraStruct.antipode K b)
  have h := analyticAt_translatedChart_comp (f := fun z ↦ ((translatedChart e p).symm z)⁻¹)
    hs he hx ((translatedChart e p).continuousAt_symm hz).inv hinv
  exact h.contDiffAt.contDiffWithinAt

include hs he ha in
private theorem lieGroup_chartedSpaceOfOne : letI := chartedSpaceOfOne e h₁
    LieGroup 𝓘(K, V) ω G := by
  let := chartedSpaceOfOne e h₁
  exact
    { toIsManifold := isManifold_chartedSpaceOfOne h₁ hs he ha
      contMDiff_inv := contMDiff_inv_chartedSpaceOfOne h₁ hs he ha
      contMDiff_mul := contMDiff_mul_chartedSpaceOfOne h₁ hs he ha }

end Manifold

public section

variable (K H) in
/-- The dimension of the analytic charts, given by the cotangent space at the identity. -/
noncomputable def chartDimension : ℕ := Module.finrank K (Bialgebra.CotangentSpace K H)

variable (K H) in
/-- The chart dimension equals the dimension of the augmentation ideal modulo its square. -/
theorem chartDimension_eq_finrank_cotangentSpace :
    chartDimension K H = Module.finrank K (Bialgebra.CotangentSpace K H) := (rfl)

end

section Smooth

variable (K H) [CompleteSpace K] [Algebra.Smooth K H]

private theorem exists_identityChart :
    ∃ (e : OpenPartialHomeomorph G (Fin (chartDimension K H) → K)), (1 : G) ∈ e.source ∧
      (∃ (s : H) (a : Fin (chartDimension K H) → H) (m : Fin (chartDimension K H) → ℕ),
        ∀ p ∈ e.source, p.ofConv s ≠ 0 ∧ ∀ i, e p i = p.ofConv (a i) / p.ofConv s ^ m i) ∧
      ∀ b : H, AnalyticOnNhd K (fun z ↦ (e.symm z).ofConv b) e.target := by
  have hdim : Module.finrank K (RingHom.ker (1 : G).ofConv).Cotangent = chartDimension K H := by
    rw [Bialgebra.ofConv_one_eq_counitAlgHom, chartDimension_eq_finrank_cotangentSpace]
    rfl
  have hchart := Algebra.Smooth.exists_openPartialHomeomorph_points (1 : G).ofConv
  rw [hdim] at hchart
  obtain ⟨E, s, b, h₁, -, hsource, he, ha⟩ := hchart
  let j : G ≃ₜ (H →ₐ[K] K) := isHomeomorph_ofConv.homeomorph
  have hj (p : G) : j p = p.ofConv := IsHomeomorph.homeomorph_apply ..
  let e := j.transOpenPartialHomeomorph E
  have h₁' : (1 : G) ∈ e.source := by simpa [e, hj] using h₁
  have hs (p : G) (hp : p ∈ e.source) : p.ofConv s ≠ 0 := by
    apply isUnit_iff_ne_zero.1 (hsource ?_)
    simpa [e, hj] using hp
  have ha' (a : H) : AnalyticOnNhd K (fun z ↦ (e.symm z).ofConv a) e.target := by
    simpa [e, ← hj] using ha a
  classical
  choose m a hm using fun i ↦ IsLocalization.Away.surj s (b i)
  have he' (p : G) (hp : p ∈ e.source) (i : Fin (chartDimension K H)) :
      e p i = p.ofConv (a i) / p.ofConv s ^ m i := by
    let ι : H →ₐ[K] Localization.Away s := IsScalarTower.toAlgHom K H (Localization.Away s)
    have hmem : p.ofConv ∈ Set.range (fun y : Localization.Away s →ₐ[K] K ↦ y.comp ι) := by
      rw [IsLocalization.Away.range_comp_toAlgHom s]
      exact isUnit_iff_ne_zero.2 (hs p hp)
    obtain ⟨y, hy⟩ := hmem
    have hy' (c : H) : y (algebraMap H (Localization.Away s) c) = p.ofConv c :=
      DFunLike.congr_fun hy c
    simp only [e, Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply, hj]
    have hforward : E p.ofConv i = y (b i) := (congrArg (fun z ↦ E z i) hy).symm.trans (he y i)
    rw [hforward, eq_div_iff (pow_ne_zero _ (hs p hp)), ← hy' s, ← hy' (a i)]
    simpa only [map_mul, map_pow] using congrArg y (hm i)
  exact ⟨e, h₁', ⟨s, a, m, fun p hp ↦ ⟨hs p hp, he' p hp⟩⟩, ha'⟩

public section

/-- The chosen chart at the identity, obtained from smooth local parameters. -/
noncomputable def identityChart : OpenPartialHomeomorph G (Fin (chartDimension K H) → K) :=
  (exists_identityChart K H).choose

/-- The chosen chart at the identity contains the identity in its source. -/
theorem one_mem_identityChart_source : (1 : G) ∈ (identityChart K H).source :=
  (exists_identityChart K H).choose_spec.1

/-- The coordinates of the identity chart are evaluations of fractions with a common
denominator element that is nonzero on the chart source. -/
theorem exists_identityChart_apply_eq_div :
    ∃ (s : H) (a : Fin (chartDimension K H) → H) (m : Fin (chartDimension K H) → ℕ),
      ∀ p ∈ (identityChart K H).source, p.ofConv s ≠ 0 ∧
        ∀ i, identityChart K H p i = p.ofConv (a i) / p.ofConv s ^ m i :=
  (exists_identityChart K H).choose_spec.2.1

/-- Each coordinate evaluation pulled back by the identity chart is analytic on its target. -/
theorem analyticOnNhd_eval_identityChart_symm (b : H) :
    AnalyticOnNhd K (fun z ↦ ((identityChart K H).symm z).ofConv b) (identityChart K H).target :=
  (exists_identityChart K H).choose_spec.2.2 b

/-- The analytic atlas of the smooth affine group, obtained by left translation of the
chosen identity chart. Use `letI := chartedSpace K H` to install it locally. -/
@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace (Fin (chartDimension K H) → K) G :=
  (identityChart K H).chartedSpaceOfOne (one_mem_identityChart_source K H)

/-- Every chart in the chosen charted space is the left translate at its base point of the
chosen identity chart. -/
@[simp]
theorem chartAt_eq_translatedChart (p : G) : letI := chartedSpace K H
    chartAt (Fin (chartDimension K H) → K) p = (identityChart K H).translatedChart p :=
  chartAt_chartedSpaceOfOne _ (one_mem_identityChart_source K H) p

/-- The points of a smooth commutative Hopf algebra form an analytic Lie group in the
chosen atlas, for the evaluation topology and convolution group law. -/
scoped instance lieGroup : letI := chartedSpace K H
    LieGroup 𝓘(K, Fin (chartDimension K H) → K) ω G := by
  obtain ⟨s, a, m, h⟩ := exists_identityChart_apply_eq_div K H
  exact lieGroup_chartedSpaceOfOne (one_mem_identityChart_source K H)
    (fun p hp ↦ (h p hp).1) (fun p hp ↦ (h p hp).2)
    (analyticOnNhd_eval_identityChart_symm K H)

/-- Every coordinate evaluation is analytic in the chosen charted space of smooth affine
group points. -/
theorem contMDiff_eval_ofConv (b : H) : letI := chartedSpace K H
    ContMDiff 𝓘(K, Fin (chartDimension K H) → K) 𝓘(K) ω (fun p : G ↦ p.ofConv b) :=
  contMDiff_eval_chartedSpaceOfOne (one_mem_identityChart_source K H)
    (analyticOnNhd_eval_identityChart_symm K H) b

end

end Smooth

end TauCeti.PointTopology
