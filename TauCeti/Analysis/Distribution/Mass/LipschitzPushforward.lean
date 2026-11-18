/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.Distribution.TestFunction.Homotopy
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.Analysis.Distribution.Mass.Support
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Pushforward of normal currents along Lipschitz maps

Let `Ω` be an open subset of a finite-dimensional real normed space `E`, and let `T` be a real
normal current on `Ω` (a current of finite mass with boundary of finite mass) whose support is a
compact subset of `Ω`. Along a map `f` smooth on `Ω` with values in a finite-dimensional real
normed space `E'`, the pushforward is `f_# T = T ∘ (χ f^*)` for a test function `χ` equal to one
near the support (`TauCeti.Analysis.Distribution.CutoffPushforward`). This file extends it to maps
which are only Lipschitz near the support.

The key estimate is the homotopy estimate `Distribution.norm_map_cutoffPullbackCLM_sub_le`: if `f`
and `g` are smooth on `Ω` with `‖g - f‖ ≤ ε` and `‖Df‖, ‖Dg‖ ≤ L` on the support of a normal
`(k + 1)`-current `T`, then

`|g_# T (ω) - f_# T (ω)| ≤ ε (L ^ (k + 1) M(T) sup ‖dω‖ + L ^ k M(∂T) sup ‖ω‖)`,

with the degree-zero version `Distribution.norm_map_cutoffPullbackCLM_sub_le_finZero`. It comes from
the homotopy formula for the straight-line homotopy `(1 - t) f + t g`. That homotopy need not be
proper on `Ω × [0, 1]`, so the formula is applied to its graph `(x, t) ↦ (x, (1 - t) f x + t g x)`,
which is proper with values in `Ω × E'`, and the test form is pulled back along the projection to
`E'` with a cutoff equal to one near the graph over the support. The bounds only use the mass
measure of `T`, which is carried by the support, so the hypotheses are only needed there.

Consequently, if maps `gⱼ` smooth on `Ω` converge uniformly on the support to `f`, with uniformly
bounded derivatives there, then `gⱼ# T (ω)` converges for every test form `ω`, to a limit which
does not depend on the sequence. This limit is the current `Distribution.lipschitzPushforward T f`
(`Distribution.tendsto_lipschitzPushforward`). If `f` is `L`-Lipschitz on a neighbourhood of the
support, such sequences exist with derivatives bounded by `L` on the support
(`LipschitzOnWith.exists_contDiff_dist_lt_norm_fderiv_le`), and

* `Distribution.mass_lipschitzPushforward_le`: `M(f_# T) ≤ L ^ k M(T)`;
* `Distribution.lipschitzPushforward_comp_extDerivCLM`: `∂ (f_# T) = f_# (∂ T)`;
* `Distribution.dsupport_lipschitzPushforward_subset`: `spt (f_# T) ⊆ f (spt T)`;
* `Distribution.isNormal_lipschitzPushforward`: `f_# T` is normal.

Along maps smooth on `Ω` it is the smooth pushforward
(`Distribution.lipschitzPushforward_eq_comp_cutoffPullbackCLM`), and it only depends on the values
of the map on the support of `T` (`Distribution.lipschitzPushforward_congr`).

Currents here are real valued, as the bounds go through the mass measure. Flat convergence of the
approximating pushforwards and pushforwards of currents without compact support are not treated.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.9 (the homotopy formula and its estimate) and
  §4.1.14 (pushforward along Lipschitz maps by smooth approximation).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula).
-/

public section

noncomputable section

open Set Filter TopologicalSpace TestFunction
open scoped Distributions Topology NNReal ENNReal BoundedContinuousFunction

namespace Distribution

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {k m : ℕ} {f g : E → E'}

section Homotopy

/-! ### The straight-line homotopy and its graph -/

/-- The straight-line homotopy `(x, t) ↦ f x + t (g x - f x)` from `f` to `g`. -/
private def lineHomotopy (f g : E → E') (p : E × ℝ) : E' :=
  f p.1 + p.2 • (g p.1 - f p.1)

/-- The graph `(x, t) ↦ (x, f x + t (g x - f x))` of the straight-line homotopy. Unlike the
homotopy itself, it is proper on `Ω × [0, 1]` with values in `Ω × E'`. -/
private def graphHomotopy (f g : E → E') (p : E × ℝ) : E × E' :=
  (p.1, lineHomotopy f g p)

/-- The open set `Ω × E'`, the target of the graph of the homotopy. -/
private def graphDomain (Ω : Opens E) (E' : Type*) [TopologicalSpace E'] : Opens (E × E') :=
  ⟨Prod.fst ⁻¹' Ω, Ω.isOpen.preimage continuous_fst⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
private theorem mem_graphDomain {p : E × E'} : p ∈ graphDomain Ω E' ↔ p.1 ∈ Ω :=
  Iff.rfl

variable (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
include hf hg

private theorem contDiffAt_lineHomotopy {p : E × ℝ} (hp : p.1 ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) (lineHomotopy f g) p := by
  have hfp := (hf.contDiffAt (Ω.isOpen.mem_nhds hp)).comp p contDiffAt_fst
  have hgp := (hg.contDiffAt (Ω.isOpen.mem_nhds hp)).comp p contDiffAt_fst
  exact hfp.add (contDiffAt_snd.smul (hgp.sub hfp))

private theorem hasFDerivAt_lineHomotopy {p : E × ℝ} (hp : p.1 ∈ Ω) :
    HasFDerivAt (lineHomotopy f g)
      ((fderiv ℝ f p.1).comp (.fst ℝ E ℝ) +
        (p.2 • ((fderiv ℝ g p.1).comp (.fst ℝ E ℝ) - (fderiv ℝ f p.1).comp (.fst ℝ E ℝ)) +
          (ContinuousLinearMap.snd ℝ E ℝ).smulRight (g p.1 - f p.1))) p := by
  have hfp := ((hf.contDiffAt (Ω.isOpen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp
    p hasFDerivAt_fst
  have hgp := ((hg.contDiffAt (Ω.isOpen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp
    p hasFDerivAt_fst
  exact hfp.add (hasFDerivAt_snd.smul (hgp.sub hfp))

/-- The time derivative of the straight-line homotopy is `g x - f x`. -/
private theorem fderiv_lineHomotopy_apply_zero_one {p : E × ℝ} (hp : p.1 ∈ Ω) :
    fderiv ℝ (lineHomotopy f g) p (0, 1) = g p.1 - f p.1 := by
  rw [(hasFDerivAt_lineHomotopy hf hg hp).fderiv]
  simp

/-- At times `t ∈ [0, 1]`, the spatial derivative of the straight-line homotopy is the convex
combination `(1 - t) Df + t Dg`, so it inherits a common bound on `Df` and `Dg`. -/
private theorem norm_fderiv_lineHomotopy_comp_inl_le {p : E × ℝ} (hp : p.1 ∈ Ω)
    (ht : p.2 ∈ Icc (0 : ℝ) 1) {L : ℝ} (hfL : ‖fderiv ℝ f p.1‖ ≤ L) (hgL : ‖fderiv ℝ g p.1‖ ≤ L) :
    ‖(fderiv ℝ (lineHomotopy f g) p).comp (.inl ℝ E ℝ)‖ ≤ L := by
  have heq : (fderiv ℝ (lineHomotopy f g) p).comp (.inl ℝ E ℝ) =
      (1 - p.2) • fderiv ℝ f p.1 + p.2 • fderiv ℝ g p.1 := by
    rw [(hasFDerivAt_lineHomotopy hf hg hp).fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply,
      _root_.smul_apply, _root_.sub_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_snd', zero_smul, add_zero]
    module
  rw [heq]
  calc ‖(1 - p.2) • fderiv ℝ f p.1 + p.2 • fderiv ℝ g p.1‖
      ≤ (1 - p.2) * ‖fderiv ℝ f p.1‖ + p.2 * ‖fderiv ℝ g p.1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ht.2),
          Real.norm_of_nonneg ht.1]
    _ ≤ (1 - p.2) * L + p.2 * L := by
        gcongr
        exacts [sub_nonneg.2 ht.2, ht.1]
    _ = L := by ring

private theorem contDiffAt_graphHomotopy {p : E × ℝ} (hp : p.1 ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) (graphHomotopy f g) p :=
  contDiffAt_fst.prodMk (contDiffAt_lineHomotopy hf hg hp)

private theorem fderiv_graphHomotopy {p : E × ℝ} (hp : p.1 ∈ Ω) :
    fderiv ℝ (graphHomotopy f g) p =
      (ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ (lineHomotopy f g) p) :=
  (hasFDerivAt_fst.prodMk ((contDiffAt_lineHomotopy hf hg hp).differentiableAt
    (by simp)).hasFDerivAt).fderiv

/-- The graph of the straight-line homotopy is proper from `Ω × [0, 1]` to `Ω × E'`. -/
private theorem isCompact_inter_preimage_graphHomotopy (K : Set (E × E')) (hK : IsCompact K)
    (hKΩ : K ⊆ graphDomain Ω E') :
    IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ graphHomotopy f g ⁻¹' K) := by
  set C := (Prod.fst '' K) ×ˢ Icc (0 : ℝ) 1
  have hC : IsCompact C := (hK.image continuous_fst).prod isCompact_Icc
  have hCΩ : C ⊆ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono (fun _ ⟨q, hq, hqx⟩ ↦ hqx ▸ mem_graphDomain.1 (hKΩ hq)) subset_rfl
  have heq : ((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ graphHomotopy f g ⁻¹' K =
      C ∩ graphHomotopy f g ⁻¹' K := by
    refine Subset.antisymm (fun p hp ↦ ⟨⟨⟨_, hp.2, rfl⟩, hp.1.2⟩, hp.2⟩)
      fun p hp ↦ ⟨hCΩ hp.1, hp.2⟩
  have hcont : ContinuousOn (graphHomotopy f g) C := fun p hp ↦
    (contDiffAt_graphHomotopy hf hg (hCΩ hp).1).continuousAt.continuousWithinAt
  rw [heq]
  exact hC.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed hC.isClosed hK.isClosed)
    inter_subset_left

omit hf hg in
/-- At a point of the graph, the cut-off pullback of `η` along the projection `E × E' → E'`,
pulled back along the graph of the homotopy, is the cut-off pullback of `η` along the homotopy. -/
private theorem cutoffPullbackCLM_snd_compContinuousLinearMap
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ψ : 𝓓(graphDomain Ω E', ℝ)} (η : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) (y : E × E')
    (A : X →L[ℝ] E × E') :
    (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd η y).compContinuousLinearMap A =
      ψ y • (η y.2).compContinuousLinearMap ((ContinuousLinearMap.snd ℝ E E').comp A) := by
  rw [cutoffPullbackCLM_apply, fderiv_snd]
  ext v
  simp [Function.comp_def]

variable [CompleteSpace F]

/-- The homotopy operator of the graph of the straight-line homotopy, applied to the cut-off
pullback of `η` along the projection to `E'`, is bounded at `x` by `‖η‖ ‖g x - f x‖ L ^ m` when
`Df` and `Dg` are bounded by `L` at `x`. -/
private theorem norm_homotopyPullbackCLM_cutoffPullbackCLM_snd_le
    {ψ : 𝓓(graphDomain Ω E', ℝ)} (hψ : ∀ y, ψ y ∈ Icc (0 : ℝ) 1)
    (η : 𝓓(Ω', E' [⋀^Fin (m + 1)]→L[ℝ] F)) {x : E} (hx : x ∈ Ω) {ε L : ℝ}
    (hε : ‖g x - f x‖ ≤ ε) (hfL : ‖fderiv ℝ f x‖ ≤ L) (hgL : ‖fderiv ℝ g x‖ ≤ L) :
    ‖homotopyPullbackCLM (H := graphHomotopy f g)
        (fun _ hp ↦ contDiffAt_graphHomotopy hf hg hp.1)
        (isCompact_inter_preimage_graphHomotopy hf hg)
        (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd η) x‖ ≤
      ‖(η : E' →ᵇ E' [⋀^Fin (m + 1)]→L[ℝ] F)‖ * ε * L ^ m := by
  rw [homotopyPullbackCLM_apply_of_mem _ hx, TauCeti.cylinderHomotopy_apply]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := ‖(η : E' →ᵇ E' [⋀^Fin (m + 1)]→L[ℝ] F)‖ * ε * L ^ m) fun t ht ↦ ?_).trans_eq
    (by simp)
  rw [uIoc_of_le zero_le_one] at ht
  have hp : ((x, t) : E × ℝ).1 ∈ Ω := hx
  rw [cutoffPullbackCLM_snd_compContinuousLinearMap, fderiv_graphHomotopy hf hg hp,
    ContinuousLinearMap.snd_comp_prod]
  -- Pull the scalar cutoff out of the contraction.
  set A := fderiv ℝ (lineHomotopy f g) (x, t)
  set c := ψ (graphHomotopy f g (x, t))
  set α := η (graphHomotopy f g (x, t)).2
  have hc : ((c • α.compContinuousLinearMap A).curryLeft (0, 1)).compContinuousLinearMap
      (.inl ℝ E ℝ) =
        c • ((α.compContinuousLinearMap A).curryLeft (0, 1)).compContinuousLinearMap
          (.inl ℝ E ℝ) := by
    ext v
    simp
  have hcon :=
    ContinuousAlternatingMap.norm_curryLeft_compContinuousLinearMap_compContinuousLinearMap_le
      α A (0, 1) (.inl ℝ E ℝ)
  rw [hc, norm_smul, Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left hcon (abs_nonneg _)).trans ?_
  rw [fderiv_lineHomotopy_apply_zero_one hf hg hp]
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hψ1 : |ψ (graphHomotopy f g (x, t))| ≤ 1 :=
    abs_le.2 ⟨by linarith [(hψ (graphHomotopy f g (x, t))).1], (hψ (graphHomotopy f g (x, t))).2⟩
  have hη : ‖η (graphHomotopy f g (x, t)).2‖ ≤ ‖(η : E' →ᵇ E' [⋀^Fin (m + 1)]→L[ℝ] F)‖ :=
    BoundedContinuousFunction.norm_coe_le_norm (η : E' →ᵇ E' [⋀^Fin (m + 1)]→L[ℝ] F) _
  have hA := norm_fderiv_lineHomotopy_comp_inl_le hf hg hp (Ioc_subset_Icc_self ht) hfL hgL
  calc |ψ (graphHomotopy f g (x, t))| * (‖η (graphHomotopy f g (x, t)).2‖ * ‖g x - f x‖ *
        ‖(fderiv ℝ (lineHomotopy f g) (x, t)).comp (.inl ℝ E ℝ)‖ ^ m)
      ≤ 1 * (‖(η : E' →ᵇ E' [⋀^Fin (m + 1)]→L[ℝ] F)‖ * ε * L ^ m) :=
        mul_le_mul hψ1 (mul_le_mul (mul_le_mul hη hε (norm_nonneg _) (norm_nonneg _))
          (pow_le_pow_left₀ (norm_nonneg _) hA m) (by positivity)
          (mul_nonneg (norm_nonneg _) hε0)) (by positivity) zero_le_one
    _ = _ := one_mul _

omit hf hg [CompleteSpace F] in
/-- On a slice `x ↦ (x, φ x)` of the graph of the homotopy, the pullback of the cut-off pullback
of `η` along the projection to `E'` is the cut-off pullback of `η` along `φ`. -/
private theorem pullbackCLM_graphHomotopy_cutoffPullbackCLM_snd_apply {t : ℝ} {φ : E → E'}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω) (hgraph : ∀ x, lineHomotopy f g (x, t) = φ x)
    {ht : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ graphHomotopy f g (x, t)) Ω}
    {htp : ∀ K : Set (E × E'), IsCompact K → K ⊆ graphDomain Ω E' →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ graphHomotopy f g (x, t)) ⁻¹' K)}
    (ψ : 𝓓(graphDomain Ω E', ℝ)) (η : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {x : E} (hx : x ∈ Ω) :
    pullbackCLM (fun x ↦ graphHomotopy f g (x, t)) ht htp
        (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd η) x =
      ψ (x, φ x) • (η (φ x)).compContinuousLinearMap (fderiv ℝ φ x) := by
  have hfun : (fun x ↦ graphHomotopy f g (x, t)) = fun x ↦ (x, φ x) :=
    funext fun x ↦ by simp [graphHomotopy, hgraph]
  have hd : HasFDerivAt (fun y ↦ (y, φ y)) ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ φ x)) x :=
    (hasFDerivAt_id x).prodMk
      ((hφ.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hpt : graphHomotopy f g (x, t) = (x, φ x) := congrFun hfun x
  rw [pullbackCLM_apply_of_mem _ hx, hfun, cutoffPullbackCLM_snd_compContinuousLinearMap, hpt,
    hd.fderiv, ContinuousLinearMap.snd_comp_prod]

end Homotopy

section Estimate

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [CompleteSpace F]

variable (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
include hf hg

/-- Over a compact subset `K` of `Ω`, there is a cutoff on `Ω × E'` with values in `[0, 1]`
which is equal to one near the graph of the straight-line homotopy over `K × [0, 1]`. -/
private theorem exists_cutoff_graphHomotopy {K : Set E} (hKc : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ψ : 𝓓(graphDomain Ω E', ℝ), (∀ y, ψ y ∈ Icc (0 : ℝ) 1) ∧
      ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ y in 𝓝 (graphHomotopy f g (x, t)), ψ y = 1 := by
  set S := graphHomotopy f g '' (K ×ˢ Icc (0 : ℝ) 1)
  have hS : IsCompact S := (hKc.prod isCompact_Icc).image_of_continuousOn fun p hp ↦
    (contDiffAt_graphHomotopy hf hg (hKΩ hp.1)).continuousAt.continuousWithinAt
  have hSΩ : S ⊆ graphDomain Ω E' := by
    rintro _ ⟨p, hp, rfl⟩
    exact hKΩ hp.1
  obtain ⟨ψ, hψ1, hψ01⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hS hSΩ
  exact ⟨ψ, hψ01, fun x hx t ht ↦
    hψ1.filter_mono (nhds_le_nhdsSet (s := S) (mem_image_of_mem _ ⟨hx, ht⟩))⟩

omit [FiniteDimensional ℝ E'] [CompleteSpace F] in
/-- If the cutoff `ψ` is equal to one near the graph of the homotopy over the support of a current
`T`, then `T` takes the same value on the end slice `x ↦ (x, φ x)` of the cut-off pullback of `ω`
as on the pushforward test `χ φ^* ω`. -/
private theorem map_pullbackCLM_graphHomotopy_eq (T : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] ℝ)
    {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {ψ : 𝓓(graphDomain Ω E', ℝ)}
    (hψ : ∀ x ∈ dsupport T, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ᶠ y in 𝓝 (graphHomotopy f g (x, t)), ψ y = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {φ : E → E'} (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω)
    (hgraph : ∀ x, lineHomotopy f g (x, t) = φ x)
    {h₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ graphHomotopy f g (x, t)) Ω}
    {h₂ : ∀ K : Set (E × E'), IsCompact K → K ⊆ graphDomain Ω E' →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ graphHomotopy f g (x, t)) ⁻¹' K)}
    (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
    T (pullbackCLM (fun x ↦ graphHomotopy f g (x, t)) h₁ h₂
        (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd ω)) =
      T (cutoffPullbackCLM χ φ hφ ω) := by
  have hKΩ := (isCompact_dsupport_and_subset_of_eventually_eq_one hχ).2
  -- Near the support, `ψ` is equal to one along the slice.
  have hψev : ∀ᶠ x in 𝓝ˢ (dsupport T), ψ (graphHomotopy f g (x, t)) = 1 := by
    rw [eventually_nhdsSet_iff_forall]
    intro x hx
    have hc : ContinuousAt (fun x ↦ graphHomotopy f g (x, t)) x :=
      ContinuousAt.comp (f := fun y : E ↦ (y, t))
        (contDiffAt_graphHomotopy hf hg (p := (x, t)) (hKΩ hx)).continuousAt
        (continuous_id.prodMk continuous_const).continuousAt
    exact hc.tendsto.eventually (hψ x hx t ht)
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ, hψev, Ω.isOpen.mem_nhdsSet.2 hKΩ] with x hχx hψx hxΩ
  rw [pullbackCLM_graphHomotopy_cutoffPullbackCLM_snd_apply hφ hgraph ψ ω hxΩ,
    cutoffPullbackCLM_apply, hχx]
  simp only [graphHomotopy, hgraph] at hψx
  rw [hψx]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Near the graph of the homotopy over a point `x` where the cutoff `ψ` is one, the homotopy
operator of `d ω'`, for the cut-off pullback `ω'` of `ω`, is bounded by `‖dω‖ ‖g x - f x‖ L ^ m`. -/
private theorem norm_homotopyPullbackCLM_extDerivCLM_le {ψ : 𝓓(graphDomain Ω E', ℝ)}
    (hψ01 : ∀ y, ψ y ∈ Icc (0 : ℝ) 1) {x : E} (hx : x ∈ Ω)
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ y in 𝓝 (graphHomotopy f g (x, t)), ψ y = 1)
    (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {ε L : ℝ} (hε : ‖g x - f x‖ ≤ ε)
    (hfL : ‖fderiv ℝ f x‖ ≤ L) (hgL : ‖fderiv ℝ g x‖ ≤ L) :
    ‖homotopyPullbackCLM (H := graphHomotopy f g)
        (fun _ hp ↦ contDiffAt_graphHomotopy hf hg hp.1)
        (isCompact_inter_preimage_graphHomotopy hf hg)
        (extDerivCLM (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd ω)) x‖ ≤
      ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (m + 1)]→L[ℝ] F)‖ * ε * L ^ m := by
  have heq : homotopyPullbackCLM (H := graphHomotopy f g)
        (fun _ hp ↦ contDiffAt_graphHomotopy hf hg hp.1)
        (isCompact_inter_preimage_graphHomotopy hf hg)
        (extDerivCLM (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd ω)) x =
      homotopyPullbackCLM (H := graphHomotopy f g)
        (fun _ hp ↦ contDiffAt_graphHomotopy hf hg hp.1)
        (isCompact_inter_preimage_graphHomotopy hf hg)
        (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd (extDerivCLM ω)) x := by
    rw [homotopyPullbackCLM_apply_of_mem _ hx, homotopyPullbackCLM_apply_of_mem _ hx]
    refine TauCeti.cylinderHomotopy_congr fun t ht ↦ ?_
    simp only [extDerivCLM_cutoffPullbackCLM_apply ω (hψ t ht)]
  rw [heq]
  exact norm_homotopyPullbackCLM_cutoffPullbackCLM_snd_le hf hg hψ01 _ hx hε hfL hgL

omit hf hg

/-- **The homotopy estimate for pushforwards**: let `T` be a normal `(k + 1)`-current whose
support is a compact subset of `Ω`, and let `f` and `g` be smooth on `Ω`. If `‖g - f‖ ≤ ε` and
`‖Df‖, ‖Dg‖ ≤ L` on the support of `T`, then the pushforwards `T ∘ (χ f^*)` and `T ∘ (χ g^*)`
satisfy

`|g_# T (ω) - f_# T (ω)| ≤ ε (L ^ (k + 1) M(T) sup ‖dω‖ + L ^ k M(∂T) sup ‖ω‖)`.

The difference is `T` applied to the homotopy operator of `dω` plus `∂T` applied to the homotopy
operator of `ω`, for the straight-line homotopy `(1 - t) f + t g`. Only the values of the maps and
of their derivatives on the support of `T` enter. -/
theorem norm_map_cutoffPullbackCLM_sub_le {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {ε L : ℝ≥0}
    (hε : ∀ x ∈ dsupport T, ‖g x - f x‖ ≤ ε) (hfL : ∀ x ∈ dsupport T, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ dsupport T, ‖fderiv ℝ g x‖ ≤ L) (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) :
    ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ ≤
      ε * (L ^ (k + 1) * (mass T).toReal *
          ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (k + 1 + 1)]→L[ℝ] F)‖ +
        L ^ k * (mass (T ∘L extDerivCLM)).toReal *
          ‖(ω : E' →ᵇ E' [⋀^Fin (k + 1)]→L[ℝ] F)‖) := by
  borelize E
  obtain ⟨hKc, hKΩ⟩ := isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨ψ, hψ01, hψ⟩ := exists_cutoff_graphHomotopy hf hg hKc hKΩ
  -- The homotopy formula for the graph of the straight-line homotopy, evaluated on the cut-off
  -- pullback `ω'` of `ω` to `Ω × E'`; its end slices are the pushforwards along `g` and `f`.
  set ω' := (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd ω :
    𝓓(graphDomain Ω E', (E × E') [⋀^Fin (k + 1)]→L[ℝ] F))
  have hG : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) (graphHomotopy f g) p :=
    fun _ hp ↦ contDiffAt_graphHomotopy hf hg hp.1
  have hGp := isCompact_inter_preimage_graphHomotopy (Ω := Ω) hf hg
  have hform := congr($(ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM
    (hH := hG) (hHp := hGp) T) ω')
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply] at hform
  rw [map_pullbackCLM_graphHomotopy_eq hf hg T hχ hψ ⟨zero_le_one, le_rfl⟩ hg
      (fun x ↦ by simp [lineHomotopy]),
    map_pullbackCLM_graphHomotopy_eq hf hg T hχ hψ ⟨le_rfl, zero_le_one⟩ hf
      (fun x ↦ by simp [lineHomotopy])] at hform
  rw [show T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω) =
      T (homotopyPullbackCLM hG hGp (extDerivCLM ω')) +
        (T ∘L extDerivCLM) (homotopyPullbackCLM hG hGp ω') by
    rw [ContinuousLinearMap.comp_apply, hform]; abel]
  refine (norm_add_le _ _).trans ?_
  rw [mul_add]
  gcongr
  · calc _ ≤ (‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (k + 1 + 1)]→L[ℝ] F)‖ * ε * L ^ (k + 1)) *
          (mass T).toReal :=
          norm_apply_le_mul_toReal_mass_of_forall_mem_dsupport hT.mass_ne_top (by positivity)
            fun x hx ↦ norm_homotopyPullbackCLM_extDerivCLM_le hf hg hψ01 (hKΩ hx) (hψ x hx) ω
              (hε x hx) (hfL x hx) (hgL x hx)
      _ = _ := by ring
  · calc _ ≤ (‖(ω : E' →ᵇ E' [⋀^Fin (k + 1)]→L[ℝ] F)‖ * ε * L ^ k) *
          (mass (T ∘L extDerivCLM)).toReal := by
          refine norm_apply_le_mul_toReal_mass_of_forall_mem_dsupport
            hT.comp_extDerivCLM.mass_ne_top (by positivity) fun x hx ↦ ?_
          have hx' : x ∈ dsupport T := dsupport_comp_extDerivCLM_subset T hx
          exact norm_homotopyPullbackCLM_cutoffPullbackCLM_snd_le hf hg hψ01 _ (hKΩ hx')
            (hε x hx') (hfL x hx') (hgL x hx')
      _ = _ := by ring

/-- **The homotopy estimate for pushforwards in degree zero**: let `T` be a `0`-current of finite
mass whose support is a compact subset of `Ω`, and let `f` and `g` be smooth on `Ω`. If
`‖g - f‖ ≤ ε` on the support of `T`, then the pushforwards satisfy
`|g_# T (ω) - f_# T (ω)| ≤ ε M(T) sup ‖dω‖`. No derivative bound is needed. -/
theorem norm_map_cutoffPullbackCLM_sub_le_finZero {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : mass T ≠ ⊤) {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {ε : ℝ≥0}
    (hε : ∀ x ∈ dsupport T, ‖g x - f x‖ ≤ ε) (ω : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F)) :
    ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ ≤
      ε * (mass T).toReal * ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (0 + 1)]→L[ℝ] F)‖ := by
  borelize E
  obtain ⟨hKc, hKΩ⟩ := isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨ψ, hψ01, hψ⟩ := exists_cutoff_graphHomotopy hf hg hKc hKΩ
  set ω' := (cutoffPullbackCLM ψ Prod.snd contDiffOn_snd ω :
    𝓓(graphDomain Ω E', (E × E') [⋀^Fin 0]→L[ℝ] F))
  have hG : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) (graphHomotopy f g) p :=
    fun _ hp ↦ contDiffAt_graphHomotopy hf hg hp.1
  have hGp := isCompact_inter_preimage_graphHomotopy (Ω := Ω) hf hg
  have hform := congr($(ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM_finZero
    (hH := hG) (hHp := hGp) T) ω')
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply] at hform
  rw [map_pullbackCLM_graphHomotopy_eq hf hg T hχ hψ ⟨zero_le_one, le_rfl⟩ hg
      (fun x ↦ by simp [lineHomotopy]),
    map_pullbackCLM_graphHomotopy_eq hf hg T hχ hψ ⟨le_rfl, zero_le_one⟩ hf
      (fun x ↦ by simp [lineHomotopy])] at hform
  rw [← hform]
  -- No derivative bound enters in degree zero: any common bound `L` gives the factor `L ^ 0`.
  calc _ ≤ (‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (0 + 1)]→L[ℝ] F)‖ * ε) * (mass T).toReal :=
        norm_apply_le_mul_toReal_mass_of_forall_mem_dsupport hT (by positivity) fun x hx ↦
          (norm_homotopyPullbackCLM_extDerivCLM_le hf hg hψ01 (hKΩ hx) (hψ x hx) ω (hε x hx)
            (le_max_left _ _) (le_max_right _ _)).trans_eq (by rw [pow_zero, mul_one])
    _ = _ := by ring

end Estimate

section Pushforward

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [CompleteSpace F]
  {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ}

omit [FiniteDimensional ℝ E'] [CompleteSpace F] in
/-- **The mass of a pushforward, bounded on the support**: if `χ` is one near the support of `T`
and `‖DΦ‖ ≤ L` at the points of the support, then `M(T ∘ (χ Φ^*)) ≤ L ^ k M(T)`. -/
theorem mass_comp_cutoffPullbackCLM_le_of_forall_mem_dsupport (hT : HasLocallyFiniteMass T)
    {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} {L : ℝ≥0} (hL : ∀ x ∈ dsupport T, ‖fderiv ℝ Φ x‖ ≤ L) :
    mass (T ∘L (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ≤
      L ^ k * mass T := by
  borelize E
  refine mass_le_iff.2 fun ω hω ↦ ?_
  rw [ContinuousLinearMap.comp_apply]
  refine enorm_apply_le_mul_mass_of_forall_mem_dsupport hT fun x hx ↦ ?_
  have h := norm_cutoffPullbackCLM_apply_le (χ := χ) (hΦ := hΦ) ω x
  rw [hχ.self_of_nhdsSet x hx, abs_one, one_mul] at h
  rw [← ENNReal.coe_pow, eNorm_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_pow]
  calc _ ≤ ‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k := h
    _ ≤ 1 * (L : ℝ) ^ k := by
        gcongr
        exacts [hω _, hL x hx]
    _ = (L : ℝ) ^ k := one_mul _

/-- The homotopy estimate in every degree: the difference of two pushforwards of a normal
current is bounded by `ε C`, where `ε` bounds the distance of the maps on the support and `C`
depends only on `T`, `ω` and a common bound for the derivatives on the support. -/
private theorem exists_norm_map_cutoffPullbackCLM_sub_le (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (L : ℝ≥0)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : E → E') (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
      (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (ε : ℝ≥0), (∀ x ∈ dsupport T, ‖g x - f x‖ ≤ ε) →
      (∀ x ∈ dsupport T, ‖fderiv ℝ f x‖ ≤ L) → (∀ x ∈ dsupport T, ‖fderiv ℝ g x‖ ≤ L) →
      ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ ≤ ε * C := by
  cases k with
  | zero =>
    exact ⟨(mass T).toReal * ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (0 + 1)]→L[ℝ] F)‖,
      by positivity, fun f g hf hg ε hε _ _ ↦
        (norm_map_cutoffPullbackCLM_sub_le_finZero hT.mass_ne_top hχ hf hg hε ω).trans_eq (by ring)⟩
  | succ k =>
    exact ⟨_, by positivity, fun f g hf hg ε hε hfL hgL ↦
      norm_map_cutoffPullbackCLM_sub_le hT hχ hf hg hε hfL hgL ω⟩

/-- Pushforwards along two sequences of smooth maps with bounded derivatives, converging
uniformly on the support to the same map, have the same asymptotic values. -/
private theorem tendsto_map_cutoffPullbackCLM_sub (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g g' : ℕ → E → E'}
    (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hg' : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g' j) Ω)
    (hgf : TendstoUniformlyOn g f atTop (dsupport T))
    (hg'f : TendstoUniformlyOn g' f atTop (dsupport T)) {L : ℝ≥0}
    (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L)
    (hg'L : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g' j) x‖ ≤ L)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω) -
      T (cutoffPullbackCLM χ (g' j) (hg' j) ω)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_map_cutoffPullbackCLM_sub_le hT hχ L ω
  refine Metric.tendsto_atTop.2 fun e he ↦ ?_
  have hδ : 0 < e / (C + 1) := by positivity
  set ε : ℝ≥0 := ⟨e / (C + 1), hδ.le⟩
  have hε : (ε : ℝ) = e / (C + 1) := rfl
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (hgf.sub hg'f) _ hδ)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [dist_zero_right]
  have hgg' (x : E) (hx : x ∈ dsupport T) : ‖g j x - g' j x‖ ≤ ε := by
    simpa [hε, dist_eq_norm, norm_sub_rev] using (hN j hj x hx).le
  calc _ ≤ ε * C := hC (g' j) (g j) (hg' j) (hg j) _ hgg' (hg'L j) (hgL j)
    _ < e := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- Pushforwards along a sequence of smooth maps with bounded derivatives, converging uniformly on
the support, form a Cauchy sequence on each test form. -/
private theorem cauchySeq_map_cutoffPullbackCLM (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : ℕ → E → E'}
    (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hgf : TendstoUniformlyOn g f atTop (dsupport T))
    {L : ℝ≥0} (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    CauchySeq fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_map_cutoffPullbackCLM_sub_le hT hχ L ω
  refine Metric.cauchySeq_iff'.2 fun e he ↦ ?_
  have hδ : 0 < e / (C + 1) := by positivity
  set ε : ℝ≥0 := ⟨e / (C + 1), hδ.le⟩
  have hε : (ε : ℝ) = e / (C + 1) := rfl
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.1 hgf _ (half_pos hδ))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnN : ∀ x ∈ dsupport T, ‖g n x - g N x‖ ≤ ε := by
    intro x hx
    rw [hε, ← dist_eq_norm]
    linarith [dist_triangle_left (g n x) (g N x) (f x), hN n hn x hx, hN N le_rfl x hx]
  rw [dist_eq_norm]
  calc _ ≤ ε * C := hC (g N) (g n) (hg N) (hg n) _ hnN (hgL N) (hgL n)
    _ < e := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- Given one sequence of smooth approximations of `f` on the support of `T`, there is a single
current which is the weak limit of the pushforwards along every such sequence. -/
private theorem exists_forall_tendsto_map_cutoffPullbackCLM (hT : IsNormal T) {χ₀ : 𝓓(Ω, ℝ)}
    (hχ₀ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ₀ x = 1) {g₀ : ℕ → E → E'}
    (hg₀ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g₀ j) Ω) (hg₀f : TendstoUniformlyOn g₀ f atTop (dsupport T))
    {L₀ : ℝ≥0} (hg₀L : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g₀ j) x‖ ≤ L₀) :
    ∃ S : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ, ∀ χ : 𝓓(Ω, ℝ),
      (∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) → ∀ (g : ℕ → E → E')
      (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω), TendstoUniformlyOn g f atTop (dsupport T) →
      ∀ L : ℝ≥0, (∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L) → ∀ ω,
      Tendsto (fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω)) atTop (𝓝 (S ω)) := by
  have hTf := hasLocallyFiniteMass_of_mass_ne_top T hT.mass_ne_top
  obtain ⟨S, -, hS⟩ := exists_tendsto_of_mass_le
    (fun j ↦ T ∘L (cutoffPullbackCLM χ₀ (g₀ j) (hg₀ j) : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _))
    (C := L₀ ^ k * mass T) (ENNReal.mul_ne_top (by simp) hT.mass_ne_top)
    (fun j ↦ mass_comp_cutoffPullbackCLM_le_of_forall_mem_dsupport hTf hχ₀ (hg₀L j))
    (cauchySeq_map_cutoffPullbackCLM hT hχ₀ hg₀ hg₀f hg₀L)
  refine ⟨S, fun χ hχ g hg hgf L hgL ω ↦ ?_⟩
  -- Change the cutoff to `χ₀`, then compare with the sequence `g₀`.
  have hχχ₀ : (χ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₀ :=
    (hχ.and hχ₀).mono fun x h ↦ h.1.trans h.2.symm
  have hcut (j : ℕ) : T (cutoffPullbackCLM χ (g j) (hg j) ω) =
      T (cutoffPullbackCLM χ₀ (g j) (hg j) ω) :=
    congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_congr (hΦ := hg j) T hχχ₀) ω)
  simp_rw [hcut]
  have hdiff := tendsto_map_cutoffPullbackCLM_sub hT hχ₀ hg hg₀ hgf hg₀f (L := max L L₀)
    (fun j x hx ↦ (hgL j x hx).trans (le_max_left _ _))
    (fun j x hx ↦ (hg₀L j x hx).trans (le_max_right _ _)) ω
  simpa using hdiff.add (hS ω)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [CompleteSpace F] in
/-- `T` is normal with compact support in `Ω`, and `f` is the uniform limit on the support of maps
smooth on `Ω` whose derivatives are uniformly bounded on the support. -/
private def IsApproximable (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) (f : E → E') : Prop :=
  IsNormal T ∧ (∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) ∧
    ∃ g : ℕ → E → E', (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) ∧
      TendstoUniformlyOn g f atTop (dsupport T) ∧
      ∃ L : ℝ≥0, ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L

open Classical in
/-- The **pushforward `f_# T` of a normal current `T` along a Lipschitz map `f`**.

Let `T` be a normal current whose support is a compact subset of `Ω`. If `f` is the uniform limit
on the support of `T` of maps `gⱼ`, smooth on `Ω`, whose derivatives are uniformly bounded on the
support, then `f_# T` is the limit on each test form of the smooth pushforwards
`gⱼ# T = T ∘ (χ gⱼ^*)`, for any test function `χ` equal to one near the support
(`Distribution.tendsto_lipschitzPushforward`); the limit does not depend on the sequence. Such
sequences exist when `f` is Lipschitz on a neighbourhood of the support, and `f_# T` is the smooth
pushforward when `f` is smooth on `Ω`
(`Distribution.lipschitzPushforward_eq_comp_cutoffPullbackCLM`). If `T` is not normal with compact
support in `Ω`, or `f` has no such approximations, it is `0`. -/
def lipschitzPushforward (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) (f : E → E') :
    𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ :=
  if h : IsApproximable T f then
    Classical.choose (exists_forall_tendsto_map_cutoffPullbackCLM h.1 h.2.1.choose_spec
      h.2.2.choose_spec.1 h.2.2.choose_spec.2.1 h.2.2.choose_spec.2.2.choose_spec)
  else 0

/-- **The Lipschitz pushforward is the limit of smooth pushforwards**: if smooth maps `gⱼ` converge
to `f` uniformly on the support of a normal current `T`, with uniformly bounded derivatives there,
then `gⱼ# T (ω) → f_# T (ω)` for every test form `ω`, where `gⱼ# T = T ∘ (χ gⱼ^*)` for any test
function `χ` equal to one near the support. -/
theorem tendsto_lipschitzPushforward (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : ℕ → E → E'}
    (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hgf : TendstoUniformlyOn g f atTop (dsupport T))
    {L : ℝ≥0} (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω)) atTop
      (𝓝 (lipschitzPushforward T f ω)) := by
  have h : IsApproximable T f := ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩
  rw [lipschitzPushforward, dite_eq_left h]
  exact Classical.choose_spec (exists_forall_tendsto_map_cutoffPullbackCLM h.1 h.2.1.choose_spec
    h.2.2.choose_spec.1 h.2.2.choose_spec.2.1 h.2.2.choose_spec.2.2.choose_spec) χ hχ g hg hgf L
    hgL ω

omit [CompleteSpace F] in
/-- Smooth approximations of a map which is Lipschitz near the support, and a cutoff. -/
private theorem exists_cutoff_seq_contDiff (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) {U : Set E} {L : ℝ≥0} (hf : LipschitzOnWith L f U)
    (hU : U ∈ 𝓝ˢ (dsupport T)) :
    ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) ∧ ∃ g : ℕ → E → E',
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) ∧ TendstoUniformlyOn g f atTop (dsupport T) ∧
        ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hKc hKΩ
  obtain ⟨g, hg, hgf, hgL⟩ := hf.exists_seq_contDiff_tendstoUniformlyOn hKc hU
  exact ⟨χ, hχ, g, fun j ↦ (hg j).contDiffOn, hgf, hgL⟩

/-- **Agreement with the smooth pushforward**: along a map smooth on `Ω`, the pushforward of a
normal current with compact support in `Ω` is `T ∘ (χ f^*)`, for any `χ` equal to one near the
support. -/
theorem lipschitzPushforward_eq_comp_cutoffPullbackCLM (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
      T ∘L cutoffPullbackCLM χ f hf := by
  obtain ⟨hKc, hKΩ⟩ := isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).mono hKΩ)
  have hconst : TendstoUniformlyOn (fun _ : ℕ ↦ f) f atTop (dsupport T) :=
    Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ Eventually.of_forall fun _ x _ ↦ by
      simpa using hε
  ext ω
  exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ (fun _ ↦ hf) hconst
    (L := C.toNNReal) (fun _ x hx ↦ (hC x hx).trans (Real.le_coe_toNNReal C)) ω)
    tendsto_const_nhds

/-- **Locality**: the pushforward of `T` only depends on the values of the map on the support of
`T`. -/
theorem lipschitzPushforward_congr {f' : E → E'} (h : EqOn f f' (dsupport T)) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
      lipschitzPushforward T f' := by
  have key {f₁ f₂ : E → E'} (h₁₂ : EqOn f₁ f₂ (dsupport T)) (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
      (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : ℕ → E → E'}
      (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hgf : TendstoUniformlyOn g f₁ atTop (dsupport T))
      {L : ℝ≥0} (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L) :
      (lipschitzPushforward T f₁ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
        lipschitzPushforward T f₂ := by
    ext ω
    exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL ω)
      (tendsto_lipschitzPushforward hT hχ hg (hgf.congr_right h₁₂) hgL ω)
  by_cases hf : IsApproximable T f
  · obtain ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩ := hf
    exact key h hT hχ hg hgf hgL
  by_cases hf' : IsApproximable T f'
  · obtain ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩ := hf'
    exact (key h.symm hT hχ hg hgf hgL).symm
  rw [lipschitzPushforward, lipschitzPushforward, dite_eq_right hf, dite_eq_right hf']

variable {U : Set E} {L : ℝ≥0}

/-- **The mass of a Lipschitz pushforward**: if `f` is `L`-Lipschitz on a neighbourhood of the
support of a normal current `T` with compact support in `Ω`, then `M(f_# T) ≤ L ^ k M(T)`. -/
theorem mass_lipschitzPushforward_le (hT : IsNormal T) (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    mass (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) ≤ L ^ k * mass T := by
  obtain ⟨χ, hχ, g, hg, hgf, hgL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  have hTf := hasLocallyFiniteMass_of_mass_ne_top T hT.mass_ne_top
  exact (mass_le_liminf (fs := fun j ↦ ⇑(T ∘L (cutoffPullbackCLM χ (g j) (hg j) :
      𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)))
    (tendsto_lipschitzPushforward hT hχ hg hgf hgL)).trans
    (liminf_le_of_frequently_le' (Frequently.of_forall fun j ↦
      mass_comp_cutoffPullbackCLM_le_of_forall_mem_dsupport hTf hχ (hgL j)))

/-- **The pushforward commutes with the boundary**: `∂ (f_# T) = f_# (∂ T)` for a normal
`(k + 1)`-current `T` with compact support in `Ω` and a map `f` Lipschitz on a neighbourhood of
the support. -/
theorem lipschitzPushforward_comp_extDerivCLM {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsNormal T) (hKc : IsCompact (dsupport T)) (hKΩ : dsupport T ⊆ Ω)
    (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) ∘L extDerivCLM =
      lipschitzPushforward (T ∘L extDerivCLM) f := by
  obtain ⟨χ, hχ, g, hg, hgf, hgL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  have hsub : dsupport (T ∘L extDerivCLM) ⊆ dsupport T := dsupport_comp_extDerivCLM_subset T
  ext ω
  refine tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL (extDerivCLM ω)) ?_
  have h := tendsto_lipschitzPushforward hT.comp_extDerivCLM
    (hχ.filter_mono (nhdsSet_mono hsub)) hg (hgf.mono hsub) (fun j x hx ↦ hgL j x (hsub hx)) ω
  refine h.congr fun j ↦ ?_
  exact (congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_comp_extDerivCLM (hΦ := hg j) T hχ)
    ω)).symm

/-- **The support of a Lipschitz pushforward** lies in the image of the support:
`spt (f_# T) ⊆ f (spt T)`. -/
theorem dsupport_lipschitzPushforward_subset (hT : IsNormal T) (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    dsupport (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) ⊆
      f '' dsupport T := by
  obtain ⟨χ, hχ, g, hg, hgf, hgL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  have hfK : IsCompact (f '' dsupport T) :=
    hKc.image_of_continuousOn (hf.continuousOn.mono (subset_of_mem_nhdsSet hU))
  -- A test form supported off the compact image is eventually supported off every `gⱼ (spt T)`.
  have hvan : IsVanishingOn (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ)
      (f '' dsupport T)ᶜ := by
    intro ω hω
    obtain ⟨δ, hδ, hδω⟩ := hfK.exists_thickening_subset_open (isClosed_tsupport ω).isOpen_compl
      fun y hy hyω ↦ hω hyω hy
    have hzero : ∀ᶠ j in atTop, T (cutoffPullbackCLM χ (g j) (hg j) ω) = 0 := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 hgf δ hδ] with j hj
      refine map_eq_zero_of_disjoint_dsupport T (disjoint_left.2 fun x hx hxT ↦ ?_)
      have hgx : g j x ∈ Metric.thickening δ (f '' dsupport T) :=
        Metric.mem_thickening_iff.2 ⟨f x, mem_image_of_mem f hxT, by rw [dist_comm]; exact hj x hxT⟩
      exact hδω hgx (tsupport_cutoffPullbackCLM_subset ω hx).2
    exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL ω)
      (tendsto_const_nhds.congr' (hzero.mono fun _ h ↦ h.symm))
  have h := (hvan.disjoint_dsupport hfK.isClosed.isOpen_compl).subset_compl_left
  rwa [compl_compl] at h

/-- **Lipschitz pushforwards of normal currents are normal**, when the map is Lipschitz on a
neighbourhood of the compact support. -/
theorem isNormal_lipschitzPushforward (hT : IsNormal T) (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    IsNormal (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) := by
  have hfin {j : ℕ} {S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] ℝ} (hS : IsNormal S)
      (hSc : IsCompact (dsupport S)) (hSΩ : dsupport S ⊆ Ω) (hSU : U ∈ 𝓝ˢ (dsupport S)) :
      mass (lipschitzPushforward S f : 𝓓(Ω', E' [⋀^Fin j]→L[ℝ] F) →L[ℝ] ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hS.mass_ne_top)
      (mass_lipschitzPushforward_le hS hSc hSΩ hf hSU)
  cases k with
  | zero => exact isNormal_finZero_iff.2 (hfin hT hKc hKΩ hU)
  | succ k =>
    have hsub : dsupport (T ∘L extDerivCLM) ⊆ dsupport T := dsupport_comp_extDerivCLM_subset T
    refine isNormal_succ_iff.2 ⟨hfin hT hKc hKΩ hU, ?_⟩
    rw [lipschitzPushforward_comp_extDerivCLM hT hKc hKΩ hf hU]
    exact hfin hT.comp_extDerivCLM (hKc.of_isClosed_subset isClosed_dsupport hsub)
      (hsub.trans hKΩ) (nhdsSet_mono hsub hU)

end Pushforward

end Distribution
