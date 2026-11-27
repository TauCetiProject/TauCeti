/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Distribution.SchwartzSpace.Subsingleton
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Patching chart estimates for classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ` and `P` a classical pseudodifferential operator of order `m`
on `M` (`TauCeti.classicalPseudodifferentialOperators`). A complex-valued smooth function `u` on
`M` is read in a chart `e` of the maximal atlas through a cutoff `φ` with compact support in the
chart target as the Schwartz function `φ · (u ∘ e⁻¹)` on `ℝⁿ`
(`OpenPartialHomeomorph.cutoffPushforwardSchwartz`).

This file patches Euclidean mapping estimates for `P` into estimates on `M`, for an abstract
source norm `‖Ls ·‖` and target norm `‖Lt ·‖` on `𝓢(ℝⁿ, ℂ)`, given by linear maps `Ls` and `Lt`
into normed spaces. It assumes that

* `Ls` is injective;
* every localized change of variables `u ↦ θ · (u ∘ κ)` is bounded in `‖Ls ·‖`;
* for every symbol `a` of order `m` with compact spatial support, `‖Lt (Op(a) w)‖ ≤ A ‖Ls w‖`.

For `Ls = H^s` and `Lt = H^{s - m}` this gives the Sobolev estimates of
`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`, and
for `Ls = B^s_{p,∞}` and `Lt = B^{s - m}_{p,∞}` the Besov and Hölder–Zygmund estimates of
`TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`.

## The argument

The core is an estimate between two charts
(`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`): the reading through `φ` in a
chart `e` of `P (Ψ g)`, where `Ψ` is a cutoff `ψ` in a second chart `e'` read on `M`, is bounded
in `‖Lt ·‖` by the reading `ψ · (g ∘ e'⁻¹)` of `g` in `‖Ls ·‖`.

* A partition of unity `ρₖ` on `e'⁻¹(supp ψ)` splits `Ψ g` into pieces `ρₖ Ψ g`, where each `ρₖ`
  is supported in the source of a chart `Eₖ` agreeing with `e` over the support of `φ`
  (`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`). Such charts exist because the
  maximal atlas contains every chart, including charts whose domain is a disjoint union of two
  coordinate balls.
* In the chart `Eₖ`, the reading of `P (ρₖ Ψ g)` through `φ` is a chart compression of `P`
  applied to the reading `Wₖ` of `ρₖ Ψ g` in `Eₖ`. So it is `Op(aₖ) Wₖ` for a classical symbol
  `aₖ` of order `m` with compact spatial support, and `‖Lt (Op(aₖ) Wₖ)‖ ≤ A ‖Ls Wₖ‖`.
* The reading `Wₖ` in `Eₖ` is a localized change of variables of the reading
  `w = ψ · (g ∘ e'⁻¹)` in `e'`, so `‖Ls Wₖ‖ ≤ B ‖Ls w‖`
  (`TauCeti.exists_norm_cutoffPushforwardSchwartz_mulLeft_le`).

In dimension zero there are no symbol estimates to use, but then every complex-homogeneous map out
of `𝓢(ℝ⁰, ℂ)` is bounded by `‖Ls ·‖` (`SchwartzMap.exists_norm_le_of_subsingleton`). The estimate
for a partition `ψᵢ` follows by writing `u = ∑ᵢ Ψᵢ u`.

## Main results

* `TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`: the estimate between two
  charts.
* `TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_le_sum`: the reading of `P u` in one chart
  is bounded in `‖Lt ·‖` by the sum of the `‖Ls ·‖` norms of the readings of `u` through cutoffs
  adding up to `1` on a set outside which `P` does not look.
* `TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum`: the same for the sum of the
  readings of `P u` over finitely many charts.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1, Theorem 18.1.13 and Definition 18.1.20.
-/

public section

noncomputable section

open Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
  {X Y Gs Gt : Type*} [NormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [FunLike Gs 𝓢(CoordinateSpace n, ℂ) X] [FunLike Gt 𝓢(CoordinateSpace n, ℂ) Y]

/-- **One chart.** In a chart `E` that agrees with `e` over the support of `φ`, reading `P` from
`E` through a cutoff `χ` to `e` through `φ` is a chart compression of `P`, hence a quantization
`Op(a)` with `a` of compact spatial support, bounded from `‖Ls ·‖` to `‖Lt ·‖`. -/
private theorem exists_norm_cutoffPushforwardSchwartz_apply_complexCutoffPullback_le (Ls : Gs)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {E : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hE : E ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφE : tsupport φ ⊆ E.target)
    (hEe : EqOn E.symm e.symm (tsupport φ)) (χ : 𝓓(⟨E.target, E.open_target⟩, ℝ)) :
    ∃ A, 0 ≤ A ∧ ∀ w : 𝓢(CoordinateSpace n, ℂ),
      ‖Lt (e.cutoffPushforwardSchwartz he φ
          (P (E.complexCutoffPullback hE χ (ContMDiffMap.ofContDiff w (w.smooth ⊤)))))‖ ≤
        A * ‖Ls w‖ := by
  let φ' : 𝓓(⟨E.target, E.open_target⟩, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφE⟩
  -- `φ'` is `φ` as a test function on `E.target`; coercing the structure literal back to a
  -- function gives its first field.
  have hφ' : (φ' : CoordinateSpace n → ℝ) = φ := (rfl)
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 E hE φ' χ
  have ha' := hasCompactSpatialSupport_of_eq_complexChartCompression hE ha
  -- `Op(a) w` is the reading of `P (χ w ∘ E)` through `φ` in `e`, since `E⁻¹ = e⁻¹` on the
  -- support of `φ`.
  have hread (w : 𝓢(CoordinateSpace n, ℂ)) : Symbol.quantizeUniformCLM a.toSymbol ha'.isUniform w =
      e.cutoffPushforwardSchwartz he φ
        (P (E.complexCutoffPullback hE χ (ContMDiffMap.ofContDiff w (w.smooth ⊤)))) := by
    ext y
    rw [Symbol.quantizeUniformCLM_apply, ha, complexChartCompression_def, LinearMap.comp_apply,
      LinearMap.comp_apply, complexCutoffPushforward_congr hE he hφ' hEe,
      complexCutoffPushforward_apply, cutoffPushforwardSchwartz_apply]
  obtain ⟨A, hA⟩ := hq a.toSymbol ha'
  exact ⟨|A|, abs_nonneg A, fun w ↦ hread w ▸
    (hA w).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (norm_nonneg _))⟩

variable [NormedSpace ℂ X] [NormedSpace ℂ Y] [LinearMapClass Gs ℂ 𝓢(CoordinateSpace n, ℂ) X]
  [LinearMapClass Gt ℂ 𝓢(CoordinateSpace n, ℂ) Y]

/-- **The estimate between two charts in dimension zero.** There `Ψ g` is the pullback of its
reading `w = ψ · (g ∘ e'⁻¹)`, through a cutoff equal to `1` on the support of `ψ`, so the reading
of `P (Ψ g)` in `e` is homogeneous in `w`. -/
private theorem exists_norm_cutoffPushforwardSchwartz_le_of_dim_eq_zero (hn : n = 0) {Ls : Gs}
    (hLs : Function.Injective Ls) (Lt : Gt)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖Lt (e.cutoffPushforwardSchwartz he φ
          (P (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g)))‖ ≤
        C * ‖Ls (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e'.target, e'.open_target⟩) (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hcw (c : ℂ) (w : 𝓢(CoordinateSpace n, ℂ)) : ContMDiffMap.ofContDiff (c • w)
      ((c • w).smooth ⊤) = c • ContMDiffMap.ofContDiff w (w.smooth ⊤) := by
    ext
    simp
  have : Subsingleton (CoordinateSpace n) := by
    subst hn
    exact ⟨fun x y ↦ PiLp.ext fun i ↦ i.elim0⟩
  obtain ⟨C, hC⟩ := SchwartzMap.exists_norm_le_of_subsingleton hLs
    (T := fun w ↦ Lt (e.cutoffPushforwardSchwartz he φ
      (P (e'.complexCutoffPullback he' ψ₁ (ContMDiffMap.ofContDiff w (w.smooth ⊤))))))
    (fun c w ↦ by simp only [hcw, map_smul])
  refine ⟨C, fun g ↦ ?_⟩
  rw [mulLeft_ofReal_cutoffPullback_one_eq_complexCutoffPullback he'
    fun y hy ↦ hψ₁.self_of_nhdsSet y hy]
  exact hC _

/-- **The estimate between two charts.** Let `Ls` and `Lt` be linear maps out of `𝓢(ℝⁿ, ℂ)` into
normed spaces, with `Ls` injective, such that every localized change of variables is bounded in
`‖Ls ·‖` and `‖Lt (Op(a) w)‖ ≤ A ‖Ls w‖` for every symbol `a` of order `m` with compact spatial
support. Let `P` be a classical pseudodifferential operator of order `m`, `φ` a cutoff in a chart
`e` and `ψ` a cutoff in a chart `e'`, with `Ψ` the smooth function `ψ ∘ e'` on `M`, extended by
`0`. There is a constant `C` such that for every smooth `g` on `M`, the reading
`φ · (P (Ψ g) ∘ e⁻¹)` of `P (Ψ g)` in `e` satisfies

`‖Lt (φ · (P (Ψ g) ∘ e⁻¹))‖ ≤ C ‖Ls (ψ · (g ∘ e'⁻¹))‖`. -/
theorem exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    {Ls : Gs} (hLs : Function.Injective Ls)
    (hcov : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖Lt (e.cutoffPushforwardSchwartz he φ
          (P (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g)))‖ ≤
        C * ‖Ls (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  classical
  rcases eq_or_ne n 0 with hn | hn
  · exact exists_norm_cutoffPushforwardSchwartz_le_of_dim_eq_zero hn hLs Lt he he' φ ψ
  have : NeZero n := ⟨hn⟩
  -- A partition of unity `ρ k` on `e'⁻¹(supp ψ)`, with `ρ k` supported in the source of a chart
  -- `E k` agreeing with `e` over the support of `φ`; `ρ k` is the cutoff `τ k` read on `M`, and
  -- `χ k = 1` on the support of `τ k`.
  obtain ⟨ι, _, ρ, E, hρ1, hE⟩ :=
    (e'.isCompact_symm_image_tsupport ψ).exists_smoothPartition_mem_maximalAtlas_eqOn_symm
      he φ.hasCompactSupport.isCompact φ.tsupport_subset
  choose hEa hρc hρE hφE hEe using hE
  choose τ hτ using fun k ↦ (E k).exists_cutoffPullback_one_eq (hEa k) (hρc k) (hρE k)
  choose χ hχ using fun k ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(E k).target, (E k).open_target⟩) (n := ⊤) (τ k).hasCompactSupport.isCompact
    (τ k).tsupport_subset
  choose A hA0 hA using fun k ↦
    exists_norm_cutoffPushforwardSchwartz_apply_complexCutoffPullback_le Ls Lt hq he hP (hEa k) φ
      (hφE k) (hEe k) (χ k)
  choose B hB using fun k ↦
    exists_norm_cutoffPushforwardSchwartz_mulLeft_le Ls hcov (hEa k) he' (τ k) ψ
  refine ⟨∑ k, A k * B k, fun g ↦ ?_⟩
  set G := LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g with hGdef
  -- `G` is supported in `e'⁻¹(supp ψ)`, where the `ρ k` add up to `1`.
  have hG : G = ∑ k,
      LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ((E k).cutoffPullback (hEa k) (τ k) 1)) G := by
    simp only [hτ]
    refine ContMDiffMap.eq_sum_mulLeft_ofReal _ ρ (fun x hx ↦ ?_) hρ1
    refine tsupport_cutoffPullback_subset he' ψ 1 (subset_tsupport _ fun h ↦ hx ?_)
    simp [hGdef, h]
  rw [hG, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [mulLeft_ofReal_cutoffPullback_one_eq_complexCutoffPullback (hEa k)
    fun y hy ↦ (hχ k).1.self_of_nhdsSet y hy, mul_assoc]
  exact (hA k _).trans (mul_le_mul_of_nonneg_left (hB k g) (hA0 k))

/-- **The estimate in one chart.** Let `Ls`, `Lt` and `P` be as in
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`, `φ` a cutoff in a chart `e`, and
`K ⊆ M` a set such that `P f` and `P g` agree on `e⁻¹(supp φ)` whenever `f` and `g` agree on `K`.
Let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended
by `0`, add up to `1` on `K`. There is a constant `C` such that every smooth `u` on `M` satisfies

`‖Lt (φ · ((P u) ∘ e⁻¹))‖ ≤ C ∑ᵢ ‖Ls (ψᵢ · (u ∘ e'ᵢ⁻¹))‖`.

For `K = M` the agreement hypothesis is automatic, and such cutoffs exist on every compact manifold
(`IsCompact.exists_sum_cutoffPullback_eq_one`). For a properly supported `P`, a compact such `K`
exists (`TauCeti.IsProperlySupported.exists_isCompact_forall_eqOn`), so `M` need not be
compact. -/
theorem exists_norm_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    {Ls : Gs} (hLs : Function.Injective Ls)
    (hcov : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {K : Set M}
    (hPK : ∀ f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      EqOn f g K → EqOn (P f) (P g) (e.symm '' tsupport φ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x ∈ K, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖Lt (e.cutoffPushforwardSchwartz he φ (P u))‖ ≤
        C * ∑ i, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ := by
  choose C hC using fun i ↦
    exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le hP hLs hcov Lt hq he (he' i) φ (ψ i)
  refine ⟨∑ i, |C i|, fun u ↦ ?_⟩
  -- Since `u = ∑ᵢ Ψᵢ u` on `K`, the reading of `P u` is the sum of the readings of `P (Ψᵢ u)`,
  -- and each piece is estimated in the chart `e'ᵢ`.
  have hu : e.cutoffPushforwardSchwartz he φ (P u) = ∑ i, e.cutoffPushforwardSchwartz he φ (P
      (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ((e' i).cutoffPullback (he' i) (ψ i) 1)) u)) := by
    rw [← map_sum, ← map_sum]
    ext y
    rw [cutoffPushforwardSchwartz_apply, cutoffPushforwardSchwartz_apply]
    by_cases hy : y ∈ tsupport φ
    · refine congrArg _ (hPK _ _ (fun x hx ↦ ?_) (mem_image_of_mem _ hy))
      simp only [ContMDiffMap.coe_sum, Finset.sum_apply, LinearMap.mulLeft_apply,
        ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.ofReal_apply, ← Finset.sum_mul,
        ← Complex.ofReal_sum, hψ x hx, Complex.ofReal_one, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [hu, map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (hC i u).trans ?_)
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum
    (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i))) (norm_nonneg _)

/-- **Patching chart estimates on a manifold.** Let `Ls`, `Lt` and `P` be as in
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`, and `ψᵢ` finitely many cutoffs
in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`, which forces
`M` to be compact. For finitely many cutoffs `φⱼ` in charts `eⱼ` there is a constant `C` such that
every smooth `u` on `M` satisfies

`∑ⱼ ‖Lt (φⱼ · ((P u) ∘ eⱼ⁻¹))‖ ≤ C ∑ᵢ ‖Ls (ψᵢ · (u ∘ e'ᵢ⁻¹))‖`. -/
theorem exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    {Ls : Gs} (hLs : Function.Injective Ls)
    (hcov : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    {κ : Type*} [Fintype κ]
    {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j) (P u))‖ ≤
        C * ∑ i, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ := by
  choose C hC using fun j ↦
    exists_norm_cutoffPushforwardSchwartz_apply_le_sum hP hLs hcov Lt hq (he j) (φ j)
      (K := univ) (fun f g hfg ↦ DFunLike.coe_injective ((eqOn_univ f g).1 hfg) ▸ eqOn_refl _ _)
      he' ψ fun x _ ↦ hψ x
  exact ⟨∑ j, C j, fun u ↦ (Finset.sum_le_sum fun j _ ↦ hC j u).trans_eq (Finset.sum_mul ..).symm⟩

end TauCeti
