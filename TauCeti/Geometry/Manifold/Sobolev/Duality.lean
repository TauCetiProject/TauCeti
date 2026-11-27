/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
public import TauCeti.Geometry.Manifold.Sobolev.Completion
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Duality of the Sobolev spaces of a compact manifold

Let `M` be a manifold modelled on `ℝⁿ`, with finitely many cutoffs `ψᵢ` in charts `eᵢ` of the
maximal atlas, and let `μ` be a measure on `M` with a smooth positive density
(`TauCeti.HasSmoothPositiveDensity`), for instance a Riemannian volume. The Sobolev space `H^s(M)`
of the cutoffs (`TauCeti.chartSobolevSpace`) is the closure of the chart readings
`ψᵢ · (u ∘ eᵢ⁻¹)` of the smooth functions `u` in `⨁ᵢ H^s(ℝⁿ)`. This file shows that the `L²(μ)`
pairing of smooth functions

`⟨u, v⟩ = ∫ ⟪u, v⟫ dμ`

identifies `H^{-s}(M)` with the antidual of `H^s(M)`, for every real `s`, when the cutoffs read on
`M` add up to `1` and `μ` is finite. This is the duality through which the cokernel of an elliptic
operator `P : H^s(M) → H^{s - m}(M)` is described by the kernel of its formal adjoint on
`H^{m - s}(M)`.

* **Boundedness** (`TauCeti.exists_norm_integral_inner_le_mul_norm_chartReading`): for a finite
  measure `μ`, `|∫ ⟪u, v⟫ dμ| ≤ C ‖u‖_{H^{-s}} ‖v‖_{H^s}`. Split `⟪u, v⟫` with the partition
  `∑ᵢ ψᵢ ∘ eᵢ = 1`. In the chart `eᵢ`, where `μ` is `ρᵢ(y) dy`, the `i`-th piece is the Euclidean
  pairing `∫ ⟪ψᵢ · (u ∘ eᵢ⁻¹), ρᵢ θᵢ · (v ∘ eᵢ⁻¹)⟫ dy`, for a cutoff `θᵢ` equal to `1` on the
  support of `ψᵢ`. The Euclidean duality of `H^{-s}` and `H^s`
  (`SchwartzMap.norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm`) bounds it, and the
  reading of `v` through the cutoff `ρᵢ θᵢ` is controlled by the readings in the partition
  (`TauCeti.exists_norm_chartReading_le`).
* **The dual norm** (`TauCeti.exists_norm_chartReading_neg_le`): conversely, if
  `|∫ ⟪u, v⟫ dμ| ≤ K ‖v‖_{H^s}` for every smooth `v`, then `‖u‖_{H^{-s}} ≤ C K`. For a Schwartz
  function `b`, the pairing `∫ ⟪ψᵢ · (u ∘ eᵢ⁻¹), b⟫ dy` of the `i`-th reading of `u` is
  `∫ ⟪u, v_b⟫ dμ` for the smooth function `v_b = ((ψᵢ / ρᵢ) b) ∘ eᵢ` on `M`, extended by `0`, and
  `‖v_b‖_{H^s} ≤ C ‖b‖_{H^s}` since its readings in the charts `eⱼ` are localized changes of
  variables of `b`. The Euclidean dual characterization of the `H^{-s}` norm
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_neg_le_of_forall`) then bounds the reading. This
  half holds for every finite family of chart cutoffs and every measure with a smooth positive
  density.
* **The pairing** `TauCeti.chartSobolevPairing he hμ hψ s : H^{-s}(M) →L⋆[ℂ] (H^s(M))⋆` is the
  continuous extension of `(u, v) ↦ ∫ ⟪u, v⟫ dμ` from the smooth functions
  (`TauCeti.chartSobolevPairing_toChartSobolevSpace`), conjugate-linear in `u` and linear in `v`.
  It is built through the Hilbert space structure of `H^s(M)`: by boundedness, `v ↦ ∫ ⟪u, v⟫ dμ` is
  `⟪R u, ·⟫_{H^s}` for a Riesz representative `R u ∈ H^s(M)` with `‖R u‖_{H^s} ≤ C ‖u‖_{H^{-s}}`,
  `R` extends to a continuous linear map `H^{-s}(M) → H^s(M)`, and the pairing is
  `⟨x, y⟩ = ⟪R x, y⟫_{H^s}`.
* **Nondegeneracy.** By the dual norm estimate and density of the smooth functions, `‖x‖_{H^{-s}}`
  is at most a constant times `‖R x‖_{H^s}`, and `‖y‖_{H^s}` at most a constant times the
  `H^{-s}` norm of `R† y`, which represents `x ↦ ⟨x, y⟩`. Hence `|⟨x, y⟩| ≤ K ‖y‖` for all `y`
  forces `‖x‖_{H^{-s}} ≤ C K`
  (`TauCeti.exists_norm_le_of_forall_norm_chartSobolevPairing_le_left`), and symmetrically in `y`
  (`TauCeti.exists_norm_le_of_forall_norm_chartSobolevPairing_le_right`).
* **Duality** (`TauCeti.chartSobolevDualEquiv`): the pairing is an isomorphism of `H^{-s}(M)` onto
  the continuous dual of `H^s(M)`, conjugate-linear because the `L²` pairing is. Indeed `R` is
  bounded below, so its range is closed, and an element of `H^s(M)` orthogonal to the range is
  killed by `R†`, hence vanishes; so `R` is bijective, and the pairing is `R` followed by the Riesz
  isomorphism `H^s(M) ≃ (H^s(M))⋆`.

The equivalence need not be isometric: the norms of `H^s(M)` depend on the chart partition, and the
pairing on the density `μ`.

## Main results

* `TauCeti.exists_norm_integral_inner_le_mul_norm_chartReading`: the `L²(μ)` pairing is bounded on
  `H^{-s} × H^s`.
* `TauCeti.exists_norm_chartReading_neg_le`: the `H^{-s}` norm is controlled by the dual norm for
  the `L²(μ)` pairing.
* `TauCeti.chartSobolevPairing`: the pairing `H^{-s}(M) →L⋆[ℂ] (H^s(M))⋆`, with
  `TauCeti.chartSobolevPairing_toChartSobolevSpace` on smooth functions.
* `TauCeti.exists_norm_le_of_forall_norm_chartSobolevPairing_le_left`,
  `TauCeti.exists_norm_le_of_forall_norm_chartSobolevPairing_le_right`: the norms of `H^{-s}(M)`
  and `H^s(M)` are controlled by the dual norms for the pairing.
* `TauCeti.chartSobolevDualEquiv`: the isomorphism `H^{-s}(M) ≃ (H^s(M))⋆` it induces, with
  `TauCeti.chartSobolevPairing_chartSobolevDualEquiv_symm` representing a functional as a pairing.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds and the duality of `H^s(M)` and `H^{-s}(M)`).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the Euclidean duality of `H_s` and `H_{-s}`).
-/

public section

noncomputable section

open Set Filter MeasureTheory TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace InnerProductSpace
  ComplexConjugate

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] {μ : Measure M}

/-! ### Integrals in a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}

omit [ChartedSpace (CoordinateSpace n) M] [BorelSpace M] in
/-- Integrating in a chart: if `μ` reads in the chart `e` as `ρ(y) dy`, a continuous function `F`
on `M` vanishing outside `e⁻¹(supp φ)`, for a cutoff `φ` in the chart, integrates as a function
`G` on `ℝⁿ` that equals `ρ(y) F(e⁻¹ y)` on the chart target and vanishes off it. -/
private theorem integral_eq_integral_of_eq_mul {ρ : CoordinateSpace n → ℝ}
    (hρ : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {F : M → ℂ} (hF : Continuous F)
    (hFφ : ∀ x ∈ e.source, φ (e x) = 0 → F x = 0) (hF0 : ∀ x ∉ e.source, F x = 0)
    {G : CoordinateSpace n → ℂ} (hG : ∀ y ∈ e.target, G y = ρ y * F (e.symm y))
    (hG0 : ∀ y ∉ e.target, G y = 0) : ∫ x, F x ∂μ = ∫ y, G y := by
  have hts : tsupport F ⊆ e.symm '' tsupport φ := e.tsupport_subset_symm_image_tsupport φ hFφ hF0
  rw [hρ F hF ((e.isCompact_symm_image_tsupport φ).of_isClosed_subset (isClosed_tsupport F) hts)
    (hts.trans (image_subset_iff.2 fun y hy ↦ e.map_target (φ.tsupport_subset hy))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
  exact setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ (hG y hy).symm

variable (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
include he

omit [BorelSpace M] in
/-- **A piece of the pairing in a chart.** For a cutoff `ψ` in a chart `e`, read on `M` as `Ψ`,
there is a cutoff `τ` in the chart (the density of `μ` times a cutoff equal to `1` on the support
of `ψ`) such that `∫ Ψ ⟪u, v⟫ dμ` is the Euclidean pairing of the readings `ψ · (u ∘ e⁻¹)` and
`τ · (v ∘ e⁻¹)`, for all smooth `u` and `v`. -/
private theorem exists_integral_mul_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ τ : 𝓓(⟨e.target, e.open_target⟩, ℝ), ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, (e.cutoffPullback he ψ 1 x : ℂ) * ⟪u x, v x⟫_ℂ ∂μ =
        ∫ y, ⟪e.cutoffPushforwardSchwartz he ψ u y, e.cutoffPushforwardSchwartz he τ v y⟫_ℂ := by
  obtain ⟨ρ, hρ, -, hint⟩ := hasSmoothPositiveDensity_iff.1 hμ e he
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨τ, hτ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn (Ω := ⟨e.target, e.open_target⟩)
    hρ θ
  refine ⟨τ, fun u v ↦ integral_eq_integral_of_eq_mul hint ψ
    (F := fun x ↦ (e.cutoffPullback he ψ 1 x : ℂ) * ⟪u x, v x⟫_ℂ)
    ((Complex.continuous_ofReal.comp (e.cutoffPullback he ψ 1).contMDiff.continuous).mul
      (u.contMDiff.continuous.inner v.contMDiff.continuous)) (fun x hx hψ ↦ ?_) (fun x hx ↦ ?_)
    (fun y hy ↦ ?_) fun y hy ↦ ?_⟩
  · simp [cutoffPullback_one_apply_of_mem he _ hx, hψ]
  · simp [cutoffPullback_apply_of_notMem he _ _ hx]
  · -- On the target, `τ = ρ θ` and `θ = 1` wherever `ψ ≠ 0`.
    rw [cutoffPushforwardSchwartz_apply, cutoffPushforwardSchwartz_apply, hτ,
      cutoffPullback_one_apply_of_mem he _ (e.map_target hy), e.right_inv hy]
    dsimp only
    by_cases hψy : ψ y = 0
    · simp [hψy]
    rw [hθ.self_of_nhdsSet y (subset_tsupport _ hψy)]
    simp only [smul_eq_mul, mul_one, Complex.real_smul, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal]
    ring
  · rw [cutoffPushforwardSchwartz_apply,
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (ψ.tsupport_subset h), zero_smul, inner_zero_left]

omit [BorelSpace M] in
/-- **A reading paired with a Schwartz function, on `M`.** For a cutoff `ψ` in a chart `e`, there is
a cutoff `σ` in the chart (`ψ` divided by the density of `μ`) such that the Euclidean pairing of the
reading `ψ · (u ∘ e⁻¹)` of a smooth `u` with a smooth `f` on `ℝⁿ` is the pairing `∫ ⟪u, v⟫ dμ` with
the smooth function `v = (σ f) ∘ e` on `M`, extended by `0`. -/
private theorem exists_integral_inner_complexCutoffPullback_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ σ : 𝓓(⟨e.target, e.open_target⟩, ℝ),
      ∀ (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
        (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯),
        ∫ x, ⟪u x, e.complexCutoffPullback he σ f x⟫_ℂ ∂μ =
          ∫ y, ⟪e.cutoffPushforwardSchwartz he ψ u y, f y⟫_ℂ := by
  obtain ⟨ρ, hρ, hρ0, hint⟩ := hasSmoothPositiveDensity_iff.1 hμ e he
  obtain ⟨σ, hσ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn (Ω := ⟨e.target, e.open_target⟩)
    (hρ.inv fun y hy ↦ (hρ0 y hy).ne') ψ
  refine ⟨σ, fun u f ↦ integral_eq_integral_of_eq_mul hint σ
    (F := fun x ↦ ⟪u x, e.complexCutoffPullback he σ f x⟫_ℂ)
    (u.contMDiff.continuous.inner (e.complexCutoffPullback he σ f).contMDiff.continuous)
    (fun x hx hσx ↦ ?_) (fun x hx ↦ ?_) (fun y hy ↦ ?_) fun y hy ↦ ?_⟩
  · simp [complexCutoffPullback_apply_of_mem he _ _ hx, hσx]
  · simp [complexCutoffPullback_apply_of_notMem he _ _ hx]
  · -- On the target, `ρ σ = ψ`.
    rw [cutoffPushforwardSchwartz_apply,
      complexCutoffPullback_apply_of_mem he _ _ (e.map_target hy), e.right_inv hy, hσ]
    simp only [Pi.inv_apply, smul_eq_mul, Complex.real_smul, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.2 (hρ0 y hy).ne']
  · rw [cutoffPushforwardSchwartz_apply,
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (ψ.tsupport_subset h), zero_smul, inner_zero_left]

end Chart

/-! ### The pairing estimates -/

variable {ι : Type*} [Fintype ι] {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))

/-- A Schwartz function on `ℝⁿ` as a smooth function. -/
private def schwartzToSmooth (b : 𝓢(CoordinateSpace n, ℂ)) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨b, contMDiff_iff_contDiff.2 (b.smooth ⊤)⟩

@[simp]
private theorem schwartzToSmooth_apply (b : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n) :
    schwartzToSmooth b y = b y :=
  rfl

/-- Coordinatewise bounds `‖x i‖ ≤ C i * g` with `0 ≤ g` bound the `Lᵖ` norm of `x` by
`(∑ i, |C i|) * g`. -/
private theorem norm_le_sum_abs_mul_of_forall_norm_apply_le {p : ENNReal} [Fact (1 ≤ p)]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] {x : PiLp p E} {C : ι → ℝ} {g : ℝ}
    (hg : 0 ≤ g) (h : ∀ i, ‖x i‖ ≤ C i * g) : ‖x‖ ≤ (∑ i, |C i|) * g := by
  refine (PiLp.norm_le_sum_norm x).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ ↦ (h i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hg)

omit [MeasurableSpace M] [BorelSpace M] in
/-- **The readings of a pulled-back Schwartz function.** For a cutoff `σ` in a chart `e'`, the
smooth function `(σ b) ∘ e'` on `M`, extended by `0`, of a Schwartz function `b` has chart readings
of order `s` bounded by `C ‖b‖_{H^s}`: its reading in the chart `eᵢ` is the localized change of
variables `y ↦ θᵢ(y) b(e' (eᵢ⁻¹ y))` of `b`. -/
private theorem exists_norm_chartReading_complexCutoffPullback_le
    {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (σ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (s : ℝ) :
    ∃ C, ∀ b : 𝓢(CoordinateSpace n, ℂ),
      ‖chartReading he ψ s (e'.complexCutoffPullback he' σ (schwartzToSmooth b))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 b‖ := by
  -- In the chart `eᵢ`, the reading is `θᵢ · (b ∘ κᵢ)` for the overlap cutoff `θᵢ` and the
  -- transition map `κᵢ = e' ∘ eᵢ⁻¹`.
  have hC (i : ι) : ∃ C, ∀ b : 𝓢(CoordinateSpace n, ℂ),
      ‖chartReading he ψ s (e'.complexCutoffPullback he' σ (schwartzToSmooth b)) i‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 b‖ := by
    obtain ⟨hθ, hθc, hθs⟩ := overlapCutoff_spec he' (he i) (ψ i) σ
    obtain ⟨C, hC⟩ := BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp
      (F := ℂ) (contDiffOn_symm_trans_of_mem_maximalAtlas (he i) he')
      (fun _ hz ↦ (contDiffAt_symm_trans_symm_of_mem_maximalAtlas (he i) he' hz).contDiffWithinAt)
      hθ hθc hθs ENNReal.one_lt_two ENNReal.ofNat_ne_top s
    refine ⟨C, fun b ↦ ?_⟩
    rw [chartReading_apply]
    refine hC _ _ fun y ↦ ?_
    rw [cutoffPushforwardSchwartz_apply, overlapCutoff_apply, coe_trans, Function.comp_apply,
      ← smul_smul]
    congr 1
    by_cases hy : (e i).symm y ∈ e'.source
    · rw [complexCutoffPullback_apply_of_mem he' _ _ hy, cutoffPullback_one_apply_of_mem he' _ hy,
        schwartzToSmooth_apply]
    · rw [complexCutoffPullback_apply_of_notMem he' _ _ hy,
        cutoffPullback_apply_of_notMem he' _ _ hy, zero_smul]
  choose C hC using hC
  exact ⟨∑ i, |C i|, fun b ↦
    norm_le_sum_abs_mul_of_forall_norm_apply_le (norm_nonneg _) fun i ↦ hC i b⟩

omit [BorelSpace M] in
/-- **The `H^{-s}` norm is the dual norm for the `L²(μ)` pairing.** For a measure `μ` with a smooth
positive density and finitely many cutoffs `ψᵢ` in charts `eᵢ`, there is a constant `C` such that
every smooth `u` with `|∫ ⟪u, v⟫ dμ| ≤ K ‖v‖_{H^s}` for all smooth `v` satisfies
`‖u‖_{H^{-s}} ≤ C K`, the norms being those of the chart readings. -/
theorem exists_norm_chartReading_neg_le (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (s : ℝ) :
    ∃ C, ∀ (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {K : ℝ}, 0 ≤ K →
      (∀ v, ‖∫ x, ⟪u x, v x⟫_ℂ ∂μ‖ ≤ K * ‖chartReading he ψ s v‖) →
        ‖chartReading he ψ (-s) u‖ ≤ C * K := by
  choose σ hσ using fun i ↦ exists_integral_inner_complexCutoffPullback_eq (he i) hμ (ψ i)
  choose C hC using fun i ↦ exists_norm_chartReading_complexCutoffPullback_le he ψ (he i) (σ i) s
  refine ⟨∑ i, |(|C i|)|, fun u K hK hu ↦
    norm_le_sum_abs_mul_of_forall_norm_apply_le hK fun i ↦ ?_⟩
  -- Pair the `i`-th reading with a Schwartz function `b` through `(σᵢ b) ∘ eᵢ` on `M`.
  rw [chartReading_apply]
  refine SchwartzMap.norm_toBesselPotentialSpaceCLM_neg_le_of_forall s _
    (mul_nonneg (abs_nonneg _) hK) fun b ↦ ?_
  have h := hσ i u (schwartzToSmooth b)
  simp only [schwartzToSmooth_apply] at h
  rw [← h, mul_comm |C i|, mul_assoc]
  exact (hu _).trans (mul_le_mul_of_nonneg_left
    ((hC i b).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))) hK)

variable {ψ}

/-- **The `L²(μ)` pairing is bounded on `H^{-s} × H^s`.** For a finite measure `μ` with a smooth
positive density and cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, there is a
constant `C` such that `|∫ ⟪u, v⟫ dμ| ≤ C ‖u‖_{H^{-s}} ‖v‖_{H^s}` for all smooth `u` and `v`, the
norms being those of the chart readings. -/
theorem exists_norm_integral_inner_le_mul_norm_chartReading [IsFiniteMeasure μ]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s : ℝ) :
    ∃ C, ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖∫ x, ⟪u x, v x⟫_ℂ ∂μ‖ ≤ C * ‖chartReading he ψ (-s) u‖ * ‖chartReading he ψ s v‖ := by
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he ψ hψ
  choose τ hτ using fun i ↦ exists_integral_mul_inner_eq (he i) hμ (ψ i)
  obtain ⟨C, hC⟩ := exists_norm_chartReading_le he ψ he τ hψ s
  refine ⟨Fintype.card ι * C, fun u v ↦ ?_⟩
  -- Split the integrand with the partition `∑ᵢ ψᵢ ∘ eᵢ = 1` and read each piece in its chart.
  have hsplit : ∫ x, ⟪u x, v x⟫_ℂ ∂μ =
      ∑ i, ∫ x, ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * ⟪u x, v x⟫_ℂ ∂μ := by
    rw [← integral_finsetSum _ fun i _ ↦ (show Integrable
      (fun x ↦ ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * ⟪u x, v x⟫_ℂ) μ from
        Continuous.integrable_of_hasCompactSupport ((Complex.continuous_ofReal.comp
          ((e i).cutoffPullback (he i) (ψ i) 1).contMDiff.continuous).mul
          (u.contMDiff.continuous.inner v.contMDiff.continuous))
          (HasCompactSupport.of_compactSpace _))]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum, hψ x, Complex.ofReal_one, one_mul]
  rw [hsplit]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖∫ x, ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * ⟪u x, v x⟫_ℂ ∂μ‖
      ≤ ∑ _i : ι, ‖chartReading he ψ (-s) u‖ * (C * ‖chartReading he ψ s v‖) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [hτ i u v]
        have hu := PiLp.norm_apply_le (chartReading he ψ (-s) u) i
        have hv := (PiLp.norm_apply_le (chartReading he τ s v) i).trans (hC v)
        rw [chartReading_apply] at hu hv
        exact (SchwartzMap.norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm s _
          _).trans (mul_le_mul hu hv (norm_nonneg _) (norm_nonneg _))
    _ = Fintype.card ι * C * ‖chartReading he ψ (-s) u‖ * ‖chartReading he ψ s v‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

section IntegralInner

variable (μ) [CompactSpace M] [IsFiniteMeasure μ]

omit [T2Space M] in
/-- The `L²(μ)` pairing `∫ ⟪u, v⟫ dμ` of smooth functions on a compact manifold, conjugate-linear in
`u` and linear in `v`. -/
private def integralInner :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ⋆[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] ℂ :=
  have hint (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      Integrable (fun x ↦ ⟪u x, v x⟫_ℂ) μ :=
    (u.contMDiff.continuous.inner v.contMDiff.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun u v ↦ ∫ x, ⟪u x, v x⟫_ℂ ∂μ)
    (fun u₁ u₂ v ↦ by
      simp only [ContMDiffMap.coe_add, Pi.add_apply, inner_add_left]
      exact integral_add (hint u₁ v) (hint u₂ v))
    (fun c u v ↦ by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [ContMDiffMap.complex_smul_apply, RCLike.inner_apply, map_mul]
      ring)
    (fun u v₁ v₂ ↦ by
      simp only [ContMDiffMap.coe_add, Pi.add_apply, inner_add_right]
      exact integral_add (hint u v₁) (hint u v₂))
    (fun c u v ↦ by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [ContMDiffMap.complex_smul_apply, RCLike.inner_apply, RingHom.id_apply]
      ring)

omit [T2Space M] in
private theorem integralInner_apply (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    integralInner μ u v = ∫ x, ⟪u x, v x⟫_ℂ ∂μ :=
  (rfl)

end IntegralInner

/-! ### The pairing of `H^{-s}(M)` and `H^s(M)` -/

section Pairing

variable [IsFiniteMeasure μ] (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
  (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s : ℝ)

/-- For a smooth `u`, the functional `v ↦ ∫ ⟪u, v⟫ dμ` extended to `H^s(M)`. -/
private def integralInnerExtension [CompactSpace M]
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    StrongDual ℂ (chartSobolevSpace he ψ s) :=
  (integralInner μ u).extendOfNorm (toChartSobolevSpace he ψ s)

include hμ hψ in
private theorem integralInnerExtension_toChartSobolevSpace [CompactSpace M]
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    integralInnerExtension (μ := μ) he s u (toChartSobolevSpace he ψ s v) =
      integralInner μ u v := by
  obtain ⟨C, hC⟩ := exists_norm_integral_inner_le_mul_norm_chartReading he hμ hψ s
  exact LinearMap.extendOfNorm_eq (denseRange_toChartSobolevSpace he ψ s)
    ⟨C * ‖chartReading he ψ (-s) u‖, fun w ↦ (hC u w).trans_eq (by
      rw [norm_toChartSobolevSpace])⟩ v

include hμ hψ in
private theorem norm_integralInnerExtension_le [CompactSpace M] :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖integralInnerExtension (μ := μ) (ψ := ψ) he s u‖ ≤ C * ‖chartReading he ψ (-s) u‖ := by
  obtain ⟨C, hC⟩ := exists_norm_integral_inner_le_mul_norm_chartReading he hμ hψ s
  refine ⟨max C 0, fun u ↦ ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (le_max_right _ _) (norm_nonneg _)) fun y ↦ ?_⟩
  refine LinearMap.norm_extendOfNorm_apply_le (denseRange_toChartSobolevSpace he ψ s) _
    (fun w ↦ ?_) y
  rw [integralInner_apply, norm_toChartSobolevSpace]
  exact (hC u w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (norm_nonneg _))

include hμ hψ in
/-- The functionals `v ↦ ∫ ⟪u, v⟫ dμ` on `H^s(M)`, as a conjugate-linear map in the smooth `u`. -/
private def integralInnerExtensionₗ :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ⋆[ℂ] StrongDual ℂ (chartSobolevSpace he ψ s) :=
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he ψ hψ
  { toFun := integralInnerExtension (μ := μ) he s
    map_add' u₁ u₂ := chartSobolevSpace_ext he ψ fun v ↦ by
      simp [integralInnerExtension_toChartSobolevSpace he hμ hψ]
    map_smul' c u := chartSobolevSpace_ext he ψ fun v ↦ by
      simp [integralInnerExtension_toChartSobolevSpace he hμ hψ] }

include hμ hψ in
/-- The Riesz representatives in `H^s(M)` of the functionals `v ↦ ∫ ⟪u, v⟫ dμ`, extended by
continuity from the smooth `u` to `H^{-s}(M)`: the element `R x` of `H^s(M)` with
`⟪R x, y⟫_{H^s} = ⟨x, y⟩`. -/
private def chartSobolevRiesz : chartSobolevSpace he ψ (-s) →L[ℂ] chartSobolevSpace he ψ s :=
  ((InnerProductSpace.toDual ℂ (chartSobolevSpace he ψ s)).symm.toLinearEquiv.toLinearMap.comp
    (integralInnerExtensionₗ he hμ hψ s)).extendOfNorm (toChartSobolevSpace he ψ (-s))

private theorem chartSobolevRiesz_toChartSobolevSpace
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevRiesz he hμ hψ s (toChartSobolevSpace he ψ (-s) u) =
      (InnerProductSpace.toDual ℂ (chartSobolevSpace he ψ s)).symm
        (integralInnerExtensionₗ he hμ hψ s u) := by
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he ψ hψ
  obtain ⟨C, hC⟩ := norm_integralInnerExtension_le he hμ hψ s
  exact LinearMap.extendOfNorm_eq (denseRange_toChartSobolevSpace he ψ (-s))
    ⟨C, fun u ↦ by
      rw [LinearMap.comp_apply, norm_toChartSobolevSpace]
      exact ((InnerProductSpace.toDual ℂ _).symm.norm_map _).trans_le (hC u)⟩ u

/-- **The pairing of `H^{-s}(M)` and `H^s(M)`.** For a finite measure `μ` with a smooth positive
density and cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, the `L²(μ)` pairing
`(u, v) ↦ ∫ ⟪u, v⟫ dμ` of smooth functions extends by continuity to a continuous pairing of
`H^{-s}(M)` with `H^s(M)`, conjugate-linear in the first and linear in the second argument
(`TauCeti.chartSobolevPairing_toChartSobolevSpace`). It identifies `H^{-s}(M)` with the dual of
`H^s(M)` (`TauCeti.chartSobolevDualEquiv`). -/
def chartSobolevPairing :
    chartSobolevSpace he ψ (-s) →L⋆[ℂ] StrongDual ℂ (chartSobolevSpace he ψ s) :=
  (innerSL ℂ).comp (chartSobolevRiesz he hμ hψ s)

/-- On smooth functions, the pairing of `H^{-s}(M)` and `H^s(M)` is the `L²(μ)` pairing. -/
@[simp]
theorem chartSobolevPairing_toChartSobolevSpace
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevPairing he hμ hψ s (toChartSobolevSpace he ψ (-s) u)
        (toChartSobolevSpace he ψ s v) = ∫ x, ⟪u x, v x⟫_ℂ ∂μ := by
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he ψ hψ
  rw [chartSobolevPairing, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    chartSobolevRiesz_toChartSobolevSpace, InnerProductSpace.toDual_symm_apply]
  exact (integralInnerExtension_toChartSobolevSpace he hμ hψ s u v).trans
    (integralInner_apply μ u v)

/-- The pairing of `x` and `y` is the `H^s` inner product of the Riesz representative of `x` with
`y`. -/
private theorem chartSobolevPairing_apply_apply (x : chartSobolevSpace he ψ (-s))
    (y : chartSobolevSpace he ψ s) :
    chartSobolevPairing he hμ hψ s x y = ⟪chartSobolevRiesz he hμ hψ s x, y⟫_ℂ :=
  (rfl)

/-- The `H^{-s}` norm is controlled by the `H^s` norm of the Riesz representative. -/
private theorem exists_norm_le_mul_norm_chartSobolevRiesz :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * ‖chartSobolevRiesz he hμ hψ s x‖ := by
  obtain ⟨C, hC⟩ := exists_norm_chartReading_neg_le he ψ hμ s
  refine ⟨max C 0, le_max_right _ _, fun x ↦ (denseRange_toChartSobolevSpace he ψ (-s)).induction_on
    x (isClosed_le continuous_norm (continuous_const.mul
      (chartSobolevRiesz he hμ hψ s).continuous.norm)) fun u ↦ ?_⟩
  rw [norm_toChartSobolevSpace]
  refine (hC u (norm_nonneg _) fun v ↦ ?_).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [← chartSobolevPairing_toChartSobolevSpace he hμ hψ s u v, chartSobolevPairing_apply_apply,
    ← norm_toChartSobolevSpace he ψ s v]
  exact norm_inner_le_norm _ _

/-- The `H^s` norm is controlled by the `H^{-s}` norm of the image under the adjoint of the Riesz
map, which represents the functional `x ↦ ⟨x, y⟩` on `H^{-s}(M)`. -/
private theorem exists_norm_le_mul_norm_adjoint_chartSobolevRiesz :
    ∃ C, 0 ≤ C ∧ ∀ y,
      ‖y‖ ≤ C * ‖ContinuousLinearMap.adjoint (chartSobolevRiesz he hμ hψ s) y‖ := by
  set R := chartSobolevRiesz he hμ hψ s
  obtain ⟨C, hC⟩ := exists_norm_chartReading_neg_le he ψ hμ (-s)
  refine ⟨max C 0, le_max_right _ _, fun y ↦ (denseRange_toChartSobolevSpace he ψ s).induction_on
    y (isClosed_le continuous_norm (continuous_const.mul
      (ContinuousLinearMap.adjoint R :
        chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he ψ (-s)).continuous.norm)) fun v ↦ ?_⟩
  have h := hC v (K := ‖ContinuousLinearMap.adjoint R (toChartSobolevSpace he ψ s v)‖)
    (norm_nonneg _) fun u ↦ ?_
  · rw [neg_neg] at h
    rw [norm_toChartSobolevSpace]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- `∫ ⟪v, u⟫ dμ` is the conjugate of `∫ ⟪u, v⟫ dμ = ⟪R u, v⟫ = ⟪u, R† v⟫`.
  have hconj : ∫ x, ⟪v x, u x⟫_ℂ ∂μ = conj (∫ x, ⟪u x, v x⟫_ℂ ∂μ) := by
    rw [← integral_conj]
    simp_rw [inner_conj_symm]
  rw [hconj, RCLike.norm_conj,
    ← chartSobolevPairing_toChartSobolevSpace he hμ hψ s u v, chartSobolevPairing_apply_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ← norm_toChartSobolevSpace he ψ (-s) u, mul_comm]
  exact norm_inner_le_norm _ _

/-- A vector `z` of a complex inner product space with `‖⟪z, z⟫‖ ≤ K ‖z‖` has norm at most `K`. -/
private theorem norm_le_of_norm_inner_self_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {z : F} {K : ℝ} (hK : 0 ≤ K) (h : ‖⟪z, z⟫_ℂ‖ ≤ K * ‖z‖) : ‖z‖ ≤ K := by
  rcases (norm_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]
    exact hK
  refine le_of_mul_le_mul_right ?_ hz
  rwa [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at h

/-- **The `H^{-s}` norm is the dual norm for the pairing**: if `|⟨x, y⟩| ≤ K ‖y‖_{H^s}` for every
`y ∈ H^s(M)`, then `‖x‖_{H^{-s}} ≤ C K`. -/
theorem exists_norm_le_of_forall_norm_chartSobolevPairing_le_left :
    ∃ C, ∀ (x : chartSobolevSpace he ψ (-s)) {K : ℝ}, 0 ≤ K →
      (∀ y, ‖chartSobolevPairing he hμ hψ s x y‖ ≤ K * ‖y‖) → ‖x‖ ≤ C * K := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_norm_chartSobolevRiesz he hμ hψ s
  refine ⟨C, fun x K hK hx ↦ (hC x).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  -- `‖R x‖² = ⟨x, R x⟩ ≤ K ‖R x‖`.
  have := hx (chartSobolevRiesz he hμ hψ s x)
  rw [chartSobolevPairing_apply_apply] at this
  exact norm_le_of_norm_inner_self_le hK this

/-- **The `H^s` norm is the dual norm for the pairing**: if `|⟨x, y⟩| ≤ K ‖x‖_{H^{-s}}` for every
`x ∈ H^{-s}(M)`, then `‖y‖_{H^s} ≤ C K`. -/
theorem exists_norm_le_of_forall_norm_chartSobolevPairing_le_right :
    ∃ C, ∀ (y : chartSobolevSpace he ψ s) {K : ℝ}, 0 ≤ K →
      (∀ x, ‖chartSobolevPairing he hμ hψ s x y‖ ≤ K * ‖x‖) → ‖y‖ ≤ C * K := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_norm_adjoint_chartSobolevRiesz he hμ hψ s
  refine ⟨C, fun y K hK hy ↦ (hC y).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  -- `‖R† y‖² = ⟨R† y, y⟩ ≤ K ‖R† y‖`.
  have := hy (ContinuousLinearMap.adjoint (chartSobolevRiesz he hμ hψ s) y)
  rw [chartSobolevPairing_apply_apply, ← ContinuousLinearMap.adjoint_inner_right] at this
  exact norm_le_of_norm_inner_self_le hK this

/-- The Riesz map `H^{-s}(M) → H^s(M)` is bijective: it is bounded below, and an element of `H^s(M)`
orthogonal to its range is killed by the adjoint, hence vanishes. -/
private theorem bijective_chartSobolevRiesz :
    Function.Bijective (chartSobolevRiesz he hμ hψ s) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_norm_chartSobolevRiesz he hμ hψ s
  obtain ⟨C', -, hC'⟩ := exists_norm_le_mul_norm_adjoint_chartSobolevRiesz he hμ hψ s
  set R := chartSobolevRiesz he hμ hψ s
  refine R.bijective_iff_dense_range_and_antilipschitz.2
    ⟨?_, _, R.antilipschitz_of_bound (K := ⟨C, hC0⟩) hC⟩
  -- An element `y` orthogonal to the range is killed by `R†`, hence vanishes.
  rw [Submodule.topologicalClosure_eq_top_iff, R.orthogonal_range]
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦ norm_le_zero_iff.1 ((hC' y).trans ?_)
  rw [show ContinuousLinearMap.adjoint R y = 0 from LinearMap.mem_ker.1 hy, norm_zero, mul_zero]

/-- **Duality of the Sobolev spaces of a compact manifold.** For a finite measure `μ` with a smooth
positive density and cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, the `L²(μ)`
pairing identifies `H^{-s}(M)` with the continuous dual of `H^s(M)`, for every real `s`: the
conjugate-linear isomorphism `x ↦ chartSobolevPairing x`, with `⟨u, v⟩ = ∫ ⟪u, v⟫ dμ` on smooth
functions. -/
def chartSobolevDualEquiv :
    chartSobolevSpace he ψ (-s) ≃SL[starRingEnd ℂ] StrongDual ℂ (chartSobolevSpace he ψ s) :=
  (ContinuousLinearEquiv.ofBijective (chartSobolevRiesz he hμ hψ s)
    (LinearMap.ker_eq_bot.2 (bijective_chartSobolevRiesz he hμ hψ s).1)
    (LinearMap.range_eq_top.2 (bijective_chartSobolevRiesz he hμ hψ s).2)).trans
    (InnerProductSpace.toDual ℂ (chartSobolevSpace he ψ s)).toContinuousLinearEquiv

@[simp]
theorem chartSobolevDualEquiv_apply (x : chartSobolevSpace he ψ (-s)) :
    chartSobolevDualEquiv he hμ hψ s x = chartSobolevPairing he hμ hψ s x := by
  ext y
  simp [chartSobolevDualEquiv, chartSobolevPairing_apply_apply]

/-- Every continuous functional `f` on `H^s(M)` is the pairing with
`(chartSobolevDualEquiv he hμ hψ s).symm f ∈ H^{-s}(M)`. -/
@[simp]
theorem chartSobolevPairing_chartSobolevDualEquiv_symm
    (f : StrongDual ℂ (chartSobolevSpace he ψ s)) (y : chartSobolevSpace he ψ s) :
    chartSobolevPairing he hμ hψ s ((chartSobolevDualEquiv he hμ hψ s).symm f) y = f y := by
  rw [← chartSobolevDualEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end Pairing

end TauCeti
