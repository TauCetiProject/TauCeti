/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.LipschitzLimit
public import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Weak convergence of derivatives along locally uniform limits

Let `uᵢ` be `C¹` maps on an open subset `Ω` of a finite-dimensional real normed space, converging
locally uniformly on `Ω` to a map `v`, and suppose that their derivatives are eventually bounded on
every compact subset of `Ω`. This is the situation produced by Arzelà–Ascoli arguments, for
instance by Gromov compactness for pseudoholomorphic curves away from the bubbling points. The
derivatives need not converge pointwise, but:

* the limit is locally Lipschitz on `Ω`, with derivative bounded on every compact subset of `Ω`
  (`TauCeti.locallyLipschitzOn_of_tendsto` and `TauCeti.exists_forall_norm_fderiv_le_of_tendsto`
  in `TauCeti.Analysis.Calculus.FDeriv.LipschitzLimit`);
* the derivatives converge weakly to the derivative of the limit: for every continuous weight `a`
  with compact support in `Ω` and every direction `w`, `∫ a • ∂_w uᵢ → ∫ a • ∂_w v`
  (`TauCeti.tendsto_integral_smul_fderiv_apply_of_tendstoLocallyUniformlyOn`), and likewise
  `∫ A (∂_w uᵢ) → ∫ A (∂_w v)` for a continuous field `A` of linear maps between
  finite-dimensional spaces with compact support in `Ω`
  (`TauCeti.tendsto_integral_apply_fderiv_apply_of_tendstoLocallyUniformlyOn`).

The zeroth-order counterpart, used for the maps themselves and for coefficients evaluated along
them, is that integrals against such a weight pass to limits that are uniform on its support
(`TauCeti.tendsto_integral_smul_of_tendstoUniformlyOn`).

Here `fderiv ℝ v` is the derivative of the limit, which exists almost everywhere by Rademacher's
theorem and is its weak derivative (`LocallyLipschitzOn.hasWeakFDerivOn_fderiv`). For a test
function `a`, integration by parts moves the derivative onto `a`, and the maps themselves converge
uniformly on its support. A continuous weight is approximated uniformly by test functions
supported in a fixed compact set, on which the derivatives are uniformly bounded
(`Continuous.exists_testFunction_dist_le`). A field of linear maps is expanded in a basis.

The operator-valued form passes first-order equations that are linear in the derivative to the
limit, even when their coefficients depend on the map, such as `∂_t u = J(u) ∂_s u`: along the
sequence the coefficients converge uniformly, while the derivatives converge weakly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2 (Lipschitz functions are
  weakly differentiable) and Appendix D.4 (weak convergence).
-/

public section

namespace TauCeti

open Filter Function Metric _root_.MeasureTheory Set TopologicalSpace
open scoped Distributions NNReal Topology

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {l : Filter ι} {u : ι → E → F} {v : E → F} {Ω : Set E}

section WeakConvergence

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Integrals against a continuous weight `a` with compact support in an open set `Ω` pass to limits
of maps continuous on `Ω` that converge uniformly on the support of `a`. -/
theorem tendsto_integral_smul_of_tendstoUniformlyOn (hΩ : IsOpen Ω) {f : ι → E → F} {g : E → F}
    (hf : ∀ i, ContinuousOn (f i) Ω) (hg : ContinuousOn g Ω) {a : E → ℝ} (ha : Continuous a)
    (hac : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω)
    (hlim : TendstoUniformlyOn f g l (tsupport a)) :
    Tendsto (fun i ↦ ∫ x, a x • f i x ∂μ) l (𝓝 (∫ x, a x • g x ∂μ)) := by
  have hint : ∀ {h : E → F}, ContinuousOn h Ω → Integrable (fun x ↦ a x • h x) μ := fun hh ↦
    (hh.locallyIntegrableOn hΩ.measurableSet).integrable_smul_left_of_hasCompactSupport ha hac
      haΩ
  obtain ⟨B, hB⟩ := ha.bounded_above_of_compact_support hac
  exact MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub (Eventually.of_forall hB)
    (Eventually.of_forall fun x hx ↦ image_eq_zero_of_notMem_tsupport hx)
    (Eventually.of_forall fun i ↦ hint (hf i)) (hint hg).aestronglyMeasurable
    (hlim.tendsto_setLIntegral_enorm_sub hac.measure_lt_top.ne)

/-- The case of a test function in
`TauCeti.tendsto_integral_smul_fderiv_apply_of_tendstoLocallyUniformlyOn`: integrating by parts,
`∫ φ • ∂_w uᵢ = -∫ (∂_w φ) • uᵢ`, and the maps converge uniformly on the support of `φ`. -/
private theorem tendsto_integral_testFunction_smul_fderiv_apply [FiniteDimensional ℝ F]
    (hΩ : IsOpen Ω) (hu : ∀ i, ContDiffOn ℝ 1 (u i) Ω)
    (hv : LocallyLipschitzOn Ω v) (hlim : TendstoLocallyUniformlyOn u v l Ω)
    (φ : 𝓓(⟨Ω, hΩ⟩, ℝ)) (w : E) :
    Tendsto (fun i ↦ ∫ x, φ x • fderiv ℝ (u i) x w ∂μ) l (𝓝 (∫ x, φ x • fderiv ℝ v x w ∂μ)) := by
  have hvw := hasWeakFDerivOn_iff.1 (hv.hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⟨Ω, hΩ⟩)) w
  have huw : ∀ i, HasWeakLineDerivOn μ ⟨Ω, hΩ⟩ (u i) (fun x ↦ fderiv ℝ (u i) x w) w := fun i ↦
    hasWeakFDerivOn_iff.1 (hasWeakFDerivOn_of_differentiableOn
      ((hu i).continuousOn.locallyIntegrableOn hΩ.measurableSet)
      (((hu i).continuousOn_fderiv_of_isOpen hΩ le_rfl).locallyIntegrableOn hΩ.measurableSet)
      fun x hx ↦ ((hu i).differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx)) w
  set ψ : 𝓓(⟨Ω, hΩ⟩, ℝ) := TestFunction.lineDerivCLM ℝ w φ
  have hcoe : (ψ : E → ℝ) = fun x ↦ lineDeriv ℝ (φ : E → ℝ) x w :=
    funext fun _ ↦ TestFunction.lineDerivCLM_apply_of_le le_top
  have key := (tendsto_integral_smul_of_tendstoUniformlyOn (μ := μ) hΩ
    (fun i ↦ (hu i).continuousOn) hv.continuousOn ψ.continuous ψ.hasCompactSupport
    ψ.tsupport_subset (((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hlim) _
      ψ.tsupport_subset ψ.hasCompactSupport)).neg
  simp only [hcoe] at key
  rw [hvw.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg] at key
  refine key.congr fun i ↦ ?_
  rw [(huw i).integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Replacing the weight `a` by `b`, with `|b - a| ≤ η` and both vanishing off a compact set `K`,
changes the integral against a function bounded by `B` on `K` by at most `η B μ(K)`. -/
private theorem norm_integral_smul_sub_integral_smul_le {K : Set E} (hK : IsCompact K)
    {a b : E → ℝ} {h : E → F} {η B : ℝ} (ha : Integrable (fun x ↦ a x • h x) μ)
    (hb : Integrable (fun x ↦ b x • h x) μ) (haK : ∀ x ∉ K, a x = 0) (hbK : ∀ x ∉ K, b x = 0)
    (hab : ∀ x, |b x - a x| ≤ η) (hB : ∀ x ∈ K, ‖h x‖ ≤ B) :
    ‖∫ x, a x • h x ∂μ - ∫ x, b x • h x ∂μ‖ ≤ η * B * μ.real K := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hab 0)
  rw [← integral_sub ha hb, ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    simp [haK x hx, hbK x hx]]
  refine norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx ↦ ?_
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_mul (hab x) (hB x hx) (norm_nonneg _) hη

/-- **Derivatives converge weakly along locally uniform limits.** Let `uᵢ` be `C¹` maps on an open
set `Ω`, with derivatives eventually bounded on every compact subset of `Ω`, converging locally
uniformly on `Ω` to `v`. Then for every continuous `a` with compact support in `Ω` and every
direction `w`, `∫ a • ∂_w uᵢ → ∫ a • ∂_w v`. The limit `v` is locally Lipschitz on `Ω`
(`TauCeti.locallyLipschitzOn_of_tendsto`), so `fderiv ℝ v` is its derivative almost everywhere
on `Ω` and its weak derivative there. -/
theorem tendsto_integral_smul_fderiv_apply_of_tendstoLocallyUniformlyOn [FiniteDimensional ℝ F]
    [l.NeBot] (hΩ : IsOpen Ω) (hu : ∀ i, ContDiffOn ℝ 1 (u i) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ᶠ i in l, ∀ x ∈ K, ‖fderiv ℝ (u i) x‖ ≤ C)
    (hlim : TendstoLocallyUniformlyOn u v l Ω) {a : E → ℝ} (ha : Continuous a)
    (hac : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) (w : E) :
    Tendsto (fun i ↦ ∫ x, a x • fderiv ℝ (u i) x w ∂μ) l (𝓝 (∫ x, a x • fderiv ℝ v x w ∂μ)) := by
  have hdiff : ∀ᶠ i in l, DifferentiableOn ℝ (u i) Ω :=
    Eventually.of_forall fun i ↦ (hu i).differentiableOn one_ne_zero
  have hpt : ∀ x ∈ Ω, Tendsto (fun i ↦ u i x) l (𝓝 (v x)) := fun _ hx ↦ hlim.tendsto_at hx
  have hv := locallyLipschitzOn_of_tendsto hΩ hdiff hbd hpt
  -- Approximate `a` on a compact neighbourhood `K` of its support, on which the derivatives of
  -- the maps and of the limit are bounded by `C` and `D`.
  obtain ⟨δ, hδ, hδΩ⟩ := hac.exists_cthickening_subset_open hΩ haΩ
  set K := cthickening δ (tsupport a)
  have hK : IsCompact K := hac.cthickening
  obtain ⟨C, hC⟩ := hbd K hK hδΩ
  obtain ⟨D, hD⟩ := exists_forall_norm_fderiv_le_of_tendsto hΩ hdiff hbd hpt hK hδΩ
  have hlocu : ∀ i, LocallyIntegrableOn (fun x ↦ fderiv ℝ (u i) x w) Ω μ := fun i ↦
    (((hu i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const)
      |>.locallyIntegrableOn hΩ.measurableSet
  have hlocv : LocallyIntegrableOn (fun x ↦ fderiv ℝ v x w) Ω μ :=
    (hasWeakFDerivOn_iff.1 (hv.hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⟨Ω, hΩ⟩)) w)
      |>.locallyIntegrableOn_deriv
  set M := (max C 0 + max D 0) * ‖w‖ * μ.real K
  have hM : 0 ≤ M := by positivity
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set η := ε / (2 * (M + 1))
  have hη : 0 < η := by positivity
  obtain ⟨φ, hφK, hφ⟩ := ha.exists_testFunction_dist_le (Ω := ⟨Ω, hΩ⟩) hac subset_rfl hδ hδΩ hη
  have hφK' : ∀ x ∉ K, φ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφK h)
  have haK : ∀ x ∉ K, a x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (self_subset_cthickening _ h)
  have hφa : ∀ x, |φ x - a x| ≤ η := fun x ↦ by simpa [Real.dist_eq] using hφ x
  have hmid := Metric.tendsto_nhds.1
    (tendsto_integral_testFunction_smul_fderiv_apply (μ := μ) hΩ hu hv hlim φ w) (ε / 2)
    (half_pos hε)
  filter_upwards [hC, hmid] with i hCi hi
  have h1 := norm_integral_smul_sub_integral_smul_le hK
    ((hlocu i).integrable_smul_left_of_hasCompactSupport ha hac haΩ)
    (φ.integrable_smul (hlocu i)) haK hφK' hφa (B := max C 0 * ‖w‖) fun x hx ↦
      ((fderiv ℝ (u i) x).le_opNorm w).trans (by gcongr; exact (hCi x hx).trans (le_max_left _ _))
  have h2 := norm_integral_smul_sub_integral_smul_le hK
    (hlocv.integrable_smul_left_of_hasCompactSupport ha hac haΩ)
    (φ.integrable_smul hlocv) haK hφK' hφa (B := max D 0 * ‖w‖) fun x hx ↦
      ((fderiv ℝ v x).le_opNorm w).trans (by gcongr; exact (hD x hx).trans (le_max_left _ _))
  rw [dist_eq_norm] at hi ⊢
  have hsplit : ∫ x, a x • fderiv ℝ (u i) x w ∂μ - ∫ x, a x • fderiv ℝ v x w ∂μ =
      (∫ x, a x • fderiv ℝ (u i) x w ∂μ - ∫ x, φ x • fderiv ℝ (u i) x w ∂μ) +
        (∫ x, φ x • fderiv ℝ (u i) x w ∂μ - ∫ x, φ x • fderiv ℝ v x w ∂μ) -
          (∫ x, a x • fderiv ℝ v x w ∂μ - ∫ x, φ x • fderiv ℝ v x w ∂μ) := by abel
  rw [hsplit]
  have hηM : η * (max C 0 * ‖w‖) * μ.real K + η * (max D 0 * ‖w‖) * μ.real K ≤ ε / 2 := by
    have : η * (M + 1) = ε / 2 := by
      simp only [η]; field_simp
    nlinarith [measureReal_nonneg (μ := μ) (s := K), norm_nonneg w]
  calc _ ≤ ‖∫ x, a x • fderiv ℝ (u i) x w ∂μ - ∫ x, φ x • fderiv ℝ (u i) x w ∂μ‖ +
        ‖∫ x, φ x • fderiv ℝ (u i) x w ∂μ - ∫ x, φ x • fderiv ℝ v x w ∂μ‖ +
          ‖∫ x, a x • fderiv ℝ v x w ∂μ - ∫ x, φ x • fderiv ℝ v x w ∂μ‖ := norm_sub_le_of_le
            (norm_add_le _ _) le_rfl
    _ < ε := by linarith

/-- **Derivatives converge weakly against fields of linear maps.** Let `uᵢ` be `C¹` maps on an
open set `Ω` with values in a finite-dimensional space, with derivatives eventually bounded on
every compact subset of `Ω`, converging locally uniformly on `Ω` to `v`. Then for every field `A`
of linear maps into a finite-dimensional space, continuous on `Ω` with compact support in `Ω`,
and every direction `w`, `∫ A (∂_w uᵢ) → ∫ A (∂_w v)`. -/
theorem tendsto_integral_apply_fderiv_apply_of_tendstoLocallyUniformlyOn [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] [l.NeBot] (hΩ : IsOpen Ω) (hu : ∀ i, ContDiffOn ℝ 1 (u i) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ᶠ i in l, ∀ x ∈ K, ‖fderiv ℝ (u i) x‖ ≤ C)
    (hlim : TendstoLocallyUniformlyOn u v l Ω) {A : E → F →L[ℝ] G} (hA : ContinuousOn A Ω)
    (hAc : HasCompactSupport A) (hAΩ : tsupport A ⊆ Ω) (w : E) :
    Tendsto (fun i ↦ ∫ x, A x (fderiv ℝ (u i) x w) ∂μ) l (𝓝 (∫ x, A x (fderiv ℝ v x w) ∂μ)) := by
  have hv := locallyLipschitzOn_of_tendsto hΩ
    (Eventually.of_forall fun i ↦ (hu i).differentiableOn one_ne_zero) hbd
    fun _ hx ↦ hlim.tendsto_at hx
  -- Expand `A` in a basis `b` of `F →L[ℝ] G`, with continuous coordinate functions `c j`.
  set b := Module.finBasis ℝ (F →L[ℝ] G)
  have hAcont : Continuous A := hA.continuous_of_tsupport_subset hΩ hAΩ
  set c : Fin (Module.finrank ℝ (F →L[ℝ] G)) → E → ℝ := fun j x ↦ b.coord j (A x)
  have hc : ∀ j, Continuous (c j) := fun j ↦
    (LinearMap.continuous_of_finiteDimensional (b.coord j)).comp hAcont
  have hcc : ∀ j, HasCompactSupport (c j) := fun j ↦ hAc.comp_left (map_zero _)
  have hcΩ : ∀ j, tsupport (c j) ⊆ Ω := fun j ↦
    (tsupport_comp_subset (map_zero (b.coord j)) A).trans hAΩ
  have hsum : ∀ {h : E → F}, LocallyIntegrableOn h Ω μ →
      ∫ x, A x (h x) ∂μ = ∑ j, b j (∫ x, c j x • h x ∂μ) := fun {h} hh ↦ by
    have hint : ∀ j, Integrable (fun x ↦ c j x • h x) μ := fun j ↦
      hh.integrable_smul_left_of_hasCompactSupport (hc j) (hcc j) (hcΩ j)
    have hexp : ∀ x, A x (h x) = ∑ j, b j (c j x • h x) := fun x ↦ by
      calc A x (h x) = (∑ j, b.repr (A x) j • b j) (h x) := by rw [b.sum_repr]
        _ = ∑ j, b j (c j x • h x) := by simp [c, -Module.Basis.sum_repr]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ ↦ (b j).integrable_comp (hint j)]
    exact Finset.sum_congr rfl fun j _ ↦ (b j).integral_comp_comm (hint j)
  have hlocv : LocallyIntegrableOn (fun x ↦ fderiv ℝ v x w) Ω μ :=
    (hasWeakFDerivOn_iff.1 (hv.hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⟨Ω, hΩ⟩)) w)
      |>.locallyIntegrableOn_deriv
  rw [hsum hlocv]
  refine (tendsto_finsetSum _ fun j _ ↦ ((b j).continuous.tendsto _).comp
    (tendsto_integral_smul_fderiv_apply_of_tendstoLocallyUniformlyOn hΩ hu hbd hlim (hc j)
      (hcc j) (hcΩ j) w)).congr fun i ↦ ?_
  exact (hsum ((((hu i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
    continuousOn_const).locallyIntegrableOn hΩ.measurableSet)).symm

end WeakConvergence

end TauCeti
