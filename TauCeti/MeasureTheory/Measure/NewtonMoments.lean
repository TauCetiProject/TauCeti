/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.FiniteMeasure.Basic
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.Probability.Moments.CompactDeterminacy
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.Ascoli
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Measures with small Newton variance are close to their root counting measures

Let `σ = μ - ν` be a signed measure on `ℂ`, given by two finite measures `μ` and `ν` carried by
the closed disc of radius `R`, with total mass `μ(ℂ) - ν(ℂ) = m`. Its moments `Mₖ = ∫ wᵏ dσ`
determine, through Newton's identities, the monic polynomial `P_σ = TauCeti.newtonPolynomial M m`
whose roots `R_σ`, counted with multiplicity, have power sums `M₁, …, Mₘ`. When `σ` is the
counting measure of `m` points, `R_σ` consists of these points. This file proves the
corresponding **compact moment lemma**: if the negative part `ν` has small mass and the *Newton
variance* `∫ |P_σ(w)|² dμ(w)` is small, then `σ` is uniformly close, in the bounded-Lipschitz
distance, to the counting measure `∑_{V ∈ R_σ} δ_V` of the roots of `P_σ`
(`TauCeti.exists_forall_abs_integral_sub_sum_roots_le`). The tolerance depends only on `m`, `R`
and the required accuracy; no rate is asserted. The same holds against any fixed continuous test
function (`TauCeti.exists_forall_norm_integral_sub_sum_roots_le`), for instance the mixed
monomials `wˡ * conj w`, which compares the mixed moments `∫ wˡ * conj w dσ` with
`∑_{V ∈ R_σ} Vˡ * conj V`.

In the large-parameter analysis of the Seiberg–Witten equations near a pseudoholomorphic curve,
`σ` is the normalized curvature density on a normal disc, and these statements identify it with
the counting measure of the algebraic roots of its moment polynomial, uniformly over the
fibres.

The proof is by compactness. Along an ultrafilter, the measures `μ` and the root counting
measures converge narrowly (Prokhorov's theorem on a disc), the moments and the coefficients of
`P_σ` converge, and both limits are carried by the finitely many roots of the limiting
polynomial: for `μ` because the limiting Newton variance vanishes, for the roots by continuity.
Both limits have the same first `m` moments, so they agree by the invertibility of the Vandermonde
matrix (`TauCeti.Measure.ext_of_forall_lt_card_integral_pow_eq_of_support`, in
`TauCeti.Probability.Moments.CompactDeterminacy`).

## Main results

* `TauCeti.exists_forall_abs_integral_sub_sum_roots_le`: the compact moment lemma, in the
  bounded-Lipschitz distance.
* `TauCeti.exists_forall_norm_integral_sub_sum_roots_le`: the same against a fixed continuous
  test function.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Metric Set Polynomial
open scoped NNReal BoundedContinuousFunction

namespace TauCeti

/-! ### The compactness argument -/

/-- The lower coefficients of `newtonPolynomial M m` (`TauCeti.newtonPolynomial_eq_monicOfCoeff`)
depend continuously on `M`. -/
private lemma continuous_newtonPolynomial_lowerCoeff (m : ℕ) :
    Continuous fun (M : ℕ → ℂ) (i : Fin m) => (-1 : ℂ) ^ (m - i) * newtonCoeff M (m - i) :=
  continuous_pi fun _ => continuous_const.mul (continuous_newtonCoeff _)

/-- The roots of the Newton polynomials of a convergent family of sequences stay in a bounded
set, by Cauchy's bound `TauCeti.Polynomial.norm_lt_of_isRoot_monicOfCoeff`. -/
private lemma exists_eventually_forall_mem_roots_norm_le {ι : Type*} {L : Filter ι}
    {M : ι → ℕ → ℂ} {M₀ : ℕ → ℂ} (hM : Tendsto M L (𝓝 M₀)) (m : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ᶠ i in L, ∀ r ∈ (newtonPolynomial (M i) m).roots, ‖r‖ ≤ B := by
  have hc := continuous_newtonPolynomial_lowerCoeff m
  refine ⟨‖fun i : Fin m => (-1 : ℂ) ^ (m - i) * newtonCoeff M₀ (m - i)‖ + 2, by positivity, ?_⟩
  filter_upwards [(((continuous_norm.comp hc).tendsto M₀).comp hM).eventually
    (eventually_le_nhds (lt_add_one _))] with i hi r hr
  have hroot := (mem_roots (monic_newtonPolynomial (M i) m).ne_zero).1 hr
  rw [newtonPolynomial_eq_monicOfCoeff] at hroot
  have := Polynomial.norm_lt_of_isRoot_monicOfCoeff _ hroot
  simp only [Function.comp_apply] at hi
  linarith

/-- The Newton variance integrands `|P_M(w)|²` of a convergent family of sequences `M` converge
uniformly on discs. -/
private lemma tendstoUniformlyOn_norm_eval_newtonPolynomial_sq {ι : Type*} {L : Filter ι}
    {M : ι → ℕ → ℂ} {M₀ : ℕ → ℂ} (hM : Tendsto M L (𝓝 M₀)) (m : ℕ) (B : ℝ) :
    TendstoUniformlyOn (fun i w => ‖(newtonPolynomial (M i) m).eval w‖ ^ 2)
      (fun w => ‖(newtonPolynomial M₀ m).eval w‖ ^ 2) L (closedBall 0 B) := by
  have hΦ : Continuous fun q : (ℕ → ℂ) × ℂ => (newtonPolynomial q.1 m).eval q.2 := by
    simp_rw [newtonPolynomial_eq_monicOfCoeff]
    exact continuousOn_univ.1 (Polynomial.continuousOn_eval_monicOfCoeff _
      ((continuous_newtonPolynomial_lowerCoeff m).comp continuous_fst).continuousOn
      continuous_snd.continuousOn)
  exact Continuous.tendstoUniformlyOn_of_tendsto
    (Φ := fun M w => ‖(newtonPolynomial M m).eval w‖ ^ 2) ((continuous_norm.comp hΦ).pow 2)
    (isCompact_closedBall 0 B) hM

/-- On the disc of radius `R`, the powers `wᵏ` are bounded by `Rᵏ`. -/
private lemma norm_pow_le_of_mem_closedBall {R : ℝ} {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) R)
    (k : ℕ) : ‖w ^ k‖ ≤ R ^ k := by
  rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hw) k

/-- Integrals against measures `ν i` carried by the disc of radius `R`, whose masses tend to zero,
of functions eventually bounded on that disc by a common constant tend to zero. -/
private lemma tendsto_integral_of_tendsto_measureReal_univ {𝕜 ι : Type*} [RCLike 𝕜]
    {L : Filter ι} {R : ℝ} {ν : ι → Measure ℂ} [∀ i, IsFiniteMeasure (ν i)]
    (hνR : ∀ i, ν i (closedBall 0 R)ᶜ = 0) (hν : Tendsto (fun i => (ν i).real univ) L (𝓝 0))
    {f : ι → ℂ → 𝕜} {C : ℝ} (hf : ∀ᶠ i in L, ∀ w ∈ closedBall (0 : ℂ) R, ‖f i w‖ ≤ C) :
    Tendsto (fun i => ∫ w, f i w ∂ν i) L (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using hν.const_mul C)
  filter_upwards [hf] with i hi
  have hνae : ∀ᵐ w ∂ν i, w ∈ closedBall (0 : ℂ) R := mem_ae_iff.2 (hνR i)
  exact norm_integral_le_of_norm_le_const (hνae.mono hi)

/-- The moments of the signed measures `μ i - ν i`, carried by a disc and of eventually bounded
masses, converge along an ultrafilter. -/
private lemma exists_tendsto_moments {ι : Type*} {U : Ultrafilter ι} {R : ℝ} (hR : 0 ≤ R)
    {μ ν : ι → Measure ℂ} [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (hμR : ∀ i, μ i (closedBall 0 R)ᶜ = 0) (hνR : ∀ i, ν i (closedBall 0 R)ᶜ = 0) {C : ℝ}
    (hC : ∀ᶠ i in U, (μ i).real univ ≤ C ∧ (ν i).real univ ≤ C) :
    ∃ M₀ : ℕ → ℂ, Tendsto (fun i k => ∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i) U (𝓝 M₀) := by
  have hμae (i : ι) : ∀ᵐ w ∂μ i, w ∈ closedBall (0 : ℂ) R := mem_ae_iff.2 (hμR i)
  have hνae (i : ι) : ∀ᵐ w ∂ν i, w ∈ closedBall (0 : ℂ) R := mem_ae_iff.2 (hνR i)
  have hlim (k : ℕ) : ∃ c, Tendsto (fun i => ∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i) U (𝓝 c) := by
    obtain ⟨c, -, hc⟩ := IsCompact.exists_tendsto_of_eventually_mem (U := U)
      (isCompact_closedBall (0 : ℂ) (2 * C * R ^ k)) <| hC.mono fun i hi => by
        rw [mem_closedBall_zero_iff]
        calc ‖∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i‖
            ≤ ‖∫ w, w ^ k ∂μ i‖ + ‖∫ w, w ^ k ∂ν i‖ := norm_sub_le _ _
          _ ≤ R ^ k * (μ i).real univ + R ^ k * (ν i).real univ :=
            add_le_add (norm_integral_le_of_norm_le_const
                ((hμae i).mono fun _ hw => norm_pow_le_of_mem_closedBall hw k))
              (norm_integral_le_of_norm_le_const
                ((hνae i).mono fun _ hw => norm_pow_le_of_mem_closedBall hw k))
          _ ≤ 2 * C * R ^ k := by nlinarith [pow_nonneg hR k]
    exact ⟨c, hc⟩
  choose M₀ hM₀ using hlim
  exact ⟨M₀, tendsto_pi_nhds.2 hM₀⟩

/-- The compactness core of the moment lemma, along an ultrafilter: if the negative masses and the
Newton variances tend to zero, then the signed measures and the root counting measures have the
same limit against test functions converging uniformly on discs. -/
private theorem tendsto_integral_sub_sum_roots {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {U : Ultrafilter ι} {m : ℕ} {R : ℝ} (hR : 0 ≤ R) {μ ν : ι → Measure ℂ}
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (hμR : ∀ i, μ i (closedBall 0 R)ᶜ = 0) (hνR : ∀ i, ν i (closedBall 0 R)ᶜ = 0)
    (hmass : ∀ i, (μ i).real univ - (ν i).real univ = m)
    (hν : Tendsto (fun i => (ν i).real univ) U (𝓝 0))
    (hvar : Tendsto (fun i => ∫ w, ‖(newtonPolynomial
      (fun k => ∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i) m).eval w‖ ^ 2 ∂μ i) U (𝓝 0))
    {f : ι → ℂ → 𝕜} {g : ℂ → 𝕜} (hf : ∀ i, Continuous (f i)) (hg : Continuous g)
    (hfg : ∀ B, TendstoUniformlyOn f g U (closedBall 0 B)) :
    Tendsto (fun i => ∫ w, f i w ∂μ i - ∫ w, f i w ∂ν i - ((newtonPolynomial
      (fun k => ∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i) m).roots.map (f i)).sum) U (𝓝 0) := by
  set M : ι → ℕ → ℂ := fun i k => ∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i
  set P : ι → ℂ[X] := fun i => newtonPolynomial (M i) m
  have hν1 : ∀ᶠ i in U, (ν i).real univ ≤ 1 := hν.eventually (eventually_le_nhds one_pos)
  have hμmass : ∀ i, (μ i).real univ = m + (ν i).real univ := fun i => by linarith [hmass i]
  -- Step 1: the moments converge along `U`, to `M₀` say.
  obtain ⟨M₀, hM⟩ := exists_tendsto_moments hR hμR hνR (C := m + 1) <|
    hν1.mono fun i hi => ⟨by rw [hμmass]; linarith, by linarith⟩
  set P₀ := newtonPolynomial M₀ m
  -- Step 2: the Newton variance integrands converge uniformly on discs, and the roots stay in a
  -- disc of radius `B`, which we take to contain the supports of the `μ i`.
  have hP2 := tendstoUniformlyOn_norm_eval_newtonPolynomial_sq hM m
  have hP₀cont : Continuous fun w => ‖P₀.eval w‖ ^ 2 := (continuous_norm.comp P₀.continuous).pow 2
  have hPcont (i : ι) : Continuous fun w => ‖(P i).eval w‖ ^ 2 :=
    (continuous_norm.comp (P i).continuous).pow 2
  obtain ⟨B₀, hB₀, hroots⟩ := exists_eventually_forall_mem_roots_norm_le hM m
  set B := max B₀ R
  have hBK : IsCompact (closedBall (0 : ℂ) B) := isCompact_closedBall 0 B
  -- Step 3: by Prokhorov's theorem, the measures `μ i` and the root counting measures `τ i`
  -- converge narrowly, to limits `ρ` and `ρ'` carried by the disc of radius `B`.
  let μf : ι → FiniteMeasure ℂ := fun i => ⟨μ i, inferInstance⟩
  let τ : ι → Measure ℂ := fun i => ((P i).roots.map Measure.dirac).sum
  let τf : ι → FiniteMeasure ℂ := fun i => ⟨τ i, inferInstance⟩
  have hμB (i : ι) : μ i (closedBall 0 B)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall (le_max_right _ _)))
      (hμR i)
  have hτB : ∀ᶠ i in U, τ i (closedBall 0 B)ᶜ = 0 := hroots.mono fun i hi =>
    Multiset.sum_map_dirac_apply_eq_zero measurableSet_closedBall.compl fun z hz hzB =>
      hzB (mem_closedBall_zero_iff.2 ((hi z hz).trans (le_max_left _ _)))
  obtain ⟨ρ, hρB, hρ⟩ := exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero
    (μs := μf) hBK (C := m + 1) <| hν1.mono fun i hi => ⟨hμB i, by
      simp only [μf, FiniteMeasure.toMeasure_mk, hμmass]; linarith⟩
  obtain ⟨ρ', hρ'B, hρ'⟩ := exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero
    (μs := τf) hBK (C := m) <| hτB.mono fun i hi => ⟨hi, by simp [τf, τ, P]⟩
  -- Integrals against `μ i` and `τ i` of functions converging uniformly on the disc converge, by
  -- `FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall`.
  have hconst {h : ℂ → ℂ} : TendstoUniformlyOn (fun _ : ι => h) h U (closedBall 0 B) :=
    fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu
  -- Step 4: `ρ` and `ρ'` have the same moments of order at most `m`, namely `M₀`.
  have hρmom (k : ℕ) : ∫ w, w ^ k ∂(ρ : Measure ℂ) = M₀ k := by
    have hνk : Tendsto (fun i => ∫ w, w ^ k ∂ν i) U (𝓝 0) :=
      tendsto_integral_of_tendsto_measureReal_univ hνR hν
        (.of_forall fun _ _ hw => norm_pow_le_of_mem_closedBall hw k)
    refine tendsto_nhds_unique (FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hρ
      (.of_forall hμB) (fun _ => (continuous_pow k).continuousOn)
      (continuous_pow k).continuousOn hconst) ?_
    simpa [M, μf] using ((tendsto_pi_nhds.1 hM k).add hνk)
  have hρ'mom (k : ℕ) (hk : k ≤ m) : ∫ w, w ^ k ∂(ρ' : Measure ℂ) = M₀ k := by
    refine tendsto_nhds_unique (FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hρ'
      hτB (fun _ => (continuous_pow k).continuousOn) (continuous_pow k).continuousOn hconst)
      ((tendsto_pi_nhds.1 hM k).congr fun i => ?_)
    simp only [τf, τ, FiniteMeasure.toMeasure_mk, Multiset.integral_sum_map_dirac]
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · have := hmass i
      simp only [M, P, pow_zero, integral_const, Complex.real_smul, mul_one, Multiset.map_const',
        Multiset.sum_replicate, nsmul_eq_mul, card_roots_newtonPolynomial]
      exact_mod_cast this
    · exact (sum_map_pow_roots_newtonPolynomial (M i) hk₀ hk).symm
  -- Step 5: both limits have vanishing Newton variance for the limiting polynomial `P₀`, since the
  -- variances of the `μ i` tend to zero and those of the `τ i` vanish.
  have hρvar : ∫ w, ‖P₀.eval w‖ ^ 2 ∂(ρ : Measure ℂ) = 0 :=
    tendsto_nhds_unique (FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hρ
      (.of_forall hμB) (fun i => (hPcont i).continuousOn) hP₀cont.continuousOn (hP2 B)) hvar
  have hρ'var : ∫ w, ‖P₀.eval w‖ ^ 2 ∂(ρ' : Measure ℂ) = 0 := by
    refine tendsto_nhds_unique (FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hρ'
      hτB (fun i => (hPcont i).continuousOn) hP₀cont.continuousOn (hP2 B))
      (tendsto_const_nhds.congr fun i => ?_)
    simp only [τf, τ, FiniteMeasure.toMeasure_mk, Multiset.integral_sum_map_dirac]
    refine (Multiset.sum_eq_zero fun x hx => ?_).symm
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hr₀ : (P i).eval r = 0 :=
      ((mem_roots (monic_newtonPolynomial (M i) m).ne_zero).1 hr).eq_zero
    simp [hr₀]
  -- Step 6: so both are carried by the at most `m` roots of `P₀`, and they agree.
  have hP₀ : P₀ ≠ 0 := (monic_newtonPolynomial M₀ m).ne_zero
  have hcard : P₀.roots.toFinset.card ≤ m :=
    (Multiset.toFinset_card_le _).trans (card_roots_newtonPolynomial M₀ m).le
  have hroots₀ {ρ₀ : Measure ℂ} [IsFiniteMeasure ρ₀] (hρ₀B : ρ₀ (closedBall 0 B)ᶜ = 0)
      (hρ₀var : ∫ w, ‖P₀.eval w‖ ^ 2 ∂ρ₀ = 0) : ρ₀ (↑P₀.roots.toFinset)ᶜ = 0 := by
    refine MeasureTheory.measure_compl_roots_eq_zero_of_integral_norm_eval_sq_eq_zero hP₀ ?_ hρ₀var
    rw [← Measure.restrict_eq_self_of_ae_mem (s := closedBall 0 B) (mem_ae_iff.2 hρ₀B)]
    exact hP₀cont.continuousOn.integrableOn_compact hBK
  have hρρ' : (ρ : Measure ℂ) = ρ' := Measure.ext_of_forall_lt_card_integral_pow_eq_of_support
    P₀.roots.toFinset (hroots₀ hρB hρvar) (hroots₀ hρ'B hρ'var) fun k hk => by
      rw [hρmom k, hρ'mom k (by omega)]
  -- Step 7: compare the three terms with their limits; the integrals against `ν i` vanish in the
  -- limit, as the `f i` are eventually bounded on the disc of radius `R`.
  have hT₁ : Tendsto (fun i => ∫ w, f i w ∂μ i) U (𝓝 (∫ w, g w ∂(ρ : Measure ℂ))) :=
    FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hρ (.of_forall hμB)
      (fun i => (hf i).continuousOn) hg.continuousOn (hfg B)
  have hT₂ : Tendsto (fun i => ∫ w, f i w ∂ν i) U (𝓝 0) := by
    obtain ⟨Cg, hCg⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hg.continuousOn
    refine tendsto_integral_of_tendsto_measureReal_univ hνR hν (C := Cg + 1) ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hfg R) 1 one_pos] with i hi w hw
    have h1 := hi w hw
    rw [dist_comm, dist_eq_norm] at h1
    linarith [norm_le_norm_add_norm_sub' (f i w) (g w), hCg w hw]
  have hT₃ : Tendsto (fun i => ((P i).roots.map (f i)).sum) U
      (𝓝 (∫ w, g w ∂(ρ' : Measure ℂ))) :=
    (FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hρ' hτB
      (fun i => (hf i).continuousOn) hg.continuousOn (hfg B)).congr fun i => by
      simp [τf, τ, Multiset.integral_sum_map_dirac]
  simpa [hρρ'] using (hT₁.sub hT₂).sub hT₃

/-- The sequential form of the compactness core used by both public statements: for data whose
negative masses and Newton variances are at most `1 / (n + 1)`, some index satisfies any required
accuracy, against test functions converging uniformly on discs along an ultrafilter. -/
private lemma exists_norm_integral_sub_sum_roots_lt {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {R : ℝ}
    {μ ν : ℕ → Measure ℂ} [∀ n, IsFiniteMeasure (μ n)] [∀ n, IsFiniteMeasure (ν n)]
    (hμR : ∀ n, μ n (closedBall 0 R)ᶜ = 0) (hνR : ∀ n, ν n (closedBall 0 R)ᶜ = 0)
    (hmass : ∀ n, (μ n).real univ - (ν n).real univ = m)
    (hνδ : ∀ n, (ν n).real univ ≤ 1 / (n + 1))
    (hvar : ∀ n, ∫ w, ‖(newtonPolynomial
      (fun k => ∫ w, w ^ k ∂μ n - ∫ w, w ^ k ∂ν n) m).eval w‖ ^ 2 ∂μ n ≤ 1 / (n + 1))
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop) {f : ℕ → ℂ → 𝕜} {g : ℂ → 𝕜}
    (hf : ∀ n, Continuous (f n)) (hg : Continuous g)
    (hfg : ∀ B, TendstoUniformlyOn f g U (closedBall 0 B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ‖∫ w, f n w ∂μ n - ∫ w, f n w ∂ν n - ((newtonPolynomial
      (fun k => ∫ w, w ^ k ∂μ n - ∫ w, w ^ k ∂ν n) m).roots.map (f n)).sum‖ < ε := by
  have hsub : (closedBall (0 : ℂ) (max R 0))ᶜ ⊆ (closedBall 0 R)ᶜ :=
    compl_subset_compl.2 (closedBall_subset_closedBall (le_max_left _ _))
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) U (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hU
  have h := tendsto_integral_sub_sum_roots (U := U) (le_max_right R 0)
    (fun n => measure_mono_null hsub (hμR n)) (fun n => measure_mono_null hsub (hνR n)) hmass
    (squeeze_zero (fun n => measureReal_nonneg) hνδ hδ)
    (squeeze_zero (fun n => integral_nonneg fun w => by positivity) hvar hδ) hf hg hfg
  simpa using (Metric.tendsto_nhds.1 h ε hε).exists

/-- **The compact moment lemma.** For every accuracy `ε > 0` there is a tolerance `δ > 0`,
depending only on `m`, `R` and `ε`, with the following property. Let `σ = μ - ν` be a signed
measure on `ℂ`, given by finite measures `μ`, `ν` carried by the closed disc of radius `R`,
with total mass `μ(ℂ) - ν(ℂ) = m`, negative mass `ν(ℂ) ≤ δ`, and Newton variance
`∫ |P(w)|² dμ(w) ≤ δ`, where `P` is the Newton polynomial of degree `m` of the moments
`∫ wᵏ dσ`. Then for every `1`-Lipschitz `f : ℂ → ℝ` bounded by `1`, the integral of `f`
against `σ` is within `ε` of the sum of `f` over the roots of `P`, counted with multiplicity.
That is, `σ` is within `ε` of the counting measure of these roots in the bounded-Lipschitz
distance. -/
theorem exists_forall_abs_integral_sub_sum_roots_le (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      μ (closedBall 0 R)ᶜ = 0 → ν (closedBall 0 R)ᶜ = 0 →
      μ.real univ - ν.real univ = m → ν.real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k => ∫ w, w ^ k ∂μ - ∫ w, w ^ k ∂ν) m).eval w‖ ^ 2 ∂μ ≤ δ →
      ∀ f : ℂ → ℝ, LipschitzWith 1 f → (∀ w, |f w| ≤ 1) →
        |∫ w, f w ∂μ - ∫ w, f w ∂ν -
          ((newtonPolynomial (fun k => ∫ w, w ^ k ∂μ - ∫ w, w ^ k ∂ν) m).roots.map f).sum| ≤
          ε := by
  by_contra! h
  choose μ ν hμ hν hμR hνR hmass hνδ hvar f hfL hfb hfε using
    fun n : ℕ => h (1 / (n + 1)) Nat.one_div_pos_of_nat
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  -- The test functions have a pointwise limit along `U`, which is `1`-Lipschitz.
  have hlim (w : ℂ) : ∃ c, Tendsto (fun n => f n w) U (𝓝 c) := by
    obtain ⟨c, -, hc⟩ := (isCompact_Icc (a := -1) (b := 1)).exists_tendsto_of_eventually_mem
      (U := U) (Eventually.of_forall fun n => abs_le.1 (hfb n w))
    exact ⟨c, hc⟩
  choose g hg using hlim
  have hgL : LipschitzWith 1 g := LipschitzWith.of_dist_le_mul fun x y =>
    le_of_tendsto ((hg x).dist (hg y)) (Eventually.of_forall fun n => (hfL n).dist_le_mul x y)
  obtain ⟨n, hn⟩ := exists_norm_integral_sub_sum_roots_lt hμR hνR hmass hνδ hvar
    (Ultrafilter.of_le atTop) (fun n => (hfL n).continuous) hgL.continuous
    (fun B => ((LipschitzWith.uniformEquicontinuous f 1 hfL).equicontinuous.equicontinuousOn
      _).tendstoUniformlyOn_of_tendsto (isCompact_closedBall 0 B) fun w _ => hg w) hε
  exact (hfε n).not_gt hn

/-- **The compact moment lemma against a fixed continuous test function.** For a continuous
`g : ℂ → 𝕜` and every accuracy `ε > 0` there is a tolerance `δ > 0`, depending only on `g`, `m`,
`R` and `ε`, with the following property. If `σ = μ - ν` is a signed measure on `ℂ`, given by
finite measures `μ`, `ν` carried by the closed disc of radius `R`, with total mass `m`, negative
mass `ν(ℂ)` at most `δ` and Newton variance `∫ |P(w)|² dμ(w)` at most `δ`, then the integral of
`g` against `σ` is within `ε` of the sum of `g` over the roots of `P`. For
`g(w) = wˡ * conj w` this compares the mixed moments of `σ` with those of the roots. -/
theorem exists_forall_norm_integral_sub_sum_roots_le {𝕜 : Type*} [RCLike 𝕜] (m : ℕ) (R : ℝ)
    {g : ℂ → 𝕜} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      μ (closedBall 0 R)ᶜ = 0 → ν (closedBall 0 R)ᶜ = 0 →
      μ.real univ - ν.real univ = m → ν.real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k => ∫ w, w ^ k ∂μ - ∫ w, w ^ k ∂ν) m).eval w‖ ^ 2 ∂μ ≤ δ →
        ‖∫ w, g w ∂μ - ∫ w, g w ∂ν -
          ((newtonPolynomial (fun k => ∫ w, w ^ k ∂μ - ∫ w, w ^ k ∂ν) m).roots.map g).sum‖ ≤
          ε := by
  by_contra! h
  choose μ ν hμ hν hμR hνR hmass hνδ hvar hgε using
    fun n : ℕ => h (1 / (n + 1)) Nat.one_div_pos_of_nat
  obtain ⟨n, hn⟩ := exists_norm_integral_sub_sum_roots_lt (f := fun _ => g) hμR hνR hmass hνδ
    hvar (Ultrafilter.of_le atTop) (fun _ => hg) hg
    (fun B u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu) hε
  exact (hgε n).not_gt hn

end TauCeti
