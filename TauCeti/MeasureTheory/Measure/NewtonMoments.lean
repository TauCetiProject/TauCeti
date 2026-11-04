/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Normed.Module.Ball.Retraction

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
`P_μ` converge, and both limits are carried by the finitely many roots of the limiting
polynomial: for `μ` because the limiting Newton variance vanishes, for the roots by continuity.
Both limits have the same first `m` moments, so they agree by the invertibility of the Vandermonde
matrix (`TauCeti.eq_of_integral_pow_eq_of_measure_compl_eq_zero`).

## Main results

* `TauCeti.eq_of_integral_pow_eq_of_measure_compl_eq_zero`: finite measures carried by a finite
  set `Z` are determined by their moments of order less than `card Z`.
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

/-! ### Finitely supported measures are determined by their moments -/

/-- Two finite measures on `𝕜` carried by a finite set `Z` agree as soon as their moments
`∫ wᵏ` agree for `k < card Z`. -/
theorem eq_of_integral_pow_eq_of_measure_compl_eq_zero {𝕜 : Type*} [RCLike 𝕜] {μ ν : Measure 𝕜}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (Z : Finset 𝕜) (hμ : μ (↑Z)ᶜ = 0) (hν : ν (↑Z)ᶜ = 0)
    (h : ∀ k < Z.card, ∫ w, w ^ k ∂μ = ∫ w, w ^ k ∂ν) : μ = ν := by
  classical
  -- Integrals against a measure carried by `Z` are finite sums over `Z`.
  have hsum (ρ : Measure 𝕜) [IsFiniteMeasure ρ] (hρ : ρ (↑Z)ᶜ = 0) (k : ℕ) :
      ∫ w, w ^ k ∂ρ = ∑ z ∈ Z, (ρ.real {z} : 𝕜) * z ^ k := by
    calc ∫ w, w ^ k ∂ρ = ∫ w in (Z : Set 𝕜), w ^ k ∂ρ := by
          rw [Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hρ)]
      _ = ∑ z ∈ Z, ρ.real {z} • z ^ k := setIntegral_finset Z
          ((continuous_pow k).continuousOn.integrableOn_compact Z.finite_toSet.isCompact)
      _ = _ := by simp [RCLike.real_smul_eq_coe_mul]
  -- The point masses agree, by the invertibility of the Vandermonde matrix.
  have hpt : ∀ z ∈ Z, μ.real {z} = ν.real {z} := by
    let e : Fin Z.card ≃ Z := Z.equivFin.symm
    have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun j => (e j : 𝕜))
      (v := fun j => (μ.real {(e j : 𝕜)} : 𝕜) - ν.real {(e j : 𝕜)})
      (fun a b hab => e.injective (Subtype.ext hab)) fun i => by
        have hi := h i i.2
        rw [hsum μ hμ, hsum ν hν, ← sub_eq_zero, ← Finset.sum_sub_distrib] at hi
        rw [← hi]
        refine (Finset.sum_congr rfl fun j _ => sub_mul _ _ _).trans <|
          (e.sum_comp fun z : Z => (μ.real {(z : 𝕜)} : 𝕜) * (z : 𝕜) ^ (i : ℕ) -
            ν.real {(z : 𝕜)} * (z : 𝕜) ^ (i : ℕ)).trans (Finset.sum_coe_sort Z fun z =>
              (μ.real {z} : 𝕜) * z ^ (i : ℕ) - ν.real {z} * z ^ (i : ℕ))
    intro z hz
    have := congrFun hv (e.symm ⟨z, hz⟩)
    simpa [sub_eq_zero] using this
  ext s hs
  have hfin (ρ : Measure 𝕜) (hρ : ρ (↑Z)ᶜ = 0) :
      ρ s = ρ ↑({z ∈ Z | z ∈ s} : Finset 𝕜) := by
    have hres := Measure.restrict_eq_self_of_ae_mem (μ := ρ) (s := (Z : Set 𝕜)) (mem_ae_iff.2 hρ)
    calc ρ s = ρ.restrict Z s := by rw [hres]
      _ = ρ (s ∩ Z) := Measure.restrict_apply hs
      _ = _ := congrArg ρ (by ext w; simp [and_comm])
  rw [hfin μ hμ, hfin ν hν, ← sum_measure_singleton, ← sum_measure_singleton]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  exact hpt z (Finset.mem_filter.1 hz).1

/-! ### Measures carried by a compact set -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private lemma integrable_of_measure_compl_eq_zero {μ : Measure ℂ} [IsFiniteMeasure μ]
    {K : Set ℂ} (hK : IsCompact K) (hμ : μ Kᶜ = 0) {f : ℂ → E} (hf : Continuous f) :
    Integrable f μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμ)]
  exact hf.continuousOn.integrableOn_compact hK

private lemma norm_integral_le_of_measure_compl_eq_zero {μ : Measure ℂ} [IsFiniteMeasure μ]
    {K : Set ℂ} (hμ : μ Kᶜ = 0) {f : ℂ → E} {C : ℝ} (hf : ∀ w ∈ K, ‖f w‖ ≤ C) :
    ‖∫ w, f w ∂μ‖ ≤ C * μ.real univ :=
  norm_integral_le_of_norm_le_const ((show ∀ᵐ w ∂μ, w ∈ K from mem_ae_iff.2 hμ).mono hf)

/-- If finite measures carried by a closed disc converge narrowly, then their integrals of every
continuous function converge. -/
private lemma tendsto_integral_of_tendsto {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure ℂ} {μ : FiniteMeasure ℂ} (h : Tendsto μs L (𝓝 μ)) {B : ℝ}
    (hB : 0 ≤ B) (hμs : ∀ᶠ i in L, (μs i : Measure ℂ) (closedBall 0 B)ᶜ = 0)
    (hμ : (μ : Measure ℂ) (closedBall 0 B)ᶜ = 0) {g : ℂ → 𝕜} (hg : Continuous g) :
    Tendsto (fun i => ∫ w, g w ∂(μs i : Measure ℂ)) L (𝓝 (∫ w, g w ∂(μ : Measure ℂ))) := by
  -- Replace `g` by the bounded continuous function `g ∘ r`, with `r` the radial retraction onto
  -- the disc; it has the same integrals against measures carried by the disc.
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn hg.continuousOn
  have hr : Continuous (radialRetraction B : ℂ → ℂ) :=
    (lipschitzWith_radialRetraction hB).continuous
  let G : ℂ →ᵇ 𝕜 := BoundedContinuousFunction.mkOfBound ⟨g ∘ radialRetraction B, hg.comp hr⟩
    (2 * C) fun x y => by
      have hx := hC _ (radialRetraction_mem_closedBall hB x)
      have hy := hC _ (radialRetraction_mem_closedBall hB y)
      calc dist (g (radialRetraction B x)) (g (radialRetraction B y))
          ≤ ‖g (radialRetraction B x)‖ + ‖g (radialRetraction B y)‖ := dist_le_norm_add_norm _ _
        _ ≤ 2 * C := by linarith
  have key (ρ : Measure ℂ) (hρ : ρ (closedBall 0 B)ᶜ = 0) : ∫ w, G w ∂ρ = ∫ w, g w ∂ρ :=
    integral_congr_ae ((show ∀ᵐ w ∂ρ, w ∈ closedBall 0 B from mem_ae_iff.2 hρ).mono fun w hw => by
      simp [G, radialRetraction_of_norm_le (mem_closedBall_zero_iff.1 hw)])
  rw [← key _ hμ]
  exact (tendsto_congr' (hμs.mono fun i hi => key _ hi)).1
    ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).1 h G)

/-- Integrals of uniformly convergent continuous functions against finite measures of bounded mass
carried by a compact set are asymptotically equal. -/
private lemma tendsto_integral_sub_integral {ι : Type*} {L : Filter ι} {μ : ι → Measure ℂ}
    [∀ i, IsFiniteMeasure (μ i)] {K : Set ℂ} (hK : IsCompact K) {C : ℝ}
    (hμ : ∀ᶠ i in L, μ i Kᶜ = 0 ∧ (μ i).real univ ≤ C) {F : ι → ℂ → E} {G : ℂ → E}
    (hF : ∀ i, Continuous (F i)) (hG : Continuous G) (hFG : TendstoUniformlyOn F G L K) :
    Tendsto (fun i => ∫ w, F i w ∂μ i - ∫ w, G w ∂μ i) L (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC : 0 < max C 0 + 1 := by positivity
  filter_upwards [hμ, Metric.tendstoUniformlyOn_iff.1 hFG (ε / (max C 0 + 1)) (by positivity)]
    with i hi hFi
  rw [dist_zero_right, ← integral_sub (integrable_of_measure_compl_eq_zero hK hi.1 (hF i))
    (integrable_of_measure_compl_eq_zero hK hi.1 hG)]
  calc ‖∫ w, F i w - G w ∂μ i‖ ≤ ε / (max C 0 + 1) * (μ i).real univ :=
        norm_integral_le_of_measure_compl_eq_zero hi.1 fun w hw => by
          rw [← dist_eq_norm, dist_comm]
          exact (hFi w hw).le
    _ ≤ ε / (max C 0 + 1) * max C 0 := by gcongr; exact hi.2.trans (le_max_left _ _)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hC]
      nlinarith [le_max_right C 0]

end Compact

/-! ### Counting measures of multisets -/

section Dirac

private lemma isFiniteMeasure_sum_dirac (s : Multiset ℂ) :
    IsFiniteMeasure (s.map Measure.dirac).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.sum_zero]; infer_instance
  | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons]; infer_instance

private lemma measureReal_univ_sum_dirac (s : Multiset ℂ) :
    (s.map Measure.dirac).sum.real univ = Multiset.card s := by
  rw [measureReal_def]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have := isFiniteMeasure_sum_dirac s
    rw [Multiset.map_cons, Multiset.sum_cons, add_apply, measure_univ,
      ENNReal.toReal_add ENNReal.one_ne_top (measure_ne_top _ _), ih]
    simp [add_comm]

private lemma sum_dirac_compl_eq_zero {s : Multiset ℂ} {K : Set ℂ} (hK : MeasurableSet K)
    (hs : ∀ z ∈ s, z ∈ K) : (s.map Measure.dirac).sum Kᶜ = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, add_apply,
      ih fun z hz => hs z (Multiset.mem_cons_of_mem hz), add_zero,
      Measure.dirac_apply' _ hK.compl]
    simp [hs a (Multiset.mem_cons_self a s)]

private lemma integral_sum_dirac {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : Multiset ℂ) (g : ℂ → E) :
    Integrable g (s.map Measure.dirac).sum ∧
      ∫ w, g w ∂(s.map Measure.dirac).sum = (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : Integrable g (Measure.dirac a) := integrable_dirac (by simp)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact ⟨ha.add_measure ih.1, by rw [integral_add_measure ha ih.1, integral_dirac, ih.2]⟩

end Dirac

/-! ### The compactness argument -/

private lemma exists_tendsto_of_eventually_mem {X ι : Type*} [TopologicalSpace X]
    {U : Ultrafilter ι} {s : Set X} (hs : IsCompact s) {u : ι → X} (hu : ∀ᶠ i in U, u i ∈ s) :
    ∃ x ∈ s, Tendsto u U (𝓝 x) := by
  obtain ⟨x, hx, h⟩ := hs.ultrafilter_le_nhds (U.map u)
    (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hu)
  exact ⟨x, hx, by rwa [Ultrafilter.coe_map] at h⟩

/-- A jointly continuous family of functions converges uniformly on compact sets when its
parameter converges. -/
private lemma tendstoUniformlyOn_of_continuous {α β F ι : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [UniformSpace F] {Φ : α → β → F} (hΦ : Continuous (Function.uncurry Φ))
    {k : Set β} (hk : IsCompact k) {L : Filter ι} {p : ι → α} {q : α} (hp : Tendsto p L (𝓝 q)) :
    TendstoUniformlyOn (fun i => Φ (p i)) (Φ q) L k := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hk.mem_uniformity_of_prod hΦ.continuousOn (mem_univ q)
    (symm_le_uniformity hu)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hp hv] with i hi x hx
  exact hvu (p i) hi x hx

/-- The roots of the Newton polynomials of a convergent family of sequences stay in a bounded
set. -/
private lemma exists_eventually_forall_mem_roots_norm_le {ι : Type*} {L : Filter ι}
    {M : ι → ℕ → ℂ} {M₀ : ℕ → ℂ} (hM : Tendsto M L (𝓝 M₀)) (m : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ᶠ i in L, ∀ r ∈ (newtonPolynomial (M i) m).roots, ‖r‖ ≤ B := by
  set C : ℝ := ∑ j ∈ Finset.range (m + 1), (‖newtonCoeff M₀ j‖ + 1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => by positivity
  set C' : ℝ≥0 := ⟨C, hC⟩
  refine ⟨C + 1, by positivity, ?_⟩
  have hb : ∀ᶠ i in L, ∀ j ∈ Finset.range (m + 1),
      ‖newtonCoeff (M i) j‖ ≤ ‖newtonCoeff M₀ j‖ + 1 := by
    rw [eventually_all_finset]
    exact fun j _ => (((continuous_norm.comp (continuous_newtonCoeff j)).tendsto M₀).comp
      hM).eventually (eventually_le_nhds (lt_add_one _))
  filter_upwards [hb] with i hi r hr
  have hP := monic_newtonPolynomial (M i) m
  have hlt := (mem_roots hP.ne_zero).1 hr |>.norm_lt_cauchyBound hP.ne_zero
  -- Cauchy's bound is one more than the largest coefficient norm.
  have hsup : (Finset.range (newtonPolynomial (M i) m).natDegree).sup
      (fun n => ‖(newtonPolynomial (M i) m).coeff n‖₊) ≤ C' := by
    refine Finset.sup_le fun n hn => ?_
    rw [natDegree_newtonPolynomial, Finset.mem_range] at hn
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    have hc := coeff_newtonPolynomial_sub (M i) (m := m) (j := m - n) (by omega)
    rw [Nat.sub_sub_self hn.le] at hc
    rw [hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact (hi _ (Finset.mem_range.2 (by omega))).trans
      (Finset.single_le_sum (f := fun j => ‖newtonCoeff M₀ j‖ + 1) (fun j _ => by positivity)
        (Finset.mem_range.2 (by omega)))
  have hle : cauchyBound (newtonPolynomial (M i) m) ≤ C' + 1 := by
    rw [cauchyBound, hP.leadingCoeff, nnnorm_one, div_one]
    exact add_le_add_left hsup 1
  have h := NNReal.coe_le_coe.2 (hlt.le.trans hle)
  rwa [coe_nnnorm, NNReal.coe_add, NNReal.coe_one] at h

/-- A finite measure whose integral of `|p|²` vanishes is carried by the roots of `p`. -/
private lemma measure_compl_roots_eq_zero {ρ : Measure ℂ} [IsFiniteMeasure ρ] {K : Set ℂ}
    (hK : IsCompact K) (hρ : ρ Kᶜ = 0) {p : ℂ[X]} (hp : p ≠ 0)
    (h : ∫ w, ‖p.eval w‖ ^ 2 ∂ρ = 0) : ρ (↑p.roots.toFinset)ᶜ = 0 := by
  have hcont : Continuous fun w => ‖p.eval w‖ ^ 2 := (continuous_norm.comp p.continuous).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun w => by positivity)
    (integrable_of_measure_compl_eq_zero hK hρ hcont)).1 h
  refine measure_mono_null (fun w hw => ?_) (ae_iff.1 hae)
  have hw' : p.eval w ≠ 0 := fun h0 => hw (by simp [mem_roots hp, h0])
  simpa using hw'

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
  classical
  set M : ι → ℕ → ℂ := fun i k => ∫ w, w ^ k ∂μ i - ∫ w, w ^ k ∂ν i with hMdef
  set P : ι → ℂ[X] := fun i => newtonPolynomial (M i) m with hPdef
  have hK : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hν1 : ∀ᶠ i in U, (ν i).real univ ≤ 1 := hν.eventually (eventually_le_nhds one_pos)
  have hμmass : ∀ i, (μ i).real univ = m + (ν i).real univ := fun i => by linarith [hmass i]
  have hpow (k : ℕ) : ∀ w ∈ closedBall (0 : ℂ) R, ‖w ^ k‖ ≤ R ^ k := fun w hw => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hw) k
  -- Step 1: the moments, hence the Newton coefficients, converge along `U`.
  have hlim : ∀ k, ∃ c, Tendsto (fun i => M i k) U (𝓝 c) := fun k => by
    obtain ⟨c, -, hc⟩ := exists_tendsto_of_eventually_mem (U := U)
      (isCompact_closedBall (0 : ℂ) ((m + 2) * R ^ k)) (u := fun i => M i k) <|
      hν1.mono fun i hi => by
        rw [mem_closedBall_zero_iff]
        calc ‖M i k‖ ≤ ‖∫ w, w ^ k ∂μ i‖ + ‖∫ w, w ^ k ∂ν i‖ := norm_sub_le _ _
          _ ≤ R ^ k * (μ i).real univ + R ^ k * (ν i).real univ :=
            add_le_add (norm_integral_le_of_measure_compl_eq_zero (hμR i) (hpow k))
              (norm_integral_le_of_measure_compl_eq_zero (hνR i) (hpow k))
          _ ≤ (m + 2) * R ^ k := by
            rw [hμmass]; nlinarith [pow_nonneg hR k, measureReal_nonneg (μ := ν i) (s := univ)]
    exact ⟨c, hc⟩
  choose M₀ hM₀ using hlim
  have hM : Tendsto M U (𝓝 M₀) := tendsto_pi_nhds.2 hM₀
  have hvar' : Tendsto (fun i => ∫ w, ‖(P i).eval w‖ ^ 2 ∂μ i) U (𝓝 0) := hvar
  set P₀ := newtonPolynomial M₀ m with hP₀def
  -- Step 2: the Newton polynomials converge uniformly on discs, and their roots stay bounded.
  have hΦ : Continuous fun q : (ℕ → ℂ) × ℂ => (newtonPolynomial q.1 m).eval q.2 := by
    simp_rw [eval_newtonPolynomial]
    exact continuous_finsetSum _ fun j _ =>
      (continuous_const.mul ((continuous_newtonCoeff j).comp continuous_fst)).mul
        (continuous_snd.pow _)
  have hP2 (B : ℝ) : TendstoUniformlyOn (fun i w => ‖(P i).eval w‖ ^ 2)
      (fun w => ‖P₀.eval w‖ ^ 2) U (closedBall 0 B) :=
    tendstoUniformlyOn_of_continuous (Φ := fun M w => ‖(newtonPolynomial M m).eval w‖ ^ 2)
      ((continuous_norm.comp hΦ).pow 2) (isCompact_closedBall 0 B) hM
  obtain ⟨B₀, hB₀, hroots⟩ := exists_eventually_forall_mem_roots_norm_le hM m
  set B := max B₀ R
  have hBK : IsCompact (closedBall (0 : ℂ) B) := isCompact_closedBall 0 B
  have hP₀cont : Continuous fun w => ‖P₀.eval w‖ ^ 2 := (continuous_norm.comp P₀.continuous).pow 2
  have hPcont (i : ι) : Continuous fun w => ‖(P i).eval w‖ ^ 2 :=
    (continuous_norm.comp (P i).continuous).pow 2
  -- Step 3: the measures `μ i` and the root counting measures `τ i` converge narrowly.
  let μf : ι → FiniteMeasure ℂ := fun i => ⟨μ i, inferInstance⟩
  let τ : ι → Measure ℂ := fun i => ((P i).roots.map Measure.dirac).sum
  have hτfin : ∀ i, IsFiniteMeasure (τ i) := fun i => isFiniteMeasure_sum_dirac (P i).roots
  let τf : ι → FiniteMeasure ℂ := fun i => ⟨τ i, hτfin i⟩
  have hτmass (i : ι) : (τ i).real univ = m := by
    rw [measureReal_univ_sum_dirac, card_roots_newtonPolynomial]
  have hτB : ∀ᶠ i in U, τ i (closedBall 0 B)ᶜ = 0 := hroots.mono fun i hi =>
    sum_dirac_compl_eq_zero measurableSet_closedBall fun z hz =>
      mem_closedBall_zero_iff.2 ((hi z hz).trans (le_max_left _ _))
  have hμB (i : ι) : μ i (closedBall 0 B)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall (le_max_right _ _)))
      (hμR i)
  have hμC : ∀ᶠ i in U, μ i (closedBall 0 B)ᶜ = 0 ∧ (μ i).real univ ≤ m + 1 :=
    hν1.mono fun i hi => ⟨hμB i, by rw [hμmass]; linarith⟩
  have hτC : ∀ᶠ i in U, τ i (closedBall 0 B)ᶜ = 0 ∧ (τ i).real univ ≤ m :=
    hτB.mono fun i hi => ⟨hi, (hτmass i).le⟩
  obtain ⟨ρ, hρS, hρ⟩ := exists_tendsto_of_eventually_mem (U := U) (u := μf)
    (isCompact_setOfPred_finiteMeasure_le_of_isCompact (m + 1 : ℝ≥0) hBK) <|
    hμC.mono fun i hi => ⟨by
      rw [← NNReal.coe_le_coe, ← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass]
      push_cast
      simp only [μf, FiniteMeasure.toMeasure_mk]
      rw [← measureReal_def]; exact hi.2, by
      rw [FiniteMeasure.null_iff_toMeasure_null]; exact hi.1⟩
  obtain ⟨ρ', hρ'S, hρ'⟩ := exists_tendsto_of_eventually_mem (U := U) (u := τf)
    (isCompact_setOfPred_finiteMeasure_le_of_isCompact (m : ℝ≥0) hBK) <|
    hτB.mono fun i hi => ⟨by
      rw [← NNReal.coe_le_coe, ← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass]
      simp only [τf, FiniteMeasure.toMeasure_mk]
      rw [← measureReal_def, hτmass]; simp, by
      rw [FiniteMeasure.null_iff_toMeasure_null]; exact hi⟩
  have hρB : (ρ : Measure ℂ) (closedBall 0 B)ᶜ = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null _ _).1 hρS.2
  have hρ'B : (ρ' : Measure ℂ) (closedBall 0 B)ᶜ = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null _ _).1 hρ'S.2
  have hB : 0 ≤ B := le_max_of_le_right hR
  have hμℂ {h : ℂ → ℂ} (hh : Continuous h) : Tendsto (fun i => ∫ w, h w ∂μ i) U
      (𝓝 (∫ w, h w ∂(ρ : Measure ℂ))) :=
    tendsto_integral_of_tendsto hρ hB (Eventually.of_forall hμB) hρB hh
  have hμℝ {h : ℂ → ℝ} (hh : Continuous h) : Tendsto (fun i => ∫ w, h w ∂μ i) U
      (𝓝 (∫ w, h w ∂(ρ : Measure ℂ))) :=
    tendsto_integral_of_tendsto hρ hB (Eventually.of_forall hμB) hρB hh
  have hμ𝕜 {h : ℂ → 𝕜} (hh : Continuous h) : Tendsto (fun i => ∫ w, h w ∂μ i) U
      (𝓝 (∫ w, h w ∂(ρ : Measure ℂ))) :=
    tendsto_integral_of_tendsto hρ hB (Eventually.of_forall hμB) hρB hh
  have hτℂ {h : ℂ → ℂ} (hh : Continuous h) : Tendsto (fun i => ∫ w, h w ∂τ i) U
      (𝓝 (∫ w, h w ∂(ρ' : Measure ℂ))) :=
    tendsto_integral_of_tendsto hρ' hB hτB hρ'B hh
  have hτℝ {h : ℂ → ℝ} (hh : Continuous h) : Tendsto (fun i => ∫ w, h w ∂τ i) U
      (𝓝 (∫ w, h w ∂(ρ' : Measure ℂ))) :=
    tendsto_integral_of_tendsto hρ' hB hτB hρ'B hh
  have hτ𝕜 {h : ℂ → 𝕜} (hh : Continuous h) : Tendsto (fun i => ∫ w, h w ∂τ i) U
      (𝓝 (∫ w, h w ∂(ρ' : Measure ℂ))) :=
    tendsto_integral_of_tendsto hρ' hB hτB hρ'B hh
  -- Step 4: `ρ` and `ρ'` have the same moments of order at most `m`, namely `M₀`.
  have hρmom (k : ℕ) : ∫ w, w ^ k ∂(ρ : Measure ℂ) = M₀ k := by
    have hνk : Tendsto (fun i => ∫ w, w ^ k ∂ν i) U (𝓝 0) :=
      squeeze_zero_norm (fun i => norm_integral_le_of_measure_compl_eq_zero (hνR i) (hpow k))
        (by simpa using hν.const_mul (R ^ k))
    have h := (hM₀ k).add hνk
    rw [add_zero] at h
    exact tendsto_nhds_unique (hμℂ (continuous_pow k)) (h.congr fun i => sub_add_cancel _ _)
  have hρ'mom (k : ℕ) (hk : k ≤ m) : ∫ w, w ^ k ∂(ρ' : Measure ℂ) = M₀ k := by
    refine tendsto_nhds_unique (hτℂ (continuous_pow k)) ((hM₀ k).congr fun i => ?_)
    rw [(integral_sum_dirac _ _).2]
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · have := hmass i
      simp only [M, P, pow_zero, integral_const, Complex.real_smul, mul_one, Multiset.map_const',
        Multiset.sum_replicate, nsmul_eq_mul, card_roots_newtonPolynomial]
      exact_mod_cast this
    · exact (sum_map_pow_roots_newtonPolynomial (M i) hk₀ hk).symm
  -- Step 5: both limits have vanishing Newton variance for the limiting polynomial `P₀`.
  have hρvar : ∫ w, ‖P₀.eval w‖ ^ 2 ∂(ρ : Measure ℂ) = 0 := by
    refine tendsto_nhds_unique (hμℝ hP₀cont) ?_
    simpa using hvar'.sub (tendsto_integral_sub_integral hBK hμC hPcont hP₀cont (hP2 B))
  have hρ'var : ∫ w, ‖P₀.eval w‖ ^ 2 ∂(ρ' : Measure ℂ) = 0 := by
    refine tendsto_nhds_unique (hτℝ hP₀cont) ?_
    have h0 (i : ι) : ∫ w, ‖(P i).eval w‖ ^ 2 ∂τ i = 0 := by
      rw [(integral_sum_dirac _ _).2]
      refine Multiset.sum_eq_zero fun x hx => ?_
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      have hr₀ : (P i).eval r = 0 :=
        ((mem_roots (monic_newtonPolynomial (M i) m).ne_zero).1 hr).eq_zero
      simp [hr₀]
    simpa [h0] using (tendsto_integral_sub_integral hBK hτC hPcont hP₀cont (hP2 B)).neg
  -- Step 6: so both are carried by the at most `m` roots of `P₀`, and they agree.
  have hP₀ : P₀ ≠ 0 := (monic_newtonPolynomial M₀ m).ne_zero
  have hcard : P₀.roots.toFinset.card ≤ m :=
    (Multiset.toFinset_card_le _).trans (card_roots_newtonPolynomial M₀ m).le
  have hρρ' : (ρ : Measure ℂ) = ρ' := eq_of_integral_pow_eq_of_measure_compl_eq_zero
    P₀.roots.toFinset (measure_compl_roots_eq_zero hBK hρB hP₀ hρvar)
    (measure_compl_roots_eq_zero hBK hρ'B hP₀ hρ'var) fun k hk => by
      rw [hρmom k, hρ'mom k (by omega)]
  -- Step 7: compare the three terms with their limits.
  have hT₁ : Tendsto (fun i => ∫ w, f i w ∂μ i) U (𝓝 (∫ w, g w ∂(ρ : Measure ℂ))) := by
    simpa using (tendsto_integral_sub_integral hBK hμC hf hg (hfg B)).add (hμ𝕜 hg)
  have hT₂ : Tendsto (fun i => ∫ w, f i w ∂ν i) U (𝓝 0) := by
    obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    have hgν : Tendsto (fun i => ∫ w, g w ∂ν i) U (𝓝 0) :=
      squeeze_zero_norm (fun i => norm_integral_le_of_measure_compl_eq_zero (hνR i) hCg)
        (by simpa using hν.const_mul Cg)
    simpa using (tendsto_integral_sub_integral hK (hν1.mono fun i hi => ⟨hνR i, hi⟩) hf hg
      (hfg R)).add hgν
  have hT₃ : Tendsto (fun i => ((P i).roots.map (f i)).sum) U
      (𝓝 (∫ w, g w ∂(ρ' : Measure ℂ))) := by
    have h := (tendsto_integral_sub_integral hBK hτC hf hg (hfg B)).add (hτ𝕜 hg)
    simp only [sub_add_cancel, zero_add] at h
    exact h.congr fun i => (integral_sum_dirac _ _).2
  simpa [hρρ'] using (hT₁.sub hT₂).sub hT₃

/-- Equi-Lipschitz functions converging pointwise converge uniformly on compact sets. -/
private lemma tendstoUniformlyOn_of_lipschitzWith {X ι : Type*} [PseudoMetricSpace X]
    {L : Filter ι} {f : ι → X → ℝ} {g : X → ℝ} {C : ℝ≥0} (hf : ∀ i, LipschitzWith C (f i))
    (hfg : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x))) {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn f g L K := by
  have heq : EquicontinuousOn f K := (Metric.equicontinuous_of_continuity_modulus
    (fun t => C * t) (by simpa using tendsto_id.const_mul (C : ℝ) (x := 𝓝 (0 : ℝ))) f
    fun x y i => (hf i).dist_le_mul x y).equicontinuousOn K
  have h := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K}) (by simpa using hK)
    (by simpa using heq) L g).2 (by rw [sUnion_singleton]; exact tendsto_pi_nhds.2 fun x => hfg x)
  exact UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 h K rfl

/-- The sequential form of the compactness core used by both public statements: data whose
negative masses and Newton variances are at most `1 / (n + 1)` eventually satisfy any required
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
    obtain ⟨c, -, hc⟩ := exists_tendsto_of_eventually_mem (U := U)
      (isCompact_Icc (a := -1) (b := 1)) (Eventually.of_forall fun n => abs_le.1 (hfb n w))
    exact ⟨c, hc⟩
  choose g hg using hlim
  have hgL : LipschitzWith 1 g := LipschitzWith.of_dist_le_mul fun x y =>
    le_of_tendsto ((hg x).dist (hg y)) (Eventually.of_forall fun n => (hfL n).dist_le_mul x y)
  obtain ⟨n, hn⟩ := exists_norm_integral_sub_sum_roots_lt hμR hνR hmass hνδ hvar
    (Ultrafilter.of_le atTop) (fun n => (hfL n).continuous) hgL.continuous
    (fun B => tendstoUniformlyOn_of_lipschitzWith hfL hg (isCompact_closedBall 0 B)) hε
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
