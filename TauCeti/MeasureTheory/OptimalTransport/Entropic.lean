/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Convex
public import TauCeti.InformationTheory.KullbackLeibler.Tilted
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Entropic optimal transport and the static Schrödinger problem

Two entropy-based transport problems share the coupling constraint of Kantorovich's problem.

* The **static Schrödinger problem** with reference measure `R` on `X × Y` minimises the relative
  entropy `klDiv π R` over the couplings `π` of `μ` and `ν`. Its value is
  `TauCeti.schroedingerValue R μ ν`.
* **Entropically regularised transport** at temperature `ε` adds `ε` times the relative entropy
  against the product of the marginals to the transport cost of a plan, and minimises
  `∫⁻ c dπ + ε * klDiv π (μ.prod ν)` over the same couplings. Its value is
  `TauCeti.entropicTransportCost c ε μ ν`.

The two are the same problem. For probability measures `μ`, `ν`, a cost that is finite
`μ.prod ν`-almost everywhere, and a positive temperature `ε`, let
`Z = ∫ e^{-c/ε} d(μ ⊗ ν)` be the partition function and `R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)` the Gibbs
measure, which is Mathlib's tilted measure
`(μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)`. Then for every probability measure `π` on
`X × Y`
`∫ c dπ + ε * klDiv π (μ ⊗ ν) = ε * klDiv π R - ε * log Z`,
so the regularised value is `ε` times the Schrödinger value with reference `R`, shifted by the
free energy `-ε log Z ≥ 0`, and the two problems have the same optimal couplings.

## Main definitions

* `TauCeti.schroedingerValue R μ ν`: the infimum of `klDiv π R` over the couplings `π` of `μ`
  and `ν`.
* `TauCeti.entropicTransportCost c ε μ ν`: the infimum of `∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)`
  over the couplings `π` of `μ` and `ν`.

## Main statements

* `TauCeti.schroedingerValue_prod`: with the product of the marginals as reference, the
  Schrödinger value is `0`, attained by the product coupling.
* `TauCeti.IsCoupling.eq_of_klDiv_eq_schroedingerValue`: a finite Schrödinger value has at most
  one minimizing coupling for a finite reference measure.
* `TauCeti.exists_isCoupling_klDiv_eq_schroedingerValue` and
  `TauCeti.existsUnique_isCoupling_klDiv_eq_schroedingerValue`: for a finite reference measure
  and a finite source measure, a finite Schrödinger value is attained, by exactly one coupling.
* `TauCeti.entropicTransportCost_zero` and `TauCeti.transportCost_le_entropicTransportCost`: at
  zero temperature the regularised value is the transport cost, which it always dominates.
* `TauCeti.entropicTransportCost_const`: for a constant cost the regularised value is the
  constant; when it is finite, with `Mathlib`'s `InformationTheory.klDiv_eq_zero_iff`, the product
  coupling is then the unique optimal plan at positive temperature.
* `TauCeti.lintegral_add_mul_klDiv_eq_mul_klDiv_tilted`: the Gibbs identity above, plan by plan.
* `TauCeti.entropicTransportCost_eq_mul_schroedingerValue_add`: the same identity for the
  optimal values.
* `TauCeti.lintegral_add_mul_klDiv_eq_entropicTransportCost_iff`: a coupling is optimal for the
  regularised problem exactly when it is optimal for the Schrödinger problem with the Gibbs
  reference.

## Implementation notes

As for `TauCeti.transportCost`, both values are defined for arbitrary measures, with an
extended-nonnegative cost, as an iterated infimum over plans and proofs of `TauCeti.IsCoupling`,
so that an empty feasible set gives `∞`. The temperature `ε` is a nonnegative real number; the
value at `ε = 0` is the unregularised transport cost.

The Gibbs identity needs the cost to be finite `μ.prod ν`-almost everywhere, since otherwise the
Gibbs measure is not equivalent to `μ.prod ν`; a cost that is infinite on a set of positive
product measure constrains the support of every plan of finite entropy and is a separate,
degenerate regime. The identity holds for every probability measure `π` on `X × Y`, not only for
couplings, and in `ℝ≥0∞` with no integrability hypothesis: when `π` is not absolutely continuous
with respect to `μ.prod ν`, or has infinite cost, both sides are `∞`.

Existence of the Schrödinger minimizer holds in the same generality as its uniqueness: for a
finite source measure `μ` and a finite reference measure `R`, a finite Schrödinger value is
attained on arbitrary measurable spaces `X` and `Y`. No topology, separability, or normalization
of `R` to a probability measure is assumed. Together with uniqueness, the minimizing coupling is
then well defined whenever the Schrödinger value is finite.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the regularised problem, its Gibbs reference measure, and the reduction to minimising
  relative entropy.
* C. Léonard, *A survey of the Schrödinger problem and some of its connections with optimal
  transport*, Discrete Contin. Dyn. Syst. 34 (2014), for the static Schrödinger problem.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158, Theorem 2.1, whose existence argument for entropy
  minimizers over convex sets closed in total variation is followed here.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c c' : X × Y → ℝ≥0∞} {ε ε' : ℝ≥0} {π R : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

/-! ### The static Schrödinger problem -/

/-- The value of the static Schrödinger problem with reference measure `R`: the infimum of the
relative entropy `klDiv π R` over the couplings `π` of `μ` and `ν`. It is `∞` when `μ` and `ν`
have no coupling, or no coupling of finite relative entropy. -/
def schroedingerValue (R : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), klDiv π R

/-- The Schrödinger value as the infimum of the relative entropies of all feasible plans. -/
theorem schroedingerValue_def :
    schroedingerValue R μ ν = ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), klDiv π R :=
  (rfl)

/-- Every coupling bounds the Schrödinger value from above. -/
theorem schroedingerValue_le_klDiv (hπ : IsCoupling π μ ν) (R : Measure (X × Y)) :
    schroedingerValue R μ ν ≤ klDiv π R :=
  iInf₂_le π hπ

/-- A bound valid on every coupling bounds the Schrödinger value from below. -/
theorem le_schroedingerValue (h : ∀ π, IsCoupling π μ ν → a ≤ klDiv π R) :
    a ≤ schroedingerValue R μ ν :=
  le_iInf₂ h

/-- The Schrödinger value is below a threshold exactly when some coupling is. -/
theorem schroedingerValue_lt_iff :
    schroedingerValue R μ ν < a ↔ ∃ π, IsCoupling π μ ν ∧ klDiv π R < a := by
  simp only [schroedingerValue, iInf_lt_iff, exists_prop]

/-- With the product of the marginals as reference, the Schrödinger value is `0`: the product
coupling has zero relative entropy. By `InformationTheory.klDiv_eq_zero_iff` it is the only
coupling attaining this value. -/
@[simp]
theorem schroedingerValue_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    schroedingerValue (μ.prod ν) μ ν = 0 :=
  nonpos_iff_eq_zero.1 <| (schroedingerValue_le_klDiv (isCoupling_prod μ ν) _).trans_eq
    (klDiv_self _)

/-- **Uniqueness of a finite-entropy Schrödinger minimizer.** For a finite reference and finite
source measure, any two couplings attaining a finite Schrödinger value agree. This applies on
arbitrary measurable spaces; existence is
`TauCeti.exists_isCoupling_klDiv_eq_schroedingerValue`. -/
theorem IsCoupling.eq_of_klDiv_eq_schroedingerValue [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hπ : IsCoupling π μ ν) {σ : Measure (X × Y)} (hσ : IsCoupling σ μ ν)
    (hπval : klDiv π R = schroedingerValue R μ ν)
    (hσval : klDiv σ R = schroedingerValue R μ ν)
    (hfin : schroedingerValue R μ ν ≠ ∞) : π = σ := by
  let := hπ.isFiniteMeasure
  let := hσ.isFiniteMeasure
  by_contra hne
  have hmix := hπ.smul_add_smul hσ (a := 2⁻¹) (b := 2⁻¹) (by norm_num)
  have hlt := klDiv_smul_add_smul_lt
    (a := (2⁻¹ : ℝ≥0)) (b := (2⁻¹ : ℝ≥0)) (by norm_num) (by norm_num) (by norm_num)
    (hπval ▸ hfin) (hσval ▸ hfin) hne
  rw [hπval, hσval, ← add_mul, ← ENNReal.coe_add, (by norm_num : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1),
    ENNReal.coe_one, one_mul] at hlt
  exact (not_lt_of_ge (schroedingerValue_le_klDiv hmix R)) hlt

/-- **Near-minimizers are close in total variation.** Two couplings whose relative entropies
exceed a finite Schrödinger value by at most `t ^ 2` have densities with respect to the
reference within `t * (2 * μ univ + 2)` of each other in `L¹`. -/
private theorem eLpNorm_toReal_rnDeriv_sub_le [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hS : schroedingerValue R μ ν ≠ ∞) (hπ : IsCoupling π μ ν) {σ : Measure (X × Y)}
    (hσ : IsCoupling σ μ ν) {t : ℝ≥0}
    (hπt : klDiv π R ≤ schroedingerValue R μ ν + (t ^ 2 : ℝ≥0))
    (hσt : klDiv σ R ≤ schroedingerValue R μ ν + (t ^ 2 : ℝ≥0)) :
    eLpNorm (fun z ↦ (π.rnDeriv R z).toReal - (σ.rnDeriv R z).toReal) 1 R ≤
      t * (2 * μ Set.univ + 2) := by
  let := hπ.isFiniteMeasure
  let := hσ.isFiniteMeasure
  set S := schroedingerValue R μ ν
  rcases eq_or_ne t 0 with rfl | ht
  · -- Both couplings are minimizers, hence equal by uniqueness.
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.coe_zero,
      add_zero] at hπt hσt
    obtain rfl := hπ.eq_of_klDiv_eq_schroedingerValue hσ
      (le_antisymm hπt (schroedingerValue_le_klDiv hπ R))
      (le_antisymm hσt (schroedingerValue_le_klDiv hσ R)) hS
    simp
  have hkey := mul_lintegral_enorm_sub_add_two_mul_klDiv_le (μ := π) (ν := σ) (ρ := R) t
  rw [← hπ.measure_univ_left, ← hσ.measure_univ_left] at hkey
  rw [eLpNorm_one_eq_lintegral_enorm (by fun_prop)]
  set E := ∫⁻ z, ‖(π.rnDeriv R z).toReal - (σ.rnDeriv R z).toReal‖ₑ ∂R
  -- The midpoint is a coupling, so its entropy is at least `S`; cancel `2 * S` and then `t`.
  have h1 : (t : ℝ≥0∞) * E + 2 * S ≤ t * (t * (2 * μ Set.univ + 2)) + 2 * S :=
    calc _ ≤ t * E + 2 * klDiv ((2⁻¹ : ℝ≥0) • π + (2⁻¹ : ℝ≥0) • σ) R := by
          gcongr
          exact schroedingerValue_le_klDiv (hπ.smul_add_smul hσ (by norm_num)) R
      _ ≤ _ := hkey
      _ ≤ t ^ 2 * (μ Set.univ + μ Set.univ) + (S + (t ^ 2 : ℝ≥0)) + (S + (t ^ 2 : ℝ≥0)) := by
          gcongr
      _ = _ := by push_cast; ring
  exact (ENNReal.mul_le_mul_iff_right (by simpa using ht) (by simp)).1
    (ENNReal.le_of_add_le_add_right (by finiteness) h1)

/-- If the densities of couplings of `μ` and `ν` with respect to `R` converge in `L¹(R)` to an
almost everywhere nonnegative limit, that limit is the density of a coupling of `μ` and `ν`. -/
private theorem isCoupling_withDensity_of_tendsto_eLpNorm [IsFiniteMeasure μ] [IsFiniteMeasure R]
    {π : ℕ → Measure (X × Y)} (hπ : ∀ n, IsCoupling (π n) μ ν) (hac : ∀ n, π n ≪ R)
    {g : X × Y → ℝ} (hgint : Integrable g R) (hg0 : 0 ≤ᵐ[R] g)
    (hL1 : Tendsto (fun n ↦ eLpNorm ((fun z ↦ ((π n).rnDeriv R z).toReal) - g) 1 R) atTop
      (𝓝 0)) :
    IsCoupling (R.withDensity fun z ↦ ENNReal.ofReal (g z)) μ ν := by
  have hfin (n : ℕ) : IsFiniteMeasure (π n) := (hπ n).isFiniteMeasure
  -- On a set where all the plans agree, the limit plan agrees with them.
  have key (s : Set (X × Y)) (hs : MeasurableSet s) (hconst : ∀ n, π n s = π 0 s) :
      R.withDensity (fun z ↦ ENNReal.ofReal (g z)) s = π 0 s := by
    have hlim := tendsto_setIntegral_of_L1' g
      (Eventually.of_forall fun n ↦ Measure.integrable_toReal_rnDeriv) hL1 s
    simp only [Measure.setIntegral_toReal_rnDeriv (hac _), measureReal_def, hconst,
      tendsto_const_nhds_iff] at hlim
    rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hgint.integrableOn
      (ae_restrict_of_ae hg0), ← hlim, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine isCoupling_of_measure_prod_univ_of_measure_univ_prod (fun s hs ↦ ?_) fun s hs ↦ ?_
  · rw [key _ (hs.prod .univ) fun n ↦ by rw [(hπ n).measure_prod_univ hs,
      (hπ 0).measure_prod_univ hs], (hπ 0).measure_prod_univ hs]
  · rw [key _ (MeasurableSet.univ.prod hs) fun n ↦ by rw [(hπ n).measure_univ_prod hs,
      (hπ 0).measure_univ_prod hs], (hπ 0).measure_univ_prod hs]

/-- **Existence of the Schrödinger minimizer.** For a finite reference measure and a finite
source measure, a finite Schrödinger value is attained by a coupling. No topology, separability
or normalization is needed: the measurable spaces are arbitrary, and `R` need not be a
probability measure. Together with `TauCeti.IsCoupling.eq_of_klDiv_eq_schroedingerValue`, the
minimizer is unique; see `TauCeti.existsUnique_isCoupling_klDiv_eq_schroedingerValue`. -/
theorem exists_isCoupling_klDiv_eq_schroedingerValue [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (h : schroedingerValue R μ ν ≠ ∞) :
    ∃ π, IsCoupling π μ ν ∧ klDiv π R = schroedingerValue R μ ν := by
  -- The densities of a minimizing sequence form a Cauchy sequence in `L¹(R)`, by the
  -- quantitative strict convexity of relative entropy
  -- `TauCeti.mul_lintegral_enorm_sub_add_two_mul_klDiv_le` applied to midpoints, which are again
  -- couplings. Their limit is the density of a coupling, and Fatou's lemma bounds its entropy.
  set S := schroedingerValue R μ ν
  -- A minimizing sequence whose entropy at step `n` exceeds `S` by less than `t n ^ 2`.
  set t : ℕ → ℝ≥0 := fun n ↦ 2⁻¹ ^ n with ht_def
  have hseq (n : ℕ) : ∃ π, IsCoupling π μ ν ∧ klDiv π R < S + (t n ^ 2 : ℝ≥0) :=
    schroedingerValue_lt_iff.1 (ENNReal.lt_add_right h (by simp [ht_def]))
  choose π hπ hπS using hseq
  have hfin (n : ℕ) : IsFiniteMeasure (π n) := (hπ n).isFiniteMeasure
  have hac (n : ℕ) : π n ≪ R := (klDiv_ne_top_iff.1 (hπS n).ne_top).1
  set f : ℕ → X × Y → ℝ := fun n z ↦ ((π n).rnDeriv R z).toReal with hf_def
  have hmeas (n : ℕ) : AEStronglyMeasurable (f n) R := by fun_prop
  -- Their densities are Cauchy in `L¹(R)`, with the summable modulus `B`.
  set B : ℕ → ℝ≥0∞ := fun N ↦ t N * (2 * μ Set.univ + 3)
  have hB : ∑' N, B N ≠ ∞ := by
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top
      (ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_geometric (by norm_num)))
      (by finiteness)
  have hcau (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) : eLpNorm (f n - f m) 1 R < B N := by
    have hexcess {k : ℕ} (hk : N ≤ k) : klDiv (π k) R ≤ S + (t N ^ 2 : ℝ≥0) := by
      have htk : t k ≤ t N := pow_le_pow_of_le_one zero_le (by norm_num) hk
      exact (hπS k).le.trans (by gcongr)
    refine (eLpNorm_toReal_rnDeriv_sub_le h (hπ n) (hπ m) (hexcess hn) (hexcess hm)).trans_lt ?_
    exact (ENNReal.mul_lt_mul_iff_right (by simp [ht_def]) (by simp)).2
      (ENNReal.add_lt_add_left (by finiteness) (by norm_num : (2 : ℝ≥0∞) < 3))
  -- The limit density defines a coupling.
  obtain ⟨g, hgm, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hmeas
    (Lp.ae_tendsto_of_cauchy_eLpNorm hmeas le_rfl hB hcau)
  have hL1 := Lp.cauchy_tendsto_of_tendsto hmeas g hB hcau hlim
  have hgint : Integrable g R := memLp_one_iff_integrable.1 <| Lp.memLp_of_cauchy_tendsto le_rfl
    (fun n ↦ memLp_one_iff_integrable.2 Measure.integrable_toReal_rnDeriv) g hL1
  have hg0 : 0 ≤ᵐ[R] g := hlim.mono fun z hz ↦ ge_of_tendsto' hz fun n ↦ ENNReal.toReal_nonneg
  have hπ₀ := isCoupling_withDensity_of_tendsto_eLpNorm hπ hac hgint hg0 hL1
  refine ⟨_, hπ₀, le_antisymm ?_ (schroedingerValue_le_klDiv hπ₀ R)⟩
  -- Its entropy is at most `S`, by Fatou's lemma along the almost everywhere convergence.
  let := hπ₀.isFiniteMeasure
  have hεlim : Tendsto (fun n ↦ S + (t n ^ 2 : ℝ≥0)) atTop (𝓝 S) := by
    have h0 : Tendsto (fun n ↦ t n ^ 2) atTop (𝓝 0) := by
      have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one zero_le
        (by norm_num : (2⁻¹ : ℝ≥0) < 1)).pow 2
      rwa [zero_pow two_ne_zero] at h0
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_coe.2 h0)
  calc klDiv (R.withDensity fun z ↦ ENNReal.ofReal (g z)) R
      = ∫⁻ z, ENNReal.ofReal (klFun (g z)) ∂R := by
        rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_withDensity R hgm.measurable.ennreal_ofReal, hg0]
          with z hz hz0
        rw [hz, ENNReal.toReal_ofReal hz0]
    _ = ∫⁻ z, liminf (fun n ↦ ENNReal.ofReal (klFun (f n z))) atTop ∂R := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with z hz
        exact (((ENNReal.continuous_ofReal.comp continuous_klFun).tendsto _).comp
          hz).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ z, ENNReal.ofReal (klFun (f n z)) ∂R) atTop :=
        lintegral_liminf_le' fun n ↦ by fun_prop
    _ = liminf (fun n ↦ klDiv (π n) R) atTop := by
        simp_rw [hf_def, ← klDiv_eq_lintegral_klFun_of_ac (hac _)]
    _ ≤ liminf (fun n ↦ S + (t n ^ 2 : ℝ≥0)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n ↦ (hπS n).le)
    _ = S := hεlim.liminf_eq

/-- **Existence and uniqueness of the Schrödinger minimizer.** For a finite reference measure and
a finite source measure, a finite Schrödinger value is attained by exactly one coupling. -/
theorem existsUnique_isCoupling_klDiv_eq_schroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (h : schroedingerValue R μ ν ≠ ∞) :
    ∃! π, IsCoupling π μ ν ∧ klDiv π R = schroedingerValue R μ ν := by
  obtain ⟨π, hπ, hπval⟩ := exists_isCoupling_klDiv_eq_schroedingerValue h
  exact ⟨π, ⟨hπ, hπval⟩, fun σ hσ ↦ (hπ.eq_of_klDiv_eq_schroedingerValue hσ.1 hπval hσ.2 h).symm⟩

/-! ### Entropically regularised transport -/

/-- The entropically regularised transport cost of `μ` and `ν` for the cost `c` at temperature
`ε`: the infimum of `∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)` over the couplings `π` of `μ` and
`ν`. It is `∞` when `μ` and `ν` have no coupling. -/
def entropicTransportCost (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) (ν : Measure Y) :
    ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν))

/-- The regularised transport cost as the infimum of the regularised costs of all feasible
plans. -/
theorem entropicTransportCost_def :
    entropicTransportCost c ε μ ν =
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)) :=
  (rfl)

/-- Every coupling bounds the regularised transport cost from above. -/
theorem entropicTransportCost_le (hπ : IsCoupling π μ ν) (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) :
    entropicTransportCost c ε μ ν ≤ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) :=
  iInf₂_le π hπ

/-- A bound valid on every coupling bounds the regularised transport cost from below. -/
theorem le_entropicTransportCost
    (h : ∀ π, IsCoupling π μ ν → a ≤ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)) :
    a ≤ entropicTransportCost c ε μ ν :=
  le_iInf₂ h

/-- The regularised transport cost is below a threshold exactly when some coupling is. -/
theorem entropicTransportCost_lt_iff :
    entropicTransportCost c ε μ ν < a ↔
      ∃ π, IsCoupling π μ ν ∧ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) < a := by
  simp only [entropicTransportCost, iInf_lt_iff, exists_prop]

/-- The regularised transport cost is monotone in the cost and in the temperature. -/
theorem entropicTransportCost_mono (hc : c ≤ c') (hε : ε ≤ ε') :
    entropicTransportCost c ε μ ν ≤ entropicTransportCost c' ε' μ ν :=
  iInf₂_mono fun _ _ ↦ add_le_add (lintegral_mono hc) (by gcongr)

/-- At zero temperature the regularised transport cost is the transport cost. -/
@[simp]
theorem entropicTransportCost_zero : entropicTransportCost c 0 μ ν = transportCost c μ ν := by
  simp [entropicTransportCost, transportCost_def]

/-- The regularised transport cost dominates the transport cost. -/
theorem transportCost_le_entropicTransportCost :
    transportCost c μ ν ≤ entropicTransportCost c ε μ ν := by
  rw [transportCost_def]
  exact iInf₂_mono fun _ _ ↦ le_self_add

/-- For a constant cost `a`, the regularised transport cost of two probability measures is `a`,
attained by the product coupling. Since a coupling `π` pays `a + ε * klDiv π (μ.prod ν)`, at
positive temperature and for finite `a` the product coupling is the only optimal plan, by
`InformationTheory.klDiv_eq_zero_iff`. -/
@[simp]
theorem entropicTransportCost_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : ℝ≥0∞) (ε : ℝ≥0) : entropicTransportCost (fun _ ↦ a) ε μ ν = a := by
  refine le_antisymm ?_ (le_entropicTransportCost fun π hπ ↦ ?_)
  · refine (entropicTransportCost_le (isCoupling_prod μ ν) _ ε).trans_eq ?_
    simp [klDiv_self]
  · have := hπ.isProbabilityMeasure
    simp

/-! ### The Gibbs reformulation -/

/-- **The Gibbs identity.** For probability measures `μ` and `ν`, a cost `c` finite
`μ.prod ν`-almost everywhere, and a positive temperature `ε`, every probability measure `π` on
`X × Y` satisfies `∫ c dπ + ε * klDiv π (μ ⊗ ν) = ε * klDiv π R - ε * log Z`, where
`Z = ∫ e^{-c/ε} d(μ ⊗ ν)` and `R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)` is the Gibbs measure, written as the
tilted measure `(μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)`. Both sides may be `∞`. -/
theorem lintegral_add_mul_klDiv_eq_mul_klDiv_tilted [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure π] (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0) :
    ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) =
      ε * klDiv π ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) +
        ε * ENNReal.ofReal (-Real.log (∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν)) := by
  have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε
  by_cases hπ : π ≪ μ.prod ν
  swap
  · have hπR : ¬ π ≪ (μ.prod ν).tilted fun z ↦ -((c z).toReal / ε) :=
      fun h ↦ hπ (h.trans (tilted_absolutelyContinuous _ _))
    simp [klDiv_of_not_ac hπ, klDiv_of_not_ac hπR, ENNReal.mul_top hε']
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hcost : (ε : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ((c z).toReal / ε) ∂π = ∫⁻ z, c z ∂π := by
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hπ.ae_le hc_top] with z hz
    rw [ENNReal.ofReal_div_of_pos hεpos, ENNReal.ofReal_toReal hz, ENNReal.ofReal_coe_nnreal,
      ENNReal.mul_div_cancel hε' ENNReal.coe_ne_top]
  rw [← hcost, ← mul_add, ← klDiv_tilted_neg_add_ofReal_neg_log
    (hc.ennreal_toReal.div_const _) (ae_of_all _ fun z ↦ by positivity), mul_add]

/-- **The Gibbs reformulation of entropic transport.** For probability measures `μ` and `ν`, a
cost `c` finite `μ.prod ν`-almost everywhere, and a positive temperature `ε`, the regularised
transport cost is `ε` times the value of the Schrödinger problem with the Gibbs reference
measure `R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)`, plus the free energy `-ε log Z`. -/
theorem entropicTransportCost_eq_mul_schroedingerValue_add [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0) :
    entropicTransportCost c ε μ ν =
      ε * schroedingerValue ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) μ ν +
        ε * ENNReal.ofReal (-Real.log (∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν)) := by
  have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε
  simp only [entropicTransportCost, schroedingerValue,
    ENNReal.mul_iInf_of_ne hε' ENNReal.coe_ne_top, ENNReal.iInf_add]
  refine iInf_congr fun π ↦ iInf_congr fun hπ ↦ ?_
  have := hπ.isProbabilityMeasure
  exact lintegral_add_mul_klDiv_eq_mul_klDiv_tilted hc hc_top hε

/-- A coupling is optimal for the regularised transport problem at positive temperature exactly
when it is optimal for the Schrödinger problem with the Gibbs reference measure
`R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)`, for a cost finite `μ.prod ν`-almost everywhere. -/
theorem lintegral_add_mul_klDiv_eq_entropicTransportCost_iff [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0) :
    ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν ↔
      klDiv π ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) =
        schroedingerValue ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) μ ν := by
  have := hπ.isProbabilityMeasure
  rw [lintegral_add_mul_klDiv_eq_mul_klDiv_tilted hc hc_top hε,
    entropicTransportCost_eq_mul_schroedingerValue_add hc hc_top hε,
    ENNReal.add_left_inj (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
    ENNReal.mul_right_inj (ENNReal.coe_ne_zero.2 hε) ENNReal.coe_ne_top]

end TauCeti
