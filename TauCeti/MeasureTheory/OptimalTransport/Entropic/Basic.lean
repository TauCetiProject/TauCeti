/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference
public import TauCeti.InformationTheory.KullbackLeibler.Convex
public import TauCeti.InformationTheory.KullbackLeibler.Tilted
public import TauCeti.MeasureTheory.Integral.Prod
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Basic

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
* `TauCeti.IsCoupling.klDiv_eq_klDiv_add_klDiv_of_eq_withDensity`: if a coupling `π` has density
  `exp (φ(x) + ψ(y))` against `R`, every coupling `γ` satisfies the Pythagorean identity
  `klDiv γ R = klDiv γ π + klDiv π R`.
* `TauCeti.IsCoupling.klDiv_eq_schroedingerValue_of_eq_withDensity` and
  `TauCeti.schroedingerValue_eq_ofReal_of_eq_withDensity`: such a coupling is the Schrödinger
  minimizer, and the Schrödinger value is the dual value `∫ φ dμ + ∫ ψ dν` of its potentials,
  corrected by the masses of `R` and `μ`.
* `TauCeti.exists_ae_eq_add_const_of_withDensity_exp_eq`: when `R` dominates `μ.prod ν`, the
  potentials are unique up to one additive constant.
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
* `TauCeti.IsCoupling.lintegral_add_mul_klDiv_eq_entropicTransportCost_of_eq_withDensity` and
  `TauCeti.entropicTransportCost_eq_ofReal_of_eq_withDensity`: a coupling with density
  `exp ((φ(x) + ψ(y) - c(x, y)) / ε)` against `μ.prod ν` is optimal for the regularised problem,
  whose value is then `∫ φ dμ + ∫ ψ dν`.

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

The potentials `φ` and `ψ` are the dual side of the problem. A coupling whose density against
the reference factorises as `exp (φ(x) + ψ(y))`, with `φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`, is the
minimizer: `log (dπ/dR)` then integrates to the same value `∫ φ dμ + ∫ ψ dν` against every
coupling, which is the hypothesis of Csiszár's Pythagorean identity
`TauCeti.klDiv_eq_klDiv_add_klDiv`. This is the sufficiency half of the characterisation of the
Schrödinger minimizer by its density; the converse, that the minimizer has such a density, needs
further hypotheses and is not part of this file. The potentials are measurable functions rather
than almost everywhere defined ones, since the density is taken against `R` and not against the
marginals.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the regularised problem, its Gibbs reference measure, and the reduction to minimising
  relative entropy, and Theorem 2.1 for the product form of the minimizer's density and the
  uniqueness of its potentials up to a constant.
* C. Léonard, *A survey of the Schrödinger problem and some of its connections with optimal
  transport*, Discrete Contin. Dyn. Syst. 34 (2014), for the static Schrödinger problem.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158, Theorem 2.1, whose existence argument for entropy
  minimizers over convex sets closed in total variation is followed here, and for the
  Pythagorean identity of relative entropy.
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

/-! ### Schrödinger potentials -/

section Potentials

variable {φ φ' : X → ℝ} {ψ ψ' : Y → ℝ}

/-- The log-likelihood ratio of a measure with density `exp (φ(x) + ψ(y))` against `R` is
`φ(x) + ψ(y)`. Against a coupling of `μ` and `ν` it is integrable, with the integral
`kantorovichDualValue μ ν φ ψ` of the two potentials. -/
private theorem integrable_llr_withDensity_exp_and_integral_eq [SigmaFinite R]
    {σ : Measure (X × Y)} (hσ : IsCoupling σ μ ν) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφi : Integrable φ μ) (hψi : Integrable ψ ν) (hσR : σ ≪ R) :
    Integrable (llr (R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2))) R) σ ∧
      ∫ z, llr (R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2))) R z ∂σ =
        kantorovichDualValue μ ν φ ψ := by
  have hllr := hσR.ae_le (llr_withDensity_exp (f := fun z ↦ φ z.1 + ψ z.2) (by fun_prop))
  exact ⟨(integrable_congr hllr).2 (hσ.integrable_add_split hφi hψi),
    (integral_congr_ae hllr).trans (kantorovichDualValue_eq_integral hσ hφi hψi).symm⟩

/-- **The Pythagorean identity of the Schrödinger problem.** Let `π` be a coupling of `μ` and `ν`
whose density against the finite reference `R` is `exp (φ(x) + ψ(y))`, for measurable potentials
`φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`. Then every coupling `γ` of `μ` and `ν` satisfies
`klDiv γ R = klDiv γ π + klDiv π R`. -/
theorem IsCoupling.klDiv_eq_klDiv_add_klDiv_of_eq_withDensity [IsFiniteMeasure μ]
    [IsFiniteMeasure R] {γ : Measure (X × Y)} (hγ : IsCoupling γ μ ν) (hπ : IsCoupling π μ ν)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)))
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    klDiv γ R = klDiv γ π + klDiv π R := by
  have := hγ.isFiniteMeasure
  have := hπ.isFiniteMeasure
  have hπR' : π ≪ R := hπR ▸ withDensity_absolutelyContinuous _ _
  have hRπ : R ≪ π := hπR ▸ withDensity_absolutelyContinuous' (by fun_prop)
    (ae_of_all _ fun z ↦ by simp [Real.exp_pos])
  by_cases hγR : γ ≪ R
  swap
  · simp [klDiv_of_not_ac hγR, klDiv_of_not_ac fun h ↦ hγR (h.trans hπR')]
  obtain ⟨hγi, hγv⟩ := integrable_llr_withDensity_exp_and_integral_eq hγ hφ hψ hφi hψi hγR
  obtain ⟨hπi, hπv⟩ := integrable_llr_withDensity_exp_and_integral_eq hπ hφ hψ hφi hψi hπR'
  rw [← hπR] at hγi hγv hπi hπv
  exact klDiv_eq_klDiv_add_klDiv (hγR.trans hRπ) hπR' hγi hπi (hγv.trans hπv.symm)

/-- The relative entropy of a coupling with density `exp (φ(x) + ψ(y))` against `R` is the dual
value `∫ φ dμ + ∫ ψ dν` of its potentials, corrected by the difference of the masses of `R` and
`μ`. -/
theorem IsCoupling.klDiv_eq_ofReal_of_eq_withDensity [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hπ : IsCoupling π μ ν)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)))
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    klDiv π R =
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ + R.real Set.univ - μ.real Set.univ) := by
  have := hπ.isFiniteMeasure
  have hπR' : π ≪ R := hπR ▸ withDensity_absolutelyContinuous _ _
  obtain ⟨hπi, hπv⟩ := integrable_llr_withDensity_exp_and_integral_eq hπ hφ hψ hφi hψi hπR'
  rw [← hπR] at hπi hπv
  rw [klDiv_of_ac_of_integrable hπR' hπi, hπv, measureReal_def π, ← hπ.measure_univ_left,
    ← measureReal_def]

/-- The real number in `TauCeti.IsCoupling.klDiv_eq_ofReal_of_eq_withDensity` is nonnegative: it is
the real form of a relative entropy. -/
private theorem IsCoupling.kantorovichDualValue_add_sub_nonneg_of_eq_withDensity
    [IsFiniteMeasure μ] [IsFiniteMeasure R] (hπ : IsCoupling π μ ν)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)))
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    0 ≤ kantorovichDualValue μ ν φ ψ + R.real Set.univ - μ.real Set.univ := by
  have := hπ.isFiniteMeasure
  have hπR' : π ≪ R := hπR ▸ withDensity_absolutelyContinuous _ _
  obtain ⟨hπi, hπv⟩ := integrable_llr_withDensity_exp_and_integral_eq hπ hφ hψ hφi hψi hπR'
  rw [← hπR] at hπi hπv
  have := integral_llr_add_sub_measure_univ_nonneg hπR' hπi
  rwa [hπv, measureReal_def π, ← hπ.measure_univ_left, ← measureReal_def] at this

/-- **A product density certifies the Schrödinger minimizer.** A coupling `π` of `μ` and `ν`
whose density against the finite reference `R` is `exp (φ(x) + ψ(y))`, for measurable
potentials `φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`, attains the Schrödinger value. By
`TauCeti.IsCoupling.eq_of_klDiv_eq_schroedingerValue` it is the only coupling to do so. -/
theorem IsCoupling.klDiv_eq_schroedingerValue_of_eq_withDensity [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (hπ : IsCoupling π μ ν)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)))
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    klDiv π R = schroedingerValue R μ ν :=
  le_antisymm (le_schroedingerValue fun γ hγ ↦ by
      rw [hγ.klDiv_eq_klDiv_add_klDiv_of_eq_withDensity hπ hπR hφ hψ hφi hψi]
      exact le_add_self)
    (schroedingerValue_le_klDiv hπ R)

/-- **The value of the Schrödinger problem from its potentials.** If some coupling of `μ` and `ν`
has density `exp (φ(x) + ψ(y))` against the finite reference `R`, for measurable potentials
`φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`, then the Schrödinger value is the dual value
`∫ φ dμ + ∫ ψ dν` of the potentials, corrected by the difference of the masses of `R` and `μ`.
For probability measures `μ` and `R` the correction vanishes. -/
theorem schroedingerValue_eq_ofReal_of_eq_withDensity [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hπ : IsCoupling π μ ν)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)))
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    schroedingerValue R μ ν =
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ + R.real Set.univ - μ.real Set.univ) := by
  rw [← hπ.klDiv_eq_schroedingerValue_of_eq_withDensity hπR hφ hψ hφi hψi,
    hπ.klDiv_eq_ofReal_of_eq_withDensity hπR hφ hψ hφi hψi]

/-- **Uniqueness of the Schrödinger potentials.** If a reference measure `R` dominates the
product of the nonzero marginals, two pairs of potentials that give the same density
`exp (φ(x) + ψ(y))` against `R` differ by one additive constant, `μ`- and `ν`-almost everywhere:
`φ = φ' + a` and `ψ = ψ' - a`. -/
theorem exists_ae_eq_add_const_of_withDensity_exp_eq [SFinite ν] [SigmaFinite R] (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (hR : μ.prod ν ≪ R) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ' : Measurable φ') (hψ' : Measurable ψ')
    (h : (R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2))) =
      R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ' z.1 + ψ' z.2))) :
    ∃ a, φ =ᵐ[μ] (fun x ↦ φ' x + a) ∧ ψ =ᵐ[ν] (fun y ↦ ψ' y - a) := by
  rw [withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)] at h
  obtain ⟨a, hφa, hψa⟩ := exists_ae_eq_const_of_ae_prod_eq (f := fun x ↦ φ x - φ' x)
    (g := fun y ↦ ψ' y - ψ y) hμ hν <| hR.ae_le <| h.mono fun z hz ↦ by
      have := Real.exp_injective <|
        (ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le).1 hz
      linarith
  exact ⟨a, hφa.mono fun x hx ↦ by simp only at hx; linarith,
    hψa.mono fun y hy ↦ by simp only at hy; linarith⟩

end Potentials

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

/-! ### Potentials of the regularised problem -/

section GibbsPotentials

variable {φ : X → ℝ} {ψ : Y → ℝ}

/-- A plan with density `exp ((φ(x) + ψ(y) - c(x, y)) / ε)` against `μ.prod ν` has density
`exp (φ(x) / ε + log Z + ψ(y) / ε)` against the Gibbs measure
`R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)`, where `Z = ∫ e^{-c/ε} d(μ ⊗ ν)`. -/
private theorem eq_withDensity_tilted_of_eq_withDensity [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : AEMeasurable c (μ.prod ν))
    (hπc : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε)))
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    π = ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 / ε + Real.log (∫ z, Real.exp (-((c z).toReal / ε))
        ∂μ.prod ν)) + ψ z.2 / ε)) := by
  have hexp : Integrable (fun z ↦ Real.exp (-((c z).toReal / ε))) (μ.prod ν) :=
    MeasureTheory.integrable_exp_neg_of_ae_nonneg (hc.ennreal_toReal.div_const _) <|
      ae_of_all _ fun z ↦ by positivity
  have hZ : 0 < ∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν := integral_exp_pos hexp
  rw [Measure.tilted, ← withDensity_mul₀ (by fun_prop) (by fun_prop), hπc]
  congr 1
  funext z
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  set Z := ∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν
  have hexponent : (φ z.1 + ψ z.2 - (c z).toReal) / ε =
      -((c z).toReal / ε) + ((φ z.1 / ε + Real.log Z) + ψ z.2 / ε) - Real.log Z := by
    ring
  rw [hexponent, Real.exp_sub, Real.exp_add, Real.exp_log hZ, div_mul_eq_mul_div]

/-- Changing the potentials on null sets does not change a Gibbs density against `μ.prod ν`. -/
private theorem withDensity_exp_congr_ae [SFinite ν] {φ₀ : X → ℝ} {ψ₀ : Y → ℝ}
    (hφ : φ =ᵐ[μ] φ₀) (hψ : ψ =ᵐ[ν] ψ₀) :
    ((μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε))) =
      (μ.prod ν).withDensity fun z ↦
        ENNReal.ofReal (Real.exp ((φ₀ z.1 + ψ₀ z.2 - (c z).toReal) / ε)) := by
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hφ,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hψ] with z h₁ h₂
  simp only [Function.comp_apply] at h₁ h₂
  rw [h₁, h₂]

/-- **A Gibbs density certifies the entropic optimal plan.** For probability measures `μ` and
`ν`, a cost `c` finite `μ.prod ν`-almost everywhere, and a positive temperature `ε`, a coupling
`π` whose density against `μ.prod ν` is `exp ((φ(x) + ψ(y) - c(x, y)) / ε)`, for potentials
`φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`, is optimal for the regularised transport problem. -/
theorem IsCoupling.lintegral_add_mul_klDiv_eq_entropicTransportCost_of_eq_withDensity
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν)
    (hc : AEMeasurable c (μ.prod ν)) (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0)
    (hπc : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε)))
    (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν := by
  wlog hφψ : Measurable φ ∧ Measurable ψ generalizing φ ψ
  · have hφ₀ := hφi.1.ae_eq_mk
    have hψ₀ := hψi.1.ae_eq_mk
    exact this (hπc.trans (withDensity_exp_congr_ae hφ₀ hψ₀)) ((integrable_congr hφ₀).1 hφi)
      ((integrable_congr hψ₀).1 hψi) ⟨hφi.1.measurable_mk, hψi.1.measurable_mk⟩
  obtain ⟨hφ, hψ⟩ := hφψ
  have hexp : Integrable (fun z ↦ Real.exp (-((c z).toReal / ε))) (μ.prod ν) :=
    MeasureTheory.integrable_exp_neg_of_ae_nonneg (hc.ennreal_toReal.div_const _) <|
      ae_of_all _ fun z ↦ by positivity
  have := isProbabilityMeasure_tilted hexp
  refine (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hπ hc hc_top hε).2 ?_
  exact hπ.klDiv_eq_schroedingerValue_of_eq_withDensity
    (φ := fun x ↦ φ x / ε + Real.log (∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν))
    (ψ := fun y ↦ ψ y / ε) (eq_withDensity_tilted_of_eq_withDensity hc hπc hφ hψ)
    ((hφ.div_const _).add_const _) (hψ.div_const _) ((hφi.div_const _).add (integrable_const _))
    (hψi.div_const _)

/-- **The entropic transport cost from its potentials.** For probability measures `μ` and `ν`,
a cost `c` finite `μ.prod ν`-almost everywhere, and a positive temperature `ε`, if some coupling
has density `exp ((φ(x) + ψ(y) - c(x, y)) / ε)` against `μ.prod ν`, for potentials
`φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`, then the regularised transport cost is the dual value
`∫ φ dμ + ∫ ψ dν` of the potentials. -/
theorem entropicTransportCost_eq_ofReal_of_eq_withDensity [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0)
    (hπc : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε)))
    (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    entropicTransportCost c ε μ ν = ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) := by
  wlog hφψ : Measurable φ ∧ Measurable ψ generalizing φ ψ
  · have hφ₀ := hφi.1.ae_eq_mk
    have hψ₀ := hψi.1.ae_eq_mk
    rw [kantorovichDualValue_def, integral_congr_ae hφ₀, integral_congr_ae hψ₀,
      ← kantorovichDualValue_def]
    exact this (hπc.trans (withDensity_exp_congr_ae hφ₀ hψ₀)) ((integrable_congr hφ₀).1 hφi)
      ((integrable_congr hψ₀).1 hψi) ⟨hφi.1.measurable_mk, hψi.1.measurable_mk⟩
  obtain ⟨hφ, hψ⟩ := hφψ
  have hexp : Integrable (fun z ↦ Real.exp (-((c z).toReal / ε))) (μ.prod ν) :=
    MeasureTheory.integrable_exp_neg_of_ae_nonneg (hc.ennreal_toReal.div_const _) <|
      ae_of_all _ fun z ↦ by positivity
  have := isProbabilityMeasure_tilted hexp
  have hπR := eq_withDensity_tilted_of_eq_withDensity hc hπc hφ hψ
  obtain ⟨Z, hZ_def⟩ : ∃ Z, ∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν = Z := ⟨_, rfl⟩
  have hZ : 0 < Z := hZ_def ▸ integral_exp_pos hexp
  have hZ1 : Z ≤ 1 := by
    rw [← hZ_def]
    calc ∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν ≤ ∫ _, (1 : ℝ) ∂μ.prod ν :=
          integral_mono hexp (integrable_const 1) fun z ↦ by
            simp only [Real.exp_le_one_iff, Left.neg_nonpos_iff]
            positivity
      _ = 1 := by simp
  rw [hZ_def] at hπR
  have hφ' : Integrable (fun x ↦ φ x / ε + Real.log Z) μ :=
    (hφi.div_const _).add (integrable_const _)
  have hnonneg := hπ.kantorovichDualValue_add_sub_nonneg_of_eq_withDensity
    (φ := fun x ↦ φ x / ε + Real.log Z) (ψ := fun y ↦ ψ y / ε) hπR
    ((hφ.div_const _).add_const _) (hψ.div_const _) hφ' (hψi.div_const _)
  have hdual : kantorovichDualValue μ ν (fun x ↦ φ x / ε + Real.log Z) (fun y ↦ ψ y / ε) =
      kantorovichDualValue μ ν φ ψ / ε + Real.log Z := by
    simp only [kantorovichDualValue_def, integral_add (hφi.div_const _) (integrable_const _),
      integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  simp only [probReal_univ, add_sub_cancel_right, hdual] at hnonneg
  rw [entropicTransportCost_eq_mul_schroedingerValue_add hc hc_top hε, hZ_def,
    schroedingerValue_eq_ofReal_of_eq_withDensity (φ := fun x ↦ φ x / ε + Real.log Z)
      (ψ := fun y ↦ ψ y / ε) hπ hπR ((hφ.div_const _).add_const _)
      (hψ.div_const _) hφ' (hψi.div_const _), hdual, probReal_univ, probReal_univ,
    add_sub_cancel_right, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul ε.coe_nonneg,
    ← ENNReal.ofReal_mul ε.coe_nonneg, ← ENNReal.ofReal_add (mul_nonneg ε.coe_nonneg hnonneg)
      (mul_nonneg ε.coe_nonneg (neg_nonneg.2 (Real.log_nonpos hZ.le hZ1)))]
  congr 1
  field_simp
  ring

end GibbsPotentials

end TauCeti
