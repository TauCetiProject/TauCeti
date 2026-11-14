/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Main
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Integral

/-!
# Krasner's discriminant-refined count of local field extensions

Let `K` be a nonarchimedean local field whose residue field `𝓀[K]` has `q` elements, and let
`σ_K(n) = TauCeti.totallyRamifiedOfDegree K n` be the set of totally ramified degree-`n`
subextensions of `SeparableClosure K`. For `L ∈ σ_K(n)` with discriminant exponent `d(L)`, Serre's
wild exponent is `c(L) = d(L) - n + 1` (`IntermediateField.wildExponent`). Serre's mass formula
computes the weighted total `∑_{L ∈ σ_K(n)} q ^ (-c(L)) = n`; building on Ore's realizability
theorem and Krasner's discriminant box `TauCeti.eisensteinBox K n j`, this file counts the members
of `σ_K(n)` of each given wild exponent `j` in arbitrary characteristic, specializes the formula to
`ℚ_[p]`, checks consistency with Serre's mass formulas, and derives total degree-`n` counts.

## Main strategy

Integrating `∑_{L ∈ σ_K(n), c(L) = j} L.rootCount = n` over `eisensteinBox K n j` against
normalized Haar measure and dividing by Serre's root-count integral `q ^ (-(n + j)) (1 - q⁻¹)`
gives Krasner's formula (`TauCeti.krasner_refined_count`), evaluated explicitly as
`TauCeti.krasnerCount K n j`. Over `ℚ_[p]`, evaluating `∑_{1 ≤ h < n} ν_h` by counting multiples
of prime powers yields the Pauli–Roblot closed form
(`TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_padic`), from which `#σ_{ℚ_2}(2) = 6`,
`#σ_{ℚ_3}(3) = 21`, and `#σ_{ℚ_2}(4) = 92` follow directly. Finally, decomposing arbitrary
degree-`n` extensions inside `SeparableClosure K` over their canonical unramified subextensions
gives `# {L | [L : K] = n} = ∑_{f ∣ n} #σ_{K_f}(n / f)`
(`TauCeti.encard_finrank_eq_sum_totallyRamifiedOfDegree`).

## Main definitions

* `TauCeti.krasnerCount`: Krasner's rational formula for `# {L ∈ σ_K(n) | c(L) = j}`.

## Main results

* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le` and
  `TauCeti.finite_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-height finiteness in
  every characteristic.
* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox` and
  `TauCeti.krasner_refined_count`: finiteness and exact cardinality of `{E ∈ σ_K(n) | c(E) = j}`.
* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_padic`: Pauli–Roblot closed form over
  `ℚ_[p]`.
* `TauCeti.tsum_ncard_wildExponent_div_natCard_residueField_pow`,
  `TauCeti.hasSum_krasnerCount_div_natCard_residueField_pow`, and
  `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: regrouped mass
  consistency with Serre's Theorem 1 and isomorphism-class mass at height `j`.
* `TauCeti.encard_totallyRamifiedOfDegree_eq_tsum`,
  `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero`,
  `TauCeti.ncard_totallyRamifiedOfDegree_two_padicTwo`,
  `TauCeti.ncard_totallyRamifiedOfDegree_three_padicThree`,
  `TauCeti.ncard_totallyRamifiedOfDegree_four_padicTwo`, and
  `TauCeti.encard_finrank_eq_sum_totallyRamifiedOfDegree`: total counts by degree.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `p`-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, Éditions du CNRS, Paris (1966), 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1.
-/

public section
noncomputable section

open MeasureTheory Polynomial ValuativeRel
open TauCeti.Polynomial (monicOfCoeff natDegree_monicOfCoeff)
open scoped ENNReal IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Krasner's discriminant-refined count -/

variable (K) in
/-- **Krasner's refined count**: rational expression for the number of totally ramified degree-`n`
extensions of `K` inside `SeparableClosure K` with wild exponent `j`, equal to `0` outside Ore's
admissible wild exponents. -/
def krasnerCount (n j : ℕ) : ℚ := by
  classical
  let q : ℚ := Nat.card 𝓀[K]
  exact if IsOreAdmissible K n j then
    n * q ^ (((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
        (if j % n = 0 then 1 else 1 - q⁻¹)
  else 0

/-- In degree `0`, `krasnerCount` vanishes. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 := by
  classical
  simp [krasnerCount]

/-- Outside Ore's admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  classical
  rw [krasnerCount, ite_eq_right h]

/-- On an Ore-admissible wild exponent, `krasnerCount` unfolds to Krasner's box formula. -/
theorem krasnerCount_of_isOreAdmissible {n j : ℕ} (h : IsOreAdmissible K n j) :
    krasnerCount K n j =
      (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^ (((n + j - 1 : ℕ) : ℤ) -
        ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
          (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹) := by
  classical
  rw [krasnerCount, ite_eq_left h]

/-- **Bounded-height finiteness**: for every local field `K` (including in equal characteristic)
and every `n, D : ℕ`, only finitely many members of `totallyRamifiedOfDegree K n` have wild
exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D}.Finite := by
  have htsum : ∑' L : totallyRamifiedOfDegree K n,
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent ≠ ∞ := by
    rw [tsum_one_div_natCard_residueField_pow_wildExponent]
    exact ENNReal.natCast_ne_top n
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ^ D ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hfin := ENNReal.finite_const_le_of_tsum_ne_top htsum (ENNReal.div_pos one_ne_zero hq).ne'
  refine (hfin.image Subtype.val).subset ?_
  rintro E ⟨hE, hle⟩
  exact ⟨⟨E, hE⟩, ENNReal.div_le_div_left
    (pow_le_pow_right₀ (Nat.one_le_cast.mpr Nat.card_pos) hle) 1, rfl⟩

/-- **Bounded-discriminant finiteness**: for every local field `K` and `n, D : ℕ`, only finitely
many members of `totallyRamifiedOfDegree K n` have discriminant exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ D}.Finite := by
  refine (finite_totallyRamifiedOfDegree_wildExponent_le (K := K) n (D + 1)).subset ?_
  rintro E ⟨hE, hd⟩
  refine ⟨hE, ?_⟩
  rw [IntermediateField.wildExponent_def]
  omega

/-- For every `n, j : ℕ`, the stratum `{E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}` is
finite. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_le n j).subset fun _ ⟨hE, hj⟩ ↦ ⟨hE, hj.le⟩

/-- If `L ∈ σ_K(n)` contains a root of an Eisenstein polynomial `monicOfCoeff a`, then
`a ∈ eisensteinBox K n L.wildExponent`. -/
private theorem mem_eisensteinBox_of_rootCount_ne_zero {n : ℕ} (hn : 0 < n)
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) (hrc : L.rootCount a ≠ 0) :
    a ∈ eisensteinBox K n L.wildExponent := by
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have := hL'.2.finite
  rw [L.rootCount_def, ← pos_iff_ne_zero, Multiset.card_pos_iff_exists_mem] at hrc
  obtain ⟨y, hy⟩ := hrc
  have hx : aeval (L.val y) (monicOfCoeff a) = 0 := by
    rw [aeval_algHom_apply, (mem_aroots.mp hy).2, map_zero]
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hzdeg := (mem_totallyRamifiedOfDegree_iff.mp
    (adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg (hf.symm ▸ hx))).1
  have hgen : K⟮L.val y⟯ = L :=
    IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr y.2) (hzdeg.trans hL'.1.symm)
  exact (mem_eisensteinBox_iff_wildExponent_adjoin_eq hn ha hx).mpr (congrArg _ hgen)

/-- For `L ∈ σ_K(n)` of wild exponent `j`, the integral of `L.rootCount` over `eisensteinBox K n j`
equals its integral over all of `eisensteinSet K n`, because `L.rootCount` vanishes outside the
box. -/
private theorem setLIntegral_eisensteinBox_rootCount {n j : ℕ} (hn : 0 < n)
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hj : L.wildExponent = j) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hsub := eisensteinBox_subset_eisensteinSet (K := K) n j
  have hsplit := lintegral_inter_add_sdiff (μ := μ) (fun a ↦ (L.rootCount a : ℝ≥0∞))
    (eisensteinSet K n) (measurableSet_eisensteinBox (K := K) n j)
  rw [Set.inter_eq_self_of_subset_right hsub] at hsplit
  have hdiff : ∫⁻ a in eisensteinSet K n \ eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ = 0 := by
    refine (setLIntegral_congr_fun
      (measurableSet_eisensteinSet.diff (measurableSet_eisensteinBox n j)) ?_).trans lintegral_zero
    intro a ⟨heis, hnot⟩
    simp only [Nat.cast_eq_zero]
    by_contra hrc
    exact hnot (hj ▸ mem_eisensteinBox_of_rootCount_ne_zero hn hL heis hrc)
  have hd : L.discriminantExponent + 1 = n + j := by
    have := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL
    omega
  rw [hdiff, add_zero, L.lintegral_rootCount hL μ hμ, hd] at hsplit
  exact hsplit

/-- Pointwise on `eisensteinBox K n j`, the root counts over the `j`-stratum of `σ_K(n)` sum to
`n`. -/
private theorem sum_rootCount_eq_of_mem_eisensteinBox {n j : ℕ} (hn : 0 < n)
    {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) :
    (∑ L ∈ (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).toFinset,
      (L.rootCount a : ℝ≥0∞)) = n := by
  classical
  set hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  have heis := eisensteinBox_subset_eisensteinSet n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp heis
  rw [← tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha)]
  have hsupp : Function.support (fun L : IntermediateField K (SeparableClosure K) ↦
      if L ∈ totallyRamifiedOfDegree K n then (L.rootCount a : ℝ≥0∞) else 0) ⊆
      (hfin.toFinset : Set (IntermediateField K (SeparableClosure K))) := by
    intro L hL
    simp only [Function.mem_support, ne_eq] at hL
    split_ifs at hL with hmem
    · rw [Finset.mem_coe, hfin.mem_toFinset]
      refine ⟨hmem, ?_⟩
      have habox := mem_eisensteinBox_of_rootCount_ne_zero hn hmem heis (by exact_mod_cast hL)
      by_contra hne
      exact Set.disjoint_left.mp (pairwiseDisjoint_eisensteinBox (K := K) n trivial trivial hne)
        habox ha
    · exact absurd rfl hL
  calc (∑ L ∈ hfin.toFinset, (L.rootCount a : ℝ≥0∞))
      = ∑ L ∈ hfin.toFinset,
          if L ∈ totallyRamifiedOfDegree K n then (L.rootCount a : ℝ≥0∞) else 0 :=
        Finset.sum_congr rfl fun L hL ↦ by simp [(hfin.mem_toFinset.mp hL).1]
    _ = ∑' L, if L ∈ totallyRamifiedOfDegree K n then (L.rootCount a : ℝ≥0∞) else 0 :=
        (tsum_eq_sum fun L hL ↦ Classical.not_not.mp (mt (@hsupp L) (by simpa using hL))).symm
    _ = ∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞) := by
        rw [tsum_subtype (totallyRamifiedOfDegree K n)
          (fun L : IntermediateField K (SeparableClosure K) ↦ (L.rootCount a : ℝ≥0∞))]
        exact tsum_congr fun L ↦ by simp [Set.indicator_apply]

/-- **Measure form of Krasner's count**: for `0 < n` and normalized left-invariant measure `μ`,
`# {E ∈ σ_K(n) | c(E) = j} * q ^ (-(n + j)) * (1 - q⁻¹) = n * μ (eisensteinBox K n j)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_mul_measure_eisensteinBox {n : ℕ}
    (hn : 0 < n) (j : ℕ) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      (n : ℝ≥0∞) * μ (eisensteinBox K n j) := by
  set hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  have haemeas (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ hfin.toFinset) :
      AEMeasurable (fun a ↦ (L.rootCount a : ℝ≥0∞)) (μ.restrict (eisensteinBox K n j)) :=
    (aemeasurable_rootCount_restrict_eisensteinSet μ (hfin.mem_toFinset.mp hL).1).mono_set
      (eisensteinBox_subset_eisensteinSet n j)
  calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)))
      = ∑ L ∈ hfin.toFinset,
          ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ := by
        rw [Set.ncard_eq_toFinset_card _ hfin, ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun L hL ↦
          (setLIntegral_eisensteinBox_rootCount hn (hfin.mem_toFinset.mp hL).1
            (hfin.mem_toFinset.mp hL).2 μ hμ).symm
    _ = ∫⁻ a in eisensteinBox K n j, ∑ L ∈ hfin.toFinset, (L.rootCount a : ℝ≥0∞) ∂μ :=
        (lintegral_finsetSum' hfin.toFinset haemeas).symm
    _ = ∫⁻ _ in eisensteinBox K n j, (n : ℝ≥0∞) ∂μ :=
        setLIntegral_congr_fun (measurableSet_eisensteinBox n j)
          fun _ ha ↦ sum_rootCount_eq_of_mem_eisensteinBox hn ha
    _ = (n : ℝ≥0∞) * μ (eisensteinBox K n j) := by
        rw [setLIntegral_const]

/-- **Krasner's theorem in measure form**: for `0 < n` and normalized left-invariant measure `μ`,
`# {E ∈ σ_K(n) | c(E) = j} = n * q ^ (n + j) * μ (eisensteinBox K n j) / (1 - q⁻¹)` in `ℝ≥0∞`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox {n : ℕ}
    (hn : 0 < n) (j : ℕ) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      (n : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * μ (eisensteinBox K n j) /
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hid := ncard_totallyRamifiedOfDegree_wildExponent_eq_mul_measure_eisensteinBox hn j μ hμ
  have hq1 : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hu0 : 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 :=
    (tsub_pos_iff_lt.mpr (by rw [one_div]; exact ENNReal.inv_lt_one.mpr hq1)).ne'
  have hu_top : 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hpow0 : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) ≠ 0 := pow_ne_zero _ hq0
  have hpow_top : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) ≠ ⊤ := ENNReal.pow_ne_top hqt
  rw [ENNReal.eq_div_iff hu0 hu_top, mul_comm]
  have hcancel : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) *
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
    calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)
        = ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)) := by ring
      _ = ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
          simp only [one_div]
          rw [ENNReal.inv_mul_cancel hpow0 hpow_top, mul_one]
  rw [← hcancel, hid]
  ring

/-- Clearing `q ^ (1 + sd) * q` in `ℝ≥0∞` for the `j % n ≠ 0` case of Krasner's formula. -/
private theorem ennreal_mul_pow_mul_sub_inv {q m : ℕ} (hq0 : (q : ℝ≥0∞) ≠ 0)
    (hqt : (q : ℝ≥0∞) ≠ ⊤) (x : ℝ≥0∞) :
    x * (1 / (q : ℝ≥0∞) ^ m * (1 - 1 / (q : ℝ≥0∞))) * ((q : ℝ≥0∞) ^ m * (q : ℝ≥0∞)) =
      x * ((q - 1 : ℕ) : ℝ≥0∞) := by
  calc x * (1 / (q : ℝ≥0∞) ^ m * (1 - 1 / (q : ℝ≥0∞))) * ((q : ℝ≥0∞) ^ m * (q : ℝ≥0∞))
      = x * (((q : ℝ≥0∞) ^ m)⁻¹ * (q : ℝ≥0∞) ^ m) * ((1 - (q : ℝ≥0∞)⁻¹) * (q : ℝ≥0∞)) := by
        simp only [one_div]; ring
    _ = x * ((q - 1 : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one,
          ENNReal.sub_mul fun _ _ ↦ hqt, one_mul, ENNReal.inv_mul_cancel hq0 hqt,
          ENNReal.natCast_sub, Nat.cast_one]

/-- Evaluating `ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox` against
normalized Haar measure on an Ore-admissible box cancels `1 - 1 / q` in `ℝ≥0∞`. -/
private theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_ennreal {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible K n j) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      (n : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
            (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
          if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  let _ : MeasurableSpace (Fin n → K) := borel _
  have _ : BorelSpace (Fin n → K) := ⟨rfl⟩
  let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
    ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
      rw [isOpen_integerBox.interior_eq]; exact ⟨0, by simp⟩⟩
  let μ := Measure.addHaarMeasure B
  have hid := ncard_totallyRamifiedOfDegree_wildExponent_eq_of_measure_eisensteinBox hn j μ
    Measure.addHaarMeasure_self
  rw [measure_eisensteinBox hn hadm μ Measure.addHaarMeasure_self] at hid
  set q := Nat.card 𝓀[K]
  have hq1 : 1 < q := Finite.one_lt_card (α := 𝓀[K])
  have hu0 : 1 - 1 / (q : ℝ≥0∞) ≠ 0 :=
    (tsub_pos_iff_lt.mpr
      (by rw [one_div]; exact ENNReal.inv_lt_one.mpr (by exact_mod_cast hq1))).ne'
  have hu_top : 1 - 1 / (q : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  set sd := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  have hnum : (n : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j) *
      (1 / (q : ℝ≥0∞) ^ (1 + sd) * (1 - 1 / (q : ℝ≥0∞)) *
        if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)) =
      (n : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j) *
        (1 / (q : ℝ≥0∞) ^ (1 + sd) * if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)) *
        (1 - 1 / (q : ℝ≥0∞)) := by ring
  rwa [hnum, ENNReal.mul_div_cancel_right hu0 hu_top] at hid

/-- Converting the `ℝ≥0∞` volume identity on an Ore-admissible box into the rational identity with
`krasnerCount K n j`. -/
private theorem cast_ncard_eq_krasnerCount_of_isOreAdmissible {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible K n j) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j := by
  have hid := ncard_totallyRamifiedOfDegree_wildExponent_eq_ennreal hn hadm
  set q := Nat.card 𝓀[K]
  have hq1 : 1 < q := Finite.one_lt_card (α := 𝓀[K])
  have hq0_enn : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  have hqt_enn : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set sd := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  rw [krasnerCount_of_isOreAdmissible hadm]
  have hq0_rat : (q : ℚ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  have hexp : ((n + j - 1 : ℕ) : ℤ) - (sd : ℤ) = ((n + j : ℕ) : ℤ) - ((1 + sd : ℕ) : ℤ) := by
    omega
  rcases eq_or_ne (j % n) 0 with hb0 | hb
  · rw [ite_eq_left hb0] at hid ⊢
    rw [mul_one, mul_one_div,
      ENNReal.eq_div_iff (pow_ne_zero _ hq0_enn) (ENNReal.pow_ne_top hqt_enn), mul_comm] at hid
    have hrat : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) *
        (q : ℚ) ^ (1 + sd) = (n : ℚ) * (q : ℚ) ^ (n + j) := by
      exact_mod_cast (by exact_mod_cast hid :
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard * q ^ (1 + sd) =
          n * q ^ (n + j))
    rwa [mul_one, hexp, zpow_sub₀ hq0_rat, zpow_natCast, zpow_natCast, mul_div_assoc',
      eq_div_iff (pow_ne_zero _ hq0_rat)]
  · rw [ite_eq_right hb] at hid ⊢
    have hmul := congrArg (· * ((q : ℝ≥0∞) ^ (1 + sd) * (q : ℝ≥0∞))) hid
    rw [ennreal_mul_pow_mul_sub_inv hq0_enn hqt_enn, ← pow_succ] at hmul
    have hnat : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard *
        q ^ (1 + sd + 1) = n * q ^ (n + j) * (q - 1) := by exact_mod_cast hmul
    have hrat : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) *
        (q : ℚ) ^ (1 + sd + 1) = (n : ℚ) * (q : ℚ) ^ (n + j) * ((q : ℚ) - 1) := by
      simpa [Nat.cast_sub hq1.le] using congrArg (Nat.cast (R := ℚ)) hnat
    rwa [hexp, zpow_sub₀ hq0_rat, zpow_natCast, zpow_natCast, inv_eq_one_div,
      one_sub_div hq0_rat, mul_assoc, div_mul_div_comm, ← pow_succ, mul_div_assoc', ← mul_assoc,
      eq_div_iff (pow_ne_zero _ hq0_rat)]

/-- **Krasner's discriminant-refined count**: for `0 < n` and any local field `K` (including in
equal characteristic), the members of `totallyRamifiedOfDegree K n` with wild exponent `j` form a
finite set of cardinality `krasnerCount K n j`. -/
theorem krasner_refined_count (n j : ℕ) (hn : 0 < n) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite ∧
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
        krasnerCount K n j := by
  refine ⟨finite_totallyRamifiedOfDegree_wildExponent_eq n j, ?_⟩
  by_cases hadm : IsOreAdmissible K n j
  · exact cast_ncard_eq_krasnerCount_of_isOreAdmissible hn hadm
  · rw [krasnerCount_of_not_isOreAdmissible hadm]
    have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro E ⟨hE, hj⟩
      exact hadm ((ore_realizability n j hn).mp ⟨E, hE, hj⟩)
    rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-! ### Closed form over `ℚ_[p]` -/

/-- For `h ≠ 0` and any prime `p`, `min m (v_p(h))` counts the powers `p ^ i` (`1 ≤ i ≤ m`)
dividing `h`. -/
private theorem min_padicValNat_eq_sum_ite_dvd (p : ℕ) [Fact p.Prime] (m : ℕ) {h : ℕ}
    (hh : h ≠ 0) :
    min m (padicValNat p h) = ∑ i ∈ Finset.Icc 1 m, if p ^ i ∣ h then 1 else 0 := by
  have hdvd (i : ℕ) : p ^ i ∣ h ↔ i ≤ padicValNat p h := by
    rw [Nat.padicValNat_def]
    exact multiplicity_dvd_iff_le hh
  simp only [hdvd]
  have hfilter : (Finset.Icc 1 m).filter (fun i ↦ i ≤ padicValNat p h) =
      Finset.Icc 1 (min m (padicValNat p h)) := by
    ext i
    simp [le_min_iff, and_assoc]
  rw [← Finset.card_filter, hfilter, Nat.card_Icc]
  omega

/-- Counting multiples of `d` in `Finset.Ico 1 m` via `Finset.Ioc 0 m`. -/
private theorem sum_Ico_ite_dvd_add_ite_eq_div {m : ℕ} (hm : 0 < m) (d : ℕ) :
    (∑ h ∈ Finset.Ico 1 m, if d ∣ h then 1 else 0) + (if d ∣ m then 1 else 0) = m / d := by
  have hIoc : Finset.Ioc 0 m = insert m (Finset.Ico 1 m) := by
    ext h; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ico]; omega
  have hcard := Nat.Ioc_filter_dvd_card_eq_div m d
  rw [Finset.card_filter, hIoc, Finset.sum_insert (by simp)] at hcard
  omega

/-- Splitting `min (a + [h < b]) (v_p(h))` into the `Icc 1 a` prime-power sum plus the `p ^ (a + 1)`
indicator on `h < b`. -/
private theorem min_padicValNat_add_ite_eq (p : ℕ) [Fact p.Prime] (a b : ℕ) {h : ℕ} (hh0 : h ≠ 0) :
    min (a + if h < b then 1 else 0) (padicValNat p h) =
      (∑ i ∈ Finset.Icc 1 a, if p ^ i ∣ h then 1 else 0) +
        if h < b ∧ p ^ (a + 1) ∣ h then 1 else 0 := by
  by_cases hlt : h < b
  · have hIcc : Finset.Icc 1 (a + 1) = insert (a + 1) (Finset.Icc 1 a) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    simp only [hlt, ↓reduceIte, true_and]
    rw [min_padicValNat_eq_sum_ite_dvd p (a + 1) hh0, hIcc, Finset.sum_insert (by simp), add_comm]
  · simp [hlt, min_padicValNat_eq_sum_ite_dvd p a hh0]

/-- Evaluating `∑_{h ∈ Ico 1 n} min (j / n + [h < j % n]) (v_p(h))` for an Ore-admissible pair
`(n, j)` over `ℚ_[p]` by swapping sums and counting prime-power multiples. -/
private theorem sum_min_padicValNat_ore (p : ℕ) [Fact p.Prime] {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    (∑ h ∈ Finset.Ico 1 n, min (j / n + if h < j % n then 1 else 0) (padicValNat p h)) + j / n =
      (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) +
        if j % n = 0 then 0 else (j % n) / p ^ (j / n + 1) := by
  set a := j / n
  set b := j % n
  have hb_lt : b < n := Nat.mod_lt j hn
  have ha_le : a ≤ padicValNat p n :=
    Nat.div_le_of_le_mul (mul_comm n _ ▸ ((isOreAdmissible_padic_iff p hn).mp hadm).2)
  have hcount_n (i : ℕ) (hi : i ∈ Finset.Icc 1 a) :
      (∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0) + 1 = n / p ^ i := by
    have hi_le : i ≤ padicValNat p n := (Finset.mem_Icc.mp hi).2.trans ha_le
    have hdvd_n : p ^ i ∣ n :=
      (multiplicity_dvd_iff_le hn.ne').mpr (Nat.padicValNat_def ▸ hi_le)
    simpa [hdvd_n] using sum_Ico_ite_dvd_add_ite_eq_div hn (p ^ i)
  have hsum_base : (∑ i ∈ Finset.Icc 1 a, ∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0) + a =
      ∑ i ∈ Finset.Icc 1 a, n / p ^ i := by
    calc (∑ i ∈ Finset.Icc 1 a, ∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0) + a
        = (∑ i ∈ Finset.Icc 1 a, ∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0) +
            ∑ _i ∈ Finset.Icc 1 a, 1 := by simp
      _ = ∑ i ∈ Finset.Icc 1 a, ((∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0) + 1) :=
            Finset.sum_add_distrib.symm
      _ = ∑ i ∈ Finset.Icc 1 a, n / p ^ i := Finset.sum_congr rfl hcount_n
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · simp only [hb0, ↓reduceIte, add_zero]
    rw [← hsum_base, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun h hh ↦
      min_padicValNat_eq_sum_ite_dvd p a (by have := (Finset.mem_Ico.mp hh).1; omega)
  · have hvb : padicValNat p b ≤ a := by
      rcases (isOreAdmissible_iff.mp hadm) with ⟨h0, -⟩ | ⟨-, hv, -⟩
      · omega
      · rwa [_root_.Padic.natValuation_of_ne_zero p hbpos.ne', Nat.cast_le] at hv
    have hnot_dvd_b : ¬ p ^ (a + 1) ∣ b := by
      rw [multiplicity_dvd_iff_le hbpos.ne', ← Nat.padicValNat_def]; omega
    have hcount_b : (∑ h ∈ Finset.Ico 1 b, if p ^ (a + 1) ∣ h then 1 else 0) = b / p ^ (a + 1) := by
      simpa [hnot_dvd_b] using sum_Ico_ite_dvd_add_ite_eq_div hbpos (p ^ (a + 1))
    simp only [hbpos.ne', ↓reduceIte]
    rw [Finset.sum_congr rfl (fun h hh ↦ min_padicValNat_add_ite_eq p a b
      (by have := (Finset.mem_Ico.mp hh).1; omega)),
      Finset.sum_add_distrib, Finset.sum_comm, ← hsum_base]
    have htail : (∑ x ∈ Finset.Ico 1 n, if x < b ∧ p ^ (a + 1) ∣ x then 1 else 0) =
        b / p ^ (a + 1) := by
      rw [← hcount_b, ← Finset.sum_subset (Finset.Ico_subset_Ico_right hb_lt.le)]
      · exact Finset.sum_congr rfl fun h hh ↦ by simp [(Finset.mem_Ico.mp hh).2]
      · intro h hh hnot
        have : ¬ h < b := fun hlt ↦ hnot (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hh).1, hlt⟩)
        simp [this]
    rw [htail]
    omega

/-- Over `ℚ_[p]`, evaluating `∑_{h ∈ Ico 1 n} oreCoefficientDepth ℚ_[p] n j h` by counting
multiples of prime powers yields the exponent of Pauli–Roblot Theorem 6.1. -/
private theorem sum_oreCoefficientDepth_padic (p : ℕ) [Fact p.Prime] {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    ((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h : ℕ) : ℤ) =
      ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i : ℕ) : ℤ) +
        if j % n = 0 then 0 else (((j % n) / p ^ (j / n + 1) : ℕ) : ℤ) + 1 := by
  have hb_lt : j % n < n := Nat.mod_lt j hn
  have hterm (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      oreCoefficientDepth ℚ_[p] n j h +
        min (j / n + if h < j % n then 1 else 0) (padicValNat p h) =
        j / n + 1 + if h < j % n then 1 else 0 := by
    have hh0 : h ≠ 0 := by have := (Finset.mem_Ico.mp hh).1; omega
    have hhK : (h : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hh0
    rw [oreCoefficientDepth_of_cast_ne_zero ℚ_[p] n j hhK,
      _root_.Padic.natCastValuation_eq_padicValNat]
    omega
  have hsum_add : (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h) +
      (∑ h ∈ Finset.Ico 1 n, min (j / n + if h < j % n then 1 else 0) (padicValNat p h)) =
      (n - 1) * (j / n + 1) + (j % n - 1) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Ico, smul_eq_mul, ← Finset.card_filter]
    have hfilt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
      ext h; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
    rw [hfilt, Nat.card_Ico]
  have hj_int : (n : ℤ) * ((j / n : ℕ) : ℤ) + ((j % n : ℕ) : ℤ) = j := by
    exact_mod_cast Nat.div_add_mod j n
  have hsum_int : ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h : ℕ) : ℤ) +
      ((∑ h ∈ Finset.Ico 1 n,
        min (j / n + if h < j % n then 1 else 0) (padicValNat p h) : ℕ) : ℤ) =
      ((n - 1 : ℕ) : ℤ) * (((j / n : ℕ) : ℤ) + 1) + ((j % n - 1 : ℕ) : ℤ) := by
    exact_mod_cast hsum_add
  have hmin_int := congrArg (Nat.cast (R := ℤ)) (sum_min_padicValNat_ore p hn hadm)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_ite, Nat.cast_zero] at hmin_int
  rw [Nat.cast_sub (by omega : 1 ≤ n + j), Nat.cast_add, Nat.cast_one]
  rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
  · simp only [hb0, Nat.zero_sub, Nat.cast_zero, add_zero, ↓reduceIte] at hj_int hsum_int hmin_int ⊢
    rw [Nat.cast_sub hn, Nat.cast_one] at hsum_int
    linarith
  · simp only [hbpos.ne', ↓reduceIte] at hmin_int ⊢
    rw [Nat.cast_sub hn, Nat.cast_sub hbpos, Nat.cast_one] at hsum_int
    linarith

open scoped Classical in
/-- **Pauli–Roblot closed form for Krasner's count over `ℚ_[p]`** ([Pauli–Roblot 2001, Theorem
6.1]): for `0 < n`, the number of totally ramified degree-`n` extensions of `ℚ_[p]` with wild
exponent `j` is `n * p ^ (∑_{i=1}^{j/n} n / p^i)` when `n ∣ j` (and `j` is Ore-admissible),
`n * (p - 1) * p ^ (∑_{i=1}^{j/n} n / p^i + (j % n) / p^{j/n + 1})` when `¬ n ∣ j` (and `j` is
Ore-admissible), and `0` otherwise. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_padic (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 0 < n) (j : ℕ) :
    {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard =
      if IsOreAdmissible ℚ_[p] n j then
        if j % n = 0 then
          n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
        else
          n * (p - 1) * p ^ ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) +
            (j % n) / p ^ (j / n + 1))
      else 0 := by
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp0 : (p : ℚ) ≠ 0 := hp_pos.ne'
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  apply Nat.cast_injective (R := ℚ)
  rw [(krasner_refined_count (K := ℚ_[p]) n j hn).2]
  by_cases hadm : IsOreAdmissible ℚ_[p] n j
  · rw [krasnerCount_of_isOreAdmissible hadm, ite_eq_left hadm, _root_.Padic.natCard_residueField p,
      sum_oreCoefficientDepth_padic p hn hadm]
    rcases eq_or_ne (j % n) 0 with hb0 | hb
    · simp only [hb0, ↓reduceIte, add_zero, zpow_natCast, mul_one]
      push_cast
      rfl
    · simp only [hb, ↓reduceIte]
      rw [← add_assoc, ← Nat.cast_add, zpow_add_one₀ hp0, zpow_natCast]
      push_cast [Nat.cast_sub hp1]
      field_simp
  · rw [krasnerCount_of_not_isOreAdmissible hadm, ite_eq_right hadm, Nat.cast_zero]

/-! ### Mass consistency and isomorphism-class mass at height `j` -/

/-- **Regrouped Serre mass consistency**: summing `# {E ∈ σ_K(n) | c(E) = j} * q ^ (-j)` over all
wild exponents `j` recovers `n`, Serre's first mass formula grouped by wild exponent. -/
theorem tsum_ncard_wildExponent_div_natCard_residueField_pow (n : ℕ) :
    ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  rw [← tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n),
    ← tsum_fiberwise (fun L : totallyRamifiedOfDegree K n ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent) (fun L ↦ L.1.wildExponent)]
  refine tsum_congr fun j ↦ ?_
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  let e : ((fun L : totallyRamifiedOfDegree K n ↦ L.1.wildExponent) ⁻¹' {j}) ≃
      {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} :=
    { toFun L := ⟨L.1.1, L.1.2, L.2⟩
      invFun E := ⟨⟨E.1, E.2.1⟩, E.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j
      = 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j *
          ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
        rw [div_eq_mul_inv, one_div, mul_comm]
    _ = ∑' E : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ E.1.wildExponent := by
        rw [tsum_congr fun E ↦ by rw [E.2.2], ENNReal.tsum_set_const, ← hfin.cast_ncard_eq,
          ENat.toENNReal_coe, mul_comm]
    _ = ∑' L : ((fun L : totallyRamifiedOfDegree K n ↦ L.1.wildExponent) ⁻¹' {j}),
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.1.wildExponent :=
        (e.tsum_eq fun E ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ E.1.wildExponent).symm

/-- **Real-series consistency of `krasnerCount` with Serre's first mass formula**: for `0 < n`,
the real series `∑_j krasnerCount K n j / q ^ j` converges to `n`. -/
theorem hasSum_krasnerCount_div_natCard_residueField_pow {n : ℕ} (hn : 0 < n) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  have hterm (j : ℕ) : (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j =
      (({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j).toReal := by
    have hkc : (krasnerCount K n j : ℝ) =
        ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) := by
      exact_mod_cast (krasner_refined_count (K := K) n j hn).2.symm
    rw [hkc, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_natCast]
  simp_rw [hterm]
  have htsum := tsum_ncard_wildExponent_div_natCard_residueField_pow (K := K) n
  have hne_top : (∑' j : ℕ,
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j) ≠ ⊤ := htsum ▸ ENNReal.natCast_ne_top n
  rw [← ENNReal.toReal_natCast n, ← htsum,
    ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hne_top)]
  exact ENNReal.hasSum_toReal hne_top

namespace IsRepresentativeSet

/-- **Isomorphism-class mass at wild exponent `j`**: for `0 < n` and any representative set `R` of
`σ_K(n)`, the `K`-isomorphism classes in `R` with wild exponent `j` have total automorphism-weighted
mass `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = # {E ∈ σ_K(n) | c(E) = j} / n`. -/
theorem tsum_one_div_natCard_algEquiv_wildExponent_eq {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R)
    (hn : 0 < n) (j : ℕ) :
    ∑' M : {M ∈ R | M.wildExponent = j}, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) / n := by
  classical
  have h := hR.tsum_eq_tsum_div_natCard_algEquiv_mul
    (fun L ↦ if L.wildExponent = j then (1 : ℝ≥0∞) else 0)
    fun e ↦ by rw [IntermediateField.wildExponent_eq_of_algEquiv e]
  -- Evaluate the left-hand side on the finite `j`-stratum of `σ_K(n)`.
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  have hlhs : (∑' L : totallyRamifiedOfDegree K n,
      if L.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
    have hsub := tsum_subtype ({L : totallyRamifiedOfDegree K n | L.1.wildExponent = j})
      (fun _ : totallyRamifiedOfDegree K n ↦ (1 : ℝ≥0∞))
    simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hsub
    rw [← hsub, ENNReal.tsum_set_one]
    let e : {L : totallyRamifiedOfDegree K n | L.1.wildExponent = j} ≃
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} :=
      { toFun L := ⟨L.1.1, L.1.2, L.2⟩
        invFun E := ⟨⟨E.1, E.2.1⟩, E.2.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Set.encard_congr e, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]
  -- Factor `(n : ℝ≥0∞)` out of the right-hand side and restrict to `{M ∈ R | M.wildExponent = j}`.
  have hrhs : (∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
      if M.1.wildExponent = j then 1 else 0) =
      (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j},
        1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) := by
    have heq (M : R) : (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
        (if M.1.wildExponent = j then 1 else 0) =
        (n : ℝ≥0∞) * (if M.1.wildExponent = j then
          1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) else 0) := by
      split_ifs <;> simp [div_eq_mul_inv]
    simp only [heq, ENNReal.tsum_mul_left]
    congr 1
    have hsub := tsum_subtype ({M : R | M.1.wildExponent = j})
      (fun M : R ↦ 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞))
    simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hsub
    rw [← hsub]
    let eR : {M : R | M.1.wildExponent = j} ≃ {M ∈ R | M.wildExponent = j} :=
      { toFun M := ⟨M.1.1, M.1.2, M.2⟩
        invFun M := ⟨⟨M.1, M.2.1⟩, M.2.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    exact eR.tsum_eq fun M ↦ 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)
  rw [hlhs, hrhs] at h
  exact (ENNReal.eq_div_iff (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top _)).mpr h.symm

end IsRepresentativeSet

/-! ### Total count of extensions of given degree -/

/-- **Krasner's total count**: the extended cardinality of `totallyRamifiedOfDegree K n` (in
`ℝ≥0∞`) equals the sum over all wild exponents `j` of `# {E ∈ σ_K(n) | c(E) = j}`, in every
characteristic. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one,
    ← tsum_fiberwise (fun _ : totallyRamifiedOfDegree K n ↦ (1 : ℝ≥0∞))
      (fun L ↦ L.1.wildExponent)]
  refine tsum_congr fun j ↦ ?_
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  let e : ((fun L : totallyRamifiedOfDegree K n ↦ L.1.wildExponent) ⁻¹' {j}) ≃
      {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} :=
    { toFun L := ⟨L.1.1, L.1.2, L.2⟩
      invFun E := ⟨⟨E.1, E.2.1⟩, E.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [e.tsum_eq fun _ ↦ (1 : ℝ≥0∞), ENNReal.tsum_set_one, ← hfin.cast_ncard_eq,
    ENat.toENNReal_coe]

/-- For `0 < n`, the extended cardinality of `totallyRamifiedOfDegree K n` (in `ℝ≥0∞`) is the sum
over Ore-admissible wild exponents `j` of `# {E ∈ σ_K(n) | c(E) = j}`. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum_isOreAdmissible {n : ℕ} (hn : 0 < n) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : {j : ℕ | IsOreAdmissible K n j},
        ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j.1}.ncard : ℝ≥0∞) := by
  rw [encard_totallyRamifiedOfDegree_eq_tsum,
    tsum_subtype {j : ℕ | IsOreAdmissible K n j}
      (fun j ↦ ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞))]
  refine tsum_congr fun j ↦ ?_
  by_cases hadm : IsOreAdmissible K n j
  · simp [hadm]
  · rw [Set.indicator_of_notMem (show j ∉ {j : ℕ | IsOreAdmissible K n j} from hadm)]
    simp only [Nat.cast_eq_zero,
      Set.ncard_eq_zero (finite_totallyRamifiedOfDegree_wildExponent_eq n j)]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro E ⟨hE, rfl⟩
    exact hadm ((ore_realizability n E.wildExponent hn).mp ⟨E, hE, rfl⟩)

/-- Away from equal characteristic `p ∣ n` (that is, whenever `(n : K) ≠ 0`), `σ_K(n)` is finite
and its cardinality is the finite sum of `# {E ∈ σ_K(n) | c(E) = j}` over
`0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.Iic (n * natCastValuation K n hnK),
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard := by
  set B := n * natCastValuation K n hnK
  have hunion : totallyRamifiedOfDegree K n =
      ⋃ j ∈ (Finset.Iic B : Set ℕ),
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} := by
    ext E
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_Iic, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun hE ↦ ⟨E.wildExponent, IntermediateField.wildExponent_le_mul_natCastValuation hE hnK,
      hE, rfl⟩, fun ⟨_, _, hE, _⟩ ↦ hE⟩
  have hdisj : (Finset.Iic B : Set ℕ).PairwiseDisjoint
      (fun j ↦ {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}) :=
    fun _ _ _ _ hne ↦ Set.disjoint_left.mpr fun _ h1 h2 ↦ hne (h1.2.symm.trans h2.2)
  conv_lhs => rw [hunion]
  rw [(Finset.finite_toSet _).ncard_biUnion
    (fun j _ ↦ finite_totallyRamifiedOfDegree_wildExponent_eq n j) hdisj,
    finsum_mem_coe_finset]

/-- When `0 < n` and `(n : K) ≠ 0`, `(#σ_K(n) : ℚ)` is the finite sum of `krasnerCount K n j` over
`0 ≤ j ≤ n * v_K(n)`. -/
theorem cast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) ≠ 0) :
    ((totallyRamifiedOfDegree K n).ncard : ℚ) =
      ∑ j ∈ Finset.Iic (n * natCastValuation K n hnK), krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero hnK, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (krasner_refined_count n j hn).2

/-- Over `ℚ_[p]`, `#σ_{ℚ_[p]}(n)` for `0 < n` is the sum of the stratum counts for
`0 ≤ j ≤ n * v_p(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum_padic (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.Iic (n * padicValNat p n),
        {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard := by
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [ncard_totallyRamifiedOfDegree_eq_sum_of_cast_ne_zero hnK,
    _root_.Padic.natCastValuation_eq_padicValNat]

/-- **`#σ_{ℚ_2}(2) = 6`**: `ℚ_2` has `6` totally ramified quadratic extensions (`2` at wild
exponent `1` and `4` at wild exponent `2`). -/
theorem ncard_totallyRamifiedOfDegree_two_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 2).ncard = 6 := by
  have hv1 : padicValNat 2 1 = 0 := by
    rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hv2 : padicValNat 2 2 = 1 := by
    rw [Nat.padicValNat_def]; exact Nat.Prime.multiplicity_self
  have hIic : Finset.Iic (2 * 1) = {0, 1, 2} := by decide
  rw [ncard_totallyRamifiedOfDegree_eq_sum_padic 2 (by decide : 0 < 2)]
  simp_rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic 2 (by decide : 0 < 2),
    isOreAdmissible_padic_iff 2 (by decide : 0 < 2)]
  rw [hv2, hIic]
  simp [hv1]

/-- **`#σ_{ℚ_3}(3) = 21`**: `ℚ_3` has `21` totally ramified cubic extensions inside
`SeparableClosure ℚ_3` (`6` at wild exponent `1`, `6` at wild exponent `2`, and `9` at wild
exponent `3`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hv1 : padicValNat 3 1 = 0 := by
    rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hv2 : padicValNat 3 2 = 0 := by
    rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hv3 : padicValNat 3 3 = 1 := by
    rw [Nat.padicValNat_def]; exact Nat.Prime.multiplicity_self
  have hIic : Finset.Iic (3 * 1) = {0, 1, 2, 3} := by decide
  rw [ncard_totallyRamifiedOfDegree_eq_sum_padic 3 (by decide : 0 < 3)]
  simp_rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic 3 (by decide : 0 < 3),
    isOreAdmissible_padic_iff 3 (by decide : 0 < 3)]
  rw [hv3, hIic]
  simp [hv1, hv2]

/-- Extended-cardinality form of `#σ_{ℚ_3}(3) = 21`. -/
theorem encard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).encard = 21 := by
  have hfin : (totallyRamifiedOfDegree ℚ_[3] 3).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [ncard_totallyRamifiedOfDegree_three_padicThree]; decide)
  rw [← hfin.cast_ncard_eq, ncard_totallyRamifiedOfDegree_three_padicThree]
  rfl

/-- **`#σ_{ℚ_2}(4) = 92`**: `ℚ_2` has `92` totally ramified quartic extensions inside
`SeparableClosure ℚ_2` (stratum counts `4, 8, 16, 16, 16, 32` at wild exponents
`1, 3, 5, 6, 7, 8`). -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have hv1 : padicValNat 2 1 = 0 := by
    rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hv2 : padicValNat 2 2 = 1 := by
    rw [Nat.padicValNat_def]; exact Nat.Prime.multiplicity_self
  have hv3 : padicValNat 2 3 = 0 := by
    rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hv4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, Nat.padicValNat_def]
    exact Nat.multiplicity_prime_pow 2
  have hIic : Finset.Iic (4 * 2) = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [ncard_totallyRamifiedOfDegree_eq_sum_padic 2 (by decide : 0 < 4)]
  simp_rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic 2 (by decide : 0 < 4),
    isOreAdmissible_padic_iff 2 (by decide : 0 < 4)]
  rw [hv4, hIic]
  simp [hv1, hv2, hv3, hIcc2]

/-- Extended-cardinality form of `#σ_{ℚ_2}(4) = 92`. -/
theorem encard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).encard = 92 := by
  have hfin : (totallyRamifiedOfDegree ℚ_[2] 4).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [ncard_totallyRamifiedOfDegree_four_padicTwo]; decide)
  rw [← hfin.cast_ncard_eq, ncard_totallyRamifiedOfDegree_four_padicTwo]
  rfl

/-- **Canonical tower decomposition of the total degree-`n` count**: for `0 < n`, the extended
cardinality of all subextensions of `SeparableClosure K / K` of degree `n` equals
`∑_{f ∣ n} #σ_{K_f}(n / f)`, where `K_f = unramifiedExtension K (SeparableClosure K) f` is the
canonical unramified extension of degree `f`. (`0 < n` is required because infinite subextensions
have `Module.finrank = 0`.) -/
theorem encard_finrank_eq_sum_totallyRamifiedOfDegree {n : ℕ} (hn : 0 < n) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.encard =
      ∑ f ∈ n.divisors,
        (letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K)
          (unramifiedExtension K (SeparableClosure K) f)
        letI := finiteIntermediateFieldTopology K (SeparableClosure K)
          (unramifiedExtension K (SeparableClosure K) f)
        haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
          (unramifiedExtension K (SeparableClosure K) f)
        (totallyRamifiedOfDegree (unramifiedExtension K (SeparableClosure K) f)
          (n / f)).encard) := by
  -- Partition `{L | finrank K L = n}` by `f = L.inertiaDegree ∈ n.divisors`.
  have hunion : {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n} =
      ⋃ f ∈ (n.divisors : Set ℕ),
        {L : IntermediateField K (SeparableClosure K) |
          Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, Nat.mem_divisors, ne_eq, hn.ne',
      not_false_eq_true, and_true, exists_prop]
    constructor
    · intro hdeg
      have : Module.Finite K L := Module.finite_of_finrank_pos (hdeg ▸ hn)
      let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
      let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
      have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
      have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
      have hmul := ramificationIndex_mul_inertiaDegree K L
      rw [← L.inertiaDegree_eq, hdeg] at hmul
      have hdvd : L.inertiaDegree ∣ n := ⟨ramificationIndex K L, by rw [← hmul, mul_comm]⟩
      exact ⟨L.inertiaDegree, hdvd, (Nat.mul_div_cancel' hdvd).symm ▸ hdeg, rfl⟩
    · rintro ⟨f, hdvd, hdeg, -⟩
      rwa [Nat.mul_div_cancel' hdvd] at hdeg
  have hdisj : (n.divisors : Set ℕ).PairwiseDisjoint
      (fun f ↦ {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f}) :=
    fun _ _ _ _ hne ↦ Set.disjoint_left.mpr fun _ h1 h2 ↦ hne (h1.2.symm.trans h2.2)
  rw [hunion, (Finset.finite_toSet _).encard_biUnion hdisj, finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  have hf0 : f ≠ 0 := Nat.pos_of_mem_divisors hf |>.ne'
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K)
    (unramifiedExtension K (SeparableClosure K) f)
  exact encard_finrank_and_inertiaDegree_eq hf0 (n / f)

end TauCeti
