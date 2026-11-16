/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.RootCount
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Main
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Countable
import TauCeti.NumberTheory.LocalField.MassFormula.Integral
import TauCeti.NumberTheory.LocalField.MassFormula.RootCount

/-!
# Krasner's discriminant-refined count of totally ramified extensions

For a nonarchimedean local field `K` with residue field `𝓀[K]` of cardinality `q`, let `σ_K(n)`
be `TauCeti.totallyRamifiedOfDegree K n` and `c(L)` the wild exponent
`IntermediateField.wildExponent` of `L ∈ σ_K(n)` (so the discriminant exponent is `n - 1 + c(L)`).
For every `n, j : ℕ`, Krasner's formula `TauCeti.krasnerCount K n j : ℕ` gives the exact number
of `L ∈ σ_K(n)` with `c(L) = j`:

* `0` when `(n, j)` is not Ore-admissible;
* `n * q ^ (n + j - 1 - ∑_{1 ≤ h < n} ν_h)` when Ore-admissible with `j % n = 0`;
* `n * (q - 1) * q ^ (n + j - 2 - ∑_{1 ≤ h < n} ν_h)` when Ore-admissible with `j % n ≠ 0`,

where `ν_h = oreCoefficientDepth K n j h`. The natural-number subtractions in the exponents are
faithful by `TauCeti.sum_oreCoefficientDepth_le_of_mod_eq_zero` and
`TauCeti.sum_oreCoefficientDepth_le_of_mod_pos`.

The proof mirrors Serre's proof of the mass formula, localized to the discriminant box
`eisensteinBox K n j`. Every polynomial in `eisensteinBox K n j` is separable and Eisenstein, so
the root counts `L.rootCount a` over `L ∈ σ_K(n)` sum to `n` pointwise on the box. By
`IntermediateField.rootCount_eq_zero_of_notMem_eisensteinBox`, only extensions `L` with `c(L) = j`
contribute to the integral over `eisensteinBox K n j`, and each such extension has root-count
integral `q ^ (-(j + n)) * (1 - q⁻¹)` by `IntermediateField.lintegral_rootCount_eisensteinBox`.
Comparing with `measure_eisensteinBox` yields both finiteness and the exact count
`TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq`.

From the discriminant-refined count we deduce:

* **Bounded-discriminant finiteness** (`TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le`):
  for every local field `K` (including equal characteristic) and fixed `n, D`, only finitely many
  members of `σ_K(n)` have wild exponent at most `D`.
* **Consistency with Serre's first mass formula** (`TauCeti.tsum_krasnerCount_div_pow_eq`,
  `TauCeti.hasSum_krasnerCount_div_pow`, `TauCeti.sum_krasnerCount_div_pow_eq`):
  `∑_j krasnerCount K n j / q ^ j = n`.
* **Isomorphism-class form**
  (`TauCeti.IsRepresentativeSet.mul_tsum_one_div_natCard_algEquiv_wildExponent_eq`,
  `TauCeti.IsRepresentativeSet.sum_one_div_natCard_algEquiv_wildExponent_eq`): for every
  representative set `R` of `σ_K(n)`,
  `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`.
* **Krasner's total count of `σ_K(n)`** (`TauCeti.encard_totallyRamifiedOfDegree_eq_tsum`,
  `TauCeti.encard_totallyRamifiedOfDegree_eq_sum`, `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum`):
  `#σ_K(n) = ∑_j krasnerCount K n j`, which is a finite sum up to `n · v_K(n)` whenever
  `(n : K) ≠ 0`.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's exact natural-number count for degree `n` and wild
  exponent `j`.

## Main results

* `IntermediateField.rootCount_eq_zero_of_notMem_eisensteinBox` and
  `IntermediateField.lintegral_rootCount_eisensteinBox`: vanishing of root counts off the
  discriminant box and localization of Serre's root-count integral to the box.
* `TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq`: Krasner's discriminant-refined count.
* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le`: bounded-discriminant finiteness.
* `TauCeti.tsum_krasnerCount_div_pow_eq`, `TauCeti.hasSum_krasnerCount_div_pow`, and
  `TauCeti.sum_krasnerCount_div_pow_eq`: consistency with Serre's first mass formula.
* `TauCeti.IsRepresentativeSet.sum_one_div_natCard_algEquiv_wildExponent_eq`: isomorphism-class
  mass in each discriminant stratum.
* `TauCeti.encard_totallyRamifiedOfDegree_eq_tsum` and
  `TauCeti.encard_totallyRamifiedOfDegree_eq_sum`: total count of `σ_K(n)`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, CNRS, Paris (1966), 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré
  donné d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1.
-/

public section
noncomputable section

open MeasureTheory Polynomial ValuativeRel IsDiscreteValuationRing TauCeti.Polynomial
open scoped ENNReal IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

section DiscreteValuationRing

variable [IsDiscreteValuationRing 𝒪[K]]

open Classical in
variable (K) in
/-- **Krasner's count** of totally ramified degree-`n` extensions of `K` inside a separable closure
with wild exponent `j`: `0` when `(n, j)` is not Ore-admissible, and otherwise
`n * q ^ (n + j - 1 - ∑_{1 ≤ h < n} ν_h)` when `j % n = 0`, or
`n * (q - 1) * q ^ (n + j - 2 - ∑_{1 ≤ h < n} ν_h)` when `j % n ≠ 0`, where
`q = Nat.card 𝓀[K]` and `ν_h = oreCoefficientDepth K n j h`. -/
def krasnerCount (n j : ℕ) : ℕ :=
  if IsOreAdmissible K n j then
    let q := Nat.card 𝓀[K]
    let S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    if j % n = 0 then n * q ^ (n + j - 1 - S)
    else n * (q - 1) * q ^ (n + j - 2 - S)
  else 0

/-- Outside Ore-admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  simp [krasnerCount, h]

/-- Formula for `krasnerCount` when `(n, j)` is Ore-admissible and `j % n = 0`. -/
theorem krasnerCount_of_isOreAdmissible_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hmod : j % n = 0) :
    krasnerCount K n j =
      n *
        Nat.card 𝓀[K] ^ (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) := by
  simp [krasnerCount, hadm, hmod]

/-- Formula for `krasnerCount` when `(n, j)` is Ore-admissible and `j % n ≠ 0`. -/
theorem krasnerCount_of_isOreAdmissible_of_mod_ne_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hmod : j % n ≠ 0) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) *
        Nat.card 𝓀[K] ^ (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) := by
  simp [krasnerCount, hadm, hmod]

/-- In degree zero, `krasnerCount` is zero. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 :=
  krasnerCount_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

/-- In degree one and wild exponent zero, `krasnerCount` is one. -/
@[simp]
theorem krasnerCount_one_zero : krasnerCount K 1 0 = 1 := by
  rw [krasnerCount_of_isOreAdmissible_of_mod_eq_zero (isOreAdmissible_one_iff.2 rfl) rfl]
  simp

/-- In the tame case (`0 < n` and `n` a unit of `𝒪[K]`), `krasnerCount K n 0 = n`. -/
theorem krasnerCount_zero_right_of_isUnit {n : ℕ} (hn : 0 < n) (hu : IsUnit (n : 𝒪[K])) :
    krasnerCount K n 0 = n := by
  rw [krasnerCount_of_isOreAdmissible_of_mod_eq_zero
    (isOreAdmissible_zero_right_iff.2 ⟨hn, hu⟩) (Nat.zero_mod n)]
  have hdepth : ∀ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n 0 h = 1 := fun h _ ↦ by
    rw [oreCoefficientDepth_def]
    cases hv : addVal 𝒪[K] (h : 𝒪[K]) with
    | top => simp
    | coe v =>
      simp only [Nat.zero_div, zero_add, Nat.zero_mod, Nat.not_lt_zero, ↓reduceIte, add_zero,
        Nat.cast_one]
      rw [ENat.toNat_sub (ENat.natCast_ne_top v), ENat.toNat_one, ENat.toNat_natCast]
      omega
  rw [Finset.sum_congr rfl hdepth, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  simp

end DiscreteValuationRing

section LocalField

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Restricting a sum over a subtype `S` of an `if p x then f x else 0` term to
`{x ∈ S | p x}`. -/
private theorem tsum_ite_eq_tsum_subtype {α : Type*} {S : Set α} (p : α → Prop)
    [DecidablePred p] (f : α → ℝ≥0∞) :
    ∑' x : S, (if p x.1 then f x.1 else 0) = ∑' x : {x ∈ S | p x}, f x.1 := by
  let e : {x ∈ S | p x} ≃ {x : S // p x.1} :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.1.2, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsupp : Function.support (fun x : S ↦ if p x.1 then f x.1 else 0) ⊆ {x : S | p x.1} := by
    intro x hx
    by_contra hnot
    exact hx (ite_eq_right hnot)
  calc ∑' x : S, (if p x.1 then f x.1 else 0)
      = ∑' x : {x : S | p x.1}, (if p x.1.1 then f x.1.1 else 0) :=
          (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' x : {x : S | p x.1}, f x.1.1 := tsum_congr fun x ↦ ite_eq_left x.2
    _ = ∑' x : {x ∈ S | p x}, f x.1 := (Equiv.tsum_eq e (fun x ↦ f x.1.1)).symm

/-! ### Localization of root counts to the discriminant box -/

/-- For `L ∈ σ_K(n)` and an Eisenstein coefficient vector `a ∈ eisensteinSet K n`, if `a` does
not lie in the discriminant box for `L.wildExponent`, then `monicOfCoeff a` has no roots in
`L`. -/
theorem _root_.IntermediateField.rootCount_eq_zero_of_notMem_eisensteinBox {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n)
    (hnot : a ∉ eisensteinBox K n L.wildExponent) : L.rootCount a = 0 := by
  by_contra hne
  have hn : 0 < n := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hL
  rw [IntermediateField.rootCount_def] at hne
  obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne)
  have hroot : aeval (y : SeparableClosure K) (monicOfCoeff a) = 0 := by
    have := (mem_aroots.1 hy).2
    simpa [aeval_algHom_apply] using congrArg L.val this
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg (hf.symm ▸ hroot)
  have := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
  have hEq : K⟮(y : SeparableClosure K)⟯ = L :=
    IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.2 y.2)
      ((mem_totallyRamifiedOfDegree_iff.1 hmem).1.trans
        (mem_totallyRamifiedOfDegree_iff.1 hL).1.symm)
  exact hnot ((mem_eisensteinBox_iff_wildExponent_eq hn ha hroot).2 (congrArg _ hEq))

/-- For `L ∈ σ_K(n)`, the root count of `L` is supported inside
`eisensteinBox K n L.wildExponent`, so its integral over that box agrees with Serre's integral
over the full Eisenstein region: `q ^ (-(L.wildExponent + n)) * (1 - q⁻¹)`. -/
theorem _root_.IntermediateField.lintegral_rootCount_eisensteinBox {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n L.wildExponent, (L.rootCount a : ℝ≥0∞) ∂μ =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (L.wildExponent + n) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have heq :
      ∫⁻ a in eisensteinBox K n L.wildExponent, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ := by
    rw [← lintegral_indicator measurableSet_eisensteinBox,
      ← lintegral_indicator measurableSet_eisensteinSet]
    refine lintegral_congr fun a ↦ ?_
    by_cases haB : a ∈ eisensteinBox K n L.wildExponent
    · rw [Set.indicator_of_mem haB,
        Set.indicator_of_mem (eisensteinBox_subset_eisensteinSet n L.wildExponent haB)]
    · rw [Set.indicator_of_notMem haB]
      by_cases haE : a ∈ eisensteinSet K n
      · rw [Set.indicator_of_mem haE, L.rootCount_eq_zero_of_notMem_eisensteinBox hL haE haB,
          Nat.cast_zero]
      · rw [Set.indicator_of_notMem haE]
  rw [heq, L.lintegral_rootCount hL μ hμ,
    IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL]

/-! ### Krasner's discriminant-refined count -/

/-- **Krasner's discriminant-refined count**: for every degree `n` and wild exponent `j`, the
totally ramified degree-`n` subextensions of `SeparableClosure K` with wild exponent `j` have
exact extended cardinality `krasnerCount K n j` (in particular, this stratum is always finite,
including in equal characteristic). -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard = krasnerCount K n j := by
  by_cases hadm : IsOreAdmissible K n j
  · have hn : 0 < n := hadm.pos
    let : MeasurableSpace (Fin n → K) := borel _
    have : BorelSpace (Fin n → K) := ⟨rfl⟩
    let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
      ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
        rw [isOpen_integerBox.interior_eq]
        exact ⟨0, by simp⟩⟩
    let μ : Measure (Fin n → K) := Measure.addHaarMeasure B
    have hμ : μ (integerBox K (Fin n)) = 1 := Measure.addHaarMeasure_self
    have : Countable (totallyRamifiedOfDegree K n) :=
      (countable_totallyRamifiedOfDegree hn (K := K)).to_subtype
    -- Pointwise on the discriminant box, every polynomial is separable and Eisenstein, so the
    -- root counts over `σ_K(n)` sum to `n`.
    have hpt : ∀ a ∈ eisensteinBox K n j,
        ∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞) = n := fun a ha ↦ by
      obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1
        (eisensteinBox_subset_eisensteinSet n j ha)
      exact tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha)
    have hmeas (L : totallyRamifiedOfDegree K n) :
        AEMeasurable (fun a ↦ (L.1.rootCount a : ℝ≥0∞))
          (μ.restrict (eisensteinBox K n j)) :=
      (aemeasurable_rootCount_restrict_eisensteinSet μ L.2).mono_measure
        (Measure.restrict_mono (eisensteinBox_subset_eisensteinSet n j) le_rfl)
    have hint :
        ∑' L : totallyRamifiedOfDegree K n,
            ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
          n * μ (eisensteinBox K n j) := by
      rw [← lintegral_tsum hmeas, setLIntegral_congr_fun measurableSet_eisensteinBox hpt,
        setLIntegral_const]
    -- Every `L ∈ σ_K(n)` with `L.wildExponent ≠ j` has zero root count on the box.
    set S : Set (IntermediateField K (SeparableClosure K)) :=
      {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
    let c : ℝ≥0∞ :=
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (j + n) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
    have hlhs :
        ∑' L : totallyRamifiedOfDegree K n,
            ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
          (S.encard : ℝ≥0∞) * c := by
      have hterm (L : totallyRamifiedOfDegree K n) :
          ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
            if L.1.wildExponent = j then c else 0 := by
        split_ifs with hj
        · simpa only [c, hj] using L.1.lintegral_rootCount_eisensteinBox L.2 μ hμ
        · refine (setLIntegral_congr_fun measurableSet_eisensteinBox fun a ha ↦ ?_).trans
            (lintegral_zero)
          have hnot : a ∉ eisensteinBox K n L.1.wildExponent :=
            Set.disjoint_left.1 (disjoint_eisensteinBox (Ne.symm hj)) ha
          rw [L.1.rootCount_eq_zero_of_notMem_eisensteinBox L.2
            (eisensteinBox_subset_eisensteinSet n j ha) hnot, Nat.cast_zero]
      simp_rw [hterm]
      rw [tsum_ite_eq_tsum_subtype
          (fun L : IntermediateField K (SeparableClosure K) ↦ L.wildExponent = j) (fun _ ↦ c),
        ENNReal.tsum_set_const]
    rw [hlhs, measure_eisensteinBox hadm μ hμ] at hint
    -- Cancel the nonzero finite factor `1 - q⁻¹` and clear powers of `q`.
    set q : ℕ := Nat.card 𝓀[K]
    have hq1 : 1 < q := Finite.one_lt_card
    have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans hq1).ne'
    have hqt : (q : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top q
    have h1sub_ne0 : (1 : ℝ≥0∞) - 1 / (q : ℝ≥0∞) ≠ 0 := by
      refine (tsub_pos_of_lt ?_).ne'
      rw [one_div]
      exact ENNReal.inv_lt_one.2 (by exact_mod_cast hq1)
    have h1sub_net : (1 : ℝ≥0∞) - 1 / (q : ℝ≥0∞) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have h1sub_eq :
        (1 : ℝ≥0∞) - 1 / (q : ℝ≥0∞) = ((q - 1 : ℕ) : ℝ≥0∞) / (q : ℝ≥0∞) := by
      symm
      refine ENNReal.eq_sub_of_add_eq (ENNReal.div_ne_top ENNReal.one_ne_top hq0) ?_
      have hqadd : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
        norm_cast
        omega
      rw [← ENNReal.add_div, hqadd, ENNReal.div_self hq0 hqt]
    set D : ℕ := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    have henc : (S.encard : ℝ≥0∞) = (krasnerCount K n j : ℝ≥0∞) := by
      by_cases hmod : j % n = 0
      · rw [ite_eq_left hmod, mul_one] at hint
        rw [krasnerCount_of_isOreAdmissible_of_mod_eq_zero hadm hmod]
        have hstep : (S.encard : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (j + n)) =
            (n : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (1 + D)) := by
          refine (ENNReal.mul_left_inj h1sub_ne0 h1sub_net).1 ?_
          simpa only [c, mul_assoc] using hint
        have hle : 1 + D ≤ j + n := by
          have := sum_oreCoefficientDepth_le_of_mod_eq_zero (K := K) hn hmod
          omega
        have hmul := congrArg (· * (q : ℝ≥0∞) ^ (j + n)) hstep
        simp only [mul_assoc, one_div] at hmul
        rw [ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one] at hmul
        have hpow : ((q : ℝ≥0∞) ^ (1 + D))⁻¹ * (q : ℝ≥0∞) ^ (j + n) =
            (q : ℝ≥0∞) ^ (n + j - 1 - D) := by
          have hqpow : (q : ℝ≥0∞) ^ (j + n) =
              (q : ℝ≥0∞) ^ (1 + D) * (q : ℝ≥0∞) ^ (n + j - 1 - D) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hqpow, ← mul_assoc,
            ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul]
        rw [hpow] at hmul
        simpa [Nat.cast_mul, Nat.cast_pow] using hmul
      · rw [ite_eq_right hmod] at hint
        rw [krasnerCount_of_isOreAdmissible_of_mod_ne_zero hadm hmod]
        have hstep : (S.encard : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (j + n)) =
            (n : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (1 + D) * (1 - 1 / (q : ℝ≥0∞))) := by
          refine (ENNReal.mul_left_inj h1sub_ne0 h1sub_net).1 ?_
          have hcomm :
              (n : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (1 + D) * (1 - 1 / (q : ℝ≥0∞)) *
                  (1 - 1 / (q : ℝ≥0∞))) =
                (n : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (1 + D) * (1 - 1 / (q : ℝ≥0∞))) *
                  (1 - 1 / (q : ℝ≥0∞)) := by ring
          simpa only [c, mul_assoc] using hint.trans hcomm
        have hle : 2 + D ≤ j + n := by
          have hmod_pos : 0 < j % n := Nat.pos_of_ne_zero hmod
          have hmod_lt : j % n < n := Nat.mod_lt j hn
          have hmod_le : j % n ≤ j := Nat.mod_le j n
          have := sum_oreCoefficientDepth_le_of_mod_pos (K := K) hn hmod_pos
          omega
        rw [h1sub_eq] at hstep
        have hmul := congrArg (· * (q : ℝ≥0∞) ^ (j + n)) hstep
        simp only [mul_assoc, one_div] at hmul
        rw [ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one] at hmul
        have hpow :
            ((q : ℝ≥0∞) ^ (1 + D))⁻¹ *
                (((q - 1 : ℕ) : ℝ≥0∞) / (q : ℝ≥0∞) * (q : ℝ≥0∞) ^ (j + n)) =
              ((q - 1 : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j - 2 - D) := by
          have hqpow : (q : ℝ≥0∞) ^ (j + n) =
              (q : ℝ≥0∞) ^ (1 + D) * (q : ℝ≥0∞) *
                (q : ℝ≥0∞) ^ (n + j - 2 - D) := by
            rw [← pow_succ, ← pow_add]
            congr 1
            omega
          rw [div_eq_mul_inv, hqpow]
          have hqinv : ((q : ℝ≥0∞) ^ (1 + D))⁻¹ * (q : ℝ≥0∞) ^ (1 + D) = 1 :=
            ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt)
          have hqinv1 : (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞) = 1 :=
            ENNReal.inv_mul_cancel hq0 hqt
          calc ((q : ℝ≥0∞) ^ (1 + D))⁻¹ *
                (((q - 1 : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ *
                  ((q : ℝ≥0∞) ^ (1 + D) * (q : ℝ≥0∞) *
                    (q : ℝ≥0∞) ^ (n + j - 2 - D)))
              = ((q - 1 : ℕ) : ℝ≥0∞) *
                  (((q : ℝ≥0∞) ^ (1 + D))⁻¹ * (q : ℝ≥0∞) ^ (1 + D)) *
                  ((q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)) *
                  (q : ℝ≥0∞) ^ (n + j - 2 - D) := by ring
            _ = ((q - 1 : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j - 2 - D) := by
                rw [hqinv, hqinv1, mul_one, mul_one]
        rw [hpow] at hmul
        simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hmul
    exact ENat.toENNReal_inj.1 (by simpa only [ENat.toENNReal_coe] using henc)
  · have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.eq_empty_of_forall_notMem fun E hE ↦
        hadm ((ore_realizability n j).1 ⟨E, hE.1, hE.2⟩)
    rw [hempty, Set.encard_empty, krasnerCount_of_not_isOreAdmissible hadm, Nat.cast_zero]

/-- Each fixed-discriminant stratum of `σ_K(n)` is finite, including in equal characteristic. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite :=
  Set.finite_of_encard_eq_coe (encard_totallyRamifiedOfDegree_wildExponent_eq n j)

/-- Exact natural-number cardinality of the stratum `{E ∈ σ_K(n) | E.wildExponent = j}`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard = krasnerCount K n j := by
  rw [Set.ncard_def, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toNat_natCast]

/-- **Bounded-discriminant finiteness**: for every nonarchimedean local field `K` (including equal
characteristic) and fixed degree `n` and bound `D`, there are only finitely many members of
`σ_K(n)` with wild exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D}.Finite := by
  refine ((Finset.finite_toSet (Finset.range (D + 1))).biUnion fun j _ ↦
    finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset fun E hE ↦ ?_
  exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hE.2)) ⟨hE.1, rfl⟩

/-! ### Consistency with Serre's mass formula -/

/-- **Consistency with Serre's first mass formula**: summing Krasner's stratum counts weighted
by `q ^ (-j)` recovers Serre's mass formula `∑' j, krasnerCount K n j / q ^ j = n` in `ℝ≥0∞`. -/
theorem tsum_krasnerCount_div_pow_eq (n : ℕ) :
    ∑' j : ℕ, (krasnerCount K n j : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  let S (j : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  have hU : totallyRamifiedOfDegree K n = ⋃ j : ℕ, S j := by
    ext E
    simp [S]
  have hdisj : Set.univ.PairwiseDisjoint S := fun j₁ _ j₂ _ hne ↦
    Set.disjoint_left.2 fun _ h₁ h₂ ↦ hne (h₁.2.symm.trans h₂.2)
  rw [← tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n), hU,
    tsum_iUnion (f := fun E : IntermediateField K (SeparableClosure K) ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ E.wildExponent) hdisj]
  refine tsum_congr fun j ↦ ?_
  rw [tsum_congr fun E : S j ↦ by rw [E.2.2], ENNReal.tsum_set_const,
    encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe, mul_one_div]

/-- Real-series consistency with Serre's first mass formula:
`∑_j krasnerCount K n j / q ^ j = n` converges in `ℝ`, also in equal characteristic. -/
theorem hasSum_krasnerCount_div_pow (n : ℕ) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  have h := tsum_krasnerCount_div_pow_eq (K := K) n
  have hne :
      (∑' j : ℕ, (krasnerCount K n j : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j) ≠ ∞ := by
    rw [h]; exact ENNReal.natCast_ne_top n
  have hs := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hne), h, ENNReal.toReal_natCast] at hs
  refine hs.congr_fun fun j ↦ ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_natCast]

/-- Finite rational consistency with Serre's first mass formula when `(n : K) ≠ 0`:
`∑_{j ≤ n v_K(n)} krasnerCount K n j / q ^ j = n` in `ℚ`. -/
theorem sum_krasnerCount_div_pow_eq {n : ℕ} (hnK : (n : K) ≠ 0) :
    ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1),
        (krasnerCount K n j : ℚ) / (Nat.card 𝓀[K] : ℚ) ^ j = n := by
  set N : ℕ := n * natCastValuation K n hnK
  have htsum := tsum_krasnerCount_div_pow_eq (K := K) n
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun j hj ↦ ?_] at htsum
  · set q : ℕ := Nat.card 𝓀[K]
    have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := 𝓀[K])).ne'
    have hqt : (q : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top q
    have hmul := congrArg (· * (q : ℝ≥0∞) ^ N) htsum
    rw [Finset.sum_mul] at hmul
    have hnat : ∑ j ∈ Finset.range (N + 1), krasnerCount K n j * q ^ (N - j) = n * q ^ N := by
      have heq : (∑ j ∈ Finset.range (N + 1),
            ((krasnerCount K n j * q ^ (N - j) : ℕ) : ℝ≥0∞)) =
          ((n * q ^ N : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_pow, ← hmul]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hjle : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hqN : (q : ℝ≥0∞) ^ N = (q : ℝ≥0∞) ^ j * (q : ℝ≥0∞) ^ (N - j) := by
          rw [← pow_add, Nat.add_sub_of_le hjle]
        rw [div_eq_mul_inv, mul_assoc, Nat.cast_mul, Nat.cast_pow]
        congr 1
        rw [hqN, ← mul_assoc,
          ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul]
      rw [← Nat.cast_sum] at heq
      exact_mod_cast heq
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := 𝓀[K])).ne'
    have hmulQ : (∑ j ∈ Finset.range (N + 1), (krasnerCount K n j : ℚ) / (q : ℚ) ^ j) *
        (q : ℚ) ^ N = (n : ℚ) * (q : ℚ) ^ N := by
      rw [Finset.sum_mul]
      have hcast :
          ((∑ j ∈ Finset.range (N + 1), krasnerCount K n j * q ^ (N - j) : ℕ) : ℚ) =
            ((n * q ^ N : ℕ) : ℚ) := by exact_mod_cast hnat
      push_cast at hcast
      rw [← hcast]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjle : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hqN : (q : ℚ) ^ N = (q : ℚ) ^ j * (q : ℚ) ^ (N - j) := by
        rw [← pow_add, Nat.add_sub_of_le hjle]
      rw [hqN, div_mul_eq_mul_div, mul_comm ((q : ℚ) ^ j), ← mul_assoc,
        mul_div_cancel_right₀ _ (pow_ne_zero _ hqQ)]
    exact mul_right_cancel₀ (pow_ne_zero N hqQ) hmulQ
  · have hnot : ¬ IsOreAdmissible K n j := fun hadm ↦
      hj (Finset.mem_range.2 (Nat.lt_succ_of_le (hadm.le_mul_natCastValuation hnK)))
    rw [krasnerCount_of_not_isOreAdmissible hnot, Nat.cast_zero, ENNReal.zero_div]

/-! ### Isomorphism-class form -/

namespace IsRepresentativeSet

variable {n : ℕ} {R : Set (IntermediateField K (SeparableClosure K))}

/-- In any set of representatives `R` of `σ_K(n)`, each wild-exponent stratum is finite. -/
theorem finite_wildExponent_eq (hR : IsRepresentativeSet n R) (j : ℕ) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_eq n j).subset
    fun _ hM ↦ ⟨hR.subset hM.1, hM.2⟩

/-- **Isomorphism-class form of Krasner's count** (in `ℝ≥0∞`): regrouping the stratum
`{E ∈ σ_K(n) | E.wildExponent = j}` along `K`-isomorphism classes gives
`n * ∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j`. -/
theorem mul_tsum_one_div_natCard_algEquiv_wildExponent_eq (hR : IsRepresentativeSet n R)
    (j : ℕ) :
    (n : ℝ≥0∞) *
        ∑' M : {M ∈ R | M.wildExponent = j}, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) =
      krasnerCount K n j := by
  classical
  let ind (L : IntermediateField K (SeparableClosure K)) : ℝ≥0∞ :=
    if L.wildExponent = j then 1 else 0
  have hreg := hR.tsum_eq_tsum_div_natCard_algEquiv_mul ind fun e ↦ by
    simp only [ind, IntermediateField.wildExponent_eq_of_algEquiv e]
  have hlhs : ∑' L : totallyRamifiedOfDegree K n, ind L = krasnerCount K n j := by
    simp only [ind]
    rw [tsum_ite_eq_tsum_subtype
        (fun L : IntermediateField K (SeparableClosure K) ↦ L.wildExponent = j)
        (fun _ ↦ (1 : ℝ≥0∞)),
      ENNReal.tsum_set_one, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe]
  have hrhs :
      ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * ind M =
        (n : ℝ≥0∞) *
          ∑' M : {M ∈ R | M.wildExponent = j}, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * ind M
        = ∑' M : R, if M.1.wildExponent = j then
            (n : ℝ≥0∞) * (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)) else 0 :=
          tsum_congr fun M ↦ by simp only [ind, mul_ite, mul_one, mul_zero, mul_one_div]
      _ = ∑' M : {M ∈ R | M.wildExponent = j},
            (n : ℝ≥0∞) * (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)) :=
          tsum_ite_eq_tsum_subtype
            (fun M : IntermediateField K (SeparableClosure K) ↦ M.wildExponent = j)
            (fun M : IntermediateField K (SeparableClosure K) ↦
              (n : ℝ≥0∞) * (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)))
  exact hrhs.symm.trans (hreg.symm.trans hlhs)

/-- **Isomorphism-class mass in each discriminant stratum** (in `ℚ`): for `0 < n` and any
representative set `R` of `σ_K(n)`,
`∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`. -/
theorem sum_one_div_natCard_algEquiv_wildExponent_eq (hR : IsRepresentativeSet n R) (hn : 0 < n)
    (j : ℕ) :
    ∑ M ∈ (hR.finite_wildExponent_eq j).toFinset, (1 : ℚ) / Nat.card (M ≃ₐ[K] M) =
      (krasnerCount K n j : ℚ) / n := by
  classical
  set s := (hR.finite_wildExponent_eq j).toFinset
  have htsum := hR.mul_tsum_one_div_natCard_algEquiv_wildExponent_eq j
  have hfin_sum :
      (n : ℝ≥0∞) * ∑ M ∈ s, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) =
        krasnerCount K n j := by
    rw [← htsum]
    congr 1
    have hcoe : (s : Set (IntermediateField K (SeparableClosure K))) =
        {M ∈ R | M.wildExponent = j} := Set.Finite.coe_toFinset _
    rw [← hcoe, tsum_fintype, ← Finset.sum_coe_sort]
    convert rfl
  have hAut (M : IntermediateField K (SeparableClosure K)) (hM : M ∈ s) :
      Nat.card (M ≃ₐ[K] M) ≠ 0 := by
    have hM' : M ∈ totallyRamifiedOfDegree K n :=
      hR.subset ((Set.Finite.mem_toFinset _).1 hM).1
    have := (mem_totallyRamifiedOfDegree_iff.1 hM').2.finite
    exact Nat.card_ne_zero.2 ⟨⟨.refl⟩, inferInstance⟩
  -- Clear all automorphism denominators in `ℕ` by multiplying by their product `P`.
  set P : ℕ := ∏ M ∈ s, Nat.card (M ≃ₐ[K] M)
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 hAut
  have hmul := congrArg (· * (P : ℝ≥0∞)) hfin_sum
  rw [mul_assoc, Finset.sum_mul] at hmul
  have hnat : n * ∑ M ∈ s, P / Nat.card (M ≃ₐ[K] M) = krasnerCount K n j * P := by
    have heq : ((n * ∑ M ∈ s, P / Nat.card (M ≃ₐ[K] M) : ℕ) : ℝ≥0∞) =
        ((krasnerCount K n j * P : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sum, ← hmul]
      congr 1
      refine Finset.sum_congr rfl fun M hM ↦ ?_
      have hdvd : Nat.card (M ≃ₐ[K] M) ∣ P := Finset.dvd_prod_of_mem _ hM
      have ha0 : (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hAut M hM
      have hat : (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      rw [one_div, mul_comm, ← div_eq_mul_inv, ENNReal.eq_div_iff ha0 hat]
      exact_mod_cast Nat.mul_div_cancel' hdvd
    exact_mod_cast heq
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hPQ : (P : ℚ) ≠ 0 := by exact_mod_cast hP0
  have hmulQ : (n : ℚ) * ((∑ M ∈ s, (1 : ℚ) / Nat.card (M ≃ₐ[K] M)) * (P : ℚ)) =
      (krasnerCount K n j : ℚ) * (P : ℚ) := by
    rw [Finset.sum_mul]
    have hcast : ((n * ∑ M ∈ s, P / Nat.card (M ≃ₐ[K] M) : ℕ) : ℚ) =
        ((krasnerCount K n j * P : ℕ) : ℚ) := by exact_mod_cast hnat
    push_cast at hcast
    rw [← hcast]
    congr 1
    refine Finset.sum_congr rfl fun M hM ↦ ?_
    have hdvd : Nat.card (M ≃ₐ[K] M) ∣ P := Finset.dvd_prod_of_mem _ hM
    have haQ : (Nat.card (M ≃ₐ[K] M) : ℚ) ≠ 0 := by exact_mod_cast hAut M hM
    rw [one_div_mul_eq_div, div_eq_iff haQ]
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  rw [eq_div_iff hnQ]
  have hcancel : (n : ℚ) * (∑ M ∈ s, (1 : ℚ) / Nat.card (M ≃ₐ[K] M)) =
      (krasnerCount K n j : ℚ) :=
    mul_right_cancel₀ hPQ (by simpa [mul_assoc] using hmulQ)
  linarith

end IsRepresentativeSet

/-! ### Krasner's total count of `σ_K(n)` -/

/-- **Krasner's total count** (infinite-sum form): the extended cardinality of `σ_K(n)` in
`ℝ≥0∞` is the sum over all wild exponents `j` of `krasnerCount K n j`. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : ℕ, (krasnerCount K n j : ℝ≥0∞) := by
  let S (j : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  have hU : totallyRamifiedOfDegree K n = ⋃ j : ℕ, S j := by
    ext E
    simp [S]
  have hdisj : Set.univ.PairwiseDisjoint S := fun j₁ _ j₂ _ hne ↦
    Set.disjoint_left.2 fun _ h₁ h₂ ↦ hne (h₁.2.symm.trans h₂.2)
  rw [← ENNReal.tsum_set_one, hU,
    tsum_iUnion (f := fun _ : IntermediateField K (SeparableClosure K) ↦ (1 : ℝ≥0∞)) hdisj]
  refine tsum_congr fun j ↦ ?_
  rw [ENNReal.tsum_set_one, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe]

/-- **Krasner's total count** (finite-sum form): whenever `(n : K) ≠ 0`, `σ_K(n)` has extended
cardinality `∑_{j ≤ n v_K(n)} krasnerCount K n j`. -/
theorem encard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).encard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  have h := encard_totallyRamifiedOfDegree_eq_tsum (K := K) n
  rw [tsum_eq_sum (s := Finset.range (n * natCastValuation K n hnK + 1)) fun j hj ↦ ?_,
    ← Nat.cast_sum] at h
  · exact ENat.toENNReal_inj.1 (by simpa only [ENat.toENNReal_coe] using h)
  · have hnot : ¬ IsOreAdmissible K n j := fun hadm ↦
      hj (Finset.mem_range.2 (Nat.lt_succ_of_le (hadm.le_mul_natCastValuation hnK)))
    rw [krasnerCount_of_not_isOreAdmissible hnot, Nat.cast_zero]

/-- Whenever `(n : K) ≠ 0`, `σ_K(n)` has natural-number cardinality
`∑_{j ≤ n v_K(n)} krasnerCount K n j`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  rw [Set.ncard_def, encard_totallyRamifiedOfDegree_eq_sum hnK, ENat.toNat_natCast]

end LocalField

end TauCeti
