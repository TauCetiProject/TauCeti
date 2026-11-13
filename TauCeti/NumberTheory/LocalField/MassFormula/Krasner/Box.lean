/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Integral
public import TauCeti.NumberTheory.LocalField.MassFormula.Ore
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Krasner's discriminant boxes in Eisenstein coefficient space

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let `σ_K(n)`
(`TauCeti.totallyRamifiedOfDegree K n`) be the family of totally ramified degree-`n` subextensions
of `SeparableClosure K`. Krasner's discriminant-refined count stratifies `TauCeti.eisensteinSet K n`
into pairwise disjoint boxes `TauCeti.eisensteinBox K n j` indexed by the wild exponent `j`.

For an Ore-admissible pair `(n, j)`, `eisensteinBox K n j` consists of the Eisenstein coefficient
vectors `a : Fin n → K` whose lower coordinates `a_h` (`1 ≤ h < n`) lie in
`𝓂[K] ^ oreCoefficientDepth K n j h`, and additionally avoid the next power of `𝓂[K]` at `j % n`
when `0 < j % n`; for inadmissible `(n, j)` the box is empty. Every polynomial in
`eisensteinBox K n j` is separable over `K`, the boxes partition the separable locus of
`eisensteinSet K n`, and for every `L ∈ σ_K(n)`, `L.rootCount` vanishes on `eisensteinSet K n`
outside `eisensteinBox K n L.wildExponent`, localizing Serre's root-count integral to a single box.

## Main definitions

* `TauCeti.eisensteinBox K n j`: the stratum of `eisensteinSet K n` corresponding to wild
  exponent `j`.

## Main results

* `TauCeti.mem_eisensteinBox_iff_of_map_eq`: valuation characterization on Eisenstein polynomials.
* `TauCeti.separable_monicOfCoeff_of_mem_eisensteinBox`,
  `TauCeti.pairwiseDisjoint_eisensteinBox`,
  `TauCeti.setOf_mem_eisensteinSet_separable_eq_iUnion_eisensteinBox`: the discriminant boxes
  partition the separable Eisenstein polynomials.
* `TauCeti.measurableSet_eisensteinBox`, `TauCeti.measure_eisensteinBox`: measurability and Haar
  volume of `eisensteinBox K n j`.
* `TauCeti.mem_eisensteinBox_iff_wildExponent_adjoin_eq`,
  `IntermediateField.rootCount_eq_zero_of_notMem_eisensteinBox`,
  `IntermediateField.lintegral_rootCount_eisensteinBox`: localization of `L.rootCount` and its
  integral to `eisensteinBox K n L.wildExponent`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, C. R. Acad. Sci. Paris
  **254** (1962), 3470–3472; Colloques Internationaux du CNRS **143**, Paris, 1966, 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, §6.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory
open scoped IntermediateField ENNReal

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff coeff_monicOfCoeff
  map_monicOfCoeff)

section DiscreteValuationRing

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **Krasner's discriminant box** inside the coefficient space `Fin n → K`: empty unless
`IsOreAdmissible K n j`, and otherwise the set of Eisenstein coefficient vectors `a` whose lower
coordinates `a i` (`1 ≤ i < n`) lie in `𝓂[K] ^ oreCoefficientDepth K n j i`, with
`a ⟨j % n, _⟩ ∉ 𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1)` when `0 < j % n`. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | IsOreAdmissible K n j ∧ a ∈ eisensteinSet K n ∧
    (∀ i : Fin n, 1 ≤ (i : ℕ) →
      a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ∧
    ∀ i : Fin n, (i : ℕ) = j % n → 0 < j % n →
      a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i + 1))}

/-- Membership in `TauCeti.eisensteinBox`, unfolded. -/
theorem mem_eisensteinBox {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔
      IsOreAdmissible K n j ∧ a ∈ eisensteinSet K n ∧
        (∀ i : Fin n, 1 ≤ (i : ℕ) →
          a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ∧
        ∀ i : Fin n, (i : ℕ) = j % n → 0 < j % n →
          a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i + 1)) := by
  rw [eisensteinBox, Set.mem_ofPred_eq]

/-- For an inadmissible wild exponent, the discriminant box is empty. -/
theorem eisensteinBox_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ := by
  ext a; simp [mem_eisensteinBox, h]

variable (K) in
/-- No discriminant box exists in degree `0`. -/
@[simp]
theorem eisensteinBox_zero_left (j : ℕ) : eisensteinBox K 0 j = ∅ :=
  eisensteinBox_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

variable (K) in
/-- Every discriminant box lies inside the Eisenstein region. -/
theorem eisensteinBox_subset_eisensteinSet (n j : ℕ) :
    eisensteinBox K n j ⊆ eisensteinSet K n :=
  fun _ ha ↦ (mem_eisensteinBox.mp ha).2.1

/-- **Valuation characterization of `eisensteinBox`.** For `f : 𝒪[K][X]` mapping to
`monicOfCoeff a`, `a ∈ eisensteinBox K n j` holds if and only if `IsOreAdmissible K n j`, `f` is
Eisenstein at `𝓂[K]`, every lower coefficient `f.coeff h` (`1 ≤ h < n`) has valuation at least
`oreCoefficientDepth K n j h`, and when `0 < j % n` the coefficient `f.coeff (j % n)` has valuation
equal to `oreCoefficientDepth K n j (j % n)`. -/
theorem mem_eisensteinBox_iff_of_map_eq {n j : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) :
    a ∈ eisensteinBox K n j ↔
      IsOreAdmissible K n j ∧ f.IsEisensteinAt 𝓂[K] ∧
        (∀ h, 1 ≤ h → h < n → (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h)) ∧
        (0 < j % n → addVal 𝒪[K] (f.coeff (j % n)) = oreCoefficientDepth K n j (j % n)) := by
  have heis : a ∈ eisensteinSet K n ↔ f.IsEisensteinAt 𝓂[K] := by
    rw [mem_eisensteinSet_iff_exists_isEisensteinAt]
    refine ⟨fun ⟨g, hg, hge⟩ ↦ ?_, fun he ↦ ⟨f, hf, he⟩⟩
    exact Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective 𝒪[K] K)
      (hg.trans hf.symm) ▸ hge
  have hai (i : Fin n) : a i = (f.coeff i : K) := by
    rw [← coeff_monicOfCoeff a i, ← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
  rw [mem_eisensteinBox, heis]
  refine and_congr_right fun hadm ↦ and_congr_right fun _ ↦ ?_
  have hn : 0 < n := hadm.pos
  have hlower :
      (∀ i : Fin n, 1 ≤ (i : ℕ) →
        a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ↔
      ∀ h, 1 ≤ h → h < n → (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h) := by
    refine ⟨fun H h hh1 hhn ↦ ?_, fun H i hi1 ↦ ?_⟩
    · have hmem := H ⟨h, hhn⟩ hh1
      rwa [hai ⟨h, hhn⟩, Subtype.coe_injective.mem_set_image, SetLike.mem_coe,
        TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at hmem
    · rw [hai i, Subtype.coe_injective.mem_set_image, SetLike.mem_coe,
        TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
      exact H i hi1 i.isLt
  rw [hlower]
  refine and_congr_right fun hcoeff ↦ ⟨fun hnot hb ↦ ?_, fun hcrit i hi hb ↦ ?_⟩
  · have hle := hcoeff (j % n) hb (Nat.mod_lt j hn)
    have hnb := hnot ⟨j % n, Nat.mod_lt j hn⟩ rfl hb
    rw [hai ⟨j % n, Nat.mod_lt j hn⟩, Subtype.coe_injective.mem_set_image, SetLike.mem_coe,
      TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at hnb
    cases hv : addVal 𝒪[K] (f.coeff (j % n)) with
    | top => exact absurd le_top (hv ▸ hnb)
    | coe m =>
      rw [hv] at hle hnb
      dsimp only at hnb
      norm_cast at hle hnb ⊢
      omega
  · rw [hai i, hi, Subtype.coe_injective.mem_set_image, SetLike.mem_coe,
      TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, hcrit hb]
    norm_cast
    omega

/-- When `0 < n` and `n` is a unit of `𝒪[K]`, the tame box `eisensteinBox K n 0` is the entire
Eisenstein region `eisensteinSet K n`. -/
theorem eisensteinBox_zero_right_of_isUnit {n : ℕ} (hn : 0 < n) (hu : IsUnit (n : 𝒪[K])) :
    eisensteinBox K n 0 = eisensteinSet K n := by
  refine Set.Subset.antisymm (eisensteinBox_subset_eisensteinSet K n 0) fun a ha ↦ ?_
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  refine (mem_eisensteinBox_iff_of_map_eq hf).mpr ⟨isOreAdmissible_zero_right_iff.mpr ⟨hn, hu⟩, he,
    fun h _ hhn ↦ ?_, fun hb ↦ by simp at hb⟩
  have hdepth : oreCoefficientDepth K n 0 h = 1 :=
    (oreCoefficientDepth_def K n 0 h).trans (max_eq_left (ENat.toNat_le_of_le_natCast (by simp)))
  rw [hdepth]
  simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal (n := 1)).mp
    (by simpa using he.mem (hdeg ▸ hhn))

/-- A discriminant box is nonempty if and only if the pair `(n, j)` is Ore-admissible. -/
@[simp]
theorem nonempty_eisensteinBox_iff {n j : ℕ} :
    (eisensteinBox K n j).Nonempty ↔ IsOreAdmissible K n j := by
  refine ⟨fun ⟨a, ha⟩ ↦ (mem_eisensteinBox.mp ha).1, fun hadm ↦ ?_⟩
  obtain ⟨c, hf, hcoeff, hcrit⟩ := hadm.exists_monic_isEisensteinAt
  refine ⟨fun i ↦ c i, (mem_eisensteinBox_iff_of_map_eq (f := monicOfCoeff c) ?_).mpr
    ⟨hadm, hf, hcoeff, hcrit⟩⟩
  rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring]

/-- Every coefficient vector in `eisensteinBox K n j` defines a separable polynomial over `K`,
including in positive characteristic. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  have heis := eisensteinBox_subset_eisensteinSet K n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp heis
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  obtain ⟨hadm, -, -, hcrit⟩ := (mem_eisensteinBox_iff_of_map_eq hf).mp ha
  refine (separable_iff_derivative_ne_zero
    (irreducible_monicOfCoeff_of_mem_eisensteinSet hadm.pos heis)).mpr ?_
  rw [← hf]
  exact hadm.derivative_map_ne_zero_of_isEisensteinAt he hdeg hcrit

variable (K) in
/-- Discriminant boxes for distinct wild exponents are pairwise disjoint. -/
theorem pairwiseDisjoint_eisensteinBox (n : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint (eisensteinBox K n) := by
  intro j₁ _ j₂ _ hne
  refine Set.disjoint_left.mpr fun a ha₁ ha₂ ↦ hne ?_
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
    (eisensteinBox_subset_eisensteinSet K n j₁ ha₁)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  obtain ⟨hadm₁, -, hcoeff₁, hcrit₁⟩ := (mem_eisensteinBox_iff_of_map_eq hf).mp ha₁
  obtain ⟨hadm₂, -, hcoeff₂, hcrit₂⟩ := (mem_eisensteinBox_iff_of_map_eq hf).mp ha₂
  have h₁ := (iInf_addVal_derivative_add_one_eq_iff hadm₁.pos he hdeg).mpr ⟨hadm₁, hcoeff₁, hcrit₁⟩
  have h₂ := (iInf_addVal_derivative_add_one_eq_iff hadm₂.pos he hdeg).mpr ⟨hadm₂, hcoeff₂, hcrit₂⟩
  have heq : ((j₁ + n : ℕ) : ℕ∞) = ((j₂ + n : ℕ) : ℕ∞) := h₁.symm.trans h₂
  norm_cast at heq
  omega

/-- **Partition of the separable Eisenstein polynomials**: for `0 < n`, the separable polynomials
in `eisensteinSet K n` are precisely the union of the discriminant boxes `eisensteinBox K n j`. -/
theorem setOf_mem_eisensteinSet_separable_eq_iUnion_eisensteinBox {n : ℕ} (hn : 0 < n) :
    {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} = ⋃ j, eisensteinBox K n j := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  refine ⟨fun ⟨ha, hsep⟩ ↦ ?_, fun ⟨j, hj⟩ ↦ ⟨eisensteinBox_subset_eisensteinSet K n j hj,
    separable_monicOfCoeff_of_mem_eisensteinBox hj⟩⟩
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hex : ∃ i : Fin n, f.coeff (i + 1) * (i + 1) ≠ 0 := by
    by_contra! hall
    refine ((separable_iff_derivative_ne_zero
      (irreducible_monicOfCoeff_of_mem_eisensteinSet hn ha)).mp hsep) ?_
    have hf0 : f.derivative = 0 := by
      ext m
      rw [coeff_zero, coeff_derivative]
      rcases lt_or_ge m n with hm | hm
      · exact congrArg Subtype.val (hall ⟨m, hm⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    rw [← hf, derivative_map, hf0, Polynomial.map_zero]
  let T : Fin n → ℕ∞ := fun i ↦
    n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + ((i : ℕ) + 1 : ℕ∞)
  have hne_top : (⨅ i : Fin n, T i) ≠ ⊤ := by
    obtain ⟨i, hi⟩ := hex
    refine ne_top_of_le_ne_top ?_ (ciInf_le (OrderBot.bddBelow _) i)
    lift addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) to ℕ using
      (fun h ↦ hi (addVal_eq_top_iff.mp h)) with v hv'
    dsimp only [T]
    rw [← hv', nsmul_eq_mul]
    exact_mod_cast ENat.natCast_ne_top (n * v + (i + 1))
  have hle_iInf : (n : ℕ∞) ≤ ⨅ i : Fin n, T i := by
    refine le_ciInf fun i ↦ ?_
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with hiTop | hiLow
    · exact (by exact_mod_cast hiTop.symm : (n : ℕ∞) = ((i : ℕ) + 1 : ℕ∞)).trans_le le_add_self
    · have hm1 : 1 ≤ addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) :=
        (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal (n := 1)).mp
          (by simpa using he.mem (hdeg ▸ hiLow))
      have hm1' : 1 ≤ addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) := by
        rw [addVal_mul]; exact hm1.trans le_self_add
      exact (nsmul_one n).symm.le.trans ((nsmul_le_nsmul_right hm1' n).trans le_self_add)
  lift ⨅ i : Fin n, T i to ℕ using hne_top with m hm
  have hnm : n ≤ m := by exact_mod_cast hle_iInf
  have hm_eq : (⨅ i : Fin n, T i) = (((m - n) + n : ℕ) : ℕ∞) := by
    rw [← hm, Nat.sub_add_cancel hnm]
  obtain ⟨hadm, hcoeff, hcrit⟩ := (iInf_addVal_derivative_add_one_eq_iff hn he hdeg).mp hm_eq
  exact ⟨m - n, (mem_eisensteinBox_iff_of_map_eq hf).mpr ⟨hadm, he, hcoeff, hcrit⟩⟩

/-- Base ideal-box exponent vector for `eisensteinBox K n j`: `1` at coordinate `0` and
`oreCoefficientDepth K n j i` at lower coordinates `1 ≤ i < n`. -/
private def oreBoxExponent (K : Type*) [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]
    (n j : ℕ) (i : Fin n) : ℕ :=
  if (i : ℕ) = 0 then 1 else oreCoefficientDepth K n j i

private theorem sum_oreBoxExponent (n j : ℕ) (hn : 0 < n) :
    ∑ i : Fin n, oreBoxExponent K n j i =
      1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
  simp only [oreBoxExponent]
  rw [Fin.sum_univ_eq_sum_range (fun h ↦ if h = 0 then 1 else oreCoefficientDepth K n j h),
    ← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hn]
  simp only [↓reduceIte]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun h hh ↦ ?_)
  rw [Finset.mem_Ico] at hh
  exact ite_eq_right (by omega : h ≠ 0)

/-- Removing a single deeper coordinate from an ideal box leaves the vectors in that box whose
`k`-th coordinate avoids the next ideal power. -/
private theorem mem_pi_sdiff_update_succ_iff {n : ℕ} (d : Fin n → ℕ) (k : Fin n)
    {a : Fin n → K} :
    a ∈ (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) \
        (Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d k (d k + 1) i)) ↔
      (∀ i, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) ∧
        a k ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (d k + 1)) := by
  simp only [Set.mem_sdiff, Set.mem_univ_pi]
  refine and_congr_right fun ha ↦ not_congr ⟨fun h ↦ by simpa using h k, fun hk i ↦ ?_⟩
  rcases eq_or_ne i k with rfl | hik
  · simpa using hk
  · simpa [Function.update_of_ne hik] using ha i

/-- Membership in the base Eisenstein subbox attached to `oreBoxExponent K n j`. -/
private theorem mem_pi_oreBoxExponent_sdiff_iff {n j : ℕ} (hn : 0 < n) {a : Fin n → K} :
    a ∈ (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreBoxExponent K n j i)) \
        (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) ''
          ↑(𝓂[K] ^ Function.update (oreBoxExponent K n j) ⟨0, hn⟩
            (oreBoxExponent K n j ⟨0, hn⟩ + 1) i)) ↔
      a ∈ eisensteinSet K n ∧
        ∀ i : Fin n, 1 ≤ (i : ℕ) →
          a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set e := oreBoxExponent K n j
  have he₀ : e i₀ + 1 = 2 := by simp [e, oreBoxExponent, i₀]
  rw [mem_pi_sdiff_update_succ_iff, eisensteinSet_eq_sdiff hn]
  have heis_iff :
      a ∈ (Set.univ.pi fun _ ↦ ((↑) : 𝒪[K] → K) '' ↑𝓂[K]) \
          (Set.univ.pi fun i ↦
            ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update (fun _ ↦ 1) i₀ 2 i)) ↔
        (∀ i, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (1 : ℕ))) ∧
          a i₀ ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (1 + 1)) := by
    simpa [pow_one] using mem_pi_sdiff_update_succ_iff (K := K) (fun _ : Fin n ↦ 1) i₀ (a := a)
  rw [heis_iff, he₀]
  refine ⟨fun ⟨hae, ha0⟩ ↦ ⟨⟨fun i ↦ ?_, ha0⟩, fun i hipos ↦ ?_⟩,
    fun ⟨⟨ha1, ha0⟩, hlow⟩ ↦ ⟨fun i ↦ ?_, ha0⟩⟩
  · have h1 : 1 ≤ e i := by
      dsimp [e, oreBoxExponent]
      split_ifs
      · exact le_rfl
      · exact one_le_oreCoefficientDepth K n j i
    exact Set.image_mono (Ideal.pow_le_pow_right h1) (hae i)
  · exact (ite_eq_right (by omega : (i : ℕ) ≠ 0) : e i = oreCoefficientDepth K n j i) ▸ hae i
  · rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · have hi : i = i₀ := Fin.ext hi0
      simpa [hi, e, oreBoxExponent, i₀] using ha1 i₀
    · simpa only [e, oreBoxExponent, ite_eq_right hipos.ne'] using hlow i hipos

/-- Box-difference presentation of `eisensteinBox K n j` when `j % n = 0`. -/
private theorem eisensteinBox_eq_sdiff_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hmod : j % n = 0) :
    eisensteinBox K n j =
      (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreBoxExponent K n j i)) \
        Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) ''
          ↑(𝓂[K] ^ Function.update (oreBoxExponent K n j) ⟨0, hadm.pos⟩
            (oreBoxExponent K n j ⟨0, hadm.pos⟩ + 1) i) := by
  ext a
  rw [mem_eisensteinBox, mem_pi_oreBoxExponent_sdiff_iff hadm.pos]
  simp [hadm, hmod]

/-- Box-difference presentation of `eisensteinBox K n j` when `0 < j % n`. -/
private theorem eisensteinBox_eq_sdiff_of_mod_pos {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hmod : 0 < j % n) :
    let e := oreBoxExponent K n j
    let i₀ : Fin n := ⟨0, hadm.pos⟩
    let ib : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
    let e₂ := Function.update e ib (e ib + 1)
    eisensteinBox K n j =
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
          Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e i₀ (e i₀ + 1) i)) \
        ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e₂ i)) \
          Set.univ.pi fun i ↦
            ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e₂ i₀ (e₂ i₀ + 1) i)) := by
  dsimp only
  set e := oreBoxExponent K n j
  set i₀ : Fin n := ⟨0, hadm.pos⟩
  set ib : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
  set e₂ := Function.update e ib (e ib + 1) with he₂
  have hib0 : ib ≠ i₀ := fun h ↦ hmod.ne' (congrArg Fin.val h)
  have heb : e ib = oreCoefficientDepth K n j ib := ite_eq_right hmod.ne'
  ext a
  have hbase := mem_pi_oreBoxExponent_sdiff_iff (K := K) (j := j) hadm.pos (a := a)
  rw [Set.mem_sdiff, mem_pi_sdiff_update_succ_iff e₂ i₀, mem_pi_sdiff_update_succ_iff e i₀]
  rw [mem_pi_sdiff_update_succ_iff e i₀] at hbase
  rw [mem_eisensteinBox, ← and_assoc (a := a ∈ eisensteinSet K n), ← hbase]
  simp only [hadm, true_and, he₂, Function.update_of_ne hib0.symm]
  refine and_congr_right fun ⟨hae, ha0⟩ ↦ ⟨fun hcrit ⟨hae₂, _⟩ ↦ ?_, fun hnot i hi _ hmem ↦ ?_⟩
  · have hb_mem := hae₂ ib
    rw [Function.update_self, heb] at hb_mem
    exact hcrit ib rfl hmod hb_mem
  · refine hnot ⟨fun k ↦ ?_, ha0⟩
    rcases eq_or_ne k ib with rfl | hk
    · have hi_eq : i = ib := Fin.ext hi
      rwa [Function.update_self, heb, ← hi_eq]
    · rw [Function.update_of_ne hk]
      exact hae k

end DiscreteValuationRing

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every discriminant box is measurable. -/
theorem measurableSet_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  by_cases hadm : IsOreAdmissible K n j
  · rcases Nat.eq_zero_or_pos (j % n) with hmod | hmod
    · rw [eisensteinBox_eq_sdiff_of_mod_eq_zero hadm hmod]
      exact (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    · rw [eisensteinBox_eq_sdiff_of_mod_pos hadm hmod]
      exact ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)).diff
          ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
            (measurableSet_univ_pi_image_maximalIdeal_pow _))
  · rw [eisensteinBox_of_not_isOreAdmissible hadm]
    exact MeasurableSet.empty

/-- Volume of an ideal box minus the subbox where a single coordinate is deepened by `1`. -/
private theorem measure_pi_sdiff_update_succ {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) (d : Fin n → ℕ) (k : Fin n) :
    μ ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) \
        Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d k (d k + 1) i)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, d i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set d' := Function.update d k (d k + 1)
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := d) (e := d')
    (le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩)
  have hsum : ∑ i, d' i = (∑ i, d i) + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ k),
      ← Finset.add_sum_erase Finset.univ d (Finset.mem_univ k),
      Finset.sdiff_singleton_eq_erase]
    omega
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ d
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ d'
  rw [hμ, mul_one] at h₁ h₂
  rw [hsum] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [measure_sdiff hsub (measurableSet_univ_pi_image_maximalIdeal_pow d').nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

/-- **The volume of Krasner's discriminant box**: for an Ore-admissible pair `(n, j)` and a
left-invariant measure `μ` on `Fin n → K` normalized on the integer box, `eisensteinBox K n j` has
volume `q ^ (-(1 + ∑_{1 ≤ h < n} ν_h)) * (1 - q⁻¹) * (1 - q⁻¹) ^ [0 < j % n]`. -/
theorem measure_eisensteinBox {n j : ℕ} (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hn := hadm.pos
  set e := oreBoxExponent K n j
  set i₀ : Fin n := ⟨0, hn⟩
  set N := 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  have hsum : ∑ i, e i = N := sum_oreBoxExponent (K := K) n j hn
  rcases Nat.eq_zero_or_pos (j % n) with hmod | hmod
  · rw [eisensteinBox_eq_sdiff_of_mod_eq_zero hadm hmod, ite_eq_left hmod, mul_one,
      measure_pi_sdiff_update_succ μ hμ e i₀, hsum]
  · set ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
    set e₂ := Function.update e ib (e ib + 1)
    have hib0 : ib ≠ i₀ := fun h ↦ hmod.ne' (congrArg Fin.val h)
    have hsum₂ : ∑ i, e₂ i = N + 1 := by
      have := Finset.add_sum_erase Finset.univ e (Finset.mem_univ ib)
      rw [Finset.sum_update_of_mem (Finset.mem_univ ib), Finset.sdiff_singleton_eq_erase]
      omega
    let S (d : Fin n → ℕ) : Set (Fin n → K) :=
      (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) \
        Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d i₀ (d i₀ + 1) i)
    have hbox : eisensteinBox K n j = S e \ S e₂ := eisensteinBox_eq_sdiff_of_mod_pos hadm hmod
    have hYX : S e₂ ⊆ S e := fun a ha ↦ by
      rw [mem_pi_sdiff_update_succ_iff] at ha ⊢
      have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := e) (e := e₂)
        (le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩) (Set.mem_univ_pi.mpr ha.1)
      exact ⟨Set.mem_univ_pi.mp hsub, by simpa [e₂, Function.update_of_ne hib0.symm] using ha.2⟩
    have hq : q ≠ 0 := by simp [q, Nat.card_pos.ne']
    have hqt : q ≠ ∞ := ENNReal.natCast_ne_top _
    have hY_vol : μ (S e₂) = (1 / q ^ N * (1 - 1 / q)) * (1 / q) := by
      rw [measure_pi_sdiff_update_succ μ hμ e₂ i₀, hsum₂]
      simp only [one_div]
      rw [pow_succ, ENNReal.mul_inv (.inl (pow_ne_zero _ hq)) (.inl (ENNReal.pow_ne_top hqt))]
      ring
    have hfin_base : 1 / q ^ N * (1 - 1 / q) ≠ ∞ := ENNReal.mul_ne_top
      (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq))
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    have hY_fin : μ (S e₂) ≠ ∞ := hY_vol ▸ ENNReal.mul_ne_top hfin_base
      (ENNReal.div_ne_top ENNReal.one_ne_top hq)
    rw [hbox, ite_eq_right hmod.ne', measure_sdiff hYX
      ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)).nullMeasurableSet hY_fin,
      measure_pi_sdiff_update_succ μ hμ e i₀, hsum, hY_vol,
      ENNReal.mul_sub fun _ _ ↦ hfin_base, mul_one]

/-- **Roots of polynomials in `eisensteinBox K n j` generate extensions of wild exponent `j`.** For
an Eisenstein coefficient vector `a` and any root `x : SeparableClosure K` of `monicOfCoeff a`, `a`
lies in `eisensteinBox K n j` if and only if `K⟮x⟯` has wild exponent `j`. -/
theorem mem_eisensteinBox_iff_wildExponent_adjoin_eq {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    a ∈ eisensteinBox K n j ↔ (K⟮x⟯).wildExponent = j := by
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  rw [mem_eisensteinBox_iff_of_map_eq hf,
    wildExponent_adjoin_eq_iff_of_eisenstein he hdeg (hf ▸ hx)]
  exact ⟨fun ⟨h₁, _, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, he, h₂, h₃⟩⟩

/-- **Root-count localization**: for `L ∈ σ_K(n)` and `a ∈ eisensteinSet K n`, the root count
`L.rootCount a` vanishes outside `eisensteinBox K n L.wildExponent`. -/
theorem _root_.IntermediateField.rootCount_eq_zero_of_notMem_eisensteinBox {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n)
    (hnot : a ∉ eisensteinBox K n L.wildExponent) :
    L.rootCount a = 0 := by
  classical
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have := hL'.2.finite
  rw [L.rootCount_eq_card_filter_adjoin_eq
    (irreducible_monicOfCoeff_of_mem_eisensteinSet (hL'.1 ▸ Module.finrank_pos) ha) hL'.1,
    Multiset.card_eq_zero, Multiset.filter_eq_nil]
  exact fun x hx heq ↦ hnot
    ((mem_eisensteinBox_iff_wildExponent_adjoin_eq ha (mem_aroots.mp hx).2).mpr (heq ▸ rfl))

/-- For `L ∈ σ_K(n)` and any measure `μ` on `Fin n → K`, `L.rootCount` is almost everywhere
measurable on `eisensteinBox K n j`. -/
theorem aemeasurable_rootCount_restrict_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] (μ : Measure (Fin n → K))
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    AEMeasurable (fun a ↦ (L.rootCount a : ℝ≥0∞)) (μ.restrict (eisensteinBox K n j)) :=
  (aemeasurable_rootCount_restrict_eisensteinSet μ hL).mono_measure
    (Measure.restrict_mono (eisensteinBox_subset_eisensteinSet K n j) le_rfl)

/-- **Localized root-count integral**: for `L ∈ σ_K(n)` and a left-invariant measure `μ` normalized
on the integer box, integrating `L.rootCount` over `eisensteinBox K n j` gives
`q ^ (-(n + j)) (1 - q⁻¹)` when `L.wildExponent = j` and `0` otherwise. -/
theorem _root_.IntermediateField.lintegral_rootCount_eisensteinBox {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      if L.wildExponent = j then
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
      else 0 := by
  split_ifs with hj
  · subst hj
    have hind : (eisensteinBox K n L.wildExponent).indicator
        (fun a ↦ (L.rootCount a : ℝ≥0∞)) =
        (eisensteinSet K n).indicator (fun a ↦ (L.rootCount a : ℝ≥0∞)) := by
      ext a
      by_cases hb : a ∈ eisensteinBox K n L.wildExponent
      · rw [Set.indicator_of_mem hb,
          Set.indicator_of_mem (eisensteinBox_subset_eisensteinSet K n _ hb)]
      · rw [Set.indicator_of_notMem hb]
        by_cases he : a ∈ eisensteinSet K n
        · rw [Set.indicator_of_mem he, L.rootCount_eq_zero_of_notMem_eisensteinBox hL he hb,
            Nat.cast_zero]
        · rw [Set.indicator_of_notMem he]
    rw [← lintegral_indicator measurableSet_eisensteinBox, hind,
      lintegral_indicator measurableSet_eisensteinSet, L.lintegral_rootCount hL μ hμ,
      ← IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL, add_comm]
  · have hzero : ∀ a ∈ eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) = 0 := fun a ha ↦ by
      have hnot : a ∉ eisensteinBox K n L.wildExponent := fun ha' ↦
        Set.disjoint_left.mp
          (pairwiseDisjoint_eisensteinBox K n (Set.mem_univ j) (Set.mem_univ _) (Ne.symm hj)) ha ha'
      rw [L.rootCount_eq_zero_of_notMem_eisensteinBox hL
        (eisensteinBox_subset_eisensteinSet K n j ha) hnot, Nat.cast_zero]
    rw [setLIntegral_congr_fun measurableSet_eisensteinBox hzero, lintegral_zero]

end LocalField

end TauCeti
