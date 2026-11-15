/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import TauCeti.FieldTheory.IntermediateField.RootCount
public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Ore
import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Separable
import TauCeti.NumberTheory.LocalField.MassFormula.Integral
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The discriminant box in Eisenstein coefficient space

For a positive degree `n` and a wild exponent `j`, the *discriminant box*
`TauCeti.eisensteinBox K n j` inside the Eisenstein region `TauCeti.eisensteinSet K n` cuts out the
monic Eisenstein polynomials whose roots generate totally ramified degree-`n` extensions of wild
exponent `j` (equivalently, discriminant exponent `n - 1 + j`).

When `(n, j)` is not Ore-admissible, the box is empty. For an Ore-admissible pair `(n, j)` with
Euclidean division `j = (j / n) * n + j % n`, a coefficient vector `a : Fin n → K` in
`eisensteinSet K n` belongs to `eisensteinBox K n j` when:
* for every `1 ≤ h < n`, `a_h` lies in `𝓂[K] ^ oreCoefficientDepth K n j h`; and
* when `0 < j % n`, `a_{j % n}` does not lie in `𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1)`.

Via the derivative-minimum criterion `TauCeti.iInf_eisenstein_derivative_eq_iff`, these boxes are
pairwise disjoint for distinct `j`, consist entirely of separable polynomials, and cover all
separable polynomials in `eisensteinSet K n` (hence almost all of `eisensteinSet K n` for additive
Haar measure, including in equal characteristic).

To compute the Haar measure without product-measure machinery, each box is written as either a
single difference of ideal-power boxes (when `j % n = 0`) or a nested difference of two such
slices (when `0 < j % n`), evaluated through
`MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow`. Finally, for any
`L ∈ totallyRamifiedOfDegree K n`, `L.rootCount` vanishes identically on
`eisensteinSet K n \ eisensteinBox K n L.wildExponent`, reducing its integral over
`eisensteinBox K n j` directly to Serre's integral `IntermediateField.lintegral_rootCount`.

## Main definitions

* `TauCeti.eisensteinBox K n j`: the discriminant box in `Fin n → K` for degree `n` and wild
  exponent `j`.

## Main results

* `TauCeti.mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq`: membership in `eisensteinBox K n j`
  is equivalent to the Eisenstein derivative valuation minimum being `n - 1 + j`.
* `TauCeti.pairwiseDisjoint_eisensteinBox`: the boxes `eisensteinBox K n j` are pairwise disjoint in
  `j`.
* `TauCeti.iUnion_eisensteinBox_eq_setOf_separable` and
  `TauCeti.ae_iUnion_eisensteinBox_eq_eisensteinSet`: in positive degree, the union of the boxes is
  exact on separable Eisenstein polynomials and equals `eisensteinSet K n` almost everywhere.
* `TauCeti.mem_eisensteinBox_iff_wildExponent_adjoin_eq`: at a root `x` of an Eisenstein polynomial
  `monicOfCoeff a`, `(K⟮x⟯).wildExponent = j` if and only if `a ∈ eisensteinBox K n j`.
* `TauCeti.measure_eisensteinBox`: the normalized additive Haar measure of an admissible box.
* `IntermediateField.lintegral_rootCount_eisensteinBox`: the integral of `L.rootCount` over
  `eisensteinBox K n j` is `q ^ (-(n + j)) (1 - q⁻¹)` when `L.wildExponent = j` and `0` otherwise.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `p`-adique*, Colloq. Internat.
  CNRS **143** (1966), 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory TauCeti.Polynomial
open scoped IntermediateField ENNReal

namespace TauCeti

section DiscreteValuation

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **The discriminant box** in `Fin n → K` associated with degree `n` and wild exponent `j`. It is
empty unless `IsOreAdmissible K n j`; for admissible `(n, j)` it consists of the Eisenstein
coefficient vectors `a` with `a_h ∈ 𝓂[K] ^ oreCoefficientDepth K n j h` for `1 ≤ h < n` and, when
`0 < j % n`, `a_{j % n} ∉ 𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1)`. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | ∃ hadm : IsOreAdmissible K n j,
    a ∈ eisensteinSet K n ∧
      (∀ h (hhn : h < n), 0 < h →
        a ⟨h, hhn⟩ ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j h)) ∧
      (0 < j % n →
        a ⟨j % n, Nat.mod_lt j hadm.pos⟩ ∉
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1)))}

/-- Explicit membership characterization for `eisensteinBox`. -/
theorem mem_eisensteinBox_iff {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔
      ∃ hadm : IsOreAdmissible K n j,
        a ∈ eisensteinSet K n ∧
          (∀ h (hhn : h < n), 0 < h →
            a ⟨h, hhn⟩ ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j h)) ∧
          (0 < j % n →
            a ⟨j % n, Nat.mod_lt j hadm.pos⟩ ∉
              ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1))) :=
  Iff.rfl

/-- Outside Ore-admissible parameters, the discriminant box is empty. -/
theorem eisensteinBox_eq_empty_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨hadm, _⟩ ↦ h hadm

/-- In degree zero, every discriminant box is empty. -/
@[simp]
theorem eisensteinBox_zero (j : ℕ) : eisensteinBox K 0 j = ∅ :=
  eisensteinBox_eq_empty_of_not_isOreAdmissible (not_isOreAdmissible_zero j)

/-- Every discriminant box lies inside the Eisenstein region. -/
theorem eisensteinBox_subset_eisensteinSet {n j : ℕ} :
    eisensteinBox K n j ⊆ eisensteinSet K n :=
  fun _ ⟨_, ha, _⟩ ↦ ha

/-- If a discriminant box is nonempty, its parameters satisfy Ore's conditions. -/
theorem isOreAdmissible_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : IsOreAdmissible K n j :=
  ha.1

/-- Reading ideal-power membership of `a i` as a valuation bound on the integral polynomial `f`. -/
private theorem coeff_mem_image_maximalIdeal_pow_iff {n k : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) (i : Fin n) :
    a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ k) ↔ (k : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i) := by
  have hai : a i = (f.coeff i : K) := by
    rw [← coeff_monicOfCoeff a i, ← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
  rw [hai, Subtype.val_injective.mem_set_image, SetLike.mem_coe,
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]

/-- **Derivative-minimum characterization of `eisensteinBox`.** Let `f : 𝒪[K][X]` be Eisenstein at
`𝓂[K]` with image `monicOfCoeff a` for `a : Fin n → K`. Then `a ∈ eisensteinBox K n j` if and only
if the minimum valuation of `n • v_K(f_h * h) + (h - 1)` equals `n - 1 + j`. -/
theorem mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq {n j : ℕ} {a : Fin n → K}
    {f : 𝒪[K][X]} (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a)
    (he : f.IsEisensteinAt 𝓂[K]) :
    a ∈ eisensteinBox K n j ↔
      (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) =
        ((n - 1 + j : ℕ) : ℕ∞) := by
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have ha : a ∈ eisensteinSet K n := mem_eisensteinSet_iff_exists_isEisensteinAt.mpr ⟨f, hf, he⟩
  rw [iInf_eisenstein_derivative_eq_iff he hdeg]
  constructor
  · rintro ⟨hadm, _, hdepth, hmod⟩
    have hn := hadm.pos
    refine ⟨hadm, fun h hh0 hhn ↦ ?_, fun hb ↦ ?_⟩
    · exact (coeff_mem_image_maximalIdeal_pow_iff hf ⟨h, hhn⟩).mp (hdepth h hhn hh0)
    · have hle := (coeff_mem_image_maximalIdeal_pow_iff hf ⟨j % n, Nat.mod_lt j hn⟩).mp
        (hdepth (j % n) (Nat.mod_lt j hn) hb)
      have hnot : ¬ (((oreCoefficientDepth K n j (j % n) + 1 : ℕ) : ℕ∞) ≤
          addVal 𝒪[K] (f.coeff (j % n))) :=
        fun h1 ↦ hmod hb ((coeff_mem_image_maximalIdeal_pow_iff hf ⟨j % n, Nat.mod_lt j hn⟩).mpr h1)
      induction hv : addVal 𝒪[K] (f.coeff (j % n)) with
      | top => simp [hv] at hnot
      | coe v =>
        rw [hv, Nat.cast_le] at hle hnot
        exact congrArg Nat.cast (by omega)
  · rintro ⟨hadm, hdepth, hmod⟩
    have hn := hadm.pos
    refine ⟨hadm, ha, fun h hhn hh0 ↦ ?_, fun hb hmem ↦ ?_⟩
    · exact (coeff_mem_image_maximalIdeal_pow_iff hf ⟨h, hhn⟩).mpr (hdepth h hh0 hhn)
    · have h1 := (coeff_mem_image_maximalIdeal_pow_iff hf ⟨j % n, Nat.mod_lt j hn⟩).mp hmem
      rw [hmod hb, Nat.cast_le] at h1
      omega

/-- Discriminant boxes for distinct wild exponents are disjoint. -/
theorem disjoint_eisensteinBox {n j j' : ℕ} (hne : j ≠ j') :
    Disjoint (eisensteinBox K n j) (eisensteinBox K n j') := by
  refine Set.disjoint_left.mpr fun a hj hj' ↦ hne ?_
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
    (eisensteinBox_subset_eisensteinSet hj)
  have h1 := (mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq hf he).mp hj
  have h2 := (mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq hf he).mp hj'
  have heq : n - 1 + j = n - 1 + j' := Nat.cast_inj.mp (h1.symm.trans h2)
  omega

/-- The family `j ↦ eisensteinBox K n j` is pairwise disjoint on `ℕ`. -/
theorem pairwiseDisjoint_eisensteinBox (n : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint (eisensteinBox K n) :=
  fun _ _ _ _ hne ↦ disjoint_eisensteinBox hne

/-- Every polynomial in a discriminant box is separable over `K`. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  have hn := ha.1.pos
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
    (eisensteinBox_subset_eisensteinSet ha)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hinf := (mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq hf he).mp ha
  exact hf ▸ (separable_map_iff_iInf_eisenstein_derivative_ne_top he hdeg hn).mpr
    (hinf ▸ ENat.natCast_ne_top _)

/-- For an Eisenstein polynomial of positive degree `n`, every derivative valuation term is at least
`n - 1`. -/
private theorem le_iInf_eisenstein_derivative {n : ℕ} {f : 𝒪[K][X]}
    (he : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n) :
    ((n - 1 : ℕ) : ℕ∞) ≤ ⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ) := by
  refine le_iInf fun i ↦ ?_
  rcases (Nat.succ_le_of_lt i.isLt).lt_or_eq with hilt | hieq
  · have hc1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) := by
      simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
        (n := 1)).mp (by simpa using he.mem (hdeg ▸ hilt))
    have hmul : (n : ℕ∞) ≤ n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) := by
      calc (n : ℕ∞) = n • (1 : ℕ∞) := (nsmul_one n).symm
        _ ≤ n • addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) := nsmul_le_nsmul_right hc1 n
        _ ≤ n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) := by
          rw [addVal_mul]
          exact nsmul_le_nsmul_right le_self_add n
    exact le_trans (Nat.cast_le.mpr (Nat.sub_le n 1)) (le_trans hmul le_self_add)
  · have hi : (i : ℕ) = n - 1 := by omega
    rw [hi]
    exact le_add_self

/-- **In positive degree, the discriminant boxes partition the separable Eisenstein
polynomials.** -/
theorem iUnion_eisensteinBox_eq_setOf_separable {n : ℕ} (hn : 0 < n) :
    (⋃ j : ℕ, eisensteinBox K n j) = {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨fun ⟨j, ha⟩ ↦ ⟨eisensteinBox_subset_eisensteinSet ha,
    separable_monicOfCoeff_of_mem_eisensteinBox ha⟩, fun ⟨ha, hsep⟩ ↦ ?_⟩
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hne :=
    (separable_map_iff_iInf_eisenstein_derivative_ne_top he hdeg hn).mp (hf.symm ▸ hsep)
  obtain ⟨m, hm_eq⟩ := ENat.ne_top_iff_exists.mp hne
  have hle : n - 1 ≤ m := by
    have h1 := le_iInf_eisenstein_derivative he hdeg hn
    rw [← hm_eq, Nat.cast_le] at h1
    exact h1
  refine ⟨m - (n - 1), (mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq hf he).mpr ?_⟩
  rw [← hm_eq, Nat.add_sub_of_le hle]

/-- Ideal-power box with the `0`-th coordinate restricted away from `𝓂[K] ^ 2`. -/
private def eisensteinSlice {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) : Set (Fin n → K) :=
  (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) \
    Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d ⟨0, hn⟩ 2 i)

/-- Membership in `eisensteinSlice` when `1 ≤ d i` everywhere. -/
private theorem mem_eisensteinSlice_iff {n : ℕ} (hn : 0 < n) {d : Fin n → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) {a : Fin n → K} :
    a ∈ eisensteinSlice hn d ↔
      a ∈ eisensteinSet K n ∧ ∀ i, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i) := by
  have h1 (i : Fin n) (h : a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) :
      a i ∈ ((↑) : 𝒪[K] → K) '' ↑𝓂[K] := by
    simpa only [pow_one] using Set.image_mono (Ideal.pow_le_pow_right (hd1 i)) h
  rw [eisensteinSlice, eisensteinSet_eq_sdiff hn]
  simp only [Set.mem_sdiff, Set.mem_univ_pi]
  refine ⟨fun ⟨hd, hnot⟩ ↦ ⟨⟨fun i ↦ h1 i (hd i), fun h2 ↦ hnot fun i ↦ ?_⟩, hd⟩,
    fun ⟨⟨_, hnot⟩, hd⟩ ↦ ⟨hd, fun h2 ↦ hnot fun i ↦ ?_⟩⟩
  · by_cases hi0 : i = ⟨0, hn⟩
    · subst hi0; simpa using h2 ⟨0, hn⟩
    · simpa [Function.update_of_ne hi0] using hd i
  · by_cases hi0 : i = ⟨0, hn⟩
    · subst hi0; simpa using h2 ⟨0, hn⟩
    · simpa [Function.update_of_ne hi0] using h1 i (hd i)

/-- Monotonicity of `eisensteinSlice` in opposite order of the coordinate exponents. -/
private theorem eisensteinSlice_subset {n : ℕ} (hn : 0 < n) {d d' : Fin n → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (hd'1 : ∀ i, 1 ≤ d' i) (hle : d ≤ d') :
    eisensteinSlice (K := K) hn d' ⊆ eisensteinSlice (K := K) hn d := by
  intro a ha
  rw [mem_eisensteinSlice_iff hn hd'1] at ha
  rw [mem_eisensteinSlice_iff hn hd1]
  exact ⟨ha.1, fun i ↦ Set.image_mono (Ideal.pow_le_pow_right (hle i)) (ha.2 i)⟩

/-- Coordinate depth vector for `eisensteinBox K n j`: `1` at `0` and `oreCoefficientDepth` at
positive indices. -/
private def oreBoxExponents (K : Type*) [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]
    (n j : ℕ) (i : Fin n) : ℕ :=
  if (i : ℕ) = 0 then 1 else oreCoefficientDepth K n j i

private theorem oreBoxExponents_zero {n j : ℕ} (hn : 0 < n) :
    oreBoxExponents K n j ⟨0, hn⟩ = 1 := rfl

private theorem one_le_oreBoxExponents {n j : ℕ} (i : Fin n) :
    1 ≤ oreBoxExponents K n j i := by
  by_cases h : (i : ℕ) = 0 <;> simp [oreBoxExponents, h, one_le_oreCoefficientDepth]

private theorem sum_oreBoxExponents {n j : ℕ} (hn : 0 < n) :
    ∑ i : Fin n, oreBoxExponents K n j i =
      1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
  simp only [oreBoxExponents]
  rw [Fin.sum_univ_eq_sum_range (fun h ↦ if h = 0 then 1 else oreCoefficientDepth K n j h),
    ← Nat.Ico_zero_eq_range, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hn,
    show Finset.Ico 0 1 = {0} from rfl, Finset.sum_singleton, ite_eq_left rfl]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun h hh ↦ ite_eq_right ?_)
  exact (Nat.pos_of_ne_zero (by have := (Finset.mem_Ico.mp hh).1; omega)).ne'

/-- When `j % n = 0`, an admissible discriminant box is a single `eisensteinSlice`. -/
private theorem eisensteinBox_eq_slice_of_mod_eq_zero {n j : ℕ}
    (hadm : IsOreAdmissible K n j) (hb : j % n = 0) :
    eisensteinBox K n j = eisensteinSlice hadm.pos (oreBoxExponents K n j) := by
  have hn := hadm.pos
  ext a
  rw [mem_eisensteinSlice_iff hn one_le_oreBoxExponents]
  refine ⟨fun ⟨_, ha, hdepth, _⟩ ↦ ⟨ha, fun i ↦ ?_⟩,
    fun ⟨ha, hall⟩ ↦ ⟨hadm, ha, fun h hhn hh0 ↦ ?_, fun hb' ↦ absurd hb hb'.ne'⟩⟩
  · rcases (i : ℕ).eq_zero_or_pos with hi0 | hipos
    · have hi : i = ⟨0, hn⟩ := Fin.ext hi0
      rw [hi, oreBoxExponents_zero, pow_one, ← valuation_lt_one_iff_mem_image_maximalIdeal]
      exact (mem_eisensteinSet.mp ha).1 ⟨0, hn⟩
    · simpa [oreBoxExponents, hipos.ne'] using hdepth i i.isLt hipos
  · simpa [oreBoxExponents, hh0.ne'] using hall ⟨h, hhn⟩

/-- When `0 < j % n`, an admissible discriminant box is the difference of two nested
`eisensteinSlice`s. -/
private theorem eisensteinBox_eq_sdiff_slice_of_mod_pos {n j : ℕ}
    (hadm : IsOreAdmissible K n j) (hb : 0 < j % n) :
    eisensteinBox K n j =
      eisensteinSlice hadm.pos (oreBoxExponents K n j) \
        eisensteinSlice hadm.pos
          (Function.update (oreBoxExponents K n j) ⟨j % n, Nat.mod_lt j hadm.pos⟩
            (oreCoefficientDepth K n j (j % n) + 1)) := by
  have hn := hadm.pos
  let e := oreBoxExponents K n j
  let ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
  let e' := Function.update e ib (oreCoefficientDepth K n j (j % n) + 1)
  have he'1 (i : Fin n) : 1 ≤ e' i := by
    by_cases hi : i = ib
    · subst hi; simp [e']
    · simp only [e', Function.update_of_ne hi]; exact one_le_oreBoxExponents i
  ext a
  rw [Set.mem_sdiff, mem_eisensteinSlice_iff hn one_le_oreBoxExponents,
    mem_eisensteinSlice_iff hn he'1]
  refine ⟨fun ⟨_, ha, hdepth, hmod⟩ ↦ ⟨⟨ha, fun i ↦ ?_⟩, fun ⟨_, hall'⟩ ↦ ?_⟩,
    fun ⟨⟨ha, hall⟩, hnot⟩ ↦ ⟨hadm, ha, fun h hhn hh0 ↦ ?_, fun _ hmem ↦ hnot ⟨ha, fun i ↦ ?_⟩⟩⟩
  · rcases (i : ℕ).eq_zero_or_pos with hi0 | hipos
    · have hi : i = ⟨0, hn⟩ := Fin.ext hi0
      rw [hi, oreBoxExponents_zero, pow_one, ← valuation_lt_one_iff_mem_image_maximalIdeal]
      exact (mem_eisensteinSet.mp ha).1 ⟨0, hn⟩
    · simpa [e, oreBoxExponents, hipos.ne'] using hdepth i i.isLt hipos
  · exact hmod hb (by simpa [e'] using hall' ib)
  · simpa [e, oreBoxExponents, hh0.ne'] using hall ⟨h, hhn⟩
  · by_cases hi : i = ib
    · subst hi; simpa [e'] using hmem
    · simpa [e', Function.update_of_ne hi] using hall i

end DiscreteValuation

section Topology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
  [IsDiscreteValuationRing 𝒪[K]]

/-- Every `eisensteinSlice` is measurable. -/
private theorem measurableSet_eisensteinSlice {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)] :
    MeasurableSet (eisensteinSlice (K := K) hn d) :=
  (measurableSet_univ_pi_image_maximalIdeal_pow d).diff
    (measurableSet_univ_pi_image_maximalIdeal_pow _)

/-- Every discriminant box is measurable. -/
theorem measurableSet_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  by_cases hadm : IsOreAdmissible K n j
  · rcases (j % n).eq_zero_or_pos with hb | hb
    · rw [eisensteinBox_eq_slice_of_mod_eq_zero hadm hb]
      exact measurableSet_eisensteinSlice hadm.pos _
    · rw [eisensteinBox_eq_sdiff_slice_of_mod_pos hadm hb]
      exact (measurableSet_eisensteinSlice hadm.pos _).diff
        (measurableSet_eisensteinSlice hadm.pos _)
  · rw [eisensteinBox_eq_empty_of_not_isOreAdmissible hadm]
    exact MeasurableSet.empty

end Topology

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Almost everywhere on the Eisenstein region**, `eisensteinSet K n` is covered by the union of
the discriminant boxes `eisensteinBox K n j`, including in equal characteristic. -/
theorem ae_iUnion_eisensteinBox_eq_eisensteinSet {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    (⋃ j : ℕ, eisensteinBox K n j : Set (Fin n → K)) =ᵐ[μ] eisensteinSet K n := by
  rw [iUnion_eisensteinBox_eq_setOf_separable hn]
  have hsep := ae_separable_monicOfCoeff_restrict_eisensteinSet hn μ
  rw [ae_restrict_iff' measurableSet_eisensteinSet] at hsep
  filter_upwards [hsep] with a ha
  exact ⟨And.left, fun h ↦ ⟨h, ha h⟩⟩

/-- If `a ∈ eisensteinBox K n j`, every root `x : SeparableClosure K` of `monicOfCoeff a` generates
a member of `totallyRamifiedOfDegree K n` whose wild exponent is `j`. -/
theorem adjoin_mem_totallyRamifiedOfDegree_and_wildExponent_eq_of_mem_eisensteinBox {n j : ℕ}
    {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n ∧ (K⟮x⟯).wildExponent = j := by
  have hn := ha.1.pos
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
    (eisensteinBox_subset_eisensteinSet ha)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hx' : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := hf.symm ▸ hx
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hx'
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein he hx'
  have hinf := (mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq hf he).mp ha
  rw [hdeg, hinf, Nat.cast_inj] at hd
  have hw := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  exact ⟨hmem, by omega⟩

/-- **Root-field characterization of `eisensteinBox`.** For `a ∈ eisensteinSet K n` and a root
`x : SeparableClosure K` of `monicOfCoeff a`, `(K⟮x⟯).wildExponent = j` if and only if
`a ∈ eisensteinBox K n j`. -/
theorem mem_eisensteinBox_iff_wildExponent_adjoin_eq {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    a ∈ eisensteinBox K n j ↔ (K⟮x⟯).wildExponent = j := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exfalso
    rw [eq_one_of_monic_natDegree_zero (monic_monicOfCoeff a) (natDegree_monicOfCoeff a), map_one]
      at hx
    exact one_ne_zero hx
  refine ⟨fun h ↦ (adjoin_mem_totallyRamifiedOfDegree_and_wildExponent_eq_of_mem_eisensteinBox
    h hx).2, fun hw ↦ ?_⟩
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hx' : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := hf.symm ▸ hx
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hx'
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein he hx'
  have hw' := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  have hdeq : (K⟮x⟯).discriminantExponent = n - 1 + j := by omega
  rw [hdeg, hdeq] at hd
  exact (mem_eisensteinBox_iff_iInf_eisenstein_derivative_eq hf he).mpr hd.symm

/-- Every discriminant box has finite volume for any measure that is finite on compact sets. -/
theorem measure_eisensteinBox_lt_top {n j : ℕ} [MeasurableSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [IsFiniteMeasureOnCompacts μ] : μ (eisensteinBox K n j) < ∞ :=
  (measure_mono eisensteinBox_subset_eisensteinSet).trans_lt (measure_eisensteinSet_lt_top μ)

/-- Normalized additive Haar measure of `eisensteinSlice` when `d 0 = 1`. -/
private theorem measure_eisensteinSlice {n : ℕ} (hn : 0 < n) {d : Fin n → ℕ}
    (hd0 : d ⟨0, hn⟩ = 1) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinSlice hn d) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, d i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  let d' : Fin n → ℕ := Function.update d ⟨0, hn⟩ 2
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := d) (e := d')
    (le_update_iff.2 ⟨hd0 ▸ one_le_two, fun _ _ ↦ le_rfl⟩)
  have hsum : ∑ i, d' i = (∑ i, d i) + 1 := by
    have h1 : ∑ i, d' i = 2 + ∑ x ∈ Finset.univ.erase ⟨0, hn⟩, d x := by
      simpa only [d', Finset.sdiff_singleton_eq_erase] using
        Finset.sum_update_of_mem (Finset.mem_univ (⟨0, hn⟩ : Fin n)) d 2
    have h2 := Finset.add_sum_erase Finset.univ d (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    rw [hd0] at h2
    omega
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ d
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ d'
  rw [hμ, mul_one] at h₁ h₂
  rw [hsum] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [eisensteinSlice, measure_sdiff hsub
    (measurableSet_univ_pi_image_maximalIdeal_pow d').nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

/-- **Haar measure of the discriminant box.** For an Ore-admissible pair `(n, j)` and any
left-invariant measure `μ` on `Fin n → K` normalized so that `μ (integerBox K (Fin n)) = 1`,
`μ (eisensteinBox K n j)` equals
`q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹) * (if j % n = 0 then 1 else 1 - q⁻¹)`,
where `q = Nat.card 𝓀[K]` and `ν_h = oreCoefficientDepth K n j h`. -/
theorem measure_eisensteinBox {n j : ℕ} (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
  have hn := hadm.pos
  let e := oreBoxExponents K n j
  have hesum : ∑ i, e i = 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h :=
    sum_oreBoxExponents hn
  rcases (j % n).eq_zero_or_pos with hb | hb
  · rw [eisensteinBox_eq_slice_of_mod_eq_zero hadm hb,
      measure_eisensteinSlice hn (oreBoxExponents_zero hn) μ hμ, hesum, ite_eq_left hb, mul_one]
  · let ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
    let e' := Function.update e ib (oreCoefficientDepth K n j (j % n) + 1)
    have hib0 : (⟨0, hn⟩ : Fin n) ≠ ib := Fin.ne_of_val_ne hb.ne
    have he'0 : e' ⟨0, hn⟩ = 1 := (Function.update_of_ne hib0 _ _).trans (oreBoxExponents_zero hn)
    have he'1 (i : Fin n) : 1 ≤ e' i := by
      rcases eq_or_ne i ib with rfl | hi
      · simp [e']
      · simp only [e', Function.update_of_ne hi]; exact one_le_oreBoxExponents i
    have hele : e ≤ e' :=
      le_update_iff.2 ⟨by simp [e, ib, oreBoxExponents, hb.ne'], fun _ _ ↦ le_rfl⟩
    have hsub := eisensteinSlice_subset (K := K) hn one_le_oreBoxExponents he'1 hele
    have he'sum : ∑ i, e' i = (∑ i, e i) + 1 := by
      have h1 : ∑ i, e' i =
          oreCoefficientDepth K n j (j % n) + 1 + ∑ x ∈ Finset.univ.erase ib, e x := by
        simpa only [e', Finset.sdiff_singleton_eq_erase] using
          Finset.sum_update_of_mem (Finset.mem_univ ib) e (oreCoefficientDepth K n j (j % n) + 1)
      have h2 := Finset.add_sum_erase Finset.univ e (Finset.mem_univ ib)
      have heib : e ib = oreCoefficientDepth K n j (j % n) := by
        simp [e, ib, oreBoxExponents, hb.ne']
      rw [heib] at h2
      omega
    have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
    have h₁ := measure_eisensteinSlice (d := e) hn (oreBoxExponents_zero hn) μ hμ
    have h₂ := measure_eisensteinSlice hn he'0 μ hμ
    have h₂fin : μ (eisensteinSlice (K := K) hn e') ≠ ∞ :=
      h₂ ▸ ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq))
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    rw [eisensteinBox_eq_sdiff_slice_of_mod_pos hadm hb, ite_eq_right hb.ne',
      measure_sdiff hsub (measurableSet_eisensteinSlice (K := K) hn e').nullMeasurableSet h₂fin,
      h₁, h₂, he'sum, hesum,
      ← ENNReal.sub_mul fun _ _ ↦ ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self]
    congr 1
    simp only [one_div]
    rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
      ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
        (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

end LocalField

end TauCeti

namespace IntermediateField

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `L ∈ totallyRamifiedOfDegree K n` and `a ∈ eisensteinSet K n`, the root count
`L.rootCount a` vanishes whenever `a` lies outside `eisensteinBox K n L.wildExponent`. -/
theorem rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n)
    (hnot : a ∉ eisensteinBox K n L.wildExponent) : L.rootCount a = 0 := by
  classical
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have := hL'.2.finite
  have hirr : Irreducible (monicOfCoeff a) :=
    irreducible_monicOfCoeff_of_mem_eisensteinSet (hL'.1 ▸ Module.finrank_pos) ha
  rw [L.rootCount_eq_card_filter_adjoin_eq hirr hL'.1, Multiset.card_eq_zero,
    Multiset.filter_eq_nil]
  intro x hx hLx
  exact hnot ((mem_eisensteinBox_iff_wildExponent_adjoin_eq ha (mem_aroots.mp hx).2).mpr
    (hLx ▸ rfl))

/-- **Integral of the root count over a discriminant box.** Let `L ∈ totallyRamifiedOfDegree K n`
and let `μ` be a left-invariant measure on `Fin n → K` normalized on `integerBox K (Fin n)`. Then
the integral of `L.rootCount` over `eisensteinBox K n j` equals `q ^ (-(n + j)) (1 - q⁻¹)` when
`L.wildExponent = j` and `0` otherwise. -/
theorem lintegral_rootCount_eisensteinBox {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      if L.wildExponent = j then
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
      else 0 := by
  split_ifs with hw
  · subst hw
    have hunion : eisensteinBox K n L.wildExponent ∪
        (eisensteinSet K n \ eisensteinBox K n L.wildExponent) = eisensteinSet K n :=
      Set.union_sdiff_cancel eisensteinBox_subset_eisensteinSet
    have hzero : ∫⁻ a in eisensteinSet K n \ eisensteinBox K n L.wildExponent,
        (L.rootCount a : ℝ≥0∞) ∂μ = 0 := by
      rw [setLIntegral_congr_fun (g := 0)
        (measurableSet_eisensteinSet.diff measurableSet_eisensteinBox) fun a ⟨ha, hnot⟩ ↦ by
          simp [L.rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL ha hnot]]
      simp
    have heq : ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∫⁻ a in eisensteinBox K n L.wildExponent, (L.rootCount a : ℝ≥0∞) ∂μ := by
      rw [← hunion, lintegral_union
        (measurableSet_eisensteinSet.diff measurableSet_eisensteinBox) disjoint_sdiff_self_right,
        hzero, add_zero]
    have hd : L.discriminantExponent + 1 = n + L.wildExponent := by
      have := L.wildExponent_add_eq_discriminantExponent_add_one hL
      omega
    rw [← heq, L.lintegral_rootCount hL μ hμ, hd]
  · rw [setLIntegral_congr_fun (g := 0) measurableSet_eisensteinBox fun a ha ↦ ?_]
    · simp
    · have hnot : a ∉ eisensteinBox K n L.wildExponent :=
        Set.disjoint_left.mp (disjoint_eisensteinBox (Ne.symm hw)) ha
      simp [L.rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL
        (eisensteinBox_subset_eisensteinSet ha) hnot]

end IntermediateField
