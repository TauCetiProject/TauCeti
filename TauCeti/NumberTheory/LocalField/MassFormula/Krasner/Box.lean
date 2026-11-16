/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Ore
public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The discriminant box in Eisenstein coefficient space

For a nonarchimedean local field `K`, degree `n`, and wild exponent `j`, the discriminant box
`TauCeti.eisensteinBox K n j` in coefficient space `Fin n → K` collects the Eisenstein coefficient
vectors whose associated monic polynomials have roots generating totally ramified extensions of
wild exponent `j`.

By `TauCeti.wildExponent_adjoin_eq_iff_of_eisenstein`, an Eisenstein polynomial `monicOfCoeff a`
of degree `n` has roots generating extensions of wild exponent `j` precisely when
`IsOreAdmissible K n j`, every intermediate coefficient `a i` (`0 < i < n`) lies in
`𝓂[K] ^ ν_i` where `ν_i = oreCoefficientDepth K n j i`, and when `0 < j % n` the coefficient at
index `b = j % n` has exact valuation `ν_b` (equivalently `a b ∉ 𝓂[K] ^ (ν_b + 1)`). When
`¬ IsOreAdmissible K n j`, the box is empty.

Every polynomial in `eisensteinBox K n j` is separable (including in equal characteristic, since
the leading term `n` when `j % n = 0` or the `b`-th derivative term `b * a b` when `0 < j % n` is
nonzero). The boxes for distinct `j` are pairwise disjoint, and for `0 < n` their union is the
set of separable Eisenstein polynomials, which agrees almost everywhere with `eisensteinSet K n`.
Each box is an explicit difference of coordinate ideal-power boxes, so it is measurable and its
Haar measure normalized on `integerBox K (Fin n)` is
`q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹) * (if j % n = 0 then 1 else 1 - q⁻¹)`.

## Main definitions

* `TauCeti.eisensteinBox K n j`: the discriminant box in `Fin n → K` for degree `n` and wild
  exponent `j`.

## Main results

* `TauCeti.eisensteinBox_subset_eisensteinSet`: every discriminant box lies in `eisensteinSet K n`.
* `TauCeti.separable_monicOfCoeff_of_mem_eisensteinBox`: every coefficient vector in a
  discriminant box defines a separable polynomial.
* `TauCeti.mem_eisensteinBox_iff_wildExponent_eq`: for a root `x` of an Eisenstein polynomial
  `monicOfCoeff a`, `a ∈ eisensteinBox K n j ↔ (K⟮x⟯).wildExponent = j`.
* `TauCeti.pairwiseDisjoint_eisensteinBox` and `TauCeti.iUnion_eisensteinBox_eq`: the discriminant
  boxes partition the separable Eisenstein polynomials.
* `TauCeti.rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne` and
  `TauCeti.rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox`: the root count of
  `L ∈ σ_K(n)` on `eisensteinSet K n` is supported on `eisensteinBox K n L.wildExponent`.
* `TauCeti.measurableSet_eisensteinBox` and `TauCeti.measure_eisensteinBox`: measurability and
  exact Haar volume of the discriminant box.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les Tendances
  Géom. en Algèbre et Théorie des Nombres*, Éditions du C.N.R.S., Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, §6.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory TauCeti.Polynomial Function
open scoped IntermediateField ENNReal

namespace TauCeti

section CoefficientSpace

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- The discriminant box in coefficient space `Fin n → K` for degree `n` and wild exponent `j`.
It is empty unless `IsOreAdmissible K n j`; otherwise it consists of the Eisenstein coefficient
vectors `a` with `a i ∈ 𝓂[K] ^ ν_i` for `0 < i < n` (where `ν_i = oreCoefficientDepth K n j i`),
and with `a (j % n) ∉ 𝓂[K] ^ (ν_(j % n) + 1)` when `0 < j % n`. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | IsOreAdmissible K n j ∧ a ∈ eisensteinSet K n ∧
    (∀ i : Fin n, 0 < (i : ℕ) →
      a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ∧
    (0 < j % n → ∀ hn : 0 < n,
      a ⟨j % n, Nat.mod_lt j hn⟩ ∉
        ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1)))}

/-- Membership in `eisensteinBox`, unfolded. -/
theorem mem_eisensteinBox_iff {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔
      IsOreAdmissible K n j ∧ a ∈ eisensteinSet K n ∧
        (∀ i : Fin n, 0 < (i : ℕ) →
          a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ∧
        (0 < j % n → ∀ hn : 0 < n,
          a ⟨j % n, Nat.mod_lt j hn⟩ ∉
            ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1))) :=
  Iff.rfl

/-- An inadmissible wild exponent has an empty discriminant box. -/
theorem eisensteinBox_eq_empty_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ha ↦ h ha.1

/-- In degree zero, every discriminant box is empty. -/
@[simp]
theorem eisensteinBox_zero (j : ℕ) : eisensteinBox K 0 j = ∅ :=
  eisensteinBox_eq_empty_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

/-- Every discriminant box lies inside the Eisenstein region. -/
theorem eisensteinBox_subset_eisensteinSet (n j : ℕ) :
    eisensteinBox K n j ⊆ eisensteinSet K n :=
  fun _ ha ↦ ha.2.1

/-- Every coefficient vector in a discriminant box defines a separable polynomial over `K`,
including in equal characteristic. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  have hO := ha.1
  have hn := hO.pos
  have hirr := irreducible_monicOfCoeff_of_mem_eisensteinSet hn ha.2.1
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hder
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · have hvn := (isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO
    have hnK : (n : K) ≠ 0 := by
      intro h0
      have hn𝒪 : (n : 𝒪[K]) = 0 := Subtype.ext (by simpa using h0)
      rw [hn𝒪, addVal_zero] at hvn
      exact ENat.natCast_ne_top _ hvn
    have hc := congrArg (fun p : K[X] ↦ p.coeff (n - 1)) hder
    rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel hn, coeff_monicOfCoeff_self, one_mul,
      Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] at hc
    exact hnK hc
  · have hvb := ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).1
    have hbK : ((j % n : ℕ) : K) ≠ 0 := by
      intro h0
      have hb𝒪 : ((j % n : ℕ) : 𝒪[K]) = 0 := Subtype.ext (by simpa using h0)
      rw [hb𝒪, addVal_zero] at hvb
      exact absurd hvb (by simp)
    have hmod : j % n < n := Nat.mod_lt j hn
    have hab : a ⟨j % n, hmod⟩ ≠ 0 := by
      intro h0
      exact ha.2.2.2 hb hn ⟨0, Ideal.zero_mem _, by simpa using h0.symm⟩
    have hc := congrArg (fun p : K[X] ↦ p.coeff (j % n - 1)) hder
    rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel hb, coeff_monicOfCoeff a ⟨j % n, hmod⟩,
      Nat.cast_sub hb, Nat.cast_one, sub_add_cancel] at hc
    exact mul_ne_zero hab hbK hc

/-- The box of ideal powers with coordinate exponent vector `e`, minus its sub-box where coordinate
`0` lies in `𝓂[K] ^ 2`, equals the vectors in the box with `a 0 ∉ 𝓂[K] ^ 2`. -/
private theorem mem_box_sdiff_zero_iff {n : ℕ} (hn : 0 < n) (e : Fin n → ℕ) (a : Fin n → K) :
    a ∈ (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e ⟨0, hn⟩ 2 i)) ↔
      (∀ i : Fin n, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) ∧
        a ⟨0, hn⟩ ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 2) := by
  set i₀ : Fin n := ⟨0, hn⟩
  simp only [Set.mem_sdiff, Set.mem_univ_pi]
  refine and_congr_right fun ha ↦ not_congr ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · simpa [Function.update_self] using h i₀
  · rcases eq_or_ne i i₀ with rfl | hi
    · simpa [Function.update_self] using h
    · simpa [Function.update_of_ne hi] using ha i

/-- When `IsOreAdmissible K n j` and `j % n = 0`, the discriminant box is a single difference of
ideal-power boxes. -/
theorem eisensteinBox_eq_sdiff_of_mod_eq_zero {n j : ℕ} (hO : IsOreAdmissible K n j)
    (hb : j % n = 0) :
    let e : Fin n → ℕ := fun i ↦ if (i : ℕ) = 0 then 1 else oreCoefficientDepth K n j i
    eisensteinBox K n j =
      (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e ⟨0, hO.pos⟩ 2 i)) := by
  intro e
  have hn := hO.pos
  set i₀ : Fin n := ⟨0, hn⟩
  have he0 : e i₀ = 1 := ite_eq_left rfl
  have he1 (i : Fin n) : 1 ≤ e i := by
    dsimp only [e]
    split_ifs
    · exact le_rfl
    · exact one_le_oreCoefficientDepth ..
  ext a
  rw [mem_box_sdiff_zero_iff hn e, mem_eisensteinBox_iff, eisensteinSet_eq_sdiff hn]
  have h1sdiff := mem_box_sdiff_zero_iff (K := K) hn (fun _ ↦ 1) a
  simp only [pow_one] at h1sdiff
  rw [h1sdiff]
  constructor
  · rintro ⟨-, ⟨⟨ha1, ha0⟩, hadepth, -⟩⟩
    refine ⟨fun i ↦ ?_, ha0⟩
    by_cases hi : (i : ℕ) = 0
    · have hieq : i = i₀ := Fin.ext hi
      subst hieq
      simpa [he0] using ha1 i₀
    · simpa [e, hi] using hadepth i (Nat.pos_of_ne_zero hi)
  · rintro ⟨ha, ha0⟩
    refine ⟨hO, ⟨fun i ↦ ?_, ha0⟩, fun i hi ↦ ?_, fun h0 _ ↦ absurd hb h0.ne'⟩
    · simpa only [pow_one] using Set.image_mono (Ideal.pow_le_pow_right (he1 i)) (ha i)
    · simpa [e, hi.ne'] using ha i

/-- When `IsOreAdmissible K n j` and `0 < j % n`, the discriminant box is the difference of two
sets of the form `box e \ box (update e 0 2)`, where the second exponent vector raises coordinate
`j % n` by `1`. -/
theorem eisensteinBox_eq_sdiff_of_mod_pos {n j : ℕ} (hO : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    let e : Fin n → ℕ := fun i ↦ if (i : ℕ) = 0 then 1 else oreCoefficientDepth K n j i
    let ib : Fin n := ⟨j % n, Nat.mod_lt j hO.pos⟩
    let e' : Fin n → ℕ := Function.update e ib (e ib + 1)
    eisensteinBox K n j =
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
          (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e ⟨0, hO.pos⟩ 2 i))) \
        ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e' i)) \
          (Set.univ.pi fun i ↦
            ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e' ⟨0, hO.pos⟩ 2 i))) := by
  intro e ib e'
  have hn := hO.pos
  set i₀ : Fin n := ⟨0, hn⟩
  have he0 : e i₀ = 1 := ite_eq_left rfl
  have heb : e ib = oreCoefficientDepth K n j (j % n) := by
    simp [e, ib, hb.ne']
  have he1 (i : Fin n) : 1 ≤ e i := by
    dsimp only [e]
    split_ifs
    · exact le_rfl
    · exact one_le_oreCoefficientDepth ..
  ext a
  rw [Set.mem_sdiff, mem_box_sdiff_zero_iff hn e, mem_box_sdiff_zero_iff hn e',
    mem_eisensteinBox_iff, eisensteinSet_eq_sdiff hn]
  have h1sdiff := mem_box_sdiff_zero_iff (K := K) hn (fun _ ↦ 1) a
  simp only [pow_one] at h1sdiff
  rw [h1sdiff]
  constructor
  · rintro ⟨-, ⟨⟨ha1, ha0⟩, hadepth, hab⟩⟩
    have hae : ∀ i : Fin n, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i) := fun i ↦ by
      by_cases hi : (i : ℕ) = 0
      · have hieq : i = i₀ := Fin.ext hi
        subst hieq
        simpa [he0] using ha1 i₀
      · simpa [e, hi] using hadepth i (Nat.pos_of_ne_zero hi)
    refine ⟨⟨hae, ha0⟩, fun ⟨hae', _⟩ ↦ hab hb hn ?_⟩
    have hmem := hae' ib
    simpa [e', Function.update_self, heb] using hmem
  · rintro ⟨⟨hae, ha0⟩, hnot⟩
    refine ⟨hO, ⟨fun i ↦ ?_, ha0⟩, fun i hi ↦ ?_, fun _ _ hab ↦ hnot ⟨fun i ↦ ?_, ha0⟩⟩
    · simpa only [pow_one] using Set.image_mono (Ideal.pow_le_pow_right (he1 i)) (hae i)
    · simpa [e, hi.ne'] using hae i
    · rcases eq_or_ne i ib with rfl | hi
      · simpa [e', Function.update_self, heb] using hab
      · simpa [e', Function.update_of_ne hi] using hae i

end CoefficientSpace

section WildExponent

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Membership of an Eisenstein coefficient vector in `eisensteinBox K n j` is equivalent to the
wild exponent of the field generated by any root of `monicOfCoeff a` being equal to `j`. -/
theorem mem_eisensteinBox_iff_wildExponent_eq {n j : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (he : f.IsEisensteinAt 𝓂[K]) (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a)
    {x : SeparableClosure K} (hx : aeval x (monicOfCoeff a) = 0) :
    a ∈ eisensteinBox K n j ↔ (K⟮x⟯).wildExponent = j := by
  have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hcoeff (i : Fin n) : ((f.coeff (i : ℕ) : 𝒪[K]) : K) = a i := by
    have := congrArg (fun p : K[X] ↦ p.coeff (i : ℕ)) hf
    simpa only [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_monicOfCoeff] using this
  have hmem_pow (i : Fin n) (k : ℕ) :
      a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ k) ↔ (k : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (i : ℕ)) := by
    rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, ← hcoeff i]
    exact ⟨fun ⟨c, hc, hce⟩ ↦ (Subtype.ext hce) ▸ hc, fun h ↦ ⟨f.coeff i, h, rfl⟩⟩
  have haE : a ∈ eisensteinSet K n :=
    mem_eisensteinSet_iff_exists_isEisensteinAt.2 ⟨f, hf, he⟩
  rw [wildExponent_adjoin_eq_iff_of_eisenstein hmonic he hdeg (hf ▸ hx), mem_eisensteinBox_iff]
  refine and_congr_right fun hO ↦ ?_
  rw [and_iff_right haE]
  have hdepth_iff :
      (∀ i : Fin n, 0 < (i : ℕ) →
          a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ↔
        ∀ i : Fin n, 0 < (i : ℕ) →
          (oreCoefficientDepth K n j i : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i) :=
    forall_congr' fun i ↦ imp_congr_right fun _ ↦ hmem_pow i _
  rw [hdepth_iff]
  refine and_congr_right fun hdepth ↦ ⟨fun hnot hb ↦ ?_, fun heq hb hn hmem ↦ ?_⟩
  · have hn := hO.pos
    have hmod : j % n < n := Nat.mod_lt j hn
    have hle := hdepth ⟨j % n, hmod⟩ hb
    have hlt : addVal 𝒪[K] (f.coeff (j % n)) <
        ((oreCoefficientDepth K n j (j % n) + 1 : ℕ) : ℕ∞) :=
      lt_of_not_ge fun h ↦ hnot hb hn ((hmem_pow ⟨j % n, hmod⟩ _).2 h)
    cases hv : addVal 𝒪[K] (f.coeff (j % n)) with
    | top =>
      rw [hv] at hlt
      exact absurd hlt (by simp)
    | coe m =>
      dsimp only at hle
      rw [hv, Nat.cast_le] at hle
      rw [hv, Nat.cast_lt] at hlt
      exact_mod_cast (by omega : m = oreCoefficientDepth K n j (j % n))
  · have hge := (hmem_pow ⟨j % n, Nat.mod_lt j hn⟩ _).1 hmem
    rw [heq hb, Nat.cast_le] at hge
    omega

/-- Any root of a polynomial in `eisensteinBox K n j` generates an extension of wild exponent
`j`. -/
theorem wildExponent_adjoin_eq_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) : (K⟮x⟯).wildExponent = j := by
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 ha.2.1
  exact (mem_eisensteinBox_iff_wildExponent_eq he hf hx).1 ha

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A separable monic polynomial of positive degree over `K` has a root in `SeparableClosure K`. -/
private theorem exists_root_monicOfCoeff_of_separable {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (hsep : (monicOfCoeff a).Separable) :
    ∃ x : SeparableClosure K, aeval x (monicOfCoeff a) = 0 := by
  have hcard : ((monicOfCoeff a).aroots (SeparableClosure K)).card = n := by
    rw [aroots_def, ← (IsSepClosed.splits_codomain _ hsep).natDegree_eq_card_roots,
      natDegree_map, natDegree_monicOfCoeff]
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard.symm ▸ hn)
  exact ⟨x, (mem_aroots.1 hx).2⟩

/-- The discriminant boxes for distinct wild exponents are pairwise disjoint. -/
theorem pairwiseDisjoint_eisensteinBox (n : ℕ) :
    Pairwise (Disjoint on fun j ↦ eisensteinBox K n j) := by
  intro j₁ j₂ hne
  refine Set.disjoint_left.2 fun a ha₁ ha₂ ↦ hne ?_
  obtain ⟨x, hx⟩ := exists_root_monicOfCoeff_of_separable ha₁.1.pos
    (separable_monicOfCoeff_of_mem_eisensteinBox ha₁)
  exact (wildExponent_adjoin_eq_of_mem_eisensteinBox ha₁ hx).symm.trans
    (wildExponent_adjoin_eq_of_mem_eisensteinBox ha₂ hx)

/-- For `0 < n`, the discriminant boxes partition the separable Eisenstein polynomials. -/
theorem iUnion_eisensteinBox_eq {n : ℕ} (hn : 0 < n) :
    (⋃ j : ℕ, eisensteinBox K n j) =
      {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, ha⟩
    exact ⟨ha.2.1, separable_monicOfCoeff_of_mem_eisensteinBox ha⟩
  · rintro ⟨ha, hsep⟩
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 ha
    obtain ⟨x, hx⟩ := exists_root_monicOfCoeff_of_separable hn hsep
    exact ⟨(K⟮x⟯).wildExponent, (mem_eisensteinBox_iff_wildExponent_eq he hf hx).2 rfl⟩

/-- At every point of a discriminant box, the root counts over `σ_K(n)` sum to `n`. -/
theorem tsum_rootCount_eq_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) :
    ∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞) = n := by
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 ha.2.1
  exact tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha)

/-- For `L ∈ σ_K(n)` and an Eisenstein coefficient vector outside
`eisensteinBox K n L.wildExponent`, `monicOfCoeff a` has no roots in `L`. -/
theorem rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n)
    (hnot : a ∉ eisensteinBox K n L.wildExponent) : L.rootCount a = 0 := by
  classical
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  have := hL'.2.finite
  have hn : 0 < n := hL'.1 ▸ Module.finrank_pos
  have hirr : Irreducible (monicOfCoeff a) :=
    irreducible_monicOfCoeff_of_mem_eisensteinSet hn ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 ha
  rw [L.rootCount_eq_card_filter_adjoin_eq hirr hL'.1, Multiset.card_eq_zero,
    Multiset.filter_eq_nil]
  intro x hx hEq
  exact hnot ((mem_eisensteinBox_iff_wildExponent_eq he hf (mem_aroots.1 hx).2).2
    (congrArg IntermediateField.wildExponent hEq))

/-- For `L ∈ σ_K(n)` and `a ∈ eisensteinBox K n j` with `L.wildExponent ≠ j`, `L.rootCount a` is
zero. -/
theorem rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) (hne : L.wildExponent ≠ j) :
    L.rootCount a = 0 :=
  rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL ha.2.1
    fun hmem ↦ Set.disjoint_left.1 (pairwiseDisjoint_eisensteinBox n hne) hmem ha

end WildExponent

section Measure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every discriminant box is measurable. -/
theorem measurableSet_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  by_cases hO : IsOreAdmissible K n j
  · rcases Nat.eq_zero_or_pos (j % n) with hb | hb
    · rw [eisensteinBox_eq_sdiff_of_mod_eq_zero hO hb]
      exact (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    · rw [eisensteinBox_eq_sdiff_of_mod_pos hO hb]
      exact ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
          (measurableSet_univ_pi_image_maximalIdeal_pow _)).diff
        ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
          (measurableSet_univ_pi_image_maximalIdeal_pow _))
  · rw [eisensteinBox_eq_empty_of_not_isOreAdmissible hO]
    exact MeasurableSet.empty

/-- For `L ∈ σ_K(n)`, the root count `a ↦ L.rootCount a` is almost everywhere measurable on every
discriminant box. -/
theorem aemeasurable_rootCount_restrict_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] (μ : Measure (Fin n → K))
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    AEMeasurable (fun a ↦ (L.rootCount a : ℝ≥0∞)) (μ.restrict (eisensteinBox K n j)) :=
  (aemeasurable_rootCount_restrict_eisensteinSet μ hL).mono_measure
    (Measure.restrict_mono (eisensteinBox_subset_eisensteinSet n j) le_rfl)

/-- For positive degree and any additive Haar measure, almost every point of `eisensteinSet K n`
lies in some discriminant box. -/
theorem ae_mem_iUnion_eisensteinBox {n : ℕ} (hn : 0 < n) [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    ∀ᵐ a ∂μ.restrict (eisensteinSet K n), a ∈ ⋃ j : ℕ, eisensteinBox K n j := by
  rw [iUnion_eisensteinBox_eq hn]
  filter_upwards [ae_restrict_mem measurableSet_eisensteinSet,
    ae_separable_monicOfCoeff_restrict_eisensteinSet hn μ] with a ha hsep
  exact ⟨ha, hsep⟩

/-- Measure of an ideal-power box `box e` minus `box (update e 0 2)`, when `e 0 = 1`. -/
private theorem measure_box_sdiff_zero {n : ℕ} (hn : 0 < n) (e : Fin n → ℕ)
    (he0 : e ⟨0, hn⟩ = 1) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    μ ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e ⟨0, hn⟩ 2 i))) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, e i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set e₂ : Fin n → ℕ := Function.update e i₀ 2
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := e) (e := e₂)
    (le_update_iff.2 ⟨by omega, fun _ _ ↦ le_rfl⟩)
  have hsum : ∑ i, e₂ i = (∑ i, e i) + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sdiff_singleton_eq_erase]
    have hsplit := Finset.add_sum_erase Finset.univ e (Finset.mem_univ i₀)
    omega
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e₂
  rw [hμ, mul_one] at h₁ h₂
  rw [hsum] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [measure_sdiff hsub (measurableSet_univ_pi_image_maximalIdeal_pow e₂).nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

/-- Measure of the double difference `(∏ 𝓂 ^ e i \ ∏ 𝓂 ^ (update e 0 2) i) \
(∏ 𝓂 ^ (update e ib (e ib + 1)) i \ ∏ 𝓂 ^ (update (update e ib (e ib + 1)) 0 2) i)`
when `e 0 = 1` and `ib ≠ 0`. -/
private theorem measure_box_sdiff_two {n : ℕ} (hn : 0 < n) (e : Fin n → ℕ)
    (he0 : e ⟨0, hn⟩ = 1) {ib : Fin n} (hbi0 : ib ≠ ⟨0, hn⟩)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    let i₀ : Fin n := ⟨0, hn⟩
    let e' : Fin n → ℕ := Function.update e ib (e ib + 1)
    μ (((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
          (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e i₀ 2 i))) \
        ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e' i)) \
          (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e' i₀ 2 i)))) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, e i) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  dsimp only
  set i₀ : Fin n := ⟨0, hn⟩
  set e' : Fin n → ℕ := Function.update e ib (e ib + 1)
  have he'0 : e' i₀ = 1 := by
    rw [show e' i₀ = e i₀ from Function.update_of_ne hbi0.symm .., he0]
  have hle : e ≤ e' := le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩
  have hsub :
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e' i)) \
          (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e' i₀ 2 i))) ⊆
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
          (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e i₀ 2 i))) := by
    intro a ha
    rw [mem_box_sdiff_zero_iff hn e]
    rw [mem_box_sdiff_zero_iff hn e'] at ha
    exact ⟨fun i ↦ Set.image_mono (Ideal.pow_le_pow_right (hle i)) (ha.1 i), ha.2⟩
  have hmeas' : MeasurableSet
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e' i)) \
        (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e' i₀ 2 i))) :=
    (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
      (measurableSet_univ_pi_image_maximalIdeal_pow _)
  have hsum_e' : ∑ i, e' i = (∑ i, e i) + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sdiff_singleton_eq_erase]
    have hsplit := Finset.add_sum_erase Finset.univ e (Finset.mem_univ ib)
    omega
  have hS := measure_box_sdiff_zero hn e he0 μ hμ
  have hS' := measure_box_sdiff_zero hn e' he'0 μ hμ
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hfin (m : ℕ) :
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ m * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq))
      (ENNReal.sub_ne_top ENNReal.one_ne_top)
  rw [measure_sdiff hsub hmeas'.nullMeasurableSet (hS' ▸ hfin _), hS, hS', hsum_e']
  set A : ℝ≥0∞ := 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, e i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
  have hstep :
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ((∑ i, e i) + 1) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
        A * (1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
    dsimp only [A]
    simp only [one_div]
    rw [pow_succ, ENNReal.mul_inv (.inl (pow_ne_zero _ hq)) (.inl (ENNReal.pow_ne_top hqt))]
    ring
  rw [hstep, ENNReal.mul_sub fun _ _ ↦ hfin _, mul_one]

/-- **Volume of the discriminant box**: for an Ore-admissible wild exponent `j` and a left-invariant
measure normalized on the integer box, `eisensteinBox K n j` has volume
`q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹) * (if j % n = 0 then 1 else 1 - q⁻¹)`. -/
theorem measure_eisensteinBox {n j : ℕ} (hO : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hn := hO.pos
  set i₀ : Fin n := ⟨0, hn⟩
  let e : Fin n → ℕ := fun i ↦ if (i : ℕ) = 0 then 1 else oreCoefficientDepth K n j i
  have he0 : e i₀ = 1 := ite_eq_left rfl
  have hsum_e : ∑ i : Fin n, e i = 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ if k = 0 then 1 else oreCoefficientDepth K n j k)]
    have hrange : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hrange, Finset.sum_insert (by simp), ite_eq_left rfl]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    exact ite_eq_right (by have := (Finset.mem_Ico.1 hk).1; omega)
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · rw [eisensteinBox_eq_sdiff_of_mod_eq_zero hO hb, measure_box_sdiff_zero hn e he0 μ hμ,
      hsum_e, ite_eq_left hb, mul_one]
  · have hbi0 : (⟨j % n, Nat.mod_lt j hn⟩ : Fin n) ≠ i₀ := fun h ↦ hb.ne' (congrArg Fin.val h)
    rw [eisensteinBox_eq_sdiff_of_mod_pos hO hb, ite_eq_right hb.ne',
      measure_box_sdiff_two hn e he0 hbi0 μ hμ, hsum_e]

end Measure

end TauCeti
