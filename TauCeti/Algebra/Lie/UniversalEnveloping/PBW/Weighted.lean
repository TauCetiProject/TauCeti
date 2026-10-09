/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.Algebra.Lie.LowerCentralSeries
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Weighted PBW truncation

Given an ordered Lie basis with natural weights, the span of its PBW monomials of weight at
least `N` is characterized by the vanishing of all coordinates below `N`. If brackets do not
lower the sum of the input weights, straightening preserves this lower bound. Consequently
these spans form a multiplicative descending filtration and are two-sided ideals.

Positive weights on a finite basis give finite-dimensional truncations. Lower-central weights
on a nilpotent Lie algebra supply the bracket condition in every characteristic. These
quotients provide finite associative targets for faithful nilpotent representations.

The construction uses `Module.Basis.pbwBasis` and
`TauCeti.exists_basis_weight_lowerCentralSeries`. Finiteness follows from
`Finsupp.finite_of_nat_weight_lt`, without assuming a field in the basis-level results.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
-/

public section

open Module

namespace Module.Basis

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι]
  (b : Basis ι R L) (w : ι → ℕ)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ιL" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)

open TauCeti.UniversalEnvelopingAlgebra

/-- The descending weighted PBW filtration: the span of monomials of weight at least `N`. -/
noncomputable def weightedPBWFiltration (N : ℕ) : Submodule R U :=
  Submodule.span R (b.pbwBasis '' {n | N ≤ Finsupp.weight w n})

/-- Membership is equivalent to vanishing of all PBW coefficients of weight below the cutoff. -/
@[simp]
theorem mem_weightedPBWFiltration_iff (N : ℕ) (a : U) :
    a ∈ b.weightedPBWFiltration w N ↔
      ∀ n, Finsupp.weight w n < N → b.pbwBasis.repr a n = 0 := by
  rw [weightedPBWFiltration, b.pbwBasis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  grind

/-- A PBW basis vector of weight at least the cutoff belongs to the weighted filtration. -/
theorem pbwBasis_mem_weightedPBWFiltration {N : ℕ} {n : ι →₀ ℕ}
    (hn : N ≤ Finsupp.weight w n) : b.pbwBasis n ∈ b.weightedPBWFiltration w N :=
  Submodule.subset_span ⟨n, hn, rfl⟩

/-- Increasing the cutoff decreases the weighted PBW filtration. -/
theorem weightedPBWFiltration_antitone : Antitone (b.weightedPBWFiltration w) := by
  intro m n hmn
  exact Submodule.span_mono (Set.image_mono fun _ hn ↦ hmn.trans hn)

/-- At cutoff zero the weighted PBW filtration is the whole enveloping algebra. -/
@[simp]
theorem weightedPBWFiltration_zero : b.weightedPBWFiltration w 0 = ⊤ := by
  simp [weightedPBWFiltration, b.pbwBasis.span_eq]

private theorem ordered_mem {N : ℕ} {l : List ι} (hl : l.Pairwise (· ≤ ·))
    (hN : N ≤ (l.map w).sum) : pbwMonomial R L b l ∈ b.weightedPBWFiltration w N := by
  classical
  have heq : b.pbwBasis (Multiset.toFinsupp (l : Multiset ι)) = pbwMonomial R L b l := by
    rw [pbwBasis_apply, Multiset.toFinsupp_toMultiset, Multiset.coe_sort,
      List.mergeSort_eq_self (· ≤ ·) hl]
  rw [← heq]
  apply b.pbwBasis_mem_weightedPBWFiltration w
  simpa using hN

attribute [local instance 100] LieRing.ofAssociativeRing

variable (hbracket : ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0)

include hbracket

private theorem swap_mem (N d : ℕ)
    (ih : ∀ l : List ι, l.length < d → N ≤ (l.map w).sum →
      pbwMonomial R L b l ∈ b.weightedPBWFiltration w N)
    (p t : List ι) (i j : ι)
    (hlen : (p ++ i :: j :: t).length ≤ d) (hw : N ≤ ((p ++ i :: j :: t).map w).sum) :
    pbwMonomial R L b (p ++ i :: j :: t) -
      pbwMonomial R L b (p ++ j :: i :: t) ∈ b.weightedPBWFiltration w N := by
  classical
  have hcomm : ιL (b i) * ιL (b j) - ιL (b j) * ιL (b i) = ιL ⁅b i, b j⁆ := by
    rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]
  have hexpand : ιL ⁅b i, b j⁆ =
      ∑ k ∈ (b.repr ⁅b i, b j⁆).support, b.repr ⁅b i, b j⁆ k • ιL (b k) := by
    conv_lhs => rw [← b.linearCombination_repr ⁅b i, b j⁆]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  have hswap : pbwMonomial R L b (p ++ i :: j :: t) -
      pbwMonomial R L b (p ++ j :: i :: t) =
      pbwMonomial R L b p * ιL ⁅b i, b j⁆ * pbwMonomial R L b t := by
    simp only [pbwMonomial_append, pbwMonomial_cons]
    rw [← hcomm]
    noncomm_ring
  rw [hswap, hexpand]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Submodule.sum_mem
  intro k hk
  have hwk : w i + w j ≤ w k := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hbracket i j k (by omega))
  simp only [mul_smul_comm, smul_mul_assoc]
  apply Submodule.smul_mem
  have hm := ih (p ++ k :: t) (by simp at hlen ⊢; omega) (by simp at hw ⊢; omega)
  simpa [pbwMonomial_append, pbwMonomial_cons, mul_assoc] using hm

private theorem perm_sub_mem (N d : ℕ)
    (ih : ∀ l : List ι, l.length < d → N ≤ (l.map w).sum →
      pbwMonomial R L b l ∈ b.weightedPBWFiltration w N)
    {l₁ l₂ : List ι} (h : l₁.Perm l₂) (p t : List ι)
    (hlen : (p ++ l₁ ++ t).length ≤ d) (hw : N ≤ ((p ++ l₁ ++ t).map w).sum) :
    pbwMonomial R L b (p ++ l₁ ++ t) - pbwMonomial R L b (p ++ l₂ ++ t) ∈
      b.weightedPBWFiltration w N := by
  induction h generalizing p with
  | nil => simp
  | cons i h ihperm =>
    simpa [List.append_assoc] using ihperm (p ++ [i])
      (by simpa [List.append_assoc] using hlen) (by simpa [List.append_assoc] using hw)
  | swap i j l =>
    simpa only [List.append_assoc, List.cons_append] using
      b.swap_mem w hbracket N d ih p (l ++ t) j i
      (by simpa [List.append_assoc] using hlen) (by simpa [List.append_assoc] using hw)
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
    have hlen₂ : (p ++ l₂ ++ t).length ≤ d := by simpa [← h₁.length_eq] using hlen
    have hw₂ : N ≤ ((p ++ l₂ ++ t).map w).sum := by
      simpa only [List.map_append, List.sum_append, (h₁.map w).sum_eq] using hw
    simpa only [sub_add_sub_cancel] using
      (b.weightedPBWFiltration w N).add_mem (ih₁ p hlen hw) (ih₂ p hlen₂ hw₂)

/-- Straightening an arbitrary basis word does not decrease its weight. -/
theorem pbwMonomial_mem_weightedPBWFiltration (l : List ι) {N : ℕ}
    (hN : N ≤ (l.map w).sum) : pbwMonomial R L b l ∈ b.weightedPBWFiltration w N := by
  -- A swap replaces two generators by a bracket, so its correction is handled
  -- by the shorter-word induction, even when its weight increases.
  have hall : ∀ d (l : List ι), l.length = d → N ≤ (l.map w).sum →
      pbwMonomial R L b l ∈ b.weightedPBWFiltration w N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro l hl hw
      have hsorted := b.ordered_mem w (List.pairwise_insertionSort (· ≤ ·) l)
        (by simpa only [((List.perm_insertionSort (· ≤ ·) l).map w).sum_eq] using hw)
      have hdiff := b.perm_sub_mem w hbracket N d
        (fun l hlt hN ↦ ih l.length hlt l rfl hN)
        (List.perm_insertionSort (· ≤ ·) l).symm [] [] (by simpa using hl.le) (by simpa using hw)
      simpa using (b.weightedPBWFiltration w N).add_mem hdiff hsorted
  exact hall l.length l rfl hN

/-- Weights add under multiplication in the descending PBW filtration. -/
theorem mul_mem_weightedPBWFiltration {m n : ℕ} {a c : U}
    (ha : a ∈ b.weightedPBWFiltration w m) (hc : c ∈ b.weightedPBWFiltration w n) :
    a * c ∈ b.weightedPBWFiltration w (m + n) := by
  classical
  rw [weightedPBWFiltration] at ha hc
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨α, hα, rfl⟩ := ha
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨β, hβ, rfl⟩ := hc
      rw [pbwBasis_apply, pbwBasis_apply, ← pbwMonomial_append]
      apply b.pbwMonomial_mem_weightedPBWFiltration w hbracket
      simp only [List.map_append, List.sum_append]
      simpa only [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq,
        ← Finsupp.weight_toFinsupp, Finsupp.toMultiset_toFinsupp] using
        Nat.add_le_add hα hβ
    | zero => simp
    | add c₁ c₂ _ _ ih₁ ih₂ =>
      simpa only [mul_add] using (b.weightedPBWFiltration w _).add_mem ih₁ ih₂
    | smul r c _ ih =>
      simpa only [mul_smul_comm] using (b.weightedPBWFiltration w _).smul_mem r ih
  | zero => simp
  | add a₁ a₂ _ _ ih₁ ih₂ =>
    simpa only [add_mul] using (b.weightedPBWFiltration w _).add_mem ih₁ ih₂
  | smul r a _ ih =>
    simpa only [smul_mul_assoc] using (b.weightedPBWFiltration w _).smul_mem r ih

/-- The weighted truncation ideal, with underlying scalar submodule the weighted PBW span. -/
noncomputable def weightedPBWIdeal
    (hbracket : ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0) (N : ℕ) : Ideal U where
  carrier := b.weightedPBWFiltration w N
  zero_mem' := (b.weightedPBWFiltration w N).zero_mem
  add_mem' := (b.weightedPBWFiltration w N).add_mem
  smul_mem' a c hc := by
    have ha : a ∈ b.weightedPBWFiltration w 0 := by simp
    simpa only [zero_add, smul_eq_mul, SetLike.mem_coe] using
      b.mul_mem_weightedPBWFiltration w hbracket ha hc

/-- Weighted truncation ideal membership is membership in the scalar PBW span. -/
@[simp]
theorem mem_weightedPBWIdeal_iff (N : ℕ) (a : U) :
    a ∈ b.weightedPBWIdeal w hbracket N ↔ a ∈ b.weightedPBWFiltration w N :=
  Iff.rfl

/-- Increasing the cutoff decreases the weighted PBW truncation ideal. -/
theorem weightedPBWIdeal_antitone : Antitone (b.weightedPBWIdeal w hbracket) := by
  intro m n hmn a ha
  rw [mem_weightedPBWIdeal_iff] at ha ⊢
  exact b.weightedPBWFiltration_antitone w hmn ha

/-- At cutoff zero the weighted PBW truncation ideal is the whole enveloping algebra. -/
@[simp]
theorem weightedPBWIdeal_zero : b.weightedPBWIdeal w hbracket 0 = ⊤ := by
  ext a
  simp

/-- The weighted PBW truncation ideal is two-sided: multiplication on the right also
preserves the lower weight bound. -/
instance weightedPBWIdeal_isTwoSided (N : ℕ) : (b.weightedPBWIdeal w hbracket N).IsTwoSided where
  mul_mem_of_left c ha := by
    rw [mem_weightedPBWIdeal_iff] at ha ⊢
    have hc : c ∈ b.weightedPBWFiltration w 0 := by simp
    simpa only [add_zero] using
      b.mul_mem_weightedPBWFiltration w hbracket ha hc

/-- The images of PBW monomials below the cutoff span the weighted quotient. -/
theorem span_image_pbwBasis_quotient_weightedPBWIdeal (N : ℕ) :
    Submodule.span R ((fun n ↦ Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N)
      (b.pbwBasis n)) '' {n | Finsupp.weight w n < N}) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  intro a ha
  clear ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction b.pbwBasis.mem_span a using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, rfl⟩ := ha
    by_cases hn : Finsupp.weight w n < N
    · exact Submodule.subset_span ⟨n, hn, rfl⟩
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        ((b.mem_weightedPBWIdeal_iff w hbracket N _).mpr
          (b.pbwBasis_mem_weightedPBWFiltration w (by omega)))]
      exact Submodule.zero_mem _
  | zero => simp
  | add a c _ _ ha hc => simpa using Submodule.add_mem _ ha hc
  | smul r a _ ha =>
    simpa only [← Ideal.Quotient.mkₐ_eq_mk R, map_smul] using Submodule.smul_mem _ r ha

/-- A finite Lie basis with positive weights gives a module-finite weighted quotient, over
any commutative coefficient ring. -/
theorem moduleFinite_quotient_weightedPBWIdeal [Finite ι] (hpos : ∀ i, 0 < w i) (N : ℕ) :
    Module.Finite R (U ⧸ b.weightedPBWIdeal w hbracket N) := by
  constructor
  rw [← b.span_image_pbwBasis_quotient_weightedPBWIdeal w hbracket N]
  exact Submodule.fg_span ((Finsupp.finite_of_nat_weight_lt w
    (fun i ↦ Nat.ne_of_gt (hpos i)) N).image _)

/-- If the cutoff exceeds every basis weight, the quotient remains injective on the
canonical copy of the Lie algebra. -/
theorem quotient_weightedPBWIdeal_ι_injective (N : ℕ) (hN : ∀ i, w i < N) :
    Function.Injective (fun x : L ↦
      Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) (ιL x)) := by
  let f := (Ideal.Quotient.mkₐ R (b.weightedPBWIdeal w hbracket N)).toLinearMap.comp
    (ιL).toLinearMap
  have hf (x : L) : f x = Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) (ιL x) := by
    simp only [f, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LieHom.coe_toLinearMap, Ideal.Quotient.mkₐ_eq_mk]
  suffices hf_inj : Function.Injective f by
    intro x y hxy
    apply hf_inj
    simpa only [hf] using hxy
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hxmem : ιL x ∈ b.weightedPBWFiltration w N :=
    (b.mem_weightedPBWIdeal_iff w hbracket N _).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [hf] using hx))
  apply b.repr.injective
  ext i
  have hcoord : (b.pbwBasis.coord (Finsupp.single i 1)).comp (ιL).toLinearMap = b.coord i := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, LieHom.coe_toLinearMap, ← pow_one (ιL (b j)),
      ← b.pbwBasis_single j 1]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  have hz := (b.mem_weightedPBWFiltration_iff w N _).mp hxmem (Finsupp.single i 1)
    (by simpa [Finsupp.weight_single] using hN i)
  simpa only [LinearMap.comp_apply, Basis.coord_apply, LieHom.coe_toLinearMap,
    LinearEquiv.map_zero, Finsupp.zero_apply] using (LinearMap.congr_fun hcoord x).symm.trans hz

omit hbracket in
/-- A canonical Lie generator has weight at least `m` when all of its nonzero basis
coordinates do. -/
theorem ι_mem_weightedPBWFiltration (x : L) {m : ℕ}
    (hx : ∀ i ∈ (b.repr x).support, m ≤ w i) : ιL x ∈ b.weightedPBWFiltration w m := by
  classical
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [← pow_one (ιL (b i)), ← b.pbwBasis_single i 1]
  apply b.pbwBasis_mem_weightedPBWFiltration w
  simpa only [Finsupp.weight_single, one_smul] using hx i hi

/-- Powers multiply the lower weight bound. -/
theorem pow_mem_weightedPBWFiltration {a : U} {m : ℕ}
    (ha : a ∈ b.weightedPBWFiltration w m) (n : ℕ) :
    a ^ n ∈ b.weightedPBWFiltration w (n * m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using
      b.mul_mem_weightedPBWFiltration w hbracket ih ha

/-- With positive weights, every Lie generator has its `N`-th power zero in the weighted
quotient at cutoff `N`. -/
theorem quotient_weightedPBWIdeal_ι_pow_eq_zero (hpos : ∀ i, 0 < w i) (N : ℕ) (x : L) :
    Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N) (ιL x) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_weightedPBWIdeal_iff]
  simpa only [mul_one] using b.pow_mem_weightedPBWFiltration w hbracket
    (b.ι_mem_weightedPBWFiltration w x (m := 1) (fun i _ ↦ hpos i)) N

end Module.Basis

namespace TauCeti.UniversalEnvelopingAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieRing.IsNilpotent L]

/-- A finite-dimensional nilpotent Lie algebra admits a weighted PBW truncation which is
finite-dimensional, preserves the canonical Lie generators injectively, and makes their powers
vanish uniformly. The weights and the cutoff are part of the conclusion. -/
theorem exists_weightedPBWIdeal_of_isNilpotent :
    ∃ (N : ℕ) (b : Basis (Fin (Module.finrank K L)) K L)
      (w : Fin (Module.finrank K L) → ℕ)
      (hbracket : ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0),
      (∀ i, 0 < w i ∧ w i < N) ∧
      Module.Finite K (_root_.UniversalEnvelopingAlgebra K L ⧸
        b.weightedPBWIdeal w hbracket N) ∧
      Function.Injective (fun x : L ↦ Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N)
        (_root_.UniversalEnvelopingAlgebra.ι K x)) ∧
      ∀ x : L, Ideal.Quotient.mk (b.weightedPBWIdeal w hbracket N)
        (_root_.UniversalEnvelopingAlgebra.ι K x) ^ N = 0 := by
  obtain ⟨N, b, w, hweight, _, hbracket⟩ := exists_basis_weight_lowerCentralSeries (K := K) (L := L)
  have hpos := fun i ↦ (hweight i).1
  have hN : ∀ i, w i < N + 1 := fun i ↦ Nat.lt_succ_of_le (hweight i).2
  exact ⟨N + 1, b, w, hbracket, fun i ↦ ⟨hpos i, hN i⟩,
    b.moduleFinite_quotient_weightedPBWIdeal w hbracket hpos _,
    b.quotient_weightedPBWIdeal_ι_injective w hbracket _ hN,
    b.quotient_weightedPBWIdeal_ι_pow_eq_zero w hbracket hpos _⟩

end TauCeti.UniversalEnvelopingAlgebra
