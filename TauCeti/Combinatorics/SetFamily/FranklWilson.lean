/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The Frankl–Wilson and Alon–Babai–Suzuki inequalities

This file develops the multilinear-polynomial method for finite set systems and proves the main
intersection bounds of Frankl and Wilson, Alon, Babai, and Suzuki, and Ray-Chaudhuri and Wilson.

Over a commutative ring `R`, a function `Finset α → R` is multilinear of degree at most `d` if it
lies in the span of the subset-inclusion indicators `B ↦ if I ⊆ B then 1 else 0` for `#I ≤ d`.
There are `∑ i ≤ d, C(n, i)` such monomials on an `n`-element ground set, and for any `A`, the
map `B ↦ #(A ∩ B)` is multilinear of degree at most `1`, so polynomial combinations in `#(A ∩ B)` of
degree at most `s` live in a submodule of rank at most `∑ i ≤ s, C(n, i)`.

## Main results

* `Finset.card_le_sum_choose_of_isIntersectingOf`: the nonuniform Frankl–Wilson inequality, bounding
  an `L`-intersecting family with `#L = s` by `∑ i ≤ s, C(n, i)`.
* `Finset.card_le_sum_choose_of_card_mem`: the Alon–Babai–Suzuki inequality for families whose
  member sizes lie in `K` (with `k > #L - #K` for all `k ∈ K`) and whose pairwise intersections lie
  in `L`.
* `Finset.card_le_choose_of_card_eq`: the Ray-Chaudhuri–Wilson inequality for uniform families of
  `k`-element sets with `#L ≤ k`.
* `Finset.card_le_sum_choose_of_natCast_card_notMem`: the Frankl–Wilson inequality over an
  arbitrary integral domain `R` (in particular `ZMod p` for a prime `p`), when member sizes avoid
  `L ⊆ R` and distinct pairwise intersections lie in `L`.
* `Finset.card_le_sum_choose_of_inter_ne`: the forbidden-intersection bound for `(2p - 1)`-element
  subsets avoiding intersection size `p - 1`, for a prime `p`.

## References

* N. Alon, L. Babai, and H. Suzuki, *Multilinear polynomials and Frankl–Ray-Chaudhuri–Wilson type
  intersection theorems*, J. Combin. Theory Ser. A 58 (1991), 165–180 (Theorems 1.1, 1.3, 1.4, 3.1).
* P. Frankl and R. M. Wilson, *Intersection theorems with geometric consequences*, Combinatorica 1
  (1981), 357–368.
* D. K. Ray-Chaudhuri and R. M. Wilson, *On t-designs*, Osaka J. Math. 12 (1975), 737–744.
* J. Matoušek, *Thirty-three Miniatures: Mathematical and Algorithmic Applications of Linear
  Algebra*, AMS, 2010 (Miniature 17).
-/

public section

namespace Finset

section

variable {α : Type*} [DecidableEq α]

private def multilinearMonomial (R : Type*) [Semiring R] (I : Finset α) : Finset α → R :=
  fun B ↦ if I ⊆ B then 1 else 0

private lemma multilinearMonomial_mul (R : Type*) [Semiring R] (I J : Finset α) :
    multilinearMonomial R I * multilinearMonomial R J = multilinearMonomial R (I ∪ J) := by
  ext B
  simp only [Pi.mul_apply, multilinearMonomial, union_subset_iff]
  split_ifs <;> simp_all

private def fwPoly (L : Finset ℕ) (A : Finset α) : Finset α → ℤ :=
  fun B ↦ ∏ l ∈ L.filter (· < #A), ((#(A ∩ B) : ℤ) - l)

private lemma fwPoly_self_ne_zero (L : Finset ℕ) (A : Finset α) : fwPoly L A A ≠ 0 := by
  rw [fwPoly, prod_ne_zero_iff]
  intro l hl
  have hl' : l < #A := (mem_filter.mp hl).2
  rw [inter_self, sub_ne_zero]
  exact_mod_cast hl'.ne'

private lemma fwPoly_eq_zero_of_card_le {F : Finset (Finset α)} {L : Finset ℕ}
    (h : Set.IsIntersectingOf (L : Set ℕ) (F : Set (Finset α))) {A B : Finset α} (hA : A ∈ F)
    (hB : B ∈ F) (hAB : A ≠ B) (hcard : #B ≤ #A) : fwPoly L A B = 0 := by
  have hinter : #(A ∩ B) ∈ L := h hA hB hAB
  have hlt : #(A ∩ B) < #A := by
    by_contra! hle
    have heq : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left hle
    have hsub : A ⊆ B := heq ▸ inter_subset_right
    exact hAB (eq_of_subset_of_card_le hsub hcard)
  exact prod_eq_zero (mem_filter.mpr ⟨hinter, hlt⟩) (sub_self _)

private lemma fwPoly_coeff_eq_zero {F : Finset (Finset α)} {L : Finset ℕ}
    (h : Set.IsIntersectingOf (L : Set ℕ) (F : Set (Finset α))) {c : F → ℤ}
    (hc : ∀ B : F, ∑ A : F, c A * fwPoly L A.val B.val = 0) : ∀ A : F, c A = 0 := by
  by_contra! hne
  let t : Finset F := univ.filter (fun A : F ↦ c A ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨A, hA⟩ := hne
    exact ⟨A, mem_filter.mpr ⟨mem_univ A, hA⟩⟩
  obtain ⟨B, hBt, hBmin⟩ := mem_image.mp (min'_mem (t.image fun A : F ↦ #A.val) (ht.image _))
  have hBne : c B ≠ 0 := (mem_filter.mp hBt).2
  have hsum : ∑ A : F, c A * fwPoly L A.val B.val = c B * fwPoly L B.val B.val := by
    refine sum_eq_single B (fun A _ hAB ↦ ?_) (fun hB ↦ absurd (mem_univ B) hB)
    by_cases hAc : c A = 0
    · simp [hAc]
    · have hAt : A ∈ t := mem_filter.mpr ⟨mem_univ A, hAc⟩
      have hcard : #B.val ≤ #A.val := hBmin ▸ min'_le _ _ (mem_image_of_mem _ hAt)
      rw [fwPoly_eq_zero_of_card_le h A.property B.property (Subtype.coe_ne_coe.mpr hAB) hcard,
        mul_zero]
  have hzero : c B * fwPoly L B.val B.val = 0 := hsum ▸ hc B
  exact absurd (mul_eq_zero.mp hzero) (by simp [hBne, fwPoly_self_ne_zero L B.val])

private lemma multilinearMonomial_mul_coeff_eq_zero {J : Finset (Finset α)} {g : Finset α → ℤ}
    (hg : ∀ I ∈ J, g I ≠ 0) {d : J → ℤ}
    (hd : ∀ I₀ : J, ∑ I : J, d I * (multilinearMonomial ℤ I.val * g) I₀.val = 0) :
    ∀ I : J, d I = 0 := by
  by_contra! hne
  let t : Finset J := univ.filter (fun I : J ↦ d I ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨I, hI⟩ := hne
    exact ⟨I, mem_filter.mpr ⟨mem_univ I, hI⟩⟩
  obtain ⟨I₀, hI₀t, hI₀min⟩ := mem_image.mp (min'_mem (t.image fun I : J ↦ #I.val) (ht.image _))
  have hI₀ne : d I₀ ≠ 0 := (mem_filter.mp hI₀t).2
  have hI₀_diag : (multilinearMonomial ℤ I₀.val * g) I₀.val = g I₀.val := by
    simp [multilinearMonomial]
  have hsum : ∑ I : J, d I * (multilinearMonomial ℤ I.val * g) I₀.val = d I₀ * g I₀.val := by
    rw [← hI₀_diag]
    refine sum_eq_single I₀ (fun I _ hII₀ ↦ ?_) (fun hmem ↦ absurd (mem_univ I₀) hmem)
    by_cases hIc : d I = 0
    · simp [hIc]
    · have hIt : I ∈ t := mem_filter.mpr ⟨mem_univ I, hIc⟩
      have hcard : #I₀.val ≤ #I.val := hI₀min ▸ min'_le _ _ (mem_image_of_mem _ hIt)
      have hnsub : ¬ I.val ⊆ I₀.val := fun hsub ↦
        hII₀ (Subtype.ext (eq_of_subset_of_card_le hsub hcard))
      simp [multilinearMonomial, hnsub]
  have hzero : d I₀ * g I₀.val = 0 := hsum ▸ hd I₀
  exact (mul_eq_zero.mp hzero).elim hI₀ne (hg I₀.val I₀.property)

end

variable {α : Type*} [Fintype α] [DecidableEq α]

private def multilinearSubmodule (R : Type*) [CommRing R] (α : Type*) [Fintype α]
    [DecidableEq α] (d : ℕ) : Submodule R (Finset α → R) :=
  Submodule.span R
    ((multilinearMonomial R) ''
      (((range (d + 1)).biUnion fun i ↦ (univ : Finset α).powersetCard i) : Set (Finset α)))

private lemma multilinearMonomial_mem_multilinearSubmodule {R : Type*} [CommRing R] {I : Finset α}
    {d : ℕ} (hI : #I ≤ d) : multilinearMonomial R I ∈ multilinearSubmodule R α d := by
  refine Submodule.subset_span ?_
  refine ⟨I, ?_, rfl⟩
  simp only [mem_coe, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and]
  exact ⟨#I, Nat.lt_succ_of_le hI, rfl⟩

private lemma const_mem_multilinearSubmodule {R : Type*} [CommRing R] (c : R) (d : ℕ) :
    (fun _ : Finset α ↦ c) ∈ multilinearSubmodule R α d := by
  have h : (fun _ : Finset α ↦ c) = c • multilinearMonomial R ∅ := by
    ext B
    simp [multilinearMonomial]
  rw [h]
  exact Submodule.smul_mem _ c (multilinearMonomial_mem_multilinearSubmodule (by simp))

private lemma multilinearSubmodule_mono {R : Type*} [CommRing R] {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    multilinearSubmodule R α d₁ ≤ multilinearSubmodule R α d₂ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨I, hI, rfl⟩
  simp only [mem_coe, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and] at hI
  obtain ⟨i, hi, rfl⟩ := hI
  exact multilinearMonomial_mem_multilinearSubmodule (Nat.le_of_lt_succ hi |>.trans h)

private lemma mul_mem_multilinearSubmodule {R : Type*} [CommRing R] {f g : Finset α → R}
    {d₁ d₂ : ℕ} (hf : f ∈ multilinearSubmodule R α d₁) (hg : g ∈ multilinearSubmodule R α d₂) :
    f * g ∈ multilinearSubmodule R α (d₁ + d₂) := by
  refine Submodule.span_induction (p := fun f _ ↦ f * g ∈ multilinearSubmodule R α (d₁ + d₂))
    ?_ (by simp) (fun _ _ _ _ ha hb ↦ by rw [add_mul]; exact add_mem ha hb)
    (fun r _ _ ha ↦ by rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha) hf
  rintro _ ⟨I, hI, rfl⟩
  simp only [mem_coe, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and] at hI
  obtain ⟨i, hi, hIi⟩ := hI
  refine Submodule.span_induction
    (p := fun g _ ↦ multilinearMonomial R I * g ∈ multilinearSubmodule R α (d₁ + d₂))
    ?_ (by simp) (fun _ _ _ _ ha hb ↦ by rw [mul_add]; exact add_mem ha hb)
    (fun r _ _ ha ↦ by rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha) hg
  rintro _ ⟨J, hJ, rfl⟩
  simp only [mem_coe, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and] at hJ
  obtain ⟨j, hj, hJj⟩ := hJ
  rw [multilinearMonomial_mul]
  exact multilinearMonomial_mem_multilinearSubmodule
    ((card_union_le I J).trans (by rw [hIi, hJj]; omega))

private lemma prod_mem_multilinearSubmodule {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → Finset α → R) (hf : ∀ i ∈ s, f i ∈ multilinearSubmodule R α 1) :
    (∏ i ∈ s, f i) ∈ multilinearSubmodule R α #s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Pi.one_def] using const_mem_multilinearSubmodule (α := α) (1 : R) 0
  | @insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha, add_comm #s 1]
    exact mul_mem_multilinearSubmodule (hf a (mem_insert_self a s))
      (ih fun i hi ↦ hf i (mem_insert_of_mem hi))

private lemma card_inter_sub_mem_multilinearSubmodule {R : Type*} [CommRing R] (A : Finset α)
    (c : R) : (fun B : Finset α ↦ (#(A ∩ B) : R) - c) ∈ multilinearSubmodule R α 1 := by
  have hsum : (fun B : Finset α ↦ (#(A ∩ B) : R)) = ∑ a ∈ A, multilinearMonomial R {a} := by
    ext B
    simp [Finset.sum_apply, multilinearMonomial]
  refine Submodule.sub_mem _ ?_ (const_mem_multilinearSubmodule c 1)
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ ↦ multilinearMonomial_mem_multilinearSubmodule (by simp)

private lemma prod_card_inter_sub_mem_multilinearSubmodule {R : Type*} [CommRing R] (A : Finset α)
    (L : Finset R) :
    (fun B : Finset α ↦ ∏ l ∈ L, ((#(A ∩ B) : R) - l)) ∈ multilinearSubmodule R α #L := by
  have h : (fun B : Finset α ↦ ∏ l ∈ L, ((#(A ∩ B) : R) - l)) =
      ∏ l ∈ L, (fun B : Finset α ↦ (#(A ∩ B) : R) - l) := by
    ext B
    simp
  rw [h]
  exact prod_mem_multilinearSubmodule L _ fun l _ ↦ card_inter_sub_mem_multilinearSubmodule A l

private lemma finrank_multilinearSubmodule_le (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) :
    Module.finrank R (multilinearSubmodule R α d) ≤
      ∑ i ∈ range (d + 1), (Fintype.card α).choose i := by
  have hfin : (((range (d + 1)).biUnion fun i ↦ (univ : Finset α).powersetCard i) :
      Set (Finset α)).Finite := Finset.finite_toSet _
  unfold multilinearSubmodule
  have hle := finrank_span_le_ncard (R := R)
    ((multilinearMonomial R) ''
      (((range (d + 1)).biUnion fun i ↦ (univ : Finset α).powersetCard i) : Set (Finset α)))
    (hfin.image (multilinearMonomial R))
  refine hle.trans ((Set.ncard_image_le hfin).trans ?_)
  rw [Set.ncard_coe_finset, card_biUnion (fun i _ j _ hij ↦ disjoint_powersetCard_of_ne hij _ _)]
  simp only [card_powersetCard, card_univ, le_refl]

private lemma card_le_sum_choose_of_linearIndependent {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [Fintype ι] {d : ℕ} {v : ι → Finset α → R}
    (hmem : ∀ i, v i ∈ multilinearSubmodule R α d) (hli : LinearIndependent R v) :
    Fintype.card ι ≤ ∑ i ∈ range (d + 1), (Fintype.card α).choose i := by
  let w : ι → multilinearSubmodule R α d := fun i ↦ ⟨v i, hmem i⟩
  have hwi : LinearIndependent R w := hli.of_comp (multilinearSubmodule R α d).subtype
  have : Module.Finite R (multilinearSubmodule R α d) :=
    Module.Finite.span_of_finite R ((Finset.finite_toSet _).image _)
  exact hwi.fintype_card_le_finrank.trans (finrank_multilinearSubmodule_le R d)

private lemma fwPoly_mem_multilinearSubmodule (L : Finset ℕ) (A : Finset α) :
    fwPoly L A ∈ multilinearSubmodule ℤ α #L := by
  have h : fwPoly L A = ∏ l ∈ L.filter (· < #A), (fun B : Finset α ↦ (#(A ∩ B) : ℤ) - l) := by
    ext B
    simp [fwPoly]
  rw [h]
  exact multilinearSubmodule_mono (card_filter_le L _)
    (prod_mem_multilinearSubmodule _ _ fun l _ ↦ card_inter_sub_mem_multilinearSubmodule A _)

/-- **The nonuniform Frankl–Wilson inequality.** If any two distinct members of a family `F` of
subsets of an `n`-element set meet in a number of elements belonging to `L`, then
`#F ≤ ∑ i ≤ #L, C(n, i)`. -/
theorem card_le_sum_choose_of_isIntersectingOf (F : Finset (Finset α)) (L : Finset ℕ)
    (h : Set.IsIntersectingOf (L : Set ℕ) (F : Set (Finset α))) :
    #F ≤ ∑ i ∈ range (#L + 1), (Fintype.card α).choose i := by
  have hli : LinearIndependent ℤ (fun A : F ↦ fwPoly L A.val) := by
    rw [linearIndependent_iff']
    intro s c hc A hA
    let c' : F → ℤ := fun x ↦ if x ∈ s then c x else 0
    have hc' : ∀ B : F, ∑ A' : F, c' A' * fwPoly L A'.val B.val = 0 := by
      intro B
      have hB : (∑ x ∈ s, c x • fwPoly L x.val) B.val = 0 := congr_fun hc B.val
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hB
      calc ∑ A' : F, c' A' * fwPoly L A'.val B.val
          = ∑ A' ∈ s, c' A' * fwPoly L A'.val B.val :=
              (sum_subset (subset_univ s) fun A' _ hA' ↦ by simp [c', hA']).symm
        _ = ∑ A' ∈ s, c A' * fwPoly L A'.val B.val :=
              sum_congr rfl fun A' hA' ↦ by simp [c', hA']
        _ = 0 := hB
    simpa [c', hA] using fwPoly_coeff_eq_zero h hc' A
  rw [← Fintype.card_coe F]
  exact card_le_sum_choose_of_linearIndependent
    (fun A : F ↦ fwPoly_mem_multilinearSubmodule L A.val) hli

private lemma linearIndependent_fwPoly_elim_abs {F : Finset (Finset α)} {K L : Finset ℕ}
    (hK : ∀ A ∈ F, #A ∈ K) (hKL : ∀ k ∈ K, #L < k + #K)
    (h : Set.IsIntersectingOf (L : Set ℕ) (F : Set (Finset α))) (hKL_le : #K ≤ #L) :
    let d := #L - #K
    let J : Finset (Finset α) := (range (d + 1)).biUnion fun i ↦ (univ : Finset α).powersetCard i
    let g : Finset α → ℤ := fun B ↦ ∏ k ∈ K, ((#B : ℤ) - k)
    LinearIndependent ℤ
      (Sum.elim (fun A : F ↦ fwPoly L A.val) (fun I : J ↦ multilinearMonomial ℤ I.val * g)) := by
  intro d J g
  rw [linearIndependent_iff']
  intro s c hc
  let c' : F ⊕ J → ℤ := fun x ↦ if x ∈ s then c x else 0
  let v : F ⊕ J → Finset α → ℤ :=
    Sum.elim (fun A : F ↦ fwPoly L A.val) (fun I : J ↦ multilinearMonomial ℤ I.val * g)
  have hc_sum : ∀ B : Finset α, ∑ x : F ⊕ J, c' x * v x B = 0 := fun B ↦ by
    have hB : (∑ x ∈ s, c x • v x) B = 0 := congr_fun hc B
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hB
    calc ∑ x : F ⊕ J, c' x * v x B
        = ∑ x ∈ s, c' x * v x B :=
            (sum_subset (subset_univ s) fun x _ hx ↦ by simp [c', hx]).symm
      _ = ∑ x ∈ s, c x * v x B := sum_congr rfl fun x hx ↦ by simp [c', hx]
      _ = 0 := hB
  have hF : ∀ A : F, c' (Sum.inl A) = 0 := by
    refine fwPoly_coeff_eq_zero h fun B ↦ ?_
    have hgB : g B.val = 0 := prod_eq_zero (hK B.val B.property) (sub_self _)
    have htot := hc_sum B.val
    rw [Fintype.sum_sum_type] at htot
    simp only [v, Sum.elim_inl, Sum.elim_inr, Pi.mul_apply, hgB, mul_zero, sum_const_zero,
      add_zero] at htot
    exact htot
  have hJ : ∀ I : J, c' (Sum.inr I) = 0 := by
    refine multilinearMonomial_mul_coeff_eq_zero (g := g) (fun I hIJ ↦ ?_) fun I₀ ↦ ?_
    · obtain ⟨i, hi, hi'⟩ := mem_biUnion.mp hIJ
      have hIcard : #I ≤ d := (mem_powersetCard.mp hi').2 ▸ Nat.le_of_lt_succ (mem_range.mp hi)
      rw [prod_ne_zero_iff]
      intro k hk
      have hkd : d < k := by have := hKL k hk; omega
      rw [sub_ne_zero]
      exact_mod_cast (hIcard.trans_lt hkd).ne
    · have htot := hc_sum I₀.val
      rw [Fintype.sum_sum_type] at htot
      simp only [v, Sum.elim_inl, Sum.elim_inr] at htot
      have hF0 : ∑ A : F, c' (Sum.inl A) * fwPoly L A.val I₀.val = 0 := by simp [hF]
      rwa [hF0, zero_add] at htot
  rintro (A | I) hx
  · simpa [c', hx] using hF A
  · simpa [c', hx] using hJ I

/-- **The Alon–Babai–Suzuki theorem.** Let `K` and `L` be finite sets of natural numbers such that
`k > #L - #K` for all `k ∈ K`. If every member of a family `F` of subsets of an `n`-element set has
size in `K` and any two distinct members meet in a number of elements in `L`, then
`#F ≤ ∑ j ∈ Ico (#L + 1 - #K) (#L + 1), C(n, j)`. -/
theorem card_le_sum_choose_of_card_mem (F : Finset (Finset α)) (K L : Finset ℕ)
    (hK : ∀ A ∈ F, #A ∈ K) (hKL : ∀ k ∈ K, #L < k + #K)
    (h : Set.IsIntersectingOf (L : Set ℕ) (F : Set (Finset α))) :
    #F ≤ ∑ j ∈ Ico (#L + 1 - #K) (#L + 1), (Fintype.card α).choose j := by
  by_cases hKempty : K = ∅
  · have hF : F = ∅ := eq_empty_of_forall_notMem fun A hA ↦ by simpa [hKempty] using hK A hA
    simp [hF]
  by_cases hKL_lt : #L < #K
  · have hsub : #L + 1 - #K = 0 := Nat.sub_eq_zero_of_le hKL_lt
    rw [hsub, Nat.Ico_zero_eq_range]
    exact F.card_le_sum_choose_of_isIntersectingOf L h
  have hKL_le : #K ≤ #L := Nat.le_of_not_lt hKL_lt
  let d := #L - #K
  let J : Finset (Finset α) := (range (d + 1)).biUnion fun i ↦ (univ : Finset α).powersetCard i
  let g : Finset α → ℤ := fun B ↦ ∏ k ∈ K, ((#B : ℤ) - k)
  have hg_mem : g ∈ multilinearSubmodule ℤ α #K := by
    have hg : g = ∏ k ∈ K, (fun B : Finset α ↦ (#B : ℤ) - k) := by ext B; simp [g]
    rw [hg]
    exact prod_mem_multilinearSubmodule K _ fun k _ ↦ by
      simpa using card_inter_sub_mem_multilinearSubmodule (univ : Finset α) (k : ℤ)
  have hmem : ∀ x : F ⊕ J,
      Sum.elim (fun A : F ↦ fwPoly L A.val) (fun I : J ↦ multilinearMonomial ℤ I.val * g) x ∈
        multilinearSubmodule ℤ α #L := by
    rintro (A | I)
    · exact fwPoly_mem_multilinearSubmodule L A.val
    · obtain ⟨i, hi, hi'⟩ := mem_biUnion.mp I.property
      have hIcard : #I.val ≤ d := (mem_powersetCard.mp hi').2 ▸ Nat.le_of_lt_succ (mem_range.mp hi)
      have hdK : d + #K = #L := Nat.sub_add_cancel hKL_le
      simpa [hdK] using mul_mem_multilinearSubmodule
        (multilinearMonomial_mem_multilinearSubmodule (R := ℤ) hIcard) hg_mem
  have hli := linearIndependent_fwPoly_elim_abs hK hKL h hKL_le
  have hcard := card_le_sum_choose_of_linearIndependent hmem hli
  have hJcard : #J = ∑ i ∈ range (d + 1), (Fintype.card α).choose i := by
    rw [card_biUnion (fun i _ j _ hij ↦ disjoint_powersetCard_of_ne hij _ _)]
    simp [card_powersetCard]
  have hsum : (∑ i ∈ range (d + 1), (Fintype.card α).choose i) +
      ∑ j ∈ Ico (d + 1) (#L + 1), (Fintype.card α).choose j =
      ∑ i ∈ range (#L + 1), (Fintype.card α).choose i :=
    sum_range_add_sum_Ico _ (by omega)
  have hsub : #L + 1 - #K = d + 1 := by omega
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, hJcard, ← hsum] at hcard
  rw [hsub]
  omega

/-- **The Ray-Chaudhuri–Wilson theorem.** A uniform family `F` of `k`-element subsets of an
`n`-element set that is `L`-intersecting with `#L ≤ k` has at most `C(n, #L)` members. -/
theorem card_le_choose_of_card_eq (F : Finset (Finset α)) (L : Finset ℕ) {k : ℕ}
    (hk : ∀ A ∈ F, #A = k) (hLk : #L ≤ k)
    (h : Set.IsIntersectingOf (L : Set ℕ) (F : Set (Finset α))) :
    #F ≤ (Fintype.card α).choose #L := by
  have hmem := F.card_le_sum_choose_of_card_mem {k} L (fun A hA ↦ by simp [hk A hA])
    (fun k' hk' ↦ by simp only [mem_singleton.mp hk', card_singleton]; omega) h
  simpa [Nat.Ico_succ_singleton] using hmem

/-- **The modular Frankl–Wilson inequality** over an integral domain `R` (in particular `ZMod p` for
a prime `p`). If no member of `F` has size lying in `L ⊆ R` and every two distinct members meet in
a number of elements whose cast to `R` lies in `L`, then `#F ≤ ∑ i ≤ #L, C(n, i)`. -/
theorem card_le_sum_choose_of_natCast_card_notMem (F : Finset (Finset α))
    {R : Type*} [CommRing R] [IsDomain R] (L : Finset R)
    (hsize : ∀ A ∈ F, ((#A : ℕ) : R) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((#(A ∩ B) : ℕ) : R) ∈ L) :
    #F ≤ ∑ i ∈ range (#L + 1), (Fintype.card α).choose i := by
  let f : F → Finset α → R := fun A B ↦ ∏ l ∈ L, ((#(A.val ∩ B) : R) - l)
  have hli : LinearIndependent R f := by
    rw [linearIndependent_iff']
    intro s c hc B hB
    have hBval : (∑ A ∈ s, c A • f A) B.val = 0 := congr_fun hc B.val
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hBval
    have hdiag : ∑ A ∈ s, c A * f A B.val = c B * f B B.val := by
      refine sum_eq_single B (fun A _ hAB ↦ ?_) (fun h ↦ absurd hB h)
      have hzero : f A B.val = 0 :=
        prod_eq_zero (hinter A.val A.property B.val B.property (Subtype.coe_ne_coe.mpr hAB))
          (sub_self _)
      simp [hzero]
    rw [hdiag, mul_eq_zero] at hBval
    refine hBval.resolve_right ?_
    dsimp [f]
    rw [← ne_eq, prod_ne_zero_iff]
    intro l hl
    exact sub_ne_zero.mpr fun heq ↦ hsize B.val B.property (by simpa [← heq] using hl)
  rw [← Fintype.card_coe F]
  exact card_le_sum_choose_of_linearIndependent (v := f)
    (fun A ↦ prod_card_inter_sub_mem_multilinearSubmodule A.val L) hli

/-- **A forbidden-intersection bound.** For a prime `p`, if every member of a family `F` of subsets
of an `n`-element set has `2p - 1` elements and no two distinct members meet in `p - 1` elements,
then `#F ≤ ∑ i < p, C(n, i)`. -/
theorem card_le_sum_choose_of_inter_ne (F : Finset (Finset α)) {p : ℕ} (hp : p.Prime)
    (hsize : ∀ A ∈ F, #A = 2 * p - 1)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → #(A ∩ B) ≠ p - 1) :
    #F ≤ ∑ i ∈ range p, (Fintype.card α).choose i := by
  have : Fact p.Prime := ⟨hp⟩
  let r : ZMod p := ((p - 1 : ℕ) : ZMod p)
  let L : Finset (ZMod p) := univ.erase r
  have hLcard : #L + 1 = p := by
    rw [card_erase_of_mem (mem_univ r), card_univ, ZMod.card, Nat.sub_add_cancel hp.pos]
  have hbound := F.card_le_sum_choose_of_natCast_card_notMem L ?_ ?_
  · rwa [hLcard] at hbound
  · intro A hA
    have hcast : ((#A : ℕ) : ZMod p) = r := by
      have heq : #A = p + (p - 1) := by have := hsize A hA; have := hp.pos; omega
      simp [heq, r]
    simp [L, hcast]
  · intro A hA B hB hAB
    refine mem_erase.mpr ⟨fun heq ↦ ?_, mem_univ _⟩
    have hlt : #(A ∩ B) < 2 * p - 1 := by
      have hAcard := hsize A hA
      have hBcard := hsize B hB
      by_contra! hge
      have hABeq : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left (by omega)
      have hsub : A ⊆ B := hABeq ▸ inter_subset_right
      exact hAB (eq_of_subset_of_card_le hsub (by omega))
    have hmod : #(A ∩ B) % p = (p - 1) % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp heq
    have hp1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (Nat.sub_lt hp.pos one_pos)
    have hdiv := Nat.div_add_mod #(A ∩ B) p
    have hq : #(A ∩ B) / p = 0 := by
      by_contra! hq0
      have hmul : p ≤ p * (#(A ∩ B) / p) := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hq0)
      omega
    rw [hq, mul_zero, zero_add] at hdiv
    exact hinter A hA B hB hAB (hdiv.symm.trans (hmod.trans hp1))

end Finset
