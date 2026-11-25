/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Basic
public import TauCeti.NumberTheory.Hypergeometric.CyclotomicData
public import TauCeti.NumberTheory.Hypergeometric.Parameters
import TauCeti.Algebra.AddCircle
import TauCeti.Data.Int.Progression
import TauCeti.GroupTheory.OrderOfElement.Basic

/-!
# The dictionary between cyclotomic data and parameter pairs

A cyclotomic datum `(A, B)` determines a hypergeometric parameter pair `(α, β)`: `α` collects,
for each `a ∈ A`, the classes `k / a` in `ℚ/ℤ` with `1 ≤ k ≤ a` and `k` prime to `a`, and `β` is
built from `B` in the same way. These are the arguments of the roots of `Φ_A = ∏_{a ∈ A} Φ_a` and
of `Φ_B`, so that the local monodromy of the hypergeometric equation read off `(α, β)` has the
characteristic polynomials `Φ_A` and `Φ_B`. This is how the LMFDB passes from the family label
`A…_B…` to the parameters its zigzag, finite sums and Euler factors are computed from.

The classes `k / a` attached to an index `a` are exactly the classes of additive order `a`, each
once. So a class `x` occurs in `α` as often as its order occurs in `A`, which gives the
cardinality `∑_{a ∈ A} φ(a)`, disjointness of `α` and `β`, injectivity of the dictionary and its
common denominator `lcm (A + B)`. Scaling by an integer prime to an index permutes the classes of
that order, so the parameter pair of a datum is Galois stable. Conversely a Galois-stable pair
gives every class of a fixed order the same multiplicity, because two classes of the same order are
unit multiples of each other, and is the pair of a unique cyclotomic datum.

## Main declarations

* `TauCeti.Hypergeometric.primitiveClasses`: the multiset `α(A)` of classes of a multiset of
  indices, with `count_primitiveClasses`, `card_primitiveClasses`, `primitiveClasses_inj` and
  `map_zsmul_primitiveClasses`.
* `TauCeti.Hypergeometric.count_eq_count_of_map_zsmul_eq` and
  `TauCeti.Hypergeometric.exists_primitiveClasses_eq`: a multiset of classes stable under the
  units modulo a common denominator is the multiset `α(A)` of some `A`.
* `TauCeti.Hypergeometric.prod_X_sub_C_expCircle_primitiveClasses`: over `ℂ`,
  `∏_{x ∈ α(A)} (X - e^{2πi x}) = ∏_{a ∈ A} Φ_a`, with `e^{2πi x}` the character
  `TauCeti.expCircle`.
* `TauCeti.Hypergeometric.CyclotomicData.toParameters`: the dictionary, with
  `toParameters_injective`, `toParameters_swap`, `denominator_toParameters`,
  `range_toParameters` (the image is the Galois-stable pairs) and
  `existsUnique_toParameters_eq`.

## References

* F. Beukers and G. Heckman, *Monodromy for the hypergeometric function `ₙFₙ₋₁`*, Invent. Math.
  95 (1989), §3.
* D. P. Roberts and F. Rodriguez-Villegas, *Hypergeometric motives*, Notices Amer. Math. Soc. 69
  (2022), §2.
-/

public section

open Polynomial

namespace TauCeti.Hypergeometric

/-! ### Primitive classes -/

/-- The *primitive classes* `α(A)` of a multiset `A` of indices: for each `a ∈ A`, the classes
`k / a` in `ℚ/ℤ` with `1 ≤ k ≤ a` and `k` prime to `a`. These are the classes of additive order
exactly `a` (`mem_primitiveClasses_singleton`), and read through `x ↦ e^{2πi x}` they are the
arguments of the roots of `∏_{a ∈ A} Φ_a` (`prod_X_sub_C_expCircle_primitiveClasses`). -/
def primitiveClasses (A : Multiset ℕ) : Multiset (AddCircle (1 : ℚ)) :=
  A.bind fun a ↦ ((Finset.Icc 1 a).filter a.Coprime).val.map
    fun k : ℕ ↦ (((k : ℚ) / a : ℚ) : AddCircle (1 : ℚ))

@[simp]
theorem primitiveClasses_zero : primitiveClasses 0 = 0 :=
  Multiset.zero_bind _

@[simp]
theorem primitiveClasses_add (A B : Multiset ℕ) :
    primitiveClasses (A + B) = primitiveClasses A + primitiveClasses B :=
  Multiset.add_bind _ _ _

theorem primitiveClasses_singleton (a : ℕ) :
    primitiveClasses {a} = ((Finset.Icc 1 a).filter a.Coprime).val.map
      fun k : ℕ ↦ (((k : ℚ) / a : ℚ) : AddCircle (1 : ℚ)) :=
  Multiset.singleton_bind _ _

theorem primitiveClasses_cons (a : ℕ) (A : Multiset ℕ) :
    primitiveClasses (a ::ₘ A) = primitiveClasses {a} + primitiveClasses A := by
  rw [← Multiset.singleton_add, primitiveClasses_add]

/-- The class `k / a` with `1 ≤ k ≤ a` is represented by `k / a` itself in `(0, 1]`. -/
private theorem div_mem_Ioc {a k : ℕ} (hk : k ∈ Finset.Icc 1 a) :
    (k : ℚ) / a ∈ Set.Ioc (0 : ℚ) 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  exact ⟨div_pos (by exact_mod_cast h1) (by exact_mod_cast h1.trans h2),
    div_le_one_of_le₀ (by exact_mod_cast h2) (Nat.cast_nonneg a)⟩

/-- The classes `k / a`, `1 ≤ k ≤ a`, are pairwise distinct. -/
theorem nodup_primitiveClasses_singleton (a : ℕ) : (primitiveClasses {a}).Nodup := by
  rw [primitiveClasses_singleton]
  refine Multiset.Nodup.map_on (fun k hk l hl h ↦ ?_) (Finset.nodup _)
  rw [Finset.mem_val, Finset.mem_filter] at hk hl
  have h' := congrArg rep h
  rw [rep_coe_of_mem (div_mem_Ioc hk.1), rep_coe_of_mem (div_mem_Ioc hl.1),
    div_left_inj₀ (Nat.cast_ne_zero.mpr (by have := Finset.mem_Icc.mp hk.1; omega))] at h'
  exact_mod_cast h'

/-- The primitive classes of a single index `a` are the classes of additive order `a`. -/
theorem mem_primitiveClasses_singleton {a : ℕ} {x : AddCircle (1 : ℚ)} :
    x ∈ primitiveClasses {a} ↔ addOrderOf x = a := by
  rw [primitiveClasses_singleton, Multiset.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_val, Finset.mem_filter, Finset.mem_Icc] at hk
    simpa using AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℚ)) (by omega) hk.2.symm
  · intro hx
    have ha : 0 < a := hx ▸ (AddCircle.isOfFinAddOrder_rat x).addOrderOf_pos
    obtain ⟨m, hm, hgcd, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff (p := (1 : ℚ)) ha).mp hx
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · -- The class `0` has order `1` and is represented by `k = 1`.
      obtain rfl : a = 1 := by simpa using hgcd
      exact ⟨1, by simp, by simp⟩
    · refine ⟨m, ?_, by simp⟩
      rw [Finset.mem_val, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm0, hm.le⟩, Nat.Coprime.symm hgcd⟩

/-- A class occurs in `α(A)` as often as its additive order occurs in `A`. -/
@[simp]
theorem count_primitiveClasses [DecidableEq (AddCircle (1 : ℚ))] (A : Multiset ℕ)
    (x : AddCircle (1 : ℚ)) : (primitiveClasses A).count x = A.count (addOrderOf x) := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [primitiveClasses_cons, Multiset.count_add, ih, Multiset.count_cons]
    split_ifs with h
    · rw [Multiset.count_eq_one_of_mem (nodup_primitiveClasses_singleton a)
        (mem_primitiveClasses_singleton.mpr h), add_comm]
    · rw [Multiset.count_eq_zero.mpr (mt mem_primitiveClasses_singleton.mp h), zero_add,
        add_zero]

@[simp]
theorem mem_primitiveClasses {A : Multiset ℕ} {x : AddCircle (1 : ℚ)} :
    x ∈ primitiveClasses A ↔ addOrderOf x ∈ A := by
  classical
  rw [← Multiset.count_pos, count_primitiveClasses, Multiset.count_pos]

/-- For positive `a`, the class of `1 / a` lies in `α(A)` exactly when `a ∈ A`. -/
theorem coe_one_div_mem_primitiveClasses {A : Multiset ℕ} {a : ℕ} (ha : 0 < a) :
    ((1 / a : ℚ) : AddCircle (1 : ℚ)) ∈ primitiveClasses A ↔ a ∈ A := by
  rw [mem_primitiveClasses, AddCircle.addOrderOf_period_div ha]

/-- `α(A)` has `∑_{a ∈ A} φ(a)` elements. -/
@[simp]
theorem card_primitiveClasses (A : Multiset ℕ) :
    Multiset.card (primitiveClasses A) = (A.map Nat.totient).sum := by
  rw [primitiveClasses, Multiset.card_bind]
  refine congrArg _ (Multiset.map_congr rfl fun a _ ↦ ?_)
  have h : Finset.Icc 1 a = Finset.Ico 1 (1 + a) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Function.comp_apply, Multiset.card_map, Finset.card_val, h,
    Nat.filter_coprime_Ico_eq_totient]

/-- Multisets of positive indices are determined by their primitive classes. -/
theorem primitiveClasses_inj {A B : Multiset ℕ} (hA : 0 ∉ A) (hB : 0 ∉ B) :
    primitiveClasses A = primitiveClasses B ↔ A = B := by
  classical
  refine ⟨fun h ↦ Multiset.ext.mpr fun a ↦ ?_, congrArg _⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.count_eq_zero.mpr hA, Multiset.count_eq_zero.mpr hB]
  · rw [← AddCircle.addOrderOf_period_div (p := (1 : ℚ)) ha, ← count_primitiveClasses, h,
      count_primitiveClasses]

/-- The additive orders of the classes of `α(A)` have the same lcm as the positive indices
`A`. -/
theorem lcm_map_addOrderOf_primitiveClasses {A : Multiset ℕ} (hA : 0 ∉ A) :
    ((primitiveClasses A).map addOrderOf).lcm = A.lcm := by
  rw [← Multiset.lcm_dedup, ← Multiset.lcm_dedup A]
  refine congrArg _ ((Multiset.Nodup.ext (Multiset.nodup_dedup _)
    (Multiset.nodup_dedup _)).mpr fun a ↦ ?_)
  simp only [Multiset.mem_dedup, Multiset.mem_map]
  refine ⟨fun ⟨_, hx, hxa⟩ ↦ hxa ▸ mem_primitiveClasses.mp hx, fun ha ↦ ?_⟩
  have ha0 : 0 < a := Nat.pos_of_ne_zero (ne_of_mem_of_not_mem ha hA)
  exact ⟨_, (coe_one_div_mem_primitiveClasses ha0).mpr ha, AddCircle.addOrderOf_period_div ha0⟩

/-- Scaling by an integer prime to `a` permutes the classes of order `a`. -/
theorem map_zsmul_primitiveClasses_singleton {a : ℕ} {u : ℤ} (hu : IsCoprime u a) :
    (primitiveClasses {a}).map (u • ·) = primitiveClasses {a} := by
  have hinj : ∀ x ∈ primitiveClasses {a}, ∀ y ∈ primitiveClasses {a}, u • x = u • y → x = y :=
    fun x hx y hy ↦ hu.injOn_zsmul_of_addOrderOf_dvd
      (mem_primitiveClasses_singleton.mp hx).dvd (mem_primitiveClasses_singleton.mp hy).dvd
  have hnodup := (nodup_primitiveClasses_singleton a).map_on hinj
  -- The image is a duplicate-free submultiset of the classes of order `a` of the same size.
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnodup).mpr fun y hy ↦ ?_)
    (Multiset.card_map _ _).ge
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  rw [mem_primitiveClasses_singleton] at hx ⊢
  exact (IsCoprime.addOrderOf_zsmul (hx ▸ hu)).trans hx

/-- Scaling by an integer prime to every index of `A` fixes `α(A)`. -/
theorem map_zsmul_primitiveClasses {A : Multiset ℕ} {u : ℤ} (hu : ∀ a ∈ A, IsCoprime u a) :
    (primitiveClasses A).map (u • ·) = primitiveClasses A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [primitiveClasses_cons, Multiset.map_add,
      map_zsmul_primitiveClasses_singleton (hu a (Multiset.mem_cons_self a A)),
      ih fun b hb ↦ hu b (Multiset.mem_cons_of_mem hb)]

/-- A multiset of classes in which classes of the same additive order occur equally often is the
multiset of primitive classes of a multiset of positive indices. -/
theorem exists_primitiveClasses_eq [DecidableEq (AddCircle (1 : ℚ))]
    {s : Multiset (AddCircle (1 : ℚ))}
    (hs : ∀ x y, addOrderOf x = addOrderOf y → s.count x = s.count y) :
    ∃ A, 0 ∉ A ∧ primitiveClasses A = s := by
  -- `A` lists the orders of the occurrences in `s` of the canonical classes `1 / n`.
  let g (n : ℕ) : AddCircle (1 : ℚ) := (((1 : ℚ) / n : ℚ) : AddCircle (1 : ℚ))
  refine ⟨(s.filter fun x ↦ x = g (addOrderOf x)).map addOrderOf, ?_,
    Multiset.ext.mpr fun x ↦ ?_⟩
  · simp only [Multiset.mem_map, not_exists, not_and]
    exact fun x _ h ↦ (AddCircle.isOfFinAddOrder_rat x).addOrderOf_pos.ne' h
  · have hg : addOrderOf (g (addOrderOf x)) = addOrderOf x :=
      AddCircle.addOrderOf_period_div (AddCircle.isOfFinAddOrder_rat x).addOrderOf_pos
    rw [count_primitiveClasses, Multiset.count_map, Multiset.filter_filter,
      hs x (g (addOrderOf x)) hg.symm, Multiset.count_eq_card_filter_eq]
    refine congrArg _ (Multiset.filter_congr fun y _ ↦ ⟨fun ⟨hxy, hy⟩ ↦ ?_, ?_⟩)
    · rw [hxy, ← hy]
    · rintro rfl
      exact ⟨hg.symm, by rw [hg]⟩

/-- In a multiset of classes killed by `N ≠ 0` and stable under every scaling by an integer prime
to `N`, classes of the same additive order occur equally often: such classes are exchanged by a
scaling prime to `N`. -/
theorem count_eq_count_of_map_zsmul_eq [DecidableEq (AddCircle (1 : ℚ))]
    {s : Multiset (AddCircle (1 : ℚ))} {N : ℕ} (hN : N ≠ 0) (hsN : ∀ x ∈ s, addOrderOf x ∣ N)
    (hs : ∀ u : ℤ, IsCoprime u N → s.map (u • ·) = s) {x y : AddCircle (1 : ℚ)}
    (h : addOrderOf x = addOrderOf y) : s.count x = s.count y := by
  suffices key : ∀ x y, addOrderOf x = addOrderOf y → x ∈ s → s.count x = s.count y by
    by_cases hx : x ∈ s
    · exact key x y h hx
    by_cases hy : y ∈ s
    · exact (key y x h.symm hy).symm
    rw [Multiset.count_eq_zero.mpr hx, Multiset.count_eq_zero.mpr hy]
  intro x y h hx
  -- `y = k • x` with `k` prime to the order of `x`; lift `k` to a unit modulo `N`.
  obtain ⟨k, hk, rfl⟩ := AddCircle.exists_isCoprime_zsmul_eq_of_addOrderOf_eq (p := (1 : ℚ))
    (AddCircle.isOfFinAddOrder_rat x).addOrderOf_pos h
  obtain ⟨t, ht⟩ := hk.exists_isCoprime_add_mul (m := N) (Int.natCast_ne_zero.mpr hN)
  have hux : (k + t * addOrderOf x) • x = k • x := by
    rw [add_smul, mul_smul, natCast_zsmul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]
  have hinj : Set.InjOn ((k + t * addOrderOf x) • ·) {z | z ∈ s} :=
    ht.injOn_zsmul_of_addOrderOf_dvd.mono fun z hz ↦ hsN z hz
  rw [← hux, ← Multiset.count_map_eq_count _ s hinj x hx, hs _ ht]

/-! ### Roots of the cyclotomic products -/

/-- Over `ℂ`, the classes of order `a` are the arguments of the roots of `Φ_a`. -/
theorem prod_X_sub_C_expCircle_primitiveClasses_singleton (a : ℕ) :
    ((primitiveClasses {a}).map fun x ↦ X - C (expCircle x)).prod = cyclotomic a ℂ := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [primitiveClasses_singleton]
  have hroots : (primitiveClasses {a}).map expCircle = (primitiveRoots a ℂ).val := by
    refine (Multiset.Nodup.ext ((nodup_primitiveClasses_singleton a).map expCircle_injective)
      (primitiveRoots a ℂ).nodup).mpr fun μ ↦ ?_
    rw [Finset.mem_val, mem_primitiveRoots ha, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_primitiveClasses_singleton.mp hx ▸ isPrimitiveRoot_expCircle_addOrderOf x
    · intro hμ
      obtain ⟨i, -, hi, rfl⟩ := (Complex.isPrimitiveRoot_iff μ a ha.ne').mp hμ
      refine ⟨(((i : ℚ) / a : ℚ) : AddCircle (1 : ℚ)), mem_primitiveClasses_singleton.mpr ?_, ?_⟩
      · simpa using AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℚ)) ha hi
      · rw [expCircle_coe, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp a ha.ne'),
    Finset.prod_eq_multiset_prod, ← hroots, Multiset.map_map, Function.comp_def]

/-- Over `ℂ`, `∏_{x ∈ α(A)} (X - e^{2πi x}) = ∏_{a ∈ A} Φ_a`: the primitive classes of `A` are
the arguments of the roots of the cyclotomic product, with multiplicity. -/
theorem prod_X_sub_C_expCircle_primitiveClasses (A : Multiset ℕ) :
    ((primitiveClasses A).map fun x ↦ X - C (expCircle x)).prod =
      (A.map fun a ↦ cyclotomic a ℂ).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [primitiveClasses_cons, Multiset.map_add, Multiset.prod_add,
      prod_X_sub_C_expCircle_primitiveClasses_singleton, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-! ### The dictionary -/

namespace CyclotomicData

variable (D : CyclotomicData)

/-- The hypergeometric parameter pair of a cyclotomic datum: `α` is the multiset of primitive
classes of `A` and `β` that of `B`, the LMFDB's reading of the label `A…_B…`. -/
def toParameters : Parameters where
  α := primitiveClasses D.A
  β := primitiveClasses D.B
  card_eq := by rw [card_primitiveClasses, card_primitiveClasses, D.totient_sum_eq]
  disjoint := Multiset.disjoint_left.mpr fun hA hB ↦
    D.notMem_B_of_mem_A (mem_primitiveClasses.mp hA) (mem_primitiveClasses.mp hB)

@[simp]
theorem toParameters_α : D.toParameters.α = primitiveClasses D.A := (rfl)

@[simp]
theorem toParameters_β : D.toParameters.β = primitiveClasses D.B := (rfl)

@[simp]
theorem degree_toParameters : D.toParameters.degree = D.degree := by
  rw [← Parameters.card_α, toParameters_α, card_primitiveClasses, sum_map_totient_A]

@[simp]
theorem toParameters_swap : D.swap.toParameters = D.toParameters.swap := by
  ext1 <;> simp

theorem toParameters_injective : Function.Injective toParameters := fun D D' h ↦ by
  have h0 (E : CyclotomicData) : 0 ∉ E.A ∧ 0 ∉ E.B :=
    ⟨fun h ↦ (E.pos_of_mem_A h).ne' rfl, fun h ↦ (E.pos_of_mem_B h).ne' rfl⟩
  rw [Parameters.ext_iff, toParameters_α, toParameters_α, toParameters_β, toParameters_β,
    primitiveClasses_inj (h0 D).1 (h0 D').1, primitiveClasses_inj (h0 D).2 (h0 D').2] at h
  exact CyclotomicData.ext h.1 h.2

@[simp]
theorem toParameters_inj {D' : CyclotomicData} : D.toParameters = D'.toParameters ↔ D = D' :=
  toParameters_injective.eq_iff

/-- The common denominator of the parameter pair of a datum is the lcm of its indices. -/
@[simp]
theorem denominator_toParameters : D.toParameters.denominator = (D.A + D.B).lcm := by
  rw [Parameters.denominator_eq_lcm, toParameters_α, toParameters_β, ← primitiveClasses_add,
    lcm_map_addOrderOf_primitiveClasses fun h ↦ (D.pos 0 h).ne' rfl]

/-- The parameter pair of a cyclotomic datum is Galois stable. -/
@[simp]
theorem isGaloisStable_toParameters : D.toParameters.IsGaloisStable := by
  rw [Parameters.isGaloisStable_iff, denominator_toParameters]
  intro u hu
  have h (a : ℕ) (ha : a ∈ D.A + D.B) : IsCoprime u a :=
    hu.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (Multiset.dvd_lcm ha))
  exact ⟨map_zsmul_primitiveClasses fun a ha ↦ h a (Multiset.mem_add.mpr (.inl ha)),
    map_zsmul_primitiveClasses fun b hb ↦ h b (Multiset.mem_add.mpr (.inr hb))⟩

/-- The parameter pair of a cyclotomic datum is fixed by negation. -/
@[simp]
theorem neg_toParameters : -D.toParameters = D.toParameters :=
  D.isGaloisStable_toParameters.neg_eq

/-- The parameter pairs of cyclotomic data are exactly the Galois-stable pairs. -/
theorem range_toParameters :
    Set.range toParameters = {P : Parameters | P.IsGaloisStable} := by
  ext P
  refine ⟨?_, fun hP ↦ ?_⟩
  · rintro ⟨D, rfl⟩
    exact D.isGaloisStable_toParameters
  classical
  have hα (u : ℤ) (hu : IsCoprime u P.denominator) := (P.isGaloisStable_iff.mp hP u hu).1
  have hβ (u : ℤ) (hu : IsCoprime u P.denominator) := (P.isGaloisStable_iff.mp hP u hu).2
  have hN (x) (hx : x ∈ P.α + P.β) : addOrderOf x ∣ P.denominator :=
    P.addOrderOf_dvd_denominator hx
  obtain ⟨A, hA0, hA⟩ := exists_primitiveClasses_eq (s := P.α) fun x y h ↦
    count_eq_count_of_map_zsmul_eq P.denominator_pos.ne'
      (fun x hx ↦ hN x (Multiset.mem_add.mpr (.inl hx))) hα h
  obtain ⟨B, hB0, hB⟩ := exists_primitiveClasses_eq (s := P.β) fun x y h ↦
    count_eq_count_of_map_zsmul_eq P.denominator_pos.ne'
      (fun x hx ↦ hN x (Multiset.mem_add.mpr (.inr hx))) hβ h
  refine ⟨{ A, B, pos := ?_, disjoint := ?_, totient_sum_eq := ?_ }, Parameters.ext hA hB⟩
  · intro n hn
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact (Multiset.mem_add.mp hn).elim hA0 hB0
  · refine Multiset.disjoint_left.mpr fun {a} ha hb ↦ ?_
    have ha0 : 0 < a := Nat.pos_of_ne_zero (ne_of_mem_of_not_mem ha hA0)
    exact P.notMem_β_of_mem_α (hA ▸ (coe_one_div_mem_primitiveClasses ha0).mpr ha)
      (hB ▸ (coe_one_div_mem_primitiveClasses ha0).mpr hb)
  · rw [← card_primitiveClasses, ← card_primitiveClasses, hA, hB, P.card_eq]

/-- A Galois-stable parameter pair is the pair of a unique cyclotomic datum. -/
theorem existsUnique_toParameters_eq {P : Parameters} (hP : P.IsGaloisStable) :
    ∃! D : CyclotomicData, D.toParameters = P := by
  obtain ⟨D, rfl⟩ : P ∈ Set.range toParameters := by
    rw [range_toParameters]
    exact hP
  exact ⟨D, rfl, fun D' h ↦ toParameters_injective h⟩

/-- Over `ℂ`, `Φ_A` is `∏_{x ∈ α} (X - e^{2πi x})`. -/
theorem prod_X_sub_C_expCircle_toParameters_α :
    (D.toParameters.α.map fun x ↦ X - C (expCircle x)).prod = D.phiA ℂ := by
  rw [toParameters_α, phiA_def]
  exact prod_X_sub_C_expCircle_primitiveClasses D.A

/-- Over `ℂ`, `Φ_B` is `∏_{x ∈ β} (X - e^{2πi x})`. -/
theorem prod_X_sub_C_expCircle_toParameters_β :
    (D.toParameters.β.map fun x ↦ X - C (expCircle x)).prod = D.phiB ℂ := by
  rw [toParameters_β, phiB_def]
  exact prod_X_sub_C_expCircle_primitiveClasses D.B

end CyclotomicData

end TauCeti.Hypergeometric
