/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.Algebra.CyclicQuotient
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.Algebra.BigOperators.Ring.List
import TauCeti.GroupTheory.PGroup.FixedPointSum

/-!
# The `p`-power commutator subspace

Let `A` be an algebra over a commutative ring `k` of prime characteristic `p`, and let
`[A, A] = TauCeti.commutatorSubmodule k A` be the `k`-span of the commutators `a * b - b * a`.
Modulo `[A, A]` the `p`-th power map is additive:

```text
(a + b) ^ p ≡ a ^ p + b ^ p   (mod [A, A]),
```

because `(a + b) ^ p` is the sum of the `2 ^ p` products of `p` factors from `{a, b}`, a rotation
of the factors changes a product only by a commutator, and the rotations act on the products that
are not powers of `a` or of `b` in orbits of size `p`. It also maps `[A, A]` into itself, since
`(x * y - y * x) ^ p ≡ (x * y) ^ p - (y * x) ^ p`, which is a commutator.

The **`p`-power commutator subspace** `TauCeti.pPowerCommutatorSubmodule p k A` is the set `T(A)`
of `a ∈ A` with `a ^ (p ^ n) ∈ [A, A]` for some `n`. By the additivity it is a `k`-submodule; it
contains `[A, A]` and every nilpotent element. This is the subspace of Webb, Lemma 9.3.1, whose
codimension counts the simple modules of a split finite-dimensional algebra (Webb,
Proposition 9.3.3); for a group algebra `k[G]` in characteristic `p` this codimension is the
number of `p`-regular conjugacy classes (Webb, Theorem 9.3.6).

## Main definitions

* `TauCeti.pPowerCommutatorSubmodule p k A`: the elements some `p`-power power of which is a sum
  of commutators.

## Main results

* `TauCeti.add_pow_char_sub_mem_commutatorSubmodule`: `(a + b) ^ p - (a ^ p + b ^ p) ∈ [A, A]`.
* `TauCeti.pow_char_mem_commutatorSubmodule`: `[A, A]` is closed under `p`-th powers.
* `TauCeti.sum_pow_char_pow_sub_mem_commutatorSubmodule`: the `p ^ n`-th power of a finite sum is
  the sum of the `p ^ n`-th powers modulo `[A, A]`.
* `TauCeti.mem_pPowerCommutatorSubmodule_of_isNilpotent`,
  `TauCeti.commutatorSubmodule_le_pPowerCommutatorSubmodule`: `T(A)` contains the nilpotent
  elements and `[A, A]`.
* `TauCeti.map_pPowerCommutatorSubmodule`: algebra isomorphisms carry `T(A)` onto `T(B)`.
* `TauCeti.pPowerCommutatorSubmodule_eq_comap_mkₐ`: for a two-sided ideal `I` of nilpotent
  elements, `T(A)` is the preimage of `T(A / I)`.
* `TauCeti.pPowerCommutatorSubmodule_pi`: `T` of a finite product is the product of the `T`s.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge Studies in Advanced
  Mathematics 161, Cambridge University Press, 2016, Lemmas 9.3.1–9.3.2, Proposition 9.3.3.
-/

public section

namespace TauCeti

open Finset

section Words

variable {A : Type*} [Ring A]

/-- The product of the factors `a` or `b` chosen by a word `w : Fin n → Bool`, in order. -/
private def wordProd (a b : A) {n : ℕ} (w : Fin n → Bool) : A :=
  (List.ofFn fun i ↦ cond (w i) a b).prod

/-- Rotation of words, `w ↦ w ∘ finRotate n`. -/
private def rotateWords (n : ℕ) : Equiv.Perm (Fin n → Bool) :=
  (finRotate n).symm.arrowCongr (.refl _)

private theorem rotateWords_apply (n : ℕ) (w : Fin n → Bool) :
    rotateWords n w = w ∘ finRotate n := by
  ext i
  rw [rotateWords, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.id_comp]

/-- Rotation of words of length `n + 2` has order dividing `n + 2`. -/
private theorem rotateWords_pow_self (n : ℕ) : rotateWords (n + 2) ^ (n + 2) = 1 := by
  have hpow : ∀ (m : ℕ) w, (rotateWords (n + 2) ^ m) w = w ∘ ⇑(finRotate (n + 2) ^ m) := by
    intro m
    induction m with
    | zero => intro w; rw [pow_zero, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.coe_one,
        Function.comp_id]
    | succ m ih =>
      intro w
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ', rotateWords_apply, Equiv.Perm.coe_mul,
        Function.comp_assoc]
  have hrot : finRotate (n + 2) ^ (n + 2) = 1 := by
    have h := (isCycle_finRotate (n := n)).orderOf
    rw [support_finRotate, card_univ, Fintype.card_fin] at h
    have h1 := pow_orderOf_eq_one (finRotate (n + 2))
    rwa [h] at h1
  ext w : 1
  rw [hpow, hrot, Equiv.Perm.coe_one, Function.comp_id, Equiv.Perm.one_apply]

/-- The words fixed by rotation are the two constant words. -/
private theorem filter_rotateWords_eq (n : ℕ) :
    univ.filter (fun w ↦ rotateWords (n + 2) w = w) = {fun _ ↦ true, fun _ ↦ false} := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, rotateWords_apply]
  constructor
  · intro h
    have hw : ∀ i, w i = w 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        simpa [← ih, Fin.coeSucc_eq_succ] using congrFun h i.castSucc
    cases h0 : w 0
    · exact Or.inr (funext fun i ↦ (hw i).trans h0)
    · exact Or.inl (funext fun i ↦ (hw i).trans h0)
  · rintro (rfl | rfl) <;> rfl

/-- Rotating a word moves its first factor to the end. -/
private theorem exists_wordProd_rotateWords (a b : A) {n : ℕ} (w : Fin (n + 2) → Bool) :
    ∃ x y : A, wordProd a b (rotateWords (n + 2) w) = y * x ∧ wordProd a b w = x * y := by
  refine ⟨cond (w 0) a b, (List.ofFn fun i : Fin (n + 1) ↦ cond (w i.succ) a b).prod, ?_, ?_⟩
  · rw [rotateWords_apply, wordProd, List.ofFn_succ', List.prod_concat]
    simp only [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one]
  · rw [wordProd, List.ofFn_succ, List.prod_cons]

end Words

variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [CommRing k] [CharP k p]
variable {A : Type*} [Ring A] [Algebra k A]

include hp in
/-- **The `p`-th power map is additive modulo commutators**: in characteristic `p`,
`(a + b) ^ p - (a ^ p + b ^ p)` is a sum of commutators. -/
theorem add_pow_char_sub_mem_commutatorSubmodule (a b : A) :
    (a + b) ^ p - (a ^ p + b ^ p) ∈ commutatorSubmodule k A := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  set C := commutatorSubmodule k A
  -- A rotation changes a word only by a commutator.
  have hf : ∀ w, C.mkQ (wordProd a b (rotateWords (n + 2) w)) = C.mkQ (wordProd a b w) := by
    intro w
    obtain ⟨x, y, h1, h2⟩ := exists_wordProd_rotateWords a b w
    rw [h1, h2, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact mul_sub_mul_mem_commutatorSubmodule k A y x
  have hM : ∀ m : A ⧸ C, (n + 2) • m = 0 := by
    intro m
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  -- Only the two constant words survive modulo `n + 2`.
  have hpow : (a + b) ^ (n + 2) = ∑ w : Fin (n + 2) → Bool, wordProd a b w := by
    simpa [wordProd] using sum_pow_eq_sum_prod_ofFn (fun x : Bool ↦ cond x a b) (n + 2)
  rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hpow, map_sum,
    Equiv.Perm.sum_eq_sum_filter_apply_eq_self_of_pow_eq_one (n := 1) _
      (by rw [pow_one]; exact rotateWords_pow_self n) hM _ hf,
    filter_rotateWords_eq, sum_pair (fun h ↦ Bool.noConfusion (congrFun h 0)), map_add]
  simp only [wordProd, Bool.cond_true, Bool.cond_false, List.ofFn_const, List.prod_replicate]

include hp in
private theorem neg_one_pow_char_of_algebra {B : Type*} [Ring B] [Algebra k B] :
    (-1 : B) ^ p = -1 := by
  have h := congrArg (algebraMap k B) (neg_one_pow_char k p)
  simpa using h

include hp in
/-- In characteristic `p`, the commutator submodule is closed under `p`-th powers. -/
theorem pow_char_mem_commutatorSubmodule {c : A} (hc : c ∈ commutatorSubmodule k A) :
    c ^ p ∈ commutatorSubmodule k A := by
  set C := commutatorSubmodule k A
  have hadd : ∀ x y : A, x ^ p ∈ C → y ^ p ∈ C → (x + y) ^ p ∈ C := fun x y hx hy ↦ by
    simpa using add_mem (add_pow_char_sub_mem_commutatorSubmodule p k x y) (add_mem hx hy)
  induction hc using commutatorSubmodule_induction with
  | mem x y =>
    -- `(x * y - y * x) ^ p ≡ (x * y) ^ p - (y * x) ^ p`, and the latter is the commutator of `x`
    -- and `y * (x * y) ^ (p - 1)`.
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
    have hyx : (y * x) ^ p = y * (x * y) ^ m * x := by
      have hs : SemiconjBy y (x * y) (y * x) := by simp [SemiconjBy, mul_assoc]
      rw [hm, pow_succ, ← mul_assoc, ← (hs.pow_right m).eq]
    have hxy : (x * y) ^ p = x * (y * (x * y) ^ m) := by rw [hm, pow_succ', mul_assoc]
    have h1 := add_pow_char_sub_mem_commutatorSubmodule p k (x * y) (-(y * x))
    rw [neg_pow, neg_one_pow_char_of_algebra p k (B := A), neg_one_mul, ← sub_eq_add_neg,
      ← sub_eq_add_neg, hxy, hyx] at h1
    have h2 := mul_sub_mul_mem_commutatorSubmodule k A x (y * (x * y) ^ m)
    simpa using add_mem h1 h2
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul r x _ hx => rw [smul_pow]; exact C.smul_mem _ hx

include hp in
/-- The `p`-th power map is well defined modulo commutators. -/
theorem pow_char_sub_pow_char_mem_commutatorSubmodule {x y : A}
    (h : x - y ∈ commutatorSubmodule k A) :
    x ^ p - y ^ p ∈ commutatorSubmodule k A := by
  have h1 := add_pow_char_sub_mem_commutatorSubmodule p k y (x - y)
  have h2 := pow_char_mem_commutatorSubmodule p k h
  rw [add_sub_cancel] at h1
  simpa [sub_add_eq_sub_sub] using add_mem h1 h2

include hp in
/-- The `p ^ n`-th power map is well defined modulo commutators. -/
theorem pow_char_pow_sub_pow_char_pow_mem_commutatorSubmodule {x y : A}
    (h : x - y ∈ commutatorSubmodule k A) (n : ℕ) :
    x ^ p ^ n - y ^ p ^ n ∈ commutatorSubmodule k A := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, pow_mul, pow_mul]
    exact pow_char_sub_pow_char_mem_commutatorSubmodule p k ih

include hp in
/-- `[A, A]` is closed under `p ^ n`-th powers. -/
theorem pow_char_pow_mem_commutatorSubmodule {c : A} (hc : c ∈ commutatorSubmodule k A)
    (n : ℕ) : c ^ p ^ n ∈ commutatorSubmodule k A := by
  simpa [zero_pow (pow_ne_zero n hp.out.ne_zero)] using
    pow_char_pow_sub_pow_char_pow_mem_commutatorSubmodule p k (x := c) (y := (0 : A))
      (by simpa using hc) n

include hp in
/-- The `p ^ n`-th power map is additive modulo commutators. -/
theorem add_pow_char_pow_sub_mem_commutatorSubmodule (a b : A) (n : ℕ) :
    (a + b) ^ p ^ n - (a ^ p ^ n + b ^ p ^ n) ∈ commutatorSubmodule k A := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := pow_char_sub_pow_char_mem_commutatorSubmodule p k ih
    have h2 := add_pow_char_sub_mem_commutatorSubmodule p k (a ^ p ^ n) (b ^ p ^ n)
    rw [pow_succ, pow_mul, pow_mul, pow_mul]
    simpa using add_mem h1 h2

include hp in
/-- The `p ^ n`-th power of a finite sum is the sum of the `p ^ n`-th powers, modulo
commutators. -/
theorem sum_pow_char_pow_sub_mem_commutatorSubmodule {ι : Type*} (s : Finset ι) (f : ι → A)
    (n : ℕ) : (∑ i ∈ s, f i) ^ p ^ n - ∑ i ∈ s, f i ^ p ^ n ∈ commutatorSubmodule k A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow (pow_ne_zero n hp.out.ne_zero)]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    have h := add_pow_char_pow_sub_mem_commutatorSubmodule p k (f i) (∑ j ∈ s, f j) n
    convert add_mem h ih using 1
    abel

include hp in
/-- If `a ^ p ^ m` is a sum of commutators, so is `a ^ p ^ n` for every `n ≥ m`. -/
theorem pow_char_pow_mem_commutatorSubmodule_of_le {a : A} {m n : ℕ} (hmn : m ≤ n)
    (h : a ^ p ^ m ∈ commutatorSubmodule k A) : a ^ p ^ n ∈ commutatorSubmodule k A := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, pow_mul]
  exact pow_char_pow_mem_commutatorSubmodule p k h j

variable (A) in
/-- The **`p`-power commutator subspace** `T(A)` of an algebra `A` over a commutative ring `k` of
characteristic `p`: the elements `a` such that `a ^ (p ^ n)` is a sum of commutators for some `n`.
It is a `k`-submodule because the `p`-th power map is additive modulo commutators. -/
def pPowerCommutatorSubmodule : Submodule k A where
  carrier := {a | ∃ n : ℕ, a ^ p ^ n ∈ commutatorSubmodule k A}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    have h := add_pow_char_pow_sub_mem_commutatorSubmodule p k a b (max m n)
    have ha := pow_char_pow_mem_commutatorSubmodule_of_le p k (le_max_left m n) hm
    have hb := pow_char_pow_mem_commutatorSubmodule_of_le p k (le_max_right m n) hn
    simpa using add_mem h (add_mem ha hb)
  smul_mem' := by
    rintro r a ⟨n, hn⟩
    exact ⟨n, by rw [smul_pow]; exact Submodule.smul_mem _ _ hn⟩

/-- Membership in the `p`-power commutator subspace. -/
@[simp]
theorem mem_pPowerCommutatorSubmodule {a : A} :
    a ∈ pPowerCommutatorSubmodule p k A ↔ ∃ n : ℕ, a ^ p ^ n ∈ commutatorSubmodule k A :=
  Iff.rfl

/-- Every sum of commutators lies in the `p`-power commutator subspace. -/
theorem commutatorSubmodule_le_pPowerCommutatorSubmodule :
    commutatorSubmodule k A ≤ pPowerCommutatorSubmodule p k A :=
  fun a ha ↦ ⟨0, by simpa using ha⟩

/-- Every nilpotent element lies in the `p`-power commutator subspace. -/
theorem mem_pPowerCommutatorSubmodule_of_isNilpotent {a : A} (ha : IsNilpotent a) :
    a ∈ pPowerCommutatorSubmodule p k A := by
  obtain ⟨m, hm⟩ := ha
  refine ⟨m, ?_⟩
  rw [pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hm]
  exact zero_mem _

section Map

variable {B : Type*} [Ring B] [Algebra k B]

/-- An algebra isomorphism preserves the `p`-power commutator subspace. -/
theorem algEquiv_apply_mem_pPowerCommutatorSubmodule_iff (e : A ≃ₐ[k] B) {a : A} :
    e a ∈ pPowerCommutatorSubmodule p k B ↔ a ∈ pPowerCommutatorSubmodule p k A := by
  simp only [mem_pPowerCommutatorSubmodule, ← map_pow, algEquiv_apply_mem_commutatorSubmodule_iff]

/-- An algebra isomorphism carries the `p`-power commutator subspace onto that of its target. -/
theorem map_pPowerCommutatorSubmodule (e : A ≃ₐ[k] B) :
    (pPowerCommutatorSubmodule p k A).map (e.toLinearEquiv : A →ₗ[k] B) =
      pPowerCommutatorSubmodule p k B := by
  ext b
  rw [Submodule.mem_map_equiv, ← algEquiv_apply_mem_pPowerCommutatorSubmodule_iff p k e]
  simp

/-- An algebra isomorphism induces an isomorphism of the quotients by the `p`-power commutator
subspaces. -/
noncomputable def quotientPPowerCommutatorEquiv (e : A ≃ₐ[k] B) :
    (A ⧸ pPowerCommutatorSubmodule p k A) ≃ₗ[k] B ⧸ pPowerCommutatorSubmodule p k B :=
  Submodule.Quotient.equiv _ _ e.toLinearEquiv (map_pPowerCommutatorSubmodule p k e)

@[simp]
theorem quotientPPowerCommutatorEquiv_mk (e : A ≃ₐ[k] B) (a : A) :
    quotientPPowerCommutatorEquiv p k e (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (e a) := by
  simp [quotientPPowerCommutatorEquiv]

end Map

section NilIdeal

variable (I : Ideal A) [I.IsTwoSided]

include hp in
/-- For a two-sided ideal `I` of nilpotent elements, `T(A)` is the preimage of `T(A / I)`
(Webb, Lemma 9.3.2 for the radical). -/
theorem pPowerCommutatorSubmodule_eq_comap_mkₐ (hI : ∀ x ∈ I, IsNilpotent x) :
    pPowerCommutatorSubmodule p k A =
      (pPowerCommutatorSubmodule p k (A ⧸ I)).comap (Ideal.Quotient.mkₐ k I).toLinearMap := by
  ext a
  simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, mem_pPowerCommutatorSubmodule]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using map_mem_commutatorSubmodule (Ideal.Quotient.mkₐ k I) hn⟩
  · rintro ⟨n, hn⟩
    rw [← map_pow] at hn
    obtain ⟨c, hc, hca⟩ := commutatorSubmodule_quotient_le_map k I hn
    have hj : a ^ p ^ n - c ∈ I := by
      rw [← Ideal.Quotient.eq]
      simpa using hca.symm
    obtain ⟨N, hN⟩ := hI _ hj
    refine ⟨n + N, ?_⟩
    have h := add_pow_char_pow_sub_mem_commutatorSubmodule p k c (a ^ p ^ n - c) N
    rw [add_sub_cancel, pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hN, add_zero] at h
    rw [pow_add, pow_mul]
    simpa using add_mem h (pow_char_pow_mem_commutatorSubmodule p k hc N)

/-- For a two-sided ideal `I` of nilpotent elements, `A / T(A)` is isomorphic to
`(A / I) / T(A / I)`. -/
noncomputable def quotientPPowerCommutatorEquivOfIsNilpotent (hI : ∀ x ∈ I, IsNilpotent x) :
    (A ⧸ pPowerCommutatorSubmodule p k A) ≃ₗ[k]
      (A ⧸ I) ⧸ pPowerCommutatorSubmodule p k (A ⧸ I) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      exact pPowerCommutatorSubmodule_eq_comap_mkₐ p k I hI)).trans
    (LinearMap.quotKerEquivOfSurjective
      ((pPowerCommutatorSubmodule p k (A ⧸ I)).mkQ ∘ₗ (Ideal.Quotient.mkₐ k I).toLinearMap)
      ((Submodule.mkQ_surjective _).comp (Ideal.Quotient.mkₐ_surjective k I)))

@[simp]
theorem quotientPPowerCommutatorEquivOfIsNilpotent_mk (hI : ∀ x ∈ I, IsNilpotent x) (a : A) :
    quotientPPowerCommutatorEquivOfIsNilpotent p k I hI (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (Ideal.Quotient.mk I a) := by
  simp [quotientPPowerCommutatorEquivOfIsNilpotent]

end NilIdeal

section Pi

variable {ι : Type*} [Finite ι] (B : ι → Type*) [∀ i, Ring (B i)]
  [∀ i, Algebra k (B i)]

include hp in
/-- The `p`-power commutator subspace of a finite product of algebras is the product of the
`p`-power commutator subspaces. -/
theorem pPowerCommutatorSubmodule_pi :
    pPowerCommutatorSubmodule p k (Π i, B i) =
      Submodule.pi Set.univ fun i ↦ pPowerCommutatorSubmodule p k (B i) := by
  have := Fintype.ofFinite ι
  ext v
  simp only [mem_pPowerCommutatorSubmodule, commutatorSubmodule_pi, Submodule.mem_pi,
    Set.mem_univ, true_imp_iff, Pi.pow_apply]
  constructor
  · rintro ⟨n, hn⟩ i
    exact ⟨n, hn i⟩
  · intro h
    choose n hn using h
    exact ⟨univ.sup n, fun i ↦
      pow_char_pow_mem_commutatorSubmodule_of_le p k (le_sup (mem_univ i)) (hn i)⟩

end Pi

end TauCeti
