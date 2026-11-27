/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.Algebra.CyclicQuotient
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Fin

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
* `TauCeti.sum_pow_char_pow_sub_mem_commutatorSubmodule`: the same for `p ^ n`-th powers of finite
  sums.
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

section Orbit

variable {p : ℕ} [hp : Fact p.Prime] {H X M : Type*} [Group H] [MulAction H X] [Fintype X]
  [AddCommGroup M]

/-- One fibre of an invariant function under a `p`-group action has as many points, modulo `p`,
as fixed points. -/
private theorem card_filter_nsmul_eq_of_isPGroup [DecidablePred (· ∈ MulAction.fixedPoints H X)]
    (hH : IsPGroup p H) (hM : ∀ m : M, p • m = 0) (f : X → M) (hf : ∀ (g : H) x, f (g • x) = f x)
    (m : M) [DecidablePred (f · = m)] :
    (univ.filter (f · = m)).card • m =
      ((univ.filter (· ∈ MulAction.fixedPoints H X)).filter (f · = m)).card • m := by
  let S : SubMulAction H X :=
    { carrier := {x | f x = m}
      smul_mem' := fun g x hx ↦ by
        change f (g • x) = m
        rw [hf g x]
        exact hx }
  have hcong := hH.card_modEq_card_fixedPoints S
  have h1 : Nat.card S = (univ.filter (f · = m)).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  have h2 : Nat.card (MulAction.fixedPoints H S) =
      ((univ.filter (· ∈ MulAction.fixedPoints H X)).filter (f · = m)).card := by
    rw [filter_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun y ↦ ⟨y.val.val, fun g ↦ congrArg Subtype.val (y.prop g), y.val.prop⟩
        invFun := fun y ↦ ⟨⟨y.val, y.prop.2⟩, fun g ↦ Subtype.ext (y.prop.1 g)⟩
        left_inv := fun y ↦ rfl
        right_inv := fun y ↦ rfl }
  rw [h1, h2] at hcong
  rw [← Nat.mod_add_div (univ.filter (f · = m)).card p,
    ← Nat.mod_add_div ((univ.filter (· ∈ MulAction.fixedPoints H X)).filter (f · = m)).card p,
    add_nsmul, add_nsmul, mul_nsmul', mul_nsmul', hM, hM, hcong]

/-- Let a `p`-group act on a finite type and let `f` be an invariant function into an additive
group killed by `p`. Then the sum of `f` equals its sum over the fixed points: the other points
fall into orbits whose size is a positive power of `p`. -/
theorem sum_eq_sum_fixedPoints_of_isPGroup [DecidablePred (· ∈ MulAction.fixedPoints H X)]
    (hH : IsPGroup p H) (hM : ∀ m : M, p • m = 0) (f : X → M)
    (hf : ∀ (g : H) x, f (g • x) = f x) :
    ∑ x, f x = ∑ x ∈ univ.filter (· ∈ MulAction.fixedPoints H X), f x := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := f) (t := univ.image f) (fun x _ ↦ mem_image_of_mem f
      (mem_univ x)),
    ← sum_fiberwise_of_maps_to (g := f) (t := univ.image f) (fun x _ ↦ mem_image_of_mem f
      (mem_univ x))]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [sum_congr rfl fun x hx ↦ (mem_filter.1 hx).2, sum_const,
    sum_congr rfl fun x hx ↦ (mem_filter.1 hx).2, sum_const,
    card_filter_nsmul_eq_of_isPGroup hH hM f hf m]

omit [MulAction H X] in
/-- Let `σ` be a permutation of a finite type with `σ ^ p = 1`, for a prime `p`, and let `f` be a
`σ`-invariant function into an additive group killed by `p`. Then the sum of `f` equals its sum
over the fixed points of `σ`: the other points fall into `σ`-orbits of size `p`. -/
theorem sum_eq_sum_filter_apply_eq_self_of_pow_eq_one [DecidableEq X] (σ : Equiv.Perm X)
    (hσ : σ ^ p = 1) (hM : ∀ m : M, p • m = 0) (f : X → M) (hf : ∀ x, f (σ x) = f x) :
    ∑ x, f x = ∑ x ∈ univ.filter (fun x ↦ σ x = x), f x := by
  classical
  -- The cyclic group `⟨σ⟩` is a `p`-group whose fixed points are those of `σ`.
  have hH : IsPGroup p (Subgroup.zpowers σ) := fun g ↦ by
    obtain ⟨g, z, rfl⟩ := g
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have hfz : ∀ (z : ℤ) x, f ((σ ^ z) x) = f x := by
    intro z
    induction z using Int.induction_on with
    | zero => simp
    | succ n ih => intro x; rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hf]
    | pred n ih =>
      intro x
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, ← hf (σ⁻¹ x)]
      simp
  have hfix : ∀ x, x ∈ MulAction.fixedPoints (Subgroup.zpowers σ) X ↔ σ x = x := by
    refine fun x ↦ ⟨fun h ↦ h ⟨σ, Subgroup.mem_zpowers σ⟩, fun h ↦ ?_⟩
    rintro ⟨g, z, rfl⟩
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h z
  rw [sum_eq_sum_fixedPoints_of_isPGroup hH hM f (by rintro ⟨g, z, rfl⟩ x; exact hfz z x)]
  exact sum_congr (filter_congr fun x _ ↦ hfix x) fun _ _ ↦ rfl

end Orbit

section Words

variable {A : Type*} [Ring A]

/-- The product of the factors `a` or `b` chosen by a word `w : Fin n → Bool`, in order. -/
private def wordProd (a b : A) {n : ℕ} (w : Fin n → Bool) : A :=
  (List.ofFn fun i ↦ cond (w i) a b).prod

/-- **Noncommutative binomial expansion**: `(a + b) ^ n` is the sum of the products of `n` factors
from `{a, b}`. -/
private theorem add_pow_eq_sum_wordProd (a b : A) (n : ℕ) :
    (a + b) ^ n = ∑ w : Fin n → Bool, wordProd a b w := by
  induction n with
  | zero => simp [wordProd]
  | succ n ih =>
    rw [pow_succ', ih, ← (Fin.consEquiv fun _ ↦ Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool, add_mul, Finset.mul_sum, Finset.mul_sum]
    simp [wordProd, Fin.consEquiv, List.ofFn_succ]

/-- Rotation of words, `w ↦ w ∘ finRotate n`. -/
private def rotateWords (n : ℕ) : Equiv.Perm (Fin n → Bool) :=
  (finRotate n).symm.arrowCongr (.refl _)

private theorem finRotate_castSucc {n : ℕ} (i : Fin (n + 1)) :
    finRotate (n + 2) i.castSucc = i.succ :=
  Fin.ext <| by
    rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i), Fin.val_castSucc, Fin.val_succ]

/-- Rotation of words of length `n + 2` has order dividing `n + 2`. -/
private theorem rotateWords_pow_self (n : ℕ) : rotateWords (n + 2) ^ (n + 2) = 1 := by
  have hpow : ∀ (m : ℕ) w, (rotateWords (n + 2) ^ m) w = w ∘ ⇑(finRotate (n + 2) ^ m) := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ']
      rfl
  have hrot : finRotate (n + 2) ^ (n + 2) = 1 := by
    have h := (isCycle_finRotate (n := n)).orderOf
    rw [support_finRotate, card_univ, Fintype.card_fin] at h
    have h1 := pow_orderOf_eq_one (finRotate (n + 2))
    rwa [h] at h1
  ext w i
  rw [hpow, hrot]
  rfl

/-- The words fixed by rotation are the two constant words. -/
private theorem filter_rotateWords_eq (n : ℕ) :
    univ.filter (fun w ↦ rotateWords (n + 2) w = w) = {fun _ ↦ true, fun _ ↦ false} := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro h
    have hw : ∀ i, w i = w 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        rw [← ih, ← finRotate_castSucc]
        exact congrFun h i.castSucc
    cases h0 : w 0
    · exact Or.inr (funext fun i ↦ (hw i).trans h0)
    · exact Or.inl (funext fun i ↦ (hw i).trans h0)
  · rintro (rfl | rfl) <;> rfl

/-- Rotating a word moves its first factor to the end. -/
private theorem exists_wordProd_rotateWords (a b : A) {n : ℕ} (w : Fin (n + 2) → Bool) :
    ∃ x y : A, wordProd a b (rotateWords (n + 2) w) = y * x ∧ wordProd a b w = x * y := by
  refine ⟨cond (w 0) a b, (List.ofFn fun i : Fin (n + 1) ↦ cond (w i.succ) a b).prod, ?_, ?_⟩
  · have hσw : rotateWords (n + 2) w = w ∘ ⇑(finRotate (n + 2)) := rfl
    rw [hσw, wordProd, List.ofFn_succ', List.prod_concat]
    simp only [Function.comp_apply, finRotate_castSucc, finRotate_last]
  · rw [wordProd, List.ofFn_succ, List.prod_cons]

end Words

variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [CommRing k] [CharP k p]
variable {A : Type*} [Ring A] [Algebra k A]

omit hp in
private theorem nsmul_char_eq_zero {B : Type*} [Ring B] [Algebra k B] (x : B) : p • x = 0 := by
  rw [nsmul_eq_mul, ← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero, zero_mul]

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
    rintro ⟨x⟩
    change (n + 2) • C.mkQ x = 0
    rw [← map_nsmul, nsmul_char_eq_zero (n + 2) k x, map_zero]
  -- Only the two constant words survive modulo `n + 2`.
  rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply,
    add_pow_eq_sum_wordProd, map_sum,
    sum_eq_sum_filter_apply_eq_self_of_pow_eq_one _ (rotateWords_pow_self n) hM _ hf,
    filter_rotateWords_eq, sum_pair (fun h ↦ Bool.noConfusion (congrFun h 0)), map_add]
  simp only [wordProd, Bool.cond_true, Bool.cond_false, List.ofFn_const, List.prod_replicate]

include hp in
private theorem neg_one_pow_char_of_algebra {B : Type*} [Ring B] [Algebra k B] :
    (-1 : B) ^ p = -1 := by
  have h := congrArg (algebraMap k B) (neg_one_pow_char k p)
  simpa using h

include hp in
/-- In characteristic `p`, the commutator submodule is closed under `p`-th powers:
`(x * y - y * x) ^ p ≡ (x * y) ^ p - (y * x) ^ p`, and the latter is the commutator of `x` and
`y * (x * y) ^ (p - 1)`. -/
theorem pow_char_mem_commutatorSubmodule {c : A} (hc : c ∈ commutatorSubmodule k A) :
    c ^ p ∈ commutatorSubmodule k A := by
  set C := commutatorSubmodule k A
  have hadd : ∀ x y : A, x ^ p ∈ C → y ^ p ∈ C → (x + y) ^ p ∈ C := fun x y hx hy ↦ by
    simpa using add_mem (add_pow_char_sub_mem_commutatorSubmodule p k x y) (add_mem hx hy)
  induction hc using commutatorSubmodule_induction with
  | mem x y =>
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

/-- An algebra isomorphism preserves the commutator submodule. -/
theorem algEquiv_apply_mem_commutatorSubmodule_iff (e : A ≃ₐ[k] B) {a : A} :
    e a ∈ commutatorSubmodule k B ↔ a ∈ commutatorSubmodule k A :=
  ⟨fun h ↦ by simpa using map_mem_commutatorSubmodule e.symm h, map_mem_commutatorSubmodule e⟩

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

end Map

section NilIdeal

variable (I : Ideal A) [I.IsTwoSided]

/-- The commutators of a quotient algebra are the images of the commutators. -/
theorem commutatorSubmodule_quotient_le_map :
    commutatorSubmodule k (A ⧸ I) ≤
      (commutatorSubmodule k A).map (Ideal.Quotient.mkₐ k I).toLinearMap := by
  refine commutatorSubmodule_le_iff.2 fun x y ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I y
  exact ⟨x * y - y * x, mul_sub_mul_mem_commutatorSubmodule k A x y, by simp⟩

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

end NilIdeal

section Pi

variable {ι : Type*} [Finite ι] (B : ι → Type*) [∀ i, Ring (B i)]
  [∀ i, Algebra k (B i)]

/-- The commutators of a finite product of algebras are the families of commutators. -/
theorem commutatorSubmodule_pi :
    commutatorSubmodule k (Π i, B i) =
      Submodule.pi Set.univ fun i ↦ commutatorSubmodule k (B i) := by
  classical
  have := Fintype.ofFinite ι
  refine le_antisymm (commutatorSubmodule_le_iff.2 fun x y i _ ↦ ?_) fun v hv ↦ ?_
  · exact mul_sub_mul_mem_commutatorSubmodule k (B i) (x i) (y i)
  · rw [← Finset.univ_sum_single v]
    refine sum_mem fun i _ ↦ ?_
    have hle : commutatorSubmodule k (B i) ≤
        (commutatorSubmodule k (Π i, B i)).comap (LinearMap.single k B i) :=
      commutatorSubmodule_le_iff.2 fun x y ↦ by
        simp [Pi.single_sub, Pi.single_mul]
    exact hle (hv i (Set.mem_univ i))

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
