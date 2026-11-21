/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.LinearAlgebra.Quotient.Map
import TauCeti.RingTheory.QuotSMulTop

/-!
# The monomial property of regular sequences

Let `x₁, …, x_d` be a weakly regular sequence on a module `M` over a commutative ring `R`, with no
finiteness or Noetherian hypothesis. For every `n`,

```text
(x₁ ⋯ x_d)ⁿ m ∈ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹) M   implies   m ∈ (x₁, …, x_d) M.
```

So if the sequence is regular, `(x₁ ⋯ x_d)ⁿ M ⊄ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹) M`. Over a ring with a regular
sequence this says `(x₁ ⋯ x_d)ⁿ ∉ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹)`. Hochster's monomial conjecture asserts the
same for every system of parameters of a Noetherian local ring. It follows from the existence of a
big Cohen–Macaulay algebra, on which the system of parameters becomes regular.

Since regular sequences on modules that are not finite cannot be permuted, the proof only ever
peels off the first element. Two facts about weakly regular sequences, valid for arbitrary
modules, go into it.

* Weak regularity is closed under extensions
  (`RingTheory.Sequence.isWeaklyRegular_of_exact`): in a short exact sequence
  `0 → M → M' → M'' → 0`, a sequence weakly regular on `M` and on `M''` is weakly regular on `M'`.
* If `x :: ys` is weakly regular on `M`, then so is `xᵏ :: ys` for `k ≥ 1`
  (`RingTheory.Sequence.IsWeaklyRegular.pow_cons`). This follows from the previous point by
  induction on `k`, through the short exact sequences
  `0 → M ⧸ x M → M ⧸ xᵏ⁺¹ M → M ⧸ xᵏ M → 0` whose first map is multiplication by `xᵏ`
  (`QuotSMulTop.mulPow`).

For `x :: ys` and the product `P` of `ys`, a relation `xⁿ Pⁿ m ∈ (xⁿ⁺¹, ysⁿ⁺¹) M` is first read in
`M ⧸ xⁿ⁺¹ M`, on which `ys` is weakly regular, and induction gives `xⁿ m ∈ (xⁿ⁺¹, ys) M`. The
short exact sequence above with `k = n`, reduced modulo `ys`, stays exact on the left because `ys`
is weakly regular on `M ⧸ xⁿ M`, and this gives `m ∈ (x, ys) M`.

## Main results

* `RingTheory.Sequence.isWeaklyRegular_of_exact`: weak regularity is closed under extensions.
* `RingTheory.Sequence.IsWeaklyRegular.pow_cons`: raising the first element of a weakly regular
  sequence to a positive power keeps it weakly regular.
* `RingTheory.Sequence.IsWeaklyRegular.mem_ofList_smul_top_of_prod_pow_smul_mem`: the monomial
  property of a weakly regular sequence.
* `RingTheory.Sequence.IsRegular.not_prod_pow_smul_top_le`: `(x₁ ⋯ x_d)ⁿ M ⊄ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹) M`
  for a regular sequence on `M`.
* `RingTheory.Sequence.IsRegular.algebraMap_prod_pow_notMem_map_ofList` and
  `RingTheory.Sequence.IsRegular.prod_pow_notMem_ofList`: `(x₁ ⋯ x_d)ⁿ ∉ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹) C` for a
  regular sequence on an `R`-algebra `C`, in particular on `R` itself.

## References

* M. Hochster, *Contracted ideals from integral extensions of regular rings*, Nagoya Math. J. 51
  (1973), for the monomial conjecture.
* H. Matsumura, *Commutative Ring Theory*, Theorem 16.1, for powers of regular sequences.
-/

public section

open Function Submodule Pointwise

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

/-- **Weak regularity is closed under extensions.** In a short exact sequence
`0 → M → M' → M'' → 0`, a sequence that is weakly regular on `M` and on `M''` is weakly regular on
`M'`. -/
theorem isWeaklyRegular_of_exact {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''} (hf : Injective f)
    (hfg : Exact f g) (hg : Surjective g) {rs : List R} (h : IsWeaklyRegular M rs)
    (h'' : IsWeaklyRegular M'' rs) : IsWeaklyRegular M' rs := by
  induction rs generalizing M M' M'' with
  | nil => exact IsWeaklyRegular.nil R M'
  | cons r rs ih =>
    rw [isWeaklyRegular_cons_iff] at h h'' ⊢
    refine ⟨isSMulRegular_of_range_eq_ker hf hfg.linearMap_ker_eq.symm h.1 h''.1, ?_⟩
    -- Reducing modulo `r` keeps the sequence short exact, since `r` is regular on `M''`.
    have hex := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
      (f₁ := (0 : PUnit.{1} →ₗ[R] M)) ((LinearMap.exact_zero_iff_injective _ f).2 hf) hfg h''.1
    rw [LinearMap.map_zero, LinearMap.exact_zero_iff_injective] at hex
    exact ih hex (QuotSMulTop.map_exact r hfg hg) (QuotSMulTop.map_surjective r hg) h.2 h''.2

/-- Raising the first element of a weakly regular sequence to a positive power keeps it weakly
regular: if `x :: ys` is weakly regular on `M`, so is `xᵏ :: ys` for every `k ≠ 0`. This is the
first-element case of Matsumura, Theorem 16.1; no finiteness of `M` is needed. -/
theorem IsWeaklyRegular.pow_cons {x : R} {ys : List R} (h : IsWeaklyRegular M (x :: ys)) {k : ℕ}
    (hk : k ≠ 0) : IsWeaklyRegular M (x ^ k :: ys) := by
  rw [isWeaklyRegular_cons_iff] at h ⊢
  refine ⟨h.1.pow k, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  induction j with
  | zero =>
    rw [zero_add, pow_one]
    exact h.2
  | succ j ih =>
    exact isWeaklyRegular_of_exact (QuotSMulTop.mulPow_injective h.1 (j + 1))
      (QuotSMulTop.exact_mulPow x (j + 1)) (factor_surjective _) h.2 (ih (Nat.succ_ne_zero j))

/-- The colon step of the monomial property: if `x` is `M`-regular and `ys` is weakly regular on
`M ⧸ xᵏ M`, then `xᵏ m ∈ (xᵏ⁺¹, ys) M` implies `m ∈ (x, ys) M`. -/
private theorem mem_sup_of_pow_smul_mem {x : R} (hx : IsSMulRegular M x) {ys : List R} {k : ℕ}
    (hys : IsWeaklyRegular (QuotSMulTop (x ^ k) M) ys) {m : M}
    (hm : x ^ k • m ∈ x ^ (k + 1) • (⊤ : Submodule R M) ⊔ Ideal.ofList ys • ⊤) :
    m ∈ x • ⊤ ⊔ Ideal.ofList ys • (⊤ : Submodule R M) := by
  -- Reduce `0 → M ⧸ x M → M ⧸ xᵏ⁺¹ M → M ⧸ xᵏ M` modulo `ys`; it stays exact on the left.
  have hex := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    (f₁ := (0 : PUnit.{1} →ₗ[R] QuotSMulTop x M))
    ((LinearMap.exact_zero_iff_injective _ _).2 (QuotSMulTop.mulPow_injective hx k))
    (QuotSMulTop.exact_mulPow x k) (factor_surjective _) hys
  rw [mapQ_zero, LinearMap.exact_zero_iff_injective] at hex
  rw [← Submodule.Quotient.mk_mem_smul_top_iff, ← Submodule.Quotient.mk_eq_zero]
  refine (injective_iff_map_eq_zero _).1 hex _ ?_
  rw [mapQ_apply, QuotSMulTop.mulPow_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.Quotient.mk_mem_smul_top_iff]
  exact hm

/-- **The monomial property of weakly regular sequences.** If `x₁, …, x_d` is weakly regular on an
`R`-module `M` and `(x₁ ⋯ x_d)ⁿ m ∈ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹) M`, then `m ∈ (x₁, …, x_d) M`. No finiteness
or Noetherian hypothesis is needed. -/
theorem IsWeaklyRegular.mem_ofList_smul_top_of_prod_pow_smul_mem {xs : List R}
    (h : IsWeaklyRegular M xs) (n : ℕ) {m : M}
    (hm : xs.prod ^ n • m ∈ Ideal.ofList (xs.map (· ^ (n + 1))) • (⊤ : Submodule R M)) :
    m ∈ Ideal.ofList xs • (⊤ : Submodule R M) := by
  induction xs generalizing M with
  | nil => simpa using hm
  | cons x ys ih =>
    rw [List.map_cons, Ideal.ofList_cons_smul, List.prod_cons, mul_pow, mul_smul] at hm
    rw [Ideal.ofList_cons_smul]
    have hx := ((isWeaklyRegular_cons_iff M x ys).1 h).1
    -- In `N = M ⧸ xⁿ⁺¹ M`, on which `ys` is weakly regular, `(∏ ys)ⁿ xⁿ m ∈ (ysⁿ⁺¹) N`.
    have hN := ((isWeaklyRegular_cons_iff M _ ys).1 (h.pow_cons (Nat.succ_ne_zero n))).2
    have hmN : ys.prod ^ n • (Submodule.Quotient.mk (x ^ n • m) : QuotSMulTop (x ^ (n + 1)) M) ∈
        Ideal.ofList (ys.map (· ^ (n + 1))) • (⊤ : Submodule R (QuotSMulTop (x ^ (n + 1)) M)) := by
      rw [← Submodule.Quotient.mk_smul, smul_comm, Submodule.Quotient.mk_mem_smul_top_iff]
      exact hm
    have hmem := ih hN hmN
    rw [Submodule.Quotient.mk_mem_smul_top_iff] at hmem
    -- Now `xⁿ m ∈ (xⁿ⁺¹, ys) M`; cancel `xⁿ` using the weak regularity of `ys` on `M ⧸ xⁿ M`.
    rcases n.eq_zero_or_pos with rfl | hn
    · simpa using hmem
    · exact mem_sup_of_pow_smul_mem hx
        ((isWeaklyRegular_cons_iff M _ ys).1 (h.pow_cons hn.ne')).2 hmem

/-- **The monomial property of regular sequences.** If `x₁, …, x_d` is a regular sequence on `M`,
then `(x₁ ⋯ x_d)ⁿ M ⊄ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹) M` for every `n`. -/
theorem IsRegular.not_prod_pow_smul_top_le {xs : List R} (h : IsRegular M xs) (n : ℕ) :
    ¬xs.prod ^ n • (⊤ : Submodule R M) ≤ Ideal.ofList (xs.map (· ^ (n + 1))) • ⊤ := by
  intro hle
  refine h.top_ne_smul (top_le_iff.1 fun m _ ↦ ?_).symm
  exact h.mem_ofList_smul_top_of_prod_pow_smul_mem n
    (hle (smul_mem_pointwise_smul m _ ⊤ mem_top))

/-- **The monomial property of an algebra.** If `x₁, …, x_d` is a regular sequence on an
`R`-algebra `C`, then the image of `(x₁ ⋯ x_d)ⁿ` in `C` does not lie in the ideal of `C` generated
by `x₁ⁿ⁺¹, …, x_dⁿ⁺¹`, for every `n`. -/
theorem IsRegular.algebraMap_prod_pow_notMem_map_ofList {C : Type*} [CommRing C] [Algebra R C]
    {xs : List R} (h : IsRegular C xs) (n : ℕ) :
    algebraMap R C (xs.prod ^ n) ∉ (Ideal.ofList (xs.map (· ^ (n + 1)))).map (algebraMap R C) := by
  intro hmem
  have h1 : (1 : C) ∈ Ideal.ofList xs • (⊤ : Submodule R C) := by
    refine h.mem_ofList_smul_top_of_prod_pow_smul_mem n ?_
    rwa [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Algebra.smul_def, mul_one]
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← Ideal.eq_top_iff_one] at h1
  exact h.top_ne_smul (by rw [Ideal.smul_top_eq_map, h1, Submodule.restrictScalars_top])

/-- **The monomial property of a regular sequence on a ring.** If `x₁, …, x_d` is a regular
sequence on `R`, then `(x₁ ⋯ x_d)ⁿ ∉ (x₁ⁿ⁺¹, …, x_dⁿ⁺¹)` for every `n`. -/
theorem IsRegular.prod_pow_notMem_ofList {xs : List R} (h : IsRegular R xs) (n : ℕ) :
    xs.prod ^ n ∉ Ideal.ofList (xs.map (· ^ (n + 1))) := by
  simpa using h.algebraMap_prod_pow_notMem_map_ofList n

end RingTheory.Sequence
