/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Exact sequences of linear maps

This file records elementary constructions and consequences for exact pairs of linear maps, and
the vanishing of the alternating sum of dimensions along a long exact sequence of
finite-dimensional vector spaces of the shape produced by a homology theory,

```text
⋯ ⟶ Aₙ ⟶ Bₙ ⟶ Cₙ ⟶ Aₙ₋₁ ⟶ ⋯ ⟶ A₀ ⟶ B₀ ⟶ C₀ ⟶ 0,
```

(`TauCeti.finsum_neg_one_pow_finrank_eq_zero_of_exact`).  Mathlib's
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact` treats a finite exact sequence indexed by
`Fin (n + 2)` with a single family of spaces; the long exact sequences of homology theories are
instead indexed by `ℕ` with three families of spaces, which is the form taken here.
-/

public section

namespace TauCeti

/-- The product of exact pairs of linear maps is exact. -/
theorem _root_.Function.Exact.prodMap
    {R M₁ N₁ P₁ M₂ N₂ P₂ : Type*} [Semiring R]
    [AddCommMonoid M₁] [AddCommMonoid N₁] [AddCommMonoid P₁]
    [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂]
    [Module R M₁] [Module R N₁] [Module R P₁]
    [Module R M₂] [Module R N₂] [Module R P₂]
    {f₁ : M₁ →ₗ[R] N₁} {g₁ : N₁ →ₗ[R] P₁}
    {f₂ : M₂ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] P₂}
    (h₁ : Function.Exact f₁ g₁) (h₂ : Function.Exact f₂ g₂) :
    Function.Exact (f₁.prodMap f₂) (g₁.prodMap g₂) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y₁, hy₁⟩ := (h₁ x.1).1 (congrArg Prod.fst hx)
    obtain ⟨y₂, hy₂⟩ := (h₂ x.2).1 (congrArg Prod.snd hx)
    exact ⟨(y₁, y₂), by ext <;> assumption⟩
  · rintro ⟨y, rfl⟩
    exact Prod.ext ((h₁ _).2 ⟨y.1, rfl⟩) ((h₂ _).2 ⟨y.2, rfl⟩)

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are finite-dimensional, then so
is `N`.

This is deduced from `Module.Finite.of_exact`, which asks the second map to be surjective, by
corestricting `g` to its range. -/
theorem finiteDimensional_of_exact {k M N P : Type*} [DivisionRing k] [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] {f : M →ₗ[k] N}
    {g : N →ₗ[k] P}
    (h : Function.Exact f g) [FiniteDimensional k M] [FiniteDimensional k P] :
    FiniteDimensional k N :=
  Module.Finite.of_exact (g := g.rangeRestrict)
    (fun x ↦ by rw [← h x, ← Subtype.coe_inj]; simp) g.surjective_rangeRestrict

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are trivial, then so is `N`. -/
theorem subsingleton_of_exact {M N P : Type*} [Zero P] {f : M → N} {g : N → P}
    (h : Function.Exact f g) [Subsingleton M] [Subsingleton P] : Subsingleton N :=
  ⟨fun x y ↦ by
    -- `P` is trivial, so both `x` and `y` are hit by `f`; `M` is trivial, so by the same element.
    obtain ⟨a, rfl⟩ := (h x).1 (Subsingleton.elim _ _)
    obtain ⟨b, rfl⟩ := (h y).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim a b]⟩

section LongExact

open Module

variable {k : Type*} [DivisionRing k] {A B C : ℕ → Type*}
  [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)] [∀ n, FiniteDimensional k (A n)]
  [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
  [∀ n, AddCommGroup (C n)] [∀ n, Module k (C n)] [∀ n, FiniteDimensional k (C n)]
  {f : ∀ n, A n →ₗ[k] B n} {g : ∀ n, B n →ₗ[k] C n} {δ : ∀ n, C (n + 1) →ₗ[k] A n}

/-- The terms of a long exact sequence `⋯ ⟶ Aₙ ⟶ Bₙ ⟶ Cₙ ⟶ Aₙ₋₁ ⟶ ⋯ ⟶ C₀ ⟶ 0` of vector
spaces satisfy the truncated Euler relation: the alternating sum through degree `n` of
`dim Aᵢ - dim Bᵢ + dim Cᵢ` is, up to the sign `(-1)ⁿ`, the dimension of the image of the
connecting map `Cₙ₊₁ ⟶ Aₙ` that the truncation cuts off. -/
theorem sum_range_neg_one_pow_finrank_eq_of_exact (hfg : ∀ n, Function.Exact (f n) (g n))
    (hgδ : ∀ n, Function.Exact (g (n + 1)) (δ n)) (hδf : ∀ n, Function.Exact (δ n) (f n))
    (hg : Function.Surjective (g 0)) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * (finrank k (A i) - finrank k (B i) + finrank k (C i)) =
      (-1) ^ n * finrank k (LinearMap.range (δ n)) := by
  have := fun i ↦ finiteDimensional_of_exact (hfg i)
  -- Rank--nullity at each map, with kernels replaced by images through exactness.
  have hA (i : ℕ) : finrank k (A i) =
      finrank k (LinearMap.range (δ i)) + finrank k (LinearMap.range (f i)) := by
    rw [← (f i).finrank_range_add_finrank_ker, (hδf i).linearMap_ker_eq, add_comm]
  have hB (i : ℕ) : finrank k (B i) =
      finrank k (LinearMap.range (f i)) + finrank k (LinearMap.range (g i)) := by
    rw [← (g i).finrank_range_add_finrank_ker, (hfg i).linearMap_ker_eq, add_comm]
  have hC (i : ℕ) : finrank k (C (i + 1)) =
      finrank k (LinearMap.range (g (i + 1))) + finrank k (LinearMap.range (δ i)) := by
    rw [← (δ i).finrank_range_add_finrank_ker, (hgδ i).linearMap_ker_eq, add_comm]
  have hC₀ : finrank k (C 0) = finrank k (LinearMap.range (g 0)) := by
    rw [LinearMap.range_eq_top.2 hg, finrank_top]
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, hA, hB, hC₀]
    push_cast
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hA, hB, hC]
    push_cast
    ring

/-- **The Euler characteristic of a long exact sequence vanishes.**  For a long exact sequence
`⋯ ⟶ Aₙ ⟶ Bₙ ⟶ Cₙ ⟶ Aₙ₋₁ ⟶ ⋯ ⟶ C₀ ⟶ 0` of finite-dimensional vector spaces in which only
finitely many `Aₙ` are nonzero, the alternating sum of `dim Aₙ - dim Bₙ + dim Cₙ` vanishes; its
summands vanish in all large degrees. -/
theorem finsum_neg_one_pow_finrank_eq_zero_of_exact (hfg : ∀ n, Function.Exact (f n) (g n))
    (hgδ : ∀ n, Function.Exact (g (n + 1)) (δ n)) (hδf : ∀ n, Function.Exact (δ n) (f n))
    (hg : Function.Surjective (g 0)) (hA : (Function.support fun n ↦ finrank k (A n)).Finite) :
    ∑ᶠ n, (-1 : ℤ) ^ n * (finrank k (A n) - finrank k (B n) + finrank k (C n)) = 0 := by
  obtain ⟨N, hN⟩ := hA.bddAbove
  have hδ {n : ℕ} (hn : N < n) : finrank k (LinearMap.range (δ n)) = 0 :=
    Nat.eq_zero_of_le_zero <| (Submodule.finrank_le _).trans_eq <|
      by_contra fun h ↦ hn.not_ge (hN h)
  have hsum := sum_range_neg_one_pow_finrank_eq_of_exact hfg hgδ hδf hg
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (N + 2)), hsum, hδ (by lia),
    Nat.cast_zero, mul_zero]
  -- In a degree `m + 1 ≥ N + 2` the summand is the difference of the truncated sums through
  -- degrees `m + 1` and `m`, both of which vanish.
  intro n hn
  by_contra h
  rw [Finset.coe_range, Set.mem_Iio, not_lt] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  have := hsum (m + 1)
  rw [Finset.sum_range_succ, hsum, hδ (by lia), hδ (by lia)] at this
  exact hn (by simpa using this)

end LongExact

end TauCeti
