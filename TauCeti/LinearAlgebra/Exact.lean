/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Exact sequences of linear maps

This file records elementary constructions and consequences for exact pairs of linear maps,
including the left exactness of `Hom` over a noncommutative ring
(`Function.Exact.lcomp_of_surjective`), the horseshoe step `TauCeti.exists_surjective_ker_exact`
and the short exact sequence of kernels `TauCeti.exact_ker_comp` attached to a surjection and a
further map, the dimension of the homology of a complex of finite-dimensional vector spaces in
terms of the two cokernels (`LinearMap.finrank_map_mkQ_ker_add_finrank`), and the vanishing of
the alternating sum of dimensions along a long exact sequence of finite-dimensional vector spaces
of the shape produced by a homology theory,

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

/-- In a short exact sequence `0 ⟶ M ⟶ N ⟶ P ⟶ 0` of vector spaces with `N` finite-dimensional,
`dim N = dim M + dim P`. -/
theorem _root_.Function.Exact.finrank_eq_add {k M N P : Type*} [DivisionRing k] [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] [FiniteDimensional k N]
    {f : M →ₗ[k] N} {g : N →ₗ[k] P} (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Module.finrank k N = Module.finrank k M + Module.finrank k P := by
  rw [← g.finrank_range_add_finrank_ker, LinearMap.range_eq_top.2 hg, finrank_top,
    h.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf, add_comm]

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are trivial, then so is `N`. -/
theorem subsingleton_of_exact {M N P : Type*} [Zero P] {f : M → N} {g : N → P}
    (h : Function.Exact f g) [Subsingleton M] [Subsingleton P] : Subsingleton N :=
  ⟨fun x y ↦ by
    -- `P` is trivial, so both `x` and `y` are hit by `f`; `M` is trivial, so by the same element.
    obtain ⟨a, rfl⟩ := (h x).1 (Subsingleton.elim _ _)
    obtain ⟨b, rfl⟩ := (h y).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim a b]⟩

/-- **Left exactness of `Hom`** over a possibly noncommutative ring. If
`M₁ --f--> M₂ --g--> M₃ → 0` is exact, then precomposition gives a sequence
`(M₃ →ₗ[R] Q) → (M₂ →ₗ[R] Q) → (M₁ →ₗ[R] Q)` that is exact in the middle, for any ring `T` of
scalars acting on the `Hom` modules through `Q`. Together with
`LinearMap.lcomp_injective_of_surjective`, this says that `0 → Hom(M₃, Q) → Hom(M₂, Q) → Hom(M₁, Q)`
is exact.

This is Mathlib's `LinearMap.exact_lcomp_of_exact_of_surjective`, whose statement and proof are
followed here, without its commutativity assumption on `R`. -/
theorem _root_.Function.Exact.lcomp_of_surjective {R T M₁ M₂ M₃ : Type*} (Q : Type*) [Ring R]
    [Semiring T] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup Q]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R Q] [Module T Q] [SMulCommClass R T Q]
    {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} (exac : Function.Exact f g)
    (surj : Function.Surjective g) :
    Function.Exact (LinearMap.lcomp T Q g) (LinearMap.lcomp T Q f) := by
  intro h
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  refine ⟨fun hh ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · use ((LinearMap.range f).liftQ h (LinearMap.range_le_ker_iff.mpr hh)).comp
      (exac.linearEquivOfSurjective surj).symm.toLinearMap
    ext x
    simp
  · rw [← hy, LinearMap.comp_assoc, exac.linearMap_comp_eq_zero, LinearMap.comp_zero y]

section ShortExact

open LinearMap

variable {R : Type*} [Ring R] {M₁ M M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

/-- **The horseshoe step.** Given a short exact sequence `0 → M₁ → M → M₂ → 0`, a surjection
`π₁ : P₁ → M₁` and a surjection `π₂ : P₂ → M₂` from a projective module, there is a surjection
`π : P₁ × P₂ → M` whose kernel is an extension of `ker π₂` by `ker π₁`. -/
theorem exists_surjective_ker_exact {P₁ P₂ : Type*} [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂] {f : M₁ →ₗ[R] M}
    {g : M →ₗ[R] M₂} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {π₁ : P₁ →ₗ[R] M₁} (hπ₁ : Function.Surjective π₁)
    {π₂ : P₂ →ₗ[R] M₂} (hπ₂ : Function.Surjective π₂) :
    ∃ π : (P₁ × P₂) →ₗ[R] M, Function.Surjective π ∧
      ∃ (i : ker π₁ →ₗ[R] ker π) (p : ker π →ₗ[R] ker π₂),
        Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p := by
  -- Lift `π₂` along `g` to `σ : P₂ → M`, and send `(x, y)` to `f (π₁ x) + σ y`.
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g π₂ hg
  have hgσ (y : P₂) : g (σ y) = π₂ y := LinearMap.congr_fun hσ y
  -- Every element of `ker g` is `f (π₁ x)` for some `x`.
  have hlift {m : M} (hm : g m = 0) : ∃ x, f (π₁ x) = m := by
    obtain ⟨m₁, rfl⟩ := (hfg m).mp hm
    obtain ⟨x, rfl⟩ := hπ₁ m₁
    exact ⟨x, rfl⟩
  let π := (f ∘ₗ π₁).coprod σ
  have hπ (z : P₁ × P₂) : π z = f (π₁ z.1) + σ z.2 := rfl
  refine ⟨π, fun m ↦ ?_, (inl R _ _).restrict fun x hx ↦ ?_, (snd R _ _).restrict fun z hz ↦ ?_,
    fun x y hxy ↦ ?_, fun z ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hπ₂ (g m)
    obtain ⟨x, hx⟩ := hlift (m := m - σ y) (by simp [hgσ, hy])
    exact ⟨(x, y), by simp [hπ, hx]⟩
  · simp_all
  · rw [mem_ker] at hz ⊢
    simpa [hπ, hgσ, hfg.apply_apply_eq_zero] using congrArg g hz
  · exact Subtype.ext (Prod.ext_iff.mp (congrArg Subtype.val hxy)).1
  · obtain ⟨⟨x, y⟩, hz⟩ := z
    have hz' : f (π₁ x) + σ y = 0 := (hπ _).symm.trans hz
    refine ⟨fun h ↦ ?_, ?_⟩
    · have hy : y = 0 := congrArg Subtype.val h
      subst hy
      exact ⟨⟨x, mem_ker.mpr (hf (by simpa using hz'))⟩, rfl⟩
    · rintro ⟨x', hx'⟩
      exact Subtype.ext (congrArg (fun z ↦ (Subtype.val z).2) hx').symm
  · obtain ⟨y, hy⟩ := y
    obtain ⟨x, hx⟩ := hlift (m := σ y) (by rwa [hgσ, ← mem_ker])
    exact ⟨⟨(-x, y), by simp [hπ, hx]⟩, rfl⟩

/-- For a surjection `π : P → M` and a linear map `g : M → M₂`, the sequence
`0 → ker π → ker (g ∘ π) → ker g → 0`, given by inclusion and by `π`, is exact. -/
theorem exact_ker_comp {P : Type*} [AddCommGroup P] [Module R P] {π : P →ₗ[R] M}
    (hπ : Function.Surjective π) (g : M →ₗ[R] M₂) :
    Function.Injective (Submodule.inclusion (ker_le_ker_comp π g)) ∧
      Function.Exact (Submodule.inclusion (ker_le_ker_comp π g))
        (π.restrict (p := ker (g ∘ₗ π)) (q := ker g) fun _ hx ↦ by simpa using hx) ∧
      Function.Surjective (π.restrict (p := ker (g ∘ₗ π)) (q := ker g)
        fun _ hx ↦ by simpa using hx) := by
  refine ⟨Submodule.inclusion_injective _, fun x ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, hx⟩ := x
    refine ⟨fun h ↦ ⟨⟨x, mem_ker.mpr (congrArg Subtype.val h)⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, hxy⟩
    obtain rfl : y = x := congrArg Subtype.val hxy
    exact Subtype.ext (mem_ker.mp hy)
  · obtain ⟨y, hy⟩ := y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, by simpa using hy⟩, rfl⟩

end ShortExact

section Homology

open Module LinearMap

variable {k V₁ V₂ V₃ : Type*} [DivisionRing k] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]

/-- For a complex `V₁ --f--> V₂ --g--> V₃` of finite-dimensional vector spaces, the dimension of
its homology at `V₂`, plus `dim V₃`, is `dim coker f + dim coker g`. The homology is written as
the image of the cycles `ker g` in the cokernel `V₂ ⧸ range f`. -/
theorem _root_.LinearMap.finrank_map_mkQ_ker_add_finrank [FiniteDimensional k V₂]
    [FiniteDimensional k V₃] (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃) (hfg : g ∘ₗ f = 0) :
    finrank k ((ker g).map (range f).mkQ) + finrank k V₃ =
      finrank k (V₂ ⧸ range f) + finrank k (V₃ ⧸ range g) := by
  have hH := Submodule.finrank_quotient_add_finrank ((ker g).map (range f).mkQ)
  rw [(Submodule.quotientQuotientEquivQuotient _ _ (range_le_ker_iff.2 hfg)).finrank_eq] at hH
  have := Submodule.finrank_quotient_add_finrank (ker g)
  have := Submodule.finrank_quotient_add_finrank (range f)
  have := Submodule.finrank_quotient_add_finrank (range g)
  have := g.finrank_range_add_finrank_ker
  omega

end Homology

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
