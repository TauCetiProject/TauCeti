/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial
public import TauCeti.RingTheory.Huber.Uniform

import Mathlib.Topology.UniformSpace.CompleteSeparated
import TauCeti.RingTheory.Adjoin.Inverse

/-!
# The Laurent cover of a uniform Tate ring

Let `A` be a complete Hausdorff Tate ring and `f ∈ A`. The rational subsets

```text
U₁ = R({f, 1}/1) = {|f| ≤ 1},      U₂ = R({1}/f) = {|f| ≥ 1},      U₁ ∩ U₂ = R({f², f, 1}/(1 · f))
```

cover `Spa(A, A⁺)`. When `A` is uniform, that is, when its power-bounded elements form a bounded
set, the augmented Čech sequence of this cover,

```text
A → A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩,      a ↦ (a, a),      (x, y) ↦ x|U₁∩U₂ - y|U₁∩U₂,
```

is exact, and its first map is a closed embedding. These are the injectivity and the exactness in
the middle in Corollary 4 of Buzzard–Verberkmoes, the case of a Laurent cover in their theorem that
stably uniform Tate rings are sheafy (their Theorem 7); Corollary 4 also asserts that the second
map is surjective, which is not part of the results here. The statements have the same form as
`laurentCover_exact` and `isClosedEmbedding_laurentCover`, which assume strong noetherianness
instead of uniformity.

## Main results

* `TauCeti.ValuationSpectrum.isPowerBounded_of_algebraMap_mem_locSubring_laurentCover`: an
  element of `A₀[f]` whose image in `A[1/f]` lies in `A₀[1/f]` is power-bounded.
* `TauCeti.ValuationSpectrum.isClosedEmbedding_laurentCover_of_isUniform`: for uniform `A` the map
  `A → A⟨U₁⟩ × A⟨U₂⟩` is a closed embedding.
* `TauCeti.ValuationSpectrum.laurentCover_exact_of_isUniform`: for uniform `A` the kernel of the
  difference of restrictions `A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩` is the image of `A`.

## Implementation notes

The rings of definition of the three localisations are `D₁ = A₀[f]`, `D₂ = A₀[1/f]` and
`D₁₂ = A₀[f, 1/f]`. The first result is Buzzard–Verberkmoes's Lemma 3 for the cover `{1, f}`: an
element of `D₁ ∩ D₂` is, up to a power of `f`, a polynomial in `f` of bounded degree on both sides,
so its powers all lie in one finitely generated `A₀`-submodule. With uniformity it bounds the
elements of `A` lying in `ϖⁿ D₁` and in `ϖⁿ D₂` by `ϖⁿ A°`, so `A` carries the topology induced
from `A⟨U₁⟩ × A⟨U₂⟩`, and the image of the complete ring `A` is closed. Since `D₁₂ = D₁ + D₂`, the
difference map is strict before completion, which makes every pair agreeing on `U₁ ∩ U₂` a limit
of pairs coming from `A`. Buzzard–Verberkmoes's Lemma 2 obtains this step from the general fact
that completion preserves exact sequences of strict maps; here it is proved directly for this
sequence.

## References

* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25–39 (arXiv:1404.7020), Lemmas 2 and 3 and Corollary 4.
-/

public section

open scoped Pointwise
open Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization
open UniformSpace (Completion)

namespace TauCeti.ValuationSpectrum

-- Decidable equality is only used to write the numerator sets `{f, 1}`, `{1}` and
-- `{f * f, f, 1}`, so it is supplied classically rather than assumed of `A`.
attribute [local instance] Classical.decEq

/-! ### Polynomials of bounded degree in one element -/

section Monomial

variable {A : Type*} [CommRing A] {A₀ : Subring A} {f : A}

-- The additive subgroup `A₀ + A₀ f + ⋯ + A₀ fᵈ` of values at `f` of polynomials of degree `≤ d`.
private def monomialSpan (A₀ : Subring A) (f : A) (d : ℕ) : AddSubgroup A :=
  AddSubgroup.closure ((A₀ : Set A) * ((f ^ ·) '' Set.Iic d))

private theorem monomialSpan_mono {d e : ℕ} (h : d ≤ e) :
    monomialSpan A₀ f d ≤ monomialSpan A₀ f e :=
  AddSubgroup.closure_mono <| by gcongr

private theorem mul_pow_mem_monomialSpan {c : A} (hc : c ∈ A₀) {i d : ℕ} (hi : i ≤ d) :
    c * f ^ i ∈ monomialSpan A₀ f d := AddSubgroup.subset_closure (Set.mul_mem_mul hc ⟨i, hi, rfl⟩)

-- Every element of `A₀` has degree `≤ 0`.
private theorem mem_monomialSpan_zero {c : A} (hc : c ∈ A₀) : c ∈ monomialSpan A₀ f 0 := by
  simpa using mul_pow_mem_monomialSpan hc (le_refl 0)

-- The degree of a product is at most the sum of the degrees.
private theorem mul_mem_monomialSpan {d e : ℕ} {x y : A} (hx : x ∈ monomialSpan A₀ f d)
    (hy : y ∈ monomialSpan A₀ f e) : x * y ∈ monomialSpan A₀ f (d + e) := by
  -- as `ℤ`-spans, the product of the spans of two sets is the span of their product set
  simp only [monomialSpan, ← Submodule.span_int_eq_addSubgroupClosure,
    Submodule.mem_toAddSubgroup] at hx hy ⊢
  refine Submodule.span_mono ?_ ((Submodule.span_mul_span ℤ _ _).le (Submodule.mul_mem_mul hx hy))
  -- and a product of two monomials `a fⁱ · b fʲ` is the monomial `(a b) fⁱ⁺ʲ`
  rintro _ ⟨_, ⟨a, ha, _, ⟨i, hi, rfl⟩, rfl⟩, _, ⟨b, hb, _, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
  exact ⟨a * b, mul_mem ha hb, f ^ (i + j), ⟨i + j, Set.mem_Iic.2 (add_le_add hi hj), rfl⟩, by ring⟩

-- The `k`-th power of an element of degree `≤ 1` has degree `≤ k`.
private theorem pow_mem_monomialSpan {s : A} (hs : s ∈ monomialSpan A₀ f 1) (k : ℕ) :
    s ^ k ∈ monomialSpan A₀ f k := by
  induction k <;> grind [mem_monomialSpan_zero, mul_mem_monomialSpan, one_mem]

-- The element `f` itself has degree `≤ 1`.
private theorem self_mem_monomialSpan_one : f ∈ monomialSpan A₀ f 1 := by
  simpa using mul_pow_mem_monomialSpan (one_mem A₀) (le_refl 1)

-- If `r` has degree `≤ d₁` and `f ^ d₂ * r` has degree `≤ d₂`, then `r fʲ` has degree
-- `≤ d₁ + d₂` for every `j ≤ d₁ + d₂`.
private theorem mul_pow_mem_monomialSpan_add {r : A} {d₁ d₂ : ℕ} (h₁ : r ∈ monomialSpan A₀ f d₁)
    (h₂ : f ^ d₂ * r ∈ monomialSpan A₀ f d₂) {j : ℕ} (hj : j ≤ d₁ + d₂) :
    r * f ^ j ∈ monomialSpan A₀ f (d₁ + d₂) := by
  rcases le_total j d₂ with h | h
  -- for `j ≤ d₂` use the bound on `r`
  · exact monomialSpan_mono (by lia)
      (mul_mem_monomialSpan h₁ (pow_mem_monomialSpan self_mem_monomialSpan_one j))
  -- otherwise use the bound on `f ^ d₂ * r`, writing `fʲ = f ^ d₂ * f ^ (j - d₂)`
  · rw [← pow_mul_pow_sub f h, ← mul_assoc, mul_comm r]
    exact monomialSpan_mono (by lia)
      (mul_mem_monomialSpan h₂ (pow_mem_monomialSpan self_mem_monomialSpan_one _))

-- Under the same bounds, multiplication by `r` preserves degree `≤ d₁ + d₂`.
private theorem mul_mem_monomialSpan_add {r : A} {d₁ d₂ : ℕ} (h₁ : r ∈ monomialSpan A₀ f d₁)
    (h₂ : f ^ d₂ * r ∈ monomialSpan A₀ f d₂) {y : A} (hy : y ∈ monomialSpan A₀ f (d₁ + d₂)) :
    r * y ∈ monomialSpan A₀ f (d₁ + d₂) := by
  -- the span pulled back along `r * ·` is an additive subgroup: check the generators `a * f ^ j`
  refine (AddSubgroup.closure_le ((monomialSpan A₀ f (d₁ + d₂)).comap (.mulLeft r))).2 ?_ hy
  rintro _ ⟨a, ha, _, ⟨j, hj, rfl⟩, rfl⟩
  simpa [mul_left_comm r a] using
    mul_mem_monomialSpan (mem_monomialSpan_zero ha) (mul_pow_mem_monomialSpan_add h₁ h₂ hj)

end Monomial

/-! ### Power-bounded elements on the two Laurent pieces -/

section PowerBounded

variable {A : Type*} [CommRing A] [TopologicalSpace A] (P : PairOfDefinition A) {f : A}

-- Every `x ∈ A₀[T/s]` satisfies `sⁿ x = y` for some `y` of degree `≤ n` in `f`, when `s` and the
-- numerators have degree `≤ 1`.
private theorem exists_pow_mul_eq_of_mem_locSubring {T : Finset A} {s : A} {S : Type*} [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hT : ∀ t ∈ T, t ∈ monomialSpan P.ringOfDefinition f 1)
    (hs : s ∈ monomialSpan P.ringOfDefinition f 1) {x : S} (hx : x ∈ locSubring P T s S) : ∃ n,
    ∃ y ∈ monomialSpan P.ringOfDefinition f n, algebraMap A S (s ^ n) * x = algebraMap A S y := by
  rw [locSubring_eq_adjoin, Subalgebra.mem_toSubring] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨t, ht⟩, rfl⟩ := hx
    exact ⟨1, t, hT t ht, by simp⟩
  | algebraMap c =>
    refine ⟨0, c, mem_monomialSpan_zero c.2, ?_⟩
    rw [pow_zero, map_one, one_mul, IsScalarTower.algebraMap_apply P.ringOfDefinition A S,
      Algebra.algebraMap_ofSubsemiring_apply]
  | add x y _ _ hx hy =>
    obtain ⟨n, y₁, hy₁, e₁⟩ := hx
    obtain ⟨m, y₂, hy₂, e₂⟩ := hy
    refine ⟨n + m, y₁ * s ^ m + s ^ n * y₂, add_mem ?_ ?_, by grind⟩
    · exact mul_mem_monomialSpan hy₁ (pow_mem_monomialSpan hs m)
    · exact mul_mem_monomialSpan (pow_mem_monomialSpan hs n) hy₂
  | mul x y _ _ hx hy =>
    obtain ⟨n, y₁, hy₁, e₁⟩ := hx
    obtain ⟨m, y₂, hy₂, e₂⟩ := hy
    exact ⟨n + m, y₁ * y₂, mul_mem_monomialSpan hy₁ hy₂, by grind⟩

-- Clearing the power of `s` in `A` itself: an element whose image lies in `A₀[T/s]` is, after
-- multiplication by some `sⁿ`, of degree `≤ n` in `f`.
private theorem exists_pow_mul_mem_monomialSpan {T : Finset A} {s : A} {S : Type*} [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hT : ∀ t ∈ T, t ∈ monomialSpan P.ringOfDefinition f 1)
    (hs : s ∈ monomialSpan P.ringOfDefinition f 1) {a : A}
    (ha : algebraMap A S a ∈ locSubring P T s S) :
    ∃ n, s ^ n * a ∈ monomialSpan P.ringOfDefinition f n := by
  obtain ⟨n, y, hy, e⟩ := exists_pow_mul_eq_of_mem_locSubring P hT hs ha
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq s ((map_mul _ _ _).trans e)
  refine ⟨k + n, ?_⟩
  rw [pow_add, mul_assoc, hk]
  exact mul_mem_monomialSpan (pow_mem_monomialSpan hs k) hy

variable [IsTopologicalRing A]

/-- **Buzzard–Verberkmoes, Lemma 3, for the Laurent cover of `f`.** Let `A₀` be the ring of
definition of a pair of definition of `A`, and `f ∈ A`. If `a ∈ A` lies in `A₀[f]`, the ring of
definition of `R({f, 1}/1) = {|f| ≤ 1}`, and its image in `A[1/f]` lies in `A₀[1/f]`, the ring of
definition of `R({1}/f) = {|f| ≥ 1}`, then `a` is power-bounded in `A`. Compare
`isPowerBounded_of_mem_locSubring`, which concerns power-boundedness in a localisation `Aₛ`. -/
theorem isPowerBounded_of_algebraMap_mem_locSubring_laurentCover (f : A) {S₁ S₂ : Type*}
    [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁] [CommRing S₂] [Algebra A S₂]
    [IsLocalization.Away f S₂] {a : A} (h₁ : algebraMap A S₁ a ∈ locSubring P {f, 1} 1 S₁)
    (h₂ : algebraMap A S₂ a ∈ locSubring P {1} f S₂) : IsPowerBounded a := by
  have := P.toNonarchimedeanRing
  have hf : f ∈ monomialSpan P.ringOfDefinition f 1 := self_mem_monomialSpan_one
  have hone : (1 : A) ∈ monomialSpan P.ringOfDefinition f 1 :=
    monomialSpan_mono zero_le_one (mem_monomialSpan_zero (one_mem _))
  -- `a` has degree `≤ d₁` in `f`, and `f ^ d₂ * a` has degree `≤ d₂`
  obtain ⟨d₁, hd₁⟩ := exists_pow_mul_mem_monomialSpan P (by simp [hf, hone]) hone h₁
  obtain ⟨d₂, hd₂⟩ := exists_pow_mul_mem_monomialSpan P (by simp [hone]) hf h₂
  rw [one_pow, one_mul] at hd₁
  -- multiplication by `a` preserves the bounded set of values of polynomials of degree
  -- `≤ d₁ + d₂`, which contains `1`
  exact isPowerBounded_of_isBounded_of_mul_mem (P.isBounded_ringOfDefinition.mul
    (isBounded_finite ((Set.finite_Iic (d₁ + d₂)).image _)))
    (monomialSpan_mono zero_le (mem_monomialSpan_zero (one_mem _)))
    fun _ ↦ mul_mem_monomialSpan_add hd₁ hd₂

end PowerBounded

/-! ### The overlap ring of definition is the sum of those of the two pieces -/

section Decomposition

variable {A : Type*} [CommRing A] [TopologicalSpace A] (P : PairOfDefinition A) (f : A)
  (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂]

-- The ring of definition `A₀[f², f, 1]/(1 · f)` of the overlap lies in `A₀[f, 1/f]`.
private theorem mem_adjoin_of_mem_locSubring {d : S₁₂}
    (hd : d ∈ locSubring P {f * f, f, 1} (1 * f) S₁₂) :
    d ∈ Algebra.adjoin P.ringOfDefinition {algebraMap A S₁₂ f, (divBy 1 (1 * f) : S₁₂)} := by
  rw [locSubring_eq_adjoin, Subalgebra.mem_toSubring] at hd
  -- the generators `f²/(1 · f) = f`, `f/(1 · f) = 1` and `1/(1 · f)` all lie in `A₀[f, 1/f]`
  exact Algebra.adjoin_le (by simp [Set.range_subset_iff, Algebra.mem_adjoin_of_mem]) hd

omit [IsLocalization.Away (1 * f) S₁₂] in
-- An element of `A₀[f]` in the overlap is the image of an element of `A₀[f] ⊆ A`.
private theorem exists_algebraMap_eq_of_mem_adjoin {y : S₁₂}
    (hy : y ∈ Algebra.adjoin P.ringOfDefinition {algebraMap A S₁₂ f}) :
    ∃ p : A, algebraMap A S₁ p ∈ locSubring P {f, 1} 1 S₁ ∧ algebraMap A S₁₂ p = y := by
  rw [← Set.image_singleton, Algebra.adjoin_algebraMap] at hy
  obtain ⟨p, hp, rfl⟩ := Subalgebra.mem_map.1 hy
  refine ⟨p, ?_, rfl⟩
  -- the image of `p` in `A_1` lies in `A₀[f/1] ⊆ A₀[f/1, 1/1]`
  rw [locSubring_eq_adjoin, Subalgebra.mem_toSubring]
  refine Algebra.adjoin_mono (Set.image_subset_iff.2 <| Set.singleton_subset_iff.2 ?_)
    ((Algebra.adjoin_algebraMap _ S₁ {f}).ge (Subalgebra.mem_map.2 ⟨p, hp, rfl⟩))
  exact ⟨⟨f, by simp⟩, by simpa using divBy_mul_cancel_right (S := S₁) f 1⟩

-- An element of `A₀[1/f]` in the overlap is the image of an element of `A₀[1/f] ⊆ A_f`.
private theorem exists_awayLift_eq_of_mem_adjoin {z : S₁₂}
    (hz : z ∈ Algebra.adjoin P.ringOfDefinition {(divBy 1 (1 * f) : S₁₂)}) :
    ∃ q ∈ locSubring P {1} f S₂, IsLocalization.Away.lift f
      (IsLocalization.Away.isUnit_of_dvd (1 * f) ⟨1, mul_comm 1 f⟩) q = z := by
  -- the image of `A₀[1/f]` is a subring, so it suffices that it contains `A₀` and `1/(1 · f)`
  refine Subring.mem_map.1 <| Subring.closure_le.2 ?_ (Algebra.mem_adjoin_iff.1 hz)
  rintro _ (⟨c, rfl⟩ | rfl)
  · refine ⟨_, algebraMap_mem_locSubring P _ f S₂ c.2, ?_⟩
    rw [IsLocalization.Away.lift_eq, IsScalarTower.algebraMap_apply P.ringOfDefinition A S₁₂,
      Algebra.algebraMap_ofSubsemiring_apply]
  · refine ⟨divBy 1 f, divBy_mem_locSubring P _ f S₂ (Finset.mem_singleton_self 1), ?_⟩
    rw [awayLift_divBy f 1 (1 * f) (mul_comm 1 f), mul_one]

-- `A₀[f², f, 1]/(1 · f) = A₀[f] + A₀[1/f]`, with `n`-th basic neighbourhoods: for `c ∈ D₁₂` and
-- `b ∈ Iⁿ`, the product `c · b` is the image of an element of `A` lying in `image(J₁ⁿ)` plus the
-- image of an element of `image(J₂ⁿ)`. These products generate `image(J₁₂ⁿ)`.
private theorem exists_mul_algebraMap_eq_add {c : S₁₂}
    (hc : c ∈ locSubring P {f * f, f, 1} (1 * f) S₁₂) {n : ℕ} {b : P.ringOfDefinition}
    (hb : b ∈ P.idealOfDefinition ^ n) : ∃ p : A,
      algebraMap A S₁ p ∈ locIdealImage P {f, 1} 1 S₁ n ∧ ∃ q ∈ locIdealImage P {1} f S₂ n,
        c * algebraMap A S₁₂ b = algebraMap A S₁₂ p + IsLocalization.Away.lift f
          (IsLocalization.Away.isUnit_of_dvd (1 * f) ⟨1, mul_comm 1 f⟩) q := by
  -- `f · (1/(1 · f)) = 1`, so `A₀[f, 1/f] = A₀[f] + A₀[1/f]` as `A₀`-modules
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 <|
    (TauCeti.Algebra.toSubmodule_adjoin_pair_eq_sup_of_mul_eq_one (by simp)).le
      (mem_adjoin_of_mem_locSubring P f S₁₂ hc)
  obtain ⟨p, hp, rfl⟩ := exists_algebraMap_eq_of_mem_adjoin P f S₁ S₁₂ hy
  obtain ⟨q, hq, rfl⟩ := exists_awayLift_eq_of_mem_adjoin P f S₂ S₁₂ hz
  refine ⟨b * p, ?_, algebraMap A S₂ b * q, ?_, by simp [mul_add, mul_comm]⟩
  · rw [map_mul]
    exact locIdealImage_mul_locSubring_subset P _ _ _ n
      (Set.mul_mem_mul (algebraMap_mem_locIdealImage P _ _ _ hb) hp)
  · exact locIdealImage_mul_locSubring_subset P _ _ _ n
      (Set.mul_mem_mul (algebraMap_mem_locIdealImage P _ _ _ hb) hq)

-- The decomposition at each basic neighbourhood: `image(J₁₂ⁿ) = image(J₁ⁿ) + image(J₂ⁿ)`.
private theorem exists_eq_add_of_mem_locIdealImage (n : ℕ) {e : S₁₂}
    (he : e ∈ locIdealImage P {f * f, f, 1} (1 * f) S₁₂ n) :
    ∃ p : A, algebraMap A S₁ p ∈ locIdealImage P {f, 1} 1 S₁ n ∧ ∃ q ∈ locIdealImage P {1} f S₂ n,
      e = algebraMap A S₁₂ p + IsLocalization.Away.lift f
        (IsLocalization.Away.isUnit_of_dvd (1 * f) ⟨1, mul_comm 1 f⟩) q := by
  rw [mem_locIdealImage_iff, locIdeal_pow] at he
  obtain ⟨d, hd, rfl⟩ := he
  -- as an `A₀`-module `J₁₂ⁿ = Iⁿ • D₁₂`, so the scalars from `D₁₂` are absorbed into the
  -- generators `b • c` with `b ∈ Iⁿ` and `c ∈ D₁₂`
  let _ := (toLocSubring P {f * f, f, 1} (1 * f) S₁₂).toAlgebra
  refine Submodule.smul_induction_on ((Ideal.smul_top_eq_map (P.idealOfDefinition ^ n)).ge hd)
    (fun b hb c _ ↦ ?_) fun x y ⟨p, hp, q, hq, e⟩ ⟨p', hp', q', hq', e'⟩ ↦ ?_
  · rw [Algebra.smul_def, Algebra.commutes, RingHom.algebraMap_toAlgebra, MulMemClass.coe_mul,
      toLocSubring_apply]
    exact exists_mul_algebraMap_eq_add P f S₁ S₂ S₁₂ c.2 hb
  · refine ⟨p + p', by rw [map_add]; exact add_mem hp hp', q + q', add_mem hq hq', ?_⟩
    rw [AddMemClass.coe_add, e, e', map_add, map_add, add_add_add_comm]

-- Strictness of the difference map before completion (Buzzard–Verberkmoes, §2, the remark before
-- Lemma 2): if `w ∈ A_f` restricts into `image(J₁₂ⁿ)`, then up to an element of `image(J₂ⁿ)` it is
-- the image of some `p ∈ A` whose image in `A_1` lies in `image(J₁ⁿ)`.
private theorem exists_sub_mem_locIdealImage (n : ℕ) {w : S₂}
    (hw : IsLocalization.Away.lift f (IsLocalization.Away.isUnit_of_dvd (1 * f) ⟨1, mul_comm 1 f⟩)
      w ∈ locIdealImage P {f * f, f, 1} (1 * f) S₁₂ n) :
    ∃ p : A, algebraMap A S₁ p ∈ locIdealImage P {f, 1} 1 S₁ n ∧
      w - algebraMap A S₂ p ∈ locIdealImage P {1} f S₂ n := by
  obtain ⟨p, hp, q, hq, e⟩ := exists_eq_add_of_mem_locIdealImage P f S₁ S₂ S₁₂ n hw
  -- the comparison map `A_f → A_{1 · f}` is bijective: both are localisations away from `f`
  have : IsLocalization.Away f S₁₂ := .of_associated (.of_eq (one_mul f))
  obtain rfl : w = algebraMap A S₂ p + q :=
    (IsLocalization.bijective (.powers f) _ (IsLocalization.Away.lift_comp f _)).injective <| by
      rw [e, map_add, IsLocalization.Away.lift_eq]
  exact ⟨p, hp, by rwa [add_sub_cancel_left]⟩

end Decomposition

/-! ### Approximation on the Laurent cover -/

section Approximation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (f : A)
  (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (hden₂ : HasDenominatorPower P {1} f S₂)
  (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂]

-- If `a ∈ A` and `b ∈ A_f` approximate a pair agreeing on the overlap to within the `n`-th
-- neighbourhoods, then `a - b` restricts into the `n`-th basic neighbourhood of the overlap.
private theorem awayLift_sub_mem_locIdealImage :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    ∀ {x₁ : Completion S₁} {x₂ : Completion S₂} {n : ℕ} {a : A} {b : S₂},
      restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp) x₁ =
        restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f)
          (by simp) x₂ →
      ((algebraMap A S₁ a : S₁) : Completion S₁) - x₁ ∈
        (localizationUniform P {f, 1} 1 S₁ hden₁).completionIdealImage n →
      (b : Completion S₂) - x₂ ∈ (localizationUniform P {1} f S₂ hden₂).completionIdealImage n →
      IsLocalization.Away.lift f (IsLocalization.Away.isUnit_of_dvd (1 * f) ⟨1, mul_comm 1 f⟩)
        (algebraMap A S₂ a - b) ∈ locIdealImage P {f * f, f, 1} (1 * f) S₁₂ n := by
  let hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  let hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  let _ := locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  let _ := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  intro x₁ x₂ n a b h ha hb
  rw [← localizationUniform_idealImage P {f * f, f, 1} (1 * f) S₁₂ hden₁₂,
    ← coe_mem_completionIdealImage_iff]
  -- restricted to the overlap, `a - b` is `(a - x₁)|U₁∩U₂ - (b - x₂)|U₁∩U₂`
  convert sub_mem
    (restrictionRingHom_mem_completionIdealImage P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂
      hden₁₂ f rfl (by simp) n _ ha)
    (restrictionRingHom_mem_completionIdealImage P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂
      hden₁₂ 1 (mul_comm 1 f) (by simp) n _ hb) using 1
  -- the `x₁`, `x₂` terms cancel by `h`, and both sides restrict `a` to the overlap
  simp [h, UniformSpace.Completion.coe_sub]

-- Pairs agreeing on the overlap lie in the closure of the image of `A`: approximate them from
-- `A` and `A_f`, and remove the error on the overlap by the strictness of the difference map.
private theorem mem_closure_range_laurentCover :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    ∀ {x₁ : Completion S₁} {x₂ : Completion S₂},
      restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp) x₁ =
        restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f)
          (by simp) x₂ →
      (x₁, x₂) ∈ closure (Set.range (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁)
        (toCompletionLoc P {1} f S₂ hden₂))) := by
  let hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  let _ := locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  intro x₁ x₂ h
  refine mem_closure_iff_nhds.2 fun t ht ↦ ?_
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht
  obtain ⟨n₁, hn₁⟩ := (localizationUniform P {f, 1} 1 S₁ hden₁).mem_nhds_completion_iff.1 hu
  obtain ⟨n₂, hn₂⟩ := (localizationUniform P {1} f S₂ hden₂).mem_nhds_completion_iff.1 hv
  -- approximate `x₁` by `a ∈ A` and `x₂` by `b ∈ A_f`, then correct `a` by `p`
  obtain ⟨y, hy⟩ :=
    (localizationUniform P {f, 1} 1 S₁ hden₁).exists_coe_sub_mem_completionIdealImage (max n₁ n₂) x₁
  -- every element of `A_1` comes from `A`
  obtain ⟨a, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (1 : A) .one y
  obtain ⟨b, hb⟩ :=
    (localizationUniform P {1} f S₂ hden₂).exists_coe_sub_mem_completionIdealImage (max n₁ n₂) x₂
  obtain ⟨p, hp, hq⟩ := exists_sub_mem_locIdealImage P f S₁ S₂ S₁₂ (max n₁ n₂)
    (awayLift_sub_mem_locIdealImage P f S₁ S₂ hden₂ S₁₂ h hy hb)
  refine ⟨_, huv ⟨?_, ?_⟩, a - p, rfl⟩
  -- `a - p = x₁ + (a - p - x₁)`, where `a - p - x₁ ∈ K_{max n₁ n₂} ⊆ K_{n₁}`; likewise at `x₂`
  · simpa only [RingHom.prod_apply, add_sub_cancel] using
      hn₁ _ (completionIdealImage_anti _ (le_max_left n₁ n₂)
        (toCompletionLoc_sub_mem_completionIdealImage P {f, 1} 1 S₁ hden₁ (a := a - p) hy
          (by simpa using hp)))
  · simpa only [RingHom.prod_apply, add_sub_cancel] using
      hn₂ _ (completionIdealImage_anti _ (le_max_right n₁ n₂)
        (toCompletionLoc_sub_mem_completionIdealImage P {1} f S₂ hden₂ (a := a - p) hb
          (by rwa [map_sub, sub_right_comm])))

end Approximation

/-! ### The Laurent cover of a uniform Tate ring -/

section Uniform

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [IsUniform A]
  (P : PairOfDefinition A) (f : A)
  (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (hden₂ : HasDenominatorPower P {1} f S₂)

omit [IsUniformAddGroup A] in
-- Every neighbourhood of zero in `A` contains the preimage of a neighbourhood of zero of
-- `A⟨U₁⟩ × A⟨U₂⟩`.
private theorem comap_laurentCover_nhds_zero_le :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    Filter.comap (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁)
      (toCompletionLoc P {1} f S₂ hden₂)) (𝓝 0) ≤ 𝓝 0 := by
  let hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  let _ := locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  intro U hU
  -- choose `n` with `ϖⁿ A° ⊆ U`
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨n, hn⟩ := (IsUniform.isBounded_setOf_isPowerBounded (A := A)).exists_pow_mul_subset
    hϖ.isTopologicallyNilpotent hU
  obtain ⟨v, hv⟩ := hϖ.isUnit.pow n
  set ρ := RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂)
  -- take `V` to be where multiplication by `ϖ⁻ⁿ` lands in the closures of the rings of definition
  have hV : (ρ ↑v⁻¹ * ·) ⁻¹' ((localizationUniform P {f, 1} 1 S₁ hden₁).completionIdealImage 0 ×ˢ
      (localizationUniform P {1} f S₂ hden₂).completionIdealImage 0) ∈ 𝓝 0 :=
    (continuous_const_mul _).tendsto' 0 0 (mul_zero _) <| prod_mem_nhds
      ((localizationUniform P {f, 1} 1 S₁ hden₁).hasBasis_nhds_zero_completion.mem_of_mem trivial)
      ((localizationUniform P {1} f S₂ hden₂).hasBasis_nhds_zero_completion.mem_of_mem trivial)
  refine ⟨_, hV, fun a ha ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_preimage, ← map_mul, Set.mem_prod] at ha
  -- the images of `ϖ⁻ⁿ a` then lie in the two rings of definition themselves
  simp only [ρ, RingHom.prod_apply, toCompletionLoc_apply, SetLike.mem_coe,
    coe_mem_completionIdealImage_iff, localizationUniform_idealImage, locIdealImage_zero,
    Subring.mem_toAddSubgroup] at ha
  -- so `ϖ⁻ⁿ a` is power-bounded, and `a = ϖⁿ (ϖ⁻ⁿ a) ∈ U`
  exact hn ⟨_, hv, _, isPowerBounded_of_algebraMap_mem_locSubring_laurentCover P f ha.1 ha.2,
    v.mul_inv_cancel_left a⟩

variable [CompleteSpace A] [T0Space A]

/-- **Buzzard–Verberkmoes, Lemma 2 and Corollary 4, strictness.** Let `A` be a complete Hausdorff
uniform Tate ring and `f ∈ A`. The map `A → A⟨U₁⟩ × A⟨U₂⟩`, `a ↦ (a, a)`, into the coordinate
rings of `U₁ = R({f, 1}/1) = {|f| ≤ 1}` and `U₂ = R({1}/f) = {|f| ≥ 1}` is a closed embedding:
it is injective, its image is closed, and the topology of `A` is the one induced from the
product. This is `isClosedEmbedding_laurentCover` with uniformity in place of strong
noetherianness. -/
theorem isClosedEmbedding_laurentCover_of_isUniform :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    IsClosedEmbedding
      (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂)) := by
  let hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  let _ := locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  set ρ := RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂)
  have hρ : Continuous ρ := (continuous_toCompletionLoc P {f, 1} 1 S₁ hden₁).prodMk
    (continuous_toCompletionLoc P {1} f S₂ hden₂)
  -- `A` has the topology induced from the product, and its image, being complete, is closed
  have hind : IsInducing ρ := IsTopologicalAddGroup.isInducing_iff_nhds_zero.2 <|
    le_antisymm (hρ.tendsto' 0 0 (map_zero ρ)).le_comap
      (comap_laurentCover_nhds_zero_le P f S₁ S₂ hden₂)
  exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding hind.isEmbedding).isClosedEmbedding

variable (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂]

/-- **Buzzard–Verberkmoes, Corollary 4, exactness in the middle.** Let `A` be a complete Hausdorff
uniform Tate ring and `f ∈ A`, and let `U₁ = R({f, 1}/1)`, `U₂ = R({1}/f)` and
`U₁ ∩ U₂ = R({f², f, 1}/(1 · f))`. In

```text
A → A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩,      a ↦ (a, a),      (x, y) ↦ x|U₁∩U₂ - y|U₁∩U₂,
```

the kernel of the second map is the image of the first. The restriction maps are those of the
refinements with cofactors `f` and `1`. The first map is injective, and even a closed embedding
(`isClosedEmbedding_laurentCover_of_isUniform`). Only `U₂` comes with a standing hypothesis: the
one for `U₁` is automatic at the denominator `1`
(`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_denom_one`), and the one for `U₁ ∩ U₂` is
built from those two by `TauCeti.Huber.PairOfDefinition.hasDenominatorPower_mul`. This is
`laurentCover_exact` with uniformity in place of strong noetherianness. -/
theorem laurentCover_exact_of_isUniform :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    Function.Exact
      (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂))
      ((restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.fst (UniformSpace.Completion S₁) (UniformSpace.Completion S₂)) -
        (restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f)
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.snd (UniformSpace.Completion S₁) (UniformSpace.Completion S₂))) := by
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ <|
    hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂ (by simp) (by simp)
      (hasDenominatorPower_denom_one P {f, 1} S₁) hden₂
  rintro ⟨x₁, x₂⟩
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.coe_fst, AddMonoidHom.coe_ofClass, AddMonoidHom.coe_snd, sub_eq_zero]
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- a pair agreeing on `U₁ ∩ U₂` lies in the closure of the image of `A`, which is closed
    exact (isClosedEmbedding_laurentCover_of_isUniform P f S₁ S₂ hden₂).isClosed_range
      |>.closure_subset (mem_closure_range_laurentCover P f S₁ S₂ hden₂ S₁₂ h)
  · -- both restrictions of the image of `a ∈ A` are the image of `a` in `A⟨U₁ ∩ U₂⟩`
    rintro ⟨a, rfl, rfl⟩
    simp only [← RingHom.comp_apply, restrictionRingHom_comp_toCompletionLoc]

end Uniform

end TauCeti.ValuationSpectrum
