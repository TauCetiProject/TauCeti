/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative maps, ring homomorphisms, and ring equivalences

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.

A ring homomorphism fixes natural number casts, so it preserves membership statements of the form
`n ^ k * x ∈ A`: if it maps `A` into `B`, then `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`. This
controls denominators under ring endomorphisms that preserve a subring, as in integrality arguments
for Hazewinkel's functional equation.

A ring equivalence `e : R ≃+* S` transports polynomial equations in both directions by applying
`e` and `e.symm`. In particular, it preserves solvability of the binary quadratic norm equation
`b = x² - a y²`, which transports Hilbert symbols and local and global quadratic norm equations
along field and completion isomorphisms.

Over an infinite field, two field endomorphisms whose `N`-th powers agree for some nonzero `N` are
equal (`RingHom.eq_of_pow_eq_pow`), and the product of their values on nonzero elements cannot
always be an `N`-th root of unity (`RingHom.false_of_pow_mul_eq_one`), since both conditions force
the field elements into a finite union of polynomial root sets.

## Main results

* `TauCeti.map_neg_one_eq_one_or_eq_neg_one`: the image of `-1` is `1` or `-1`.
* `Set.MapsTo.natCast_pow_mul_apply_mem`: if a ring homomorphism `f` maps `A` into `B`, then
  `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`.
* `Set.MapsTo.ringHom_pow`: if a ring endomorphism `f` maps `A` into itself, so does `f ^ n`.
* `RingEquiv.exists_eq_sq_sub_mul_sq_map_iff`: a ring equivalence preserves solvability of
  `b = x² - a y²`.
* `RingHom.false_of_pow_mul_eq_one` and `RingHom.eq_of_pow_eq_pow`: over an infinite field,
  endomorphisms cannot have `(g₁ x * g₂ x) ^ N = 1` on `Kˣ`, and `(g₁ x) ^ N = (g₂ x) ^ N` on
  `Kˣ` forces `g₁ = g₂`.
-/

public section

namespace TauCeti

/-- A multiplicative map into a ring without zero divisors sends `-1` to `1` or `-1`.
Only distributive negation and a multiplicative identity are required in the source; the target
ring need not be associative. -/
theorem map_neg_one_eq_one_or_eq_neg_one {F M R : Type*} [MulOneClass M] [HasDistribNeg M]
    [NonAssocRing R] [NoZeroDivisors R] [FunLike F M R] [MonoidHomClass F M R] (f : F) :
    f (-1) = 1 ∨ f (-1) = -1 :=
  mul_self_eq_one_iff.mp (by rw [← map_mul]; simp)

end TauCeti

namespace Set.MapsTo

/-- If a ring endomorphism `f` maps `A` into itself, then so does its power `f ^ n`, which is the
`n`-th iterate of `f`. -/
theorem ringHom_pow {R : Type*} [NonAssocSemiring R] {f : R →+* R} {A : Set R}
    (hf : MapsTo f A A) (n : ℕ) : MapsTo (f ^ n) A A := by
  rw [RingHom.coe_pow]
  exact hf.iterate n

/-- If a ring homomorphism `f` maps `A` into `B`, then `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`
for all natural numbers `n` and `k`, since `f` fixes `n ^ k`. No closure properties of `A` or `B`
are needed. -/
theorem natCast_pow_mul_apply_mem {R S F : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] {f : F} {A : Set R} {B : Set S} (hf : MapsTo f A B)
    {n k : ℕ} {x : R} (hx : (n : R) ^ k * x ∈ A) : (n : S) ^ k * f x ∈ B := by
  simpa only [map_mul, map_pow, map_natCast] using hf hx

end Set.MapsTo

namespace RingEquiv

-- Not `@[simp]`: the left-hand side is headed by `Exists`, which would index under a wildcard key.
/-- A ring isomorphism preserves solvability of the binary quadratic norm equation
`b = x² - a y²`. -/
theorem exists_eq_sq_sub_mul_sq_map_iff {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    (a b : R) :
    (∃ x y : S, e b = x ^ 2 - e a * y ^ 2) ↔ ∃ x y : R, b = x ^ 2 - a * y ^ 2 := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨e.symm x, e.symm y, e.injective (by simpa using h)⟩
  · rintro ⟨x, y, h⟩
    exact ⟨e x, e y, by simp [h]⟩

end RingEquiv

namespace RingHom

/-- Over an infinite field, two field endomorphisms `g₁, g₂` cannot satisfy
`(g₁ x * g₂ x) ^ N = 1` for all nonzero `x` and a nonzero natural number `N`. -/
theorem false_of_pow_mul_eq_one {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x * g₂ x) ^ N = 1) : False := by
  classical
  let R : Set K := ↑(Polynomial.nthRootsFinset N (1 : K))
  have hR : R.Finite := (Polynomial.nthRootsFinset N (1 : K)).finite_toSet
  have hR_iff (ζ : K) : ζ ∈ R ↔ ζ ^ N = 1 := by
    simp [R, Polynomial.nthRootsFinset_toSet (Nat.pos_of_ne_zero hN)]
  let qPoly : K × K → Polynomial K := fun p =>
    Polynomial.X ^ 2 - Polynomial.C (p.2 - 1 - p.1) * Polynomial.X + Polynomial.C p.1
  have hqPoly_ne (p : K × K) : qPoly p ≠ 0 := by
    intro h0
    have hc := congrArg (fun f : Polynomial K => f.coeff 2) h0
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_mul_X,
      Polynomial.coeff_C_of_ne_zero (by decide), Polynomial.coeff_C_of_ne_zero (by decide),
      Polynomial.coeff_zero] at hc
    simp at hc
  let Q : K × K → Set K := fun p => ↑(qPoly p).roots.toFinset
  have hQ (p : K × K) : (Q p).Finite := (qPoly p).roots.toFinset.finite_toSet
  have hU : (⋃ p ∈ R ×ˢ R, Q p).Finite := (hR.prod hR).biUnion fun p _ => hQ p
  let T : Set K := Set.univ \ ({0, -1} : Set K)
  have hsub : g₁ '' T ⊆ ⋃ p ∈ R ×ˢ R, Q p := by
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    have hx0 : x ≠ 0 := fun h0 => hx (Or.inl h0)
    have hx1 : 1 + x ≠ 0 := fun h1 => hx (Or.inr (eq_of_sub_eq_zero (by linear_combination h1)))
    refine Set.mem_biUnion (Set.mk_mem_prod ((hR_iff _).mpr (h x hx0))
      ((hR_iff _).mpr (h (1 + x) hx1))) ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots (hqPoly_ne _),
      Polynomial.IsRoot.def]
    simp only [qPoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, map_add, map_one]
    ring
  exact ((Set.infinite_univ.sdiff (Set.toFinite _)).image g₁.injective.injOn) (hU.subset hsub)

/-- Over an infinite field, two field endomorphisms whose `N`-th powers agree on all nonzero
elements for some `N ≠ 0` are equal. -/
theorem eq_of_pow_eq_pow {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x) ^ N = (g₂ x) ^ N) : g₁ = g₂ := by
  let R : Set K := ↑(Polynomial.nthRootsFinset N (1 : K))
  have hR : R.Finite := (Polynomial.nthRootsFinset N (1 : K)).finite_toSet
  have hR_iff (ζ : K) : ζ ∈ R ↔ ζ ^ N = 1 := by
    simp [R, Polynomial.nthRootsFinset_toSet (Nat.pos_of_ne_zero hN)]
  let E : K × K → Set K := fun p => {y : K | p.1 ≠ p.2 ∧ (p.1 - p.2) * y = p.2 - 1}
  have hE (p : K × K) : (E p).Finite := Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ => by
    have hdiff : (p.1 - p.2) * (y₁ - y₂) = 0 := by
      have h1 : (p.1 - p.2) * y₁ = p.2 - 1 := hy₁.2
      have h2 : (p.1 - p.2) * y₂ = p.2 - 1 := hy₂.2
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hy₁.1))
  let B : Set K := ⋃ p ∈ R ×ˢ R, E p
  have hB : B.Finite := (hR.prod hR).biUnion fun p _ => hE p
  let bad : Set K := {x : K | g₁ x ≠ g₂ x}
  have hratio (z : K) (hz : z ≠ 0) :
      g₁ z * (g₂ z)⁻¹ ∈ R ∧ g₁ z = (g₁ z * (g₂ z)⁻¹) * g₂ z := by
    have hg2z : g₂ z ≠ 0 := fun h0 => hz (g₂.injective (h0.trans (map_zero g₂).symm))
    exact ⟨(hR_iff _).mpr <| by
        rw [mul_pow, inv_pow, h z hz, mul_inv_cancel₀ (pow_ne_zero N hg2z)],
      (inv_mul_cancel_right₀ hg2z (g₁ z)).symm⟩
  have hbad_sub : bad ⊆ ({0, -1} : Set K) ∪ g₂ ⁻¹' B := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl (Or.inl hx0)
    by_cases hx1 : x = -1
    · exact Or.inl (Or.inr hx1)
    right
    have hx1' : 1 + x ≠ 0 := fun h1 => hx1 (eq_of_sub_eq_zero (by linear_combination h1))
    let ζ₁ : K := g₁ x * (g₂ x)⁻¹
    let ζ₂ : K := g₁ (1 + x) * (g₂ (1 + x))⁻¹
    have hζ₁ : ζ₁ ∈ R := (hratio x hx0).1
    have h1 : g₁ x = ζ₁ * g₂ x := (hratio x hx0).2
    have hζ₂ : ζ₂ ∈ R := (hratio (1 + x) hx1').1
    have h2' : g₁ (1 + x) = ζ₂ * g₂ (1 + x) := (hratio (1 + x) hx1').2
    have h2 : 1 + g₁ x = ζ₂ * (1 + g₂ x) := by
      rwa [map_add, map_one, map_add, map_one] at h2'
    have heq : (ζ₁ - ζ₂) * g₂ x = ζ₂ - 1 := by linear_combination h2 - h1
    have hne : ζ₁ ≠ ζ₂ := fun h12 => by
      rw [h12, sub_self, zero_mul] at heq
      rw [h12.trans (eq_of_sub_eq_zero heq.symm), one_mul] at h1
      exact hx h1
    exact Set.mem_biUnion (Set.mk_mem_prod hζ₁ hζ₂) ⟨hne, heq⟩
  have hbad : bad.Finite :=
    ((Set.toFinite _).union (hB.preimage g₂.injective.injOn)).subset hbad_sub
  refine RingHom.ext fun x => ?_
  obtain ⟨y, hy⟩ := (Set.infinite_univ.sdiff (hbad.union (hbad.image (fun z => z - x)))).nonempty
  have hgy : g₁ y = g₂ y := not_not.mp fun hmem => hy.2 (Or.inl hmem)
  have hgxy : g₁ (x + y) = g₂ (x + y) := not_not.mp fun hmem => hy.2 (Or.inr ⟨x + y, hmem, by ring⟩)
  rw [map_add, map_add, hgy] at hgxy
  exact add_right_cancel hgxy

end RingHom
