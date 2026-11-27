/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Group.Hom.Finite

/-!
# Rigidity of field endomorphisms with equal pointwise powers

Over an infinite field `K`, two field endomorphisms `g₁, g₂ : K →+* K` whose pointwise `N`-th
powers `(g₁ x) ^ N` and `(g₂ x) ^ N` agree on all nonzero `x : K` for some `N ≠ 0` are equal
(`RingHom.eq_of_forall_apply_pow_eq`), and the product `(g₁ x * g₂ x) ^ N` cannot equal `1` on
all nonzero `x` (`RingHom.not_forall_mul_apply_pow_eq_one`).

Both arguments restrict attention to the disagreement set `{x | g₁ x ≠ g₂ x}` (respectively
`Set.univ \ {0, -1}`): evaluating on `x` and `1 + x` forces `g₁ x` or `g₂ x` into a finite union
of polynomial root sets indexed by pairs of `N`-th roots of unity, so in the equality proof the
disagreement set `{x | g₁ x ≠ g₂ x}` is finite, and additivity on an infinite group yields
`g₁ = g₂`.

## Main results

* `RingHom.not_forall_mul_apply_pow_eq_one`: over an infinite field, `(g₁ x * g₂ x) ^ N = 1`
  cannot hold for all nonzero `x` and a nonzero `N`.
* `RingHom.eq_of_forall_apply_pow_eq`: over an infinite field, `(g₁ x) ^ N = (g₂ x) ^ N` for all
  nonzero `x` and some `N ≠ 0` implies `g₁ = g₂`.
-/

public section

namespace RingHom

/-- Over an infinite field, two field endomorphisms `g₁, g₂` cannot satisfy pointwise relations
`(g₁ x * g₂ x) ^ N = 1` for all nonzero `x` and a nonzero natural number `N`. -/
theorem not_forall_mul_apply_pow_eq_one {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0) :
    ¬ ∀ x : K, x ≠ 0 → (g₁ x * g₂ x) ^ N = 1 := by
  classical
  intro h
  let R : Set K := {ζ : K | ζ ^ N = 1}
  have hR : R.Finite := by
    rw [show R = ↑(Polynomial.nthRootsFinset N (1 : K)) from
      (Polynomial.nthRootsFinset_toSet (Nat.pos_of_ne_zero hN) 1).symm]
    exact Finset.finite_toSet _
  let qPoly : K × K → Polynomial K := fun p =>
    Polynomial.X ^ 2 - Polynomial.C (p.2 - 1 - p.1) * Polynomial.X + Polynomial.C p.1
  have hqPoly_ne (p : K × K) : qPoly p ≠ 0 :=
    Polynomial.Monic.ne_zero (by dsimp only [qPoly]; monicity!)
  let Q : K × K → Set K := fun p => ↑(qPoly p).roots.toFinset
  have hQ (p : K × K) : (Q p).Finite := (qPoly p).roots.toFinset.finite_toSet
  have hU : (⋃ p ∈ R ×ˢ R, Q p).Finite := (hR.prod hR).biUnion fun p _ => hQ p
  let T : Set K := Set.univ \ ({0, -1} : Set K)
  have hsub : g₁ '' T ⊆ ⋃ p ∈ R ×ˢ R, Q p := by
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    have hx0 : x ≠ 0 := fun h0 => hx (Or.inl h0)
    have hx1 : 1 + x ≠ 0 := fun h1 => hx (Or.inr (eq_of_sub_eq_zero (by linear_combination h1)))
    refine Set.mem_biUnion (Set.mk_mem_prod (h x hx0) (h (1 + x) hx1)) ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots (hqPoly_ne _),
      Polynomial.IsRoot.def]
    simp only [qPoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, map_add, map_one]
    ring
  exact ((Set.infinite_univ.sdiff (Set.toFinite _)).image g₁.injective.injOn) (hU.subset hsub)

/-- Over an infinite field, two field endomorphisms whose pointwise `N`-th powers agree on all
nonzero elements (`(g₁ x) ^ N = (g₂ x) ^ N`) for some `N ≠ 0` are equal. -/
theorem eq_of_forall_apply_pow_eq {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x) ^ N = (g₂ x) ^ N) : g₁ = g₂ := by
  let R : Set K := {ζ : K | ζ ^ N = 1}
  have hR : R.Finite := by
    rw [show R = ↑(Polynomial.nthRootsFinset N (1 : K)) from
      (Polynomial.nthRootsFinset_toSet (Nat.pos_of_ne_zero hN) 1).symm]
    exact Finset.finite_toSet _
  let E : K × K → Set K := fun p => {y : K | p.1 ≠ p.2 ∧ (p.1 - p.2) * y = p.2 - 1}
  have hE (p : K × K) : (E p).Finite := Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ => by
    have hdiff : (p.1 - p.2) * (y₁ - y₂) = 0 := by
      have h1 : (p.1 - p.2) * y₁ = p.2 - 1 := hy₁.2
      have h2 : (p.1 - p.2) * y₂ = p.2 - 1 := hy₂.2
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hy₁.1))
  let B : Set K := ⋃ p ∈ R ×ˢ R, E p
  have hB : B.Finite := (hR.prod hR).biUnion fun p _ => hE p
  have hratio (z : K) (hz : z ≠ 0) :
      g₁ z * (g₂ z)⁻¹ ∈ R ∧ g₁ z = (g₁ z * (g₂ z)⁻¹) * g₂ z := by
    have hg2z : g₂ z ≠ 0 := fun h0 => hz (g₂.injective (h0.trans (map_zero g₂).symm))
    refine ⟨Set.mem_ofPred.mpr ?_, (inv_mul_cancel_right₀ hg2z (g₁ z)).symm⟩
    rw [mul_pow, inv_pow, h z hz, mul_inv_cancel₀ (pow_ne_zero N hg2z)]
  -- Every disagreement outside `{0, -1}` forces `g₂ x` into `B` via the `N`-th roots `ζ₁, ζ₂`.
  have hbad_sub : {x : K | g₁ x ≠ g₂ x} ⊆ ({0, -1} : Set K) ∪ g₂ ⁻¹' B := by
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
  have hfin : {x : K | g₁ x ≠ g₂ x}.Finite :=
    ((Set.toFinite _).union (hB.preimage g₂.injective.injOn)).subset hbad_sub
  exact RingHom.toAddMonoidHom_injective <|
    AddMonoidHom.eq_of_finite_setOf_ne g₁.toAddMonoidHom g₂.toAddMonoidHom hfin

end RingHom
