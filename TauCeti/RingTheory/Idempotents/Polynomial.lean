/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Idempotents.Jacobson

/-!
# Idempotents modulo an ideal from coprime factorizations

Let `I` be an ideal of a commutative ring `R`, let `S` be an `R`-algebra, and let `s : S` be
idempotent modulo `IS`. Suppose `a g + b h = 1` over `R`, where `g ≡ Xᵐ⁺¹` and `h ≡ (X - 1)ⁿ⁺¹`
modulo `I`. Then `a(s) g(s) ≡ s` modulo `IS`
(`Ideal.aeval_mul_sub_mem_map_of_add_eq_one`). When moreover `g h` annihilates `s`, the element
`a(s) g(s)` is an idempotent of `S`, so this is how lifts of factorizations of a monic
polynomial over `R ⧸ I` produce lifts of idempotents.
-/

public section

open Polynomial

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) {S : Type*} [CommRing S] [Algebra R S]

/-- Let `a g + b h = 1` over `R` with `g ≡ Xᵐ⁺¹` and `h ≡ (X - 1)ⁿ⁺¹` modulo `I`, and let `s` be
idempotent modulo `IS`. Then `a(s) g(s) ≡ s` modulo `IS`: there `g(s) ≡ sᵐ⁺¹ = s` and
`h(s) s ≡ (s - 1)ⁿ⁺¹ s = 0`. -/
theorem aeval_mul_sub_mem_map_of_add_eq_one {s : S}
    (hs : s * s - s ∈ I.map (algebraMap R S)) {a b g h : R[X]} {m n : ℕ}
    (hab : a * g + b * h = 1) (hgmap : g.map (Ideal.Quotient.mk I) = X ^ (m + 1))
    (hhmap : h.map (Ideal.Quotient.mk I) = (X - C 1) ^ (n + 1)) :
    aeval s (a * g) - s ∈ I.map (algebraMap R S) := by
  set J := I.map (algebraMap R S)
  set φ : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J (algebraMap R S) Ideal.le_comap_map
  set t := Ideal.Quotient.mk J s
  have hφ (f : R[X]) :
      Ideal.Quotient.mk J (aeval s f) = (f.map (Ideal.Quotient.mk I)).eval₂ φ t := by
    rw [aeval_def, hom_eval₂, eval₂_map, Ideal.quotientMap_comp_mk]
  have ht : IsIdempotentElem t := Ideal.Quotient.isIdempotentElem_mk_iff.mpr hs
  have htt : (t - 1) ^ (n + 1) * t = 0 := by
    rw [pow_succ, mul_assoc, sub_mul, one_mul, ht.eq, sub_self, mul_zero]
  have hab' := congrArg (fun f : R[X] ↦ (f.map (Ideal.Quotient.mk I)).eval₂ φ t) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, hgmap, hhmap, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_sub, eval₂_X, map_one, Polynomial.map_one, eval₂_one] at hab'
  rw [← Ideal.Quotient.eq, hφ, Polynomial.map_mul, eval₂_mul, hgmap, eval₂_X_pow]
  linear_combination t * hab' - (eval₂ φ t (b.map (Ideal.Quotient.mk I))) * htt +
    (eval₂ φ t (a.map (Ideal.Quotient.mk I))) * (1 - t) * ht.pow_succ_eq m -
    (eval₂ φ t (a.map (Ideal.Quotient.mk I))) * ht.eq

end Ideal
