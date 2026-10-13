/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# Complex conjugation on exact cyclotomic integers

For positive `e`, complex conjugation preserves `ℤ[ζ_e]` and is determined by
`ζ_e ↦ ζ_e⁻¹ = ζ_e ^ (e - 1)`.  This file implements that substitution directly on the
coefficient-vector type `TauCeti.Cyclotomic e`, proves that it agrees with complex conjugation
under the distinguished embedding into `ℂ`, and equips the exact ring with its canonical
star-ring structure.

The operation is a genuine computation: it evaluates the canonical coefficient list at
`ζ_e ^ (e - 1)` using `TauCeti.Cyclotomic.evalCoeffs`.  In particular, exact Hermitian products
can be checked before any passage to `ℂ`; this is needed by the cyclotomic stage of the
Burnside--Dixon--Schneider character-table solver.

## Main definitions

* `TauCeti.Cyclotomic.instStar`: computable conjugation on exact cyclotomic integers, given by the
  substitution `ζ_e ↦ ζ_e ^ (e - 1)`.
* `TauCeti.Cyclotomic.instStarRing`: the canonical star-ring structure, including the zero ring
  at conductor zero.

## Main results

* `TauCeti.Cyclotomic.star_def`: `star` evaluates the canonical coefficient vector at
  `ζ_e ^ (e - 1)`.
* `TauCeti.Cyclotomic.star_zeta`: conjugation sends `ζ_e` to `ζ_e ^ (e - 1)`.
* `TauCeti.Cyclotomic.complexEmbedding_star`: the distinguished complex embedding intertwines
  exact and complex conjugation.
* `RingHom.map_star_eq_evalCoeffs`: a ring homomorphism evaluates conjugates at the `(e - 1)`-st
  power of the image of `ζ_e`.
* `TauCeti.Cyclotomic.reduce_star`: reducing a conjugate at a cyclotomic root `r` is reduction of
  the original exact integer at `r ^ (e - 1)`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 2, Corollary 2.14 and Lemma 2.15(d),
  for row orthogonality and complex conjugation of character values.
-/

public section

namespace TauCeti.Cyclotomic

variable {e : ℕ}

/-- `star` on exact cyclotomic integers evaluates the canonical coefficient vector after replacing
`ζ_e` by `ζ_e ^ (e - 1)`.  For positive `e` this power is `ζ_e⁻¹`, so the substitution is complex
conjugation on exact `e`-th cyclotomic integers. -/
instance instStar : Star (Cyclotomic e) where
  star x := evalCoeffs (Int.castRingHom (Cyclotomic e)) (zeta e ^ (e - 1)) x

/-- `star` is the computable substitution `ζ_e ↦ ζ_e ^ (e - 1)`: it evaluates the canonical
coefficient vector at that power.  This is the defining equation of `Star (Cyclotomic e)`; it is
not `simp`, since it unfolds into coefficient lists. -/
theorem star_def (x : Cyclotomic e) :
    star x = evalCoeffs (Int.castRingHom (Cyclotomic e)) (zeta e ^ (e - 1)) x :=
  rfl

/-- A ring homomorphism evaluates conjugates at the `(e - 1)`-st power of the image of the
distinguished generator. The target ring need not be commutative or carry a star operation. -/
theorem _root_.RingHom.map_star_eq_evalCoeffs {R : Type*} [Ring R]
    (f : Cyclotomic e →+* R) (x : Cyclotomic e) :
    f (star x) = evalCoeffs (Int.castRingHom R) (f (zeta e) ^ (e - 1)) x := by
  rw [star_def, RingHom.map_evalCoeffs]
  congr 1
  · exact RingHom.ext_int _ _
  · exact map_pow _ _ _

/-- **The distinguished complex embedding intertwines exact conjugation with complex
conjugation.** -/
@[simp]
theorem complexEmbedding_star [NeZero e] (x : Cyclotomic e) :
    complexEmbedding (star x) = star (complexEmbedding x) := by
  rw [RingHom.map_star_eq_evalCoeffs, complexEmbedding_zeta]
  simp only [complexEmbedding_apply, Polynomial.aeval_def,
    algebraMap_int_eq, evalCoeffs_eq_eval₂]
  rw [← starRingEnd_apply, Polynomial.hom_eval₂]
  congr 1
  · exact RingHom.ext_int _ _
  · exact (conj_complexRoot_eq_pow_sub_one (e := e)).symm

/-- Computable conjugation makes exact cyclotomic integers a star ring, including the zero ring
at conductor zero. -/
instance instStarRing : StarRing (Cyclotomic e) := by
  -- Split only the laws, so the star projection remains the primitive computable operation.
  have laws : Function.Involutive (star : Cyclotomic e → Cyclotomic e) ∧
      (∀ x y : Cyclotomic e, star (x + y) = star x + star y) ∧
      (∀ x y : Cyclotomic e, star (x * y) = star y * star x) := by
    by_cases he : e = 0
    · subst e
      exact ⟨fun x => ext fun j => Fin.elim0 j,
        fun x y => ext fun j => Fin.elim0 j, fun x y => ext fun j => Fin.elim0 j⟩
    · have : NeZero e := ⟨he⟩
      let transported : StarRing (Cyclotomic e) :=
        complexEmbedding_injective.starRing complexEmbedding complexEmbedding_star
          complexEmbedding.map_add complexEmbedding.map_mul
      exact ⟨transported.star_involutive, transported.star_add, transported.star_mul⟩
  exact { star_involutive := laws.1, star_add := laws.2.1, star_mul := laws.2.2 }

/-- Conjugation sends the distinguished generator to `ζ_e ^ (e - 1)`. -/
@[simp]
theorem star_zeta : star (zeta e) = zeta e ^ (e - 1) := by
  by_cases he : e = 0
  · subst e
    decide
  · have : NeZero e := ⟨he⟩
    apply complexEmbedding_injective
    simpa only [complexEmbedding_star, complexEmbedding_zeta, map_pow, starRingEnd_apply] using
      (conj_complexRoot_eq_pow_sub_one (e := e))

/-- **Reduction intertwines `star` with passing to the `(e - 1)`-st power of the chosen cyclotomic
root.** Reducing `star x` at `r` is the same as reducing `x` at `r ^ (e - 1)`, which for positive
`e` and primitive `r` is `r⁻¹`. This is the exact relation between conjugate cyclotomic entries
and the residue tuples used by the Dixon lift. -/
theorem reduce_star (p : ℕ) (r : ZMod p)
    (hr : (Polynomial.cyclotomic e ℤ).eval₂ (Int.castRingHom (ZMod p)) r = 0)
    (x : Cyclotomic e) :
    reduce p r (star x) = reduce p (r ^ (e - 1)) x := by
  rw [reduce, ← evalRingHom_eq_evalCoeffs _ _ hr, RingHom.map_star_eq_evalCoeffs,
    evalRingHom_zeta, reduce]

/-! The exact operation reduces in the kernel. -/

example : star (zeta 3) = zeta 3 ^ 2 := by decide

example : star (zeta 4 + 1) = -(zeta 4) + 1 := by decide

end TauCeti.Cyclotomic
