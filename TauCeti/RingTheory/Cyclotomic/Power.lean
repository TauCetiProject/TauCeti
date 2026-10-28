/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# Coprime power substitutions on exact cyclotomic integers

Substitution `ζ_e ↦ ζ_e ^ n`, for `n` coprime to `e`, preserves the cyclotomic relation.
The resulting ring homomorphism is computed by Horner evaluation of coefficient vectors.
Evaluation at another cyclotomic root intertwines it with the same power substitution on that
root. This allows all conjugate residues to be recovered from one reduction.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.
-/

public section

namespace TauCeti.Cyclotomic

variable {e n : ℕ} [NeZero e]

/-- For `n` coprime to `e`, the power `ζ_e ^ n` of the distinguished generator is a root of the
cyclotomic polynomial `Φ_e`, so `TauCeti.Cyclotomic.evalRingHom` can evaluate at it. -/
theorem eval₂_cyclotomic_zeta_pow (hn : e.Coprime n) :
    (Polynomial.cyclotomic e ℤ).eval₂ (Int.castRingHom (Cyclotomic e)) (zeta e ^ n) = 0 := by
  apply complexEmbedding_injective
  rw [Polynomial.hom_eval₂, map_pow, complexEmbedding_zeta, map_zero]
  exact (isPrimitiveRoot_complexRoot.pow_of_coprime n hn.symm).eval₂_cyclotomic _

/-- The computable coprime power substitution `ζ_e ↦ ζ_e ^ n`. -/
def powRingHom (hn : e.Coprime n) : Cyclotomic e →+* Cyclotomic e where
  toFun := evalCoeffs (Int.castRingHom (Cyclotomic e)) (zeta e ^ n)
  map_one' := by
    rw [← evalRingHom_eq_evalCoeffs _ _ (eval₂_cyclotomic_zeta_pow hn)]
    exact map_one _
  map_zero' := by
    rw [← evalRingHom_eq_evalCoeffs _ _ (eval₂_cyclotomic_zeta_pow hn)]
    exact map_zero _
  map_add' x y := by
    simp only [← evalRingHom_eq_evalCoeffs _ _ (eval₂_cyclotomic_zeta_pow hn)]
    exact map_add _ x y
  map_mul' x y := by
    simp only [← evalRingHom_eq_evalCoeffs _ _ (eval₂_cyclotomic_zeta_pow hn)]
    exact map_mul _ x y

/-- Power substitution evaluates the canonical coefficient vector at `ζ_e ^ n`. -/
theorem powRingHom_apply (hn : e.Coprime n) (x : Cyclotomic e) :
    powRingHom hn x = evalCoeffs (Int.castRingHom (Cyclotomic e)) (zeta e ^ n) x := (rfl)

/-- Power substitution sends the distinguished generator to its specified power. -/
@[simp]
theorem powRingHom_zeta (hn : e.Coprime n) : powRingHom hn (zeta e) = zeta e ^ n := by
  rw [powRingHom_apply, ← evalRingHom_eq_evalCoeffs _ _ (eval₂_cyclotomic_zeta_pow hn)]
  exact evalRingHom_zeta _ _ _

/-- A ring homomorphism intertwines power substitution with evaluation at the powered image
of the distinguished generator. The target ring need not be commutative. -/
theorem map_powRingHom {R : Type*} [Ring R] (hn : e.Coprime n)
    (φ : Cyclotomic e →+* R) (x : Cyclotomic e) :
    φ (powRingHom hn x) = evalCoeffs (Int.castRingHom R) (φ (zeta e) ^ n) x := by
  rw [powRingHom_apply, RingHom.map_evalCoeffs]
  congr 1
  · exact RingHom.ext_int _ _
  · exact map_pow _ _ _

/-- Reduction at a root of the cyclotomic polynomial, over any modulus, intertwines power
substitution with powering the root. -/
@[simp]
theorem reduce_powRingHom {p : ℕ} (hn : e.Coprime n)
    {α : ZMod p}
    (hα : (Polynomial.cyclotomic e ℤ).eval₂ (Int.castRingHom (ZMod p)) α = 0)
    (x : Cyclotomic e) :
    reduce p α (powRingHom hn x) = reduce p (α ^ n) x := by
  rw [reduce, ← evalRingHom_eq_evalCoeffs _ _ hα, map_powRingHom,
    evalRingHom_zeta, reduce]

end TauCeti.Cyclotomic
