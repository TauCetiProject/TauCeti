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

/-- A coprime power of the distinguished exact generator annihilates the cyclotomic polynomial. -/
theorem eval₂_cyclotomic_zeta_pow (hn : e.Coprime n) :
    (Polynomial.cyclotomic e ℤ).eval₂ (Int.castRingHom (Cyclotomic e)) (zeta e ^ n) = 0 := by
  apply complexEmbedding_injective
  rw [Polynomial.hom_eval₂, map_pow, complexEmbedding_zeta, map_zero]
  have hcomp : complexEmbedding.comp (Int.castRingHom (Cyclotomic e)) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  rw [hcomp, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
  exact (isPrimitiveRoot_complexRoot.pow_of_coprime n hn.symm).isRoot_cyclotomic
    (NeZero.pos e)

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
of the distinguished generator. -/
theorem map_powRingHom {R : Type*} [CommRing R] (hn : e.Coprime n)
    (φ : Cyclotomic e →+* R) (x : Cyclotomic e) :
    φ (powRingHom hn x) = evalCoeffs (Int.castRingHom R) (φ (zeta e) ^ n) x := by
  rw [powRingHom_apply, evalCoeffs_eq_eval₂, Polynomial.hom_eval₂, evalCoeffs_eq_eval₂]
  congr 1
  · exact RingHom.ext_int _ _
  · exact map_pow _ _ _

/-- Reduction after power substitution is reduction at the powered primitive root. -/
@[simp]
theorem reduce_powRingHom {p : ℕ} [Fact p.Prime] (hn : e.Coprime n)
    {α : ZMod p} (hα : IsPrimitiveRoot α e) (x : Cyclotomic e) :
    reduce p α (powRingHom hn x) = reduce p (α ^ n) x := by
  rw [← reduceRingHom_apply p α hα]
  rw [map_powRingHom, reduceRingHom_apply, reduce_zeta p α hα, reduce]

end TauCeti.Cyclotomic
