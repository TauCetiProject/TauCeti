/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PinnedMultiplication

/-!
# Producing derivations of the type-F4 multiplication from the simple root generators

The eight numbered simple root generators of the twenty-six-dimensional module of type `F₄`
differentiate its invariant symmetric multiplication. This file records the two operations that
produce further derivations from them, over a ring of characteristic two: the commutator with a
generator, and the divided adjoint of a generator.

The commutator is available because the derivations are closed under it. The divided adjoint is
not a commutator, and it is needed because a long root vector is reached from a short one only by a
divided power. It appears here as conjugation by a numbered simple root element of parameter one,
an involution in characteristic two whose conjugation action preserves the derivations; removing
the terms of degree zero and one in the expansion of that conjugation leaves the six products of
the divided adjoint.

Both operations are stated up to congruence modulo two, because the integral matrices they produce
represent the target only after reduction.

## Main results

* `TauCeti.F4ShortRoot.map_intCast_eq_of_modEq`: integer matrices congruent entry by entry modulo
  two have the same image in a ring of characteristic two.
* `TauCeti.F4ShortRoot.isDerivation_of_bracket_congr`: the commutator with a numbered simple root
  generator.
* `TauCeti.F4ShortRoot.isDerivation_of_conjugation_congr`: the divided adjoint of a numbered simple
  root generator.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §§2 and 11.
* B. Kostant, *Groups over `ℤ`*, Proc. Sympos. Pure Math. **IX** (1966).
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R]

variable [CharP R 2]

/-- **Integer matrices congruent entry by entry modulo two have the same image** in a ring of
characteristic two. -/
theorem map_intCast_eq_of_modEq {M M' : Matrix (Fin 26) (Fin 26) ℤ}
    (h : ∀ a b, M a b ≡ M' a b [ZMOD 2]) :
    M.map (Int.cast : ℤ → R) = M'.map (Int.cast : ℤ → R) := by
  ext a b
  rw [Matrix.map_apply, Matrix.map_apply]
  exact (CharP.intCast_eq_intCast R 2).mpr (h a b)

/-- **Commuting a derivation with a numbered simple root generator.** If an integer matrix
differentiates the multiplication modulo two, so does any integer matrix congruent modulo two to
its commutator with a numbered simple root generator. -/
theorem isDerivation_of_bracket_congr (k : Fin 4 ⊕ Fin 4) {M M' : Matrix (Fin 26) (Fin 26) ℤ}
    (hM : IsDerivation (M.map (Int.cast : ℤ → R)))
    (h : ∀ a b, (rootMatrix k * M - M * rootMatrix k) a b ≡ M' a b [ZMOD 2]) :
    IsDerivation (M'.map (Int.cast : ℤ → R)) := by
  have hbr := ((isDerivation_rootMatrix k).map (R := R)).bracket hM
  rwa [← Matrix.map_intCast_mul, ← Matrix.map_intCast_mul, ← Matrix.map_sub _ Int.cast_sub,
    map_intCast_eq_of_modEq (R := R) h] at hbr

/-- **The divided adjoint of a derivation by a numbered simple root generator.** Conjugating by the
numbered simple root element of parameter one, an involution in characteristic two, preserves the
derivations; removing the terms of degree zero and one in that conjugation leaves the six products
below. -/
theorem isDerivation_of_conjugation_congr (k : Fin 4 ⊕ Fin 4)
    {M M' : Matrix (Fin 26) (Fin 26) ℤ} (hM : IsDerivation (M.map (Int.cast : ℤ → R)))
    (h : ∀ a b, (rootDividedSquareMatrix k * M + M * rootDividedSquareMatrix k +
        rootMatrix k * M * rootMatrix k + rootMatrix k * M * rootDividedSquareMatrix k +
        rootDividedSquareMatrix k * M * rootMatrix k +
        rootDividedSquareMatrix k * M * rootDividedSquareMatrix k) a b ≡ M' a b [ZMOD 2]) :
    IsDerivation (M'.map (Int.cast : ℤ → R)) := by
  have hgg : rootElementMatrix k (1 : R) * rootElementMatrix k 1 = 1 :=
    rootElementMatrix_mul_self k 1
  have hconj : IsDerivation
      (rootElementMatrix k (1 : R) * M.map (Int.cast : ℤ → R) * rootElementMatrix k 1) :=
    hM.conj (preservesMultiplication_rootElementMatrix k 1) hgg hgg
  have hbr := ((isDerivation_rootMatrix k).map (R := R)).bracket hM
  have key := (hconj.sub hM).sub hbr
  have hge : rootElementMatrix k (1 : R) = 1 + (rootMatrix k).map (Int.cast : ℤ → R) +
      (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) := by
    rw [rootElementMatrix_def, one_smul, one_pow, one_smul]
  have hself : ∀ A : Matrix (Fin 26) (Fin 26) R, A + A = 0 := fun A => by
    ext a b
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hexp : rootElementMatrix k (1 : R) * M.map (Int.cast : ℤ → R) * rootElementMatrix k 1 -
      M.map (Int.cast : ℤ → R) -
      ((rootMatrix k).map (Int.cast : ℤ → R) * M.map (Int.cast : ℤ → R) -
        M.map (Int.cast : ℤ → R) * (rootMatrix k).map (Int.cast : ℤ → R)) =
      ((rootDividedSquareMatrix k).map (Int.cast : ℤ → R) * M.map (Int.cast : ℤ → R) +
          M.map (Int.cast : ℤ → R) * (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) +
          (rootMatrix k).map (Int.cast : ℤ → R) * M.map (Int.cast : ℤ → R) *
            (rootMatrix k).map (Int.cast : ℤ → R) +
          (rootMatrix k).map (Int.cast : ℤ → R) * M.map (Int.cast : ℤ → R) *
            (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) +
          (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) * M.map (Int.cast : ℤ → R) *
            (rootMatrix k).map (Int.cast : ℤ → R) +
          (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) * M.map (Int.cast : ℤ → R) *
            (rootDividedSquareMatrix k).map (Int.cast : ℤ → R)) +
        (M.map (Int.cast : ℤ → R) * (rootMatrix k).map (Int.cast : ℤ → R) +
          M.map (Int.cast : ℤ → R) * (rootMatrix k).map (Int.cast : ℤ → R)) := by
    rw [hge]
    noncomm_ring
  rw [hexp, hself, add_zero] at key
  simp only [← Matrix.map_intCast_mul, ← Matrix.map_add _ Int.cast_add] at key
  rwa [map_intCast_eq_of_modEq (R := R) h] at key

end TauCeti.F4ShortRoot
