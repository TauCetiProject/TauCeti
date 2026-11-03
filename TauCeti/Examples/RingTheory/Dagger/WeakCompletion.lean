/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Dagger.WeakCompletion.Surjective
import Mathlib.Data.ZMod.Basic

/-!
# Checks for maps of weak completions

Evaluation at zero and one, substitution of a square, and polynomial retraction test the
induced maps. The retraction and identity checks apply to arbitrary weakly completed
elements, not just polynomials in the original algebra. The base ring and parameter are
arbitrary, so the checks apply in positive characteristic and with nilpotents as well.
Surjectivity is tested on polynomial presentations and quotients, including a nonreduced
quotient and reduction modulo four with nilpotent parameter two.
-/

namespace TauCeti.Dagger

variable {O S : Type*} [CommRing O] [CommRing S] [Algebra O S]
  [Algebra.FiniteType O S] (π : O)

open weakCompletion

-- Both evaluations retract inclusion, even on nonalgebraic weakly completed elements.
example (z : weakCompletion π S) :
    map π ((Polynomial.aeval (0 : S)).restrictScalars O)
      (map π (IsScalarTower.toAlgHom O S (Polynomial S)) z) = z :=
  leftInverse_map_aeval π 0 z

example (z : weakCompletion π S) :
    map π ((Polynomial.aeval (1 : S)).restrictScalars O)
      (map π (IsScalarTower.toAlgHom O S (Polynomial S)) z) = z :=
  leftInverse_map_aeval π 1 z

-- The constant inclusion is injective, without separatedness of the original algebra.
example : Function.Injective
    (map π (IsScalarTower.toAlgHom O S (Polynomial S))) :=
  (leftInverse_map_aeval π (0 : S)).injective

-- The weak coordinate has the correct values at zero and at one.
example : map π ((Polynomial.aeval (0 : S)).restrictScalars O)
    (of π (Polynomial S) Polynomial.X) = 0 := by
  simpa only [AlgHom.restrictScalars_apply, Polynomial.aeval_X, map_zero] using
    map_of π ((Polynomial.aeval (R := S) (0 : S)).restrictScalars O) Polynomial.X

example : map π ((Polynomial.aeval (1 : S)).restrictScalars O)
    (of π (Polynomial S) Polynomial.X) = 1 := by
  simpa only [AlgHom.restrictScalars_apply, Polynomial.aeval_X, map_one] using
    map_of π ((Polynomial.aeval (R := S) (1 : S)).restrictScalars O) Polynomial.X

-- A ramified substitution is permitted: weak-completion functoriality requires no étaleness.
example : map π ((Polynomial.aeval (Polynomial.X ^ 2 : Polynomial S)).restrictScalars O)
    (of π (Polynomial S) Polynomial.X) = of π (Polynomial S) (Polynomial.X ^ 2) := by
  simpa only [AlgHom.restrictScalars_apply, Polynomial.aeval_X] using
    map_of π ((Polynomial.aeval (R := S) (Polynomial.X ^ 2 : Polynomial S)).restrictScalars O)
      Polynomial.X

example (z : weakCompletion π S) : map π (AlgHom.id O S) z = z := by
  rw [map_id]
  rfl

-- Polynomial presentations lift every weakly completed element, not merely polynomials.
example {ι : Type*} [Finite ι] (x : ι → S)
    (hx : Algebra.adjoin O (Set.range x) = ⊤) (z : weakCompletion π S) :
    ∃ w : weakCompletion π (MvPolynomial ι O), map π (MvPolynomial.aeval x) w = z :=
  map_aeval_surjective π x hx z

-- Arbitrary quotient ideals are allowed; no flatness or radicality is assumed.
example (I : Ideal (Polynomial O)) (z : weakCompletion π (Polynomial O ⧸ I)) :
    ∃ w : weakCompletion π (Polynomial O), map π (Ideal.Quotient.mkₐ O I) w = z :=
  map_surjective π (Ideal.Quotient.mkₐ O I) Ideal.Quotient.mk_surjective z

-- In particular the squared-origin thickening has a surjective weak presentation.
example (z : weakCompletion π (Polynomial O ⧸ Ideal.span {(Polynomial.X : Polynomial O) ^ 2})) :
    ∃ w : weakCompletion π (Polynomial O),
      map π (Ideal.Quotient.mkₐ O (Ideal.span {Polynomial.X ^ 2})) w = z :=
  map_surjective π _ Ideal.Quotient.mk_surjective z

-- The lifted map still kills the defining relation on the original polynomial algebra.
example : map π (Ideal.Quotient.mkₐ O (Ideal.span {Polynomial.X ^ 2}))
    (of π (Polynomial O) (Polynomial.X ^ 2)) = 0 := by
  rw [map_of, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _)), map_zero]

-- Reduction modulo four is nonflat over ℤ; parameter two becomes nilpotent in the target.
example (z : weakCompletion (2 : ℤ) (Polynomial (ZMod 4))) :
    ∃ w : weakCompletion (2 : ℤ) (Polynomial ℤ),
      map 2 (Polynomial.mapAlgHom (Algebra.ofId ℤ (ZMod 4))) w = z := by
  apply map_surjective
  exact Polynomial.map_surjective _ (ZMod.intCast_surjective :
    Function.Surjective (Int.cast : ℤ → ZMod 4))

end TauCeti.Dagger
