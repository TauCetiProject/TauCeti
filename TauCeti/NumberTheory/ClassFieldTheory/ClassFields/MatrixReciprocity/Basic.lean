/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower
public import TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Quotient

/-!
# Multiplication-matrix Galois actions on ray class fields

For a number field `K`, a positive natural number `N`, and any ring isomorphism
`e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b`, combining the relative ray-class reciprocity of
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower` with the multiplication-matrix
presentation of `TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Quotient` expresses the Galois
group `Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)` and its relative norm in
terms of multiplication matrices:

* `TauCeti.ClassFieldTheory.periodMatrixQuotientArtinEquiv`: group isomorphism
  `periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N ≃*
  Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)` with explicit Artin evaluation
  (`restrictScalars_periodMatrixQuotientArtinEquiv_mk`,
  `periodMatrixQuotientArtinEquiv_mk_apply`) and norm product
  (`algebraMap_norm_hilbertClassField_periodMatrixQuotient`).

For the level-`2` and unipotent level-`3` specializations when `discr a b < -4`, see
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MatrixReciprocity.LevelTwo` and
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MatrixReciprocity.LevelThree`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §§9, 11.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1, 6.
-/

public noncomputable section

open IsDedekindDomain Module NumberField QuadraticAlgebra TauCeti.GlobalNumberFields
open scoped NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **Multiplication-matrix reciprocity over the Hilbert class field**: given any ring isomorphism
`e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b`, the level-`N` multiplication-matrix group modulo the reduced
global units is isomorphic to
`Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)`. -/
def periodMatrixQuotientArtinEquiv {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (N : ℕ) [NeZero N]
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))] :
    periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N ≃*
      Gal(rayClassField (Modulus.spanNat K N)/hilbertClassField K) :=
  (residueUnitsQuotientPeriodMatrixEquiv e N).symm.trans
    (residueUnitsQuotientArtinEquiv (Modulus.spanNat_infinitePart (K := K) N))

/-- Unfolding lemma for `periodMatrixQuotientArtinEquiv`. -/
theorem periodMatrixQuotientArtinEquiv_def {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (N : ℕ) [NeZero N]
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))] :
    periodMatrixQuotientArtinEquiv e N =
      (residueUnitsQuotientPeriodMatrixEquiv e N).symm.trans
        (residueUnitsQuotientArtinEquiv (Modulus.spanNat_infinitePart (K := K) N)) :=
  (rfl)

/-- On the coset of an explicit matrix `M : periodMatrixGroup (a : ZMod N) (b : ZMod N)`,
`periodMatrixQuotientArtinEquiv e N` acts as the Artin symbol of the corresponding residue unit
`((unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M)`. -/
@[simp]
theorem restrictScalars_periodMatrixQuotientArtinEquiv_mk {a b : ℤ}
    (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) [NeZero N]
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N)) :
    (periodMatrixQuotientArtinEquiv e N M).restrictScalars K =
      rayClassArtinEquiv (Modulus.spanNat K N)
        (residueRayClass (Modulus.spanNat K N)
          ((unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M)) := by
  rw [periodMatrixQuotientArtinEquiv_def]
  -- `(Modulus.spanNat K N).finitePart` is definitionally `Ideal.span {(N : 𝓞 K)}`; `change`
  -- reconciles the two so `residueUnitsQuotientPeriodMatrixEquiv_symm_mk` matches.
  change ((residueUnitsQuotientArtinEquiv (Modulus.spanNat_infinitePart (K := K) N))
    ((residueUnitsQuotientPeriodMatrixEquiv e N).symm M)).restrictScalars K = _
  rw [residueUnitsQuotientPeriodMatrixEquiv_symm_mk]
  exact restrictScalars_residueUnitsQuotientArtinEquiv_mk _ _

/-- Pointwise evaluation of `periodMatrixQuotientArtinEquiv` on the coset of `M` agrees with the
ray-class Artin action of `(unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M`. -/
@[simp]
theorem periodMatrixQuotientArtinEquiv_mk_apply {a b : ℤ}
    (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) [NeZero N]
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N))
    (y : rayClassField (Modulus.spanNat K N)) :
    periodMatrixQuotientArtinEquiv e N M y =
      rayClassArtinEquiv (Modulus.spanNat K N)
        (residueRayClass (Modulus.spanNat K N)
          ((unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M)) y := by
  rw [← AlgEquiv.restrictScalars_apply K, restrictScalars_periodMatrixQuotientArtinEquiv_mk]

/-- **Relative norm as a product over the unit-quotient multiplication-matrix group**: the norm of
any `y : rayClassField (Modulus.spanNat K N)` down to `hilbertClassField K` is the product of its
conjugates over `periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N`. -/
theorem algebraMap_norm_hilbertClassField_periodMatrixQuotient {a b : ℤ}
    (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) [NeZero N]
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    (y : rayClassField (Modulus.spanNat K N)) :
    algebraMap (hilbertClassField K) (rayClassField (Modulus.spanNat K N))
        (Algebra.norm (hilbertClassField K) y) =
      ∏ᶠ M : periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N,
        periodMatrixQuotientArtinEquiv e N M y := by
  rw [algebraMap_norm_hilbertClassField_of_infinitePart_eq_empty
    (Modulus.spanNat_infinitePart (K := K) N)]
  exact (finprod_comp_equiv (residueUnitsQuotientPeriodMatrixEquiv e N).symm.toEquiv).symm

end TauCeti.ClassFieldTheory
