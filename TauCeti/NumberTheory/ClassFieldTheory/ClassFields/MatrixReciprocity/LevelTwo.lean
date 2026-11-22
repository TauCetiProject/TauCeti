/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MatrixReciprocity.Basic
import TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Two.Quotient

/-!
# Level-two multiplication-matrix reciprocity over the Hilbert class field

For a number field `K` and a ring isomorphism `e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b` with
`discr a b < -4`, `unitPeriodMatrixSubgroup a b 2 = ⊥`
(`QuadraticAlgebra.unitPeriodMatrixSubgroup_two_eq_bot_of_discr_lt_neg_four`), so the level-`2`
multiplication-matrix group `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)` itself identifies with
`Gal(rayClassField (Modulus.spanNat K 2) / hilbertClassField K)`:

* `TauCeti.ClassFieldTheory.periodMatrixArtinEquivTwo`: group isomorphism
  `periodMatrixGroup (a : ZMod 2) (b : ZMod 2) ≃*
  Gal(rayClassField (Modulus.spanNat K 2) / hilbertClassField K)`.
* `TauCeti.ClassFieldTheory.periodMatrixArtinEquivTwo_apply`: evaluation via
  `periodMatrixQuotientArtinEquiv e 2`.
* `TauCeti.ClassFieldTheory.algebraMap_norm_hilbertClassField_periodMatrixTwo`: relative norm
  product indexed directly by `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §§9, 11.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1, 6.
-/

public noncomputable section

open NumberField QuadraticAlgebra TauCeti.GlobalNumberFields
open scoped NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **Level-`2` multiplication-matrix reciprocity for `discr a b < -4`**: since `-1 ≡ 1 (mod 2)`,
the reduced global-unit subgroup is trivial and `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)` itself
maps isomorphically onto `Gal(rayClassField (Modulus.spanNat K 2) / hilbertClassField K)`. -/
def periodMatrixArtinEquivTwo {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (hd : QuadraticAlgebra.discr a b < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))] :
    periodMatrixGroup (a : ZMod 2) (b : ZMod 2) ≃*
      Gal(rayClassField (Modulus.spanNat K 2)/hilbertClassField K) :=
  ((QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq
      (unitPeriodMatrixSubgroup_two_eq_bot_of_discr_lt_neg_four hd).symm)).trans
    (periodMatrixQuotientArtinEquiv e 2)

/-- `periodMatrixArtinEquivTwo` sends a matrix `M` to `periodMatrixQuotientArtinEquiv e 2` on the
coset of `M`. -/
@[simp]
theorem periodMatrixArtinEquivTwo_apply {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (hd : QuadraticAlgebra.discr a b < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    (M : periodMatrixGroup (a : ZMod 2) (b : ZMod 2)) :
    periodMatrixArtinEquivTwo e hd M =
      periodMatrixQuotientArtinEquiv e 2
        (M : periodMatrixGroup (a : ZMod 2) (b : ZMod 2) ⧸ unitPeriodMatrixSubgroup a b 2) := by
  simp [periodMatrixArtinEquivTwo]

/-- **Level-`2` norm product for `discr a b < -4`** indexed directly by
`periodMatrixGroup (a : ZMod 2) (b : ZMod 2)`. -/
theorem algebraMap_norm_hilbertClassField_periodMatrixTwo {a b : ℤ}
    (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) (hd : QuadraticAlgebra.discr a b < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    (y : rayClassField (Modulus.spanNat K 2)) :
    algebraMap (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))
        (Algebra.norm (hilbertClassField K) y) =
      ∏ᶠ M : periodMatrixGroup (a : ZMod 2) (b : ZMod 2),
        periodMatrixArtinEquivTwo e hd M y := by
  rw [algebraMap_norm_hilbertClassField_periodMatrixQuotient e 2 y,
    ← finprod_comp_equiv ((QuotientGroup.quotientBot.symm).trans
      (QuotientGroup.quotientMulEquivOfEq
        (unitPeriodMatrixSubgroup_two_eq_bot_of_discr_lt_neg_four hd).symm)).toEquiv]
  simp [periodMatrixArtinEquivTwo]

end TauCeti.ClassFieldTheory
