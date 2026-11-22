/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MatrixReciprocity.Basic
public import TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Three

/-!
# Level-three unipotent multiplication-matrix reciprocity over the Hilbert class field

For a number field `K` and a ring isomorphism `e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b` with
`discr a b < -4` and `(a : ZMod 3) = (b : ZMod 3) = 0` — as holds for the period presentation of
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MatrixReciprocity.PeriodAlgebra` whenever `3`
ramifies (`3 ∣ D` and
`D < -4`, for example `D ≡ 0 (mod 12)` or `D ≡ 9, 21 (mod 24)`) — the three lower-triangular
unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`) identify `Multiplicative (ZMod 3)` with
`Gal(rayClassField (Modulus.spanNat K 3) / hilbertClassField K)`:

* `TauCeti.ClassFieldTheory.unipotentLevelThreeArtinEquiv`: group isomorphism
  `Multiplicative (ZMod 3) ≃*
  Gal(rayClassField (Modulus.spanNat K 3) / hilbertClassField K)`.
* `TauCeti.ClassFieldTheory.unipotentLevelThreeArtinEquiv_ofAdd`: evaluation on
  `Multiplicative.ofAdd s`.
* `TauCeti.ClassFieldTheory.algebraMap_norm_hilbertClassField_unipotentLevelThree`: three-factor
  relative norm product from `K_(3)` to `H_K`.

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

/-- **Level-`3` unipotent reciprocity when `3` divides `a` and `b` and `discr a b < -4`** (as holds
for the period presentation whenever `3` ramifies, i.e. `3 ∣ D` and `D < -4`, for example
`D ≡ 0 (mod 12)` or `D ≡ 9, 21 (mod 24)`): the three unipotent matrices `!![1, 0; s, 1]`
(`s : ZMod 3`) identify `Multiplicative (ZMod 3)` with
`Gal(rayClassField (Modulus.spanNat K 3) / hilbertClassField K)`. -/
def unipotentLevelThreeArtinEquiv {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (hd : QuadraticAlgebra.discr a b < -4) (ha : (a : ZMod 3) = 0) (hb : (b : ZMod 3) = 0)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    Multiplicative (ZMod 3) ≃*
      Gal(rayClassField (Modulus.spanNat K 3)/hilbertClassField K) :=
  (unipotentPeriodMatrixQuotientEquivZModThree.trans
    (periodMatrixQuotientEquivZpowersNegOne hd ha hb)).trans
    (periodMatrixQuotientArtinEquiv e 3)

/-- Unfolding lemma for `unipotentLevelThreeArtinEquiv`. -/
theorem unipotentLevelThreeArtinEquiv_def {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (hd : QuadraticAlgebra.discr a b < -4) (ha : (a : ZMod 3) = 0) (hb : (b : ZMod 3) = 0)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    unipotentLevelThreeArtinEquiv e hd ha hb =
      (unipotentPeriodMatrixQuotientEquivZModThree.trans
        (periodMatrixQuotientEquivZpowersNegOne hd ha hb)).trans
        (periodMatrixQuotientArtinEquiv e 3) :=
  (rfl)

/-- `unipotentLevelThreeArtinEquiv` sends `Multiplicative.ofAdd s` to the
`periodMatrixQuotientArtinEquiv` action of the unipotent matrix `!![1, 0; s, 1]`. -/
@[simp]
theorem unipotentLevelThreeArtinEquiv_ofAdd {a b : ℤ} (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b)
    (hd : QuadraticAlgebra.discr a b < -4) (ha : (a : ZMod 3) = 0) (hb : (b : ZMod 3) = 0)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    (s : ZMod 3) :
    unipotentLevelThreeArtinEquiv e hd ha hb (Multiplicative.ofAdd s) =
      periodMatrixQuotientArtinEquiv e 3
        ((⟨(unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s) : GL (Fin 2) (ZMod 3)),
          by
            rw [ha, hb]
            exact (unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s)).property⟩ :
            periodMatrixGroup (a : ZMod 3) (b : ZMod 3)) :
          periodMatrixGroup (a : ZMod 3) (b : ZMod 3) ⧸ unitPeriodMatrixSubgroup a b 3) := by
  simp [unipotentLevelThreeArtinEquiv]

/-- **Three-factor unipotent norm product from `K_(3)` to `H_K`** when `discr a b < -4` and
`(a : ZMod 3) = (b : ZMod 3) = 0`. -/
theorem algebraMap_norm_hilbertClassField_unipotentLevelThree {a b : ℤ}
    (e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) (hd : QuadraticAlgebra.discr a b < -4)
    (ha : (a : ZMod 3) = 0) (hb : (b : ZMod 3) = 0)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    (y : rayClassField (Modulus.spanNat K 3)) :
    algebraMap (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))
        (Algebra.norm (hilbertClassField K) y) =
      ∏ s : ZMod 3, unipotentLevelThreeArtinEquiv e hd ha hb (Multiplicative.ofAdd s) y := by
  rw [algebraMap_norm_hilbertClassField_periodMatrixQuotient e 3 y,
    ← finprod_comp_equiv (Multiplicative.ofAdd.trans
      (unipotentPeriodMatrixQuotientEquivZModThree.trans
        (periodMatrixQuotientEquivZpowersNegOne hd ha hb)).toEquiv),
    finprod_eq_prod_of_fintype]
  simp [unipotentLevelThreeArtinEquiv]

end TauCeti.ClassFieldTheory
