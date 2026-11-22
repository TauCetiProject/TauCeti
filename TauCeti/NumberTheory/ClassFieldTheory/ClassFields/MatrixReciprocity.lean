/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower
public import TauCeti.NumberTheory.QuadraticOrder.LevelTwoMatrix

/-!
# Multiplication-matrix Galois actions on ray class fields

For a number field `K`, a rational integer `N ≠ 0`, and any ring isomorphism
`e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b`, combining the relative ray-class reciprocity of
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower` with the multiplication-matrix
presentation of `TauCeti.NumberTheory.QuadraticOrder.MatrixQuotient` and the level-two
computations of `TauCeti.NumberTheory.QuadraticOrder.LevelTwoMatrix` expresses the Galois group
`Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)` and its relative norm in terms
of multiplication matrices:

* `TauCeti.ClassFieldTheory.periodMatrixQuotientArtinEquiv`: group isomorphism
  `periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N ≃*
  Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)` with explicit Artin evaluation
  (`restrictScalars_periodMatrixQuotientArtinEquiv_mk`,
  `periodMatrixQuotientArtinEquiv_mk_apply`) and norm product
  (`algebraMap_norm_hilbertClassField_periodMatrixQuotient`).
* `TauCeti.ClassFieldTheory.periodMatrixArtinEquivTwo`: at level `N = 2` when `discr a b < -4`,
  `unitPeriodMatrixSubgroup a b 2 = ⊥`, so the relative Galois group is
  `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)` itself (`periodMatrixArtinEquivTwo_apply`,
  `algebraMap_norm_hilbertClassField_periodMatrixTwo`).
* `TauCeti.ClassFieldTheory.unipotentLevelThreeArtinEquiv`: at level `N = 3` when `discr a b < -4`
  and `(a : ZMod 3) = (b : ZMod 3) = 0` (as holds for the period presentation of
  `TauCeti.NumberTheory.NumberField.Quadratic.PeriodAlgebra` whenever `3 ∣ D`), the three
  lower-triangular unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`) identify
  `Multiplicative (ZMod 3)` with `Gal(K_(3) / H_K)` (`unipotentLevelThreeArtinEquiv_ofAdd`,
  `algebraMap_norm_hilbertClassField_unipotentLevelThree`).

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
