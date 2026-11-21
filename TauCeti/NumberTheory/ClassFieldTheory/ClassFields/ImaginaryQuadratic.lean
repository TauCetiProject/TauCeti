/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower
public import TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits
public import TauCeti.NumberTheory.QuadraticOrder.MatrixQuotient
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values
import TauCeti.NumberTheory.NumberField.Global.RayClass.ImaginaryQuadratic
import TauCeti.NumberTheory.NumberField.Quadratic.Units

/-!
# Multiplication-matrix Galois actions and ray class field degrees for imaginary quadratic fields

Let `K` be an imaginary quadratic field (`[IsTotallyComplex K]`, `finrank ℚ K = 2`) of discriminant
`D = NumberField.discr K`, and let `Modulus.spanNat K N` denote the purely finite modulus `(N)` for
`N ≠ 0`. Combining the relative ray-class reciprocity of
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower`, the matrix-quotient presentation of
`TauCeti.NumberTheory.QuadraticOrder.MatrixQuotient`, the unit-congruence indices of
`TauCeti.NumberTheory.NumberField.Global.RayClass.ImaginaryQuadratic`, and the residue-unit
counts of `TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits` yields the full
multiplication-matrix and degree dictionary over `hilbertClassField K`:

1. **Multiplication-matrix presentation of `Gal(K_(N) / H_K)` and norm products.** Any ring
   isomorphism `e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b` (for instance a period-algebra presentation
   onto `QuadraticAlgebra ℤ (-periodCoeffC D) (-periodCoeffB D)` from
   `exists_ringOfIntegers_periodAlgEquiv`) induces a group isomorphism
   `periodMatrixQuotientArtinEquiv : periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸
   unitPeriodMatrixSubgroup a b N ≃* Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)`
   and expresses the relative norm to `hilbertClassField K` as the product of conjugates over this
   unit-quotient matrix group (`algebraMap_norm_hilbertClassField_periodMatrixQuotient`).
   * At level `N = 2` for `discr a b < -4`, `unitPeriodMatrixSubgroup a b 2 = ⊥`, so the relative
     Galois group is `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)` itself
     (`periodMatrixArtinEquivTwo`, `algebraMap_norm_hilbertClassField_periodMatrixTwo`).
   * At level `N = 3` when `discr a b < -4` and `(a : ZMod 3) = (b : ZMod 3) = 0` — which holds for
     the period presentation whenever `3` ramifies (`3 ∣ D`, `D < -4`, for example `D ≡ 0 (mod 12)`
     or `D ≡ 9, 21 (mod 24)`, via `intCast_neg_periodCoeffB_zmod_three_eq_zero` and
     `intCast_neg_periodCoeffC_zmod_three_eq_zero_of_three_dvd`) — the three lower-triangular
     unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`) give a `Multiplicative (ZMod 3)` isomorphism
     onto `Gal(K_(3) / H_K)` and express the norm to `H_K` as the `3`-factor product over
     `s : ZMod 3` (`unipotentLevelThreeArtinEquiv`,
     `algebraMap_norm_hilbertClassField_unipotentLevelThree`).
2. **Closed ray class field degree formulas at levels `2`, `3`, `6`, and `8`.** Using the exact
   unit congruence subgroups (`⊤` at `1`, `{±1}` at `2`, `⊥` for `3 ≤ N`), this file establishes
   `[K_(N) : H_K] * #(𝓞 K)ˣ = #(𝓞 K ⧸ (N))ˣ` for every `3 ≤ N`
   (`finrank_hilbertClassField_rayClassField_spanNat_mul_card_units`), evaluates `[K_(N) : H_K]` at
   levels `2`, `3`, `6`, and `8` for all imaginary quadratic fields — including `D = -4` and
   `D = -3`, where `[K_(2) : H_K] = 1` despite `#(𝓞 K ⧸ (2))ˣ > 1` — and deduces the unconditional
   relative tower degrees `[K_(6) : K_(2)] = (3 - χ_D(3)).toNat` and `[K_(8) : K_(2)] = 8`, valid
   uniformly for every imaginary quadratic discriminant `D`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §§9, 11.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1, 6.
-/

public noncomputable section

open IsDedekindDomain Module NumberField QuadraticAlgebra TauCeti.GlobalNumberFields
  TauCeti.NumberField
open scoped NumberField nonZeroDivisors
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr
  fundamentalDiscriminantChar_le_one fundamentalDiscriminantChar_neg_four_two
  fundamentalDiscriminantChar_neg_four_three fundamentalDiscriminantChar_neg_three_two
  fundamentalDiscriminantChar_neg_three_three)

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-! ### Multiplication-matrix presentation of `Gal(K_(N) / H_K)` and relative norms -/

section MatrixAction

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

end MatrixAction

/-! ### Ray class field degrees for imaginary quadratic fields -/

section Degrees

variable [IsTotallyComplex K]

/-- **General relative degree relation at level `N ≥ 3` for imaginary quadratic fields**:
`[K_(N) : H_K] * #(𝓞 K)ˣ = #(𝓞 K ⧸ (N))ˣ`, with `#(𝓞 K)ˣ` given by
`TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr`. -/
theorem finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    (hK : finrank ℚ K = 2) {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K N)) *
        Nat.card (𝓞 K)ˣ =
      Nat.card (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ := by
  have hrel := finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
    (Modulus.spanNat_infinitePart (K := K) N)
  rw [Modulus.spanNat_finitePart, index_unitsCongruenceSubgroup_spanNat_of_three_le hK hN,
    ← TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at hrel
  exact hrel

/-- Integer-cast form of `finrank_hilbertClassField_rayClassField_spanNat_mul_card_units` with
`#(𝓞 K)ˣ` evaluated by discriminant. -/
private theorem intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    (hK : finrank ℚ K = 2) {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))] :
    (Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K N)) : ℤ) *
        (if discr K = -4 then 4 else if discr K = -3 then 6 else 2) =
      (Nat.card (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ : ℤ) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_spanNat_mul_card_units hK hN
  rw [Nat.cast_mul, TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at h
  simpa using h

omit [IsTotallyComplex K] in
/-- Case split on `discr K ∈ {-4, -3}` together with the values of `χ_D(2)` and `χ_D(3)`
(and the uniform bound `χ_D(2), χ_D(3) ≤ 1` away from `-4` and `-3`). -/
private theorem discr_cases_char_two_three (hK : finrank ℚ K = 2) :
    (discr K = -4 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 = 0 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3 = -1) ∨
    (discr K = -3 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 = -1 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3 = 0) ∨
    (discr K ≠ -4 ∧ discr K ≠ -3 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 ≤ 1 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3 ≤ 1) := by
  generalize hD : isFundamentalDiscr_discr hK = hD'
  clear hD
  generalize discr K = D at hD' ⊢
  rcases eq_or_ne D (-4) with rfl | h4
  · exact Or.inl ⟨rfl, fundamentalDiscriminantChar_neg_four_two hD',
      fundamentalDiscriminantChar_neg_four_three hD'⟩
  rcases eq_or_ne D (-3) with rfl | h3
  · exact Or.inr (Or.inl ⟨rfl, fundamentalDiscriminantChar_neg_three_two hD',
      fundamentalDiscriminantChar_neg_three_three hD'⟩)
  · exact Or.inr (Or.inr ⟨h4, h3, fundamentalDiscriminantChar_le_one hD' 2,
      fundamentalDiscriminantChar_le_one hD' 3⟩)

/-- **Degree of `K_(2)` over the Hilbert class field**: `1` at `D = -4` and `D = -3` (where the
fourth or sixth roots of unity surject onto `(𝓞 K ⧸ (2))ˣ`), and `(2 - χ_D(2)).toNat` (`1`, `2`,
or `3` according as `2` splits, ramifies, or is inert) for `D < -4`. -/
theorem finrank_hilbertClassField_rayClassField_two (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) =
      if discr K = -4 ∨ discr K = -3 then 1
      else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat := by
  have hrel := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
      (Modulus.spanNat_infinitePart (K := K) 2)
  rw [Nat.cast_mul, Modulus.spanNat_finitePart, Nat.cast_ofNat, card_units_quotient_span_two hK,
    index_unitsCongruenceSubgroup_spanNat_two hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, hc2, _⟩ | ⟨hD, hc2, _⟩ | ⟨h4, h3, _, _⟩
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [h4, h3] at hrel ⊢; omega

/-- Specialization of `finrank_hilbertClassField_rayClassField_two` to `discr K < -4`. -/
theorem finrank_hilbertClassField_rayClassField_two_of_discr_lt_neg_four (hK : finrank ℚ K = 2)
    (hd : discr K < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) =
      (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat := by
  have hnot : ¬(discr K = -4 ∨ discr K = -3) := by omega
  simp [finrank_hilbertClassField_rayClassField_two hK, hnot]

/-- **Degree of `K_(3)` over the Hilbert class field**: `2` at `D = -4`, `1` at `D = -3`, and
`(3 - χ_D(3)).toNat` (`2`, `3`, or `4` according as `3` splits, ramifies, or is inert) for
`D < -4`. -/
theorem finrank_hilbertClassField_rayClassField_three (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) =
      if discr K = -4 then 2 else if discr K = -3 then 1
      else (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have hrel := intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units hK (le_refl 3)
  rw [Nat.cast_ofNat, card_units_quotient_span_three hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, _, hc3⟩ | ⟨hD, _, hc3⟩ | ⟨h4, h3, _, _⟩
  · simp [hD, hc3] at hrel ⊢; omega
  · simp [hD, hc3] at hrel ⊢; omega
  · simp [h4, h3] at hrel ⊢; omega

/-- Specialization of `finrank_hilbertClassField_rayClassField_three` to `discr K < -4`. -/
theorem finrank_hilbertClassField_rayClassField_three_of_discr_lt_neg_four (hK : finrank ℚ K = 2)
    (hd : discr K < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) =
      (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  simp [finrank_hilbertClassField_rayClassField_three hK, show discr K ≠ -4 by omega,
    show discr K ≠ -3 by omega]

/-- **Degree of `K_(6)` over the Hilbert class field** for all imaginary quadratic fields. -/
theorem finrank_hilbertClassField_rayClassField_six (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 6))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 6))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) =
      (if discr K = -4 ∨ discr K = -3 then 1
        else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat) *
        (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have hrel := intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    hK (N := 6) (by decide)
  rw [Nat.cast_ofNat, card_units_quotient_span_six hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, hc2, hc3⟩ | ⟨hD, hc2, hc3⟩ | ⟨h4, h3, hc2, hc3⟩
  · simp [hD, hc2, hc3] at hrel ⊢; omega
  · simp [hD, hc2, hc3] at hrel ⊢; omega
  · simp only [h4, h3, or_self, ↓reduceIte] at hrel ⊢
    rw [← Int.toNat_mul (by omega) (by omega)]
    exact Nat.cast_injective (R := ℤ) (by rw [Int.toNat_of_nonneg (by nlinarith)]; linarith)

/-- **Degree of `K_(8)` over the Hilbert class field** for all imaginary quadratic fields. -/
theorem finrank_hilbertClassField_rayClassField_eight (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 8))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 8))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) =
      8 * (if discr K = -4 ∨ discr K = -3 then 1
        else (2 - fundamentalDiscriminantChar (discr K)
          (isFundamentalDiscr_discr hK) 2).toNat) := by
  have hrel := intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    hK (N := 8) (by decide)
  rw [Nat.cast_ofNat, card_units_quotient_span_eight hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, hc2, _⟩ | ⟨hD, hc2, _⟩ | ⟨h4, h3, _, _⟩
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [h4, h3] at hrel ⊢; omega

/-- **Unconditional relative degree `[K_(6) : K_(2)] = 3 - χ_D(3)`** for every imaginary quadratic
field `K` (including `D = -4` and `D = -3`, since the unit congruence subgroup shrinks from `{±1}`
to `{1}` between levels `2` and `6`). -/
theorem finrank_rayClassField_two_rayClassField_six (hK : finrank ℚ K = 2)
    [Algebra (rayClassField (Modulus.spanNat K 2)) (rayClassField (Modulus.spanNat K 6))]
    [IsScalarTower K (rayClassField (Modulus.spanNat K 2))
      (rayClassField (Modulus.spanNat K 6))] :
    Module.finrank (rayClassField (Modulus.spanNat K 2))
        (rayClassField (Modulus.spanNat K 6)) =
      (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 2))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 6))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hmul := finrank_hilbertClassField_mul_finrank_rayClassField
    (Modulus.spanNat K 2) (Modulus.spanNat K 6)
  rw [finrank_hilbertClassField_rayClassField_two hK,
    finrank_hilbertClassField_rayClassField_six hK] at hmul
  refine Nat.mul_left_cancel ?_ hmul
  split_ifs
  · omega
  · have := fundamentalDiscriminantChar_le_one (isFundamentalDiscr_discr hK) 2; omega

/-- **Unconditional relative degree `[K_(8) : K_(2)] = 8`** for every imaginary quadratic field `K`
(including `D = -4` and `D = -3`). -/
theorem finrank_rayClassField_two_rayClassField_eight (hK : finrank ℚ K = 2)
    [Algebra (rayClassField (Modulus.spanNat K 2)) (rayClassField (Modulus.spanNat K 8))]
    [IsScalarTower K (rayClassField (Modulus.spanNat K 2))
      (rayClassField (Modulus.spanNat K 8))] :
    Module.finrank (rayClassField (Modulus.spanNat K 2))
        (rayClassField (Modulus.spanNat K 8)) = 8 := by
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 2))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 8))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hmul := finrank_hilbertClassField_mul_finrank_rayClassField
    (Modulus.spanNat K 2) (Modulus.spanNat K 8)
  rw [finrank_hilbertClassField_rayClassField_two hK,
    finrank_hilbertClassField_rayClassField_eight hK] at hmul
  refine Nat.mul_left_cancel ?_ (hmul.trans (mul_comm 8 _))
  split_ifs
  · omega
  · have := fundamentalDiscriminantChar_le_one (isFundamentalDiscr_discr hK) 2; omega

end Degrees

end TauCeti.ClassFieldTheory
