/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower
public import TauCeti.NumberTheory.NumberField.Quadratic.CongruenceUnits

/-!
# Multiplication-matrix Galois actions and ray class field degrees for imaginary quadratic fields

Let `K` be an imaginary quadratic field (`[IsTotallyComplex K]`, `finrank ℚ K = 2`) of discriminant
`D = NumberField.discr K`, and let `Modulus.spanNat K N` denote the purely finite modulus `(N)` for
`N ≠ 0`. Combining the relative ray-class reciprocity of
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower`, the matrix-quotient presentation of
`TauCeti.NumberTheory.QuadraticOrder.MatrixQuotient`, and the unit-congruence and residue-unit
formulas of `TauCeti.NumberTheory.NumberField.Quadratic.CongruenceUnits` yields the full
multiplication-matrix and degree dictionary over `hilbertClassField K`:

1. **Multiplication-matrix presentation of `Gal(K_(N) / H_K)` and norm products.** Any ring
   isomorphism `e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b` (such as the canonical `(1, τ_D)` presentation
   from `exists_ringOfIntegers_periodAlgEquiv`) induces a group isomorphism
   `periodMatrixQuotientArtinEquiv : periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸
   unitPeriodMatrixSubgroup a b N ≃* Gal(rayClassField (Modulus.spanNat K N) / hilbertClassField K)`
   and expresses the relative norm to `hilbertClassField K` as the product of conjugates over this
   unit-quotient matrix group (`algebraMap_norm_hilbertClassField_periodMatrixQuotient`).
   * At level `N = 2` for `discr a b < -4`, `unitPeriodMatrixSubgroup a b 2 = ⊥`, so the relative
     Galois group is `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)` itself
     (`periodMatrixArtinEquivTwo`, `algebraMap_norm_hilbertClassField_periodMatrixTwo`).
   * At level `N = 3` when `discr a b < -4` and `(a : ZMod 3) = (b : ZMod 3) = 0` — which holds for
     the canonical `(1, τ_D)` presentation when `2` is inert and `3` ramifies (`D ≡ 21 (mod 24)`,
     `D < -4`) — the three lower-triangular unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`)
     give a `Multiplicative (ZMod 3)` isomorphism onto `Gal(K_(3) / H_K)` and express the norm to
     `H_K` as the `3`-factor product over `s : ZMod 3` (`unipotentLevelThreeArtinEquiv`,
     `algebraMap_norm_hilbertClassField_unipotentLevelThree`).
2. **Closed ray class field degree formulas at levels `2`, `3`, `6`, and `8`.** Using the exact
   unit congruence subgroups (`⊤` at `1`, `{±1}` at `2`, `⊥` for `3 ≤ N`), this file evaluates
   `[K_(N) : H_K]` for all imaginary quadratic fields — including `D = -4` and `D = -3`, where
   `[K_(2) : H_K] = 1` despite `#(𝓞 K ⧸ (2))ˣ > 1` — and deduces the unconditional relative tower
   degrees `[K_(6) : K_(2)] = (3 - χ_D(3)).toNat` and `[K_(8) : K_(2)] = 8`, valid uniformly for
   every imaginary quadratic discriminant `D`.

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
  fundamentalDiscriminantChar_isQuadratic fundamentalDiscriminantChar_two
  fundamentalDiscriminantChar_natCast_eq_legendreSym)

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-! ### Multiplication-matrix presentation of `Gal(K_(N) / H_K)` and relative norms -/

section MatrixAction

/-- **Multiplication-matrix reciprocity over the Hilbert class field**: given any ring isomorphism
`e : 𝓞 K ≃+* QuadraticAlgebra ℤ a b`, the level-`N` multiplication-matrix group modulo the reduced
global units is canonically isomorphic to
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
      (unitPeriodMatrixSubgroup_two_of_discr_lt_neg_four hd).symm)).trans
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
  classical
  have : IsGalois (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    IsGalois.tower_top_of_isGalois K _ _
  have : FiniteDimensional (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    FiniteDimensional.right K _ _
  rw [Algebra.norm_eq_prod_automorphisms, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv (periodMatrixArtinEquivTwo e hd).toEquiv]
  rfl

/-- **Level-`3` unipotent reciprocity when `3` divides `a` and `b` and `discr a b < -4`** (as holds
for `(1, τ_D)` when `2` is inert and `3` ramifies, i.e. `D ≡ 21 (mod 24)` and `D < -4`): the three
unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`) identify `Multiplicative (ZMod 3)` with
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
          by rw [ha, hb]; exact (unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s)).2⟩ :
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
  classical
  have : IsGalois (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) :=
    IsGalois.tower_top_of_isGalois K _ _
  have : FiniteDimensional (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) :=
    FiniteDimensional.right K _ _
  rw [Algebra.norm_eq_prod_automorphisms,
    ← Fintype.prod_equiv (Multiplicative.ofAdd.trans
      (unipotentLevelThreeArtinEquiv e hd ha hb).toEquiv)]
  intro s
  rfl

end MatrixAction

/-! ### Unit congruence indices and ray class field degrees for imaginary quadratic fields -/

section Degrees

variable [IsTotallyComplex K]

/-- **Congruence subgroup of global units modulo `(N)` in an imaginary quadratic field**: `⊤` at
`N = 1`, `Subgroup.zpowers (-1)` at `N = 2`, and `⊥` for `3 ≤ N`. -/
theorem unitsCongruenceSubgroup_spanNat (hK : finrank ℚ K = 2) (N : ℕ) [NeZero N] :
    unitsCongruenceSubgroup (Modulus.spanNat K N) =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  rw [unitsCongruenceSubgroup_eq_ker_of_infinitePart_eq_empty (Modulus.spanNat_infinitePart N),
    Modulus.spanNat_finitePart, ker_unitsMap_ringOfIntegers_quotient_span_natCast hK (NeZero.ne N)]

/-- **Index of `unitsCongruenceSubgroup (Modulus.spanNat K 2)`**: `2` at `D = -4`, `3` at `D = -3`,
and `1` for all `D < -4`. -/
theorem index_unitsCongruenceSubgroup_spanNat_two (hK : finrank ℚ K = 2) :
    (unitsCongruenceSubgroup (Modulus.spanNat K 2)).index =
      if discr K = -4 then 2 else if discr K = -3 then 3 else 1 := by
  rw [unitsCongruenceSubgroup_spanNat hK 2]
  simp only [OfNat.ofNat_ne_one, ↓reduceIte]
  have hmul := (Subgroup.zpowers (-1 : (𝓞 K)ˣ)).card_mul_index
  rw [card_zpowers_neg_one_units_ringOfIntegers,
    TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at hmul
  split_ifs at hmul ⊢ <;> omega

/-- **Index of `unitsCongruenceSubgroup (Modulus.spanNat K N)` for `3 ≤ N`**: every non-identity
root of unity acts nontrivially modulo `(N)`, so the index is `#(𝓞 K)ˣ` (`4` at `D = -4`, `6` at
`D = -3`, and `2` for `D < -4`). -/
theorem index_unitsCongruenceSubgroup_spanNat_of_three_le (hK : finrank ℚ K = 2) {N : ℕ}
    [NeZero N] (hN : 3 ≤ N) :
    (unitsCongruenceSubgroup (Modulus.spanNat K N)).index =
      if discr K = -4 then 4 else if discr K = -3 then 6 else 2 := by
  have h1 : N ≠ 1 := by omega
  have h2 : N ≠ 2 := by omega
  rw [unitsCongruenceSubgroup_spanNat hK N]
  simp only [h1, h2, ↓reduceIte]
  have hmul := (⊥ : Subgroup (𝓞 K)ˣ).card_mul_index
  rw [Subgroup.card_bot, one_mul,
    TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at hmul
  exact hmul

/-- Evaluation of `χ_D(2)` and `χ_D(3)` at the Gaussian discriminant `D = -4`. -/
private theorem char_of_eq_neg_four {D : ℤ} (hD : Int.IsFundamentalDiscr D) (h : D = -4) :
    fundamentalDiscriminantChar D hD 2 = 0 ∧
      fundamentalDiscriminantChar D hD 3 = -1 := by
  have hnsq : ¬IsSquare ((-4 : ℤ) : ZMod 3) := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, ?_⟩
  · rw [fundamentalDiscriminantChar_two, h, ZMod.χ₈_int_eq_if_mod_eight]
    norm_num
  · rw [show (3 : ZMod D.natAbs) = ((3 : ℕ) : ℤ) by norm_num,
      fundamentalDiscriminantChar_natCast_eq_legendreSym hD (by decide), h,
      legendreSym.eq_neg_one_iff]
    exact hnsq

/-- Evaluation of `χ_D(2)` and `χ_D(3)` at the Eisenstein discriminant `D = -3`. -/
private theorem char_of_eq_neg_three {D : ℤ} (hD : Int.IsFundamentalDiscr D) (h : D = -3) :
    fundamentalDiscriminantChar D hD 2 = -1 ∧
      fundamentalDiscriminantChar D hD 3 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, ?_⟩
  · rw [fundamentalDiscriminantChar_two, h, ZMod.χ₈_int_eq_if_mod_eight]
    norm_num
  · rw [show (3 : ZMod D.natAbs) = ((3 : ℕ) : ℤ) by norm_num,
      fundamentalDiscriminantChar_natCast_eq_legendreSym hD (by decide), h,
      legendreSym.eq_zero_iff 3 (-3), ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega

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
  have hq := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 2
  by_cases h4 : discr K = -4
  · have hc2 := (char_of_eq_neg_four (isFundamentalDiscr_discr hK) h4).1
    rw [hc2, h4] at hrel
    simp only [h4, true_or, ↓reduceIte]
    norm_num at hrel ⊢
    omega
  · by_cases h3 : discr K = -3
    · have hc2 := (char_of_eq_neg_three (isFundamentalDiscr_discr hK) h3).1
      rw [hc2, h3] at hrel
      simp only [h3, or_true, ↓reduceIte]
      norm_num at hrel ⊢
      omega
    · simp only [h4, h3, or_self, ↓reduceIte] at hrel ⊢
      rcases hq with hc | hc | hc <;> rw [hc] at hrel ⊢ <;> omega

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
  have hrel := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
      (Modulus.spanNat_infinitePart (K := K) 3)
  rw [Nat.cast_mul, Modulus.spanNat_finitePart, Nat.cast_ofNat, card_units_quotient_span_three hK,
    index_unitsCongruenceSubgroup_spanNat_of_three_le hK (le_refl 3)] at hrel
  have hq := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 3
  by_cases h4 : discr K = -4
  · have hc3 := (char_of_eq_neg_four (isFundamentalDiscr_discr hK) h4).2
    rw [hc3, h4] at hrel
    simp only [h4, ↓reduceIte]
    norm_num at hrel ⊢
    omega
  · by_cases h3 : discr K = -3
    · have hc3 := (char_of_eq_neg_three (isFundamentalDiscr_discr hK) h3).2
      rw [hc3, h3] at hrel
      simp only [h3, ↓reduceIte]
      norm_num at hrel ⊢
      omega
    · simp only [h4, h3, ↓reduceIte] at hrel ⊢
      rcases hq with hc | hc | hc <;> rw [hc] at hrel ⊢ <;> omega

/-- Specialization of `finrank_hilbertClassField_rayClassField_three` to `discr K < -4`. -/
theorem finrank_hilbertClassField_rayClassField_three_of_discr_lt_neg_four (hK : finrank ℚ K = 2)
    (hd : discr K < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) =
      (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have h4 : discr K ≠ -4 := by omega
  have h3 : discr K ≠ -3 := by omega
  simp [finrank_hilbertClassField_rayClassField_three hK, h4, h3]

/-- **Degree of `K_(6)` over the Hilbert class field** for all imaginary quadratic fields. -/
theorem finrank_hilbertClassField_rayClassField_six (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 6))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 6))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) =
      (if discr K = -4 ∨ discr K = -3 then 1
        else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat) *
        (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have hrel := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
      (Modulus.spanNat_infinitePart (K := K) 6)
  rw [Nat.cast_mul, Modulus.spanNat_finitePart, Nat.cast_ofNat, card_units_quotient_span_six hK,
    index_unitsCongruenceSubgroup_spanNat_of_three_le hK (by decide)] at hrel
  have hq2 := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 2
  have hq3 := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 3
  by_cases h4 : discr K = -4
  · obtain ⟨hc2, hc3⟩ := char_of_eq_neg_four (isFundamentalDiscr_discr hK) h4
    rw [hc2, hc3, h4] at hrel
    simp only [h4, true_or, ↓reduceIte]
    rw [hc3]
    norm_num at hrel ⊢
    omega
  · by_cases h3 : discr K = -3
    · obtain ⟨hc2, hc3⟩ := char_of_eq_neg_three (isFundamentalDiscr_discr hK) h3
      rw [hc2, hc3, h3] at hrel
      simp only [h3, or_true, ↓reduceIte]
      rw [hc3]
      norm_num at hrel ⊢
      omega
    · simp only [h4, h3, or_self, ↓reduceIte] at hrel ⊢
      rcases hq2 with hc2 | hc2 | hc2 <;> rcases hq3 with hc3 | hc3 | hc3 <;>
        (rw [hc2, hc3] at hrel ⊢; rw [← Int.toNat_mul (by omega) (by omega)]; omega)

/-- **Degree of `K_(8)` over the Hilbert class field** for all imaginary quadratic fields. -/
theorem finrank_hilbertClassField_rayClassField_eight (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 8))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 8))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) =
      8 * (if discr K = -4 ∨ discr K = -3 then 1
        else (2 - fundamentalDiscriminantChar (discr K)
          (isFundamentalDiscr_discr hK) 2).toNat) := by
  have hrel := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
      (Modulus.spanNat_infinitePart (K := K) 8)
  rw [Nat.cast_mul, Modulus.spanNat_finitePart, Nat.cast_ofNat, card_units_quotient_span_eight hK,
    index_unitsCongruenceSubgroup_spanNat_of_three_le hK (by decide)] at hrel
  have hq2 := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 2
  by_cases h4 : discr K = -4
  · have hc2 := (char_of_eq_neg_four (isFundamentalDiscr_discr hK) h4).1
    rw [hc2, h4] at hrel
    simp only [h4, true_or, ↓reduceIte]
    norm_num at hrel ⊢
    omega
  · by_cases h3 : discr K = -3
    · have hc2 := (char_of_eq_neg_three (isFundamentalDiscr_discr hK) h3).1
      rw [hc2, h3] at hrel
      simp only [h3, or_true, ↓reduceIte]
      norm_num at hrel ⊢
      omega
    · simp only [h4, h3, or_self, ↓reduceIte] at hrel ⊢
      rcases hq2 with hc2 | hc2 | hc2 <;> rw [hc2] at hrel ⊢ <;> omega

omit [IsTotallyComplex K] in
/-- Relate `[rayClassField 𝔪 : K]` to `classNumber K * [rayClassField 𝔪 : hilbertClassField K]`
using the canonical inclusion inside `Kᵃᵇ`. -/
private theorem classNumber_mul_eq_finrank_rayClassField (𝔪 : Modulus K) {a : ℕ}
    (h𝔪 : ∀ [Algebra (hilbertClassField K) (rayClassField 𝔪)]
      [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)],
        Module.finrank (hilbertClassField K) (rayClassField 𝔪) = a) :
    classNumber K * a = Module.finrank K (rayClassField 𝔪) := by
  let : Algebra (hilbertClassField K) (rayClassField 𝔪) :=
    (IntermediateField.inclusion (hilbertClassField_le_rayClassField 𝔪)).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField 𝔪) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Free K (hilbertClassField K) := .of_divisionRing K (hilbertClassField K)
  have : Module.Free (hilbertClassField K) (rayClassField 𝔪) :=
    .of_divisionRing (hilbertClassField K) (rayClassField 𝔪)
  rw [← finrank_hilbertClassField K, ← h𝔪,
    Module.finrank_mul_finrank K (hilbertClassField K) (rayClassField 𝔪)]

omit [IsTotallyComplex K] in
/-- Deduce `[rayClassField 𝔫 : rayClassField 𝔪]` from the degrees of `rayClassField 𝔪` and
`rayClassField 𝔫` over `hilbertClassField K` by cancelling `classNumber K > 0` over `K`. -/
private theorem finrank_mul_finrank_via_hilbertClassField {𝔪 𝔫 : Modulus K}
    [Algebra (rayClassField 𝔪) (rayClassField 𝔫)]
    [IsScalarTower K (rayClassField 𝔪) (rayClassField 𝔫)]
    {a b : ℕ}
    (h𝔪 : ∀ [Algebra (hilbertClassField K) (rayClassField 𝔪)]
      [IsScalarTower K (hilbertClassField K) (rayClassField 𝔪)],
        Module.finrank (hilbertClassField K) (rayClassField 𝔪) = a)
    (h𝔫 : ∀ [Algebra (hilbertClassField K) (rayClassField 𝔫)]
      [IsScalarTower K (hilbertClassField K) (rayClassField 𝔫)],
        Module.finrank (hilbertClassField K) (rayClassField 𝔫) = b) :
    a * Module.finrank (rayClassField 𝔪) (rayClassField 𝔫) = b := by
  have : Module.Free K (rayClassField 𝔪) := .of_divisionRing K (rayClassField 𝔪)
  have : Module.Free (rayClassField 𝔪) (rayClassField 𝔫) :=
    .of_divisionRing (rayClassField 𝔪) (rayClassField 𝔫)
  have hmul := Module.finrank_mul_finrank K (rayClassField 𝔪) (rayClassField 𝔫)
  rw [← classNumber_mul_eq_finrank_rayClassField 𝔪 h𝔪,
    ← classNumber_mul_eq_finrank_rayClassField 𝔫 h𝔫, mul_assoc] at hmul
  exact Nat.mul_left_cancel (NumberField.classNumber_pos K) hmul

/-- **Unconditional relative degree `[K_(6) : K_(2)] = 3 - χ_D(3)`** for every imaginary quadratic
field `K` (including `D = -4` and `D = -3`, since the unit congruence subgroup shrinks from `{±1}`
to `{1}` between levels `2` and `6`). -/
theorem finrank_rayClassField_two_six (hK : finrank ℚ K = 2)
    [Algebra (rayClassField (Modulus.spanNat K 2)) (rayClassField (Modulus.spanNat K 6))]
    [IsScalarTower K (rayClassField (Modulus.spanNat K 2))
      (rayClassField (Modulus.spanNat K 6))] :
    Module.finrank (rayClassField (Modulus.spanNat K 2))
        (rayClassField (Modulus.spanNat K 6)) =
      (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have hmul := finrank_mul_finrank_via_hilbertClassField
    (finrank_hilbertClassField_rayClassField_two hK)
    (finrank_hilbertClassField_rayClassField_six hK)
  have hq2 := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 2
  have hpos : 0 < (if discr K = -4 ∨ discr K = -3 then 1
      else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat) := by
    split_ifs
    · omega
    · rcases hq2 with hc | hc | hc <;> rw [hc] <;> omega
  exact Nat.mul_left_cancel hpos hmul

/-- **Unconditional relative degree `[K_(8) : K_(2)] = 8`** for every imaginary quadratic field `K`
(including `D = -4` and `D = -3`). -/
theorem finrank_rayClassField_two_eight (hK : finrank ℚ K = 2)
    [Algebra (rayClassField (Modulus.spanNat K 2)) (rayClassField (Modulus.spanNat K 8))]
    [IsScalarTower K (rayClassField (Modulus.spanNat K 2))
      (rayClassField (Modulus.spanNat K 8))] :
    Module.finrank (rayClassField (Modulus.spanNat K 2))
        (rayClassField (Modulus.spanNat K 8)) = 8 := by
  have hmul := finrank_mul_finrank_via_hilbertClassField
    (finrank_hilbertClassField_rayClassField_two hK)
    (finrank_hilbertClassField_rayClassField_eight hK)
  rw [mul_comm 8] at hmul
  have hq2 := fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) 2
  have hpos : 0 < (if discr K = -4 ∨ discr K = -3 then 1
      else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat) := by
    split_ifs
    · omega
    · rcases hq2 with hc | hc | hc <;> rw [hc] <;> omega
  exact Nat.mul_left_cancel hpos hmul

end Degrees

end TauCeti.ClassFieldTheory
