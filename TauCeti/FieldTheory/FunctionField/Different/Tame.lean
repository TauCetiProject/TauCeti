/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.RingTheory.DedekindDomain.Different

/-!
# The different exponent of a tame or wild place

Let `F' / k'` be an extension of the algebraic function field `F / k` with `F' / F` finite and
separable, and let `P'` be a place of `F' / k'` over `P = P'.restrict k F`.  Dedekind's different
theorem (Stichtenoth, Theorem 3.5.1) says that `d(P' ∣ P) ≥ e(P' ∣ P) - 1` always, with equality
exactly when the place is **tame**.  The inequality is
`TauCeti.Place.ramificationIdx_le_differentExponent_add_one`; this file introduces the tame/wild
vocabulary (Stichtenoth, Definition 3.5.4) as `TauCeti.Place.IsTame` and `TauCeti.Place.IsWild` and
supplies the second part: `e(P' ∣ P) = d(P' ∣ P) + 1` holds exactly at the tame places, those where
the residue extension of the local model is separable and the residue characteristic does not
divide `e(P' ∣ P)`, and at the wild places `d(P' ∣ P) ≥ e(P' ∣ P)` (Stichtenoth, Corollary 3.5.5).

Everything is read on the local model `𝒪_P ⊆ 𝒪'_P` of
`TauCeti/FieldTheory/FunctionField/Different/Basic.lean`, where the different exponent lives, so
the two conditions are stated for the centre `𝔓` of `P'` on `𝒪'_P` over the maximal ideal of the
discrete valuation ring `𝒪_P`, whose residue ring is the residue field of `P`
(`TauCeti.Place.center_restrict_asIdeal_eq_maximalIdeal`).  This is the same ideal-theoretic
reading of the residue extension that `TauCeti.Place.differentExponent_eq_zero_iff` uses for
unramifiedness.  The theorem behind it is
`TauCeti.ramificationIdx_le_multiplicity_differentIdeal_iff`.

Stichtenoth assumes a perfect constant field, under which residue extensions are separable and
tameness is the single condition that the characteristic does not divide `e(P' ∣ P)`.  No such
assumption is made here: over an imperfect residue field an inseparable residue extension already
forces `d(P' ∣ P) ≥ e(P' ∣ P)`, even at `e(P' ∣ P) = 1`, so the separability condition is part of
the statement.

## Main results

* `TauCeti.Place.IsTame` and `TauCeti.Place.IsWild`: tame and wild places, with
  `TauCeti.Place.isTame_iff` and `TauCeti.Place.isWild_iff` unfolding the two predicates into
  their defining residue conditions.
* `TauCeti.Place.ramificationIdx_eq_differentExponent_add_one_iff`: **Dedekind's different theorem,
  second part** (Stichtenoth, Theorem 3.5.1(b)), in the subtraction-free form
  `e(P' ∣ P) = d(P' ∣ P) + 1`, holding exactly at the tame places.
* `TauCeti.Place.ramificationIdx_le_differentExponent_iff`: `e(P' ∣ P) ≤ d(P' ∣ P)` exactly at the
  wild places (Stichtenoth, Corollary 3.5.5).
* `TauCeti.Place.relativeDegree_eq_one_of_isSepClosed_of_differentExponent_eq_zero`: a place with
  zero different exponent over a separably closed residue field has relative degree one.
* `TauCeti.Divisor.coeff_different_add_one_eq_ramificationIdx_iff` and
  `TauCeti.Divisor.ramificationIdx_le_coeff_different_iff`: the same statements read on the
  different divisor.
* `TauCeti.Divisor.tameDifferent`: the divisor `∑_{P'} (e(P' ∣ P) - 1) · P'`, with
  `TauCeti.Divisor.tameDifferent_le_different` and `TauCeti.Divisor.tameDifferent_eq_different_iff`:
  it is bounded by the different divisor, with equality exactly when every place is tame.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.5.4, Theorem 3.5.1 and Corollary 3.5.5.
-/

public section

open IsDedekindDomain

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k F] [Algebra F F'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
variable [Algebra.IsSeparable F F']

attribute [local instance 10] Place.algebraIntegersExtension
  Place.isScalarTowerIntegersExtension

namespace Place

variable (k F) (P' : Place k' F')

/-- A place `P'` of `F'` is **tame** over `F` (Stichtenoth, Definition 3.5.4) when the residue
extension of its local model is separable and its ramification index is invertible in the residue
field of `P = P'.restrict k F`.

The residue extension is read on the local model, between the residue ring of the maximal ideal of
the discrete valuation ring `𝒪_P` — which is the residue field of `P`, by
`TauCeti.Place.center_restrict_asIdeal_eq_maximalIdeal` — and the residue ring of the centre of
`P'` on `𝒪'_P`.  Stichtenoth assumes a perfect constant field, where the separability condition is
automatic; unlike Stichtenoth's *tamely ramified*, an unramified place with separable residue
extension also counts as tame here. -/
def IsTame : Prop :=
  Algebra.IsSeparable
      (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
      (integralClosure ((P'.restrict k F).integers) F' ⧸ (centerIntegralClosure k F P').asIdeal) ∧
    ((ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠ 0

/-- A place is tame exactly when the residue extension of its local model is separable and its
ramification index is invertible in the residue field of `P`. -/
@[simp]
theorem isTame_iff :
    IsTame k F P' ↔
      Algebra.IsSeparable
          (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
          (integralClosure ((P'.restrict k F).integers) F' ⧸
            (centerIntegralClosure k F P').asIdeal) ∧
        ((ramificationIdx F P' : ℕ) :
          ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠
          0 :=
  Iff.rfl

/-- A place `P'` of `F'` is **wild** over `F` (Stichtenoth, Definition 3.5.4) when it is not tame:
the residue extension of its local model is inseparable or its ramification index vanishes in the
residue field of `P`. -/
def IsWild : Prop :=
  ¬ IsTame k F P'

/-- A place is wild exactly when the residue extension of its local model is inseparable or its
ramification index vanishes in the residue field of `P`. -/
@[simp]
theorem isWild_iff :
    IsWild k F P' ↔
      ¬ Algebra.IsSeparable
          (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
          (integralClosure ((P'.restrict k F).integers) F' ⧸
            (centerIntegralClosure k F P').asIdeal) ∨
        ((ramificationIdx F P' : ℕ) :
          ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) =
          0 := by
  rw [IsWild, IsTame, not_and_or, not_not]

/-- **The different exponent reaches the ramification index exactly at the wild places**
(Stichtenoth, Corollary 3.5.5): `e(P' ∣ P) ≤ d(P' ∣ P)` if and only if `P'` is wild. -/
theorem ramificationIdx_le_differentExponent_iff :
    ramificationIdx F P' ≤ differentExponent k F P' ↔ IsWild k F P' := by
  have hS := algebraMap_mem_integers_of_mem_integralClosure k F P'
  have hpbot : IsLocalRing.maximalIdeal ((P'.restrict k F).integers) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field _
  have hmax : (centerIntegralClosure k F P').asIdeal.IsMaximal :=
    (centerIntegralClosure k F P').isPrime.isMaximal (centerIntegralClosure k F P').ne_bot
  have hidx : (centerIntegralClosure k F P').asIdeal.ramificationIdx
      ((P'.restrict k F).integers) = ramificationIdx F P' := by
    rw [centerIntegralClosure_def]
    exact (ramificationIdx_eq_ramificationIdx_center
      (R := ((P'.restrict k F).integers)) k F P' hS).symm
  rw [isWild_iff, differentExponent_def, ← hidx]
  exact ramificationIdx_le_multiplicity_differentIdeal_iff _ hpbot _

/-- **Dedekind's different theorem, second part** (Stichtenoth, Theorem 3.5.1(b)): the different
exponent of `P'` is exactly one less than its ramification index if and only if `P'` is tame.  It
is stated as `e(P' ∣ P) = d(P' ∣ P) + 1` so that no truncated subtraction of natural numbers
appears. -/
theorem ramificationIdx_eq_differentExponent_add_one_iff :
    ramificationIdx F P' = differentExponent k F P' + 1 ↔ IsTame k F P' := by
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  have hiff : ramificationIdx F P' = differentExponent k F P' + 1 ↔
      ¬ ramificationIdx F P' ≤ differentExponent k F P' := ⟨fun _ ↦ by omega, fun _ ↦ by omega⟩
  rw [hiff, ramificationIdx_le_differentExponent_iff, IsWild, not_not]

/-- If the residue field of the place below `P'` is separably closed and the different exponent
of `P'` vanishes, then the relative residue degree of `P'` is one. -/
theorem relativeDegree_eq_one_of_isSepClosed_of_differentExponent_eq_zero
    (P' : Place k F') [IsSepClosed (P'.restrict k F).ResidueField]
    (hd : differentExponent k F P' = 0) :
    relativeDegree k F P' = 1 := by
  -- The zero different exponent forces the place to be tame.
  have htame : P'.IsTame k F :=
    (P'.ramificationIdx_eq_differentExponent_add_one_iff k F).mp <| by
      have := P'.ramificationIdx_le_differentExponent_add_one k F
      have := P'.ramificationIdx_pos F
      omega
  -- Tameness supplies separability of the residue extension on the local model.
  have hsep := (P'.isTame_iff k F).mp htame |>.1
  let _ : IsScalarTower k (P'.restrict k F).integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply (P'.restrict k F).integers F F',
      ← IsScalarTower.algebraMap_apply k (P'.restrict k F).integers F,
      ← IsScalarTower.algebraMap_apply k F F']
  have hconstants : ∀ c : k, algebraMap k F' c ∈
      integralClosure (P'.restrict k F).integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k (integralClosure (P'.restrict k F).integers F') :=
    ((algebraMap k F').codRestrict _ hconstants).toAlgebra
  let _ : IsScalarTower k (integralClosure (P'.restrict k F).integers F') F' :=
    .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra (P'.restrict k F).ResidueField
      (integralClosure (P'.restrict k F).integers F' ⧸
        (P'.centerIntegralClosure k F).asIdeal) :=
    Ideal.Quotient.algebraOfLiesOver (P'.centerIntegralClosure k F).asIdeal
      (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
  let _ : Algebra.IsSeparable (P'.restrict k F).ResidueField
      (integralClosure (P'.restrict k F).integers F' ⧸
        (P'.centerIntegralClosure k F).asIdeal) := hsep
  have hsepClosed : IsSepClosed (P'.restrict k F).ResidueField := inferInstance
  let _ : (P'.centerIntegralClosure k F).asIdeal.IsMaximal :=
    (P'.centerIntegralClosure k F).isPrime.isMaximal
      (P'.centerIntegralClosure k F).ne_bot
  let _ : Field ((P'.restrict k F).integers ⧸
      IsLocalRing.maximalIdeal (P'.restrict k F).integers) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
  let _ : Field (integralClosure (P'.restrict k F).integers F' ⧸
      (P'.centerIntegralClosure k F).asIdeal) :=
    Ideal.Quotient.field (P'.centerIntegralClosure k F).asIdeal
  let _ : IsSepClosed ((P'.restrict k F).integers ⧸
      IsLocalRing.maximalIdeal (P'.restrict k F).integers) :=
    ⟨hsepClosed.splits_of_separable⟩
  -- Identify relative degree with the local-model inertia degree, which must be one.
  rw [P'.relativeDegree_eq_inertiaDeg_center (R := (P'.restrict k F).integers) k F
    (P'.algebraMap_mem_integers_of_mem_integralClosure k F)]
  rw [← P'.centerIntegralClosure_def k F]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
      (P'.centerIntegralClosure k F).asIdeal,
    Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact IsSepClosed.algebraMap_bijective _ _

end Place

namespace Divisor

/-- **The different divisor at a wild place** (Stichtenoth, Corollary 3.5.5): the coefficient of
`P'` in `Diff(F'/F)` is at least `e(P' ∣ P)` if and only if `P'` is wild. -/
theorem ramificationIdx_le_coeff_different_iff (hF : IsFunctionField k F) (P' : Place k' F') :
    (Place.ramificationIdx F P' : ℤ) ≤ (different k' F' hF).coeff P' ↔ Place.IsWild k F P' := by
  rw [coeff_different, ← Place.ramificationIdx_le_differentExponent_iff]
  norm_cast

/-- **The different divisor detects tameness** (Stichtenoth, Theorem 3.5.1(b) and Remark 3.4.4):
the coefficient of `P'` in `Diff(F'/F)` is `e(P' ∣ P) - 1`, stated without subtraction, exactly
when `P'` is tame. -/
theorem coeff_different_add_one_eq_ramificationIdx_iff (hF : IsFunctionField k F)
    (P' : Place k' F') :
    (different k' F' hF).coeff P' + 1 = (Place.ramificationIdx F P' : ℤ) ↔ Place.IsTame k F P' := by
  rw [coeff_different, ← Place.ramificationIdx_eq_differentExponent_add_one_iff, eq_comm]
  norm_cast

open AlgebraicGeometry

variable (k' F') (hF : IsFunctionField k F)

/-- **The tame different** `∑_{P'} (e(P' ∣ P) - 1) · P'` of a finite separable extension `F' / F`
of an algebraic function field: the value the different divisor `Diff(F'/F)` would take if every
place of `F'` were tame (Stichtenoth, Theorem 3.5.1(b)).  It is a divisor because a place with
`e(P' ∣ P) > 1` lies in the support of the different, and it is the lower bound for the different
in the Hurwitz genus formula (Stichtenoth, Corollary 3.5.6). -/
noncomputable def tameDifferent : Divisor k' F' :=
  Finsupp.ofSupportFinite (fun P' ↦ (Place.ramificationIdx F P' : ℤ) - 1)
    ((different k' F' hF).support.finite_toSet.subset fun P' hP' ↦ by
      have hne : (Place.ramificationIdx F P' : ℤ) - 1 ≠ 0 := hP'
      have hpos := Place.ramificationIdx_pos F P'
      exact mem_support_different_of_one_lt_ramificationIdx k' F' hF (by omega))

/-- The coefficient of `P'` in the tame different is `e(P' ∣ P) - 1`. -/
@[simp]
theorem coeff_tameDifferent (P' : Place k' F') :
    (tameDifferent k' F' hF).coeff P' = (Place.ramificationIdx F P' : ℤ) - 1 :=
  (rfl)

/-- **The tame different is effective**: every ramification index is positive. -/
theorem zero_le_tameDifferent : 0 ≤ tameDifferent k' F' hF := by
  refine WeilDivisor.isEffective_iff_zero_le.mp <| (WeilDivisor.isEffective_iff _).mpr fun P' ↦ ?_
  have := Place.ramificationIdx_pos F P'
  rw [coeff_tameDifferent]
  omega

/-- **Dedekind's different theorem, first part, as an inequality of divisors** (Stichtenoth,
Theorem 3.5.1(a)): the tame different is bounded by the different divisor. -/
theorem tameDifferent_le_different : tameDifferent k' F' hF ≤ different k' F' hF := by
  refine WeilDivisor.le_iff.mpr fun P' ↦ ?_
  have := ramificationIdx_le_coeff_different_add_one k' F' hF P'
  rw [coeff_tameDifferent]
  omega

/-- **The different divisor is the tame different exactly when every place is tame**
(Stichtenoth, Theorem 3.5.1(b)). -/
@[simp]
theorem tameDifferent_eq_different_iff :
    tameDifferent k' F' hF = different k' F' hF ↔ ∀ P' : Place k' F', Place.IsTame k F P' := by
  simp only [← coeff_different_add_one_eq_ramificationIdx_iff hF,
    WeilDivisor.ext_iff, coeff_tameDifferent]
  exact forall_congr' fun P' ↦ by omega

end Divisor

end TauCeti
