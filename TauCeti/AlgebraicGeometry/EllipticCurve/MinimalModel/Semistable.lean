/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation

/-!
# Semistable elliptic curves over a Dedekind domain

Let `O` be a Dedekind domain with fraction field `K`. An elliptic curve over `K` is
**semistable over `O`** when its reduction at every height-one prime is either good or
multiplicative, equivalently never additive. Reduction is a property of a minimal equation, so
the definition applies Mathlib's reduction predicates to a chosen local minimal equation.

This file proves both local characterizations of semistability. At a discrete valuation ring, a
minimal equation is not additive exactly when either its discriminant or its `c₄` has valuation
one. Globally, this criterion is imposed at every height-one prime. It also proves that the
predicate is independent of the equation presenting the curve: changing variables changes the
chosen local minimal equation, but the two minimal equations have the same discriminant and `c₄`
valuations.

## Main definitions

* `WeierstrassCurve.IsSemistable`: the local minimal equation has no additive reduction at every
  height-one prime.

## Main results

* `WeierstrassCurve.isSemistable_iff_forall_hasGoodReduction_or_hasMultiplicativeReduction`:
  semistability is good or multiplicative reduction everywhere.
* `WeierstrassCurve.not_hasAdditiveReduction_iff_valuation_Δ_eq_one_or_valuation_c₄_eq_one`:
  the local valuation criterion on a minimal equation.
* `WeierstrassCurve.isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one`:
  the corresponding global criterion.
* `WeierstrassCurve.isSemistable_smul`: semistability is invariant under a change of variables.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and VIII.8.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing

/-! ### Invariance of the local valuations -/

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The discriminants of the chosen minimal equations have the same valuation after a change of
variables. -/
@[simp]
theorem valuation_Δ_minimal_smul (D : VariableChange K) (W : WeierstrassCurve K) :
    valuation K (maximalIdeal R) ((D • W).minimal R).Δ =
      valuation K (maximalIdeal R) (W.minimal R).Δ := by
  obtain ⟨C, hC⟩ := exists_smul_minimal_eq_minimal R D W
  exact valuation_Δ_eq_of_isMinimal_smul R C hC

/-- The `c₄` invariants of the chosen minimal equations have the same valuation after a change of
variables. -/
@[simp]
theorem valuation_c₄_minimal_smul (D : VariableChange K) (W : WeierstrassCurve K)
    [W.IsElliptic] :
    valuation K (maximalIdeal R) ((D • W).minimal R).c₄ =
      valuation K (maximalIdeal R) (W.minimal R).c₄ := by
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal R
  let hEll : (W.minimal R).IsElliptic := hC₀ ▸ inferInstance
  obtain ⟨C, hC⟩ := exists_smul_minimal_eq_minimal R D W
  have hu := @valuation_u_eq_one_of_isMinimal_smul R _ _ _ K _ _ _
    (W.minimal R) ((D • W).minimal R) _ _ hEll C hC
  rw [← hC, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀, hu]
  simp

/-! ### The local criterion -/

/-- A minimal equation is not additively reduced exactly when its discriminant or its `c₄` is a
unit at the place. These are respectively the good- and multiplicative-reduction cases. -/
theorem not_hasAdditiveReduction_iff_valuation_Δ_eq_one_or_valuation_c₄_eq_one
    (W : WeierstrassCurve K) [IsMinimal R W] :
    ¬ W.HasAdditiveReduction R ↔
      valuation K (maximalIdeal R) W.Δ = 1 ∨
        valuation K (maximalIdeal R) W.c₄ = 1 := by
  constructor
  · intro h
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
        (W := W) with hgood | hmult | hadd
    · exact Or.inl hgood.goodReduction
    · exact Or.inr hmult.multiplicativeReduction
    · exact (h hadd).elim
  · rintro (hΔ | hc₄) hadd
    · exact hadd.badReduction.ne hΔ
    · exact hadd.additiveReduction.ne hc₄

/-! ### Semistability over a Dedekind domain -/

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F]

/-- **Semistability over a Dedekind domain**: at every height-one prime, a local minimal equation
has no additive reduction. Equivalently, the reduction is good or multiplicative everywhere.

The predicate is stated on an equation but depends only on its `F`-isomorphism class, as proved by
`isSemistable_smul`. -/
def IsSemistable (W : WeierstrassCurve F) [W.IsElliptic] : Prop :=
  ∀ v : HeightOneSpectrum O,
    ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal)

variable {O}

/-- Semistability, unfolded. -/
@[simp]
theorem isSemistable_iff {W : WeierstrassCurve F} [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
        (Localization.AtPrime v.asIdeal) :=
  Iff.rfl

/-- A semistable curve has no additive reduction at any height-one prime. -/
theorem IsSemistable.not_hasAdditiveReduction {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsSemistable O W) (v : HeightOneSpectrum O) :
    ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal) :=
  hW v

/-- A curve with no additive reduction at any height-one prime is semistable. -/
theorem IsSemistable.of_forall_not_hasAdditiveReduction {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : ∀ v : HeightOneSpectrum O,
      ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
        (Localization.AtPrime v.asIdeal)) :
    IsSemistable O W :=
  hW

/-- **A curve is semistable exactly when it has good or multiplicative reduction at every
height-one prime.** -/
theorem isSemistable_iff_forall_hasGoodReduction_or_hasMultiplicativeReduction
    (W : WeierstrassCurve F) [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
          (Localization.AtPrime v.asIdeal) ∨
        (W.minimal (Localization.AtPrime v.asIdeal)).HasMultiplicativeReduction
          (Localization.AtPrime v.asIdeal) := by
  rw [isSemistable_iff]
  refine forall_congr' fun v ↦ ?_
  constructor
  · intro h
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
        (R := Localization.AtPrime v.asIdeal)
        (W := W.minimal (Localization.AtPrime v.asIdeal)) with hgood | hmult | hadd
    · exact Or.inl hgood
    · exact Or.inr hmult
    · exact (h hadd).elim
  · rintro (hgood | hmult)
    · exact hgood.not_hasAdditiveReduction
    · exact hmult.not_hasAdditiveReduction

/-- **The valuation criterion for semistability**: at every height-one prime, a local minimal
equation has discriminant of valuation one (good reduction) or `c₄` of valuation one
(multiplicative reduction). -/
theorem isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one
    (W : WeierstrassCurve F) [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      valuation F (maximalIdeal (Localization.AtPrime v.asIdeal))
          (W.minimal (Localization.AtPrime v.asIdeal)).Δ = 1 ∨
        valuation F (maximalIdeal (Localization.AtPrime v.asIdeal))
          (W.minimal (Localization.AtPrime v.asIdeal)).c₄ = 1 := by
  rw [isSemistable_iff]
  exact forall_congr' fun v ↦
    not_hasAdditiveReduction_iff_valuation_Δ_eq_one_or_valuation_c₄_eq_one
      (Localization.AtPrime v.asIdeal) (W.minimal (Localization.AtPrime v.asIdeal))

/-- **Semistability is invariant under a change of variables.** -/
@[simp]
theorem isSemistable_smul (D : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] :
    IsSemistable O (D • W) ↔ IsSemistable O W := by
  rw [isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one,
    isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one]
  refine forall_congr' fun v ↦ ?_
  rw [valuation_Δ_minimal_smul, valuation_c₄_minimal_smul]

end WeierstrassCurve

end
