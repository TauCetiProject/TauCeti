/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

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

Finally, semistability is preserved by base change (Silverman VII.5.4(b)). Locally, no additive
reduction is the same as having *some* integral model with a unit discriminant or a unit `c₄`, not
necessarily the chosen minimal one, and such a model stays integral with that unit along any map of
discrete valuation rings compatible with the fraction fields. Globally, a height-one prime of the
larger Dedekind domain lies over a height-one prime of the smaller one, whose local ring maps to its
own, or over zero, where the curve has good reduction.

## Main definitions

* `WeierstrassCurve.IsSemistable`: an elliptic equation whose local minimal equation has no
  additive reduction at any height-one prime.

## Main results

* `WeierstrassCurve.isSemistable_iff_forall_hasGoodReduction_or_hasMultiplicativeReduction`:
  semistability is good or multiplicative reduction everywhere.
* `WeierstrassCurve.not_hasAdditiveReduction_iff_valuation_Δ_eq_one_or_valuation_c₄_eq_one`:
  the local valuation criterion on a minimal equation.
* `WeierstrassCurve.isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one`:
  the corresponding global criterion.
* `WeierstrassCurve.isSemistable_smul`: semistability is invariant under a change of variables.
* `WeierstrassCurve.not_hasAdditiveReduction_minimal_iff_exists_isUnit`: no additive reduction
  means some integral model has a unit discriminant or a unit `c₄`.
* `WeierstrassCurve.not_hasAdditiveReduction_minimal_baseChange`: no additive reduction is
  preserved along a map of discrete valuation rings.
* `WeierstrassCurve.IsSemistable.baseChange`: semistability is preserved by base change along an
  extension of Dedekind domains.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and VIII.8.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The local criterion -/

/-- A minimal equation is not additively reduced exactly when its discriminant or its `c₄` is a
unit at the place. A unit discriminant gives good reduction; a unit `c₄` gives multiplicative
reduction when the discriminant is not a unit.

This is valuation arithmetic on the equation itself, so no ellipticity is needed; `IsSemistable`
adds that hypothesis where the trichotomy is read as a reduction type. -/
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

/-- **An elliptic curve has no additive reduction exactly when some integral model has a unit
discriminant or a unit `c₄`.** The model need not be minimal: such a model is automatically
minimal, and it then shares its discriminant and `c₄` valuations with the chosen minimal
equation. -/
theorem not_hasAdditiveReduction_minimal_iff_exists_isUnit (W : WeierstrassCurve K)
    [W.IsElliptic] :
    ¬ (W.minimal R).HasAdditiveReduction R ↔
      ∃ (W₀ : WeierstrassCurve R) (C : VariableChange K),
        (IsUnit W₀.Δ ∨ IsUnit W₀.c₄) ∧ C • W = W₀.baseChange K := by
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal R
  have : (W.minimal R).IsElliptic := hC₀ ▸ inferInstance
  have hval (r : R) : valuation K (maximalIdeal R) (algebraMap R K r) = 1 ↔ IsUnit r :=
    (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem.trans notMem_maximalIdeal
  rw [not_hasAdditiveReduction_iff_valuation_Δ_eq_one_or_valuation_c₄_eq_one]
  constructor
  · -- the integral model of the chosen minimal equation is a witness
    intro h
    refine ⟨(W.minimal R).integralModel R, C₀, ?_,
      hC₀.trans (baseChange_integralModel_eq R _).symm⟩
    rwa [← integralModel_Δ_eq R (W.minimal R), ← integralModel_c₄_eq R (W.minimal R),
      hval, hval] at h
  · -- a witness is minimal, so it shares both valuations with the chosen minimal equation
    rintro ⟨W₀, C, hunit, hC⟩
    have : IsIntegral R (C • W) := ⟨⟨W₀, hC⟩⟩
    have hv : valuation K (maximalIdeal R) (C • W).Δ = 1 ∨
        valuation K (maximalIdeal R) (C • W).c₄ = 1 := by
      rwa [hC, baseChange, map_Δ, map_c₄, hval, hval]
    have : IsMinimal R (C • W) := hv.elim (isMinimal_of_valuation_Δ_eq_one R _)
      (isMinimal_of_valuation_c₄_eq_one R _)
    have hD : (C₀ * C⁻¹) • (C • W) = W.minimal R := by rw [mul_smul, inv_smul_smul, hC₀]
    rwa [valuation_Δ_eq_of_isMinimal_smul R _ hD, valuation_c₄_eq_of_isMinimal_smul R _ hD]

/-! ### Base change -/

/-- The base change of an elliptic curve is elliptic. Mathlib's instance is stated for
`WeierstrassCurve.map`, which instance search does not see through the plain `def`
`WeierstrassCurve.baseChange`; this local copy avoids importing the affine point theory that
carries the global one. -/
local instance isElliptic_baseChange {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (W : WeierstrassCurve A) [W.IsElliptic] : (W.baseChange B).IsElliptic :=
  inferInstanceAs (W.map _).IsElliptic

section BaseChange

variable (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R S]

/-- **Absence of additive reduction is preserved by base change.** Let `S` be a discrete
valuation ring with fraction field `L`, receiving `R` compatibly with `K → L`. If an elliptic curve
over `K` has good or multiplicative reduction over `R`, then over `L` it has good or multiplicative
reduction over `S`. No ramification hypothesis is needed and `R → S` need not be local: a unit
discriminant or a unit `c₄` of an integral model over `R` stays a unit over `S`. This is Silverman,
*AEC*, VII.5.4(b). -/
theorem not_hasAdditiveReduction_minimal_baseChange {W : WeierstrassCurve K} [W.IsElliptic]
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (h : ¬ (W.minimal R).HasAdditiveReduction R) :
    ¬ ((W.baseChange L).minimal S).HasAdditiveReduction S := by
  obtain ⟨W₀, C, hunit, hC⟩ := (not_hasAdditiveReduction_minimal_iff_exists_isUnit R W).mp h
  refine (not_hasAdditiveReduction_minimal_iff_exists_isUnit S (W.baseChange L)).mpr
    ⟨W₀.map (algebraMap R S), C.baseChange L, ?_, ?_⟩
  · simpa [map_Δ, map_c₄] using hunit.imp (IsUnit.map _) (IsUnit.map _)
  · rw [baseChange, VariableChange.baseChange, map_variableChange, hC, baseChange, baseChange,
      map_map, map_map, hRS]

end BaseChange

/-! ### Semistability over a Dedekind domain -/

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F]

/-- **Semistability over a Dedekind domain**: at every height-one prime, a local minimal equation
has no additive reduction. Equivalently, the reduction is good or multiplicative everywhere.

The predicate is stated on an elliptic equation but depends only on its `F`-isomorphism class, as
proved by `isSemistable_smul`. The ellipticity instance excludes singular cubics, which have no
reduction type in the good/multiplicative/additive trichotomy of elliptic curves. -/
def IsSemistable (W : WeierstrassCurve F) [_hE : W.IsElliptic] : Prop :=
  ∀ v : HeightOneSpectrum O,
    ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal)

variable {O}

/-- Semistability means that every local minimal equation has no additive reduction. -/
theorem isSemistable_iff {W : WeierstrassCurve F} [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
        (Localization.AtPrime v.asIdeal) :=
  Iff.rfl

/-- A semistable curve has no additive reduction at any height-one prime. -/
theorem IsSemistable.not_hasAdditiveReduction {W : WeierstrassCurve F} [W.IsElliptic]
    (h : IsSemistable O W) (v : HeightOneSpectrum O) :
    ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal) :=
  h v

/-- A curve with no additive reduction at every height-one prime is semistable. -/
theorem IsSemistable.of_forall_not_hasAdditiveReduction {W : WeierstrassCurve F} [W.IsElliptic]
    (h : ∀ v : HeightOneSpectrum O,
      ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
        (Localization.AtPrime v.asIdeal)) :
    IsSemistable O W :=
  h

/-- **A curve is semistable exactly when it has good or multiplicative reduction at every
height-one prime.** -/
theorem isSemistable_iff_forall_hasGoodReduction_or_hasMultiplicativeReduction
    (W : WeierstrassCurve F) [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
          (Localization.AtPrime v.asIdeal) ∨
        (W.minimal (Localization.AtPrime v.asIdeal)).HasMultiplicativeReduction
          (Localization.AtPrime v.asIdeal) := by
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
equation has a unit discriminant or a unit `c₄`; the latter gives multiplicative reduction when
the discriminant is not a unit. -/
theorem isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one
    (W : WeierstrassCurve F) [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      valuation F (maximalIdeal (Localization.AtPrime v.asIdeal))
          (W.minimal (Localization.AtPrime v.asIdeal)).Δ = 1 ∨
        valuation F (maximalIdeal (Localization.AtPrime v.asIdeal))
          (W.minimal (Localization.AtPrime v.asIdeal)).c₄ = 1 := by
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

variable (O' : Type*) [CommRing O'] [IsDedekindDomain O'] {L : Type*} [Field L] [Algebra O' L]
  [IsFractionRing O' L] [Algebra O O'] [Algebra F L] [Algebra O L] [IsScalarTower O O' L]
  [IsScalarTower O F L]

/-- **Semistability is preserved by base change** along an extension of Dedekind domains
`O → O'` compatible with the extension of fraction fields `F → L`. At a height-one prime `w` of
`O'` lying over a height-one prime `v` of `O`, the local ring at `v` maps to the local ring at `w`,
and `not_hasAdditiveReduction_minimal_baseChange` applies. When `w` lies over the zero ideal, every
nonzero element of `O` is a unit at `w` and the curve has good reduction there. No hypothesis on
ramification or on the degree of `L / F` is needed. -/
theorem IsSemistable.baseChange {W : WeierstrassCurve F} [W.IsElliptic] (h : IsSemistable O W) :
    IsSemistable O' (W.baseChange L) := by
  intro w
  -- along `O → O' → O'_w`, an element of `O` lands where it lands along `O → F → L`
  have hO (a : O) : algebraMap (Localization.AtPrime w.asIdeal) L
      (algebraMap O' (Localization.AtPrime w.asIdeal) (algebraMap O O' a)) =
        algebraMap F L (algebraMap O F a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  by_cases hp : w.asIdeal.comap (algebraMap O O') = ⊥
  · -- `w` lies over zero, so `F` maps into the local ring at `w` and `W` is integral there
    have hunit (y : nonZeroDivisors O) :
        IsUnit (algebraMap O' (Localization.AtPrime w.asIdeal) (algebraMap O O' y)) := by
      refine (IsLocalization.AtPrime.isUnit_to_map_iff _ w.asIdeal _).mpr fun hy ↦ ?_
      have : (y : O) ∈ w.asIdeal.comap (algebraMap O O') := hy
      exact nonZeroDivisors.ne_zero y.2 (by simp [hp] at this)
    let g : F →+* Localization.AtPrime w.asIdeal := IsLocalization.lift (M := nonZeroDivisors O)
      (g := (algebraMap O' _).comp (algebraMap O O')) hunit
    have hg : (algebraMap (Localization.AtPrime w.asIdeal) L).comp g = algebraMap F L :=
      IsLocalization.ringHom_ext (nonZeroDivisors O) <| RingHom.ext fun a ↦ by
        simpa [g] using hO a
    refine (not_hasAdditiveReduction_minimal_iff_exists_isUnit _ (W.baseChange L)).mpr
      ⟨W.map g, 1, Or.inl ?_, ?_⟩
    · rw [map_Δ]
      exact W.isUnit_Δ.map g
    · rw [one_smul, WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, map_map, hg]
  · -- `w` lies over a height-one prime `v`, and the local ring at `v` maps to that at `w`
    obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum O, v.asIdeal = w.asIdeal.comap (algebraMap O O') :=
      ⟨⟨_, inferInstance, hp⟩, rfl⟩
    let g := Localization.localRingHom v.asIdeal w.asIdeal (algebraMap O O') hv
    have hg : (algebraMap (Localization.AtPrime w.asIdeal) L).comp g =
        (algebraMap F L).comp (algebraMap (Localization.AtPrime v.asIdeal) F) :=
      IsLocalization.ringHom_ext v.asIdeal.primeCompl <| RingHom.ext fun a ↦ by
        simp only [RingHom.comp_apply, g, Localization.localRingHom_to_map]
        rw [← IsScalarTower.algebraMap_apply O (Localization.AtPrime v.asIdeal) F]
        exact hO a
    let _ : Algebra (Localization.AtPrime v.asIdeal) (Localization.AtPrime w.asIdeal) :=
      g.toAlgebra
    exact not_hasAdditiveReduction_minimal_baseChange (Localization.AtPrime v.asIdeal) _ hg (h v)

end WeierstrassCurve

end
