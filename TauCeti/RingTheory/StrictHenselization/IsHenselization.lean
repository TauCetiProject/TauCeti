/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.IsHenselization
public import TauCeti.RingTheory.StrictHenselization.Equiv
public import TauCeti.RingTheory.StrictHenselization.Field
public import TauCeti.RingTheory.StrictHenselization.FromHenselization
public import TauCeti.RingTheory.StrictHenselization.Henselian
public import TauCeti.RingTheory.StrictHenselization.IndEtale
public import TauCeti.RingTheory.StrictHenselization.ResidueField

/-!
# Recognising the strict henselization

For any commutative ring `R` and field `Ω` with an `R`-algebra structure, the colimit
`StrictHenselization.algebra R Ω` of `Ω`-pointed étale neighbourhoods is already a Henselian local
ring (`StrictHenselization.henselianLocalRing`) and ind-étale over `R`
(`StrictHenselization.indEtale`). Consequently, `toTarget R Ω : algebra R Ω →ₐ[R] Ω` satisfies
`TauCeti.IsHenselization` if and only if `toTarget R Ω` is surjective
(`isHenselization_iff_surjective`).

In particular:

* For a local ring `R` and a separable algebraic extension `Ω` of `ResidueField R` (such as a
  separable closure), `toTarget R Ω` is a henselization of `R` at `Ω` (`isHenselization`,
  registered as a typeclass instance).
* For a field `K` and a separable algebraic extension `Ω` of `K`, `toTarget K Ω` is a henselization
  of `K` at `Ω` (`isHenselization_of_field`, registered as a typeclass instance).
* For a local ring `R` and an `R`-algebra isomorphism `e : Ω ≃ₐ[R] ResidueField R`,
  `toTarget R Ω` is a henselization of `R` at `Ω` (`isHenselization_of_residueFieldEquiv`).

This file also reconciles the abstract maps produced by `IsHenselization` with the explicit
pointed-colimit maps:

* `isHenselizationLift_toTarget_eq` and `isHenselizationLift_toTarget_eq_lift`: lifting
  `toTarget R Ω` into a Henselian local ring `B` along a surjective map `χ : B →ₐ[R] Ω` agrees with
  `StrictHenselization.lift R Ω` for any compatible `pointMap : Ω →ₐ[R] ResidueField B`, and in
  particular along `(IsHenselization.residueFieldEquiv χ).symm` when `[IsHenselization χ]` holds.
* `isHenselizationLift_eq_fromHenselization`: any lift produced by `IsHenselization.lift` out of the
  ordinary henselization `Henselization.algebra (maximalIdeal R)` into `algebra R Ω` agrees with
  `fromHenselization R Ω`.
* `bijective_fromHenselization_of_residueFieldEquiv` and `fromHenselizationAlgEquiv`: when
  `Ω` is `R`-isomorphic to `ResidueField R` (in particular at `Ω = ResidueField R`), both the
  ordinary henselization and the `Ω`-pointed étale colimit are henselizations at the same point, so
  `fromHenselization R Ω` is bijective and identifies the unpointed and pointed colimits.

## References

* [Stacks Project, Lemma 10.155.2 (04GP)](https://stacks.math.columbia.edu/tag/04GP)
* [Stacks Project, Definition 10.155.3 (04GQ)](https://stacks.math.columbia.edu/tag/04GQ)
* [Stacks Project, Lemma 10.155.11 (04GW)](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Lemma 10.154.7 (08HT)](https://stacks.math.columbia.edu/tag/08HT)
-/

public section

open IsLocalRing

universe u v

namespace TauCeti.StrictHenselization

section Surjective

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- Because `algebra R Ω` is always Henselian local and ind-étale over `R` when `Ω` is a field,
`toTarget R Ω` satisfies `IsHenselization` if and only if `toTarget R Ω` is surjective. -/
theorem isHenselization_iff_surjective :
    IsHenselization (toTarget R Ω) ↔ Function.Surjective (toTarget R Ω) :=
  ⟨fun h ↦ h.surjective, fun h ↦ ⟨inferInstance, inferInstance, h⟩⟩

/-- Constructor for `IsHenselization (toTarget R Ω)` from surjectivity of `toTarget R Ω`, with no
local-ring assumption on `R`. -/
theorem isHenselization_of_surjective {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]
    (h : Function.Surjective (toTarget R Ω)) : IsHenselization (toTarget R Ω) :=
  (isHenselization_iff_surjective R Ω).mpr h

/-- Lifting `toTarget R Ω` into a Henselian local `R`-algebra `B` along a surjective `R`-algebra
map `χ : B →ₐ[R] Ω` agrees with `StrictHenselization.lift R Ω pointMap` for any
`pointMap : Ω →ₐ[R] ResidueField B` sending `χ b` to `residue B b`. -/
theorem isHenselizationLift_toTarget_eq {B : Type v} [CommRing B] [Algebra R B]
    [HenselianLocalRing B] {χ : B →ₐ[R] Ω} (hχ : Function.Surjective χ)
    (pointMap : Ω →ₐ[R] ResidueField B) (hpoint : ∀ b : B, pointMap (χ b) = residue B b) :
    IsHenselization.lift (toTarget R Ω) hχ = lift R Ω pointMap := by
  symm
  refine IsHenselization.eq_lift hχ (AlgHom.ext fun x ↦ ?_)
  exact RingHom.injective pointMap.toRingHom ((hpoint _).trans (residue_lift R Ω pointMap x))

/-- For a henselization `χ : B →ₐ[R] Ω`, the map `IsHenselization.lift (toTarget R Ω) hχ.surjective`
agrees with `StrictHenselization.lift` along `(IsHenselization.residueFieldEquiv χ).symm`. -/
theorem isHenselizationLift_toTarget_eq_lift {B : Type u} [CommRing B] [Algebra R B]
    [HenselianLocalRing B] (χ : B →ₐ[R] Ω) [hχ : IsHenselization χ] :
    IsHenselization.lift (toTarget R Ω) hχ.surjective =
      lift R Ω (IsHenselization.residueFieldEquiv χ).symm.toAlgHom :=
  isHenselizationLift_toTarget_eq R Ω hχ.surjective _
    (IsHenselization.residueFieldEquiv_symm_apply χ)

end Surjective

section LocalBase

/-- For a local ring `R` and a separable algebraic extension `Ω` of its residue field, in
particular a separable closure, the colimit of pointed étale neighbourhoods with its map
`toTarget` is a henselization of `R` at `R → Ω`, Stacks, Lemma 10.155.2 (04GP) with Lemma
10.155.11 (04GW). -/
@[stacks 04GP "(2), (5) and ind-étale, recognition form"]
theorem isHenselization {R Ω : Type u} [CommRing R] [IsLocalRing R]
    [Field Ω] [Algebra R Ω] [Algebra (ResidueField R) Ω]
    [IsScalarTower R (ResidueField R) Ω]
    [Algebra.IsSeparable (ResidueField R) Ω] :
    IsHenselization (toTarget R Ω) :=
  isHenselization_of_surjective (toTarget_surjective R Ω)

attribute [instance] isHenselization

/-- The residue-field equivalence `IsHenselization.residueFieldEquiv (toTarget R Ω)` agrees with
`StrictHenselization.residueFieldEquiv R Ω`. -/
@[simp]
theorem isHenselizationResidueFieldEquiv_toTarget (R Ω : Type u) [CommRing R] [IsLocalRing R]
    [Field Ω] [Algebra R Ω] [Algebra (ResidueField R) Ω]
    [IsScalarTower R (ResidueField R) Ω]
    [Algebra.IsSeparable (ResidueField R) Ω] :
    IsHenselization.residueFieldEquiv (toTarget R Ω) = residueFieldEquiv R Ω := by
  rw [IsHenselization.residueFieldEquiv_def, residueFieldEquiv_def]

/-- For a local ring `R` and a field `Ω` receiving a local map from `R`, any lift out of the
ordinary henselization `Henselization.algebra (maximalIdeal R)` into `algebra R Ω` produced by
`IsHenselization.lift` equals `fromHenselization R Ω`. -/
theorem isHenselizationLift_eq_fromHenselization (R Ω : Type u) {L : Type*} [CommRing R]
    [IsLocalRing R] [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)] [Field L]
    [Algebra R L] (ψ : Henselization.algebra (maximalIdeal R) →ₐ[R] L)
    {χ : algebra R Ω →ₐ[R] L} (hχ : Function.Surjective χ) :
    IsHenselization.lift ψ hχ = fromHenselization R Ω :=
  eq_fromHenselization R Ω _

/-- Over a local ring `R`, an `R`-algebra isomorphism `e : Ω ≃ₐ[R] ResidueField R` makes
`toTarget R Ω` a henselization of `R` at `Ω`. -/
theorem isHenselization_of_residueFieldEquiv (R Ω : Type u) [CommRing R] [IsLocalRing R]
    [Field Ω] [Algebra R Ω] (e : Ω ≃ₐ[R] ResidueField R) :
    IsHenselization (toTarget R Ω) := by
  refine isHenselization_of_surjective fun y ↦ ?_
  obtain ⟨r, hr⟩ := residue_surjective (e y)
  refine ⟨algebraMap R (algebra R Ω) r, e.injective ?_⟩
  rw [AlgHom.commutes, e.commutes, ResidueField.algebraMap_eq, hr]

/-- For a local ring `R` and a field `Ω` receiving a local map from `R` together with an
`R`-algebra isomorphism `e : ResidueField R ≃ₐ[R] Ω`, the comparison `fromHenselization R Ω` from
the ordinary henselization to the `Ω`-pointed étale colimit is bijective: both are henselizations
of `R` at `Ω`. -/
theorem bijective_fromHenselization_of_residueFieldEquiv (R Ω : Type u) [CommRing R] [IsLocalRing R]
    [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)] (e : ResidueField R ≃ₐ[R] Ω) :
    Function.Bijective (fromHenselization R Ω) := by
  have : IsHenselization (toTarget R Ω) := isHenselization_of_residueFieldEquiv R Ω e.symm
  have : IsHenselization (e.toAlgHom.comp (Henselization.toResidueField R)) :=
    (IsHenselization.algEquiv_comp_iff e (Henselization.toResidueField R)).mpr inferInstance
  refine IsHenselization.bijective_of_comp_eq
    (e.toAlgHom.comp (Henselization.toResidueField R)) (toTarget R Ω)
    (fromHenselization R Ω) ?_
  rw [toTarget_comp_fromHenselization]
  exact (Henselization.eq_lift (map_maximalIdeal_le (algebraMap R Ω)) _).symm

/-- For any local ring `R`, the ordinary henselization `Henselization.algebra (maximalIdeal R)` is
canonically `R`-isomorphic to the `ResidueField R`-pointed étale colimit
`algebra R (ResidueField R)` via `IsHenselization.algEquiv`. -/
noncomputable def fromHenselizationAlgEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    Henselization.algebra (maximalIdeal R) ≃ₐ[R] algebra R (ResidueField R) :=
  IsHenselization.algEquiv (Henselization.toResidueField R) (toTarget R (ResidueField R))

/-- `fromHenselizationAlgEquiv R` unfolds to `IsHenselization.algEquiv` between
`Henselization.toResidueField R` and `toTarget R (ResidueField R)`. -/
theorem fromHenselizationAlgEquiv_def (R : Type u) [CommRing R] [IsLocalRing R] :
    fromHenselizationAlgEquiv R =
      IsHenselization.algEquiv (Henselization.toResidueField R) (toTarget R (ResidueField R)) :=
  (rfl)

/-- The forward map of `fromHenselizationAlgEquiv R` is `fromHenselization R (ResidueField R)`. -/
theorem toAlgHom_fromHenselizationAlgEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (fromHenselizationAlgEquiv R).toAlgHom = fromHenselization R (ResidueField R) :=
  eq_fromHenselization R (ResidueField R) _

/-- The inverse map of `fromHenselizationAlgEquiv R` is `StrictHenselization.lift` along
`Henselization.residueFieldEquiv R`. -/
theorem toAlgHom_fromHenselizationAlgEquiv_symm (R : Type u) [CommRing R] [IsLocalRing R] :
    (fromHenselizationAlgEquiv R).symm.toAlgHom =
      lift R (ResidueField R) (Henselization.residueFieldEquiv R).toAlgHom := by
  rw [fromHenselizationAlgEquiv_def, IsHenselization.algEquiv_symm,
    IsHenselization.toAlgHom_algEquiv, isHenselizationLift_toTarget_eq_lift,
    Henselization.isHenselizationResidueFieldEquiv_toResidueField, AlgEquiv.symm_symm]

/-- Evaluating `toTarget R (ResidueField R)` on `fromHenselizationAlgEquiv R` recovers
`Henselization.toResidueField R`. -/
@[simp]
theorem toTarget_fromHenselizationAlgEquiv (R : Type u) [CommRing R] [IsLocalRing R]
    (x : Henselization.algebra (maximalIdeal R)) :
    toTarget R (ResidueField R) (fromHenselizationAlgEquiv R x) =
      Henselization.toResidueField R x :=
  IsHenselization.apply_algEquiv (Henselization.toResidueField R) (toTarget R (ResidueField R)) x

/-- Evaluating `Henselization.toResidueField R` on `(fromHenselizationAlgEquiv R).symm` recovers
`toTarget R (ResidueField R)`. -/
@[simp]
theorem toResidueField_fromHenselizationAlgEquiv_symm (R : Type u) [CommRing R] [IsLocalRing R]
    (x : algebra R (ResidueField R)) :
    Henselization.toResidueField R ((fromHenselizationAlgEquiv R).symm x) =
      toTarget R (ResidueField R) x := by
  rw [fromHenselizationAlgEquiv_def, IsHenselization.algEquiv_symm,
    IsHenselization.apply_algEquiv]

end LocalBase

section FieldAndHenselian

/-- Over a field `K`, for any separable algebraic extension `Ω / K`, `toTarget K Ω` is a
henselization of `K` at `Ω`. -/
instance isHenselization_of_field {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsSeparable K Ω] : IsHenselization (toTarget K Ω) :=
  isHenselization_of_surjective fun x ↦
    ⟨(algEquivOfField K Ω).symm x, toTarget_algEquivOfField_symm K Ω x⟩

/-- Over a field `K` and a separable algebraic extension `Ω / K`, lifting `toTarget K Ω` along the
identity of `Ω` via `IsHenselization.lift` recovers `algEquivOfField K Ω`. -/
theorem isHenselizationLift_toTarget_eq_algEquivOfField (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [Algebra.IsSeparable K Ω] :
    IsHenselization.lift (χ := AlgHom.id K Ω) (toTarget K Ω) Function.surjective_id =
      (algEquivOfField K Ω).toAlgHom := by
  symm
  exact IsHenselization.eq_lift _ (AlgHom.ext fun x ↦ by simp)

/-- Over a Henselian local ring `R` with `e : Ω ≃ₐ[R] ResidueField R`, lifting `toTarget R Ω` into
`R` along `e.symm ∘ residue R` via `IsHenselization.lift` recovers
`algEquivOfResidueFieldEquiv R Ω e`. -/
theorem isHenselizationLift_toTarget_eq_algEquivOfResidueFieldEquiv (R Ω : Type u) [CommRing R]
    [HenselianLocalRing R] [Field Ω] [Algebra R Ω] (e : Ω ≃ₐ[R] ResidueField R) :
    IsHenselization.lift (χ := e.symm.toAlgHom.comp (Algebra.ofId R (ResidueField R)))
      (toTarget R Ω) (e.symm.surjective.comp residue_surjective) =
      (algEquivOfResidueFieldEquiv R Ω e).toAlgHom := by
  symm
  refine IsHenselization.eq_lift _ (AlgHom.ext fun x ↦ e.injective ?_)
  simp [ResidueField.algebraMap_eq]

end FieldAndHenselian

-- Typeclass synthesis checks for local bases and field bases.
example (R : Type u) [CommRing R] [IsLocalRing R] :
    IsHenselization (toTarget R (ResidueField R)) :=
  inferInstance

example (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω] :
    IsHenselization (toTarget K Ω) :=
  inferInstance

end TauCeti.StrictHenselization
