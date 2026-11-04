/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
import TauCeti.RingTheory.Henselian.Etale

/-!
# Lifting property of the pointed étale colimit

A point of an étale neighbourhood lifts uniquely to a henselian local algebra once a map from its
target algebra to the residue field is fixed. The compatible lifts at all stages give the
universal map from the colimit constructed in `StrictHenselization.Algebra`. For a local base and
a separable closure of its residue field, this is the universal property of the strict
henselization. When `S` is moreover strictly henselian, a map from the separable closure to the
residue field of `S` always exists, so every local map from the base to `S` extends to a local map
out of the strict henselization.

## Main results

* `TauCeti.StrictHenselization.lift`: the map from the colimit to a henselian local `R`-algebra `S`
  determined by an `R`-algebra map `Ω → κ(S)`.
* `TauCeti.StrictHenselization.residue_lift`: `lift` reduces to the given map composed with
  `toTarget`.
* `TauCeti.StrictHenselization.eq_lift`: any map out of the colimit with this reduction is
  `lift`.
* `TauCeti.StrictHenselization.lift_comp_stage`, `TauCeti.StrictHenselization.lift_stage`: on a
  neighbourhood, `lift` is the unique lift of the induced point.
* `TauCeti.StrictHenselization.existsUnique_lift`: the universal property for a ring map
  `Ω → κ(S)` compatible with `R`.
* `TauCeti.StrictHenselization.isLocalHom_lift`: when `Ω` is a field, `lift` is local.
* `TauCeti.StrictHenselization.exists_isLocalHom_lift`: a local homomorphism from a local ring
  to a strictly henselian local ring extends to a local homomorphism out of the colimit, for `Ω`
  separable algebraic over the residue field of the base.

## Implementation notes

The colimit lives in the universe of `R` and `Ω`, while `S` may live in any universe. The stage
lifts are assembled by `StrictHenselization.descOfCompatible`, which goes through the shared
construction `SmallFilteredAlgebraColimit.descOfCompatible`.

## References

* Stacks Project, Tag 08HQ.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`
  (Apache 2.0), `StrictHenselizationConstruction.lean` and `StrictHenselizationStages.lean` for
  the construction of the colimit. The universal property follows Stacks 08HQ, applied
  stagewise.
-/

public section

open CategoryTheory IsLocalRing

universe u v

namespace TauCeti.StrictHenselization

section HenselianTarget

variable (R Ω : Type u) {S : Type v} [CommRing R] [CommRing Ω] [Algebra R Ω]
  [CommRing S] [Algebra R S] [HenselianLocalRing S]

/-- The point of a neighbourhood induced by a map from the target algebra to the residue field. -/
private noncomputable def reducedPoint (pointMap : Ω →ₐ[R] ResidueField S)
    (B : Neighbourhood R Ω) : B.obj.left →ₐ[R] ResidueField S :=
  pointMap.comp ((toTarget R Ω).comp (stage R Ω B))

/-- A chosen lift to `S` of the point of a neighbourhood induced by `pointMap`. -/
private noncomputable def stageLift (pointMap : Ω →ₐ[R] ResidueField S)
    (B : Neighbourhood R Ω) : B.obj.left →ₐ[R] S :=
  Function.surjInv (HenselianLocalRing.comp_bijective_of_algebra (R := R) (S := S)
    (A := B.obj.left)).2 (reducedPoint R Ω pointMap B)

private theorem reduction_comp_stageLift (pointMap : Ω →ₐ[R] ResidueField S)
    (B : Neighbourhood R Ω) :
    (IsScalarTower.toAlgHom R S (ResidueField S)).comp (stageLift R Ω pointMap B) =
      reducedPoint R Ω pointMap B :=
  Function.surjInv_eq (HenselianLocalRing.comp_bijective_of_algebra (R := R) (S := S)
    (A := B.obj.left)).2 _

/-- Two lifts of the same point of an étale neighbourhood to `S` agree. -/
private theorem stage_ext (B : Neighbourhood R Ω) {f g : B.obj.left →ₐ[R] S}
    (h : (IsScalarTower.toAlgHom R S (ResidueField S)).comp f =
      (IsScalarTower.toAlgHom R S (ResidueField S)).comp g) : f = g :=
  (HenselianLocalRing.comp_bijective_of_algebra (R := R) (S := S) (A := B.obj.left)).1 h

private theorem stageLift_comp (pointMap : Ω →ₐ[R] ResidueField S) {B C : Neighbourhood R Ω}
    (f : B ⟶ C) :
    (stageLift R Ω pointMap C).comp f.hom.left.hom = stageLift R Ω pointMap B := by
  apply stage_ext R Ω B
  rw [← AlgHom.comp_assoc, reduction_comp_stageLift, reduction_comp_stageLift, reducedPoint,
    reducedPoint, AlgHom.comp_assoc, AlgHom.comp_assoc,
    stage_naturality]

/-- The `R`-algebra map from the colimit of pointed étale neighbourhoods to a henselian local
`R`-algebra `S` determined by an `R`-algebra map `Ω → κ(S)`. At each neighbourhood it is the lift
of the induced point (`lift_comp_stage`), and it is the unique map with the induced reduction
(`residue_lift`, `eq_lift`). -/
noncomputable def lift (pointMap : Ω →ₐ[R] ResidueField S) : algebra R Ω →ₐ[R] S :=
  descOfCompatible R Ω (stageLift R Ω pointMap) (stageLift_comp R Ω pointMap)

/-- On the stage of a neighbourhood `B`, `lift` is the chosen lift of the induced point. -/
private theorem lift_comp_stage_eq (pointMap : Ω →ₐ[R] ResidueField S) (B : Neighbourhood R Ω) :
    (lift R Ω pointMap).comp (stage R Ω B) = stageLift R Ω pointMap B :=
  descOfCompatible_comp_stage R Ω (stageLift R Ω pointMap) (stageLift_comp R Ω pointMap) B

/-- Reducing `lift` modulo the maximal ideal of `S` gives the given map composed with
`toTarget`. -/
@[simp]
theorem residue_comp_lift (pointMap : Ω →ₐ[R] ResidueField S) :
    (IsScalarTower.toAlgHom R S (ResidueField S)).comp (lift R Ω pointMap) =
      pointMap.comp (toTarget R Ω) := by
  apply hom_ext R Ω
  intro B
  rw [AlgHom.comp_assoc, lift_comp_stage_eq, reduction_comp_stageLift, reducedPoint,
    AlgHom.comp_assoc]

/-- Elementwise form of `residue_comp_lift`. -/
@[simp]
theorem residue_lift (pointMap : Ω →ₐ[R] ResidueField S) (x : algebra R Ω) :
    residue S (lift R Ω pointMap x) = pointMap (toTarget R Ω x) :=
  by simpa [IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq, -residue_comp_lift] using
    DFunLike.congr_fun (residue_comp_lift R Ω pointMap) x

/-- Every `R`-algebra map out of the colimit with the reduction `pointMap ∘ toTarget` is
`lift`. -/
theorem eq_lift (pointMap : Ω →ₐ[R] ResidueField S) {f : algebra R Ω →ₐ[R] S}
    (hf : (IsScalarTower.toAlgHom R S (ResidueField S)).comp f =
      pointMap.comp (toTarget R Ω)) :
    f = lift R Ω pointMap := by
  apply hom_ext R Ω
  intro B
  apply stage_ext R Ω B
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hf, residue_comp_lift]

/-- On the stage of a neighbourhood `B`, `lift` is the unique map to `S` reducing to the point
`pointMap ∘ toTarget ∘ stage` of `B`. -/
theorem lift_comp_stage (pointMap : Ω →ₐ[R] ResidueField S) (B : Neighbourhood R Ω)
    {φ : B.obj.left →ₐ[R] S}
    (hφ : (IsScalarTower.toAlgHom R S (ResidueField S)).comp φ =
      pointMap.comp ((toTarget R Ω).comp (stage R Ω B))) :
    (lift R Ω pointMap).comp (stage R Ω B) = φ := by
  apply stage_ext R Ω B
  rw [lift_comp_stage_eq, reduction_comp_stageLift, reducedPoint, hφ]

/-- Elementwise form of `lift_comp_stage`. -/
theorem lift_stage (pointMap : Ω →ₐ[R] ResidueField S) (B : Neighbourhood R Ω)
    {φ : B.obj.left →ₐ[R] S}
    (hφ : (IsScalarTower.toAlgHom R S (ResidueField S)).comp φ =
      pointMap.comp ((toTarget R Ω).comp (stage R Ω B))) (b : B.obj.left) :
    lift R Ω pointMap (stage R Ω B b) = φ b :=
  DFunLike.congr_fun (lift_comp_stage R Ω pointMap B hφ) b

/-- **Lifting property.** For a henselian local algebra `S` over `R` and a ring map
`φ : Ω → κ(S)` compatible with `R`, there is a unique `R`-algebra map `f` out of the colimit of
pointed étale neighbourhoods whose reduction modulo the maximal ideal of `S` is `φ ∘ toTarget`.
For a local base ring and a separable closure `Ω` of its residue field, this is the universal
property of the strict henselization. -/
@[stacks 08HQ "applied stagewise"]
theorem existsUnique_lift (φ : Ω →+* ResidueField S)
    (hφ : ∀ r : R, φ (algebraMap R Ω r) = residue S (algebraMap R S r)) :
    ∃! f : algebra R Ω →ₐ[R] S, ∀ x, residue S (f x) = φ (toTarget R Ω x) := by
  let pointMap : Ω →ₐ[R] ResidueField S :=
    { φ with
      commutes' := fun r => (hφ r).trans (by
        rw [IsScalarTower.algebraMap_apply R S (ResidueField S), ResidueField.algebraMap_eq]) }
  -- Holds by construction: `pointMap` is `φ` with the commutation proof added.
  have hpoint : ∀ y, pointMap y = φ y := fun _ ↦ rfl
  refine ⟨lift R Ω pointMap,
    fun x ↦ (residue_lift R Ω pointMap x).trans (hpoint _),
    fun f hf ↦ eq_lift R Ω pointMap (AlgHom.ext fun x ↦ by
      simpa [IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq, hpoint] using hf x)⟩

end HenselianTarget

section FieldTarget

variable (R : Type u) {Ω : Type u} {S : Type v} [CommRing R] [Field Ω] [Algebra R Ω]
  [CommRing S] [Algebra R S] [HenselianLocalRing S]

/-- When the target `Ω` is a field, `lift` is a local homomorphism. -/
instance isLocalHom_lift (pointMap : Ω →ₐ[R] ResidueField S) :
    IsLocalHom (lift R Ω pointMap) where
  map_nonunit x hx := by
    -- If `lift x` is a unit, then its reduction `pointMap (toTarget x)` is nonzero, so
    -- `toTarget x` is a unit in the field `Ω`, and hence so is `x`.
    rw [isUnit_iff_isUnit_toTarget, isUnit_iff_ne_zero]
    intro h
    apply (residue_ne_zero_iff_isUnit _).mpr hx
    rw [residue_lift, h, map_zero]

/-- **Local maps to strictly henselian rings.** Let `R` be a local ring and `Ω` a separable
algebraic extension of its residue field, such as a separable closure. A local homomorphism
`R → S` into a strictly henselian local ring `S` extends to a local homomorphism from the colimit
of pointed étale neighbourhoods, that is, from the strict henselization when `Ω` is a separable
closure. -/
theorem exists_isLocalHom_lift [IsLocalRing R] [Algebra (ResidueField R) Ω]
    [IsScalarTower R (ResidueField R) Ω] [Algebra.IsSeparable (ResidueField R) Ω]
    [IsSepClosed (ResidueField S)] [IsLocalHom (algebraMap R S)] :
    ∃ f : algebra R Ω →ₐ[R] S, IsLocalHom f :=
  -- Embed `Ω` into the separably closed residue field of `S` over the residue field of `R`;
  -- `lift` along this embedding is local.
  ⟨lift R Ω ((IsSepClosed.lift : Ω →ₐ[ResidueField R] ResidueField S).restrictScalars R),
    inferInstance⟩

end FieldTarget

end TauCeti.StrictHenselization
