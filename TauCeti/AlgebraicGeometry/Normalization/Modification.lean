/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Morphisms.Modification
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.RingTheory.Japanese

/-!
# The finite normalization of an integral scheme is a modification

Let `Y` be an integral scheme and `ν : Y^ν ⟶ Y` its normalization in its function field, along
`Spec k(Y) ⟶ Y`. Over an affine open `U = Spec A` of `Y`, the scheme `Y^ν` is the spectrum of the
integral closure of `A` in `k(Y)`, the fraction field of `A`.

So `ν` is an isomorphism over every affine open whose ring is integrally closed. When `ν` is
finite, these rings are N-1, and an N-1 domain becomes integrally closed after inverting one
nonzero element. Hence `ν` is an isomorphism over a nonempty, so dense, basic open of `Y`, and being
finite it is proper: `ν` is a modification. Together with
`TauCeti.AlgebraicGeometry.isRegular_normalization_fromSpecStalk_genericPoint`, this shows that the
finite normalization of an integral locally Noetherian scheme of dimension at most one is a
resolution of singularities: a regular scheme with a finite modification to `Y` (Stacks,
Lemma 33.41.1 (0C45) over a field).

## Main results

* `TauCeti.AlgebraicGeometry.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed`:
  the normalization of an integral scheme in its function field is an isomorphism over every
  affine open with integrally closed ring of sections.
* `TauCeti.AlgebraicGeometry.isN1_of_isFinite_fromNormalization`: if this normalization is finite,
  the ring of sections of every nonempty affine open is N-1.
* `TauCeti.AlgebraicGeometry.isModification_fromNormalization_fromSpecStalk_genericPoint`: if this
  normalization is finite, it is a modification.

## References

* [Stacks Project, Lemma 33.41.1](https://stacks.math.columbia.edu/tag/0C45).
* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- The normalization of an integral scheme `Y` in its function field, along `Spec k(Y) ⟶ Y`, is an
isomorphism over every affine open `U` whose ring of sections is integrally closed: the integral
closure of `Γ(Y, U)` in its fraction field `k(Y)` is `Γ(Y, U)` itself. -/
theorem isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed {U : Y.Opens}
    (hU : IsAffineOpen U) [IsIntegrallyClosed Γ(Y, U)] :
    IsIso ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ U) := by
  set f := Y.fromSpecStalk (genericPoint Y)
  rw [isIso_morphismRestrict_iff_isIso_app _ hU, Scheme.Hom.fromNormalization_app _ hU]
  let := (f.app U).hom.toAlgebra
  suffices h : Function.Bijective
      (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U))) by
    have : IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U)
        (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr h
    infer_instance
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    have := Scheme.isFractionRing_app_fromSpecStalk_genericPoint hU
    refine ⟨fun a b hab ↦ IsFractionRing.injective Γ(Y, U) _ (congrArg Subtype.val hab),
      fun ⟨x, hx⟩ ↦ ?_⟩
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨a, rfl⟩
  · -- Otherwise `U` is empty and all the rings involved are zero.
    have hU : U = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hη ((genericPoint_specializes x).mem_open U.isOpen hx), fun hx ↦ hx.elim⟩
    have : Subsingleton Γ(Y, U) := by
      rw [hU]
      infer_instance
    have : Subsingleton Γ(Spec Y.functionField, f ⁻¹ᵁ U) := by
      rw [hU, Scheme.Hom.preimage_bot]
      infer_instance
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- If the normalization of an integral scheme `Y` in its function field is finite over `Y`, then
the ring of sections of every nonempty affine open of `Y` is N-1: over `U` the normalization is the
spectrum of the integral closure of `Γ(Y, U)` in its fraction field, a finite `Γ(Y, U)`-module. -/
theorem isN1_of_isFinite_fromNormalization
    [IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization] {U : Y.Opens}
    (hU : IsAffineOpen U) [Nonempty U] : Ring.IsN1 Γ(Y, U) := by
  set f := Y.fromSpecStalk (genericPoint Y)
  let := (f.app U).hom.toAlgebra
  have := Scheme.isFractionRing_app_fromSpecStalk_genericPoint hU
  -- Up to `normalizationObjIso`, the algebra map to the integral closure is
  -- `f.fromNormalization.app U`, which is finite.
  have heq : (f.fromNormalization.app U ≫ (f.normalizationObjIso hU).hom).hom =
      algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U)) := by
    rw [Scheme.Hom.fromNormalization_app _ hU, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      CommRingCat.hom_ofHom]
  have hfin :
      (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U))).Finite := by
    rw [← heq, CommRingCat.hom_comp]
    exact (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2).comp
      (f.fromNormalization.finite_app U hU)
  have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U)) :=
    RingHom.finite_algebraMap.mp hfin
  exact .of_finite_integralClosure Γ(Spec Y.functionField, f ⁻¹ᵁ U)

/-- **Resolution of curves: the normalization is a modification.** If the normalization of an
integral scheme `Y` in its function field, along `Spec k(Y) ⟶ Y`, is finite over `Y`, then it is a
modification of `Y`: it is proper, and an isomorphism over a dense open of `Y` with dense preimage.
Stacks, Lemma 33.41.1 (0C45) over a field. -/
@[stacks 0C45 "modification part, for integral schemes"]
instance isModification_fromNormalization_fromSpecStalk_genericPoint
    [IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization] :
    IsModification (Y.fromSpecStalk (genericPoint Y)).fromNormalization where
  exists_isIso_morphismRestrict := by
    set ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
    obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint Y)) isOpen_univ
    have : Nonempty V := ⟨⟨_, hηV⟩⟩
    have := isN1_of_isFinite_fromNormalization hV
    -- Some nonzero `s` makes `Γ(Y, V)_s` integrally closed, and `ν` is an isomorphism over `D(s)`.
    obtain ⟨s, hs, _⟩ := Ring.IsN1.exists_isIntegrallyClosed_localization_away (R := Γ(Y, V))
    have := hV.isLocalization_basicOpen s
    have : IsIntegrallyClosed Γ(Y, Y.basicOpen s) := .of_equiv
      (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) _).toRingEquiv
    have hiso := isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed (hV.basicOpen s)
    obtain ⟨y, hy⟩ : (Y.basicOpen s : Set Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, ne_eq,
        SetLike.coe_set_eq, basicOpen_eq_bot_iff]
      exact hs
    refine ⟨Y.basicOpen s, (Y.basicOpen s).isOpen.dense ⟨y, hy⟩,
      (ν ⁻¹ᵁ Y.basicOpen s).isOpen.dense ⟨_, ((asIso (ν ∣_ Y.basicOpen s)).inv ⟨y, hy⟩).2⟩, hiso⟩

end TauCeti.AlgebraicGeometry
