/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.RingTheory.UniversallyJapanese
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType

import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import TauCeti.RingTheory.IntegralClosure.DiscreteValuationRing

/-!
# Finiteness of the relative normalization

Let `f : X ⟶ Y` be quasi-compact and quasi-separated. Over an affine open `U` of `Y`, the
normalization of `Y` in `X` is the spectrum of the integral closure of `Γ(Y, U)` in
`Γ(X, f ⁻¹ᵁ U)`. Since the normalization is an affine morphism, it is finite over `Y` exactly when
each of these integral closures is a finite `Γ(Y, U)`-module.

For an integral scheme `Y` and a finite extension `L` of its function field `k(Y)`, consider the
normalization of `Y` in `Spec L`, along `Spec L ⟶ Spec k(Y) ⟶ Y`. Over a nonempty affine open `U`,
the sections of `Spec L` are `L`, and `k(Y)` is the fraction field of `Γ(Y, U)`. So this
normalization is finite when the rings `Γ(Y, U)` are Japanese; for instance when `Y` is locally of
finite type over a universally Japanese ring `R` (such as a field), or when the rings `Γ(Y, U)` are
Nagata. For `L = k(Y)` itself, the normalization of `Y` in its function field is finite exactly
when the rings `Γ(Y, U)` are N-1. This supplies the finiteness hypothesis of resolution of curves
by normalization (`TauCeti.AlgebraicGeometry.isRegular_normalization_of_field`) for integral
schemes of dimension one locally of finite type over a field.

Over an arbitrary discrete valuation ring `R` with fraction field `K` (not assumed Japanese or
excellent), if `X` is locally of finite type over `Spec R` and its generic fibre `C` is smooth of
relative dimension `1` over `Spec K`, then the normalization of `X` in `C` is finite over `X`
(`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isPullback`, Stacks Lemma 55.8.3 / 0C2U).

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization_iff`: the normalization of `Y` in `X` is
  finite over `Y` if and only if, over every affine open `U` of `Y`, the integral closure of
  `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)` is a finite `Γ(Y, U)`-module.
* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint_iff`: the
  normalization of an integral scheme in its function field is finite if and only if the ring of
  sections of every nonempty affine open is N-1.
* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isJapanese`: if the ring of sections of
  every nonempty affine open of an integral scheme `Y` is Japanese, the normalization of `Y` in a
  finite extension of its function field is finite over `Y` (Stacks, Lemma 29.54.14 (0AVK), with
  the hypothesis on every affine open).
* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isPullback`: for a scheme `X` locally of
  finite type over a discrete valuation ring `R` whose generic fibre `C` is smooth of relative
  dimension `1` over `Frac(R)`, the normalization of `X` in `C` is finite over `X`.
* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType` and
  `isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType`:
  if `Y` is an integral scheme locally of finite type over `Spec R` for a universally Japanese ring
  `R` (such as a field), the normalization of `Y` in any finite extension of `k(Y)`, and in `k(Y)`
  itself, is finite over `Y`.

## References

* [Stacks Project, Lemma 29.54.14](https://stacks.math.columbia.edu/tag/0AVK).
* [Stacks Project, Proposition 10.162.16](https://stacks.math.columbia.edu/tag/0335).
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H), for the relative
  normalization over affine opens.
* [Stacks Project, Lemma 55.8.3](https://stacks.math.columbia.edu/tag/0C2U), for finiteness of
  normalization of one-dimensional schemes over arbitrary discrete valuation rings.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The normalization of `Y` in `X`, along `f`, is finite over `Y` if and only if, over every affine
open `U` of `Y`, the integral closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ᵁ U)` is a finite
`Γ(Y, U)`-module. -/
theorem isFinite_fromNormalization_iff :
    IsFinite f.fromNormalization ↔ ∀ U : Y.Opens, IsAffineOpen U →
      letI := (f.app U).hom.toAlgebra
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
  -- Over an affine open `U`, the map on sections is the algebra map to the integral closure,
  -- followed by the isomorphism `normalizationObjIso`.
  have key : ∀ U (_ : IsAffineOpen U), (f.fromNormalization.app U).hom.Finite ↔
      letI := (f.app U).hom.toAlgebra
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := fun U hU ↦ by
    let := (f.app U).hom.toAlgebra
    rw [fromNormalization_app _ hU, CommRingCat.hom_comp,
      RingHom.finite_respectsIso.cancel_right_isIso, CommRingCat.hom_ofHom]
    exact RingHom.finite_algebraMap
  refine ⟨fun _ U hU ↦ (key U hU).mp (f.fromNormalization.finite_app U hU), fun h ↦ ?_⟩
  exact { finite_app U hU := (key U hU).mpr (h U hU) }

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- **Finite normalization and N-1 rings.** The normalization of an integral scheme `Y` in its
function field, along `Spec k(Y) ⟶ Y`, is finite over `Y` if and only if the ring of sections of
every nonempty affine open of `Y` is N-1: over such an open `U` the normalization is the spectrum
of the integral closure of `Γ(Y, U)` in its fraction field `k(Y)`. -/
theorem isFinite_fromNormalization_fromSpecStalk_genericPoint_iff :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization ↔
      ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → Ring.IsN1 Γ(Y, U) := by
  set f := Y.fromSpecStalk (genericPoint Y)
  rw [f.isFinite_fromNormalization_iff]
  refine forall₂_congr fun U hU ↦ ?_
  let := (f.app U).hom.toAlgebra
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    have := Scheme.isFractionRing_app_fromSpecStalk_genericPoint hU
    exact ⟨fun _ _ ↦ .of_finite_integralClosure Γ(Spec Y.functionField, f ⁻¹ᵁ U),
      fun h ↦ (h ‹_›).finite_integralClosure _⟩
  · -- Over an open missing the generic point, the sections of `Spec k(Y)` are the zero ring.
    have := Scheme.subsingleton_preimage_of_genericPoint_notMem f hη
    refine ⟨fun _ hU ↦ (hη ?_).elim, fun _ ↦ inferInstance⟩
    obtain ⟨⟨y, hy⟩⟩ := hU
    exact (genericPoint_specializes y).mem_open U.isOpen hy

variable (L : Type u) [Field L] [Algebra Y.functionField L] in
/-- **Finite normalization in a finite extension of the function field.** Let `Y` be an integral
scheme such that the ring of sections of every nonempty affine open is Japanese, for instance
Nagata. Then for every finite extension `L` of the function field `k(Y)`, the normalization of `Y`
in `Spec L`, along `Spec L ⟶ Spec k(Y) ⟶ Y`, is finite over `Y`. Stacks, Lemma 29.54.14 (0AVK),
with the hypothesis imposed on every nonempty affine open. -/
@[stacks 0AVK "The Japanese hypothesis is imposed on every nonempty affine open."]
theorem isFinite_fromNormalization_of_isJapanese
    (hY : ∀ U : Y.Opens, IsAffineOpen U → ∀ [Nonempty U], Ring.IsJapanese Γ(Y, U))
    [FiniteDimensional Y.functionField L] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
    Y.fromSpecStalk (genericPoint Y)
  refine f.isFinite_fromNormalization_iff.mpr fun U hU ↦ ?_
  let := (f.app U).hom.toAlgebra
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    -- Over `U`, the integral closure is that of `Γ(Y, U)` in `L`, which is finite as
    -- `Γ(Y, U)` is a Japanese domain with fraction field `k(Y)`.
    let : Algebra Γ(Y, U) L :=
      ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra
    have : IsScalarTower Γ(Y, U) Y.functionField L := .of_algebraMap_eq' rfl
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have := hY U hU
    have := Ring.IsJapanese.finite_integralClosure (R := Γ(Y, U)) Y.functionField L
    exact .equiv (Scheme.algEquivAppPreimageSpecExtension L).mapIntegralClosure.toLinearEquiv
  · -- Over an open missing the generic point, the sections of `Spec L` are the zero ring.
    have := Scheme.subsingleton_preimage_of_genericPoint_notMem f hη
    infer_instance

open Limits in
/-- **Finiteness of normalization in a smooth generic fibre of relative dimension one.** Let `R` be
a discrete valuation ring with fraction field `K`, let `X` be a scheme locally of finite type over
`Spec R`, and let `C` be its generic fibre over `Spec K`, with projection `g : C ⟶ X`. If `C` is
smooth of relative dimension `1` over `Spec K`, then the normalization of `X` in `C` along `g` is
finite over `X`. No excellence or Japanese hypothesis on `R` and no flatness hypothesis on `X` are
needed. -/
@[stacks 0C2U]
theorem isFinite_fromNormalization_of_isPullback
    {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X C : Scheme.{u}} {toBase : X ⟶ Spec (.of R)} [LocallyOfFiniteType toBase]
    {toK : C ⟶ Spec (.of K)} [SmoothOfRelativeDimension 1 toK] {g : C ⟶ X}
    (H : IsPullback g toK toBase (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    haveI : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
    IsFinite g.fromNormalization := by
  have : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine g.isFinite_fromNormalization_iff.mpr fun U hU ↦ ?_
  let : X.Over (Spec (.of R)) := ⟨toBase⟩
  let : C.Over (Spec (.of K)) := ⟨toK⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of R)) := inferInstanceAs (LocallyOfFiniteType toBase)
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  refine Scheme.with_algebraIsPushout_baseRingToStructurePresheaf_of_isAffineOpen
    (R := R) (S := K) (Y := C) H hU fun hpush hRX hSY hXY ↦ ?_
  have : Algebra.IsPushout R Γ(X, U) K Γ(C, g ⁻¹ᵁ U) := hpush.symm
  have : Algebra.FiniteType R Γ(X, U) :=
    hRX ▸ finiteType_sections_of_locallyOfFiniteType R X ⟨U, hU⟩
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (toK.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
      (f := toK) ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨g ⁻¹ᵁ U, hV⟩ le_top
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K Γ(C, g ⁻¹ᵁ U)) := by
    rw [hSY]
    simp only [RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_app_eq_appLE,
      CommRingCat.hom_comp]
    exact (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).right _
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv hsm
  open TauCeti.IsDiscreteValuationRing in
  exact hXY ▸ finite_integralClosure_of_locally_isStandardSmoothOfRelativeDimension_one
    (R := R) (K := K) hloc

section UniversallyJapanese

variable {R : Type u} [CommRing R] [Ring.IsUniversallyJapanese R]

/-- The ring of sections of every nonempty affine open of an integral scheme locally of finite type
over `Spec R`, for a universally Japanese ring `R` (such as a field), is Japanese: it is an
integral domain of finite type over `R`. -/
theorem isJapanese_sections_of_locallyOfFiniteType (g : Y ⟶ Spec (.of R)) [LocallyOfFiniteType g]
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] : Ring.IsJapanese Γ(Y, U) := by
  let : Algebra R Γ(Y, U) := ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType R Γ(Y, U) := g.finiteType_ΓSpecIso_inv_comp_appLE hU
  exact Ring.IsUniversallyJapanese.isJapanese R Γ(Y, U)

/-- **Finite normalization in a finite extension over a universally Japanese base.** Let `Y` be an
integral scheme locally of finite type over `Spec R`, where `R` is universally Japanese (for
instance a field). Then for every finite extension `L` of `k(Y)`, the normalization of `Y` in
`Spec L` is finite over `Y`. -/
theorem isFinite_fromNormalization_of_locallyOfFiniteType (g : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType g] (L : Type u) [Field L] [Algebra Y.functionField L]
    [FiniteDimensional Y.functionField L] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)).fromNormalization :=
  isFinite_fromNormalization_of_isJapanese L fun _ hU _ ↦
    isJapanese_sections_of_locallyOfFiniteType g hU

/-- **Finite normalization of an integral scheme locally of finite type over a universally Japanese
ring.** In particular, the normalization of an integral scheme locally of finite type over a field
in its function field is finite over it. -/
theorem isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (g : Y ⟶ Spec (.of R)) [LocallyOfFiniteType g] :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization :=
  isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mpr fun _ hU _ ↦ by
    have := isJapanese_sections_of_locallyOfFiniteType g hU
    infer_instance

end UniversallyJapanese

end TauCeti.AlgebraicGeometry
