/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Degree.Different
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Cohomology
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Curve
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Divisor
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteMap
public import TauCeti.FieldTheory.FunctionField.Different.Tower
import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# The Cartier ramification divisor and trace-dual different on two-chart models

Let `F' / F` be a finite separable extension of algebraic function fields over a field `k`, and let
`X = twoChartModel hF hx` and `X' = twoChartModel hF' hx'` be regular proper models of `F` and
`F'` built from arbitrary nonzero transcendental functions `x ∈ F` and `x' ∈ F'`. The inclusion
`F →ₐ[k] F'` induces a finite dominant `k`-morphism
`homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F') : X' ⟶ X`
(`isFinite_homOfAlgHom`), which agrees with the glued chart morphism `twoChartModel.map` whenever
`algebraMap F F' x = x'`.

Transporting `Place.differentExponent` across the function-field identifications
`twoChartModel.functionFieldEquiv` shows that for any dominant `k`-morphism `f : X' ⟶ X`
compatible with `F → F'` on the separable-residue branch (and in particular automatically for
`homOfAlgHom` and `map` whenever `k` is a perfect field), the Cartier ramification divisor of `f`
corresponds under `twoChartModel.equivDivisor` to the trace-dual different divisor
`Divisor.different k F' hF` (`equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom`),
and the subscheme rank `dim_k Γ(R_f, 𝒪_{R_f})` of its ramification locus equals `deg Diff(F'/F)`
(`finrank_ramificationIdealSheaf_homOfAlgHom_eq_degree_different`).

## Main results

* `twoChartModel.isFinite_homOfAlgHom`: `homOfAlgHom` of `F →ₐ[k] F'` is a finite morphism.
* `twoChartModel.equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap`:
  `twoChartModel.equivDivisor hx't (ramificationCartierDivisor k f).toWeilDivisor =
    Divisor.different k F' hF` on models with invertible differentials and separable residue
  extensions.
* `twoChartModel.equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom` and
  `..._map`: specializations to `homOfAlgHom` and `twoChartModel.map`.
* `twoChartModel.finrank_ramificationIdealSheaf_homOfAlgHom_eq_degree_different` and
  `..._map_eq_degree_different`: `dim_k Γ(R_f, 𝒪_{R_f}) = deg Diff(F'/F)`.
* `twoChartModel.equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom_of_perfectField`
  and `..._map_of_perfectField`: automatic versions over a perfect base field `k`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : x ≠ 0) {x' : F'}
  (hx' : x' ≠ 0)

/-- The morphism of two-chart models induced by an integral extension `F' / F` of function fields
over `k` is finite, for arbitrary choices of transcendental parameters `x ∈ F` and `x' ∈ F'`. -/
theorem isFinite_homOfAlgHom (hxt : Transcendental k x) (hx't : Transcendental k x')
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] :
    IsFinite (homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F')) := by
  let y' : F' := algebraMap F F' x
  have hy' : y' ≠ 0 := (map_ne_zero _).mpr hx
  have hy't : Transcendental k y' :=
    (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxt
  have hcomp :
      (isoOfAlgEquiv hF' hF' hy' hx' (1 : F' ≃ₐ[k] F')
          (hxt := hy't) (hx't := hx't)).hom ≫
        map hF hF' hx hy' (rfl : algebraMap F F' x = y') =
      homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F') := by
    rw [isoOfAlgEquiv_hom, map_eq_homOfAlgHom (hxt := hxt) (hx't := hy't), homOfAlgHom_comp]
    rfl
  have : IsFinite (map hF hF' hx hy' (rfl : algebraMap F F' x = y')) :=
    isFinite_map hF hF' hx hy' rfl hxt
  rw [← hcomp]
  infer_instance

private theorem isSeparable_residueField_of_perfectField [PerfectField k]
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k F') (P' : Place k F') :
    Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField := by
  let _ := Place.integersAlgebraBase k P'
  have := Place.isScalarTower_integersAlgebraBase k P'
  have := Place.isScalarTower_integers_restrict k F P'
  have _ : PerfectField (P'.restrict k F).ResidueField :=
    (P'.restrict k F).perfectField_residueField hF
  have _ : FiniteDimensional k P'.ResidueField := P'.finiteDimensional_residueField hF'
  have _ : FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField :=
    Module.Finite.of_restrictScalars_finite k _ _
  infer_instance

section Extension

variable [Algebra F F']

private theorem functionFieldEquiv_algebraMap_eq {hxt : Transcendental k x}
    {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (a : (twoChartModel hF hx).functionField) :
    functionFieldEquiv hx't (f.functionFieldMap a) =
      algebraMap F F' (functionFieldEquiv hxt a) := by
  have h := hfmap (functionFieldEquiv hxt a)
  rw [AlgEquiv.symm_apply_apply] at h
  exact h

/-- When `F' / F` is separable and a dominant morphism `f : X' ⟶ X` realizes `algebraMap F F'` on
function fields, `f.functionFieldMap` induces a separable field extension
`k(X') / k(X)`. -/
theorem isSeparable_functionFieldMap_of_eq [Algebra.IsSeparable F F']
    {hxt : Transcendental k x} {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z) :
    letI : Algebra (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    Algebra.IsSeparable (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField := by
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  exact Algebra.IsSeparable.of_equiv_equiv (functionFieldEquiv hxt).symm.toRingEquiv
    (functionFieldEquiv hx't).symm.toRingEquiv <| RingHom.ext fun z ↦ by
      apply (functionFieldEquiv hx't).injective
      change functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        functionFieldEquiv hx't ((functionFieldEquiv hx't).symm (algebraMap F F' z))
      rw [hfmap, AlgEquiv.apply_symm_apply]

private theorem isScalarTower_functionFieldMap_of_eq [IsScalarTower k F F']
    {hxt : Transcendental k x} {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z) :
    letI : Algebra (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    IsScalarTower k (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField := by
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  refine .of_algebraMap_eq fun c ↦ (functionFieldEquiv hx't).injective ?_
  change functionFieldEquiv hx't (algebraMap k _ c) =
    functionFieldEquiv hx't (f.functionFieldMap (algebraMap k _ c))
  rw [AlgEquiv.commutes,
    functionFieldEquiv_algebraMap_eq hF hF' hx hx' f hfmap, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

private theorem finiteDimensional_functionFieldMap_of_eq [FiniteDimensional F F']
    {hxt : Transcendental k x} {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z) :
    letI : Algebra (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    FiniteDimensional (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField := by
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  let e : (twoChartModel hF hx).functionField ≃+* F := (functionFieldEquiv hxt).toRingEquiv
  let e' : (twoChartModel hF' hx').functionField ≃+* F' := (functionFieldEquiv hx't).toRingEquiv
  let _ : Algebra (twoChartModel hF hx).functionField F' :=
    ((algebraMap F F').comp (e : _ →+* F)).toAlgebra
  let eL : F' ≃ₗ[(twoChartModel hF hx).functionField] (twoChartModel hF' hx').functionField :=
    { toFun := e'.symm
      invFun := e'
      left_inv := e'.apply_symm_apply
      right_inv := e'.symm_apply_apply
      map_add' := map_add e'.symm
      map_smul' := fun r b ↦ by
        apply e'.injective
        change e' (e'.symm (algebraMap F F' (e r) * b)) = e' (f.functionFieldMap r * e'.symm b)
        rw [e'.apply_symm_apply, map_mul, e'.apply_symm_apply]
        congr 1
        exact (functionFieldEquiv_algebraMap_eq hF hF' hx hx' f hfmap r).symm }
  let _ : Algebra (twoChartModel hF hx).functionField F := e.toRingHom.toAlgebra
  have : IsScalarTower (twoChartModel hF hx).functionField F F' :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite (twoChartModel hF hx).functionField F :=
    Module.Finite.of_surjective (Algebra.linearMap (twoChartModel hF hx).functionField F)
      e.surjective
  have : Module.Finite (twoChartModel hF hx).functionField F' :=
    Module.Finite.trans F F'
  exact Module.Finite.equiv eL

private theorem isSeparable_residueField_toPlace_of_functionFieldMap
    [IsScalarTower k F F'] [FiniteDimensional F F']
    {hxt : Transcendental k x} {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (p : CodimensionOnePoint (twoChartModel hF' hx'))
    [Algebra.IsSeparable ((equivPlace hx't p).restrict k F).ResidueField
      (equivPlace hx't p).ResidueField] :
    letI : Algebra (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    letI := isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap
    letI := finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap
    Algebra.IsSeparable
      (((twoChartModel hF' hx').toPlace (k := k) (p : _)).restrict k
        (twoChartModel hF hx).functionField).ResidueField
      ((twoChartModel hF' hx').toPlace (k := k) (p : _)).ResidueField := by
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  have : IsScalarTower k (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have : FiniteDimensional (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  let P' := (twoChartModel hF' hx').toPlace (k := k) (p : _)
  let Q' := equivPlace (hF := hF') (hx := hx') hx't p
  have hQ' : Q' = P'.map (functionFieldEquiv hx't) := equivPlace_apply hx't p
  have hresMem : ∀ z : (twoChartModel hF hx).functionField,
      z ∈ (P'.restrict k (twoChartModel hF hx).functionField).integers ↔
        functionFieldEquiv hxt z ∈ (Q'.restrict k F).integers := by
    intro z
    rw [Place.mem_integers_restrict_iff, Place.mem_integers_restrict_iff, hQ',
      Place.mem_integers_map_iff,
      ← functionFieldEquiv_algebraMap_eq hF hF' hx hx' f hfmap z,
      AlgEquiv.symm_apply_apply]
    rfl
  let σ₀ : (P'.restrict k (twoChartModel hF hx).functionField).integers ≃+*
      (Q'.restrict k F).integers :=
    { toFun := fun z ↦ ⟨functionFieldEquiv hxt z, (hresMem z).mp z.property⟩
      invFun := fun w ↦ ⟨(functionFieldEquiv hxt).symm w,
        (hresMem _).mpr (by simpa only [AlgEquiv.apply_symm_apply] using w.property)⟩
      left_inv := fun z ↦ Subtype.ext ((functionFieldEquiv hxt).symm_apply_apply z)
      right_inv := fun w ↦ Subtype.ext ((functionFieldEquiv hxt).apply_symm_apply w)
      map_mul' := fun a b ↦ Subtype.ext (map_mul _ _ _)
      map_add' := fun a b ↦ Subtype.ext (map_add _ _ _) }
  have hP'Mem : ∀ z : (twoChartModel hF' hx').functionField,
      z ∈ P'.integers ↔ functionFieldEquiv hx't z ∈ Q'.integers := fun z ↦ by
    rw [hQ', Place.mem_integers_map_iff, AlgEquiv.symm_apply_apply]
  let σ : P'.integers ≃+* Q'.integers :=
    { toFun := fun z ↦ ⟨functionFieldEquiv hx't z, (hP'Mem z).mp z.property⟩
      invFun := fun w ↦ ⟨(functionFieldEquiv hx't).symm w,
        (hP'Mem _).mpr (by simpa only [AlgEquiv.apply_symm_apply] using w.property)⟩
      left_inv := fun z ↦ Subtype.ext ((functionFieldEquiv hx't).symm_apply_apply z)
      right_inv := fun w ↦ Subtype.ext ((functionFieldEquiv hx't).apply_symm_apply w)
      map_mul' := fun a b ↦ Subtype.ext (map_mul _ _ _)
      map_add' := fun a b ↦ Subtype.ext (map_add _ _ _) }
  let _ := Place.algebraIntegersExtension (F' := (twoChartModel hF' hx').functionField)
    (P'.restrict k (twoChartModel hF hx).functionField)
  let _ := Place.algebraIntegersExtension (F' := F') (Q'.restrict k F)
  have hcommInt : ∀ a : (P'.restrict k (twoChartModel hF hx).functionField).integers,
      algebraMap (Q'.restrict k F).integers Q'.integers (σ₀ a) =
        σ (algebraMap (P'.restrict k (twoChartModel hF hx).functionField).integers
          P'.integers a) :=
    fun a ↦ Subtype.ext
      (functionFieldEquiv_algebraMap_eq hF hF' hx hx' f hfmap (a : _)).symm
  let e₀ := IsLocalRing.ResidueField.mapEquiv σ₀
  let e := IsLocalRing.ResidueField.mapEquiv σ
  have he : RingHom.comp (algebraMap (Q'.restrict k F).ResidueField Q'.ResidueField) e₀.toRingHom =
      RingHom.comp e.toRingHom
        (algebraMap (P'.restrict k (twoChartModel hF hx).functionField).ResidueField
          P'.ResidueField) := by
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    exact congrArg (IsLocalRing.residue Q'.integers) (hcommInt a)
  exact Algebra.IsSeparable.of_equiv_equiv e₀.symm e.symm <| by
    ext r
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective r
    simpa [RingEquiv.eq_symm_apply] using
      (congrArg (fun φ : _ →+* Q'.ResidueField ↦ φ (e₀.symm (IsLocalRing.residue _ w))) he).symm

variable [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

private theorem differentExponent_toPlace_of_functionFieldMap {hxt : Transcendental k x}
    {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (p : CodimensionOnePoint (twoChartModel hF' hx')) :
    letI : Algebra (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    letI := isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap
    letI := finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap
    letI := isSeparable_functionFieldMap_of_eq hF hF' hx hx' f hfmap
    Place.differentExponent k (twoChartModel hF hx).functionField
        ((twoChartModel hF' hx').toPlace (k := k) (p : _)) =
      Place.differentExponent k F (equivPlace hx't p) := by
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  have : IsScalarTower k (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have : FiniteDimensional (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have : Algebra.IsSeparable (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    isSeparable_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  let e : F ≃ₐ[k] (twoChartModel hF hx).functionField := (functionFieldEquiv hxt).symm
  let _ : Algebra F (twoChartModel hF hx).functionField := e.toAlgHom.toRingHom.toAlgebra
  let _ : Algebra F (twoChartModel hF' hx').functionField :=
    (f.functionFieldMap.hom.comp e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower F (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k F (twoChartModel hF hx).functionField :=
    .of_algebraMap_eq fun c ↦ (e.commutes c).symm
  have : IsScalarTower k F (twoChartModel hF' hx').functionField :=
    .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply F (twoChartModel hF hx).functionField
          (twoChartModel hF' hx').functionField,
        ← IsScalarTower.algebraMap_apply k F (twoChartModel hF hx).functionField,
        IsScalarTower.algebraMap_apply k (twoChartModel hF hx).functionField
          (twoChartModel hF' hx').functionField]
  have hfinF : Module.finrank F (twoChartModel hF hx).functionField = 1 :=
    Module.finrank_of_bijective_algebraMap e.bijective
  have : FiniteDimensional F (twoChartModel hF hx).functionField :=
    FiniteDimensional.of_finrank_eq_succ hfinF
  have : Algebra.IsSeparable F (twoChartModel hF hx).functionField :=
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl F) e.toRingEquiv
      (RingHom.ext fun _ ↦ rfl)
  let _ : FiniteDimensional F (twoChartModel hF' hx').functionField :=
    FiniteDimensional.trans F (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField
  let _ : Algebra.IsSeparable F (twoChartModel hF' hx').functionField :=
    Algebra.IsSeparable.trans F (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField
  let e' : (twoChartModel hF' hx').functionField ≃ₐ[F] F' :=
    { __ := functionFieldEquiv hx't
      commutes' := fun z ↦ hfmap z }
  let P' := (twoChartModel hF' hx').toPlace (k := k) (p : _)
  rw [← Place.differentExponent_eq_of_finrank_left_eq_one (k₀ := k) (F₀ := F) P' hfinF,
    ← Place.differentExponent_map_restrictScalars (k₀ := k) (F₀ := F) P' e',
    equivPlace_apply]
  rfl

/-- **Cartier ramification divisor equals the trace-dual different on two-chart models** on the
separable-residue branch, for any dominant `k`-morphism `f : X' ⟶ X` realizing `F →ₐ[k] F'` on
function fields when `Ω_{X/k}` and `Ω_{X'/k}` are invertible. -/
theorem equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap
    (hxt : Transcendental k x) (hx't : Transcendental k x')
    [SheafOfModules.isInvertible (twoChartModel hF hx)
      ((twoChartModel hF hx).relativeDifferentials k)]
    [SheafOfModules.isInvertible (twoChartModel hF' hx')
      ((twoChartModel hF' hx').relativeDifferentials k)]
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx)
    [f.IsOver (Spec (.of k))] [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (hsep : ∀ P' : Place k F', Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField) :
    haveI := isCurveOver (hF := hF) (hx := hx) hxt
    haveI := isCurveOver (hF := hF') (hx := hx') hx't
    haveI : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    haveI : Mono (cotangentMap k f) :=
      mono_cotangentMap_of_ne_zero k f
        (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f
          (isSeparable_functionFieldMap_of_eq hF hF' hx hx' f hfmap))
    equivDivisor hx't (ramificationCartierDivisor k f).toWeilDivisor =
      Divisor.different k F' hF := by
  have := isCurveOver (hF := hF) (hx := hx) hxt
  have := isCurveOver (hF := hF') (hx := hx') hx't
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  have := isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have := finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have := isSeparable_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have : Mono (cotangentMap k f) :=
    mono_cotangentMap_of_ne_zero k f
      (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f this)
  ext P'
  obtain ⟨p, rfl⟩ := (equivPlace (hF := hF') (hx := hx') hx't).surjective P'
  have hfxne : f (p : twoChartModel hF' hx') ≠ genericPoint (twoChartModel hF hx) :=
    f.ne_genericPoint_of_isIntegral (k := k) (fun _ ↦ rfl) (p : _)
  have hfxco : Order.coheight (f (p : twoChartModel hF' hx')) = 1 :=
    (Scheme.coheight_eq_one_iff_ne_genericPoint
      (topologicalKrullDim_eq_one (hF := hF) (hx := hx) hxt).le).mpr hfxne
  have : IsDiscreteValuationRing ((twoChartModel hF hx).presheaf.stalk (f (p : _))) :=
    CodimensionOnePoint.isDiscreteValuationRing_stalk ⟨f (p : _), hfxco⟩
  have := hsep (equivPlace hx't p)
  have := isSeparable_residueField_toPlace_of_functionFieldMap hF hF' hx hx' f hfmap p
  rw [coeff_equivDivisor_equivPlace, Divisor.coeff_different,
    Scheme.CartierDivisor.coeff_toWeilDivisor,
    orderAt_ramificationCartierDivisor_eq_differentExponent k f (fun _ ↦ rfl) p,
    differentExponent_toPlace_of_functionFieldMap hF hF' hx hx' f hfmap p]

/-- **Subscheme rank of the ramification locus equals the degree of the trace-dual different** on
two-chart models on the separable-residue branch, for any dominant `k`-morphism `f : X' ⟶ X`
realizing `F →ₐ[k] F'` on function fields when `Ω_{X/k}` and `Ω_{X'/k}` are invertible. -/
theorem finrank_ramificationIdealSheaf_of_functionFieldMap_eq_degree_different
    (hxt : Transcendental k x) (hx't : Transcendental k x')
    [SheafOfModules.isInvertible (twoChartModel hF hx)
      ((twoChartModel hF hx).relativeDifferentials k)]
    [SheafOfModules.isInvertible (twoChartModel hF' hx')
      ((twoChartModel hF' hx').relativeDifferentials k)]
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx)
    [f.IsOver (Spec (.of k))] [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (hsep : ∀ P' : Place k F', Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField) :
    haveI := isCurveOver (hF := hF) (hx := hx) hxt
    haveI := isCurveOver (hF := hF') (hx := hx') hx't
    haveI : (cokernel (cotangentMap k f)).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k f).subschemeι ≫
          twoChartModel hF' hx' ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k F' hF) := by
  have := isCurveOver (hF := hF) (hx := hx) hxt
  have := isCurveOver (hF := hF') (hx := hx') hx't
  let _ : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
    f.functionFieldMap.hom.toAlgebra
  have := isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have := finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have := isSeparable_functionFieldMap_of_eq hF hF' hx hx' f hfmap
  have : Mono (cotangentMap k f) :=
    mono_cotangentMap_of_ne_zero k f
      (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f this)
  have hsepX' : ∀ p : CodimensionOnePoint (twoChartModel hF' hx'),
      Algebra.IsSeparable
        (((twoChartModel hF' hx').toPlace (k := k) (p : _)).restrict k
          (twoChartModel hF hx).functionField).ResidueField
        ((twoChartModel hF' hx').toPlace (k := k) (p : _)).ResidueField := fun p ↦ by
    have := hsep (equivPlace hx't p)
    exact isSeparable_residueField_toPlace_of_functionFieldMap hF hF' hx hx' f hfmap p
  rw [finrank_ramificationIdealSheaf_eq_degree_different k f (fun _ ↦ rfl) hsepX',
    ← equivFunctionFieldDivisor_toWeilDivisor_ramificationCartierDivisor k f (fun _ ↦ rfl) hsepX',
    SchemeWeilDivisor.degree_equivFunctionFieldDivisor
      (valuativeCriterion_existence hF' hx') coheight_le_one,
    ← degree_equivDivisor hx't,
    equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap hF hF' hx hx' hxt hx't
      f hfmap hsep]

/-- **Cartier ramification divisor equals the trace-dual different on smooth two-chart models**
on the separable-residue branch, for `f = homOfAlgHom hF hF' hx hx' hxt hx't (toAlgHom k F F')`. -/
theorem equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom
    (hxt : Transcendental k x) (hx't : Transcendental k x')
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))]
    [Smooth (twoChartModel hF' hx' ↘ Spec (.of k))]
    (hsep : ∀ P' : Place k F', Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField) :
    haveI := isInvertible_relativeDifferentials (hF := hF) (hx := hx) hxt
    haveI := isInvertible_relativeDifferentials (hF := hF') (hx := hx') hx't
    haveI : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
      (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F')).functionFieldMap.hom.toAlgebra
    haveI : Mono (cotangentMap k (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F'))) :=
      mono_cotangentMap_of_ne_zero k _
        (cotangentMap_ne_zero_of_isDominant_of_isSeparable k _
          (isSeparable_functionFieldMap_of_eq hF hF' hx hx' _
            (fun z ↦ functionFieldEquiv_functionFieldMap_homOfAlgHom hF hF' hx hx'
              (IsScalarTower.toAlgHom k F F') z)))
    equivDivisor hx't (ramificationCartierDivisor k
        (homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F'))).toWeilDivisor =
      Divisor.different k F' hF :=
  have := isInvertible_relativeDifferentials (hF := hF) (hx := hx) hxt
  have := isInvertible_relativeDifferentials (hF := hF') (hx := hx') hx't
  equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_homOfAlgHom hF hF' hx hx'
      (IsScalarTower.toAlgHom k F F') z)
    hsep

/-- Specialization of `equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom` to
`twoChartModel.map`. -/
theorem equivDivisor_toWeilDivisor_ramificationCartierDivisor_map
    (hxt : Transcendental k x) (hx't : Transcendental k x') (h : algebraMap F F' x = x')
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))]
    [Smooth (twoChartModel hF' hx' ↘ Spec (.of k))]
    (hsep : ∀ P' : Place k F', Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField) :
    haveI := isInvertible_relativeDifferentials (hF := hF) (hx := hx) hxt
    haveI := isInvertible_relativeDifferentials (hF := hF') (hx := hx') hx't
    haveI : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
      (map hF hF' hx hx' h).functionFieldMap.hom.toAlgebra
    haveI : Mono (cotangentMap k (map hF hF' hx hx' h)) :=
      mono_cotangentMap_of_ne_zero k _
        (cotangentMap_ne_zero_of_isDominant_of_isSeparable k _
          (isSeparable_functionFieldMap_of_eq hF hF' hx hx' _
            (fun z ↦ functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z)))
    equivDivisor hx't (ramificationCartierDivisor k (map hF hF' hx hx' h)).toWeilDivisor =
      Divisor.different k F' hF :=
  have := isInvertible_relativeDifferentials (hF := hF) (hx := hx) hxt
  have := isInvertible_relativeDifferentials (hF := hF') (hx := hx') hx't
  equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z) hsep

/-- **Subscheme rank of the ramification locus equals the degree of the trace-dual different** on
smooth two-chart models on the separable-residue branch, for `f = homOfAlgHom`. -/
theorem finrank_ramificationIdealSheaf_homOfAlgHom_eq_degree_different
    (hxt : Transcendental k x) (hx't : Transcendental k x')
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))]
    [Smooth (twoChartModel hF' hx' ↘ Spec (.of k))]
    (hsep : ∀ P' : Place k F', Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField) :
    haveI := isCurveOver (hF := hF) (hx := hx) hxt
    haveI := isCurveOver (hF := hF') (hx := hx') hx't
    haveI : (cokernel (cotangentMap k (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F')))).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F'))).subschemeι ≫
          twoChartModel hF' hx' ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k F' hF) :=
  have := isInvertible_relativeDifferentials (hF := hF) (hx := hx) hxt
  have := isInvertible_relativeDifferentials (hF := hF') (hx := hx') hx't
  finrank_ramificationIdealSheaf_of_functionFieldMap_eq_degree_different hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_homOfAlgHom hF hF' hx hx'
      (IsScalarTower.toAlgHom k F F') z)
    hsep

/-- Specialization of `finrank_ramificationIdealSheaf_homOfAlgHom_eq_degree_different` to
`twoChartModel.map`. -/
theorem finrank_ramificationIdealSheaf_map_eq_degree_different
    (hxt : Transcendental k x) (hx't : Transcendental k x') (h : algebraMap F F' x = x')
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))]
    [Smooth (twoChartModel hF' hx' ↘ Spec (.of k))]
    (hsep : ∀ P' : Place k F', Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField) :
    haveI := isCurveOver (hF := hF) (hx := hx) hxt
    haveI := isCurveOver (hF := hF') (hx := hx') hx't
    haveI : (cokernel (cotangentMap k (map hF hF' hx hx' h))).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k (map hF hF' hx hx' h)).subschemeι ≫
          twoChartModel hF' hx' ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k F' hF) :=
  have := isInvertible_relativeDifferentials (hF := hF) (hx := hx) hxt
  have := isInvertible_relativeDifferentials (hF := hF') (hx := hx') hx't
  finrank_ramificationIdealSheaf_of_functionFieldMap_eq_degree_different hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z) hsep

section PerfectField

variable [PerfectField k]

/-- Over a perfect field `k`, for any finite separable extension `F' / F` of function fields, the
Weil divisor of `ramificationCartierDivisor k (homOfAlgHom ...)` matches
`Divisor.different k F' hF`. -/
theorem equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom_of_perfectField
    (hxt : Transcendental k x) (hx't : Transcendental k x') :
    haveI := smoothOfRelativeDimension_one_of_perfectField (hF := hF) (hx := hx) hxt
    haveI := smoothOfRelativeDimension_one_of_perfectField (hF := hF') (hx := hx') hx't
    haveI := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
      (X := twoChartModel hF hx) k
    haveI := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
      (X := twoChartModel hF' hx') k
    haveI : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
      (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F')).functionFieldMap.hom.toAlgebra
    haveI : Mono (cotangentMap k (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F'))) :=
      mono_cotangentMap_of_ne_zero k _
        (cotangentMap_ne_zero_of_isDominant_of_isSeparable k _
          (isSeparable_functionFieldMap_of_eq hF hF' hx hx' _
            (fun z ↦ functionFieldEquiv_functionFieldMap_homOfAlgHom hF hF' hx hx'
              (IsScalarTower.toAlgHom k F F') z)))
    equivDivisor hx't (ramificationCartierDivisor k
        (homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F'))).toWeilDivisor =
      Divisor.different k F' hF :=
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF) (hx := hx) hxt
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF') (hx := hx') hx't
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF hx) k
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF' hx') k
  equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_homOfAlgHom hF hF' hx hx'
      (IsScalarTower.toAlgHom k F F') z)
    (isSeparable_residueField_of_perfectField hF hF')

/-- Over a perfect field `k`, the Weil divisor of `ramificationCartierDivisor k (map ...)`
matches `Divisor.different k F' hF`. -/
theorem equivDivisor_toWeilDivisor_ramificationCartierDivisor_map_of_perfectField
    (hxt : Transcendental k x) (hx't : Transcendental k x') (h : algebraMap F F' x = x') :
    haveI := smoothOfRelativeDimension_one_of_perfectField (hF := hF) (hx := hx) hxt
    haveI := smoothOfRelativeDimension_one_of_perfectField (hF := hF') (hx := hx') hx't
    haveI := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
      (X := twoChartModel hF hx) k
    haveI := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
      (X := twoChartModel hF' hx') k
    haveI : Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField :=
      (map hF hF' hx hx' h).functionFieldMap.hom.toAlgebra
    haveI : Mono (cotangentMap k (map hF hF' hx hx' h)) :=
      mono_cotangentMap_of_ne_zero k _
        (cotangentMap_ne_zero_of_isDominant_of_isSeparable k _
          (isSeparable_functionFieldMap_of_eq hF hF' hx hx' _
            (fun z ↦ functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z)))
    equivDivisor hx't (ramificationCartierDivisor k (map hF hF' hx hx' h)).toWeilDivisor =
      Divisor.different k F' hF :=
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF) (hx := hx) hxt
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF') (hx := hx') hx't
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF hx) k
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF' hx') k
  equivDivisor_toWeilDivisor_ramificationCartierDivisor_of_functionFieldMap hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z)
    (isSeparable_residueField_of_perfectField hF hF')

/-- Over a perfect field `k`, `dim_k Γ(R_f, 𝒪_{R_f}) = deg Diff(F'/F)` for `f = homOfAlgHom`. -/
theorem finrank_ramificationIdealSheaf_homOfAlgHom_eq_degree_different_of_perfectField
    (hxt : Transcendental k x) (hx't : Transcendental k x') :
    haveI := isCurveOver (hF := hF) (hx := hx) hxt
    haveI := isCurveOver (hF := hF') (hx := hx') hx't
    haveI : (cokernel (cotangentMap k (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F')))).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k (homOfAlgHom hF hF' hx hx' hxt hx't
        (IsScalarTower.toAlgHom k F F'))).subschemeι ≫
          twoChartModel hF' hx' ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k F' hF) :=
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF) (hx := hx) hxt
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF') (hx := hx') hx't
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF hx) k
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF' hx') k
  finrank_ramificationIdealSheaf_of_functionFieldMap_eq_degree_different hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_homOfAlgHom hF hF' hx hx'
      (IsScalarTower.toAlgHom k F F') z)
    (isSeparable_residueField_of_perfectField hF hF')

/-- Over a perfect field `k`, `dim_k Γ(R_f, 𝒪_{R_f}) = deg Diff(F'/F)` for `f = map`. -/
theorem finrank_ramificationIdealSheaf_map_eq_degree_different_of_perfectField
    (hxt : Transcendental k x) (hx't : Transcendental k x') (h : algebraMap F F' x = x') :
    haveI := isCurveOver (hF := hF) (hx := hx) hxt
    haveI := isCurveOver (hF := hF') (hx := hx') hx't
    haveI : (cokernel (cotangentMap k (map hF hF' hx hx' h))).IsFiniteType := by infer_instance
    (((ramificationIdealSheaf k (map hF hF' hx hx' h)).subschemeι ≫
          twoChartModel hF' hx' ↘ Spec (.of k)).finrank default : ℤ) =
      Divisor.degree (Divisor.different k F' hF) :=
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF) (hx := hx) hxt
  have := smoothOfRelativeDimension_one_of_perfectField (hF := hF') (hx := hx') hx't
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF hx) k
  have := _root_.TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials
    (X := twoChartModel hF' hx') k
  finrank_ramificationIdealSheaf_of_functionFieldMap_eq_degree_different hF hF' hx hx' hxt hx't _
    (fun z ↦ functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z)
    (isSeparable_residueField_of_perfectField hF hF')

end PerfectField

end Extension

end TauCeti.AlgebraicGeometry.twoChartModel

end
