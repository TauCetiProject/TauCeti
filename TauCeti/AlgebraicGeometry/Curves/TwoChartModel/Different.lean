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
import TauCeti.FieldTheory.FunctionField.Place.Extension.Equiv

/-!
# The Cartier ramification divisor and trace-dual different on two-chart models

Let `F' / F` be a finite separable extension of algebraic function fields over a field `k`, and let
`X = twoChartModel hF hx` and `X' = twoChartModel hF' hx'` be regular proper models of `F` and
`F'` built from arbitrary nonzero transcendental functions `x ∈ F` and `x' ∈ F'`. The inclusion
`F →ₐ[k] F'` induces a finite dominant `k`-morphism
`homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F') : X' ⟶ X`, which agrees with the
glued chart morphism `twoChartModel.map` whenever `algebraMap F F' x = x'`.

Transporting `Place.differentExponent` across the function-field identifications
`twoChartModel.functionFieldEquiv` shows that for any dominant `k`-morphism `f : X' ⟶ X`
compatible with `F → F'` on the separable-residue branch (and in particular automatically for
`homOfAlgHom` and `map` whenever `k` is a perfect field), the Cartier ramification divisor of `f`
corresponds under `twoChartModel.equivDivisor` to the trace-dual different divisor
`Divisor.different k F' hF` (`equivDivisor_toWeilDivisor_ramificationCartierDivisor_homOfAlgHom`),
and the subscheme rank `dim_k Γ(R_f, 𝒪_{R_f})` of its ramification locus equals `deg Diff(F'/F)`
(`finrank_ramificationIdealSheaf_homOfAlgHom_eq_degree_different`).

## Main results

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

section Extension

variable [Algebra F F']

section PrivateHelpers

variable [IsScalarTower k F F'] [FiniteDimensional F F']
  {hxt : Transcendental k x} {hx't : Transcendental k x'}
  [Algebra (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField]
  [IsScalarTower k (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField]
  [FiniteDimensional (twoChartModel hF hx).functionField (twoChartModel hF' hx').functionField]

private noncomputable def integersEquivRestrict
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (halg : ∀ a : (twoChartModel hF hx).functionField,
      algebraMap (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField a = f.functionFieldMap a)
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (P' : Place k (twoChartModel hF' hx').functionField) :
    (P'.restrict k (twoChartModel hF hx).functionField).integers ≃+*
      ((P'.map (functionFieldEquiv hx't)).restrict k F).integers :=
  (Place.integersEquivMap (functionFieldEquiv hxt)
      (P'.restrict k (twoChartModel hF hx).functionField)).trans
    (RingEquiv.subringCongr (congrArg (fun q ↦ q.integers.toSubring)
      (Place.restrict_map (functionFieldEquiv hx't) (functionFieldEquiv hxt)
        (fun a ↦ by
          rw [halg a]
          exact functionFieldEquiv_algebraMap_eq hF hF' hx hx' f hfmap a) P').symm))

private theorem residueField_comm_of_functionFieldMap
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (halg : ∀ a : (twoChartModel hF hx).functionField,
      algebraMap (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField a = f.functionFieldMap a)
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (P' : Place k (twoChartModel hF' hx').functionField) :
    (algebraMap ((P'.map (functionFieldEquiv hx't)).restrict k F).ResidueField
        (P'.map (functionFieldEquiv hx't)).ResidueField).comp
      (IsLocalRing.ResidueField.mapEquiv
        (integersEquivRestrict hF hF' hx hx' f halg hfmap P')).toRingHom =
      (Place.residueFieldEquivMap (functionFieldEquiv hx't) P').toRingEquiv.toRingHom.comp
        (algebraMap (P'.restrict k (twoChartModel hF hx).functionField).ResidueField
          P'.ResidueField) := by
  let _ := Place.algebraIntegersExtension (F' := (twoChartModel hF' hx').functionField)
    (P'.restrict k (twoChartModel hF hx).functionField)
  let _ := Place.algebraIntegersExtension (F' := F')
    ((P'.map (functionFieldEquiv hx't)).restrict k F)
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
    AlgEquiv.coe_toRingEquiv, IsLocalRing.ResidueField.algebraMap_residue,
    Place.residueFieldEquivMap_residue]
  refine congrArg (IsLocalRing.residue (P'.map (functionFieldEquiv hx't)).integers) ?_
  refine Subtype.ext ?_
  rw [Place.coe_integersEquivMap, Place.coe_algebraMap_integers, Place.coe_algebraMap_integers]
  dsimp only [integersEquivRestrict]
  rw [RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply, Place.coe_integersEquivMap, halg]
  exact (functionFieldEquiv_algebraMap_eq hF hF' hx hx' f hfmap (a : _)).symm

private theorem isSeparable_residueField_toPlace_of_functionFieldMap
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (halg : ∀ a : (twoChartModel hF hx).functionField,
      algebraMap (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField a = f.functionFieldMap a)
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (p : CodimensionOnePoint (twoChartModel hF' hx'))
    [Algebra.IsSeparable ((equivPlace hx't p).restrict k F).ResidueField
      (equivPlace hx't p).ResidueField] :
    Algebra.IsSeparable
      (((twoChartModel hF' hx').toPlace (k := k) (p : _)).restrict k
        (twoChartModel hF hx).functionField).ResidueField
      ((twoChartModel hF' hx').toPlace (k := k) (p : _)).ResidueField := by
  let P' := (twoChartModel hF' hx').toPlace (k := k) (p : _)
  have hsep : Algebra.IsSeparable ((P'.map (functionFieldEquiv hx't)).restrict k F).ResidueField
      (P'.map (functionFieldEquiv hx't)).ResidueField := by
    rw [← equivPlace_apply hx't p]
    infer_instance
  exact (Algebra.IsSeparable.iff_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (integersEquivRestrict hF hF' hx hx' f halg hfmap P'))
    (Place.residueFieldEquivMap (functionFieldEquiv hx't) P').toRingEquiv
    (residueField_comm_of_functionFieldMap hF hF' hx hx' f halg hfmap P')).mpr hsep

private theorem differentExponent_toPlace_of_functionFieldMap
    [Algebra.IsSeparable F F']
    [Algebra.IsSeparable (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField]
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (halg : ∀ a : (twoChartModel hF hx).functionField,
      algebraMap (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField a = f.functionFieldMap a)
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z)
    (p : CodimensionOnePoint (twoChartModel hF' hx')) :
    Place.differentExponent k (twoChartModel hF hx).functionField
        ((twoChartModel hF' hx').toPlace (k := k) (p : _)) =
      Place.differentExponent k F (equivPlace hx't p) := by
  let e : F ≃ₐ[k] (twoChartModel hF hx).functionField := (functionFieldEquiv hxt).symm
  let _ : Algebra F (twoChartModel hF hx).functionField := e.toAlgHom.toRingHom.toAlgebra
  let _ : Algebra F (twoChartModel hF' hx').functionField :=
    (f.functionFieldMap.hom.comp e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower F (twoChartModel hF hx).functionField
      (twoChartModel hF' hx').functionField :=
    .of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra, halg]
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
    show e'.restrictScalars k = functionFieldEquiv hx't from AlgEquiv.ext fun _ ↦ rfl,
    equivPlace_apply]

end PrivateHelpers

variable [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

private theorem functionFieldMap_extension {hxt : Transcendental k x} {hx't : Transcendental k x'}
    (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx) [IsDominant f]
    (hfmap : ∀ z : F,
      functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        algebraMap F F' z) :
    letI : Algebra (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
      f.functionFieldMap.hom.toAlgebra
    IsScalarTower k (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField ∧
      FiniteDimensional (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField ∧
      Algebra.IsSeparable (twoChartModel hF hx).functionField
        (twoChartModel hF' hx').functionField :=
  ⟨isScalarTower_functionFieldMap_of_eq hF hF' hx hx' f hfmap,
    finiteDimensional_functionFieldMap_of_eq hF hF' hx hx' f hfmap,
    isSeparable_functionFieldMap_of_eq hF hF' hx hx' f hfmap⟩

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
  obtain ⟨_, _, _⟩ := functionFieldMap_extension hF hF' hx hx' f hfmap
  have : Mono (cotangentMap k f) :=
    mono_cotangentMap_of_ne_zero k f
      (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f ‹_›)
  ext P'
  obtain ⟨p, rfl⟩ := (equivPlace (hF := hF') (hx := hx') hx't).surjective P'
  have : IsDiscreteValuationRing ((twoChartModel hF hx).presheaf.stalk (f (p : _))) :=
    f.isDiscreteValuationRing_stalk_image (k := k) (fun _ ↦ rfl)
      (topologicalKrullDim_eq_one (hF := hF) (hx := hx) hxt).le (p : _)
  have := hsep (equivPlace hx't p)
  have := isSeparable_residueField_toPlace_of_functionFieldMap
    hF hF' hx hx' f (fun _ ↦ rfl) hfmap p
  rw [coeff_equivDivisor_equivPlace, Divisor.coeff_different,
    Scheme.CartierDivisor.coeff_toWeilDivisor,
    orderAt_ramificationCartierDivisor_eq_differentExponent k f (fun _ ↦ rfl) p,
    differentExponent_toPlace_of_functionFieldMap hF hF' hx hx' f (fun _ ↦ rfl) hfmap p]

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
  obtain ⟨_, _, _⟩ := functionFieldMap_extension hF hF' hx hx' f hfmap
  have : Mono (cotangentMap k f) :=
    mono_cotangentMap_of_ne_zero k f
      (cotangentMap_ne_zero_of_isDominant_of_isSeparable k f ‹_›)
  have hsepX' : ∀ p : CodimensionOnePoint (twoChartModel hF' hx'),
      Algebra.IsSeparable
        (((twoChartModel hF' hx').toPlace (k := k) (p : _)).restrict k
          (twoChartModel hF hx).functionField).ResidueField
        ((twoChartModel hF' hx').toPlace (k := k) (p : _)).ResidueField := fun p ↦ by
    have := hsep (equivPlace hx't p)
    exact isSeparable_residueField_toPlace_of_functionFieldMap
      hF hF' hx hx' f (fun _ ↦ rfl) hfmap p
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
    (Place.isSeparable_residueField_restrict_of_perfectField hF)

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
    (Place.isSeparable_residueField_restrict_of_perfectField hF)

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
    (Place.isSeparable_residueField_restrict_of_perfectField hF)

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
    (Place.isSeparable_residueField_restrict_of_perfectField hF)

end PerfectField

end Extension

end TauCeti.AlgebraicGeometry.twoChartModel

end
