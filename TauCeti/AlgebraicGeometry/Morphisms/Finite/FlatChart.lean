/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

public import TauCeti.RingTheory.NoetherNormalization
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite flat parameter spaces over fields

A nonempty scheme locally of finite type over a field has a nonempty affine open
finite, flat and surjective over a nonempty principal open in polynomial affine space.
The map is locally of finite presentation and both structure maps to the field commute.
This supplies parameter spaces for translated-divisor constructions in projectivity
arguments for algebraic groups.

## References

* The Stacks Project, Tags 00OW (Noether normalization) and 051R (generic freeness).
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]

/-- A nonempty scheme locally of finite type over a field contains a nonempty affine
open finite, flat and surjective over a nonempty principal open of polynomial affine space.
The finite flat map is locally of finite presentation and respects the ground-field map. -/
theorem exists_isOpenImmersion_isFinite_flat_surjective_localizationAway_mvPolynomial
    {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ (U : Scheme.{u}) (i : U ⟶ X) (n : ℕ) (r : MvPolynomial (Fin n) k)
      (p : U ⟶ Spec (.of (Localization.Away r))),
      IsOpenImmersion i ∧ IsAffine U ∧ Nonempty U ∧ r ≠ 0 ∧
        IsFinite p ∧ Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
        i ≫ f = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨A, i, _, y, φ, hφ, -, hft⟩ := f.exists_isOpenImmersion_finiteType x
  have : Nontrivial A := PrimeSpectrum.nontrivial y
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k A := hft
  obtain ⟨n, g, -, r, hr, hfin, hfree, hloc0⟩ :=
    Algebra.FiniteType.exists_injective_finite_free_localizedModule_powers k A
  let := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) k) A := hfin
  let B := Localization (Algebra.algebraMapSubmonoid A (.powers r))
  let l : A →ₗ[MvPolynomial (Fin n) k] B :=
    (IsScalarTower.toAlgHom (MvPolynomial (Fin n) k) A B).toLinearMap
  let e := (IsLocalizedModule.linearEquiv (.powers r)
    (LocalizedModule.mkLinearMap (.powers r) A) l).extendScalarsOfIsLocalization
      (.powers r) (Localization.Away r)
  have : Module.Finite (Localization.Away r) B :=
    Module.Finite.of_isLocalizedModule (.powers r) l
  have : Module.Free (Localization.Away r) B := Module.Free.of_equiv' hfree e
  have : Nontrivial B := (IsLocalization.toLocalizationMap _ B).nontrivial hloc0
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin n) k) A r) B := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have := IsOpenImmersion.of_isLocalization (algebraMap (MvPolynomial (Fin n) k) A r) (S := B)
  have hfaith : (algebraMap (Localization.Away r) B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hflat, hsurj⟩ :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap (Localization.Away r) B))).mpr
      hfaith
  refine ⟨Spec (.of B), Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ i,
    n, r, Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) B)), inferInstance,
    inferInstance, inferInstance, hr, (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance), hflat, hsurj, HasRingHomProperty.Spec_iff.mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)), ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (Localization.Away r),
    ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k) (Localization.Away r) B,
    IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k) A B]
  congr 1
  simpa only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using (g.commutes a).symm

end AlgebraicGeometry.Scheme.Hom
