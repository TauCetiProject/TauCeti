/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Finite flat charts over fields

A nonempty scheme locally of finite type over a field has a nonempty affine open
finite and flat over a nonempty principal open in polynomial affine space. Noether
normalization gives a finite map, and spreading a basis from the fraction field supplies
flatness after restricting to a principal open. The chart map is also locally of finite
presentation, and both structure maps to the ground field commute.

This provides finite flat parameter charts for translated-divisor constructions in
projectivity arguments for algebraic groups.

## Main results

* `AlgebraicGeometry.Scheme.exists_finite_flat_chart`.

## References

* J. S. Milne, *Abelian Varieties*, I, Section 6.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A nonempty scheme locally of finite type over a field contains a nonempty affine
open finite and flat over a nonempty principal open of polynomial affine space. The map
is locally of finite presentation and respects the given structure map to the field. -/
theorem Scheme.exists_finite_flat_chart (X : Scheme.{u}) [Nonempty X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ (U : Scheme.{u}) (i : U ⟶ X) (n : ℕ) (r : MvPolynomial (Fin n) k)
      (p : U ⟶ Spec (.of (Localization.Away r))),
      IsOpenImmersion i ∧ IsAffine U ∧ Nonempty U ∧ r ≠ 0 ∧
        IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧
        i ≫ f = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra k Γ(X, U) :=
    ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k Γ(X, U)
  let : Algebra (MvPolynomial (Fin n) k) Γ(X, U) := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) k) Γ(X, U) := hfin
  have : Module.FinitePresentation (MvPolynomial (Fin n) k) Γ(X, U) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hr, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors (MvPolynomial (Fin n) k))
      (LocalizedModule.mkLinearMap (nonZeroDivisors (MvPolynomial (Fin n) k)) Γ(X, U))
      (FractionRing (MvPolynomial (Fin n) k))
  have hr : r ≠ 0 := nonZeroDivisors.ne_zero hr
  let B := Localization (Algebra.algebraMapSubmonoid Γ(X, U) (.powers r))
  have hfin' : Module.Finite (Localization.Away r) B :=
    Module.Finite.of_isLocalizedModule (.powers r)
      (IsScalarTower.toAlgHom (MvPolynomial (Fin n) k) Γ(X, U) B).toLinearMap
  have hflat : Module.Flat (Localization.Away r) B :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv (.powers r)
      (LocalizedModule.mkLinearMap (.powers r) Γ(X, U))
      (IsScalarTower.toAlgHom (MvPolynomial (Fin n) k) Γ(X, U) B).toLinearMap
      ).extendScalarsOfIsLocalization (.powers r) (Localization.Away r)).symm
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin n) k) Γ(X, U) r) B := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have hloc0 : (0 : Γ(X, U)) ∉ Algebra.algebraMapSubmonoid Γ(X, U) (.powers r) := by
    rintro ⟨_, ⟨n, rfl⟩, hp⟩
    change g (r ^ n) = 0 at hp
    exact (pow_ne_zero n hr) (hg (by simpa using hp))
  have : Nontrivial B := (IsLocalization.toLocalizationMap _ B).nontrivial hloc0
  have := IsOpenImmersion.of_isLocalization
    (algebraMap (MvPolynomial (Fin n) k) Γ(X, U) r) (S := B)
  refine ⟨Spec (.of B),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B)) ≫ hU.fromSpec,
    n, r, Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) B)), inferInstance,
    inferInstance, inferInstance, hr, (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr hfin'), Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr hflat), HasRingHomProperty.Spec_iff.mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)), ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (Localization.Away r),
    ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k) (Localization.Away r) B,
    IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k) Γ(X, U) B]
  congr 1
  exact (g.commutes a).symm

end AlgebraicGeometry
