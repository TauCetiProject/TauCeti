/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Linear actions on the projective spectrum of a symmetric algebra

A linear equivalence induces a contravariant isomorphism of projective spectra.
Applying this construction to inverse equivalences gives a homomorphism into scheme
automorphisms and hence, for any linear group action, an action by continuous translations.
These are the translations used in studying projective orbits and homogeneous spaces.

The convention here is `Proj(Sym M)`: `M` is the module of linear homogeneous coordinates.
For the projective space of lines in a finite locally free module `V`, take `M = V∨`
and the contragredient representation. No finite generation or freeness is needed here.
The point action is selected explicitly, since a scheme can admit many linear actions.
This file constructs individual scheme automorphisms; it does not construct a morphism
from a product of schemes representing a family of translations.

The construction combines `SymmetricAlgebra.gradedMap` with `Proj.mapIso`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective representations and orbits.
-/

public section

open CategoryTheory
open TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Proj

universe u v

variable (R : Type u) [CommRing R]
variable {M N P : Type u} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- A linear equivalence induces a contravariant isomorphism of projective spectra of
symmetric algebras. -/
noncomputable def symmetricAlgebraMapIso (e : M ≃ₗ[R] N) :
    Proj (homogeneousSubmodule R N) ≅ Proj (homogeneousSubmodule R M) :=
  mapIso (SymmetricAlgebra.gradedMap R e.toLinearMap)
    (SymmetricAlgebra.gradedMap R e.symm.toLinearMap)
    (by intro a; simpa only [SymmetricAlgebra.gradedMap_apply] using
      SymmetricAlgebra.map_rightInverse R e.apply_symm_apply a)
    (by intro a; simpa only [SymmetricAlgebra.gradedMap_apply] using
      SymmetricAlgebra.map_leftInverse R e.symm_apply_apply a)

/-- The forward projective map pulls coordinates back by the given linear equivalence. -/
@[simp]
theorem symmetricAlgebraMapIso_hom (e : M ≃ₗ[R] N) :
    (symmetricAlgebraMapIso R e).hom =
      map (SymmetricAlgebra.gradedMap R e.toLinearMap)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _
          (by simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
            SymmetricAlgebra.map_surjective R e.toLinearMap e.surjective)) := by
  rw [symmetricAlgebraMapIso, mapIso_hom]

/-- The inverse projective map pulls coordinates back by the inverse linear equivalence. -/
@[simp]
theorem symmetricAlgebraMapIso_inv (e : M ≃ₗ[R] N) :
    (symmetricAlgebraMapIso R e).inv =
      map (SymmetricAlgebra.gradedMap R e.symm.toLinearMap)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _
          (by simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
            SymmetricAlgebra.map_surjective R e.symm.toLinearMap e.symm.surjective)) := by
  rw [symmetricAlgebraMapIso, mapIso_inv]

/-- A projective linear automorphism fixes the degree-zero structural morphism. -/
-- Preserve this square before simplifying the isomorphism to `Proj.map`.
@[reassoc (attr := simp↓)]
theorem symmetricAlgebraMapIso_hom_toSpecZero (e : M ≃ₗ[R] M) :
    (symmetricAlgebraMapIso R e).hom ≫ toSpecZero (homogeneousSubmodule R M) =
      toSpecZero (homogeneousSubmodule R M) := by
  rw [symmetricAlgebraMapIso_hom, map_toSpecZero]
  simp

/-- Inverting a linear equivalence inverts its projective isomorphism. -/
@[simp]
theorem symmetricAlgebraMapIso_symm (e : M ≃ₗ[R] N) :
    symmetricAlgebraMapIso R e.symm = (symmetricAlgebraMapIso R e).symm := by
  apply Iso.ext
  simp

/-- The identity equivalence induces the identity projective isomorphism. -/
@[simp]
theorem symmetricAlgebraMapIso_refl :
    symmetricAlgebraMapIso R (LinearEquiv.refl R M) = Iso.refl _ := by
  apply Iso.ext
  simp [map_id]

/-- Projective pullback reverses composition of linear equivalences. -/
@[simp]
theorem symmetricAlgebraMapIso_trans (e : M ≃ₗ[R] N) (d : N ≃ₗ[R] P) :
    symmetricAlgebraMapIso R (e.trans d) =
      (symmetricAlgebraMapIso R d).trans (symmetricAlgebraMapIso R e) := by
  apply Iso.ext
  simp only [symmetricAlgebraMapIso_hom, Iso.trans_hom]
  rw [← map_comp]
  congr 1
  simp only [SymmetricAlgebra.gradedMap_comp, LinearEquiv.coe_trans]

/-- Inverse pullback turns linear coordinate automorphisms into scheme automorphisms,
with the usual (function-composition) multiplication on both groups. -/
noncomputable def symmetricAlgebraAut :
    (M ≃ₗ[R] M) →* Aut (Proj (homogeneousSubmodule R M)) where
  toFun e := symmetricAlgebraMapIso R e.symm
  map_one' := symmetricAlgebraMapIso_refl R
  map_mul' e d := by
    -- Multiplication of linear equivalences and of categorical automorphisms both
    -- reverses the order of `trans`; inverse pullback compensates for contravariance.
    exact symmetricAlgebraMapIso_trans R e.symm d.symm

/-- The automorphism attached to `e` is projective pullback by `e⁻¹`. -/
@[simp]
theorem symmetricAlgebraAut_apply (e : M ≃ₗ[R] M) :
    symmetricAlgebraAut R e = symmetricAlgebraMapIso R e.symm := (rfl)

variable {G : Type v} [Monoid G]

/-- A linear group action gives an action on `Proj(Sym M)` by scheme automorphisms.
Install this definition as a local instance to select the action. -/
@[instance_reducible]
noncomputable def symmetricAlgebraMulAction (ρ : G →* (M ≃ₗ[R] M)) :
    MulAction G (Proj (homogeneousSubmodule R M)) where
  smul g x := (symmetricAlgebraMapIso R (ρ g).symm).hom x
  one_smul x := by
    -- Expose the action field being constructed; its computation lemma is not yet available.
    change (symmetricAlgebraMapIso R (ρ 1).symm).hom x = x
    rw [map_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_symm,
      symmetricAlgebraMapIso_refl]
    rfl
  mul_smul g h x := by
    -- Expose the action field being constructed before using projective functoriality.
    change (symmetricAlgebraMapIso R (ρ (g * h)).symm).hom x =
      (symmetricAlgebraMapIso R (ρ g).symm).hom
        ((symmetricAlgebraMapIso R (ρ h).symm).hom x)
    rw [map_mul, LinearEquiv.mul_eq_trans, LinearEquiv.trans_symm]
    exact congrArg (fun e => e.hom x)
      (symmetricAlgebraMapIso_trans R (ρ g).symm (ρ h).symm)

variable (ρ : G →* (M ≃ₗ[R] M))

/-- The selected point action is the underlying map of the projective scheme automorphism. -/
theorem symmetricAlgebra_smul_def (g : G) (x : Proj (homogeneousSubmodule R M)) :
    letI := symmetricAlgebraMulAction R ρ
    g • x = (symmetricAlgebraMapIso R (ρ g).symm).hom x := (rfl)

/-- Every translation of the selected projective action is continuous in the Zariski topology. -/
theorem symmetricAlgebraMulAction_continuousConstSMul :
    letI := symmetricAlgebraMulAction R ρ
    ContinuousConstSMul G (Proj (homogeneousSubmodule R M)) := by
  let := symmetricAlgebraMulAction R ρ
  exact ⟨fun g => (symmetricAlgebraMapIso R (ρ g).symm).hom.continuous⟩

end AlgebraicGeometry.Proj
