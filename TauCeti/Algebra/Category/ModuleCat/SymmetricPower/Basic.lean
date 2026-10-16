/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

/-!
# The symmetric powers as functors on the category of modules

Given `M : ModuleCat R` over a commutative ring `R` and `n : ℕ`, this file defines
`M.symmetricPower n : ModuleCat R` as the degree-`n` homogeneous submodule
`TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n` of the symmetric algebra of `M`, and
extends it to a functor `ModuleCat.symmetricPower.functor R n`. The zeroth and first symmetric
powers are identified with `R` and with `M`, naturally.

The degree-`n` piece of the symmetric algebra is used rather than the symmetric tensor power
`Sym[R]^n M`: Mathlib's `SymmetricPower R ι M` requires the index type `ι` to live in the universe
of `R`, so `Sym[R]^n M = Sym[R] (Fin n) M` is only available for rings in `Type`, while the
homogeneous pieces exist in every universe and assemble into the graded symmetric algebra.

This is the analogue of Mathlib's `ModuleCat.exteriorPower`, and it is the sectionwise input for
the symmetric powers of presheaves and sheaves of modules.
-/

public section

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The `n`-th symmetric power of an object of `ModuleCat R`: the degree-`n` homogeneous
submodule of its symmetric algebra. -/
abbrev symmetricPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n)

namespace symmetricPower

/-- The morphism on `n`-th symmetric powers induced by a morphism of modules: the restriction of
the induced map of symmetric algebras. -/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    M.symmetricPower n ⟶ N.symmetricPower n :=
  ofHom ((SymmetricAlgebra.map R f.hom).toLinearMap.restrict fun _ hx ↦
    TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule f.hom hx)

/-- The morphism induced on symmetric powers is the induced map of symmetric algebras. -/
@[simp]
lemma coe_map_apply {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) (x : M.symmetricPower n) :
    Subtype.val (map f n x) = SymmetricAlgebra.map R f.hom x.1 :=
  (rfl)

variable (R) in
/-- The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its `n`-th symmetric
power. -/
@[expose]
noncomputable def functor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.symmetricPower n
  map f := map f n
  map_id M := by
    ext x
    exact (coe_map_apply (𝟙 M) n x).trans (DFunLike.congr_fun (SymmetricAlgebra.map_id R) x.1)
  map_comp f g := by
    ext x
    exact (coe_map_apply (f ≫ g) n x).trans
      (DFunLike.congr_fun (SymmetricAlgebra.map_comp_map R f.hom g.hom) x.1).symm

@[simp]
lemma functor_obj (n : ℕ) (M : ModuleCat.{v} R) : (functor R n).obj M = M.symmetricPower n :=
  rfl

@[simp]
lemma functor_map (n : ℕ) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (functor R n).map f = map f n :=
  rfl

/-- The isomorphism `M.symmetricPower 0 ≅ ModuleCat.of R R`. -/
noncomputable def iso₀ (M : ModuleCat.{u} R) : M.symmetricPower 0 ≅ ↧R :=
  (TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R M).toModuleIso

/-- The inverse of `iso₀` sends a scalar to its image in the symmetric algebra. -/
@[simp]
lemma coe_iso₀_inv_apply (M : ModuleCat.{u} R) (r : R) :
    Subtype.val ((iso₀ M).inv r) = algebraMap R (SymmetricAlgebra R M) r :=
  TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleZeroEquiv_symm_apply R M r

/-- A degree-zero element is the image of the scalar `iso₀` assigns to it. -/
@[simp]
lemma algebraMap_iso₀_hom_apply (M : ModuleCat.{u} R) (x : M.symmetricPower 0) :
    algebraMap R (SymmetricAlgebra R M) ((iso₀ M).hom x) = x.1 :=
  TauCeti.SymmetricAlgebra.algebraMap_homogeneousSubmoduleZeroEquiv_apply R M x

@[reassoc (attr := simp)]
lemma iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 0 ≫ (iso₀ N).hom = (iso₀ M).hom := by
  rw [← cancel_epi (iso₀ M).inv, Iso.inv_hom_id]
  ext
  have h : map f 0 ((iso₀ M).inv 1) = (iso₀ N).inv 1 := by
    apply Subtype.ext
    rw [coe_map_apply, coe_iso₀_inv_apply, coe_iso₀_inv_apply, AlgHom.commutes]
  simp [h]

/-- The isomorphism `M.symmetricPower 1 ≅ M`. -/
noncomputable def iso₁ (M : ModuleCat.{u} R) : M.symmetricPower 1 ≅ M :=
  (TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv R M).toModuleIso

/-- The inverse of `iso₁` sends an element of the module to its generator in the symmetric
algebra. -/
@[simp]
lemma coe_iso₁_inv_apply (M : ModuleCat.{u} R) (m : M) :
    Subtype.val ((iso₁ M).inv m) = SymmetricAlgebra.ι R M m :=
  TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleOneEquiv_symm_apply R M m

/-- A degree-one element is the generator of the element `iso₁` assigns to it. -/
@[simp]
lemma ι_iso₁_hom_apply (M : ModuleCat.{u} R) (x : M.symmetricPower 1) :
    SymmetricAlgebra.ι R M ((iso₁ M).hom x) = x.1 :=
  TauCeti.SymmetricAlgebra.ι_homogeneousSubmoduleOneEquiv_apply R M x

@[reassoc (attr := simp)]
lemma iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 1 ≫ (iso₁ N).hom = (iso₁ M).hom ≫ f := by
  rw [← cancel_epi (iso₁ M).inv, Iso.inv_hom_id_assoc]
  ext m
  have h : map f 1 ((iso₁ M).inv m) = (iso₁ N).inv (f m) := by
    apply Subtype.ext
    rw [coe_map_apply, coe_iso₁_inv_apply, coe_iso₁_inv_apply, SymmetricAlgebra.map_apply_ι]
  simp [h]

end symmetricPower

end ModuleCat
