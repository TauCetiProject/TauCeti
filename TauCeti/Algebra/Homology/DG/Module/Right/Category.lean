/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.Algebra.Homology.DG.Module.Right.HomComplex

/-!
# The category of differential graded right modules

`DGRightModuleCat h` bundles internally graded right modules over the DG algebra `h`.
Its morphisms are the existing `DGRightModuleHom`: degree-preserving module maps commuting
with differentials, equivalently the closed degree-zero elements of the Hom complex.
The category is linear over the ground ring. Forgetting the grading, differential, and
algebra action gives a faithful linear functor to modules over the ground ring.

This is the ordinary category of DG modules, before taking chain-homotopy classes or
inverting quasi-isomorphisms.

The bundling constructor `of` and the forgetful functor expose their bodies so that their
underlying carriers remain definitionally the supplied module types.

## References

* B. Keller, *Deriving DG categories*, Section 2.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- A bundled differential graded right module over the DG algebra `h`. -/
structure DGRightModuleCat (h : IsDGAlgebra 𝒜 d) where
  /-- The underlying module. -/
  carrier : Type uM
  [addCommGroup : AddCommGroup carrier]
  [moduleBase : Module R carrier]
  [moduleOp : Module Aᵐᵒᵖ carrier]
  [scalarTower : IsScalarTower R Aᵐᵒᵖ carrier]
  /-- The internal grading of the module. -/
  grading : ℤ → Submodule R carrier
  [decomposition : DirectSum.Decomposition grading]
  [gradedSMul : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece grading]
  /-- The module differential. -/
  differential : carrier →ₗ[R] carrier
  /-- The differential and action satisfy the DG right-module laws. -/
  isDGRightModule : IsDGRightModule h grading differential

namespace DGRightModuleCat

attribute [instance] addCommGroup moduleBase moduleOp scalarTower decomposition gradedSMul

variable {h : IsDGAlgebra 𝒜 d}

instance : CoeSort (DGRightModuleCat.{uR, uA, uM} h) (Type uM) := ⟨carrier⟩

/-- Bundle a differential graded right module with its existing structures. -/
abbrev of {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    {dM : M →ₗ[R] M} (hM : IsDGRightModule h ℳ dM) : DGRightModuleCat h where
  carrier := M
  grading := ℳ
  differential := dM
  isDGRightModule := hM

instance : Category (DGRightModuleCat.{uR, uA, uM} h) where
  Hom M N := DGRightModuleHom M.isDGRightModule N.isDGRightModule
  id M := DGRightModuleHom.id M.isDGRightModule
  comp f g := g.comp f
  id_comp f := DGRightModuleHom.comp_id f
  comp_id f := DGRightModuleHom.id_comp f
  assoc f g k := (DGRightModuleHom.comp_assoc k g f).symm

variable {M N P : DGRightModuleCat.{uR, uA, uM} h}

instance : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (DGRightModuleHom M.isDGRightModule N.isDGRightModule) M N)

/-- Morphisms of bundled DG right modules are equal when their values agree. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (hfg : ∀ x, f x = g x) : f = g :=
  DGRightModuleHom.ext hfg

@[simp]
theorem id_apply (M : DGRightModuleCat.{uR, uA, uM} h) (x : M) : (𝟙 M) x = x :=
  DGRightModuleHom.id_apply M.isDGRightModule x

@[simp]
theorem comp_apply (f : M ⟶ N) (g : N ⟶ P) (x : M) : (f ≫ g) x = g (f x) :=
  DGRightModuleHom.comp_apply g f x

instance : AddCommGroup (M ⟶ N) :=
  inferInstanceAs (AddCommGroup (DGRightModuleHom M.isDGRightModule N.isDGRightModule))

instance : Module R (M ⟶ N) :=
  inferInstanceAs (Module R (DGRightModuleHom M.isDGRightModule N.isDGRightModule))

@[simp]
theorem zero_apply (x : M) : (0 : M ⟶ N) x = 0 :=
  DGRightModuleHom.zero_apply x

@[simp]
theorem neg_apply (f : M ⟶ N) (x : M) : (-f) x = -f x :=
  DGRightModuleHom.neg_apply f x

@[simp]
theorem sub_apply (f g : M ⟶ N) (x : M) : (f - g) x = f x - g x :=
  DGRightModuleHom.sub_apply f g x

@[simp]
theorem add_apply (f g : M ⟶ N) (x : M) : (f + g) x = f x + g x :=
  DGRightModuleHom.add_apply f g x

@[simp]
theorem smul_apply (r : R) (f : M ⟶ N) (x : M) : (r • f) x = r • f x :=
  DGRightModuleHom.smul_apply r f x

instance : LinearMapClass (M ⟶ N) Aᵐᵒᵖ M N :=
  inferInstanceAs
    (LinearMapClass (DGRightModuleHom M.isDGRightModule N.isDGRightModule) Aᵐᵒᵖ M N)

instance : GradedFunLike (M ⟶ N) M.grading N.grading :=
  inferInstanceAs
    (GradedFunLike (DGRightModuleHom M.isDGRightModule N.isDGRightModule) M.grading N.grading)

/-- A morphism of bundled DG modules commutes with the differentials. -/
@[simp]
theorem map_d (f : M ⟶ N) (x : M) : N.differential (f x) = f (M.differential x) :=
  DGRightModuleHom.map_d f x

instance : Preadditive (DGRightModuleCat.{uR, uA, uM} h) where
  homGroup M N := inferInstanceAs
    (AddCommGroup (DGRightModuleHom M.isDGRightModule N.isDGRightModule))
  add_comp M N P f f' g := by
    -- Expose category composition so the unbundled morphism API applies.
    change g.comp (f + f') = g.comp f + g.comp f'
    apply DGRightModuleHom.ext
    intro x
    rw [DGRightModuleHom.comp_apply, DGRightModuleHom.add_apply f f',
      DGRightModuleHom.add_apply (g.comp f) (g.comp f'),
      DGRightModuleHom.comp_apply, DGRightModuleHom.comp_apply]
    exact map_add g _ _
  comp_add M N P f g g' := by
    -- Expose category composition so the unbundled morphism API applies.
    change (g + g').comp f = g.comp f + g'.comp f
    apply DGRightModuleHom.ext
    intro x
    rw [DGRightModuleHom.comp_apply, DGRightModuleHom.add_apply g g',
      DGRightModuleHom.add_apply (g.comp f) (g'.comp f),
      DGRightModuleHom.comp_apply, DGRightModuleHom.comp_apply]

instance : Linear R (DGRightModuleCat.{uR, uA, uM} h) where
  homModule M N := inferInstanceAs
    (Module R (DGRightModuleHom M.isDGRightModule N.isDGRightModule))
  smul_comp M N P r f g := by
    -- Expose category composition so the unbundled morphism API applies.
    change g.comp (r • f) = r • g.comp f
    apply DGRightModuleHom.ext
    intro x
    rw [DGRightModuleHom.comp_apply, DGRightModuleHom.smul_apply r f,
      DGRightModuleHom.smul_apply r (g.comp f), DGRightModuleHom.comp_apply]
    exact g.toLinearMap.map_smul_of_tower r (f x)
  comp_smul M N P f r g := by
    -- Expose category composition so the unbundled morphism API applies.
    change (r • g).comp f = r • g.comp f
    apply DGRightModuleHom.ext
    intro x
    rw [DGRightModuleHom.comp_apply, DGRightModuleHom.smul_apply r g,
      DGRightModuleHom.smul_apply r (g.comp f), DGRightModuleHom.comp_apply]

/-- Forget the grading, differential, and algebra action of a DG right module. -/
@[expose]
def forgetToModuleCat : DGRightModuleCat.{uR, uA, uM} h ⥤ ModuleCat.{uM} R where
  obj M := ModuleCat.of R M
  map f := ModuleCat.ofHom (f.toLinearMap.restrictScalars R)
  map_id M := by
    apply ModuleCat.hom_ext
    ext x
    exact DGRightModuleHom.id_apply M.isDGRightModule x
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    exact DGRightModuleHom.comp_apply g f x

@[simp]
theorem forgetToModuleCat_map_hom (f : M ⟶ N) :
    ((forgetToModuleCat (h := h)).map f).hom = f.toLinearMap.restrictScalars R := (rfl)

instance : (forgetToModuleCat.{uR, uA, uM} (h := h)).Faithful where
  map_injective {M N} f g hfg := by
    apply hom_ext
    intro x
    exact congrArg (fun k => (ModuleCat.Hom.hom k) x) hfg

instance : (forgetToModuleCat.{uR, uA, uM} (h := h)).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact add_apply f g x

instance : (forgetToModuleCat.{uR, uA, uM} (h := h)).Linear R where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact smul_apply r f x

end DGRightModuleCat

end TauCeti
