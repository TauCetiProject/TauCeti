/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Basic

/-!
# The category of differential graded right modules

`DGRightModuleCat h` bundles internally graded right modules over the DG algebra `h`.
Its morphisms are the existing `DGRightModuleHom`: degree-preserving module maps commuting
with differentials, equivalently the closed degree-zero elements of the Hom complex.
The category is linear over the ground ring, and `DGRightModuleCat.isoMk` builds an isomorphism
from a linear equivalence preserving the grading and the differential. Forgetting the grading,
differential, and algebra action gives a faithful linear functor to modules over the ground ring.
A DG module is concentrated in degree zero (`DGRightModuleCat.IsConcentratedInDegreeZero`) when
its pieces of nonzero degree vanish; then its differential is zero, and homogeneous algebra
elements of nonzero degree and boundaries of the algebra act on it by zero.

This is the ordinary category of DG modules, before taking chain-homotopy classes or
inverting quasi-isomorphisms.

`forgetToRightModuleCat` retains the right algebra action and forgets the grading and
differential.

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

/-- Categorical composition agrees with composition of unbundled DG-module morphisms. -/
theorem comp_eq_comp (f : M ⟶ N) (g : N ⟶ P) : f ≫ g = g.comp f := by
  ext x
  exact (comp_apply f g x).trans (DGRightModuleHom.comp_apply g f x).symm

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
    apply hom_ext
    intro x
    simp
  comp_add M N P f g g' := by
    apply hom_ext
    intro x
    simp

instance : Linear R (DGRightModuleCat.{uR, uA, uM} h) where
  homModule M N := inferInstanceAs
    (Module R (DGRightModuleHom M.isDGRightModule N.isDGRightModule))
  smul_comp M N P r f g := by
    apply hom_ext
    intro x
    simp only [comp_apply, smul_apply]
    exact g.toLinearMap.map_smul_of_tower r (f x)
  comp_smul M N P f r g := by
    apply hom_ext
    intro x
    simp

/-- Build an isomorphism of DG right modules from an isomorphism of the underlying right modules
that preserves the homogeneous pieces and commutes with the differentials. -/
def isoMk (e : M ≃ₗ[Aᵐᵒᵖ] N) (he : ∀ q x, x ∈ M.grading q ↔ e x ∈ N.grading q)
    (hd : ∀ x, N.differential (e x) = e (M.differential x)) : M ≅ N where
  hom :=
    { toLinearMap := e.toLinearMap
      map_mem' := fun {q x} hx ↦ (he q x).1 hx
      map_d' := hd }
  inv :=
    { toLinearMap := e.symm.toLinearMap
      map_mem' := fun {q x} hx ↦ (he q _).2 (by rwa [LinearEquiv.coe_coe, e.apply_symm_apply])
      map_d' := fun x ↦ e.injective (by
        rw [LinearEquiv.coe_coe, ← hd, e.apply_symm_apply, e.apply_symm_apply]) }
  hom_inv_id := hom_ext fun x ↦ by
    rw [comp_apply, id_apply]
    exact e.symm_apply_apply x
  inv_hom_id := hom_ext fun x ↦ by
    rw [comp_apply, id_apply]
    exact e.apply_symm_apply x

/-- The isomorphism `isoMk e he hd` acts by `e`. -/
@[simp]
theorem isoMk_hom_apply (e : M ≃ₗ[Aᵐᵒᵖ] N)
    (he : ∀ q x, x ∈ M.grading q ↔ e x ∈ N.grading q)
    (hd : ∀ x, N.differential (e x) = e (M.differential x)) (x : M) :
    (isoMk e he hd).hom x = e x := (rfl)

/-- The inverse of `isoMk e he hd` acts by `e.symm`. -/
@[simp]
theorem isoMk_inv_apply (e : M ≃ₗ[Aᵐᵒᵖ] N)
    (he : ∀ q x, x ∈ M.grading q ↔ e x ∈ N.grading q)
    (hd : ∀ x, N.differential (e x) = e (M.differential x)) (x : N) :
    (isoMk e he hd).inv x = e.symm x := (rfl)

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

/-- Forget the grading and differential of a DG right module, retaining the right action. -/
-- Expose the carrier so scalar-restriction comparisons can use the underlying module type.
@[expose]
def forgetToRightModuleCat : DGRightModuleCat.{uR, uA, uM} h ⥤ ModuleCat.{uM} Aᵐᵒᵖ where
  obj M := ModuleCat.of Aᵐᵒᵖ M
  map f := ModuleCat.ofHom f.toLinearMap
  map_id M := ModuleCat.hom_ext (LinearMap.ext fun x ↦ id_apply M x)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x ↦ comp_apply f g x)

/-- Forgetting the grading and differential keeps the original right action. -/
@[simp]
theorem forgetToRightModuleCat_obj_smul (M : DGRightModuleCat.{uR, uA, uM} h) (a : Aᵐᵒᵖ)
    (x : (forgetToRightModuleCat (h := h)).obj M) :
    a • x = @SMul.smul Aᵐᵒᵖ M inferInstance a x := (rfl)

@[simp]
theorem forgetToRightModuleCat_map_hom (f : M ⟶ N) :
    ((forgetToRightModuleCat (h := h)).map f).hom = f.toLinearMap := (rfl)

instance : (forgetToRightModuleCat.{uR, uA, uM} (h := h)).Faithful where
  map_injective hfg := hom_ext fun x ↦ congrArg (fun f ↦ (ModuleCat.Hom.hom f) x) hfg

instance : (forgetToRightModuleCat.{uR, uA, uM} (h := h)).Additive where
  map_add := ModuleCat.hom_ext (LinearMap.ext fun x ↦ add_apply _ _ x)

section DegreeZero

open MulOpposite

/-- A DG right module is **concentrated in degree zero** when its homogeneous pieces of nonzero
degree vanish. -/
def IsConcentratedInDegreeZero (M : DGRightModuleCat.{uR, uA, uM} h) : Prop :=
  ∀ ⦃q : ℤ⦄, q ≠ 0 → M.grading q = ⊥

/-- Unfolding lemma for `DGRightModuleCat.IsConcentratedInDegreeZero`. -/
theorem isConcentratedInDegreeZero_iff {M : DGRightModuleCat.{uR, uA, uM} h} :
    M.IsConcentratedInDegreeZero ↔ ∀ ⦃q : ℤ⦄, q ≠ 0 → M.grading q = ⊥ :=
  Iff.rfl

namespace IsConcentratedInDegreeZero

/-- Every element of a DG module concentrated in degree zero has degree zero. -/
theorem mem_grading_zero (hM : M.IsConcentratedInDegreeZero) (x : M) : x ∈ M.grading 0 := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => exact zero_mem _
  | @homogeneous q y =>
    obtain ⟨y, hy⟩ := y
    by_cases hq : q = 0
    · exact hq ▸ hy
    · rw [hM hq, Submodule.mem_bot] at hy
      exact hy ▸ zero_mem _
  | add y z hy hz => exact add_mem hy hz

/-- In a DG module concentrated in degree zero, an element has degree `q` exactly when `q = 0` or
the element is zero. -/
@[simp]
theorem mem_grading_iff (hM : M.IsConcentratedInDegreeZero) {q : ℤ} {x : M} :
    x ∈ M.grading q ↔ q = 0 ∨ x = 0 := by
  by_cases hq : q = 0
  · subst hq
    simp [hM.mem_grading_zero x]
  · rw [hM hq, Submodule.mem_bot]
    simp [hq]

/-- The differential of a DG module concentrated in degree zero vanishes, as it raises the degree
by one. -/
@[simp]
theorem differential_eq_zero (hM : M.IsConcentratedInDegreeZero) : M.differential = 0 := by
  ext x
  have hx := M.isDGRightModule.isHomogeneous.map_mem (hM.mem_grading_zero x)
  rw [zero_add, hM one_ne_zero, Submodule.mem_bot] at hx
  exact hx

/-- On a DG module concentrated in degree zero, homogeneous elements of nonzero degree act by
zero. -/
theorem op_smul_eq_zero (hM : M.IsConcentratedInDegreeZero) {i : ℤ} (hi : i ≠ 0) {a : A}
    (ha : a ∈ 𝒜 i) (x : M) : op a • x = 0 := by
  have hax := SetLike.GradedSMul.smul_mem (A := (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    ((InternalGrading.op_mem_opposite_piece_iff _ _ _).2
      (by rwa [InternalGrading.ofDecomposition_piece])) (hM.mem_grading_zero x)
  rw [vadd_eq_add, add_zero, hM hi, Submodule.mem_bot] at hax
  exact hax

/-- On a DG module concentrated in degree zero, boundaries of the algebra act by zero: this is
the Leibniz rule with the zero differential. -/
theorem op_smul_d_eq_zero (hM : M.IsConcentratedInDegreeZero) (a : A) (x : M) :
    op (d a) • x = 0 := by
  have hl := M.isDGRightModule.leibniz (hM.mem_grading_zero x) a
  rw [hM.differential_eq_zero] at hl
  simpa using hl.symm

/-- Being concentrated in degree zero is invariant under isomorphism. -/
theorem of_iso (e : M ≅ N) (hM : M.IsConcentratedInDegreeZero) : N.IsConcentratedInDegreeZero :=
  fun _ hq ↦ (Submodule.eq_bot_iff _).2 fun x hx ↦ by
    have hex := GradedFunLike.map_mem e.inv hx
    rw [hM hq, Submodule.mem_bot] at hex
    rw [← id_apply N x, ← e.inv_hom_id, comp_apply, hex, map_zero]

end IsConcentratedInDegreeZero

/-- Being concentrated in degree zero is a property of DG modules closed under isomorphisms. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsConcentratedInDegreeZero (h := h)) :=
  ⟨fun e hM ↦ hM.of_iso e⟩

end DegreeZero

end DGRightModuleCat

end TauCeti
