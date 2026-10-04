/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Kernels of group schemes

This file constructs the scheme-theoretic kernel of an arbitrary homomorphism of group schemes
over an arbitrary base. It is the categorical kernel in `Grp (Over S)`, equivalently the fibre of
the homomorphism over the identity section. No affineness, finiteness, or flatness hypothesis is
imposed.

Formation of this kernel commutes with arbitrary base change. Categorically, this follows because
pullback of schemes over a base preserves limits, limits of group objects are created by the
forgetful functor, and that functor reflects limits. The comparison isomorphism is Mathlib's
canonical `PreservesKernel.iso`; its compatibility with inclusions and maps between kernels is
recorded explicitly for downstream use.

## Main declarations

* `TauCeti.GroupScheme.isPullback_kernel`: a group-scheme kernel is the fibre over the identity.
* `TauCeti.GroupScheme.isPullback_kernel_scheme`: the corresponding square of underlying schemes
  is a pullback.
* `TauCeti.GroupScheme.kernelBaseChangeIso`: the canonical isomorphism from the base change of a
  kernel to the kernel of the base-changed homomorphism.
* `TauCeti.GroupScheme.kernelMap_comp_kernelBaseChangeIso_inv`: naturality of the comparison
  isomorphism with respect to commutative squares.

The categorical kernel and comparison constructions are provided by
`Mathlib.CategoryTheory.Limits.Shapes.Kernels` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

/-- Pullback of group schemes along an arbitrary base morphism preserves parallel-pair limits.
In particular, it preserves kernels. -/
noncomputable instance pullbackMapGrp_preservesLimitsOfShape_walkingParallelPair
    {S T : Scheme.{u}} (s : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (Over.pullback s).mapGrp := by
  have : PreservesLimitsOfShape WalkingParallelPair
      ((Over.pullback s).mapGrp ⋙ Grp.forget (Over T)) := by
    -- Forgetting the group structure after the lifted pullback functor is definitionally the
    -- same functor as first forgetting and then applying pullback in the over category.
    change PreservesLimitsOfShape WalkingParallelPair
      (Grp.forget (Over S) ⋙ Over.pullback s)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (Over.pullback s).mapGrp (Grp.forget (Over T))

/-- The canonical isomorphism from the base change of a scheme-theoretic kernel to the kernel of
the base-changed homomorphism. -/
noncomputable def kernelBaseChangeIso {S T : Scheme.{u}} (s : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) :
    (Over.pullback s).mapGrp.obj (kernel f) ≅
      kernel ((Over.pullback s).mapGrp.map f) :=
  PreservesKernel.iso (Over.pullback s).mapGrp f

/-- The forward base-change comparison intertwines the two kernel inclusions. -/
@[reassoc (attr := simp)]
lemma kernelBaseChangeIso_hom_comp_ι {S T : Scheme.{u}} (s : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) :
    (kernelBaseChangeIso s f).hom ≫
        kernel.ι ((Over.pullback s).mapGrp.map f) =
      (Over.pullback s).mapGrp.map (kernel.ι f) := by
  simp [kernelBaseChangeIso, PreservesKernel.iso_hom]

/-- The inverse base-change comparison intertwines the two kernel inclusions. -/
@[reassoc (attr := simp)]
lemma kernelBaseChangeIso_inv_comp_ι {S T : Scheme.{u}} (s : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) :
    (kernelBaseChangeIso s f).inv ≫
        (Over.pullback s).mapGrp.map (kernel.ι f) =
      kernel.ι ((Over.pullback s).mapGrp.map f) :=
  PreservesKernel.iso_inv_ι (Over.pullback s).mapGrp f

/-- The base-change comparison for kernels is natural in commutative squares of group-scheme
homomorphisms. -/
@[reassoc]
lemma kernelMap_comp_kernelBaseChangeIso_inv {S T : Scheme.{u}} (s : T ⟶ S)
    {G₁ H₁ G₂ H₂ : Grp (Over S)} (f₁ : G₁ ⟶ H₁) (f₂ : G₂ ⟶ H₂)
    (g : G₁ ⟶ G₂) (h : H₁ ⟶ H₂) (w : f₁ ≫ h = g ≫ f₂) :
    kernel.map ((Over.pullback s).mapGrp.map f₁) ((Over.pullback s).mapGrp.map f₂)
        ((Over.pullback s).mapGrp.map g) ((Over.pullback s).mapGrp.map h)
          (by rw [← Functor.map_comp, w, Functor.map_comp]) ≫
        (kernelBaseChangeIso s f₂).inv =
      (kernelBaseChangeIso s f₁).inv ≫
        (Over.pullback s).mapGrp.map (kernel.map f₁ f₂ g h w) :=
  kernel_map_comp_preserves_kernel_iso_inv (Over.pullback s).mapGrp f₁ f₂ g h w

/-- The categorical kernel of a group-scheme homomorphism is its fibre over the identity section.
The horizontal maps are the kernel inclusion and the identity section; the other map from the
kernel is the unique morphism to the trivial group scheme. -/
theorem isPullback_kernel {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H) :
    IsPullback (kernel.ι f)
      (0 : kernel f ⟶ Grp.trivial (Over S)) f
      (0 : Grp.trivial (Over S) ⟶ H) := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ ?_
  refine PullbackCone.IsLimit.mk (by simp)
    (fun t ↦ kernel.lift f t.fst (by simpa using t.condition)) ?_ ?_ ?_
  · intro t
    simp
  · intro t
    exact Subsingleton.elim _ _
  · intro t m hm _
    apply (cancel_mono (kernel.ι f)).1
    simpa using hm

/-- On underlying schemes, the scheme-theoretic kernel is the fibre of the homomorphism over its
identity section. -/
theorem isPullback_kernel_scheme {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H) :
    IsPullback (kernel.ι f).hom.hom.left
      (0 : kernel f ⟶ Grp.trivial (Over S)).hom.hom.left f.hom.hom.left
      (0 : Grp.trivial (Over S) ⟶ H).hom.hom.left := by
  exact ((isPullback_kernel f).map (Grp.forget _)).map (Over.forget _)

/-- The underlying-scheme isomorphism from the base change of a scheme-theoretic kernel to the
kernel of the base-changed homomorphism. -/
noncomputable def kernelBaseChangeSchemeIso {S T : Scheme.{u}} (s : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) :
    ((Over.pullback s).mapGrp.obj (kernel f)).X.left ≅
      (kernel ((Over.pullback s).mapGrp.map f)).X.left :=
  (Grp.forget (Over T) ⋙ Over.forget T).mapIso (kernelBaseChangeIso s f)

/-- The forward underlying-scheme comparison intertwines the two kernel inclusions. -/
@[reassoc (attr := simp)]
lemma kernelBaseChangeSchemeIso_hom_comp_ι {S T : Scheme.{u}} (s : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) :
    (kernelBaseChangeSchemeIso s f).hom ≫
        (kernel.ι ((Over.pullback s).mapGrp.map f)).hom.hom.left =
      ((Over.pullback s).mapGrp.map (kernel.ι f)).hom.hom.left := by
  exact congrArg (fun k ↦ k.hom.hom.left) (kernelBaseChangeIso_hom_comp_ι s f)

/-- The inverse underlying-scheme comparison intertwines the two kernel inclusions. -/
@[reassoc (attr := simp)]
lemma kernelBaseChangeSchemeIso_inv_comp_ι {S T : Scheme.{u}} (s : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) :
    (kernelBaseChangeSchemeIso s f).inv ≫
        (pullback.lift
          (pullback.fst (kernel f).X.hom s ≫ (kernel.ι f).hom.hom.left)
          (pullback.snd (kernel f).X.hom s)
          ((Category.assoc _ _ _).trans <|
            (congrArg (pullback.fst (kernel f).X.hom s ≫ ·)
              (kernel.ι f).hom.hom.w).trans pullback.condition) :
          ((Over.pullback s).mapGrp.obj (kernel f)).X.left ⟶
            ((Over.pullback s).mapGrp.obj G).X.left) =
      (kernel.ι ((Over.pullback s).mapGrp.map f)).hom.hom.left := by
  refine (Iso.inv_comp_eq _).2 ((kernelBaseChangeSchemeIso_hom_comp_ι s f).trans ?_).symm
  rw [Functor.mapGrp_map_hom_hom]
  exact Over.pullback_map_left s (kernel f).X

end TauCeti.GroupScheme
