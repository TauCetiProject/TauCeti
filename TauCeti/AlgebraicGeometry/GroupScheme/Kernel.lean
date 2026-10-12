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
imposed. Its points with values in any `Z` over the base are the points of the source killed by the
homomorphism, as a group, and it is commutative when the source is.

Formation of this kernel commutes with arbitrary base change. Categorically, this follows because
pullback of schemes over a base preserves limits, limits of group objects are created by the
forgetful functor, and that functor reflects limits. The comparison isomorphism is Mathlib's
canonical `PreservesKernel.iso`; its compatibility with inclusions and maps between kernels is
recorded explicitly for downstream use.

## Main declarations

* `TauCeti.GroupScheme.isPullback_kernel`: a group-scheme kernel is the fibre over the identity.
* `TauCeti.GroupScheme.isPullback_kernel_scheme`: the corresponding square of underlying schemes
  is a pullback.
* `TauCeti.GroupScheme.kernelPointsMulEquiv`: the points of a kernel with values in `Z` are the
  kernel of the induced homomorphism on points with values in `Z`.
* `TauCeti.GroupScheme.isCommMonObj_kernel`: the kernel of a homomorphism out of a commutative
  group scheme is commutative.
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

/-! ### Points of a kernel -/

section Points

open MonObj

variable {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)

/-- A homomorphism of group schemes kills its kernel: the composite of the kernel inclusion and
the homomorphism is the unit point. -/
@[reassoc]
theorem kernel_ι_comp_hom : (kernel.ι f).hom.hom ≫ f.hom.hom = 1 :=
  congrArg (fun g ↦ g.hom.hom) (kernel.condition f)

/-- The categorical kernel of a homomorphism of group schemes, as a square of `Over S`: it is the
fibre of the homomorphism over the unit section. -/
theorem isPullback_kernel_hom :
    IsPullback (kernel.ι f).hom.hom (CartesianMonoidalCategory.toUnit _) f.hom.hom η[H.X] :=
  (isPullback_kernel f).map (Grp.forget _)

/-- The inclusion of the kernel of a homomorphism of group schemes is a monomorphism of
`Over S`. -/
instance mono_kernel_ι_hom : Mono (kernel.ι f).hom.hom :=
  inferInstanceAs (Mono ((Grp.forget _).map (kernel.ι f)))

variable {f} {Z : Over S}

/-- The point of the kernel of `f` given by a point `x` of `G` with values in `Z` which is killed
by `f`. -/
noncomputable def kernelLift (x : Z ⟶ G.X) (hx : x ≫ f.hom.hom = 1) : Z ⟶ (kernel f).X :=
  (isPullback_kernel_hom f).lift x (CartesianMonoidalCategory.toUnit Z) (by rw [hx, Hom.one_def])

/-- The point `kernelLift x hx` of the kernel maps to `x` in `G`. -/
@[reassoc (attr := simp)]
theorem kernelLift_ι (x : Z ⟶ G.X) (hx : x ≫ f.hom.hom = 1) :
    kernelLift x hx ≫ (kernel.ι f).hom.hom = x :=
  IsPullback.lift_fst _ _ _ _

/-- Two points of the kernel of `f` agree if their images in `G` do. -/
theorem kernel_hom_ext {y y' : Z ⟶ (kernel f).X}
    (h : y ≫ (kernel.ι f).hom.hom = y' ≫ (kernel.ι f).hom.hom) : y = y' :=
  (cancel_mono _).1 h

variable (f Z)

/-- **The points of a kernel.** The points of the kernel of a homomorphism `f : G ⟶ H` of group
schemes with values in `Z` form the kernel of the induced homomorphism from the points of `G` to
the points of `H` with values in `Z`. -/
noncomputable def kernelPointsMulEquiv :
    (Z ⟶ (kernel f).X) ≃* (IsMonHom.monoidHom f.hom.hom Z).ker where
  toFun y := ⟨y ≫ (kernel.ι f).hom.hom, by simp [kernel_ι_comp_hom]⟩
  invFun x := kernelLift x.1 (MonoidHom.mem_ker.1 x.2 :)
  left_inv y := kernel_hom_ext (kernelLift_ι _ _)
  right_inv x := Subtype.ext (kernelLift_ι _ _)
  map_mul' y y' := Subtype.ext (MonObj.mul_comp _ _ _)

/-- A point of the kernel corresponds to its image in `G`. -/
@[simp]
theorem coe_kernelPointsMulEquiv_apply (y : Z ⟶ (kernel f).X) :
    (kernelPointsMulEquiv f Z y : Z ⟶ G.X) = y ≫ (kernel.ι f).hom.hom :=
  (rfl)

/-- The point of the kernel corresponding to a point `x` of `G` killed by `f` maps to `x` in
`G`. -/
@[simp]
theorem kernelPointsMulEquiv_symm_apply_ι (x : (IsMonHom.monoidHom f.hom.hom Z).ker) :
    (kernelPointsMulEquiv f Z).symm x ≫ (kernel.ι f).hom.hom = x :=
  kernelLift_ι x.1 (MonoidHom.mem_ker.1 x.2 :)

/-- **The kernel of a homomorphism out of a commutative group scheme is commutative**: its group
law is the restriction of that of the source. -/
instance isCommMonObj_kernel [IsCommMonObj G.X] : IsCommMonObj (kernel f).X :=
  (isCommMonObj_iff_isMulCommutative _).2 fun _ ↦ ⟨⟨fun y y' ↦ kernel_hom_ext (by
    simp only [MonObj.mul_comp, mul_comm])⟩⟩

end Points

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
