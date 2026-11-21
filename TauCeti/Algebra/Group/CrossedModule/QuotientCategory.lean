/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.CrossedModule.Basic
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map

/-!
# The quotient groupoid of a crossed module

The **quotient groupoid** of a crossed module `∂ : T → H` has the elements of `H` as objects; an
arrow `h ⟶ h'` is an element `x : T` with `∂ x * h = h'`, and arrows compose by multiplication
in `T`. It is the action groupoid of `T` acting on `H` by left translation through `∂`, built
here as Mathlib's `ActionCategory` on a type synonym `CrossedModule.TranslationSpace` of `H`
carrying that action.

Its isomorphism classes are the elements of the cokernel `H ⧸ ∂.range`, a group because the range
of `∂` is normal, and the automorphism group of every object is the kernel of `∂`, which is
central in `T`. This is the groupoid underlying the strict `2`-group of the crossed module, the
nonabelian form of the groupoid of a two-term complex: the kernel plays the role of `H⁻¹` and the
cokernel that of `H⁰`. A morphism of crossed modules induces a functor of quotient groupoids,
acting on objects by the homomorphism of targets and on arrows by the homomorphism of sources.

The arrows `h ⟶ h'` are labelled by elements of `T` (`CrossedModule.QuotientCategory.label`),
and arrows with the same label coincide; when `∂` is injective, as for a normal subgroup, there
is at most one arrow between two objects.

## Main definitions

* `TauCeti.CrossedModule.TranslationSpace`: the set `H` with `T` acting by `x • h = ∂ x * h`.
* `TauCeti.CrossedModule.QuotientCategory`: the quotient groupoid of a crossed module.
* `TauCeti.CrossedModule.QuotientCategory.objEquiv`: its objects are the elements of `H`.
* `TauCeti.CrossedModule.QuotientCategory.homEquiv`: its arrows `h ⟶ h'` are the elements
  `x : T` with `∂ x * h = h'`.
* `TauCeti.CrossedModule.QuotientCategory.isomorphismClassesEquiv`: its isomorphism classes are
  the cokernel `H ⧸ ∂.range`.
* `TauCeti.CrossedModule.QuotientCategory.autMulEquiv`: the automorphism group of each object is
  the kernel of `∂`.
* `TauCeti.CrossedModule.Hom.functor`: the functor induced by a morphism of crossed modules.

## Main results

* `TauCeti.CrossedModule.QuotientCategory.isIsomorphic_objEquiv_iff`: two objects are isomorphic
  exactly when they lie in the same coset of the range of `∂`.
* `TauCeti.CrossedModule.QuotientCategory.subsingleton_hom_of_injective`: for injective `∂` there
  is at most one arrow between two objects.
* `TauCeti.CrossedModule.Hom.functor_id`, `TauCeti.CrossedModule.Hom.functor_comp`: the induced
  functors are compatible with identities and composites.
* `TauCeti.CrossedModule.Hom.isomorphismClassesEquiv_functor_obj`,
  `TauCeti.CrossedModule.Hom.autMulEquiv_functor_mapAut`: on isomorphism classes and on
  automorphism groups, the induced functor is the induced homomorphism of cokernels and of
  kernels.

## References

* M. Kisin, *Mod p points on Shimura varieties of abelian type*, J. Amer. Math. Soc. 30 (2017),
  §3.2.1.
* J.-P. Labesse, *Cohomologie, stabilisation et changement de base*, Astérisque 257 (1999), §1.1.
-/

public section

open CategoryTheory MulAction

namespace TauCeti

namespace CrossedModule

variable {T H : Type*} [Group T] [Group H] (M : CrossedModule T H)

/-- The set `H`, on which `T` acts by left translation through the boundary,
`x • h = ∂ x * h`: the objects of the quotient groupoid of the crossed module. It is a type
synonym so that this action is not an instance on `H` itself. -/
@[expose]
def TranslationSpace (_M : CrossedModule T H) : Type _ :=
  H

namespace TranslationSpace

/-- The identification of `H` with the translation space of a crossed module. -/
def of : H ≃ M.TranslationSpace :=
  Equiv.refl H

/-- `T` acts on the translation space by left translation through the boundary. -/
instance : MulAction T M.TranslationSpace :=
  MulAction.compHom H M.boundary

@[simp]
theorem smul_of (x : T) (h : H) : x • of M h = of M (M.boundary x * h) :=
  (rfl)

variable {M}

/-- Two points of the translation space lie in the same orbit exactly when they lie in the same
coset of the range of the boundary. -/
theorem orbitRel_of_iff {h h' : H} :
    orbitRel T M.TranslationSpace (of M h) (of M h') ↔ h⁻¹ * h' ∈ M.boundary.range := by
  simp only [orbitRel_apply, mem_orbit_iff, smul_of, (of M).injective.eq_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨M.act h'⁻¹ x⁻¹, by rw [M.boundary_act]; simp [mul_assoc]⟩
  · rintro ⟨y, hy⟩
    exact ⟨M.act h y⁻¹, by rw [M.boundary_act]; simp [hy, mul_assoc]⟩

/-- An element of `T` fixes a point of the translation space exactly when it lies in the kernel
of the boundary. -/
theorem mem_stabilizer_iff {x : T} {h : M.TranslationSpace} :
    x ∈ stabilizer T h ↔ x ∈ M.boundary.ker := by
  obtain ⟨h, rfl⟩ := (of M).surjective h
  simp [MulAction.mem_stabilizer_iff, (of M).injective.eq_iff]

/-- The stabilizer of every point of the translation space is the kernel of the boundary. -/
theorem stabilizer_eq_ker (h : M.TranslationSpace) : stabilizer T h = M.boundary.ker :=
  Subgroup.ext fun _ ↦ mem_stabilizer_iff

/-- The map of translation spaces induced by a morphism of crossed modules, equivariant along
the homomorphism of sources. -/
def map {T' H' : Type*} [Group T'] [Group H'] {M' : CrossedModule T' H'} (f : Hom M M') :
    M.TranslationSpace →ₑ[f.left] M'.TranslationSpace where
  toFun h := of M' (f.right ((of M).symm h))
  map_smul' x h := by
    obtain ⟨h, rfl⟩ := (of M).surjective h
    simp [smul_of]

@[simp]
theorem map_of {T' H' : Type*} [Group T'] [Group H'] {M' : CrossedModule T' H'} (f : Hom M M')
    (h : H) : map f (of M h) = of M' (f.right h) :=
  (rfl)

end TranslationSpace

/-- The **quotient groupoid** of a crossed module `∂ : T → H`: the action groupoid of `T`
acting on `H` by left translation through `∂`. Its objects are the elements of `H`, and an arrow
`h ⟶ h'` is an element `x : T` with `∂ x * h = h'`. -/
abbrev QuotientCategory : Type _ :=
  ActionCategory T M.TranslationSpace

namespace QuotientCategory

/-- The identification of `H` with the objects of the quotient groupoid. -/
def objEquiv : H ≃ M.QuotientCategory :=
  (TranslationSpace.of M).trans (ActionCategory.objEquiv _ _)

/-- The object of the quotient groupoid at `h : H` is the object of the action groupoid at the
corresponding point of the translation space. -/
theorem objEquiv_apply (h : H) :
    objEquiv M h = ActionCategory.objEquiv T M.TranslationSpace (TranslationSpace.of M h) :=
  (rfl)

variable {M}

/-- The label `x : T` of an arrow of the quotient groupoid. -/
def label {X Y : M.QuotientCategory} (f : X ⟶ Y) : T :=
  f.hom

/-- An arrow of the quotient groupoid translates its source to its target by the boundary of its
label. -/
theorem boundary_label_mul {X Y : M.QuotientCategory} (f : X ⟶ Y) :
    M.boundary (label f) * (objEquiv M).symm X = (objEquiv M).symm Y := by
  obtain ⟨h, rfl⟩ := (objEquiv M).surjective X
  obtain ⟨h', rfl⟩ := (objEquiv M).surjective Y
  have hf := ActionCategory.hom_smul (x := TranslationSpace.of M h)
    (y := TranslationSpace.of M h') f
  rw [TranslationSpace.smul_of, (TranslationSpace.of M).injective.eq_iff] at hf
  simpa [label] using hf

/-- The arrow of the quotient groupoid with a given label. -/
def homMk {X Y : M.QuotientCategory} (x : T)
    (hx : M.boundary x * (objEquiv M).symm X = (objEquiv M).symm Y) : X ⟶ Y :=
  -- `Functor.Elements.homMk` asks for `x • X.back = Y.back` in the action category, and
  -- `objEquiv M` is `TranslationSpace.of M` followed by `ActionCategory.objEquiv`, so by
  -- `TranslationSpace.smul_of` this is the condition `hx` after unfolding these equivalences.
  Functor.Elements.homMk x <| by
    obtain ⟨h, rfl⟩ := (objEquiv M).surjective X
    obtain ⟨h', rfl⟩ := (objEquiv M).surjective Y
    change x • TranslationSpace.of M h = TranslationSpace.of M h'
    rw [TranslationSpace.smul_of]
    exact congrArg (TranslationSpace.of M) (by simpa using hx)

@[simp]
theorem label_homMk {X Y : M.QuotientCategory} (x : T)
    (hx : M.boundary x * (objEquiv M).symm X = (objEquiv M).symm Y) : label (homMk x hx) = x :=
  (rfl)

/-- Arrows of the quotient groupoid are determined by their labels. -/
@[ext]
theorem hom_ext {X Y : M.QuotientCategory} {f g : X ⟶ Y} (h : label f = label g) : f = g :=
  Functor.Elements.hom_ext h

@[simp]
theorem homMk_label {X Y : M.QuotientCategory} (f : X ⟶ Y) :
    homMk (label f) (boundary_label_mul f) = f :=
  hom_ext rfl

@[simp]
theorem label_id (X : M.QuotientCategory) : label (𝟙 X) = 1 :=
  ActionCategory.id_hom X

/-- The label of a composite is the product of the labels, the later arrow on the left. -/
@[simp]
theorem label_comp {X Y Z : M.QuotientCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    label (f ≫ g) = label g * label f :=
  ActionCategory.comp_hom f g

@[simp]
theorem label_inv {X Y : M.QuotientCategory} (f : X ⟶ Y) : label (inv f) = (label f)⁻¹ :=
  ActionCategory.inv_hom f

@[simp]
theorem label_eqToHom {X Y : M.QuotientCategory} (h : X = Y) : label (eqToHom h) = 1 :=
  ActionCategory.eqToHom_hom h

variable (M) in
/-- The arrows `h ⟶ h'` of the quotient groupoid are the elements `x : T` with
`∂ x * h = h'`. -/
def homEquiv (h h' : H) :
    (objEquiv M h ⟶ objEquiv M h') ≃ {x : T // M.boundary x * h = h'} where
  toFun f := ⟨label f, boundary_label_mul f⟩
  invFun x := homMk x.1 x.2
  left_inv f := homMk_label f
  right_inv _ := rfl

@[simp]
theorem coe_homEquiv_apply {h h' : H} (f : objEquiv M h ⟶ objEquiv M h') :
    (homEquiv M h h' f : T) = label f :=
  (rfl)

@[simp]
theorem label_homEquiv_symm_apply {h h' : H} (x : {x : T // M.boundary x * h = h'}) :
    label ((homEquiv M h h').symm x) = x :=
  (rfl)

/-- If the boundary is injective, for instance for the crossed module of a normal subgroup, there
is at most one arrow between two objects of the quotient groupoid. -/
theorem subsingleton_hom_of_injective (hM : Function.Injective M.boundary)
    (X Y : M.QuotientCategory) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g ↦ hom_ext <| hM <| mul_right_cancel <|
    (boundary_label_mul f).trans (boundary_label_mul g).symm⟩

instance (N : Subgroup H) [N.Normal] (X Y : (ofNormal N).QuotientCategory) :
    Subsingleton (X ⟶ Y) :=
  subsingleton_hom_of_injective (by simp) X Y

section IsomorphismClasses

/-- Two objects of the quotient groupoid are isomorphic exactly when they lie in the same coset
of the range of the boundary. -/
theorem isIsomorphic_objEquiv_iff {h h' : H} :
    IsIsomorphic (objEquiv M h) (objEquiv M h') ↔ h⁻¹ * h' ∈ M.boundary.range :=
  by rw [objEquiv_apply, objEquiv_apply, ActionCategory.isIsomorphic_iff_orbitRel,
    TranslationSpace.orbitRel_of_iff]

variable (M) in
/-- The isomorphism classes of the quotient groupoid of a crossed module are the elements of the
cokernel `H ⧸ ∂.range` of its boundary. -/
def isomorphismClassesEquiv :
    _root_.Quotient (isIsomorphicSetoid M.QuotientCategory) ≃ H ⧸ M.boundary.range :=
  (Quotient.congr (objEquiv M) fun _ _ ↦
    QuotientGroup.leftRel_apply.trans isIsomorphic_objEquiv_iff.symm).symm

@[simp]
theorem isomorphismClassesEquiv_mk (h : H) :
    isomorphismClassesEquiv M (_root_.Quotient.mk _ (objEquiv M h)) =
      (h : H ⧸ M.boundary.range) := by
  rw [isomorphismClassesEquiv, Equiv.symm_apply_eq, Quotient.congr_mk]

@[simp]
theorem isomorphismClassesEquiv_symm_mk (h : H) :
    (isomorphismClassesEquiv M).symm (h : H ⧸ M.boundary.range) =
      _root_.Quotient.mk _ (objEquiv M h) := by
  rw [Equiv.symm_apply_eq, isomorphismClassesEquiv_mk]

end IsomorphismClasses

section Aut

variable (M) in
/-- The automorphism group of an object of the quotient groupoid of a crossed module is the
kernel of the boundary, a commutative group (`CrossedModule.ker_le_center`). -/
def autMulEquiv (h : H) : Aut (objEquiv M h) ≃* M.boundary.ker :=
  (ActionCategory.stabilizerMulEquivAut T (TranslationSpace.of M h)).symm.trans
    (MulEquiv.subgroupCongr (TranslationSpace.stabilizer_eq_ker _))

@[simp]
theorem coe_autMulEquiv_apply (h : H) (e : Aut (objEquiv M h)) :
    (autMulEquiv M h e : T) = label e.asIso.hom :=
  ActionCategory.coe_stabilizerMulEquivAut_symm_apply (G := T) (TranslationSpace.of M h) e

@[simp]
theorem label_autMulEquiv_symm_apply (h : H) (x : M.boundary.ker) :
    label ((autMulEquiv M h).symm x).asIso.hom = x :=
  ActionCategory.stabilizerMulEquivAut_apply_hom_hom (G := T) (TranslationSpace.of M h) _

end Aut

end QuotientCategory

namespace Hom

open QuotientCategory

variable {M} {T' H' T'' H'' : Type*} [Group T'] [Group H'] [Group T''] [Group H'']
  {M' : CrossedModule T' H'} {M'' : CrossedModule T'' H''}

/-- The functor of quotient groupoids induced by a morphism of crossed modules: it sends the
object `h` to `f.right h` and the arrow labelled `x` to the arrow labelled `f.left x`. -/
def functor (f : Hom M M') : M.QuotientCategory ⥤ M'.QuotientCategory :=
  ActionCategory.map f.left (TranslationSpace.map f)

@[simp]
theorem functor_obj_objEquiv (f : Hom M M') (h : H) :
    f.functor.obj (objEquiv M h) = objEquiv M' (f.right h) := by
  rw [functor, objEquiv_apply, ActionCategory.map_obj, TranslationSpace.map_of, objEquiv_apply]

@[simp]
theorem label_functor_map (f : Hom M M') {X Y : M.QuotientCategory} (g : X ⟶ Y) :
    label (f.functor.map g) = f.left (label g) :=
  ActionCategory.map_map_hom _ _ g

/-- The identity morphism induces the identity functor. -/
@[simp]
theorem functor_id : (Hom.id M).functor = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun X ↦ by obtain ⟨h, rfl⟩ := (objEquiv M).surjective X; simp)
    fun _ _ _ ↦ by ext; simp

/-- The functor induced by a composite of morphisms is the composite of the induced functors. -/
theorem functor_comp (g : Hom M' M'') (f : Hom M M') :
    (g.comp f).functor = f.functor ⋙ g.functor :=
  CategoryTheory.Functor.ext (fun X ↦ by obtain ⟨h, rfl⟩ := (objEquiv M).surjective X; simp)
    fun _ _ _ ↦ by ext; simp

/-- On isomorphism classes, the functor induced by a morphism of crossed modules is the
homomorphism it induces on cokernels. -/
theorem isomorphismClassesEquiv_functor_obj (f : Hom M M') (X : M.QuotientCategory) :
    isomorphismClassesEquiv M' (_root_.Quotient.mk _ (f.functor.obj X)) =
      f.cokerMap (isomorphismClassesEquiv M (_root_.Quotient.mk _ X)) := by
  obtain ⟨h, rfl⟩ := (objEquiv M).surjective X
  simp

/-- On automorphism groups, the functor induced by a morphism of crossed modules is the
homomorphism it induces on kernels, after transporting along the identification of the image of
the object `h` with the object `f.right h`. -/
theorem autMulEquiv_functor_mapAut (f : Hom M M') (h : H) (e : Aut (objEquiv M h)) :
    autMulEquiv M' (f.right h)
        (Aut.autMulEquivOfIso (eqToIso (functor_obj_objEquiv f h)) (f.functor.mapAut _ e)) =
      f.kerMap (autMulEquiv M h e) := by
  ext
  simp [Aut.autMulEquivOfIso, Functor.mapAut]

end Hom

end CrossedModule

end TauCeti
