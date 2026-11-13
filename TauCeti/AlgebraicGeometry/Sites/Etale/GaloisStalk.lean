/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# The Galois action on stalks of étale sheaves on a field

Let `S` be a scheme. A morphism `a : Spec Ω' ⟶ Spec Ω` of geometric points of `S` over `S`, that
is with `a ≫ s = s'`, induces a morphism of points `pointSmallEtale s' ⟶ pointSmallEtale s` of
the small étale site (`AlgebraicGeometry.Scheme.pointSmallEtaleHom`): a lift `t` of `s` to an
étale `S`-scheme goes to the lift `a ≫ t` of `s'`. This construction is functorial in `a`.

Let `K` be a field and `Ω` a separably closed field with an algebra map `K → Ω`, giving the
geometric point `x : Spec Ω ⟶ Spec K`. Every `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of
`Spec Ω` over `Spec K`, hence an endomorphism of the point `pointSmallEtale x`, hence an
endomorphism of the stalk at `x` of every étale sheaf on `Spec K`. This is a left action of
`Gal(Ω/K)`, natural in the sheaf, so the stalk at `x` is a functor
(`AlgebraicGeometry.Scheme.galoisStalk`)

`Sheaf (smallEtaleTopology (Spec K)) A ⥤ Action A Gal(Ω/K)`

for every coefficient category `A` with colimits. For concrete coefficients whose forgetful
functor preserves filtered colimits, such as sets or modules, the action is continuous for the
discrete topology on the stalk and the Krull topology on `Gal(Ω/K)`: every element of the stalk
has an open stabilizer (`AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`). Indeed,
an element of the stalk is represented by a section over an étale `K`-scheme `X` together with a
lift `t : Spec Ω ⟶ X` of `x`. The lift `t` is a point `y` of `X` with an embedding `κ(y) → Ω`,
and `κ(y)` is a finite extension of `K` because étale morphisms are locally quasi-finite. Every
`σ` fixing the image of `κ(y)` fixes `t`, and the elements of `Gal(Ω/K)` fixing a finite
extension of `K` in `Ω` form an open subgroup.

This is the functor from étale sheaves on `Spec K` to discrete continuous `Gal(Ω/K)`-sets in the
classification of étale sheaves on a field (SGA 4, Exposé VIII, §2).

## Main definitions

* `AlgebraicGeometry.Scheme.pointSmallEtaleHom a h`: the morphism of points of the small étale
  site induced by a morphism `a` of geometric points.
* `AlgebraicGeometry.Scheme.galoisStalk K Ω A`: the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf
  on `Spec K`, with its action of `Gal(Ω/K)`.

## Main results

* `AlgebraicGeometry.Scheme.pointSmallEtaleHom_id`,
  `AlgebraicGeometry.Scheme.pointSmallEtaleHom_comp`: functoriality in the geometric point.
* `AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`: for an étale sheaf of sets or
  modules, the stabilizer in `Gal(Ω/K)` of every element of the stalk is open.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Hom

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω'] [Field Ω''] [IsSepClosed Ω'']

/-- A morphism `a : Spec Ω' ⟶ Spec Ω` of geometric points of `S`, with `a ≫ s = s'`, induces a
morphism of points `pointSmallEtale s' ⟶ pointSmallEtale s` of the small étale site: a lift `t`
of `s` to an étale `S`-scheme goes to the lift `a ≫ t` of `s'`. -/
noncomputable def pointSmallEtaleHom {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') :
    pointSmallEtale s' ⟶ pointSmallEtale s where
  hom := Functor.whiskerLeft (Etale.forget S)
    (coyoneda.map (Over.homMk a h : Over.mk s' ⟶ Over.mk s).op)

/-- The morphism of points induced by `a` is precomposition with `Over.homMk a h` on the fiber
functors. -/
theorem pointSmallEtaleHom_hom {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') :
    (pointSmallEtaleHom a h).hom = Functor.whiskerLeft (Etale.forget S)
      (coyoneda.map (Over.homMk a h : Over.mk s' ⟶ Over.mk s).op) :=
  (rfl)

/-- The morphism of points induced by `a` sends a lift `t` to `a ≫ t`. -/
@[simp]
theorem pointSmallEtaleHom_hom_app_left {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') (X : S.Etale)
    (t : (pointSmallEtale s).fiber.obj X) :
    ((pointSmallEtaleHom a h).hom.app X t).left = a ≫ t.left :=
  (rfl)

/-- The identity of a geometric point induces the identity of its point of the small étale
site. -/
@[simp]
theorem pointSmallEtaleHom_id (s : Spec (.of Ω) ⟶ S) (h : 𝟙 _ ≫ s = s) :
    pointSmallEtaleHom (𝟙 _) h = 𝟙 (pointSmallEtale s) := by
  ext X : 3
  refine ConcreteCategory.hom_ext _ _ fun t ↦ Over.OverMorphism.ext ?_
  simp only [pointSmallEtaleHom_hom_app_left, GrothendieckTopology.Point.id_hom, NatTrans.id_app,
    ConcreteCategory.id_apply, Category.id_comp]

/-- The morphism of points induced by a composite of geometric points is the composite of the
induced morphisms. -/
theorem pointSmallEtaleHom_comp {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    {s'' : Spec (.of Ω'') ⟶ S} (a : Spec (.of Ω'') ⟶ Spec (.of Ω'))
    (b : Spec (.of Ω') ⟶ Spec (.of Ω)) (ha : a ≫ s' = s'') (hb : b ≫ s = s')
    (hab : (a ≫ b) ≫ s = s'') :
    pointSmallEtaleHom (a ≫ b) hab = pointSmallEtaleHom a ha ≫ pointSmallEtaleHom b hb := by
  ext X : 3
  refine ConcreteCategory.hom_ext _ _ fun t ↦ Over.OverMorphism.ext ?_
  simp only [pointSmallEtaleHom_hom_app_left, GrothendieckTopology.Point.comp_hom,
    NatTrans.comp_app, ConcreteCategory.comp_apply, Category.assoc]

/-- Equal morphisms of geometric points induce equal morphisms of points. -/
theorem pointSmallEtaleHom_congr {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    {a b : Spec (.of Ω') ⟶ Spec (.of Ω)} (hab : a = b) (ha : a ≫ s = s') (hb : b ≫ s = s') :
    pointSmallEtaleHom a ha = pointSmallEtaleHom b hb := by
  subst hab
  rfl

end Hom

/-- An `R`-algebra map `f : A → B` gives a morphism `Spec f : Spec B ⟶ Spec A` over `Spec R`. In
particular, every `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of the geometric point
`Spec Ω ⟶ Spec K` over `Spec K`. -/
@[reassoc (attr := simp)]
theorem SpecMap_algHom_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg _ (congrArg _ (RingHom.ext (AlgHomClass.commutes f)))

section Galois

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- **A point of a locally quasi-finite `K`-scheme with values in `Ω` is fixed by an open
subgroup of `Gal(Ω/K)`.** If `t : Spec Ω ⟶ X` lifts `Spec Ω ⟶ Spec K`, then `t` is a point `y` of
`X` with an embedding `φ : κ(y) → Ω`. The image of `φ` is a finite extension `L` of `K` in `Ω`,
because `κ(y)` is finite over the residue field of `Spec K`, and every `σ` fixing `L` fixes
`t`. -/
theorem exists_finiteDimensional_forall_fixingSubgroup {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (t : Spec (.of Ω) ⟶ X)
    (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
      ∀ σ ∈ L.fixingSubgroup, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t = t := by
  obtain ⟨⟨y, φ⟩, rfl⟩ := (X.SpecToEquivOfField Ω).symm.surjective t
  simp only [SpecToEquivOfField_symm_apply] at ht ⊢
  -- The embedding `φ` restricted to the residue field of `Spec K` at the image of `y` is the
  -- algebra map of `K`, after identifying that residue field with `K`.
  have := (f y).isPrime
  have h : CommRingCat.ofHom (algebraMap K (f y).asIdeal.ResidueField) ≫
      (Spec.residueFieldIso (.of K) (f y)).inv ≫ f.residueFieldMap y ≫ φ =
        CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    rw [← ht]
    simp only [Spec.map_comp, Category.assoc]
    rw [Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hφ (k : K) : φ (f.residueFieldMap y ((Spec.residueFieldIso (.of K) (f y)).inv
      (algebraMap K (f y).asIdeal.ResidueField k))) = algebraMap K Ω k := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using congr($h k)
  -- Make `κ(y)` a `K`-algebra through the residue field of `Spec K` at the image of `y`, which is
  -- finite over `K`. Then `κ(y)` is finite over `K`, because `f` is locally quasi-finite, and `φ`
  -- is a `K`-algebra map.
  let ψ : K →+* (Spec (.of K)).residueField (f y) :=
    (Spec.residueFieldIso (.of K) (f y)).inv.hom.comp (algebraMap K (f y).asIdeal.ResidueField)
  have hψ : Function.Surjective ψ :=
    (Spec.residueFieldIso (.of K) (f y)).commRingCatIsoToRingEquiv.symm.surjective.comp
      (Ideal.algEquivResidueFieldOfField (f y).asIdeal).surjective
  algebraize [ψ, (f.residueFieldMap y).hom, (f.residueFieldMap y).hom.comp ψ]
  have : Module.Finite K ((Spec (.of K)).residueField (f y)) :=
    Module.Finite.of_surjective (Algebra.linearMap K _) hψ
  have : Module.Finite K (X.residueField y) :=
    Module.Finite.trans ((Spec (.of K)).residueField (f y)) _
  let φ' : X.residueField y →ₐ[K] Ω := { φ.hom with commutes' := hφ }
  -- Every `σ` fixing the image of `φ` fixes `t`.
  refine ⟨φ'.fieldRange, φ'.toLinearMap.finiteDimensional_range, fun σ hσ ↦ ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ ⟨a, rfl⟩

variable [IsSepClosed Ω] (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The endomorphism of the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K` induced by
`σ ∈ Gal(Ω/K)`, natural in the sheaf. -/
noncomputable def galoisStalkMap (σ : Gal(Ω/K)) :
    (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber (A := A) ⟶
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (pointSmallEtaleHom (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)))
      (SpecMap_algHom_comp σ))

/-- The identity of `Gal(Ω/K)` acts trivially on stalks. -/
@[simp]
theorem galoisStalkMap_one : galoisStalkMap K Ω A 1 = 𝟙 _ := by
  have h1 : ((1 : Gal(Ω/K)) : Ω →+* Ω) = RingHom.id Ω := by
    ext x
    simp
  have : Spec.map (CommRingCat.ofHom ((1 : Gal(Ω/K)) : Ω →+* Ω)) = 𝟙 _ := by
    rw [h1, CommRingCat.ofHom_id, Spec.map_id]
  simp only [galoisStalkMap]
  rw [← GrothendieckTopology.Point.Hom.sheafFiber_id]
  congr 1
  rw [← pointSmallEtaleHom_id _ (Category.id_comp _)]
  exact pointSmallEtaleHom_congr this _ _

/-- The Galois action on stalks is a left action: `σ * τ` acts by `τ` followed by `σ`. -/
@[reassoc, simp]
theorem galoisStalkMap_mul (σ τ : Gal(Ω/K)) :
    galoisStalkMap K Ω A (σ * τ) = galoisStalkMap K Ω A τ ≫ galoisStalkMap K Ω A σ := by
  have h1 : ((σ * τ : Gal(Ω/K)) : Ω →+* Ω) = (σ : Ω →+* Ω).comp τ := by
    ext x
    simp [AlgEquiv.mul_apply]
  have : Spec.map (CommRingCat.ofHom ((σ * τ : Gal(Ω/K)) : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω)) := by
    rw [h1, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [galoisStalkMap]
  rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, ← pointSmallEtaleHom_comp _ _
    (SpecMap_algHom_comp σ) (SpecMap_algHom_comp τ)
    (by rw [Category.assoc, SpecMap_algHom_comp, SpecMap_algHom_comp])]
  exact congrArg _ (pointSmallEtaleHom_congr this _ _)

/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` of a section of an étale sheaf on `Spec K` to its
germ at the lift `Spec σ ≫ t`. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F =
      (pointSmallEtale _).toPresheafFiber X
        ((pointSmallEtaleHom _ (SpecMap_algHom_comp σ)).hom.app X t) F.obj := by
  simp only [galoisStalkMap, Functor.whiskerLeft_app,
    GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

-- `reassoc` and `elementwise` cannot generate these two forms: the germ lands in the presheaf
-- fiber, while `(galoisStalkMap K Ω A σ).app F` starts at the sheaf fiber, and the two objects
-- are only equal after unfolding `sheafFiber`, so `Category.assoc` does not rewrite the
-- composite and the generated lemmas keep it left-associated.

/-- Version of `toPresheafFiber_galoisStalkMap_app` for a right-associated composite. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app_assoc (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) {Z : A}
    (h : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F ⟶ Z) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F ≫ h =
      (pointSmallEtale _).toPresheafFiber X
        ((pointSmallEtaleHom _ (SpecMap_algHom_comp σ)).hom.app X t) F.obj ≫ h :=
  (Category.assoc _ _ _).symm.trans
    (eq_whisker (toPresheafFiber_galoisStalkMap_app K Ω A σ F X t) h)

/-- Version of `toPresheafFiber_galoisStalkMap_app` for elements of the germs, for concrete
coefficients. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app_apply {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (z : ToType (F.obj.obj (op X))) :
    (galoisStalkMap K Ω A σ).app F ((pointSmallEtale _).toPresheafFiber X t F.obj z) =
      (pointSmallEtale _).toPresheafFiber X
        ((pointSmallEtaleHom _ (SpecMap_algHom_comp σ)).hom.app X t) F.obj z :=
  (ConcreteCategory.comp_apply _ _ z).symm.trans
    congr($(toPresheafFiber_galoisStalkMap_app K Ω A σ F X t) z)

/-- **The Galois action on stalks of étale sheaves on a field.** The stalk at the geometric point
`Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K`, with the action of `Gal(Ω/K)` through the
automorphisms `Spec σ` of the geometric point. -/
@[expose, simps]
noncomputable def galoisStalk :
    Sheaf (smallEtaleTopology (Spec (.of K))) A ⥤ Action A Gal(Ω/K) where
  obj F :=
    { V := (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F
      ρ :=
        { toFun σ := .of ((galoisStalkMap K Ω A σ).app F)
          map_one' := by
            ext1
            simp
          map_mul' σ τ := by
            ext1
            simp } }
  map f :=
    { hom := (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map f
      comm σ := ((galoisStalkMap K Ω A σ).naturality f).symm }

section Concrete

variable {A : Type (v + 1)} [LargeCategory A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasColimitsOfSize.{u, u} A]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- **Stalks of étale sheaves on `Spec K` are discrete continuous `Gal(Ω/K)`-sets**: for a
concrete coefficient category whose forgetful functor preserves filtered colimits, such as sets or
modules, every element of the stalk at `Spec Ω ⟶ Spec K` has an open stabilizer in `Gal(Ω/K)`. An
element of the stalk is the germ of a section over an étale `K`-scheme `X` at a lift `t` of the
geometric point, and an open subgroup of `Gal(Ω/K)` fixes `t`
(`exists_finiteDimensional_forall_fixingSubgroup`). -/
theorem isOpen_stabilizer_galoisStalk (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (p : ToType ((galoisStalk K Ω A).obj F)) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) p : Set Gal(Ω/K)) := by
  obtain ⟨X, t, z, hp⟩ := (pointSmallEtale _).toPresheafFiber_jointly_surjective (P := F.obj) p
  have : Etale X.hom := X.prop
  obtain ⟨L, _, hL⟩ := exists_finiteDimensional_forall_fixingSubgroup K Ω X.hom t.left (Over.w t)
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup)
    (fun σ hσ ↦ MulAction.mem_stabilizer_iff.mpr ?_)
    (IntermediateField.fixingSubgroup_isOpen L)
  have ht : (pointSmallEtaleHom _ (SpecMap_algHom_comp σ)).hom.app X t = t :=
    Over.OverMorphism.ext ((pointSmallEtaleHom_hom_app_left _ _ X t).trans (hL σ hσ))
  -- `σ` acts on `p` through `galoisStalkMap`, which sends the germ at `t` to the germ at `t`.
  subst hp
  exact (toPresheafFiber_galoisStalkMap_app_apply K Ω A σ F X t z).trans (by rw [ht])

end Concrete

end Galois

end AlgebraicGeometry.Scheme
