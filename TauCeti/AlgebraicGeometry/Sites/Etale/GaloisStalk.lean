/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.Sites.Etale.Point

/-!
# The Galois action on stalks of étale sheaves on a field

Let `K` be a field and `Ω` a separably closed field with an algebra map `K → Ω`, giving the
geometric point `x : Spec Ω ⟶ Spec K`. Every `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of
`Spec Ω` over `Spec K`, hence an endomorphism of the point `pointSmallEtale x` (by
`AlgebraicGeometry.Scheme.pointSmallEtaleHom`, from `TauCeti.AlgebraicGeometry.Sites.Etale.Point`),
hence an
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

The functor `galoisStalk` lands in `Action A Gal(Ω/K)`; together with
`isOpen_stabilizer_galoisStalk` it supplies the forward data of the classification of étale
sheaves on a field by discrete continuous `Gal(Ω/K)`-sets (SGA 4, Exposé VIII, §2).

## Main definitions

* `AlgebraicGeometry.Scheme.galoisStalk K Ω A`: the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf
  on `Spec K`, with its action of `Gal(Ω/K)`.
* `AlgebraicGeometry.Scheme.toGaloisStalk K Ω A F X t`: the germ at a lift `t` of the geometric
  point of sections over an étale `K`-scheme `X`, landing in `((galoisStalk K Ω A).obj F).V`, with
  `AlgebraicGeometry.Scheme.galoisStalkDesc` for morphisms out of the stalk.

## Main results

* `AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`: for an étale sheaf with values in a
  concrete category whose forgetful functor preserves filtered colimits (such as sets or modules),
  the stabilizer in `Gal(Ω/K)` of every element of the stalk is open.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme


section Galois

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

variable [IsSepClosed Ω] (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The endomorphism of the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K` induced by
`σ ∈ Gal(Ω/K)`, natural in the sheaf. -/
noncomputable def galoisStalkMap (σ : Gal(Ω/K)) :
    (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber (A := A) ⟶
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (pointSmallEtaleHom (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)))
      (Spec.map_algHom_comp_map_algebraMap σ))

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
    (Spec.map_algHom_comp_map_algebraMap σ) (Spec.map_algHom_comp_map_algebraMap τ)
    (by rw [Category.assoc, Spec.map_algHom_comp_map_algebraMap,
      Spec.map_algHom_comp_map_algebraMap])]
  exact congrArg _ (pointSmallEtaleHom_congr this _ _)

/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` of a section of an étale sheaf on `Spec K` to its
germ at the lift `Spec σ ≫ t`. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F =
      (pointSmallEtale _).toPresheafFiber X
        ((pointSmallEtaleHom _ (Spec.map_algHom_comp_map_algebraMap σ)).hom.app X t) F.obj := by
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
        ((pointSmallEtaleHom _ (Spec.map_algHom_comp_map_algebraMap σ)).hom.app X t) F.obj ≫ h :=
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
        ((pointSmallEtaleHom _ (Spec.map_algHom_comp_map_algebraMap σ)).hom.app X t) F.obj z :=
  (ConcreteCategory.comp_apply _ _ z).symm.trans
    congr($(toPresheafFiber_galoisStalkMap_app K Ω A σ F X t) z)

/-- **The Galois action on stalks of étale sheaves on a field.** The stalk at the geometric point
`Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K`, with the action of `Gal(Ω/K)` through the
automorphisms `Spec σ` of the geometric point. -/
@[expose]
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

/-- The underlying object of the stalk with its Galois action is the stalk. -/
theorem galoisStalk_obj_V (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) :
    ((galoisStalk K Ω A).obj F).V =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F :=
  (rfl)

/-- `σ ∈ Gal(Ω/K)` acts on the stalk by `galoisStalkMap K Ω A σ`. -/
theorem galoisStalk_obj_ρ_asHom (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (σ : Gal(Ω/K)) :
    (((galoisStalk K Ω A).obj F).ρ σ).asHom = (galoisStalkMap K Ω A σ).app F :=
  (rfl)

/-- The equivariant map of stalks induced by a morphism of sheaves is the map of stalks. -/
theorem galoisStalk_map_hom {F G : Sheaf (smallEtaleTopology (Spec (.of K))) A} (f : F ⟶ G) :
    ((galoisStalk K Ω A).map f).hom =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map f :=
  (rfl)

-- The germ API below restates `toPresheafFiber` and its lemmas with the stalk typed as
-- `((galoisStalk K Ω A).obj F).V`. The presheaf fiber that `toPresheafFiber` lands in agrees with
-- this object only after unfolding `galoisStalk` and `sheafFiber`, so `simp` and `rw` cannot
-- combine Mathlib's germ lemmas with the Galois action or with `galoisStalk.map`.

/-- The germ at a lift `t` of the geometric point of a section of an étale sheaf over an étale
`K`-scheme `X`, as an element of the stalk with its Galois action. -/
noncomputable def toGaloisStalk (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    F.obj.obj (op X) ⟶ ((galoisStalk K Ω A).obj F).V :=
  (pointSmallEtale _).toPresheafFiber X t F.obj

theorem toGaloisStalk_def (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    toGaloisStalk K Ω A F X t = (pointSmallEtale _).toPresheafFiber X t F.obj :=
  (rfl)

/-- Two morphisms out of the stalk agree when they agree on all germs. -/
@[ext]
theorem galoisStalk_hom_ext {F : Sheaf (smallEtaleTopology (Spec (.of K))) A} {T : A}
    {f g : ((galoisStalk K Ω A).obj F).V ⟶ T}
    (h : ∀ (X : (Spec (.of K)).Etale)
      (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      toGaloisStalk K Ω A F X t ≫ f = toGaloisStalk K Ω A F X t ≫ g) : f = g :=
  (pointSmallEtale _).presheafFiber_hom_ext h

section Desc

variable {K Ω A} {F : Sheaf (smallEtaleTopology (Spec (.of K))) A} {T : A}
  (φ : ∀ (X : (Spec (.of K)).Etale),
    (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X →
      (F.obj.obj (op X) ⟶ T))
  (hφ : ∀ ⦃X Y : (Spec (.of K)).Etale⦄ (f : X ⟶ Y)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
    F.obj.map f.op ≫ φ X t = φ Y ((pointSmallEtale _).fiber.map f t))

/-- The morphism out of the stalk given by a compatible family of morphisms out of the sections,
indexed by the lifts of the geometric point. -/
noncomputable def galoisStalkDesc : ((galoisStalk K Ω A).obj F).V ⟶ T :=
  (pointSmallEtale _).presheafFiberDesc φ hφ

theorem galoisStalkDesc_def :
    galoisStalkDesc φ hφ = (pointSmallEtale _).presheafFiberDesc φ hφ :=
  (rfl)

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toGaloisStalk_galoisStalkDesc (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    toGaloisStalk K Ω A F X t ≫ galoisStalkDesc φ hφ = φ X t :=
  (pointSmallEtale _).toPresheafFiber_presheafFiberDesc φ hφ X t

end Desc

/-- Germs are compatible with restriction along morphisms of étale `K`-schemes. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toGaloisStalk_w (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    {X Y : (Spec (.of K)).Etale} (f : X ⟶ Y)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    F.obj.map f.op ≫ toGaloisStalk K Ω A F X t =
      toGaloisStalk K Ω A F Y ((pointSmallEtale _).fiber.map f t) :=
  (pointSmallEtale _).toPresheafFiber_w f t F.obj

/-- Germs are natural in the sheaf. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toGaloisStalk_naturality {F G : Sheaf (smallEtaleTopology (Spec (.of K))) A}
    (g : F ⟶ G) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    toGaloisStalk K Ω A F X t ≫ ((galoisStalk K Ω A).map g).hom =
      g.hom.app (op X) ≫ toGaloisStalk K Ω A G X t :=
  (pointSmallEtale _).toPresheafFiber_naturality g.hom X t

/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` to the germ at the lift `Spec σ ≫ t`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toGaloisStalk_ρ (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (σ : Gal(Ω/K)) :
    toGaloisStalk K Ω A F X t ≫ (((galoisStalk K Ω A).obj F).ρ σ).asHom =
      toGaloisStalk K Ω A F X
        ((pointSmallEtaleHom _ (Spec.map_algHom_comp_map_algebraMap σ)).hom.app X t) :=
  toPresheafFiber_galoisStalkMap_app K Ω A σ F X t

section Concrete

variable {A : Type (v + 1)} [LargeCategory A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasColimitsOfSize.{u, u} A]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

omit [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)] in
/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` of a section to its germ at the lift `Spec σ ≫ t`,
for the action of `Gal(Ω/K)` on the elements of the stalk. -/
@[simp]
theorem smul_toGaloisStalk_apply (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (σ : Gal(Ω/K)) (z : ToType (F.obj.obj (op X))) :
    σ • toGaloisStalk K Ω A F X t z = toGaloisStalk K Ω A F X
      ((pointSmallEtaleHom _ (Spec.map_algHom_comp_map_algebraMap σ)).hom.app X t) z :=
  toGaloisStalk_ρ_apply K Ω A F X t σ z

/-- Every element of the stalk is the germ of a section over an étale `K`-scheme at a lift of the
geometric point. -/
theorem toGaloisStalk_jointly_surjective (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (p : ToType ((galoisStalk K Ω A).obj F).V) :
    ∃ (X : (Spec (.of K)).Etale)
      (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (z : ToType (F.obj.obj (op X))), toGaloisStalk K Ω A F X t z = p :=
  (pointSmallEtale _).toPresheafFiber_jointly_surjective (P := F.obj) p

/-- Two sections have the same germ at a lift `t` exactly when they agree after restriction to
some étale `K`-scheme over `X` with a lift of the geometric point mapping to `t`. -/
theorem toGaloisStalk_eq_iff (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (z₁ z₂ : ToType (F.obj.obj (op X))) :
    toGaloisStalk K Ω A F X t z₁ = toGaloisStalk K Ω A F X t z₂ ↔
      ∃ (Y : (Spec (.of K)).Etale) (f : Y ⟶ X)
        (y : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj Y),
        (pointSmallEtale _).fiber.map f y = t ∧ F.obj.map f.op z₁ = F.obj.map f.op z₂ :=
  (pointSmallEtale _).toPresheafFiber_eq_iff' X t z₁ z₂

/-- **Point stabilizers of the Galois action on stalks are open**: for an étale sheaf `F` on
`Spec K` with values in a concrete category whose forgetful functor preserves filtered colimits,
such as sets or modules, the stabilizer in `Gal(Ω/K)` of every element of
`(galoisStalk K Ω A).obj F` is open in the Krull topology. -/
theorem isOpen_stabilizer_galoisStalk (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (p : ToType ((galoisStalk K Ω A).obj F)) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) p : Set Gal(Ω/K)) := by
  -- `p` is the germ of a section `z` over an étale `K`-scheme `X` at a lift `t` of the geometric
  -- point, and `t` is fixed by the fixing subgroup of a finite extension `L` of `K`, which is open.
  obtain ⟨X, t, z, hp⟩ := toGaloisStalk_jointly_surjective K Ω F p
  have : Etale X.hom := X.prop
  obtain ⟨L, _, hL⟩ :=
    exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq K Ω X.hom t.left (Over.w t)
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup)
    (fun σ hσ ↦ MulAction.mem_stabilizer_iff.mpr ?_)
    (IntermediateField.fixingSubgroup_isOpen L)
  have ht : (pointSmallEtaleHom _ (Spec.map_algHom_comp_map_algebraMap σ)).hom.app X t = t :=
    Over.OverMorphism.ext ((pointSmallEtaleHom_hom_app_left _ _ X t).trans (hL σ hσ))
  -- `σ` acts on `p` through `galoisStalkMap`, which sends the germ at `t` to the germ at `t`.
  subst hp
  rw [smul_toGaloisStalk_apply, ht]

end Concrete

end Galois

end AlgebraicGeometry.Scheme
