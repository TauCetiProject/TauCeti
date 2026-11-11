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

for every coefficient category `A` with colimits. For sheaves of sets the action is continuous
for the discrete topology on the stalk and the Krull topology on `Gal(Ω/K)`: every element of the
stalk has an open stabilizer (`AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`). Indeed,
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
* `AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`: for an étale sheaf of sets, the
  stabilizer in `Gal(Ω/K)` of every element of the stalk is open.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Hom

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω'] [Field Ω''] [IsSepClosed Ω'']

/-- A morphism `a : Spec Ω' ⟶ Spec Ω` of geometric points of `S`, with `a ≫ s = s'`, induces a
morphism of points `pointSmallEtale s' ⟶ pointSmallEtale s` of the small étale site: a lift `t`
of `s` to an étale `S`-scheme goes to the lift `a ≫ t` of `s'`. -/
@[expose, simps]
noncomputable def pointSmallEtaleHom {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') :
    pointSmallEtale s' ⟶ pointSmallEtale s where
  hom := Functor.whiskerLeft (Etale.forget S)
    (coyoneda.map (Over.homMk a h : Over.mk s' ⟶ Over.mk s).op)

/-- The identity of a geometric point induces the identity of its point of the small étale
site. -/
@[simp]
theorem pointSmallEtaleHom_id (s : Spec (.of Ω) ⟶ S) (h : 𝟙 _ ≫ s = s) :
    pointSmallEtaleHom (𝟙 _) h = 𝟙 (pointSmallEtale s) := by
  have : (Over.homMk (𝟙 (Spec (.of Ω))) h : Over.mk s ⟶ Over.mk s) = 𝟙 _ := by cat_disch
  ext1
  rw [pointSmallEtaleHom_hom, this]
  simp only [op_id]
  rfl

/-- The morphism of points induced by a composite of geometric points is the composite of the
induced morphisms. -/
theorem pointSmallEtaleHom_comp {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    {s'' : Spec (.of Ω'') ⟶ S} (a : Spec (.of Ω'') ⟶ Spec (.of Ω'))
    (b : Spec (.of Ω') ⟶ Spec (.of Ω)) (ha : a ≫ s' = s'') (hb : b ≫ s = s')
    (hab : (a ≫ b) ≫ s = s'') :
    pointSmallEtaleHom (a ≫ b) hab = pointSmallEtaleHom a ha ≫ pointSmallEtaleHom b hb := by
  have : (Over.homMk (a ≫ b) hab : Over.mk s'' ⟶ Over.mk s) =
      (Over.homMk a ha : Over.mk s'' ⟶ Over.mk s') ≫
        (Over.homMk b hb : Over.mk s' ⟶ Over.mk s) := by cat_disch
  ext1
  rw [GrothendieckTopology.Point.comp_hom, pointSmallEtaleHom_hom, pointSmallEtaleHom_hom,
    pointSmallEtaleHom_hom, this]
  simp only [op_comp, Functor.map_comp, Functor.whiskerLeft_comp]
  rfl

/-- Equal morphisms of geometric points induce equal morphisms of points. -/
theorem pointSmallEtaleHom_congr {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    {a b : Spec (.of Ω') ⟶ Spec (.of Ω)} (hab : a = b) (ha : a ≫ s = s') (hb : b ≫ s = s') :
    pointSmallEtaleHom a ha = pointSmallEtaleHom b hb := by
  subst hab
  rfl

end Hom

section Galois

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- An element `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of the geometric point
`Spec Ω ⟶ Spec K` over `Spec K`. -/
theorem SpecMap_algEquiv_comp (σ : Gal(Ω/K)) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact σ.commutes r

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
    rw [← ht, Spec.map_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
      Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [Category.assoc, Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hK (c : (Spec (.of K)).residueField (f y)) :
      φ (f.residueFieldMap y c) ∈ Set.range (algebraMap K Ω) := by
    obtain ⟨d, rfl⟩ :=
      (Spec.residueFieldIso (.of K) (f y)).commRingCatIsoToRingEquiv.symm.surjective c
    obtain ⟨k, rfl⟩ := (Ideal.algEquivResidueFieldOfField (f y).asIdeal).surjective d
    refine ⟨k, ?_⟩
    have := congr($h k)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [Ideal.algEquivResidueFieldOfField_apply]
    exact this.symm
  -- The image of `φ` is an intermediate field of `Ω / K`.
  let L : IntermediateField K Ω := φ.hom.fieldRange.toIntermediateField fun k ↦ by
    have := congr($h k)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this ▸ RingHom.mem_fieldRange_self _ _
  -- It lies in the `K`-span of the images of generators of `κ(y)` over the residue field of
  -- `Spec K`, which exist because `f` is locally quasi-finite.
  algebraize [(f.residueFieldMap y).hom]
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin
    (R := (Spec (.of K)).residueField (f y)) (M := X.residueField y)
  have hLV : Subalgebra.toSubmodule L.toSubalgebra ≤
      Submodule.span K (Set.range fun i ↦ φ (g i)) := by
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ Submodule.span ((Spec (.of K)).residueField (f y)) (Set.range g) := hg ▸ trivial
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add b b' _ _ hb hb' =>
      rw [map_add]
      exact add_mem hb hb'
    | smul c b _ hb =>
      obtain ⟨k, hk⟩ := hK c
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hk, ← Algebra.smul_def]
      exact Submodule.smul_mem _ k hb
  have := FiniteDimensional.span_of_finite K (Set.finite_range fun i ↦ φ (g i))
  have : FiniteDimensional K (Subalgebra.toSubmodule L.toSubalgebra) :=
    Submodule.finiteDimensional_of_le hLV
  refine ⟨L, this, fun σ hσ ↦ ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ ⟨a, rfl⟩

variable [IsSepClosed Ω] (A : Type v) [Category.{u} A] [HasColimitsOfSize.{u, u} A]

/-- The endomorphism of the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K` induced by
`σ ∈ Gal(Ω/K)`, natural in the sheaf. -/
@[expose] noncomputable def galoisStalkMap (σ : Gal(Ω/K)) :
    (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber (A := A) ⟶
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (pointSmallEtaleHom (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)))
      (SpecMap_algEquiv_comp K Ω σ))

/-- The identity of `Gal(Ω/K)` acts trivially on stalks. -/
theorem galoisStalkMap_one : galoisStalkMap K Ω A 1 = 𝟙 _ := by
  have : Spec.map (CommRingCat.ofHom ((1 : Gal(Ω/K)) : Ω →+* Ω)) = 𝟙 _ := by
    rw [← Spec.map_id]
    rfl
  simp only [galoisStalkMap]
  rw [← GrothendieckTopology.Point.Hom.sheafFiber_id]
  congr 1
  rw [← pointSmallEtaleHom_id _ (Category.id_comp _)]
  exact pointSmallEtaleHom_congr this _ _

/-- The Galois action on stalks is a left action: `σ * τ` acts by `τ` followed by `σ`. -/
theorem galoisStalkMap_mul (σ τ : Gal(Ω/K)) :
    galoisStalkMap K Ω A (σ * τ) = galoisStalkMap K Ω A τ ≫ galoisStalkMap K Ω A σ := by
  have : Spec.map (CommRingCat.ofHom ((σ * τ : Gal(Ω/K)) : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω)) := by
    rw [← Spec.map_comp]
    rfl
  simp only [galoisStalkMap]
  rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, ← pointSmallEtaleHom_comp _ _
    (SpecMap_algEquiv_comp K Ω σ) (SpecMap_algEquiv_comp K Ω τ)
    (by rw [Category.assoc, SpecMap_algEquiv_comp, SpecMap_algEquiv_comp])]
  exact congrArg _ (pointSmallEtaleHom_congr this _ _)

/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` of a section of an étale sheaf on `Spec K` to its
germ at the lift `Spec σ ≫ t`. -/
@[reassoc]
theorem toPresheafFiber_galoisStalkMap_app (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F =
      (pointSmallEtale _).toPresheafFiber X
        ((pointSmallEtaleHom _ (SpecMap_algEquiv_comp K Ω σ)).hom.app X t) F.obj := by
  simp only [galoisStalkMap, Functor.whiskerLeft_app,
    GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

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
            simp [galoisStalkMap_one]
          map_mul' σ τ := by
            ext1
            simp [galoisStalkMap_mul] } }
  map f :=
    { hom := (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map f
      comm σ := ((galoisStalkMap K Ω A σ).naturality f).symm }

/-- **Stalks of étale sheaves of sets on `Spec K` are discrete continuous `Gal(Ω/K)`-sets**:
every element of the stalk at `Spec Ω ⟶ Spec K` has an open stabilizer in `Gal(Ω/K)`. An element
of the stalk is the germ of a section over an étale `K`-scheme `X` at a lift `t` of the geometric
point, and an open subgroup of `Gal(Ω/K)` fixes `t`
(`exists_finiteDimensional_forall_fixingSubgroup`). -/
theorem isOpen_stabilizer_galoisStalk (F : Sheaf (smallEtaleTopology (Spec (.of K))) (Type u))
    (p : ToType ((galoisStalk K Ω (Type u)).obj F)) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) p : Set Gal(Ω/K)) := by
  obtain ⟨X, t, z, rfl⟩ := (pointSmallEtale _).toPresheafFiber_jointly_surjective (P := F.obj) p
  have : Etale X.hom := X.prop
  obtain ⟨L, _, hL⟩ := exists_finiteDimensional_forall_fixingSubgroup K Ω X.hom t.left (Over.w t)
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) (fun σ hσ ↦ ?_)
    (IntermediateField.fixingSubgroup_isOpen L)
  have ht : (pointSmallEtaleHom _ (SpecMap_algEquiv_comp K Ω σ)).hom.app X t = t :=
    Over.OverMorphism.ext (hL σ hσ)
  exact (ConcreteCategory.congr_hom
    (toPresheafFiber_galoisStalkMap_app K Ω (Type u) σ F X t) z).trans (by rw [ht]; rfl)

end Galois

end AlgebraicGeometry.Scheme
