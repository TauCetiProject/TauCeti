/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.AddBasepoint
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# Simplicial tensors and cotensors of pointed simplicial sets

An unpointed simplicial set acts on pointed simplicial sets after adjoining a disjoint
basepoint `K₊` (see `PointedSSet.addBasepoint`).  The tensor of `K` and `X` is `K₊ ∧ X`,
while the cotensor is the pointed mapping simplicial set `Map_*(K₊, X)`.  Their characteristic
hom-set equivalences identify both with maps from `K` to the underlying pointed mapping
simplicial set.

This supplies the tensors and cotensors for the simplicial enrichment of pointed simplicial
sets.  In particular, the construction uses the disjoint-basepoint functor and is distinct from
one-point compactification.

## Main definitions

* `PointedSSet.simplicialTensor`: the bifunctor `(K, X) ↦ K₊ ∧ X`.
* `PointedSSet.simplicialCotensor`: the bifunctor `(K, X) ↦ Map_*(K₊, X)`.
* `PointedSSet.simplicialTensorHomEquiv`: the tensor hom-set equivalence.
* `PointedSSet.homSimplicialCotensorEquiv`: the cotensor hom-set equivalence.

Both hom-set equivalences come with naturality lemmas in all three arguments.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory CategoryTheory.ConcreteCategory MonoidalCategory

namespace TauCeti.PointedSSet

/-- Tensoring a pointed simplicial set by an unpointed simplicial set:
`K ⊗ X = K₊ ∧ X`. -/
@[expose]
noncomputable def simplicialTensor : SSet.{u} ⥤ PointedSSet.{u} ⥤ PointedSSet.{u} :=
  addBasepoint ⋙ tensoringLeft PointedSSet.{u}

/-- Cotensoring a pointed simplicial set by an unpointed simplicial set:
`X^K = Map_*(K₊, X)`. -/
@[expose]
noncomputable def simplicialCotensor : SSet.{u}ᵒᵖ ⥤ PointedSSet.{u} ⥤ PointedSSet.{u} :=
  addBasepoint.op ⋙ MonoidalClosed.internalHom

@[simp]
lemma simplicialTensor_obj_obj (K : SSet.{u}) (X : PointedSSet.{u}) :
    (simplicialTensor.obj K).obj X = addBasepoint.obj K ⊗ X :=
  (rfl)

@[simp]
lemma simplicialCotensor_obj_obj (K : SSet.{u}ᵒᵖ) (X : PointedSSet.{u}) :
    (simplicialCotensor.obj K).obj X = (PointedSSet.ihom (addBasepoint.obj K.unop)).obj X :=
  (rfl)

/-- The tensor acts on a map of simplicial sets `g` by whiskering with `g₊`. -/
@[simp]
lemma simplicialTensor_map_app {K' K : SSet.{u}} (g : K' ⟶ K) (X : PointedSSet.{u}) :
    (simplicialTensor.map g).app X = addBasepoint.map g ▷ X :=
  (rfl)

/-- The tensor by `K` acts on based maps by whiskering with `K₊`. -/
@[simp]
lemma simplicialTensor_obj_map (K : SSet.{u}) {X' X : PointedSSet.{u}} (h : X' ⟶ X) :
    (simplicialTensor.obj K).map h = addBasepoint.obj K ◁ h :=
  (rfl)

/-- The cotensor acts on a map of simplicial sets `g` by precomposition with `g₊`. -/
@[simp]
lemma simplicialCotensor_map_app {K' K : SSet.{u}} (g : K' ⟶ K) (Y : PointedSSet.{u}) :
    (simplicialCotensor.map g.op).app Y = (MonoidalClosed.pre (addBasepoint.map g)).app Y :=
  (rfl)

/-- The cotensor by `K` acts on based maps by postcomposition. -/
@[simp]
lemma simplicialCotensor_obj_map (K : SSet.{u}ᵒᵖ) {Y Y' : PointedSSet.{u}} (g : Y ⟶ Y') :
    (simplicialCotensor.obj K).map g = (ihom (addBasepoint.obj K.unop)).map g :=
  (rfl)

/-- The tensor universal property, expressed using the underlying simplicial set of based maps. -/
noncomputable def simplicialTensorHomEquiv (K : SSet.{u}) (X Y : PointedSSet.{u}) :
    ((simplicialTensor.obj K).obj X ⟶ Y) ≃
      (K ⟶ ((PointedSSet.ihom X).obj Y).right) :=
  (((β_ (addBasepoint.obj K) X).homCongr (Iso.refl Y)).trans
    (PointedSSet.tensorHomEquiv X (addBasepoint.obj K) Y)).trans
      (addBasepointHomEquiv K ((PointedSSet.ihom X).obj Y))

/-- The cotensor universal property, expressed using the underlying simplicial set of based maps. -/
noncomputable def homSimplicialCotensorEquiv (K : SSet.{u}) (X Y : PointedSSet.{u}) :
    (X ⟶ (simplicialCotensor.obj (Opposite.op K)).obj Y) ≃
      (K ⟶ ((PointedSSet.ihom X).obj Y).right) :=
  (PointedSSet.tensorHomEquiv (addBasepoint.obj K) X Y).symm.trans
    (simplicialTensorHomEquiv K X Y)

/-- The tensor hom-set equivalence curries after braiding `K₊ ∧ X` to `X ∧ K₊`. -/
lemma simplicialTensorHomEquiv_apply {K : SSet.{u}} {X Y : PointedSSet.{u}}
    (f : addBasepoint.obj K ⊗ X ⟶ Y) :
    simplicialTensorHomEquiv K X Y f =
      addBasepointHomEquiv K _ (MonoidalClosed.curry ((β_ (addBasepoint.obj K) X).inv ≫ f)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, homEquiv_def]
  exact congrArg (fun k ↦ addBasepointHomEquiv K _ (tensorHomEquiv X _ Y k))
    (Category.comp_id ((β_ (addBasepoint.obj K) X).inv ≫ f)).symm

/-- The cotensor hom-set equivalence uncurries and then applies the tensor equivalence. -/
lemma homSimplicialCotensorEquiv_apply {K : SSet.{u}} {X Y : PointedSSet.{u}}
    (f : X ⟶ (ihom (addBasepoint.obj K)).obj Y) :
    homSimplicialCotensorEquiv K X Y f =
      simplicialTensorHomEquiv K X Y (MonoidalClosed.uncurry f) := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]
  -- Both sides are now the unfolded composite `Equiv.trans`.
  rfl

/-!
The naturality lemmas below are stated in `simp`-normal form, with `K₊ ∧ X` in place of
`(simplicialTensor.obj K).obj X` and `Map_*(K₊, Y)` in place of the cotensor.
-/

/- Their sources differ from the stated domains of the equivalences only definitionally, which
`rw` cannot see through. Each proof therefore starts from an explicitly typed instance of the
`_apply` characterization, and the closing `rfl` identifies the two definitionally equal
presentations. Only the lemmas whose left-hand side is an arbitrary composite are `simp`: the
`simpNF` linter rejects the others, whose left-hand sides those two lemmas already rewrite. -/

/-- The tensor hom-set equivalence is natural in the simplicial set `K`. -/
lemma simplicialTensorHomEquiv_whiskerRight_comp {K' K : SSet.{u}} (g : K' ⟶ K)
    {X Y : PointedSSet.{u}} (f : addBasepoint.obj K ⊗ X ⟶ Y) :
    simplicialTensorHomEquiv K' X Y (addBasepoint.map g ▷ X ≫ f) =
      g ≫ simplicialTensorHomEquiv K X Y f :=
  (simplicialTensorHomEquiv_apply (addBasepoint.map g ▷ X ≫ f)).trans <| by
    rw [← BraidedCategory.braiding_inv_naturality_right_assoc, MonoidalClosed.curry_natural_left,
      addBasepointHomEquiv_map_comp, simplicialTensorHomEquiv_apply]
    rfl

/-- The tensor hom-set equivalence is natural in the pointed simplicial set `X`. -/
lemma simplicialTensorHomEquiv_whiskerLeft_comp {K : SSet.{u}} {X' X Y : PointedSSet.{u}}
    (h : X' ⟶ X) (f : addBasepoint.obj K ⊗ X ⟶ Y) :
    simplicialTensorHomEquiv K X' Y (addBasepoint.obj K ◁ h ≫ f) =
      simplicialTensorHomEquiv K X Y f ≫ ((MonoidalClosed.pre h).app Y).right :=
  (simplicialTensorHomEquiv_apply (addBasepoint.obj K ◁ h ≫ f)).trans <| by
    rw [← BraidedCategory.braiding_inv_naturality_left_assoc, ← MonoidalClosed.curry_pre_app,
      addBasepointHomEquiv_comp, simplicialTensorHomEquiv_apply]
    rfl

/-- The tensor hom-set equivalence is natural in the target `Y`. -/
@[simp]
lemma simplicialTensorHomEquiv_comp {K : SSet.{u}} {X Y Y' : PointedSSet.{u}}
    (f : addBasepoint.obj K ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    simplicialTensorHomEquiv K X Y' (f ≫ g) =
      simplicialTensorHomEquiv K X Y f ≫ ((ihom X).map g).right :=
  (simplicialTensorHomEquiv_apply (f ≫ g)).trans <| by
    rw [← Category.assoc, MonoidalClosed.curry_natural_right, addBasepointHomEquiv_comp,
      simplicialTensorHomEquiv_apply]
    rfl

/-- The cotensor hom-set equivalence is natural in the simplicial set `K`. -/
lemma homSimplicialCotensorEquiv_comp_pre {K' K : SSet.{u}} (g : K' ⟶ K)
    {X Y : PointedSSet.{u}} (f : X ⟶ (ihom (addBasepoint.obj K)).obj Y) :
    homSimplicialCotensorEquiv K' X Y (f ≫ (MonoidalClosed.pre (addBasepoint.map g)).app Y) =
      g ≫ homSimplicialCotensorEquiv K X Y f :=
  (homSimplicialCotensorEquiv_apply
    (f ≫ (MonoidalClosed.pre (addBasepoint.map g)).app Y)).trans <| by
    rw [MonoidalClosed.uncurry_pre_app]
    exact (simplicialTensorHomEquiv_whiskerRight_comp g (MonoidalClosed.uncurry f)).trans
      (congrArg (g ≫ ·) (homSimplicialCotensorEquiv_apply f).symm)

/-- The cotensor hom-set equivalence is natural in the source `X`. -/
@[simp]
lemma homSimplicialCotensorEquiv_comp {K : SSet.{u}} {X' X Y : PointedSSet.{u}}
    (h : X' ⟶ X) (f : X ⟶ (ihom (addBasepoint.obj K)).obj Y) :
    homSimplicialCotensorEquiv K X' Y (h ≫ f) =
      homSimplicialCotensorEquiv K X Y f ≫ ((MonoidalClosed.pre h).app Y).right :=
  (homSimplicialCotensorEquiv_apply (h ≫ f)).trans <| by
    rw [MonoidalClosed.uncurry_natural_left]
    exact (simplicialTensorHomEquiv_whiskerLeft_comp h (MonoidalClosed.uncurry f)).trans
      (congrArg (· ≫ _) (homSimplicialCotensorEquiv_apply f).symm)

/-- The cotensor hom-set equivalence is natural in the pointed simplicial set `Y`. -/
lemma homSimplicialCotensorEquiv_comp_ihom_map {K : SSet.{u}} {X Y Y' : PointedSSet.{u}}
    (f : X ⟶ (ihom (addBasepoint.obj K)).obj Y) (g : Y ⟶ Y') :
    homSimplicialCotensorEquiv K X Y' (f ≫ (ihom (addBasepoint.obj K)).map g) =
      homSimplicialCotensorEquiv K X Y f ≫ ((ihom X).map g).right :=
  (homSimplicialCotensorEquiv_apply
    (f ≫ (ihom (addBasepoint.obj K)).map g)).trans <| by
    rw [MonoidalClosed.uncurry_natural_right]
    exact (simplicialTensorHomEquiv_comp (MonoidalClosed.uncurry f) g).trans
      (congrArg (· ≫ _) (homSimplicialCotensorEquiv_apply f).symm)

/-- For each simplicial set `K`, tensor by `K` is left adjoint to cotensor by `K`. -/
noncomputable def simplicialTensorCotensorAdjunction (K : SSet.{u}) :
    simplicialTensor.obj K ⊣ simplicialCotensor.obj (Opposite.op K) :=
  ihom.adjunction (addBasepoint.obj K)

end TauCeti.PointedSSet
