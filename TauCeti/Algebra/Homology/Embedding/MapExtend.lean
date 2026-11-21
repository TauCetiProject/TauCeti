/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Functors commute with the extension of complexes

Let `e : c.Embedding c'` be an embedding of complex shapes and `F : C ⥤ D` a functor between
categories with zero objects which preserves zero morphisms. Extending a complex `K` of shape `c`
along `e` (`HomologicalComplex.extend`) puts zero objects in the degrees outside the image of
`e.f`. Applying `F` degreewise to `K.extend e` therefore gives `F(0)` in those degrees, which is
again a zero object, so the result is isomorphic to the extension of the image of `K` under `F`
(`HomologicalComplex.mapExtendIso`).

This lets statements about complexes indexed by `ℕ`, such as Čech complexes, be transported to
their extensions to `ℤ`, which is the indexing used for bounded complexes, compatibly with
operations applied degreewise such as extension of scalars.

## Main definitions

* `HomologicalComplex.mapExtendIso`: the isomorphism
  `F(K.extend e) ≅ (F K).extend e` of complexes of shape `c'`.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (K : HomologicalComplex C c) (e : c.Embedding c')

namespace extend

/-- The canonical isomorphism `F (X K i) ≅ X (F K) i` between the terms of the extension of `K`,
mapped by `F`, and those of the extension of the image of `K` under `F`. -/
def mapXIso (i : Option ι) :
    F.obj (X K i) ≅ X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (F.map_isZero (isZero_X _ rfl)) (isZero_X _ rfl)

/-- On a term `X K (some a)`, `mapXIso` is the identity of `F (K.X a)`, up to the identifications
`HomologicalComplex.extend.XIso`. -/
lemma mapXIso_hom_of_eq_some {i : Option ι} {a : ι} (hi : i = some a) :
    (mapXIso F K i).hom =
      F.map (XIso K hi).hom ≫ (XIso ((F.mapHomologicalComplex c).obj K) hi).inv := by
  subst hi
  rw [XIso, XIso, eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans]
  -- both sides are identities, of objects which agree up to unfolding the match defining `X`
  exact (eqToHom_refl _ _).symm

@[reassoc]
lemma mapXIso_hom_d (i j : Option ι) :
    (mapXIso F K i).hom ≫ d ((F.mapHomologicalComplex c).obj K) i j =
      F.map (d K i j) ≫ (mapXIso F K j).hom :=
  match i, j with
  | none, _ => by simp only [d_none_eq_zero, comp_zero, Functor.map_zero, zero_comp]
  -- `mapXIso` is `Iso.refl` on `some _`, and `d` of either extension at `some _, some _` is the
  -- differential of the complex, so both sides are `F.map (K.d _ _)` up to identities
  | some _, some _ => (Category.id_comp _).trans (Category.comp_id _).symm
  | some _, none => by simp only [d_none_eq_zero', comp_zero, Functor.map_zero, zero_comp]

end extend

/-- **Functors commute with extension of complexes.** For a functor `F` preserving zero
morphisms between categories with zero objects, applying `F` degreewise to the extension
`K.extend e` gives the extension of the image of `K` under `F`. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i' ↦ extend.mapXIso F K (e.r i'))
    fun i' j' _ ↦ extend.mapXIso_hom_d F K (e.r i') (e.r j')

/-- In a degree `e.f j`, the component of `mapExtendIso` is the identity of `F (K.X j)`, up to the
identifications `HomologicalComplex.extendXIso` of the terms of both extensions. -/
lemma mapExtendIso_hom_f {j : ι} {j' : ι'} (h : e.f j = j') :
    (mapExtendIso F K e).hom.f j' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  subst h
  exact extend.mapXIso_hom_of_eq_some F K (e.r_f j)

end HomologicalComplex
