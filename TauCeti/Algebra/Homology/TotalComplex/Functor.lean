/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Homology.TotalComplex.AcyclicAssembly
public import TauCeti.Algebra.Homology.TotalComplex.Additive

/-!
# Total complexes of diagrams of double complexes

Mathlib's total complex functor `HomologicalComplex₂.totalFunctor` needs every double complex of
the shape to have a total complex, which in general asks for infinite coproducts. A diagram
`G : J ⥤ HomologicalComplex₂ C c₁ c₂` all of whose values have total complexes still has a
diagram of total complexes `G.totalComplex c₁₂ : J ⥤ HomologicalComplex C c₁₂`, with the maps
`HomologicalComplex₂.total.map (G.map f) c₁₂`. This is the case, for instance, of a diagram of
double complexes indexed by `ℤ × ℤ` whose columns vanish outside a fixed finite range
(`HomologicalComplex₂.hasTotal_of_isZero_X`), in a category with finite coproducts only.

A morphism of such diagrams induces a morphism of their diagrams of total complexes
(`CategoryTheory.NatTrans.totalComplex`), and a short complex of such diagrams which is split in
each bidegree at each object of `J` induces a short exact sequence of diagrams of total complexes
(`CategoryTheory.ShortComplex.shortExact_totalComplex`), objectwise the short exact sequence
`HomologicalComplex₂.totalShortComplex_shortExact`.

## Main definitions and results

* `CategoryTheory.Functor.totalComplex`: the diagram of total complexes of a diagram of double
  complexes.
* `CategoryTheory.NatTrans.totalComplex`: the morphism of diagrams of total complexes induced by a
  morphism of diagrams of double complexes.
* `CategoryTheory.ShortComplex.totalComplex`, `CategoryTheory.ShortComplex.shortExact_totalComplex`:
  the short complex of diagrams of total complexes of a short complex of diagrams of double
  complexes, short exact when the latter is split in each bidegree.
* `CategoryTheory.Functor.shiftIsoTotalComplexOfIsZero`: for a diagram of double complexes
  indexed by `ℤ × ℤ` concentrated in the column `c`, the diagram of total complexes is the diagram
  of the columns `c` shifted by `-c`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {J C : Type*} [Category* J] [Category* C] {I₁ I₂ I₁₂ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]

section Preadditive

variable [Preadditive C]

/-- The diagram of total complexes `j ↦ (G.obj j).total c₁₂` of a diagram `G` of double
complexes all of which have total complexes. -/
@[expose, simps]
noncomputable def Functor.totalComplex (G : J ⥤ HomologicalComplex₂ C c₁ c₂)
    [∀ j, (G.obj j).HasTotal c₁₂] : J ⥤ HomologicalComplex C c₁₂ where
  obj j := (G.obj j).total c₁₂
  map f := HomologicalComplex₂.total.map (G.map f) c₁₂
  map_id j := by simp
  map_comp f g := by simp [HomologicalComplex₂.total.map_comp]

/-- The morphism of diagrams of total complexes induced by a morphism `τ : G ⟶ G'` of diagrams of
double complexes all of which have total complexes. -/
@[expose, simps]
noncomputable def NatTrans.totalComplex {G G' : J ⥤ HomologicalComplex₂ C c₁ c₂}
    [∀ j, (G.obj j).HasTotal c₁₂] [∀ j, (G'.obj j).HasTotal c₁₂] (τ : G ⟶ G') :
    G.totalComplex c₁₂ ⟶ G'.totalComplex c₁₂ where
  app j := HomologicalComplex₂.total.map (τ.app j) c₁₂
  naturality _ _ f := (HomologicalComplex₂.total.map_comp _ _ c₁₂).symm.trans (by
    rw [τ.naturality]
    exact HomologicalComplex₂.total.map_comp _ _ c₁₂)

@[simp]
theorem NatTrans.totalComplex_id (G : J ⥤ HomologicalComplex₂ C c₁ c₂)
    [∀ j, (G.obj j).HasTotal c₁₂] : NatTrans.totalComplex c₁₂ (𝟙 G) = 𝟙 _ := by
  ext j : 2
  exact HomologicalComplex₂.total.map_id _ _

@[simp]
theorem NatTrans.totalComplex_comp {G G' G'' : J ⥤ HomologicalComplex₂ C c₁ c₂}
    [∀ j, (G.obj j).HasTotal c₁₂] [∀ j, (G'.obj j).HasTotal c₁₂] [∀ j, (G''.obj j).HasTotal c₁₂]
    (τ : G ⟶ G') (τ' : G' ⟶ G'') :
    NatTrans.totalComplex c₁₂ (τ ≫ τ') =
      NatTrans.totalComplex c₁₂ τ ≫ NatTrans.totalComplex c₁₂ τ' := by
  ext j : 2
  exact HomologicalComplex₂.total.map_comp (τ.app j) (τ'.app j) c₁₂

@[simp]
theorem NatTrans.totalComplex_zero (G G' : J ⥤ HomologicalComplex₂ C c₁ c₂)
    [∀ j, (G.obj j).HasTotal c₁₂] [∀ j, (G'.obj j).HasTotal c₁₂] :
    NatTrans.totalComplex c₁₂ (0 : G ⟶ G') = 0 := by
  ext j : 2
  exact HomologicalComplex₂.total.map_zero (G.obj j) (G'.obj j) c₁₂

/-- The short complex of diagrams of total complexes of a short complex `S` of diagrams of double
complexes all of which have total complexes. -/
noncomputable abbrev ShortComplex.totalComplex
    (S : ShortComplex (J ⥤ HomologicalComplex₂ C c₁ c₂)) [∀ j, (S.X₁.obj j).HasTotal c₁₂]
    [∀ j, (S.X₂.obj j).HasTotal c₁₂] [∀ j, (S.X₃.obj j).HasTotal c₁₂] :
    ShortComplex (J ⥤ HomologicalComplex C c₁₂) :=
  ShortComplex.mk (NatTrans.totalComplex c₁₂ S.f) (NatTrans.totalComplex c₁₂ S.g) (by
    rw [← NatTrans.totalComplex_comp, S.zero, NatTrans.totalComplex_zero])

section Int

variable (G : J ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [∀ j, (G.obj j).HasTotal (ComplexShape.up ℤ)]

/-- For a diagram of double complexes indexed by `ℤ × ℤ` and concentrated in the column `c`, the
diagram of total complexes is the diagram of the columns `c` shifted by `-c`: objectwise, the
isomorphism `HomologicalComplex₂.shiftIsoTotalOfIsZero`, the inclusion of the terms `(c, n - c)`. -/
noncomputable def Functor.shiftIsoTotalComplexOfIsZero (c : ℤ)
    (hG : ∀ j p, p ≠ c → IsZero ((G.obj j).X p)) :
    (G ⋙ HomologicalComplex.eval _ _ c) ⋙ shiftFunctor (CochainComplex C ℤ) (-c) ≅
      G.totalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun j ↦ (G.obj j).shiftIsoTotalOfIsZero c (hG j)) fun f ↦ by
    ext n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    simp only [HomologicalComplex₂.shiftIsoTotalOfIsZero_hom_f]
    -- the shift of `(G.map f).f c` is `(G.map f).f c` in degree `n + -c`
    exact (HomologicalComplex₂.ιTotal_map ..).symm

@[simp]
theorem Functor.shiftIsoTotalComplexOfIsZero_hom_app (c : ℤ)
    (hG : ∀ j p, p ≠ c → IsZero ((G.obj j).X p)) (j : J) :
    (G.shiftIsoTotalComplexOfIsZero c hG).hom.app j =
      ((G.obj j).shiftIsoTotalOfIsZero c (hG j)).hom :=
  (rfl)

end Int

end Preadditive

variable [Abelian C]

/-- A short complex of diagrams of double complexes which is split in each bidegree at each object
of `J` induces a short exact sequence of diagrams of total complexes. -/
theorem ShortComplex.shortExact_totalComplex
    (S : ShortComplex (J ⥤ HomologicalComplex₂ C c₁ c₂)) [∀ j, (S.X₁.obj j).HasTotal c₁₂]
    [∀ j, (S.X₂.obj j).HasTotal c₁₂] [∀ j, (S.X₃.obj j).HasTotal c₁₂]
    (σ : ∀ j i₁ i₂, (((S.map ((evaluation J _).obj j)).map (HomologicalComplex.eval _ c₁ i₁)).map
      (HomologicalComplex.eval C c₂ i₂)).Splitting) :
    (S.totalComplex c₁₂).ShortExact :=
  ShortComplex.shortExact_of_forall_evaluation _ fun j ↦ by
    -- the terms of `S` evaluated at `j` are the values at `j` of the terms of `S`
    have : (S.map ((evaluation J _).obj j)).X₁.HasTotal c₁₂ :=
      inferInstanceAs ((S.X₁.obj j).HasTotal c₁₂)
    have : (S.map ((evaluation J _).obj j)).X₂.HasTotal c₁₂ :=
      inferInstanceAs ((S.X₂.obj j).HasTotal c₁₂)
    have : (S.map ((evaluation J _).obj j)).X₃.HasTotal c₁₂ :=
      inferInstanceAs ((S.X₃.obj j).HasTotal c₁₂)
    -- by `NatTrans.totalComplex_app`, the maps of `S.totalComplex c₁₂` at `j` are `total.map` of
    -- those of `S` at `j`, so `(S.totalComplex c₁₂).map ((evaluation J _).obj j)` is by
    -- definition `totalShortComplex c₁₂ (S.map ((evaluation J _).obj j))`
    exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm))
      (HomologicalComplex₂.totalShortComplex_shortExact c₁₂ (S.map ((evaluation J _).obj j)) (σ j))

end CategoryTheory
