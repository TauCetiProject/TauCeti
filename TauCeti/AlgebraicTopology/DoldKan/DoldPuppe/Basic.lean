/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.SimplicialHomotopy
public import TauCeti.AlgebraicTopology.DoldKan.Const
import TauCeti.AlgebraicTopology.ExtraDegeneracy
import TauCeti.CategoryTheory.Functor.Const

/-!
# The Dold–Puppe functor

For an arbitrary (not necessarily additive) functor `F : C ⥤ D` from an idempotent-complete
preadditive category `C` with finite coproducts into a preadditive category `D`, the chain-level
**Dold–Puppe functor** `CategoryTheory.Functor.doldPuppeFunctor F` is
`Idempotents.DoldKan.Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D`,
packaged functorially in `F` as `CategoryTheory.doldPuppe C D`.

Because `Γ` carries chain homotopies to combinatorial simplicial homotopies
(`Idempotents.DoldKan.Γ.mapHomotopy`), levelwise whiskering by *any* functor preserves simplicial
homotopies, and `alternatingFaceMapComplex` returns to chain homotopies, `F.doldPuppeFunctor`
preserves chain homotopies and chain homotopy equivalences with no additivity or projectivity
hypotheses. The projective resolution-independence theorem
`CategoryTheory.Functor.quasiIso_doldPuppeFunctor_map_of_projective` lives in
`TauCeti.AlgebraicTopology.DoldKan.DoldPuppe.Projective`.

## Main definitions and results

* `doldPuppe`, `Functor.doldPuppeFunctor`:
  `Γ ⋙ (whiskering C D).obj F ⋙ alternatingFaceMapComplex D`, functorial in `F : C ⥤ D`.
* `Functor.doldPuppeMapHomotopy`, `Functor.doldPuppeMapHomotopyEquiv`: preservation of chain
  homotopies and homotopy equivalences for arbitrary functors `F`.
* `Functor.doldPuppeFunctorAdditiveHomotopyEquiv`: when `F` is additive,
  `F.doldPuppeFunctor.obj K` is chain homotopy equivalent to `(F.mapHomologicalComplex _).obj K`.
* `Functor.doldPuppeFunctorSingle₀HomotopyEquiv`: degree-zero comparison sending
  `(ChainComplex.single₀ C).obj X` to `(ChainComplex.single₀ D).obj (F.obj X)`.
* `Functor.doldPuppeFunctorConstHomotopyEquiv`: constant-functor comparison sending every `K`
  (including `K = 0`) to `(ChainComplex.single₀ D).obj B`.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §4 (especially 4.4–4.7).
* D. Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43, Springer-Verlag (1967), II.4.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994), §8.4.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.DoldKan Idempotents.DoldKan
open scoped Simplicial

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

variable (C D) in
/-- **The Dold–Puppe functor** on `C ⥤ D`: sends a functor `F : C ⥤ D` to
`Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D` and a natural
transformation `α : F ⟶ G` to the induced natural transformation between Dold–Puppe functors. -/
@[expose]
def doldPuppe : (C ⥤ D) ⥤ ChainComplex C ℕ ⥤ ChainComplex D ℕ :=
  SimplicialObject.whiskering C D ⋙
    (Functor.whiskeringRight (SimplicialObject C) (SimplicialObject D) (ChainComplex D ℕ)).obj
      (alternatingFaceMapComplex D) ⋙
    (Functor.whiskeringLeft (ChainComplex C ℕ) (SimplicialObject C) (ChainComplex D ℕ)).obj Γ

/-- **The Dold–Puppe chain-complex functor** associated to an arbitrary (not necessarily additive)
functor `F : C ⥤ D`: sends `K : ChainComplex C ℕ` to the alternating face map complex of `F` applied
levelwise to `Idempotents.DoldKan.Γ.obj K`. Evaluating `F.doldPuppeFunctor` on a projective
resolution computes the left derived functor of `F` in the sense of Dold and Puppe. -/
abbrev Functor.doldPuppeFunctor (F : C ⥤ D) : ChainComplex C ℕ ⥤ ChainComplex D ℕ :=
  (doldPuppe C D).obj F

/-- Functor-level characterization of `Functor.doldPuppeFunctor`. -/
theorem Functor.doldPuppeFunctor_eq (F : C ⥤ D) :
    F.doldPuppeFunctor =
      Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D := (rfl)

lemma Functor.doldPuppeFunctor_obj (F : C ⥤ D) (K : ChainComplex C ℕ) :
    F.doldPuppeFunctor.obj K =
      (alternatingFaceMapComplex D).obj
        (((SimplicialObject.whiskering C D).obj F).obj (Γ.obj K)) := (rfl)

/-- Morphism-level characterization of `Functor.doldPuppeFunctor`. -/
lemma Functor.doldPuppeFunctor_map (F : C ⥤ D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    F.doldPuppeFunctor.map φ =
      (alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ)) := (rfl)

@[simp]
lemma Functor.doldPuppeFunctor_obj_X (F : C ⥤ D) (K : ChainComplex C ℕ) (n : ℕ) :
    (F.doldPuppeFunctor.obj K).X n = F.obj ((Γ.obj K) _⦋n⦌) := (rfl)

@[simp]
lemma Functor.doldPuppeFunctor_obj_d (F : C ⥤ D) (K : ChainComplex C ℕ) (n : ℕ) :
    (F.doldPuppeFunctor.obj K).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((Γ.obj K).δ i) := by
  simp [Functor.doldPuppeFunctor, doldPuppe, AlternatingFaceMapComplex.objD, SimplicialObject.δ]

@[simp]
lemma Functor.doldPuppeFunctor_map_f (F : C ⥤ D) {K L : ChainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    (F.doldPuppeFunctor.map f).f n = F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) := (rfl)

/-- Component-level characterization of `(doldPuppe C D).map α`. -/
lemma doldPuppe_map_app {F G : C ⥤ D} (α : F ⟶ G) (K : ChainComplex C ℕ) :
    ((doldPuppe C D).map α).app K =
      (alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).map α).app (Γ.obj K)) := (rfl)

@[simp]
lemma doldPuppe_map_app_f {F G : C ⥤ D} (α : F ⟶ G) (K : ChainComplex C ℕ) (n : ℕ) :
    (((doldPuppe C D).map α).app K).f n = α.app ((Γ.obj K) _⦋n⦌) := (rfl)

/-- For *any* functor `F : C ⥤ D` (not necessarily additive), `F.doldPuppeFunctor` preserves chain
homotopies. -/
def Functor.doldPuppeMapHomotopy (F : C ⥤ D) {K L : ChainComplex C ℕ} {φ ψ : K ⟶ L}
    (H : Homotopy φ ψ) : Homotopy (F.doldPuppeFunctor.map φ) (F.doldPuppeFunctor.map ψ) :=
  ((Γ.mapHomotopy H).whiskerRight F).toChainHomotopy

/-- For *any* functor `F : C ⥤ D` (not necessarily additive), `F.doldPuppeFunctor` preserves chain
homotopy equivalences. -/
def Functor.doldPuppeMapHomotopyEquiv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv (F.doldPuppeFunctor.obj K) (F.doldPuppeFunctor.obj L) :=
  ((Γ.mapHomotopyEquiv e).whiskerRight F).toChainHomotopyEquiv

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_hom (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).hom = F.doldPuppeFunctor.map e.hom := by
  rw [Functor.doldPuppeFunctor_map]
  dsimp only [Functor.doldPuppeMapHomotopyEquiv]
  simp
  rfl

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_inv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).inv = F.doldPuppeFunctor.map e.inv := by
  rw [Functor.doldPuppeFunctor_map]
  dsimp only [Functor.doldPuppeMapHomotopyEquiv]
  simp
  rfl

/-- **Agreement with the classical additive derived functor** (Dold–Puppe, Satz 4.7): when
`F : C ⥤ D` is additive, `F.doldPuppeFunctor.obj K` is canonically chain homotopy equivalent to
`(F.mapHomologicalComplex (.down ℕ)).obj K` for every chain complex `K`. -/
def Functor.doldPuppeFunctorAdditiveHomotopyEquiv (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) :
    HomotopyEquiv (F.doldPuppeFunctor.obj K) ((F.mapHomologicalComplex (.down ℕ)).obj K) :=
  (HomotopyEquiv.ofIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.app (Γ.obj K))).trans
    ((F.mapHomotopyEquiv (homotopyEquivNAlternatingFaceMapComplex (Γ.obj K)).symm).trans
      (HomotopyEquiv.ofIso
        ((F.mapHomologicalComplex (.down ℕ)).mapIso ((η (C := C)).app K))))

@[simp]
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) :
    (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj K) ≫
        (F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj K)) ≫
          (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).hom.app K) := by
  dsimp only [Functor.doldPuppeFunctorAdditiveHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso]
  rw [Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Functor.mapHomotopyEquiv_hom,
    HomotopyEquiv.symm_hom, homotopyEquivNAlternatingFaceMapComplex_inv]

@[simp]
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) :
    (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv =
      (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app K) ≫
        (F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj K)) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K) := by
  dsimp only [Functor.doldPuppeFunctorAdditiveHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso]
  rw [Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Functor.mapHomotopyEquiv_inv,
    HomotopyEquiv.symm_inv, homotopyEquivNAlternatingFaceMapComplex_hom, Category.assoc]

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `K`. -/
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    F.doldPuppeFunctor.map φ ≫ (F.doldPuppeFunctorAdditiveHomotopyEquiv L).hom =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom ≫
        (F.mapHomologicalComplex (.down ℕ)).map φ := by
  have hsq1 : CommSq
      ((alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ)))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj K))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj L))
      ((F.mapHomologicalComplex (.down ℕ)).map ((alternatingFaceMapComplex C).map (Γ.map φ))) :=
    ⟨(alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.hom.naturality (Γ.map φ)⟩
  have hsq2 : CommSq
      ((F.mapHomologicalComplex (.down ℕ)).map ((alternatingFaceMapComplex C).map (Γ.map φ)))
      ((F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj K)) ≫
        (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).hom.app K))
      ((F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj L)) ≫
        (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).hom.app L))
      ((F.mapHomologicalComplex (.down ℕ)).map φ) :=
    CommSq.vert_comp
      ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨PInftyToN.naturality (Γ.map φ)⟩)
      ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨(η (C := C)).hom.naturality φ⟩)
  have hsq := CommSq.vert_comp hsq1 hsq2
  simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom]
  exact hsq.w

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `K`. -/
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (.down ℕ)).map φ ≫ (F.doldPuppeFunctorAdditiveHomotopyEquiv L).inv =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv ≫ F.doldPuppeFunctor.map φ := by
  have hsq1 : CommSq
      ((F.mapHomologicalComplex (.down ℕ)).map φ)
      ((F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app K))
      ((F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app L))
      ((F.mapHomologicalComplex (.down ℕ)).map ((Γ ⋙ N).map φ)) :=
    (F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨(η (C := C)).inv.naturality φ⟩
  have hsq2 : CommSq
      ((F.mapHomologicalComplex (.down ℕ)).map ((Γ ⋙ N).map φ))
      ((F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj K)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K))
      ((F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj L)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj L))
      ((alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ))) :=
    CommSq.vert_comp
      ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨inclusionN.naturality (Γ.map φ)⟩)
      ⟨(alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.inv.naturality (Γ.map φ)⟩
  have hsq := CommSq.vert_comp hsq1 hsq2
  simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv]
  exact hsq.w

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `F`. -/
lemma NatTrans.doldPuppeFunctorAdditiveHomotopyEquiv_hom_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (K : ChainComplex C ℕ) :
    ((doldPuppe C D).map α).app K ≫ (G.doldPuppeFunctorAdditiveHomotopyEquiv K).hom =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom ≫
        (α.mapHomologicalComplex (.down ℕ)).app K := by
  have hsq1 : CommSq
      ((alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).map α).app (Γ.obj K)))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj K))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso G).inv.app (Γ.obj K))
      ((α.mapHomologicalComplex (.down ℕ)).app ((alternatingFaceMapComplex C).obj (Γ.obj K))) :=
    ⟨by
      ext n
      simp [alternatingFaceMapComplexCompMapHomologicalComplexIso_inv_app_f]⟩
  have hsq2 : CommSq
      ((α.mapHomologicalComplex (.down ℕ)).app ((alternatingFaceMapComplex C).obj (Γ.obj K)))
      ((F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj K)) ≫
        (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).hom.app K))
      ((G.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj K)) ≫
        (G.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).hom.app K))
      ((α.mapHomologicalComplex (.down ℕ)).app K) :=
    CommSq.vert_comp
      ⟨((α.mapHomologicalComplex (.down ℕ)).naturality (PInftyToN.app (Γ.obj K))).symm⟩
      ⟨((α.mapHomologicalComplex (.down ℕ)).naturality ((η (C := C)).hom.app K)).symm⟩
  have hsq := CommSq.vert_comp hsq1 hsq2
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom]
  exact hsq.w

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `F`. -/
lemma NatTrans.doldPuppeFunctorAdditiveHomotopyEquiv_inv_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (K : ChainComplex C ℕ) :
    (α.mapHomologicalComplex (.down ℕ)).app K ≫
        (G.doldPuppeFunctorAdditiveHomotopyEquiv K).inv =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv ≫
        ((doldPuppe C D).map α).app K := by
  have hsq1 : CommSq
      ((α.mapHomologicalComplex (.down ℕ)).app K)
      ((F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app K))
      ((G.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app K))
      ((α.mapHomologicalComplex (.down ℕ)).app ((Γ ⋙ N).obj K)) :=
    ⟨((α.mapHomologicalComplex (.down ℕ)).naturality ((η (C := C)).inv.app K)).symm⟩
  have hsq2 : CommSq
      ((α.mapHomologicalComplex (.down ℕ)).app ((Γ ⋙ N).obj K))
      ((F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj K)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K))
      ((G.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj K)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (Γ.obj K))
      ((alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).map α).app (Γ.obj K))) :=
    CommSq.vert_comp
      ⟨((α.mapHomologicalComplex (.down ℕ)).naturality (inclusionN.app (Γ.obj K))).symm⟩
      ⟨by
        ext n
        simp [alternatingFaceMapComplexCompMapHomologicalComplexIso_hom_app_f]⟩
  have hsq := CommSq.vert_comp hsq1 hsq2
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv]
  exact hsq.w

/-- **Degree-zero law**: for any object `X : C` and any functor `F : C ⥤ D` into a preadditive
category with a zero object, `F.doldPuppeFunctor.obj ((ChainComplex.single₀ C).obj X)` is
canonically chain homotopy equivalent to `(ChainComplex.single₀ D).obj (F.obj X)`. In particular,
when `X` is projective, `(ChainComplex.single₀ C).obj X` is a projective resolution of `X`, so the
derived functor of `F` recovers `F.obj X` concentrated in degree `0`. -/
def Functor.doldPuppeFunctorSingle₀HomotopyEquiv [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) (X : C) :
    HomotopyEquiv (F.doldPuppeFunctor.obj ((ChainComplex.single₀ C).obj X))
      ((ChainComplex.single₀ D).obj (F.obj X)) :=
  let isoSimp : ((SimplicialObject.whiskering C D).obj F).obj
        (Γ.obj ((ChainComplex.single₀ C).obj X)) ≅ (SimplicialObject.const D).obj (F.obj X) :=
    ((SimplicialObject.whiskering C D).obj F).mapIso (Γ.single₀Iso.app X) ≪≫
      Functor.constComp _ X F
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso isoSimp)).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj X)).homotopyEquiv

@[simp]
lemma Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) (X : C) :
    (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom =
      (alternatingFaceMapComplex D).map
          (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.hom.app X) F) ≫
        (alternatingFaceMapComplex D).map (Functor.constComp _ X F).hom ≫
          AlgebraicTopology.AlternatingFaceMapComplex.ε.app
            (SimplicialObject.Augmented.const.obj (F.obj X)) := by
  simp only [Functor.doldPuppeFunctorSingle₀HomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_hom]
  exact Category.assoc _ _ _

@[simp]
lemma Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) (X : C) :
    (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv =
      (ChainComplex.fromSingle₀Equiv
          ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj (F.obj X)))
          (F.obj X)).symm (𝟙 (F.obj X)) ≫
        (alternatingFaceMapComplex D).map (Functor.constComp _ X F).inv ≫
          (alternatingFaceMapComplex D).map
            (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.inv.app X) F) := by
  dsimp only [Functor.doldPuppeFunctorSingle₀HomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, SimplicialObject.whiskering]
  simp only [Functor.mapIso_inv, Iso.trans_inv, Functor.map_comp, Iso.app_inv,
    whiskeringRight_obj_map, SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv]
  rfl

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom` in `X`. -/
lemma Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom_naturality
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    F.doldPuppeFunctor.map ((ChainComplex.single₀ C).map f) ≫
        (F.doldPuppeFunctorSingle₀HomotopyEquiv Y).hom =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom ≫ (ChainComplex.single₀ D).map (F.map f) := by
  have hConst : CommSq
      (((SimplicialObject.whiskering C D).obj F).map ((SimplicialObject.const C).map f))
      (Functor.constComp _ X F).hom (Functor.constComp _ Y F).hom
      ((SimplicialObject.const D).map (F.map f)) :=
    ⟨(Functor.compConstIso _ F).symm.hom.naturality f⟩
  have hsq : CommSq _ _ _ ((ChainComplex.single₀ D).map (F.map f)) := CommSq.vert_comp
    ((alternatingFaceMapComplex D).map_commSq
      (((SimplicialObject.whiskering C D).obj F).map_commSq
        ⟨Idempotents.DoldKan.Γ.single₀Iso.hom.naturality f⟩))
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hConst)
      ⟨AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
        (SimplicialObject.Augmented.const.map (F.map f))⟩)
  simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]
  exact hsq.w

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv` in `X`. -/
lemma Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv_naturality
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (ChainComplex.single₀ D).map (F.map f) ≫ (F.doldPuppeFunctorSingle₀HomotopyEquiv Y).inv =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv ≫
        F.doldPuppeFunctor.map ((ChainComplex.single₀ C).map f) := by
  have hConst : CommSq
      ((SimplicialObject.const D).map (F.map f))
      (Functor.constComp _ X F).inv (Functor.constComp _ Y F).inv
      (((SimplicialObject.whiskering C D).obj F).map ((SimplicialObject.const C).map f)) :=
    ⟨(Functor.compConstIso _ F).symm.inv.naturality f⟩
  have hsq : CommSq ((ChainComplex.single₀ D).map (F.map f)) _ _ _ := CommSq.vert_comp
    ⟨SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality (F.map f)⟩
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hConst)
      ((alternatingFaceMapComplex D).map_commSq
        (((SimplicialObject.whiskering C D).obj F).map_commSq
          ⟨Idempotents.DoldKan.Γ.single₀Iso.inv.naturality f⟩)))
  simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv]
  exact hsq.w

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom` in `F`. -/
lemma NatTrans.doldPuppeFunctorSingle₀HomotopyEquiv_hom_naturality
    [HasZeroObject C] [HasZeroObject D] {F G : C ⥤ D} (α : F ⟶ G) (X : C) :
    ((doldPuppe C D).map α).app ((ChainComplex.single₀ C).obj X) ≫
        (G.doldPuppeFunctorSingle₀HomotopyEquiv X).hom =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom ≫
        (ChainComplex.single₀ D).map (α.app X) := by
  have hsq1 : CommSq
      (((SimplicialObject.whiskering C D).map α).app (Γ.obj ((ChainComplex.single₀ C).obj X)))
      (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.hom.app X) F)
      (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.hom.app X) G)
      (((SimplicialObject.whiskering C D).map α).app ((SimplicialObject.const C).obj X)) :=
    ⟨(((SimplicialObject.whiskering C D).map α).naturality
      (Idempotents.DoldKan.Γ.single₀Iso.hom.app X)).symm⟩
  have hsq2 : CommSq
      (((SimplicialObject.whiskering C D).map α).app ((SimplicialObject.const C).obj X))
      (Functor.constComp _ X F).hom (Functor.constComp _ X G).hom
      ((SimplicialObject.const D).map (α.app X)) :=
    ⟨by ext Δ; simp⟩
  have hsq : CommSq _ _ _ ((ChainComplex.single₀ D).map (α.app X)) := CommSq.vert_comp
    ((alternatingFaceMapComplex D).map_commSq hsq1)
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hsq2)
      ⟨AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
        (SimplicialObject.Augmented.const.map (α.app X))⟩)
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]
  exact hsq.w

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv` in `F`. -/
lemma NatTrans.doldPuppeFunctorSingle₀HomotopyEquiv_inv_naturality
    [HasZeroObject C] [HasZeroObject D] {F G : C ⥤ D} (α : F ⟶ G) (X : C) :
    (ChainComplex.single₀ D).map (α.app X) ≫
        (G.doldPuppeFunctorSingle₀HomotopyEquiv X).inv =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv ≫
        ((doldPuppe C D).map α).app ((ChainComplex.single₀ C).obj X) := by
  have hsq1 : CommSq
      ((SimplicialObject.const D).map (α.app X))
      (Functor.constComp _ X F).inv (Functor.constComp _ X G).inv
      (((SimplicialObject.whiskering C D).map α).app ((SimplicialObject.const C).obj X)) :=
    ⟨by ext Δ; simp⟩
  have hsq2 : CommSq
      (((SimplicialObject.whiskering C D).map α).app ((SimplicialObject.const C).obj X))
      (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.inv.app X) F)
      (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.inv.app X) G)
      (((SimplicialObject.whiskering C D).map α).app (Γ.obj ((ChainComplex.single₀ C).obj X))) :=
    ⟨(((SimplicialObject.whiskering C D).map α).naturality
      (Idempotents.DoldKan.Γ.single₀Iso.inv.app X)).symm⟩
  have hsq : CommSq ((ChainComplex.single₀ D).map (α.app X)) _ _ _ := CommSq.vert_comp
    ⟨SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality (α.app X)⟩
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hsq1)
      ((alternatingFaceMapComplex D).map_commSq hsq2))
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv]
  exact hsq.w

/-- **Constant non-additive functor law**: for any object `B : D` and any chain complex
`K : ChainComplex C ℕ` (including `K = 0`), `((Functor.const C).obj B).doldPuppeFunctor.obj K` is
canonically chain homotopy equivalent to `(ChainComplex.single₀ D).obj B`. -/
def Functor.doldPuppeFunctorConstHomotopyEquiv [HasZeroObject D] (B : D) (K : ChainComplex C ℕ) :
    HomotopyEquiv (((Functor.const C).obj B).doldPuppeFunctor.obj K)
      ((ChainComplex.single₀ D).obj B) :=
  let isoSimp :
      ((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).obj (Γ.obj K) ≅
        (SimplicialObject.const D).obj B :=
    (Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso isoSimp)).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv

@[simp]
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom [HasZeroObject D]
    (B : D) (K : ChainComplex C ℕ) :
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom =
      (alternatingFaceMapComplex D).map
          ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom.app B) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.ε.app
          (SimplicialObject.Augmented.const.obj B) := by
  dsimp only [Functor.doldPuppeFunctorConstHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso]
  rw [Functor.mapIso_hom, Iso.app_hom,
    SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_hom]
  dsimp only [SimplicialObject.Augmented.drop, SimplicialObject.Augmented.const]

@[simp]
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv [HasZeroObject D]
    (B : D) (K : ChainComplex C ℕ) :
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv =
      (ChainComplex.fromSingle₀Equiv
          ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj B)) B).symm (𝟙 B) ≫
        (alternatingFaceMapComplex D).map
          ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.app B) := by
  dsimp only [Functor.doldPuppeFunctorConstHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso]
  rw [Functor.mapIso_inv, Iso.app_inv,
    SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv]

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `K`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom_naturality [HasZeroObject D]
    (B : D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    ((Functor.const C).obj B).doldPuppeFunctor.map φ ≫
        (Functor.doldPuppeFunctorConstHomotopyEquiv B L).hom =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom := by
  have hConst : CommSq
      (((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).map (Γ.map φ))
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom.app B)
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj L)).hom.app B)
      (𝟙 ((SimplicialObject.const D).obj B)) :=
    ⟨by ext Δ; simp⟩
  have hCh := ((alternatingFaceMapComplex D).map_commSq hConst).w
  simp only [Functor.map_id, Category.comp_id] at hCh
  have hw := congrArg
    (· ≫ AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (SimplicialObject.Augmented.const.obj B)) hCh
  dsimp only [SimplicialObject.Augmented.drop, SimplicialObject.Augmented.const] at hw
  rw [Category.assoc] at hw
  simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorConstHomotopyEquiv_hom]
  exact hw

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `K`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv_naturality [HasZeroObject D]
    (B : D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
        ((Functor.const C).obj B).doldPuppeFunctor.map φ =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B L).inv := by
  have hConst : CommSq
      (𝟙 ((SimplicialObject.const D).obj B))
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.app B)
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj L)).inv.app B)
      (((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).map (Γ.map φ)) :=
    ⟨by ext Δ; simp⟩
  have hCh := ((alternatingFaceMapComplex D).map_commSq hConst).w
  simp only [Functor.map_id, Category.id_comp] at hCh
  have hw := congrArg
    (((ChainComplex.fromSingle₀Equiv
        ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj B)) B).symm (𝟙 B)) ≫
      ·) hCh
  rw [← Category.assoc] at hw
  simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorConstHomotopyEquiv_inv]
  exact hw.symm

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `B`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom_naturality_left [HasZeroObject D]
    {B B' : D} (g : B ⟶ B') (K : ChainComplex C ℕ) :
    ((doldPuppe C D).map ((Functor.const C).map g)).app K ≫
        (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).hom =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom ≫ (ChainComplex.single₀ D).map g := by
  have hConst : CommSq
      (((SimplicialObject.whiskering C D).map ((Functor.const C).map g)).app (Γ.obj K))
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom.app B)
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom.app B')
      ((SimplicialObject.const D).map g) :=
    ⟨(Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom.naturality g⟩
  have hsq : CommSq _ _ _ ((ChainComplex.single₀ D).map g) := CommSq.vert_comp
    ((alternatingFaceMapComplex D).map_commSq hConst)
    ⟨AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
      (SimplicialObject.Augmented.const.map g)⟩
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorConstHomotopyEquiv_hom]
  exact hsq.w

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `B`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv_naturality_left [HasZeroObject D]
    {B B' : D} (g : B ⟶ B') (K : ChainComplex C ℕ) :
    (ChainComplex.single₀ D).map g ≫ (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).inv =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
        ((doldPuppe C D).map ((Functor.const C).map g)).app K := by
  have hConst : CommSq
      ((SimplicialObject.const D).map g)
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.app B)
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.app B')
      (((SimplicialObject.whiskering C D).map ((Functor.const C).map g)).app (Γ.obj K)) :=
    ⟨(Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.naturality g⟩
  have hsq : CommSq ((ChainComplex.single₀ D).map g) _ _ _ := CommSq.vert_comp
    ⟨SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality g⟩
    ((alternatingFaceMapComplex D).map_commSq hConst)
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorConstHomotopyEquiv_inv]
  exact hsq.w

end CategoryTheory
