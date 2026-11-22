/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.SimplicialHomotopy
public import TauCeti.AlgebraicTopology.DoldKan.Const
import TauCeti.AlgebraicTopology.SimplicialObject.ExtraDegeneracy
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
`TauCeti.AlgebraicTopology.DoldKan.Projective`.

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

lemma Functor.doldPuppeFunctor_map (F : C ⥤ D) {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    F.doldPuppeFunctor.map f =
      eqToHom (F.doldPuppeFunctor_obj K) ≫
        (alternatingFaceMapComplex D).map
          (((SimplicialObject.whiskering C D).obj F).map (Γ.map f)) ≫
        eqToHom (F.doldPuppeFunctor_obj L).symm := by
  change (alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map f)) =
      𝟙 _ ≫ (alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map f)) ≫ 𝟙 _
  simp

@[simp]
lemma Functor.doldPuppeFunctor_obj_X (F : C ⥤ D) (K : ChainComplex C ℕ) (n : ℕ) :
    (F.doldPuppeFunctor.obj K).X n = F.obj ((Γ.obj K) _⦋n⦌) := (rfl)

@[simp]
lemma Functor.doldPuppeFunctor_obj_d (F : C ⥤ D) (K : ChainComplex C ℕ) (n : ℕ) :
    (F.doldPuppeFunctor.obj K).d (n + 1) n =
      eqToHom (F.doldPuppeFunctor_obj_X K (n + 1)) ≫
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((Γ.obj K).δ i)) ≫
        eqToHom (F.doldPuppeFunctor_obj_X K n).symm := by
  change ((alternatingFaceMapComplex D).obj
        (((SimplicialObject.whiskering C D).obj F).obj (Γ.obj K))).d (n + 1) n =
      𝟙 _ ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((Γ.obj K).δ i)) ≫ 𝟙 _
  simp [AlternatingFaceMapComplex.objD, SimplicialObject.δ]

@[simp]
lemma Functor.doldPuppeFunctor_map_f (F : C ⥤ D) {K L : ChainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    (F.doldPuppeFunctor.map f).f n =
      eqToHom (F.doldPuppeFunctor_obj_X K n) ≫
        F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) ≫
        eqToHom (F.doldPuppeFunctor_obj_X L n).symm := by
  change F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) =
      𝟙 _ ≫ F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) ≫ 𝟙 _
  simp

@[simp]
lemma doldPuppe_map_app_f {F G : C ⥤ D} (α : F ⟶ G) (K : ChainComplex C ℕ) (n : ℕ) :
    (((doldPuppe C D).map α).app K).f n =
      eqToHom (F.doldPuppeFunctor_obj_X K n) ≫
        α.app ((Γ.obj K) _⦋n⦌) ≫
        eqToHom (G.doldPuppeFunctor_obj_X K n).symm := by
  change α.app ((Γ.obj K) _⦋n⦌) = 𝟙 _ ≫ α.app ((Γ.obj K) _⦋n⦌) ≫ 𝟙 _
  simp

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
  dsimp only [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor, doldPuppe]; simp

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_inv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).inv = F.doldPuppeFunctor.map e.inv := by
  dsimp only [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor, doldPuppe]; simp

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
  simp [Functor.doldPuppeFunctorAdditiveHomotopyEquiv, HomotopyEquiv.ofIso]
  rfl

@[simp]
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) :
    (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv =
      (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app K) ≫
        (F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj K)) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K) := by
  simp [Functor.doldPuppeFunctorAdditiveHomotopyEquiv, HomotopyEquiv.ofIso]
  rfl

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `K`. -/
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    F.doldPuppeFunctor.map φ ≫ (F.doldPuppeFunctorAdditiveHomotopyEquiv L).hom =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom ≫
        (F.mapHomologicalComplex (.down ℕ)).map φ := by
  have hsq : CommSq
      ((alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ)))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj K) ≫
        (F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj K) ≫ (η.hom.app K)))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj L) ≫
        (F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj L) ≫ (η.hom.app L)))
      ((F.mapHomologicalComplex (.down ℕ)).map φ) :=
    CommSq.vert_comp
      ⟨(alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.hom.naturality (Γ.map φ)⟩
      ((F.mapHomologicalComplex (.down ℕ)).map_commSq
        (CommSq.vert_comp ⟨PInftyToN.naturality (Γ.map φ)⟩ ⟨(η (C := C)).hom.naturality φ⟩))
  simpa [Functor.doldPuppeFunctor, doldPuppe, Category.assoc] using hsq.w

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `K`. -/
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (.down ℕ)).map φ ≫ (F.doldPuppeFunctorAdditiveHomotopyEquiv L).inv =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv ≫ F.doldPuppeFunctor.map φ := by
  have hsq : CommSq
      ((F.mapHomologicalComplex (.down ℕ)).map φ)
      ((F.mapHomologicalComplex (.down ℕ)).map ((η.inv.app K) ≫ inclusionN.app (Γ.obj K)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K))
      ((F.mapHomologicalComplex (.down ℕ)).map ((η.inv.app L) ≫ inclusionN.app (Γ.obj L)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj L))
      ((alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ))) :=
    CommSq.vert_comp
      ((F.mapHomologicalComplex (.down ℕ)).map_commSq
        (CommSq.vert_comp ⟨(η (C := C)).inv.naturality φ⟩ ⟨inclusionN.naturality (Γ.map φ)⟩))
      ⟨(alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.inv.naturality (Γ.map φ)⟩
  simpa [Functor.doldPuppeFunctor, doldPuppe, Category.assoc] using hsq.w

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `F`. -/
lemma NatTrans.doldPuppeFunctorAdditiveHomotopyEquiv_hom_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (K : ChainComplex C ℕ) :
    ((doldPuppe C D).map α).app K ≫ (G.doldPuppeFunctorAdditiveHomotopyEquiv K).hom =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom ≫
        (α.mapHomologicalComplex (.down ℕ)).app K := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [doldPuppe, Functor.doldPuppeFunctor, Functor.comp_map,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom, HomologicalComplex.comp_f,
    alternatingFaceMapComplexCompMapHomologicalComplexIso_inv_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
  dsimp
  simp only [Category.id_comp]
  rw [← α.naturality_assoc, ← α.naturality, Category.assoc]

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `F`. -/
lemma NatTrans.doldPuppeFunctorAdditiveHomotopyEquiv_inv_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (K : ChainComplex C ℕ) :
    (α.mapHomologicalComplex (.down ℕ)).app K ≫
        (G.doldPuppeFunctorAdditiveHomotopyEquiv K).inv =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv ≫
        ((doldPuppe C D).map α).app K := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [doldPuppe, Functor.doldPuppeFunctor, Functor.comp_map,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv, HomologicalComplex.comp_f,
    alternatingFaceMapComplexCompMapHomologicalComplexIso_hom_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
  dsimp
  simp only [Category.comp_id]
  rw [← α.naturality_assoc, ← α.naturality, Category.assoc]

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
  simp [Functor.doldPuppeFunctorSingle₀HomotopyEquiv, HomotopyEquiv.trans, HomotopyEquiv.ofIso]
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
    ⟨by ext Δ; simp⟩
  have hsq : CommSq _ _ _ ((ChainComplex.single₀ D).map (F.map f)) := CommSq.vert_comp
    ((alternatingFaceMapComplex D).map_commSq
      (((SimplicialObject.whiskering C D).obj F).map_commSq
        ⟨Idempotents.DoldKan.Γ.single₀Iso.hom.naturality f⟩))
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hConst)
      ⟨AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
        (SimplicialObject.Augmented.const.map (F.map f))⟩)
  simp only [Functor.doldPuppeFunctor, doldPuppe, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]
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
    ⟨by ext Δ; simp⟩
  have hsq : CommSq ((ChainComplex.single₀ D).map (F.map f)) _ _ _ := CommSq.vert_comp
    ⟨SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality (F.map f)⟩
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hConst)
      ((alternatingFaceMapComplex D).map_commSq
        (((SimplicialObject.whiskering C D).obj F).map_commSq
          ⟨Idempotents.DoldKan.Γ.single₀Iso.inv.naturality f⟩)))
  simp only [Functor.doldPuppeFunctor, doldPuppe, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv]
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
    ⟨by ext Δ; dsimp; simp [α.naturality]⟩
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
  simp only [doldPuppe, Functor.comp_map, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]
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
    ⟨by ext Δ; dsimp; simp [α.naturality]⟩
  have hsq : CommSq ((ChainComplex.single₀ D).map (α.app X)) _ _ _ := CommSq.vert_comp
    ⟨SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality (α.app X)⟩
    (CommSq.vert_comp
      ((alternatingFaceMapComplex D).map_commSq hsq1)
      ((alternatingFaceMapComplex D).map_commSq hsq2))
  simp only [doldPuppe, Functor.comp_map, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv]
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
  simp [Functor.doldPuppeFunctorConstHomotopyEquiv, HomotopyEquiv.trans, HomotopyEquiv.ofIso]
  rfl

@[simp]
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv [HasZeroObject D]
    (B : D) (K : ChainComplex C ℕ) :
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv =
      (ChainComplex.fromSingle₀Equiv
          ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj B)) B).symm (𝟙 B) ≫
        (alternatingFaceMapComplex D).map
          ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.app B) := by
  simp [Functor.doldPuppeFunctorConstHomotopyEquiv, HomotopyEquiv.trans, HomotopyEquiv.ofIso]
  rfl

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `K`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom_naturality [HasZeroObject D]
    (B : D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    ((Functor.const C).obj B).doldPuppeFunctor.map φ ≫
        (Functor.doldPuppeFunctorConstHomotopyEquiv B L).hom =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom := by
  ext
  rw [HomologicalComplex.comp_f]
  simp [Functor.doldPuppeFunctor, doldPuppe, Functor.constCompWhiskeringLeftIso]

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `K`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv_naturality [HasZeroObject D]
    (B : D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
        ((Functor.const C).obj B).doldPuppeFunctor.map φ =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B L).inv := by
  ext
  simp [Functor.doldPuppeFunctor, doldPuppe]

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
    ⟨by ext Δ; simp⟩
  have hsq : CommSq _ _ _ ((ChainComplex.single₀ D).map g) := CommSq.vert_comp
    ((alternatingFaceMapComplex D).map_commSq hConst)
    ⟨AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
      (SimplicialObject.Augmented.const.map g)⟩
  simp only [doldPuppe, Functor.comp_map, Functor.doldPuppeFunctorConstHomotopyEquiv_hom]
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
    ⟨by ext Δ; simp⟩
  have hsq : CommSq ((ChainComplex.single₀ D).map g) _ _ _ := CommSq.vert_comp
    ⟨SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality g⟩
    ((alternatingFaceMapComplex D).map_commSq hConst)
  simp only [doldPuppe, Functor.comp_map, Functor.doldPuppeFunctorConstHomotopyEquiv_inv]
  exact hsq.w

end CategoryTheory
