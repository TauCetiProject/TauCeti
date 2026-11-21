/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.SimplicialHomotopy
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import TauCeti.AlgebraicTopology.DoldKan.Const

/-!
# The Dold–Puppe functor

For an arbitrary (not necessarily additive) functor `F : C ⥤ D` from an idempotent-complete
preadditive category `C` with finite coproducts into a preadditive category `D`, the chain-level
**Dold–Puppe functor** `CategoryTheory.Functor.doldPuppeFunctor F` is
`Idempotents.DoldKan.Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D`.

Because `Γ` carries chain homotopies to combinatorial simplicial homotopies
(`Idempotents.DoldKan.Γ.mapHomotopy`), levelwise whiskering by *any* functor preserves simplicial
homotopies, and `alternatingFaceMapComplex` returns to chain homotopies, `F.doldPuppeFunctor`
preserves chain homotopies and chain homotopy equivalences with no additivity or projectivity
hypotheses. The projective resolution-independence theorem
`CategoryTheory.Functor.quasiIso_doldPuppeFunctor_map_of_projective` lives in
`TauCeti.AlgebraicTopology.DoldKan.Projective`.

## Main definitions and results

* `Functor.doldPuppeFunctor`: `Γ ⋙ (whiskering C D).obj F ⋙ alternatingFaceMapComplex D`.
* `NatTrans.doldPuppeFunctor`: naturality of `doldPuppeFunctor` in `F`.
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

/-- **The Dold–Puppe chain-complex functor** associated to an arbitrary (not necessarily additive)
functor `F : C ⥤ D`: sends `K : ChainComplex C ℕ` to the alternating face map complex of `F` applied
levelwise to `Idempotents.DoldKan.Γ.obj K`. Evaluating `F.doldPuppeFunctor` on a projective
resolution computes the left derived functor of `F` in the sense of Dold and Puppe. -/
def Functor.doldPuppeFunctor (F : C ⥤ D) : ChainComplex C ℕ ⥤ ChainComplex D ℕ :=
  Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D

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
lemma Functor.doldPuppeFunctor_map_f (F : C ⥤ D) {K L : ChainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    (F.doldPuppeFunctor.map f).f n =
      eqToHom (F.doldPuppeFunctor_obj_X K n) ≫
        F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) ≫
        eqToHom (F.doldPuppeFunctor_obj_X L n).symm := by
  change F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) =
      𝟙 _ ≫ F.map ((Γ.map f).app (Opposite.op ⦋n⦌)) ≫ 𝟙 _
  simp

/-- Naturality of `Functor.doldPuppeFunctor` with respect to a natural transformation
`α : F ⟶ G`. -/
def NatTrans.doldPuppeFunctor {F G : C ⥤ D} (α : F ⟶ G) :
    F.doldPuppeFunctor ⟶ G.doldPuppeFunctor :=
  Functor.whiskerLeft Γ
    (Functor.whiskerRight ((SimplicialObject.whiskering C D).map α) (alternatingFaceMapComplex D))

@[simp]
lemma NatTrans.doldPuppeFunctor_app_f {F G : C ⥤ D} (α : F ⟶ G) (K : ChainComplex C ℕ) (n : ℕ) :
    ((NatTrans.doldPuppeFunctor α).app K).f n =
      eqToHom (F.doldPuppeFunctor_obj_X K n) ≫
        α.app ((Γ.obj K) _⦋n⦌) ≫
        eqToHom (G.doldPuppeFunctor_obj_X K n).symm := by
  change α.app ((Γ.obj K) _⦋n⦌) = 𝟙 _ ≫ α.app ((Γ.obj K) _⦋n⦌) ≫ 𝟙 _
  simp

@[simp]
lemma NatTrans.doldPuppeFunctor_id (F : C ⥤ D) :
    NatTrans.doldPuppeFunctor (𝟙 F) = 𝟙 F.doldPuppeFunctor := by ext K n; simp

@[simp]
lemma NatTrans.doldPuppeFunctor_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.doldPuppeFunctor (α ≫ β) =
      NatTrans.doldPuppeFunctor α ≫ NatTrans.doldPuppeFunctor β := by ext K n; simp

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
  dsimp only [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor]; simp

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_inv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).inv = F.doldPuppeFunctor.map e.inv := by
  dsimp only [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor]; simp

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

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `K`. -/
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    F.doldPuppeFunctor.map φ ≫ (F.doldPuppeFunctorAdditiveHomotopyEquiv L).hom =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom ≫
        (F.mapHomologicalComplex (.down ℕ)).map φ := by
  dsimp only [Functor.doldPuppeFunctorAdditiveHomotopyEquiv, Functor.doldPuppeFunctor,
    Functor.comp_map, HomotopyEquiv.trans, HomotopyEquiv.ofIso, HomotopyEquiv.symm]
  simp only [Functor.mapHomotopyEquiv_hom, homotopyEquivNAlternatingFaceMapComplex_inv,
    Functor.mapIso_hom]
  have hnat :
      (alternatingFaceMapComplex D).map (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ)) ≫
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.app (Γ.obj L)).hom =
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.app (Γ.obj K)).hom ≫
          (F.mapHomologicalComplex (.down ℕ)).map ((alternatingFaceMapComplex C).map (Γ.map φ)) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.hom.naturality (Γ.map φ)
  have hη : N.map (Γ.map φ) ≫ (η.app L).hom = (η.app K).hom ≫ φ :=
    (η (C := C)).hom.naturality φ
  rw [← Category.assoc, hnat, Category.assoc,
    ← Category.assoc _ ((F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj L))),
    ← (F.mapHomologicalComplex (.down ℕ)).map_comp,
    PInftyToN.naturality (Γ.map φ),
    (F.mapHomologicalComplex (.down ℕ)).map_comp, Category.assoc, Category.assoc,
    ← (F.mapHomologicalComplex (.down ℕ)).map_comp, hη,
    (F.mapHomologicalComplex (.down ℕ)).map_comp, ← Category.assoc, ← Category.assoc]
  simp only [Category.assoc]

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `K`. -/
lemma Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (.down ℕ)).map φ ≫ (F.doldPuppeFunctorAdditiveHomotopyEquiv L).inv =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv ≫ F.doldPuppeFunctor.map φ := by
  dsimp only [Functor.doldPuppeFunctorAdditiveHomotopyEquiv, Functor.doldPuppeFunctor,
    Functor.comp_map, HomotopyEquiv.trans, HomotopyEquiv.ofIso, HomotopyEquiv.symm]
  simp only [Functor.mapHomotopyEquiv_inv, homotopyEquivNAlternatingFaceMapComplex_hom,
    Functor.mapIso_inv]
  have hnat :
      (F.mapHomologicalComplex (.down ℕ)).map ((alternatingFaceMapComplex C).map (Γ.map φ)) ≫
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.app (Γ.obj L)).inv =
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.app (Γ.obj K)).inv ≫
          (alternatingFaceMapComplex D).map
            (((SimplicialObject.whiskering C D).obj F).map (Γ.map φ)) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.inv.naturality (Γ.map φ)
  have hη : φ ≫ (η.app L).inv = (η.app K).inv ≫ N.map (Γ.map φ) :=
    (η (C := C)).inv.naturality φ
  rw [← Category.assoc, ← Category.assoc,
    ← (F.mapHomologicalComplex (.down ℕ)).map_comp, hη,
    (F.mapHomologicalComplex (.down ℕ)).map_comp, Category.assoc, Category.assoc,
    ← Category.assoc _ ((F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj L))),
    ← (F.mapHomologicalComplex (.down ℕ)).map_comp,
    inclusionN.naturality (Γ.map φ),
    (F.mapHomologicalComplex (.down ℕ)).map_comp, Category.assoc, Category.assoc, hnat,
    ← Category.assoc]

private lemma single₀_map_comp_extraDegeneracy_const_inv [HasZeroObject D]
    {X Y : D} (f : X ⟶ Y) :
    ((ChainComplex.single₀ D).map f ≫
        (SimplicialObject.Augmented.ExtraDegeneracy.const Y).homotopyEquiv.inv) =
      ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv.inv ≫
        (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map f)) := by
  ext
  dsimp only [SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero,
    ChainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  erw [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  dsimp
  erw [Category.comp_id, Category.id_comp]

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

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom` in `X`. -/
lemma Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom_naturality
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    F.doldPuppeFunctor.map ((ChainComplex.single₀ C).map f) ≫
        (F.doldPuppeFunctorSingle₀HomotopyEquiv Y).hom =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom ≫ (ChainComplex.single₀ D).map (F.map f) := by
  have hΓ : Γ.map ((ChainComplex.single₀ C).map f) ≫ (Γ.single₀Iso.app Y).hom =
      (Γ.single₀Iso.app X).hom ≫ (SimplicialObject.const C).map f :=
    Γ.single₀Iso.hom.naturality f
  have hconst :
      (((SimplicialObject.whiskering C D).obj F).map ((SimplicialObject.const C).map f) ≫
        (Functor.constComp _ Y F).hom) =
      (Functor.constComp _ X F).hom ≫ (SimplicialObject.const D).map (F.map f) := by
    apply NatTrans.ext
    funext Δ
    dsimp; simp
  have hiso :
      (((SimplicialObject.whiskering C D).obj F).map (Γ.map ((ChainComplex.single₀ C).map f)) ≫
        ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).hom ≫
        (Functor.constComp _ Y F).hom) =
      (((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app X).hom ≫
        (Functor.constComp _ X F).hom) ≫ (SimplicialObject.const D).map (F.map f) := by
    rw [← Category.assoc, ← Functor.map_comp, hΓ, Functor.map_comp, Category.assoc,
      hconst, ← Category.assoc]
  have hε :
      (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map (F.map f)) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.hom =
        (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj X)).homotopyEquiv.hom ≫
          (ChainComplex.single₀ D).map (F.map f) :=
    AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
      (SimplicialObject.Augmented.const.map (F.map f))
  have h1 :
      F.doldPuppeFunctor.map ((ChainComplex.single₀ C).map f) ≫
          (F.doldPuppeFunctorSingle₀HomotopyEquiv Y).hom =
        (alternatingFaceMapComplex D).map
            (((SimplicialObject.whiskering C D).obj F).map
                (Γ.map ((ChainComplex.single₀ C).map f)) ≫
              ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).hom ≫
              (Functor.constComp _ Y F).hom) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.hom := by
    dsimp only [Functor.doldPuppeFunctorSingle₀HomotopyEquiv, Functor.doldPuppeFunctor,
      Functor.comp_map, HomotopyEquiv.trans, HomotopyEquiv.ofIso, Functor.mapIso_hom,
      Iso.trans_hom]
    erw [← Category.assoc, ← (alternatingFaceMapComplex D).map_comp]
    rfl
  have h2 :
      (alternatingFaceMapComplex D).map
            (((SimplicialObject.whiskering C D).obj F).map
                (Γ.map ((ChainComplex.single₀ C).map f)) ≫
              ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).hom ≫
              (Functor.constComp _ Y F).hom) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.hom =
        ((alternatingFaceMapComplex D).map
              (((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app X).hom ≫
                (Functor.constComp _ X F).hom) ≫
            (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map (F.map f))) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.hom := by
    rw [hiso, (alternatingFaceMapComplex D).map_comp]
  have h3 :
      ((alternatingFaceMapComplex D).map
              (((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app X).hom ≫
                (Functor.constComp _ X F).hom) ≫
            (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map (F.map f))) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.hom =
        (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom ≫
          (ChainComplex.single₀ D).map (F.map f) := by
    erw [Category.assoc]
    refine (whisker_eq _ hε).trans ?_
    exact (Category.assoc _ _ _).symm
  exact h1.trans (h2.trans h3)

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv` in `X`. -/
lemma Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv_naturality
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (ChainComplex.single₀ D).map (F.map f) ≫ (F.doldPuppeFunctorSingle₀HomotopyEquiv Y).inv =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv ≫
        F.doldPuppeFunctor.map ((ChainComplex.single₀ C).map f) := by
  have hΓ : (SimplicialObject.const C).map f ≫ (Γ.single₀Iso.app Y).inv =
      (Γ.single₀Iso.app X).inv ≫ Γ.map ((ChainComplex.single₀ C).map f) :=
    Γ.single₀Iso.inv.naturality f
  have hiso :
      ((SimplicialObject.const D).map (F.map f) ≫
        (Functor.constComp _ Y F).inv ≫
        ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).inv) =
      ((Functor.constComp _ X F).inv ≫
        ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app X).inv) ≫
        ((SimplicialObject.whiskering C D).obj F).map (Γ.map ((ChainComplex.single₀ C).map f)) := by
    have hconst : ((SimplicialObject.const D).map (F.map f) ≫ (Functor.constComp _ Y F).inv) =
        (Functor.constComp _ X F).inv ≫
          ((SimplicialObject.whiskering C D).obj F).map ((SimplicialObject.const C).map f) := by
      apply NatTrans.ext
      funext Δ
      dsimp; simp
    rw [← Category.assoc, hconst, Category.assoc, Category.assoc, ← Functor.map_comp,
      hΓ, Functor.map_comp, ← Category.assoc]
  have h1 :
      (ChainComplex.single₀ D).map (F.map f) ≫ (F.doldPuppeFunctorSingle₀HomotopyEquiv Y).inv =
        ((ChainComplex.single₀ D).map (F.map f) ≫
            (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.inv) ≫
          (alternatingFaceMapComplex D).map
            ((Functor.constComp _ Y F).inv ≫
              ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).inv) := by
    exact (Category.assoc _ _ _).symm
  have h2 :
      ((ChainComplex.single₀ D).map (F.map f) ≫
            (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj Y)).homotopyEquiv.inv) ≫
          (alternatingFaceMapComplex D).map
            ((Functor.constComp _ Y F).inv ≫
              ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).inv) =
        (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj X)).homotopyEquiv.inv ≫
          (alternatingFaceMapComplex D).map
            ((SimplicialObject.const D).map (F.map f) ≫
              (Functor.constComp _ Y F).inv ≫
              ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).inv) := by
    refine (congrArg (· ≫ _) (single₀_map_comp_extraDegeneracy_const_inv (F.map f))).trans ?_
    erw [Category.assoc, (alternatingFaceMapComplex D).map_comp]
    rfl
  have h3 :
      (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj X)).homotopyEquiv.inv ≫
          (alternatingFaceMapComplex D).map
            ((SimplicialObject.const D).map (F.map f) ≫
              (Functor.constComp _ Y F).inv ≫
              ((SimplicialObject.whiskering C D).obj F).map (Γ.single₀Iso.app Y).inv) =
        (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv ≫
          F.doldPuppeFunctor.map ((ChainComplex.single₀ C).map f) := by
    erw [hiso, (alternatingFaceMapComplex D).map_comp, ← Category.assoc]
    rfl
  exact h1.trans (h2.trans h3)

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

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `K`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom_naturality [HasZeroObject D]
    (B : D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    ((Functor.const C).obj B).doldPuppeFunctor.map φ ≫
        (Functor.doldPuppeFunctorConstHomotopyEquiv B L).hom =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom := by
  dsimp only [Functor.doldPuppeFunctorConstHomotopyEquiv, Functor.doldPuppeFunctor,
    Functor.comp_map, HomotopyEquiv.trans, HomotopyEquiv.ofIso, Functor.mapIso_hom]
  rw [← Category.assoc, ← (alternatingFaceMapComplex D).map_comp]
  have hiso :
      (((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).map (Γ.map φ) ≫
        ((Functor.constCompWhiskeringLeftIso _ (Γ.obj L)).app B).hom) =
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B).hom := by
    ext Δ; dsimp; simp
  rw [hiso]

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `K`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv_naturality [HasZeroObject D]
    (B : D) {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
        ((Functor.const C).obj B).doldPuppeFunctor.map φ =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B L).inv := by
  dsimp only [Functor.doldPuppeFunctorConstHomotopyEquiv, Functor.doldPuppeFunctor,
    Functor.comp_map, HomotopyEquiv.trans, HomotopyEquiv.ofIso, Functor.mapIso_inv]
  rw [Category.assoc, ← (alternatingFaceMapComplex D).map_comp]
  have hiso :
      (((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B).inv ≫
        ((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).map (Γ.map φ)) =
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj L)).app B).inv := by
    ext Δ; dsimp; simp
  rw [hiso]

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `B`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom_naturality_left [HasZeroObject D]
    {B B' : D} (g : B ⟶ B') (K : ChainComplex C ℕ) :
    (NatTrans.doldPuppeFunctor ((Functor.const C).map g)).app K ≫
        (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).hom =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom ≫ (ChainComplex.single₀ D).map g := by
  have hiso :
      (((SimplicialObject.whiskering C D).map ((Functor.const C).map g)).app (Γ.obj K) ≫
        ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').hom) =
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B).hom ≫
        (SimplicialObject.const D).map g := by
    ext Δ; dsimp; simp
  have hε :
      (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map g) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.hom =
        (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv.hom ≫
          (ChainComplex.single₀ D).map g :=
    AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
      (SimplicialObject.Augmented.const.map g)
  have h1 :
      (NatTrans.doldPuppeFunctor ((Functor.const C).map g)).app K ≫
          (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).hom =
        (alternatingFaceMapComplex D).map
            (((SimplicialObject.whiskering C D).map ((Functor.const C).map g)).app (Γ.obj K) ≫
              ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').hom) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.hom := by
    erw [← Category.assoc, ← (alternatingFaceMapComplex D).map_comp]
    rfl
  have h2 :
      (alternatingFaceMapComplex D).map
            (((SimplicialObject.whiskering C D).map ((Functor.const C).map g)).app (Γ.obj K) ≫
              ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').hom) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.hom =
        ((alternatingFaceMapComplex D).map
              ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B).hom ≫
            (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map g)) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.hom := by
    rw [hiso, (alternatingFaceMapComplex D).map_comp]
  have h3 :
      ((alternatingFaceMapComplex D).map
              ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B).hom ≫
            (alternatingFaceMapComplex D).map ((SimplicialObject.const D).map g)) ≫
          (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.hom =
        (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom ≫ (ChainComplex.single₀ D).map g := by
    erw [Category.assoc]
    refine (whisker_eq _ hε).trans ?_
    exact (Category.assoc _ _ _).symm
  exact h1.trans (h2.trans h3)

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `B`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv_naturality_left [HasZeroObject D]
    {B B' : D} (g : B ⟶ B') (K : ChainComplex C ℕ) :
    (ChainComplex.single₀ D).map g ≫ (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).inv =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
        (NatTrans.doldPuppeFunctor ((Functor.const C).map g)).app K := by
  have hiso :
      ((SimplicialObject.const D).map g ≫
        ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').inv) =
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B).inv ≫
        ((SimplicialObject.whiskering C D).map ((Functor.const C).map g)).app (Γ.obj K) := by
    ext Δ; dsimp; simp
  have h1 :
      (ChainComplex.single₀ D).map g ≫ (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).inv =
        ((ChainComplex.single₀ D).map g ≫
            (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.inv) ≫
          (alternatingFaceMapComplex D).map
            ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').inv :=
    (Category.assoc _ _ _).symm
  have h2 :
      ((ChainComplex.single₀ D).map g ≫
            (SimplicialObject.Augmented.ExtraDegeneracy.const B').homotopyEquiv.inv) ≫
          (alternatingFaceMapComplex D).map
            ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').inv =
        (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv.inv ≫
          (alternatingFaceMapComplex D).map
            ((SimplicialObject.const D).map g ≫
              ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').inv) := by
    refine (congrArg (· ≫ _) (single₀_map_comp_extraDegeneracy_const_inv g)).trans ?_
    erw [Category.assoc, (alternatingFaceMapComplex D).map_comp]
    rfl
  have h3 :
      (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv.inv ≫
          (alternatingFaceMapComplex D).map
            ((SimplicialObject.const D).map g ≫
              ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B').inv) =
        (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
          (NatTrans.doldPuppeFunctor ((Functor.const C).map g)).app K := by
    erw [hiso, (alternatingFaceMapComplex D).map_comp, ← Category.assoc]
    rfl
  exact h1.trans (h2.trans h3)

end CategoryTheory
