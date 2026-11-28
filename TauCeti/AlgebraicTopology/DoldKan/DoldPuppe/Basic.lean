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
* `Functor.doldPuppeFunctorAdditiveHomotopyEquiv`, `Functor.doldPuppeFunctorAdditiveHom`,
  `Functor.doldPuppeFunctorAdditiveInv`: when `F` is additive, `F.doldPuppeFunctor` is
  naturally chain homotopy equivalent to `F.mapHomologicalComplex (.down ℕ)`.
* `Functor.doldPuppeFunctorSingle₀HomotopyEquiv`, `Functor.doldPuppeFunctorSingle₀Hom`,
  `Functor.doldPuppeFunctorSingle₀Inv`: degree-zero comparison sending
  `(ChainComplex.single₀ C).obj X` to `(ChainComplex.single₀ D).obj (F.obj X)`.
* `Functor.doldPuppeFunctorConstHomotopyEquiv`, `Functor.doldPuppeFunctorConstHom`,
  `Functor.doldPuppeFunctorConstInv`: constant-functor comparison sending every `K`
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

@[simp]
lemma Functor.doldPuppeMapHomotopy_hom (F : C ⥤ D) {K L : ChainComplex C ℕ} {φ ψ : K ⟶ L}
    (H : Homotopy φ ψ) (p : ℕ) :
    (F.doldPuppeMapHomotopy H).hom p (p + 1) =
      -∑ k : Fin (p + 1), (-1 : ℤ) ^ (k : ℕ) • F.map ((Γ.mapHomotopy H).h k) := by
  simp [Functor.doldPuppeMapHomotopy, SimplicialObject.Homotopy.toChainHomotopy]; rfl

@[simp]
lemma Functor.doldPuppeMapHomotopy_hom_eq_zero (F : C ⥤ D) {K L : ChainComplex C ℕ} {φ ψ : K ⟶ L}
    (H : Homotopy φ ψ) {p q : ℕ} (hpq : p + 1 ≠ q) :
    (F.doldPuppeMapHomotopy H).hom p q = 0 :=
  SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ p q hpq

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
  rw [Functor.doldPuppeFunctor_map]; dsimp only [Functor.doldPuppeMapHomotopyEquiv]; simp; rfl

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_inv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).inv = F.doldPuppeFunctor.map e.inv := by
  rw [Functor.doldPuppeFunctor_map]; dsimp only [Functor.doldPuppeMapHomotopyEquiv]; simp; rfl

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_homotopyHomInvId_hom (F : C ⥤ D)
    {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) (p q : ℕ) :
    (F.doldPuppeMapHomotopyEquiv e).homotopyHomInvId.hom p q =
      (F.doldPuppeMapHomotopy e.homotopyHomInvId).hom p q := by
  rcases eq_or_ne (p + 1) q with rfl | hpq
  · simp [Functor.doldPuppeMapHomotopyEquiv, SimplicialObject.Homotopy.toChainHomotopy]; rfl
  · simp [Functor.doldPuppeMapHomotopyEquiv, SimplicialObject.Homotopy.toChainHomotopy, hpq]; rfl

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_homotopyInvHomId_hom (F : C ⥤ D)
    {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) (p q : ℕ) :
    (F.doldPuppeMapHomotopyEquiv e).homotopyInvHomId.hom p q =
      (F.doldPuppeMapHomotopy e.homotopyInvHomId).hom p q := by
  rcases eq_or_ne (p + 1) q with rfl | hpq
  · simp [Functor.doldPuppeMapHomotopyEquiv, SimplicialObject.Homotopy.toChainHomotopy]; rfl
  · simp [Functor.doldPuppeMapHomotopyEquiv, SimplicialObject.Homotopy.toChainHomotopy, hpq]; rfl

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

/-- Natural transformation bundling the forward additive comparison
`(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `K`. -/
def Functor.doldPuppeFunctorAdditiveHom (F : C ⥤ D) [F.Additive] :
    F.doldPuppeFunctor ⟶ F.mapHomologicalComplex (.down ℕ) where
  app K := (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom
  naturality _ _ φ := by
    have hsq := CommSq.vert_comp
      ⟨(alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.hom.naturality (Γ.map φ)⟩
      (CommSq.vert_comp
        ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨PInftyToN.naturality (Γ.map φ)⟩)
        ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨(η (C := C)).hom.naturality φ⟩))
    simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom]
    exact hsq.w

@[simp]
lemma Functor.doldPuppeFunctorAdditiveHom_app (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    F.doldPuppeFunctorAdditiveHom.app K = (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom := (rfl)

/-- Natural transformation bundling the backward additive comparison
`(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `K`. -/
def Functor.doldPuppeFunctorAdditiveInv (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.down ℕ) ⟶ F.doldPuppeFunctor where
  app K := (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv
  naturality _ _ φ := by
    have hsq := CommSq.vert_comp
      ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨(η (C := C)).inv.naturality φ⟩)
      (CommSq.vert_comp
        ((F.mapHomologicalComplex (.down ℕ)).map_commSq ⟨inclusionN.naturality (Γ.map φ)⟩)
        ⟨(alternatingFaceMapComplexCompMapHomologicalComplexIso F).symm.inv.naturality (Γ.map φ)⟩)
    simp only [Functor.doldPuppeFunctor_map, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv]
    exact hsq.w

@[simp]
lemma Functor.doldPuppeFunctorAdditiveInv_app (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    F.doldPuppeFunctorAdditiveInv.app K = (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv := (rfl)

@[reassoc (attr := simp)]
lemma Functor.doldPuppeFunctorAdditiveInv_comp_hom (F : C ⥤ D) [F.Additive] :
    F.doldPuppeFunctorAdditiveInv ≫ F.doldPuppeFunctorAdditiveHom =
      𝟙 (F.mapHomologicalComplex (.down ℕ)) := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  have hL : (F.doldPuppeFunctorAdditiveInv ≫ F.doldPuppeFunctorAdditiveHom).app K =
      ((F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).inv.app K) ≫
          (F.mapHomologicalComplex (.down ℕ)).map (inclusionN.app (Γ.obj K)) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K)) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj K) ≫
          (F.mapHomologicalComplex (.down ℕ)).map (PInftyToN.app (Γ.obj K)) ≫
          (F.mapHomologicalComplex (.down ℕ)).map ((η (C := C)).hom.app K)) := by
    simp only [NatTrans.comp_app, Functor.doldPuppeFunctorAdditiveInv_app,
      Functor.doldPuppeFunctorAdditiveHom_app, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv,
      Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom]; rfl
  rw [hL, NatTrans.id_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp]
  rw [reassoc_of% inclusionN_app_comp_PInftyToN_app, Iso.inv_hom_id_app, Functor.map_id]; rfl

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom` in `F`. -/
lemma NatTrans.doldPuppeFunctorAdditiveHomotopyEquiv_hom_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (K : ChainComplex C ℕ) :
    ((doldPuppe C D).map α).app K ≫ (G.doldPuppeFunctorAdditiveHomotopyEquiv K).hom =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom ≫
        (α.mapHomologicalComplex (.down ℕ)).app K := by
  have hsq1 : CommSq
      ((alternatingFaceMapComplex D).map (((SimplicialObject.whiskering C D).map α).app (Γ.obj K)))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app (Γ.obj K))
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso G).inv.app (Γ.obj K))
      ((α.mapHomologicalComplex (.down ℕ)).app ((alternatingFaceMapComplex C).obj (Γ.obj K))) :=
    ⟨by ext n; simp [alternatingFaceMapComplexCompMapHomologicalComplexIso_inv_app_f]⟩
  have hsq2 := CommSq.vert_comp
    ⟨((α.mapHomologicalComplex (.down ℕ)).naturality (PInftyToN.app (Γ.obj K))).symm⟩
    ⟨((α.mapHomologicalComplex (.down ℕ)).naturality ((η (C := C)).hom.app K)).symm⟩
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_hom]
  exact (CommSq.vert_comp hsq1 hsq2).w

/-- Naturality of `(F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv` in `F`. -/
lemma NatTrans.doldPuppeFunctorAdditiveHomotopyEquiv_inv_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (K : ChainComplex C ℕ) :
    (α.mapHomologicalComplex (.down ℕ)).app K ≫
        (G.doldPuppeFunctorAdditiveHomotopyEquiv K).inv =
      (F.doldPuppeFunctorAdditiveHomotopyEquiv K).inv ≫
        ((doldPuppe C D).map α).app K := by
  have hsq2 := CommSq.vert_comp
    ⟨((α.mapHomologicalComplex (.down ℕ)).naturality (inclusionN.app (Γ.obj K))).symm⟩
    ⟨show (α.mapHomologicalComplex (.down ℕ)).app ((alternatingFaceMapComplex C).obj (Γ.obj K)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (Γ.obj K) =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Γ.obj K) ≫
        (alternatingFaceMapComplex D).map
          (((SimplicialObject.whiskering C D).map α).app (Γ.obj K)) by
      ext n; simp [alternatingFaceMapComplexCompMapHomologicalComplexIso_hom_app_f]⟩
  have hsq := CommSq.vert_comp
    ⟨((α.mapHomologicalComplex (.down ℕ)).naturality ((η (C := C)).inv.app K)).symm⟩ hsq2
  simp only [doldPuppe_map_app, Functor.doldPuppeFunctorAdditiveHomotopyEquiv_inv]
  exact hsq.w

section ConstComparison

private def constAugment [HasZeroObject D] :
    SimplicialObject.const D ⋙ alternatingFaceMapComplex D ⟶ ChainComplex.single₀ D :=
  Functor.whiskerLeft SimplicialObject.Augmented.const
    AlgebraicTopology.AlternatingFaceMapComplex.ε

private def constSection [HasZeroObject D] :
    ChainComplex.single₀ D ⟶ SimplicialObject.const D ⋙ alternatingFaceMapComplex D where
  app B := (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv.inv
  naturality _ _ g :=
    SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv_naturality g

@[simp]
private lemma constSection_comp_constAugment [HasZeroObject D] :
    (constSection (D := D)) ≫ constAugment = 𝟙 (ChainComplex.single₀ D) := by
  refine NatTrans.ext (funext fun B ↦ ?_)
  change (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv.inv ≫
      (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv.hom =
    𝟙 ((ChainComplex.single₀ D).obj B)
  ext
  change (((ChainComplex.fromSingle₀Equiv
      ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj B)) B).symm (𝟙 B)).f 0 ≫
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (SimplicialObject.Augmented.const.obj B)).f 0) = 𝟙 B
  rw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  dsimp [AlgebraicTopology.AlternatingFaceMapComplex.ε]
  rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  exact Category.id_comp (𝟙 B)

private def single₀EvalConstCompIso (X : C) :
    (SimplicialObject.whiskering C D ⋙
        (evaluation (SimplicialObject C) (SimplicialObject D)).obj
          ((SimplicialObject.const C).obj X)) ≅
      (evaluation C D).obj X ⋙ SimplicialObject.const D :=
  NatIso.ofComponents (fun F ↦ Functor.constComp _ X F) (fun _ ↦ by ext Δ; simp)

private def constWhiskeringIso (B : D) :
    ((Functor.const C).obj B).doldPuppeFunctor ≅
      (Functor.const (ChainComplex C ℕ)).obj
        ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj B)) :=
  NatIso.ofComponents
    (fun K ↦ (alternatingFaceMapComplex D).mapIso
      ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).app B))
    (fun φ ↦ by
      change (alternatingFaceMapComplex D).map
          (((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).map (Γ.map φ)) ≫
          (alternatingFaceMapComplex D).map
            ((Functor.constCompWhiskeringLeftIso _ (Γ.obj _)).hom.app B) =
        (alternatingFaceMapComplex D).map
            ((Functor.constCompWhiskeringLeftIso _ (Γ.obj _)).hom.app B) ≫
          𝟙 ((alternatingFaceMapComplex D).obj ((SimplicialObject.const D).obj B))
      rw [← Functor.map_comp, Category.comp_id]; congr 1; ext Δ; simp)

end ConstComparison

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

/-- Natural transformation bundling the forward degree-zero comparison
`(F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom` in `X`. -/
def Functor.doldPuppeFunctorSingle₀Hom [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) :
    ChainComplex.single₀ C ⋙ F.doldPuppeFunctor ⟶ F ⋙ ChainComplex.single₀ D where
  app X := (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom
  naturality _ _ f := by
    have h := (Functor.whiskerRight Idempotents.DoldKan.Γ.single₀Iso.hom
        ((SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D) ≫
      Functor.whiskerRight (Functor.compConstIso _ F).symm.hom (alternatingFaceMapComplex D) ≫
      Functor.whiskerLeft F constAugment).naturality f
    dsimp [NatTrans.comp_app, constAugment] at h
    rw [Functor.comp_map, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom,
      Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]
    exact h

@[simp]
lemma Functor.doldPuppeFunctorSingle₀Hom_app [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) (X : C) :
    F.doldPuppeFunctorSingle₀Hom.app X = (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom := (rfl)

/-- Natural transformation bundling the backward degree-zero comparison
`(F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv` in `X`. -/
def Functor.doldPuppeFunctorSingle₀Inv [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) :
    F ⋙ ChainComplex.single₀ D ⟶ ChainComplex.single₀ C ⋙ F.doldPuppeFunctor where
  app X := (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv
  naturality _ _ f := by
    have h := (Functor.whiskerLeft F constSection ≫
      Functor.whiskerRight (Functor.compConstIso _ F).symm.inv (alternatingFaceMapComplex D) ≫
      Functor.whiskerRight Idempotents.DoldKan.Γ.single₀Iso.inv
        ((SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D)).naturality f
    dsimp [constSection] at h
    rw [Functor.comp_map, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv,
      Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv]
    exact h

@[simp]
lemma Functor.doldPuppeFunctorSingle₀Inv_app [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) (X : C) :
    F.doldPuppeFunctorSingle₀Inv.app X = (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv := (rfl)

@[reassoc (attr := simp)]
lemma Functor.doldPuppeFunctorSingle₀Inv_comp_hom [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) :
    F.doldPuppeFunctorSingle₀Inv ≫ F.doldPuppeFunctorSingle₀Hom =
      𝟙 (F ⋙ ChainComplex.single₀ D) := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  have hL : (F.doldPuppeFunctorSingle₀Inv ≫ F.doldPuppeFunctorSingle₀Hom).app X =
      ((constSection (D := D)).app (F.obj X) ≫
          (alternatingFaceMapComplex D).map (Functor.constComp _ X F).inv ≫
          (alternatingFaceMapComplex D).map
            (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.inv.app X) F)) ≫
        ((alternatingFaceMapComplex D).map
            (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.hom.app X) F) ≫
          (alternatingFaceMapComplex D).map (Functor.constComp _ X F).hom ≫
          (constAugment (D := D)).app (F.obj X)) := by
    simp only [NatTrans.comp_app, Functor.doldPuppeFunctorSingle₀Inv_app,
      Functor.doldPuppeFunctorSingle₀Hom_app, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv,
      Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]; rfl
  rw [hL, NatTrans.id_app]; simp only [Category.assoc]
  have hSimp : (Functor.constComp _ X F).inv ≫
      Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.inv.app X) F ≫
      Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.hom.app X) F ≫
      (Functor.constComp _ X F).hom = 𝟙 ((SimplicialObject.const D).obj (F.obj X)) := by
    rw [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id_app]; simp
  rw [reassoc_of% (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hSimp,
    Functor.map_id] : (alternatingFaceMapComplex D).map (Functor.constComp _ X F).inv ≫
    (alternatingFaceMapComplex D).map
      (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.inv.app X) F) ≫
    (alternatingFaceMapComplex D).map
      (Functor.whiskerRight (Idempotents.DoldKan.Γ.single₀Iso.hom.app X) F) ≫
    (alternatingFaceMapComplex D).map (Functor.constComp _ X F).hom = 𝟙 _)]
  exact congrArg (·.app (F.obj X)) (constSection_comp_constAugment (D := D))

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom` in `F`. -/
lemma NatTrans.doldPuppeFunctorSingle₀HomotopyEquiv_hom_naturality
    [HasZeroObject C] [HasZeroObject D] {F G : C ⥤ D} (α : F ⟶ G) (X : C) :
    ((doldPuppe C D).map α).app ((ChainComplex.single₀ C).obj X) ≫
        (G.doldPuppeFunctorSingle₀HomotopyEquiv X).hom =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom ≫
        (ChainComplex.single₀ D).map (α.app X) := by
  have h := (Functor.whiskerRight (Functor.whiskerLeft (SimplicialObject.whiskering C D)
        ((evaluation (SimplicialObject C) (SimplicialObject D)).map
          (Idempotents.DoldKan.Γ.single₀Iso.hom.app X))) (alternatingFaceMapComplex D) ≫
      Functor.whiskerRight (single₀EvalConstCompIso (D := D) X).hom (alternatingFaceMapComplex D) ≫
      Functor.whiskerLeft ((evaluation C D).obj X) constAugment).naturality α
  dsimp [NatTrans.comp_app, single₀EvalConstCompIso, constAugment] at h
  rw [doldPuppe_map_app, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom,
    Functor.doldPuppeFunctorSingle₀HomotopyEquiv_hom]
  exact h

/-- Naturality of `(F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv` in `F`. -/
lemma NatTrans.doldPuppeFunctorSingle₀HomotopyEquiv_inv_naturality
    [HasZeroObject C] [HasZeroObject D] {F G : C ⥤ D} (α : F ⟶ G) (X : C) :
    (ChainComplex.single₀ D).map (α.app X) ≫
        (G.doldPuppeFunctorSingle₀HomotopyEquiv X).inv =
      (F.doldPuppeFunctorSingle₀HomotopyEquiv X).inv ≫
        ((doldPuppe C D).map α).app ((ChainComplex.single₀ C).obj X) := by
  have h := (Functor.whiskerLeft ((evaluation C D).obj X) constSection ≫
      Functor.whiskerRight (single₀EvalConstCompIso (D := D) X).inv (alternatingFaceMapComplex D) ≫
      Functor.whiskerRight (Functor.whiskerLeft (SimplicialObject.whiskering C D)
        ((evaluation (SimplicialObject C) (SimplicialObject D)).map
          (Idempotents.DoldKan.Γ.single₀Iso.inv.app X))) (alternatingFaceMapComplex D)).naturality α
  dsimp [single₀EvalConstCompIso, constSection] at h
  rw [doldPuppe_map_app, Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv,
    Functor.doldPuppeFunctorSingle₀HomotopyEquiv_inv]
  exact h

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
  dsimp only [Functor.doldPuppeFunctorConstHomotopyEquiv, HomotopyEquiv.trans, HomotopyEquiv.ofIso]
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
  dsimp only [Functor.doldPuppeFunctorConstHomotopyEquiv, HomotopyEquiv.trans, HomotopyEquiv.ofIso]
  rw [Functor.mapIso_inv, Iso.app_inv,
    SimplicialObject.Augmented.ExtraDegeneracy.const_homotopyEquiv_inv]

variable (C) in
/-- Natural transformation bundling the forward constant-functor comparison
`(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `K`. -/
def Functor.doldPuppeFunctorConstHom [HasZeroObject D] (B : D) :
    ((Functor.const C).obj B).doldPuppeFunctor ⟶
      (Functor.const (ChainComplex C ℕ)).obj ((ChainComplex.single₀ D).obj B) where
  app K := (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom
  naturality _ _ φ := by
    have h := ((constWhiskeringIso (C := C) B).hom ≫
      (Functor.const (ChainComplex C ℕ)).map ((constAugment (D := D)).app B)).naturality φ
    dsimp [NatTrans.comp_app, constWhiskeringIso, constAugment] at h
    rw [Functor.doldPuppeFunctorConstHomotopyEquiv_hom,
      Functor.doldPuppeFunctorConstHomotopyEquiv_hom]
    exact h

@[simp]
lemma Functor.doldPuppeFunctorConstHom_app [HasZeroObject D] (B : D) (K : ChainComplex C ℕ) :
    (Functor.doldPuppeFunctorConstHom C B).app K =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom := (rfl)

variable (C) in
/-- Natural transformation bundling the backward constant-functor comparison
`(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `K`. -/
def Functor.doldPuppeFunctorConstInv [HasZeroObject D] (B : D) :
    (Functor.const (ChainComplex C ℕ)).obj ((ChainComplex.single₀ D).obj B) ⟶
      ((Functor.const C).obj B).doldPuppeFunctor where
  app K := (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv
  naturality _ _ φ := by
    have h := ((Functor.const (ChainComplex C ℕ)).map ((constSection (D := D)).app B) ≫
      (constWhiskeringIso (C := C) B).inv).naturality φ
    dsimp [constWhiskeringIso, constSection] at h
    rw [Functor.doldPuppeFunctorConstHomotopyEquiv_inv,
      Functor.doldPuppeFunctorConstHomotopyEquiv_inv]
    exact h

@[simp]
lemma Functor.doldPuppeFunctorConstInv_app [HasZeroObject D] (B : D) (K : ChainComplex C ℕ) :
    (Functor.doldPuppeFunctorConstInv C B).app K =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv := (rfl)

@[reassoc (attr := simp)]
lemma Functor.doldPuppeFunctorConstInv_comp_hom [HasZeroObject D] (B : D) :
    Functor.doldPuppeFunctorConstInv C B ≫ Functor.doldPuppeFunctorConstHom C B =
      𝟙 ((Functor.const (ChainComplex C ℕ)).obj ((ChainComplex.single₀ D).obj B)) := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  change ((constSection (D := D)).app B ≫
      (alternatingFaceMapComplex D).map
        ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv.app B)) ≫
    ((alternatingFaceMapComplex D).map
        ((Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom.app B) ≫
      (constAugment (D := D)).app B) = 𝟙 ((ChainComplex.single₀ D).obj B)
  rw [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  exact congrArg (·.app B) (constSection_comp_constAugment (D := D))

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom` in `B`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_hom_naturality_left [HasZeroObject D]
    {B B' : D} (g : B ⟶ B') (K : ChainComplex C ℕ) :
    ((doldPuppe C D).map ((Functor.const C).map g)).app K ≫
        (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).hom =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom ≫ (ChainComplex.single₀ D).map g := by
  have h := (Functor.whiskerRight (Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).hom
    (alternatingFaceMapComplex D) ≫ constAugment).naturality g
  dsimp [NatTrans.comp_app, constAugment] at h
  rw [doldPuppe_map_app, Functor.doldPuppeFunctorConstHomotopyEquiv_hom,
    Functor.doldPuppeFunctorConstHomotopyEquiv_hom]
  exact h

/-- Naturality of `(Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv` in `B`. -/
lemma Functor.doldPuppeFunctorConstHomotopyEquiv_inv_naturality_left [HasZeroObject D]
    {B B' : D} (g : B ⟶ B') (K : ChainComplex C ℕ) :
    (ChainComplex.single₀ D).map g ≫ (Functor.doldPuppeFunctorConstHomotopyEquiv B' K).inv =
      (Functor.doldPuppeFunctorConstHomotopyEquiv B K).inv ≫
        ((doldPuppe C D).map ((Functor.const C).map g)).app K := by
  have h := (constSection ≫ Functor.whiskerRight
    (Functor.constCompWhiskeringLeftIso _ (Γ.obj K)).inv
    (alternatingFaceMapComplex D)).naturality g
  dsimp [constSection] at h
  rw [doldPuppe_map_app, Functor.doldPuppeFunctorConstHomotopyEquiv_inv,
    Functor.doldPuppeFunctorConstHomotopyEquiv_inv]
  exact h

end CategoryTheory
