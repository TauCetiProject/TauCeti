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
abbrev Functor.doldPuppeFunctor (F : C ⥤ D) : ChainComplex C ℕ ⥤ ChainComplex D ℕ :=
  Γ ⋙ (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D

lemma Functor.doldPuppeFunctor_obj (F : C ⥤ D) (K : ChainComplex C ℕ) :
    F.doldPuppeFunctor.obj K =
      (alternatingFaceMapComplex D).obj
        (((SimplicialObject.whiskering C D).obj F).obj (Γ.obj K)) := (rfl)

lemma Functor.doldPuppeFunctor_map (F : C ⥤ D) {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    F.doldPuppeFunctor.map f =
      (alternatingFaceMapComplex D).map
        (((SimplicialObject.whiskering C D).obj F).map (Γ.map f)) := (rfl)

/-- Naturality of `Functor.doldPuppeFunctor` with respect to a natural transformation
`α : F ⟶ G`. -/
def NatTrans.doldPuppeFunctor {F G : C ⥤ D} (α : F ⟶ G) :
    F.doldPuppeFunctor ⟶ G.doldPuppeFunctor :=
  Functor.whiskerLeft Γ
    (Functor.whiskerRight ((SimplicialObject.whiskering C D).map α) (alternatingFaceMapComplex D))

@[simp]
lemma NatTrans.doldPuppeFunctor_app_f {F G : C ⥤ D} (α : F ⟶ G) (K : ChainComplex C ℕ) (n : ℕ) :
    ((NatTrans.doldPuppeFunctor α).app K).f n = α.app ((Γ.obj K) _⦋n⦌) := (rfl)

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
  dsimp [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor]; simp

@[simp]
lemma Functor.doldPuppeMapHomotopyEquiv_inv (F : C ⥤ D) {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) :
    (F.doldPuppeMapHomotopyEquiv e).inv = F.doldPuppeFunctor.map e.inv := by
  dsimp [Functor.doldPuppeMapHomotopyEquiv, Functor.doldPuppeFunctor]; simp

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

/-- When `F : C ⥤ D` is additive and `D` has homology, the comparison chain map from
`F.doldPuppeFunctor.obj K` to `(F.mapHomologicalComplex (.down ℕ)).obj K` is a
quasi-isomorphism. -/
instance Functor.quasiIso_doldPuppeFunctorAdditiveHomotopyEquiv_hom [CategoryWithHomology D]
    (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    QuasiIso (F.doldPuppeFunctorAdditiveHomotopyEquiv K).hom :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (F.doldPuppeFunctorAdditiveHomotopyEquiv K).homotopyEquivalences_hom

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
    ((SimplicialObject.whiskering C D).obj F).mapIso (Γ.single₀Iso X) ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl (F.obj X)) (fun _ ↦ by dsimp; simp)
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso isoSimp)).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const (F.obj X)).homotopyEquiv

instance Functor.quasiIso_doldPuppeFunctorSingle₀HomotopyEquiv_hom
    [HasZeroObject C] [HasZeroObject D] [CategoryWithHomology D] (F : C ⥤ D) (X : C) :
    QuasiIso (F.doldPuppeFunctorSingle₀HomotopyEquiv X).hom :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (F.doldPuppeFunctorSingle₀HomotopyEquiv X).homotopyEquivalences_hom

/-- **Constant non-additive functor law**: for any object `B : D` and any chain complex
`K : ChainComplex C ℕ` (including `K = 0`), `((Functor.const C).obj B).doldPuppeFunctor.obj K` is
canonically chain homotopy equivalent to `(ChainComplex.single₀ D).obj B`. -/
def Functor.doldPuppeFunctorConstHomotopyEquiv [HasZeroObject D] (B : D) (K : ChainComplex C ℕ) :
    HomotopyEquiv (((Functor.const C).obj B).doldPuppeFunctor.obj K)
      ((ChainComplex.single₀ D).obj B) :=
  let isoSimp : ((SimplicialObject.whiskering C D).obj ((Functor.const C).obj B)).obj (Γ.obj K) ≅
      (SimplicialObject.const D).obj B :=
    NatIso.ofComponents (fun _ ↦ Iso.refl B) (fun _ ↦ by dsimp)
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso isoSimp)).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv

instance Functor.quasiIso_doldPuppeFunctorConstHomotopyEquiv_hom
    [HasZeroObject D] [CategoryWithHomology D] (B : D) (K : ChainComplex C ℕ) :
    QuasiIso (Functor.doldPuppeFunctorConstHomotopyEquiv B K).hom :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (Functor.doldPuppeFunctorConstHomotopyEquiv B K).homotopyEquivalences_hom

end CategoryTheory
