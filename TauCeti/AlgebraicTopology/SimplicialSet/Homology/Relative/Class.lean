/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.One
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero

/-!
# Relative classes of `1`-simplices

For a pair of simplicial sets `Q` (a monomorphism `Q.left ⟶ Q.right`), a `1`-simplex `s` of
`Q.right` whose two faces lie in `Q.left` is a relative cycle, and so has a class
`SSetPair.relClass₁ R Q s v₀ v₁ h₀ h₁ : R ⟶ Q.homology R 1` in relative homology with coefficients
in `R`. This file computes its image under the connecting morphism, the difference
`[v₁] - [v₀]` of the classes of its endpoints (`SSetPair.relClass₁_homologyδ`); proves that the
class is natural in maps of pairs (`SSetPair.relClass₁_homologyMap`); and identifies it with the
image of the absolute class `TauCeti.SSet.ιHomology₁` (in `SimplicialSet/Homology/One.lean`) when
the two faces agree (`SSetPair.ιHomology₁_homologyπ`). The computation of the connecting morphism
is `ShortComplex.ShortExact.δ_eq` for the short exact sequence of chain complexes of the pair.

With coproducts available, the relative cycle needs only preadditive coefficients. Its class
and naturality also require a category with homology. The connecting-morphism calculation uses
abelian coefficients.

## Main definitions and results

* `SSetPair.relClass₁`: the relative class of a `1`-simplex with faces in the subcomplex.
* `SSetPair.relClass₁_homologyδ`: its image under the connecting morphism.
* `SSetPair.relClass₁_homologyMap`: naturality in maps of pairs.
* `SSetPair.ιHomology₁_homologyπ`: the image in relative homology of the absolute class of a
  `1`-simplex with equal faces.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] (R : C)
  (Q : SSetPair.{w}) (s : Q.right _⦋1⦌) (v₀ v₁ : Q.left _⦋0⦌)
  (h₀ : Q.right.δ 1 s = Q.hom.app _ v₀) (h₁ : Q.right.δ 0 s = Q.hom.app _ v₁)

section

variable [Preadditive C]

/-- The chain of a vertex in the subcomplex vanishes in relative chains. -/
-- Explicit functors in `app` keep the identity functors in `Q.hom` out of the simp pattern.
@[reassoc (attr := simp)]
lemma ιChainComplex_hom_app_comp_chainComplexπ (v : Q.left _⦋0⦌) :
    Q.right.ιChainComplex (R := R) (Q.hom.app (F := Q.left) (G := Q.right) _ v) ≫
      (Q.chainComplexπ R).f 0 = 0 := by
  rw [← SSet.ι_chainComplexMap_f Q.left Q.right Q.hom R v, Category.assoc]
  simp

include h₀ h₁ in
/-- A simplex whose endpoints lie in the subcomplex defines a relative cycle. -/
lemma relClass₁_cycle :
    (Q.right.ιChainComplex (R := R) s ≫ (Q.chainComplexπ R).f 1) ≫ (Q.chainComplex R).d 1 0 =
      0 := by
  rw [Category.assoc, (Q.chainComplexπ R).comm, ← Category.assoc, SSet.ιChainComplex_d,
    Fin.sum_univ_two, h₀, h₁]
  simp

variable [CategoryWithHomology C]

/-- The relative homology class of a `1`-simplex of the ambient simplicial set whose two faces
lie in the subcomplex. -/
def relClass₁ : R ⟶ Q.homology R 1 :=
  (Q.chainComplex R).liftCycles (Q.right.ιChainComplex s ≫ (Q.chainComplexπ R).f 1) 0
    (by simp) (relClass₁_cycle R Q s v₀ v₁ h₀ h₁) ≫ (Q.chainComplex R).homologyπ 1

/-- The relative class of a `1`-simplex is the homology class of the relative cycle it defines. -/
lemma relClass₁_eq :
    relClass₁ R Q s v₀ v₁ h₀ h₁ =
      (Q.chainComplex R).liftCycles (Q.right.ιChainComplex s ≫ (Q.chainComplexπ R).f 1) 0
        (by simp) (relClass₁_cycle R Q s v₀ v₁ h₀ h₁) ≫ (Q.chainComplex R).homologyπ 1 := by
  rw [relClass₁]

variable {Q} in
/-- A map of pairs carries a face of a `1`-simplex lying in the subcomplex to a face lying in the
subcomplex. -/
lemma δ_map_eq {Q' : SSetPair.{w}} (f : Q ⟶ Q') (i : Fin 2) (v : Q.left _⦋0⦌)
    (h : Q.right.δ i s = Q.hom.app _ v) :
    Q'.right.δ i (f.right.app _ s) = Q'.hom.app _ (f.left.app _ v) := by
  rw [← SSet.δ_naturality_apply, h]
  exact congr($(Arrow.w f.hom).app (Opposite.op ⦋0⦌) v).symm

variable {Q} in
/-- **Naturality of the relative class of a `1`-simplex** in maps of pairs. -/
@[reassoc (attr := simp)]
lemma relClass₁_homologyMap {Q' : SSetPair.{w}} (f : Q ⟶ Q') :
    relClass₁ R Q s v₀ v₁ h₀ h₁ ≫ SSetPair.homologyMap f R 1 =
      relClass₁ R Q' (f.right.app _ s) (f.left.app _ v₀) (f.left.app _ v₁)
        (δ_map_eq s f 1 v₀ h₀) (δ_map_eq s f 0 v₁ h₁) := by
  rw [relClass₁, relClass₁, Category.assoc, SSetPair.homologyMap,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 2
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← chainComplexπ_naturality,
    HomologicalComplex.comp_f, ← Category.assoc, SSet.ι_chainComplexMap_f]

/-- The relative class of a `1`-simplex whose two faces agree is the image of its absolute
class. -/
lemma ιHomology₁_homologyπ (h : Q.right.δ 0 s = Q.right.δ 1 s) :
    TauCeti.SSet.ιHomology₁ R Q.right s h ≫ Q.homologyπ R 1 = relClass₁ R Q s v₀ v₁ h₀ h₁ := by
  rw [TauCeti.SSet.ιHomology₁_eq, relClass₁, Category.assoc, SSetPair.homologyπ,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

end

variable [Abelian C]

/-- **The connecting morphism on the relative class of a `1`-simplex** is the difference of the
classes of its two vertices in the subcomplex. -/
@[reassoc (attr := simp)]
lemma relClass₁_homologyδ :
    relClass₁ R Q s v₀ v₁ h₀ h₁ ≫ Q.homologyδ R 1 0 =
      TauCeti.SSet.ιHomology₀ R v₁ - TauCeti.SSet.ιHomology₀ R v₀ := by
  have hx₁ : (Q.left.ιChainComplex (R := R) v₁ - Q.left.ιChainComplex v₀) ≫
      (SSet.chainComplexMap Q.hom R).f 0 =
        Q.right.ιChainComplex s ≫ (Q.right.chainComplex R).d 1 0 := by
    rw [SSet.ιChainComplex_d, Fin.sum_univ_two, h₀, h₁, Preadditive.sub_comp,
      SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
    simp [sub_eq_add_neg]
  have := (Q.shortExact_chainComplexShortComplex R).δ_eq 1 0 (by simp)
    (Q.right.ιChainComplex s ≫ (Q.chainComplexπ R).f 1) (relClass₁_cycle R Q s v₀ v₁ h₀ h₁)
    (Q.right.ιChainComplex s) rfl _ hx₁ 0 (by simp)
  rw [relClass₁, Category.assoc]
  refine this.trans ?_
  rw [TauCeti.SSet.ιHomology₀_eq, TauCeti.SSet.ιHomology₀_eq, ← Preadditive.sub_comp]
  congr 1
  rw [← cancel_mono ((Q.left.chainComplex R).iCycles 0)]
  simp

end SSetPair
