/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative

/-!
# Functoriality of relative singular homology with local coefficients

A map of topological pairs `f : (X, A) ⟶ (Y, B)` and a local coefficient system `L` on `Y`
induce maps from the relative twisted chains and homology of `(X, A)` with coefficients in
`f⁎L` to those of `(Y, B)` with coefficients in `L`.  The construction descends the map on
ambient twisted chains through the quotient by the subspace chains.

The coefficient system on `A` obtained by first pulling `L` back to `X` and then restricting to
`A` is canonically isomorphic to the pullback to `A` of the restriction of `L` to `B`.  This
comparison makes the maps on subspace and ambient chains into a morphism of the short exact
sequences of a pair.  Consequently the relative map commutes with the connecting morphism in the
long exact sequence.

Together with `TauCeti.AlgebraicTopology.Singular.Twisted.Basic`, this supplies functoriality of
twisted singular homology for maps of spaces and maps of pairs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapters VII--VIII.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] {P Q : TopPair.{v}} (f : P ⟶ Q)
  (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)

/-- The ambient component of the identity map of a topological pair is the identity. -/
@[simp]
lemma Hom.fst_id (P : TopPair.{v}) : Hom.fst (𝟙 P) = 𝟙 P.fst :=
  rfl

/-- The ambient component of a composite map of topological pairs is the composite of the
ambient components. -/
@[simp]
lemma Hom.fst_comp {S : TopPair.{v}} (f : P ⟶ Q) (g : Q ⟶ S) :
    Hom.fst (f ≫ g) = Hom.fst f ≫ Hom.fst g :=
  rfl

/-- Restricting a pulled-back local coefficient system to the subspace agrees canonically with
pulling the restricted system back along the subspace component of a map of pairs. -/
def subspaceSystemPullbackIso :
    P.subspaceSystem ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ≅
      (LocalCoefficientSystem.pullback (Hom.snd f).hom).obj (Q.subspaceSystem L) :=
  ((LocalCoefficientSystem.pullbackCompIso P.map.hom (Hom.fst f).hom).app L).symm ≪≫
    eqToIso (congrArg (fun g : P.snd ⟶ Q.fst ↦
      (LocalCoefficientSystem.pullback g.hom).obj L) (Hom.w f).symm) ≪≫
    (LocalCoefficientSystem.pullbackCompIso (Hom.snd f).hom Q.map.hom).app L

/-- The map on twisted chains of the subspaces induced by a map of pairs.  Its source is first
identified with the pullback of the target subspace system. -/
def twistedSubspaceChainComplexMap :
    (P.subspaceSystem
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)).twistedChainComplex ⟶
      (Q.subspaceSystem L).twistedChainComplex :=
  LocalCoefficientSystem.twistedChainComplexCoefficientMap (subspaceSystemPullbackIso f L).hom ≫
    LocalCoefficientSystem.twistedChainComplexMap (Hom.snd f) (Q.subspaceSystem L)

/-- The maps induced by a map of pairs on subspace and ambient twisted chains form a commutative
square. -/
@[reassoc]
lemma twistedChainComplexMap_naturality_pair :
    LocalCoefficientSystem.twistedChainComplexMap P.map
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ≫
        LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L =
      twistedSubspaceChainComplexMap f L ≫
        LocalCoefficientSystem.twistedChainComplexMap Q.map L := by
  let e := LocalCoefficientSystem.pullbackCompIso (R := R) P.map.hom (Hom.fst f).hom
  have he : IsIso (LocalCoefficientSystem.twistedChainComplexCoefficientMap (e.hom.app L)) := by
    rw [← Iso.app_hom,
      ← LocalCoefficientSystem.twistedChainComplexCoefficientIso_hom]
    infer_instance
  let _ := he
  apply (cancel_epi (LocalCoefficientSystem.twistedChainComplexCoefficientMap (e.hom.app L))).1
  dsimp [e]
  rw [← LocalCoefficientSystem.twistedChainComplexMap_comp P.map (Hom.fst f) L]
  simp only [twistedSubspaceChainComplexMap, subspaceSystemPullbackIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc]
  rw [← LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp]
  rw [Iso.app_inv]
  simp only [← Category.assoc]
  rw [Iso.hom_inv_id_app, Category.id_comp]
  rw [LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp]
  simp only [Category.assoc]
  rw [Iso.app_hom]
  rw [← LocalCoefficientSystem.twistedChainComplexMap_comp (Hom.snd f) Q.map L]
  exact LocalCoefficientSystem.twistedChainComplexMap_congr
    (P.map ≫ Hom.fst f) L (Hom.w f).symm

/-- The map on relative twisted chain complexes induced by a map of topological pairs. -/
def twistedChainComplexMap :
    P.twistedChainComplex ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ⟶
      Q.twistedChainComplex L :=
  P.twistedChainComplexDesc _
    (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
      Q.twistedChainComplexπ L)
    (by
      calc
        _ = (LocalCoefficientSystem.twistedChainComplexMap P.map _ ≫
              LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L) ≫
            Q.twistedChainComplexπ L := Category.assoc _ _ _ |>.symm
        _ = (twistedSubspaceChainComplexMap f L ≫
              LocalCoefficientSystem.twistedChainComplexMap Q.map L) ≫
            Q.twistedChainComplexπ L := by
              rw [twistedChainComplexMap_naturality_pair]
        _ = twistedSubspaceChainComplexMap f L ≫
            (LocalCoefficientSystem.twistedChainComplexMap Q.map L ≫
              Q.twistedChainComplexπ L) := Category.assoc _ _ _
        _ = 0 := by rw [Q.twistedChainComplexMap_comp_twistedChainComplexπ, comp_zero])

/-- The relative twisted chain map is characterized by compatibility with the quotient maps from
the ambient twisted chain complexes. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_twistedChainComplexMap :
    P.twistedChainComplexπ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ≫
        twistedChainComplexMap f L =
      LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L ≫
        Q.twistedChainComplexπ L :=
  P.twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _

/-- The pullback along the ambient component of the identity map of a pair is canonically
isomorphic to the original coefficient system. -/
def fstPullbackIdIso (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) :
    (LocalCoefficientSystem.pullback (Hom.fst (𝟙 P)).hom).obj L ≅ L :=
  eqToIso (congrArg (fun k : P.fst ⟶ P.fst ↦
    (LocalCoefficientSystem.pullback k.hom).obj L)
      (Hom.fst_id P)) ≪≫
    (LocalCoefficientSystem.pullbackIdIso P.fst).app L

/-- The identity map of a pair induces the coefficient-change map coming from the canonical
identification of a system with its pullback along the identity. -/
@[simp]
lemma twistedChainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) :
    twistedChainComplexMap (𝟙 P) L =
      P.twistedChainComplexCoefficientMap (fstPullbackIdIso P L).hom := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst (𝟙 P)).hom).obj L))).1
  rw [twistedChainComplexπ_comp_twistedChainComplexMap,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap]
  congr 1
  rw [fstPullbackIdIso, Iso.trans_hom,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp]
  rw [LocalCoefficientSystem.twistedChainComplexMap_congr (Hom.fst (𝟙 P)) L
    (Hom.fst_id P),
    LocalCoefficientSystem.twistedChainComplexMap_id]
  rw [Iso.app_hom]

variable {S : TopPair.{v}} (g : Q ⟶ S)
  (K : LocalCoefficientSystem.{u, v, max v w} R S.fst)

/-- Pullback along the ambient component of a composite of pair maps agrees canonically with
iterated pullback along their ambient components. -/
def fstPullbackCompIso :
    (LocalCoefficientSystem.pullback (Hom.fst (f ≫ g)).hom).obj K ≅
      (LocalCoefficientSystem.pullback (Hom.fst f).hom).obj
        ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) :=
  eqToIso (congrArg (fun k : P.fst ⟶ S.fst ↦
    (LocalCoefficientSystem.pullback k.hom).obj K)
      (Hom.fst_comp f g)) ≪≫
    (LocalCoefficientSystem.pullbackCompIso (Hom.fst f).hom (Hom.fst g).hom).app K

/-- Maps of relative twisted chain complexes respect composition of maps of pairs, after the
canonical comparison between pullback along a composite and iterated pullback. -/
@[simp, reassoc]
lemma twistedChainComplexMap_comp :
    twistedChainComplexMap (f ≫ g) K =
      P.twistedChainComplexCoefficientMap (fstPullbackCompIso f g K).hom ≫
        twistedChainComplexMap f
          ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) ≫
        twistedChainComplexMap g K := by
  apply (cancel_epi (P.twistedChainComplexπ
    ((LocalCoefficientSystem.pullback (Hom.fst (f ≫ g)).hom).obj K))).1
  rw [twistedChainComplexπ_comp_twistedChainComplexMap,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    twistedChainComplexπ_comp_twistedChainComplexMap]
  simp only [fstPullbackCompIso, Iso.trans_hom,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp]
  rw [LocalCoefficientSystem.twistedChainComplexMap_congr (Hom.fst (f ≫ g)) K
    (Hom.fst_comp f g),
    LocalCoefficientSystem.twistedChainComplexMap_comp]
  simp only [Iso.app_hom, Category.assoc]

/-- The morphism between the short exact sequences of twisted chains induced by a map of
topological pairs. -/
def twistedChainComplexShortComplexMap :
    P.twistedChainComplexShortComplex
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) ⟶
      Q.twistedChainComplexShortComplex L :=
  ShortComplex.homMk (twistedSubspaceChainComplexMap f L)
    (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L)
    (twistedChainComplexMap f L)
    (twistedChainComplexMap_naturality_pair f L).symm
    (twistedChainComplexπ_comp_twistedChainComplexMap f L).symm

@[simp]
lemma twistedChainComplexShortComplexMap_τ₁ :
    (twistedChainComplexShortComplexMap f L).τ₁ = twistedSubspaceChainComplexMap f L :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexMap_τ₂ :
    (twistedChainComplexShortComplexMap f L).τ₂ =
      LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L :=
  (rfl)

@[simp]
lemma twistedChainComplexShortComplexMap_τ₃ :
    (twistedChainComplexShortComplexMap f L).τ₃ = twistedChainComplexMap f L :=
  (rfl)

/-- The map on relative twisted singular homology induced by a map of topological pairs. -/
abbrev twistedHomologyMap (k : ℕ) :
    P.twistedHomology ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k ⟶
      Q.twistedHomology L k :=
  HomologicalComplex.homologyMap (twistedChainComplexMap f L) k

/-- The quotient maps from ambient to relative twisted homology are natural in maps of
topological pairs. -/
@[reassoc (attr := simp)]
lemma twistedHomologyπ_naturality (k : ℕ) :
    LocalCoefficientSystem.twistedHomologyMap (Hom.fst f) L k ≫
        Q.twistedHomologyπ L k =
      P.twistedHomologyπ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) k ≫
        twistedHomologyMap f L k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    twistedChainComplexπ_comp_twistedChainComplexMap]

/-- The identity law for maps on relative twisted homology. -/
@[simp]
lemma twistedHomologyMap_id
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : ℕ) :
    twistedHomologyMap (𝟙 P) L k =
      P.twistedHomologyCoefficientMap (fstPullbackIdIso P L).hom k :=
  congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
    (twistedChainComplexMap_id L)

/-- The composition law for maps on relative twisted homology. -/
@[simp, reassoc]
lemma twistedHomologyMap_comp (k : ℕ) :
    twistedHomologyMap (f ≫ g) K k =
      P.twistedHomologyCoefficientMap (fstPullbackCompIso f g K).hom k ≫
        twistedHomologyMap f ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj K) k ≫
        twistedHomologyMap g K k :=
  (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
      (twistedChainComplexMap_comp f g K)).trans
    (by rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp])

/-- The homology map induced by the map on subspace chains is the coefficient comparison followed
by the map induced by the subspace component. -/
lemma homologyMap_twistedSubspaceChainComplexMap (k : ℕ) :
    HomologicalComplex.homologyMap (twistedSubspaceChainComplexMap f L) k =
      LocalCoefficientSystem.twistedHomologyCoefficientMap
          (subspaceSystemPullbackIso f L).hom k ≫
        LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) k := by
  rw [twistedSubspaceChainComplexMap, HomologicalComplex.homologyMap_comp]

/-- The connecting morphism in relative twisted homology is natural in maps of topological
pairs. -/
@[reassoc]
lemma twistedHomologyδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomologyδ ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L) n m h ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
            (subspaceSystemPullbackIso f L).hom m ≫
          LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) m =
      twistedHomologyMap f L n ≫ Q.twistedHomologyδ L n m h :=
  by
    have hδ := HomologicalComplex.HomologySequence.δ_naturality
      (twistedChainComplexShortComplexMap f L)
      (P.shortExact_twistedChainComplexShortComplex _)
      (Q.shortExact_twistedChainComplexShortComplex L) n m (by simpa)
    rw [twistedChainComplexShortComplexMap_τ₁,
      twistedChainComplexShortComplexMap_τ₃,
      homologyMap_twistedSubspaceChainComplexMap] at hδ
    exact hδ

end TopPair
