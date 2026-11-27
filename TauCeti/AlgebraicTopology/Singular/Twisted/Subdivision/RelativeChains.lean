/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Subdivision.Basic

/-!
# Relative barycentric subdivision with local coefficients

`TopPair.twistedSubdivisionChainMap` and `TopPair.twistedSubdivisionHomotopy` descend
the ambient subdivision and prism of `LocalCoefficientSystem` through the relative cokernel.
They are natural in pairs and local coefficients, and subdivision induces the identity on
relative homology compatibly with the pair sequence (Hatcher, *Algebraic Topology*, §2.1,
proof of Proposition 2.21, and §3.H).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti

namespace TopPair

variable {R : Type u} [Ring R] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- Barycentric subdivision on the relative twisted chains of a pair. -/
def twistedSubdivisionChainMap : P.twistedChainComplex L ⟶ P.twistedChainComplex L :=
  P.twistedChainComplexDesc L (L.twistedSubdivisionChainMap ≫ P.twistedChainComplexπ L) (by
    rw [← Category.assoc,
      LocalCoefficientSystem.twistedChainComplexMap_comp_twistedSubdivisionChainMap,
      Category.assoc, twistedChainComplexMap_comp_twistedChainComplexπ, comp_zero])

/-- Relative subdivision sends the class of an ambient chain to the class of its subdivision. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_twistedSubdivisionChainMap :
    P.twistedChainComplexπ L ≫ P.twistedSubdivisionChainMap L =
      L.twistedSubdivisionChainMap ≫ P.twistedChainComplexπ L :=
  P.twistedChainComplexπ_comp_twistedChainComplexDesc L _ _

/-- In each degree, relative subdivision descends the ambient subdivision map. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_f_comp_twistedSubdivisionChainMap_f (n : ℕ) :
    (P.twistedChainComplexπ L).f n ≫ (P.twistedSubdivisionChainMap L).f n =
      L.twistedSubdivisionChainMap.f n ≫ (P.twistedChainComplexπ L).f n := by
  simpa only [HomologicalComplex.comp_f] using
    congrArg (fun g ↦ g.f n) (P.twistedChainComplexπ_comp_twistedSubdivisionChainMap L)

/-- Relative subdivision computes on any ambient chain representative. -/
@[simp]
lemma twistedSubdivisionChainMap_f_apply {n : ℕ} (c : L.twistedChainComplex.X n) :
    (P.twistedSubdivisionChainMap L).f n ((P.twistedChainComplexπ L).f n c) =
      (P.twistedChainComplexπ L).f n (L.twistedSubdivisionChainMap.f n c) :=
  ConcreteCategory.congr_hom (P.twistedChainComplexπ_f_comp_twistedSubdivisionChainMap_f L n) c

local instance (n : ℕ) : Epi ((P.twistedChainComplexπ L).f n) :=
  (ModuleCat.epi_iff_surjective _).2 (P.twistedChainComplexπ_f_surjective L)

/-- The relative subdivision prism sends a chain class to the class of its ambient prism. -/
def twistedPrismX (n : ℕ) :
    (P.twistedChainComplex L).X n ⟶ (P.twistedChainComplex L).X (n + 1) :=
  (P.isColimitCokernelCoforkTwistedChainComplexX L n).desc
    (CokernelCofork.ofπ (L.twistedPrismX n ≫ (P.twistedChainComplexπ L).f (n + 1)) (by
      rw [← Category.assoc, LocalCoefficientSystem.twistedChainComplexMap_f_comp_twistedPrismX,
        Category.assoc, twistedChainComplex_condition_f, comp_zero]))

/-- The relative prism agrees with the ambient prism after projection to relative chains. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_f_comp_twistedPrismX (n : ℕ) :
    (P.twistedChainComplexπ L).f n ≫ P.twistedPrismX L n =
      L.twistedPrismX n ≫ (P.twistedChainComplexπ L).f (n + 1) :=
  (P.isColimitCokernelCoforkTwistedChainComplexX L n).fac _ WalkingParallelPair.one

/-- The relative prism computes on any ambient chain representative. -/
@[simp]
lemma twistedPrismX_apply {n : ℕ} (c : L.twistedChainComplex.X n) :
    P.twistedPrismX L n ((P.twistedChainComplexπ L).f n c) =
      (P.twistedChainComplexπ L).f (n + 1) (L.twistedPrismX n c) :=
  ConcreteCategory.congr_hom (P.twistedChainComplexπ_f_comp_twistedPrismX L n) c

/-- The relative twisted prism is a homotopy from the identity to barycentric subdivision. -/
def twistedSubdivisionHomotopy :
    _root_.Homotopy (𝟙 (P.twistedChainComplex L)) (P.twistedSubdivisionChainMap L) :=
  _root_.Homotopy.equivSubZero.symm <| _root_.Homotopy.mkChainComplex _ (P.twistedPrismX L)
    (by
      rw [← cancel_epi ((P.twistedChainComplexπ L).f 0)]
      simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
        Preadditive.comp_sub, Category.comp_id, twistedChainComplexπ_f_comp_twistedPrismX_assoc,
        twistedChainComplexπ_f_comp_twistedSubdivisionChainMap_f,
        LocalCoefficientSystem.twistedSubdivisionChainMap_f,
        LocalCoefficientSystem.twistedSubdivisionX_zero, LocalCoefficientSystem.twistedPrismX_zero,
        Category.id_comp, sub_self, zero_comp])
    (fun n ↦ by
      rw [← cancel_epi ((P.twistedChainComplexπ L).f (n + 1))]
      simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
        Preadditive.comp_sub, Category.comp_id,
        twistedChainComplexπ_f_comp_twistedSubdivisionChainMap_f,
        Preadditive.comp_add, LocalCoefficientSystem.twistedSubdivisionChainMap_f]
      -- Move the quotient past the two terms of the ambient homotopy identity.
      rw [(P.twistedChainComplexπ L).comm_assoc,
        twistedChainComplexπ_f_comp_twistedPrismX_assoc,
        twistedChainComplexπ_f_comp_twistedPrismX,
        (P.twistedChainComplexπ L).comm, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
        LocalCoefficientSystem.twistedPrismX_boundary_add_boundary_twistedPrismX,
        Preadditive.sub_comp, Category.id_comp])

/-- The successor-degree component of the relative subdivision homotopy is the relative prism. -/
@[simp]
lemma twistedSubdivisionHomotopy_hom (n : ℕ) :
    (P.twistedSubdivisionHomotopy L).hom n (n + 1) = P.twistedPrismX L n :=
  _root_.Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-- Barycentric subdivision induces the identity on relative homology with local coefficients. -/
@[simp]
lemma homologyMap_twistedSubdivisionChainMap (n : ℕ) :
    HomologicalComplex.homologyMap (P.twistedSubdivisionChainMap L) n = 𝟙 _ := by
  rw [← (P.twistedSubdivisionHomotopy L).homologyMap_eq n, HomologicalComplex.homologyMap_id]

/-- Subdivision commutes with the connecting morphism of the pair. -/
@[reassoc]
lemma twistedHomologyδ_naturality_subdivision (m : ℕ) :
    P.twistedHomologyδ L (m + 1) m ≫
        HomologicalComplex.homologyMap (P.subspaceSystem L).twistedSubdivisionChainMap m =
      HomologicalComplex.homologyMap (P.twistedSubdivisionChainMap L) (m + 1) ≫
        P.twistedHomologyδ L (m + 1) m := by
  let S := P.twistedChainComplexShortComplex L
  let sd : S ⟶ S :=
    ShortComplex.homMk (P.subspaceSystem L).twistedSubdivisionChainMap
      L.twistedSubdivisionChainMap (P.twistedSubdivisionChainMap L)
      (LocalCoefficientSystem.twistedChainComplexMap_comp_twistedSubdivisionChainMap P.map L).symm
      (P.twistedChainComplexπ_comp_twistedSubdivisionChainMap L).symm
  exact HomologicalComplex.HomologySequence.δ_naturality sd
    (P.shortExact_twistedChainComplexShortComplex L)
    (P.shortExact_twistedChainComplexShortComplex L) (m + 1) m (by simp)

variable {P} {Q : TopPair.{v}} (f : P ⟶ Q)
  (K : LocalCoefficientSystem.{u, v, max v w} R Q.fst)

/-- Relative twisted subdivision is natural under maps of pairs with pulled-back coefficients. -/
@[reassoc]
lemma twistedChainComplexMap_comp_twistedSubdivisionChainMap :
    twistedChainComplexMap f K ≫ Q.twistedSubdivisionChainMap K =
      P.twistedSubdivisionChainMap ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K) ≫
        twistedChainComplexMap f K := by
  apply P.twistedChainComplex_hom_ext
  simp only [twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    twistedChainComplexπ_comp_twistedSubdivisionChainMap_assoc,
    twistedChainComplexπ_comp_twistedSubdivisionChainMap,
    twistedChainComplexπ_comp_twistedChainComplexMap,
    LocalCoefficientSystem.twistedChainComplexMap_comp_twistedSubdivisionChainMap_assoc]

/-- The relative twisted prism is natural under maps of pairs with pulled-back coefficients. -/
@[reassoc]
lemma twistedChainComplexMap_f_comp_twistedPrismX (n : ℕ) :
    (twistedChainComplexMap f K).f n ≫ Q.twistedPrismX K n =
      P.twistedPrismX ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K) n ≫
        (twistedChainComplexMap f K).f (n + 1) := by
  have h (i : ℕ) := congrArg (fun g ↦ g.f i) (twistedChainComplexπ_comp_twistedChainComplexMap f K)
  simp only [HomologicalComplex.comp_f] at h
  rw [← cancel_epi ((P.twistedChainComplexπ _).f n), reassoc_of% h n,
    twistedChainComplexπ_f_comp_twistedPrismX, twistedChainComplexπ_f_comp_twistedPrismX_assoc,
    h, LocalCoefficientSystem.twistedChainComplexMap_f_comp_twistedPrismX_assoc]

variable (P) {L}
  {M : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L ⟶ M)

/-- Relative twisted subdivision is natural in the local coefficient system. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_comp_twistedSubdivisionChainMap :
    P.twistedChainComplexCoefficientMap η ≫ P.twistedSubdivisionChainMap M =
      P.twistedSubdivisionChainMap L ≫ P.twistedChainComplexCoefficientMap η := by
  apply P.twistedChainComplex_hom_ext
  simp only [twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_comp_twistedSubdivisionChainMap_assoc,
    twistedChainComplexπ_comp_twistedSubdivisionChainMap,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_comp_twistedSubdivisionChainMap_assoc]

/-- The relative twisted prism is natural in the local coefficient system. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_f_comp_twistedPrismX (n : ℕ) :
    (P.twistedChainComplexCoefficientMap η).f n ≫ P.twistedPrismX M n =
      P.twistedPrismX L n ≫ (P.twistedChainComplexCoefficientMap η).f (n + 1) := by
  have h (i : ℕ) :=
    congrArg (fun g ↦ g.f i) (P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)
  simp only [HomologicalComplex.comp_f] at h
  rw [← cancel_epi ((P.twistedChainComplexπ L).f n), reassoc_of% h n,
    twistedChainComplexπ_f_comp_twistedPrismX, twistedChainComplexπ_f_comp_twistedPrismX_assoc,
    h, LocalCoefficientSystem.twistedChainComplexCoefficientMap_f_comp_twistedPrismX_assoc]

end TopPair
