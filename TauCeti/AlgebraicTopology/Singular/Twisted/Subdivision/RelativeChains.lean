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

`TopPair.twistedSubdivisionChainMap` and `TopPair.twistedSubdivisionHomotopy` descend the
ambient subdivision and prism of `LocalCoefficientSystem` using `TopPair.twistedChainComplexDesc`
and `Homotopy.descCokernel`.
In positive degrees, `TopPair.twistedPrismX_boundary_add_boundary_twistedPrismX` gives
the relative prism identity `∂T + T∂ = id - Sd` from `Homotopy.comm`.
Both operators are natural in pairs and local coefficients, and subdivision induces the identity on
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
      L.twistedSubdivisionChainMap.f n ≫ (P.twistedChainComplexπ L).f n :=
  HomologicalComplex.congr_hom (P.twistedChainComplexπ_comp_twistedSubdivisionChainMap L) n

/-- Relative subdivision computes on any ambient chain representative. -/
@[simp]
lemma twistedSubdivisionChainMap_f_apply {n : ℕ} (c : L.twistedChainComplex.X n) :
    (P.twistedSubdivisionChainMap L).f n ((P.twistedChainComplexπ L).f n c) =
      (P.twistedChainComplexπ L).f n (L.twistedSubdivisionChainMap.f n c) :=
  ConcreteCategory.congr_hom (P.twistedChainComplexπ_f_comp_twistedSubdivisionChainMap_f L n) c

/-- Relative barycentric subdivision fixes degree-zero chains. -/
@[simp]
lemma twistedSubdivisionChainMap_f_zero : (P.twistedSubdivisionChainMap L).f 0 = 𝟙 _ := by
  rw [← cancel_epi ((P.twistedChainComplexπ L).f 0)]
  simp only [twistedChainComplexπ_f_comp_twistedSubdivisionChainMap_f,
    LocalCoefficientSystem.twistedSubdivisionChainMap_f,
    LocalCoefficientSystem.twistedSubdivisionX_zero, Category.id_comp, Category.comp_id]

/-- The relative twisted prism is a homotopy from the identity to barycentric subdivision. -/
def twistedSubdivisionHomotopy :
    _root_.Homotopy (𝟙 (P.twistedChainComplex L)) (P.twistedSubdivisionChainMap L) :=
  _root_.Homotopy.descCokernel L.twistedSubdivisionHomotopy
    (LocalCoefficientSystem.twistedChainComplexMap P.map L)
    (P.twistedChainComplexπ L) (P.twistedChainComplexπ L) (P.twistedChainComplex_condition_f L)
    (P.isColimitCokernelCoforkTwistedChainComplexX L)
    (fun i j ↦ by
      by_cases hij : i + 1 = j
      · subst j
        simp only [LocalCoefficientSystem.twistedSubdivisionHomotopy_hom,
          LocalCoefficientSystem.twistedChainComplexMap_f_comp_twistedPrismX_assoc,
          twistedChainComplex_condition_f, comp_zero]
      · rw [(L.twistedSubdivisionHomotopy).zero i j (by simpa using hij), zero_comp, comp_zero])
    (by simp only [Category.comp_id, Category.id_comp])
    (P.twistedChainComplexπ_comp_twistedSubdivisionChainMap L)

/-- The relative subdivision prism sends a chain class to the class of its ambient prism. -/
def twistedPrismX (n : ℕ) : (P.twistedChainComplex L).X n ⟶ (P.twistedChainComplex L).X (n + 1) :=
  (P.twistedSubdivisionHomotopy L).hom n (n + 1)

/-- The successor-degree component of the relative subdivision homotopy is the relative prism
`twistedPrismX` by definition. -/
@[simp]
lemma twistedSubdivisionHomotopy_hom (n : ℕ) :
    (P.twistedSubdivisionHomotopy L).hom n (n + 1) = P.twistedPrismX L n := (rfl)

/-- The relative prism agrees with the ambient prism after projection to relative chains. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_f_comp_twistedPrismX (n : ℕ) :
    (P.twistedChainComplexπ L).f n ≫ P.twistedPrismX L n =
      L.twistedPrismX n ≫ (P.twistedChainComplexπ L).f (n + 1) := by
  rw [← twistedSubdivisionHomotopy_hom, twistedSubdivisionHomotopy,
    _root_.Homotopy.π_descCokernel_hom, LocalCoefficientSystem.twistedSubdivisionHomotopy_hom]

/-- The relative subdivision prism vanishes in degree zero. -/
@[simp]
lemma twistedPrismX_zero : P.twistedPrismX L 0 = 0 := by
  rw [← cancel_epi ((P.twistedChainComplexπ L).f 0)]
  simp only [twistedChainComplexπ_f_comp_twistedPrismX,
    LocalCoefficientSystem.twistedPrismX_zero, zero_comp, comp_zero]

/-- The relative prism computes on any ambient chain representative. -/
@[simp]
lemma twistedPrismX_apply {n : ℕ} (c : L.twistedChainComplex.X n) :
    P.twistedPrismX L n ((P.twistedChainComplexπ L).f n c) =
      (P.twistedChainComplexπ L).f (n + 1) (L.twistedPrismX n c) :=
  ConcreteCategory.congr_hom (P.twistedChainComplexπ_f_comp_twistedPrismX L n) c

/-- In positive degrees, the relative twisted prism satisfies `∂T + T∂ = id - Sd`. -/
lemma twistedPrismX_boundary_add_boundary_twistedPrismX (n : ℕ) :
    (P.twistedChainComplex L).d (n + 1) n ≫ P.twistedPrismX L n +
        P.twistedPrismX L (n + 1) ≫ (P.twistedChainComplex L).d (n + 2) (n + 1) =
      𝟙 _ - (P.twistedSubdivisionChainMap L).f (n + 1) := by
  rw [eq_sub_iff_add_eq]
  simpa only [← twistedSubdivisionHomotopy_hom, Homotopy.dNext_succ_chainComplex,
    Homotopy.prevD_chainComplex, HomologicalComplex.id_f] using
      ((P.twistedSubdivisionHomotopy L).comm (n + 1)).symm

/-- Barycentric subdivision induces the identity on relative homology with local coefficients. -/
@[simp]
lemma homologyMap_twistedSubdivisionChainMap (n : ℕ) :
    HomologicalComplex.homologyMap (P.twistedSubdivisionChainMap L) n = 𝟙 _ := by
  rw [← (P.twistedSubdivisionHomotopy L).homologyMap_eq n, HomologicalComplex.homologyMap_id]

/-- Subdivision commutes with the connecting morphism of the pair from degree `n` to degree `m`,
where `m + 1 = n`. -/
@[reassoc]
lemma twistedHomologyδ_naturality_subdivision (n m : ℕ) (h : m + 1 = n := by lia) :
    P.twistedHomologyδ L n m h ≫
        HomologicalComplex.homologyMap (P.subspaceSystem L).twistedSubdivisionChainMap m =
      HomologicalComplex.homologyMap (P.twistedSubdivisionChainMap L) n ≫
        P.twistedHomologyδ L n m h := by
  let S := P.twistedChainComplexShortComplex L
  let sd : S ⟶ S :=
    ShortComplex.homMk (P.subspaceSystem L).twistedSubdivisionChainMap
      L.twistedSubdivisionChainMap (P.twistedSubdivisionChainMap L)
      (LocalCoefficientSystem.twistedChainComplexMap_comp_twistedSubdivisionChainMap P.map L).symm
      (P.twistedChainComplexπ_comp_twistedSubdivisionChainMap L).symm
  exact HomologicalComplex.HomologySequence.δ_naturality sd
    (P.shortExact_twistedChainComplexShortComplex L)
    (P.shortExact_twistedChainComplexShortComplex L) n m (by simpa using h)

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
  rw [← cancel_epi ((P.twistedChainComplexπ _).f n)]
  simp only [twistedChainComplexπ_f_comp_twistedChainComplexMap_f_assoc,
    twistedChainComplexπ_f_comp_twistedPrismX, twistedChainComplexπ_f_comp_twistedPrismX_assoc,
    twistedChainComplexπ_f_comp_twistedChainComplexMap_f,
    LocalCoefficientSystem.twistedChainComplexMap_f_comp_twistedPrismX_assoc]

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
  rw [← cancel_epi ((P.twistedChainComplexπ L).f n)]
  simp only [twistedChainComplexπ_f_comp_twistedChainComplexCoefficientMap_f_assoc,
    twistedChainComplexπ_f_comp_twistedPrismX, twistedChainComplexπ_f_comp_twistedPrismX_assoc,
    twistedChainComplexπ_f_comp_twistedChainComplexCoefficientMap_f,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_f_comp_twistedPrismX_assoc]

end TopPair
