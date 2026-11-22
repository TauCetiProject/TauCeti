/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple
public import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Pairs with trivial relative homology with local coefficients

This file collects criteria, read off homotopy invariance and the long exact sequences of pairs and
triples, for the relative singular homology `Hₙ(X, A; L)` with coefficients in a local system `L`
to vanish or to agree with the relative homology of another pair.

* If `B ↪ A` is a homotopy equivalence (for example a deformation retraction), then `C(A, B; L)` is
  acyclic and `Hₖ(A, B; L) = 0`, and for a triple `(X, A, B)` the quotient map `C(X, B; L) ⟶
  C(X, A; L)` (`TauCeti.TopTriple.twistedChainComplexTotalToOuter`) is a quasi-isomorphism for every
  `L` on `X`.
* Let `U` and `V` be open subsets of `X` such that `X` is acyclic modulo `U` and modulo `V`:
  `Hₙ(X, U; L) = Hₙ(X, V; L) = 0` for all `n`. Then `Hₙ₊₁(X, U ∪ V; L) ≅ Hₙ(X, U ∩ V; L)`
  (`TopPair.twistedHomologyOfSubsetUnionIso`) and `H₀(X, U ∪ V; L) = 0`
  (`TopPair.isZero_twistedHomology_ofSubset_union_zero`). This is what the relative Mayer–Vietoris
  sequence gives for constant coefficients. Here it is obtained from the long exact sequences of the
  triples `(X, U ∪ V, U)` and `(X, V, U ∩ V)` and excision of the pair `(V, U ∩ V) ⟶ (U ∪ V, U)`
  (`TopPair.isIso_twistedHomologyMap_unionExcisionMap`):
  `Hₙ₊₁(X, U ∪ V) ≅ Hₙ(U ∪ V, U) ≅ Hₙ(V, U ∩ V) ≅ Hₙ(X, U ∩ V)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1 (the long exact sequences of a pair and of a
  triple, and excision) and Section 3.H (local coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TopPair

open TauCeti

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The total pair `(X, B)` of the triple `(X, A, B)` of nested subsets `B ⊆ A` of `X` has the
twisted homology of the pair `TopPair.ofSubset B`. -/
def twistedHomologyTotalPairOfSubsetIso {A B : Set X} (h : B ⊆ A) (n : ℕ) :
    (TopTriple.totalPair.obj (TopTriple.ofSubset h)).twistedHomology L n ≅
      (ofSubset B).twistedHomology L n :=
  -- The pairs are named explicitly: inferring them from the twisted homology map runs out of
  -- time.
  have hiso := LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_homotopyInverse
    (P := TopTriple.totalPair.obj (TopTriple.ofSubset h)) (Q := ofSubset B) L
    (TopTriple.ofSubsetTotalPairIso h).inv (TopTriple.ofSubsetTotalPairIso h).hom
    (by rw [Iso.inv_hom_id]; exact ⟨Homotopy.refl _⟩)
    (by rw [Iso.hom_inv_id]; exact ⟨Homotopy.refl _⟩) n
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((TopTriple.totalPair.obj (TopTriple.ofSubset h)).twistedChainComplexCoefficientIso
      ((LocalCoefficientSystem.pullbackIdIso X).app L).symm) ≪≫
  @asIso _ _ _ _ (twistedHomologyMap (P := TopTriple.totalPair.obj (TopTriple.ofSubset h))
    (Q := ofSubset B) (TopTriple.ofSubsetTotalPairIso h).inv L n) hiso

section Union

variable {U V : Set X}

/-- The inclusion of pairs `(V, U ∩ V) ⟶ (U ∪ V, U)`, from the inner pair of the triple
`(X, V, U ∩ V)` to the inner pair of the triple `(X, U ∪ V, U)`. -/
def unionExcisionMap :
    TopTriple.innerPair.obj (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)) ⟶
      TopTriple.innerPair.obj (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)) :=
  ofHom (TopCat.ofHom (ContinuousMap.inclusion Set.subset_union_right))
    (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)) rfl

/-- The total-space component of `TopPair.unionExcisionMap` is the inclusion `V ⊆ U ∪ V`. -/
@[simp]
lemma unionExcisionMap_fst :
    Hom.fst (unionExcisionMap (U := U) (V := V)) =
      TopCat.ofHom (ContinuousMap.inclusion Set.subset_union_right) :=
  (rfl)

/-- The subspace component of `TopPair.unionExcisionMap` is the inclusion `U ∩ V ⊆ U`. -/
@[simp]
lemma unionExcisionMap_snd :
    Hom.snd (unionExcisionMap (U := U) (V := V)) =
      TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left) :=
  (rfl)

/-- **Excision of `U ∖ V`.** For open sets `U` and `V`, the inclusion of pairs
`(V, U ∩ V) ⟶ (U ∪ V, U)` induces isomorphisms on twisted homology. -/
theorem isIso_twistedHomologyMap_unionExcisionMap (hU : IsOpen U) (hV : IsOpen V)
    (L : LocalCoefficientSystem.{u, v, max v w} R
      (TopTriple.innerPair.obj (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V))).fst)
    (n : ℕ) :
    IsIso (twistedHomologyMap (P := TopTriple.innerPair.obj
      (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)))
      (Q := TopTriple.innerPair.obj (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)))
      unionExcisionMap L n) := by
  -- `U ∪ V` is covered by its open subsets `U`, the subspace of the target pair, and `V`, the
  -- image of the source pair.
  refine isIso_twistedHomologyMap_of_open_cover (P := TopTriple.innerPair.obj
      (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)))
      (P' := TopTriple.innerPair.obj (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)))
      unionExcisionMap L (Topology.IsEmbedding.inclusion Set.subset_union_right) ?_
      (fun b : Bool ↦ bif b then {x | x.val ∈ U} else {x | x.val ∈ V}) ?_ ?_ ?_ n
  · rintro x ⟨y, hy⟩
    exact ⟨⟨x.val, (congrArg Subtype.val hy).symm ▸ y.property, x.property⟩, rfl⟩
  · rintro (_ | _)
    exacts [hV.preimage continuous_subtypeVal, hU.preimage continuous_subtypeVal]
  · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    rcases x.property with h | h
    exacts [⟨true, h⟩, ⟨false, h⟩]
  · rintro (_ | _)
    exacts [Or.inr fun x hx ↦ ⟨⟨x.val, hx⟩, rfl⟩, Or.inl fun x hx ↦ ⟨⟨x.val, hx⟩, rfl⟩]

/-- The two restrictions of `L` to the pair `(V, U ∩ V)`: along `V ⟶ X`, and along
`V ⟶ U ∪ V ⟶ X`. -/
private def unionExcisionCoefficientIso :
    (LocalCoefficientSystem.pullback (Hom.fst (TopTriple.innerToTotal.app
      (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)))).hom).obj L ≅
    (LocalCoefficientSystem.pullback (Hom.fst (unionExcisionMap (U := U) (V := V))).hom).obj
      ((TopTriple.outerPair.obj
        (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V))).subspaceSystem L) :=
  (LocalCoefficientSystem.pullbackCompIso (Hom.fst (unionExcisionMap (U := U) (V := V))).hom
    (ofSubset (U ∪ V)).map.hom).app L

variable {L} (hU₀ : ∀ n, IsZero ((ofSubset U).twistedHomology L n))
include hU₀

/-- If `X` is acyclic modulo `U`, the connecting map `Hₙ₊₁(X, U ∪ V) ⟶ Hₙ(U ∪ V, U)` of the
triple `(X, U ∪ V, U)` is an isomorphism. -/
private theorem isIso_twistedHomologyδ_ofSubset_union (n : ℕ) :
    IsIso ((TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)).twistedHomologyδ L
      (n + 1) n) :=
  TopTriple.isIso_twistedHomologyδ_of_isZero
    (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)) L (n + 1) n
    ((hU₀ (n + 1)).of_iso (twistedHomologyTotalPairOfSubsetIso L Set.subset_union_left (n + 1)))
    ((hU₀ n).of_iso (twistedHomologyTotalPairOfSubsetIso L Set.subset_union_left n))

/-- **Degree zero.** If `X` is acyclic modulo `U`, then `H₀(X, U ∪ V; L) = 0`. -/
theorem isZero_twistedHomology_ofSubset_union_zero :
    IsZero ((ofSubset (U ∪ V)).twistedHomology L 0) := by
  let T := TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)
  have h₀ : IsZero ((TopTriple.totalPair.obj T).twistedHomology L 0) :=
    (hU₀ 0).of_iso (twistedHomologyTotalPairOfSubsetIso L Set.subset_union_left 0)
  -- The instance argument is passed explicitly: searching for it runs out of time.
  exact @IsZero.of_epi _ _ _ _ _ (T.twistedHomologyTotalToOuter L 0)
    (TopTriple.epi_twistedHomologyTotalToOuter_zero T L) h₀

variable (hU : IsOpen U) (hV : IsOpen V) (hV₀ : ∀ n, IsZero ((ofSubset V).twistedHomology L n))
include hU hV hV₀

/-- **The relative homology modulo a union of two acyclic open sets.** If `U` and `V` are open and
`X` is acyclic modulo each of them, with coefficients in `L`, then
`Hₙ₊₁(X, U ∪ V; L) ≅ Hₙ(X, U ∩ V; L)`. The isomorphism is the connecting map of the triple
`(X, U ∪ V, U)`, followed by the inverse of the excision `(V, U ∩ V) ⟶ (U ∪ V, U)` and the
inclusion `(V, U ∩ V) ⟶ (X, U ∩ V)`. -/
def twistedHomologyOfSubsetUnionIso (n : ℕ) :
    (ofSubset (U ∪ V)).twistedHomology L (n + 1) ≅ (ofSubset (U ∩ V)).twistedHomology L n :=
  have h₁ := isIso_twistedHomologyδ_ofSubset_union (V := V) hU₀ n
  have h₂ := isIso_twistedHomologyMap_unionExcisionMap hU hV
    ((TopTriple.outerPair.obj
      (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V))).subspaceSystem L) n
  have h₃ := TopTriple.isIso_twistedHomologyMap_innerToTotal_of_isZero
    (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)) L n (hV₀ n) (hV₀ (n + 1))
  -- The maps are named explicitly, with their instances: inferring them runs out of time.
  @asIso _ _ _ _ ((TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)).twistedHomologyδ L
    (n + 1) n rfl) h₁ ≪≫
  (@asIso _ _ _ _ (twistedHomologyMap (P := TopTriple.innerPair.obj
      (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)))
      (Q := TopTriple.innerPair.obj (TopTriple.ofSubset (Set.subset_union_left : U ⊆ U ∪ V)))
      unionExcisionMap _ n) h₂).symm ≪≫
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((TopTriple.innerPair.obj (TopTriple.ofSubset
      (Set.inter_subset_right : U ∩ V ⊆ V))).twistedChainComplexCoefficientIso
        (unionExcisionCoefficientIso L).symm) ≪≫
  @asIso _ _ _ _ (twistedHomologyMap (P := TopTriple.innerPair.obj
      (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)))
      (Q := TopTriple.totalPair.obj (TopTriple.ofSubset (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopTriple.innerToTotal.app _) L n) h₃ ≪≫
  twistedHomologyTotalPairOfSubsetIso L Set.inter_subset_right n

end Union

section HomotopyEquiv

open TauCeti.LocalCoefficientSystem
variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- If `P.map` is a homotopy equivalence, `P.twistedChainComplex L` is acyclic. -/
theorem acyclic_twistedChainComplex_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst) (he : e.toFun = P.map.hom) :
    (P.twistedChainComplex L).Acyclic := by
  have h := e.quasiIso_twistedChainComplexMap L; rw [he, TopCat.ofHom_hom] at h
  exact (P.shortExact_twistedChainComplexShortComplex L).quasiIso_f_iff.1 h

/-- Relative twisted homology vanishes when `P.map` is a homotopy equivalence. -/
theorem isZero_twistedHomology_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst) (he : e.toFun = P.map.hom) (k : ℕ) :
    IsZero (P.twistedHomology L k) :=
  (P.acyclic_twistedChainComplex_of_homotopyEquiv L e he k).isZero_homology

section DR

variable (r : C(P.fst, P.snd)) (hr : Function.LeftInverse r P.map.hom)
  (hH : (P.map.hom.comp r).Homotopic (ContinuousMap.id P.fst))
include r hr hH

/-- If `P.fst` deformation retracts onto `P.snd`, `P.twistedChainComplex L` is acyclic. -/
theorem acyclic_twistedChainComplex_of_deformationRetraction :
    (P.twistedChainComplex L).Acyclic :=
  P.acyclic_twistedChainComplex_of_homotopyEquiv L (.ofDeformationRetraction P.map.hom r hr hH)
    (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun P.map.hom r hr hH)

/-- Relative twisted homology vanishes when `P.fst` deformation retracts onto `P.snd`. -/
theorem isZero_twistedHomology_of_deformationRetraction (k : ℕ) :
    IsZero (P.twistedHomology L k) :=
  (P.acyclic_twistedChainComplex_of_deformationRetraction L r hr hH k).isZero_homology

end DR

end HomotopyEquiv

end TopPair

namespace TauCeti.TopTriple

variable {R : Type u} [Ring R]

section General

variable (T : TopTriple.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R T.fst)

/-- If `T.innerMap` is a homotopy equivalence, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv T.thd T.snd) (he : e.toFun = T.innerMap.hom) :
    QuasiIso (T.twistedChainComplexTotalToOuter L) :=
  (T.shortExact_twistedChainComplexShortComplex L).quasiIso_g_iff.2
    ((innerPair.obj T).acyclic_twistedChainComplex_of_homotopyEquiv
      ((outerPair.obj T).subspaceSystem L) e he)

/-- Homology isomorphism induced by `quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv`. -/
theorem isIso_twistedHomologyTotalToOuter_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv T.thd T.snd) (he : e.toFun = T.innerMap.hom) (k : ℕ) :
    IsIso (T.twistedHomologyTotalToOuter L k) :=
  have := T.quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L e he; inferInstance

section DR

variable (r : C(T.snd, T.thd)) (hr : Function.LeftInverse r T.innerMap.hom)
  (hH : (T.innerMap.hom.comp r).Homotopic (ContinuousMap.id T.snd))
include r hr hH

/-- If `T.snd` deformation retracts onto `T.thd`, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-iso. -/
theorem quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction :
    QuasiIso (T.twistedChainComplexTotalToOuter L) :=
  T.quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L
    (.ofDeformationRetraction T.innerMap.hom r hr hH)
    (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun T.innerMap.hom r hr hH)

/-- Homology isomorphism for `quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction`. -/
theorem isIso_twistedHomologyTotalToOuter_of_deformationRetraction (k : ℕ) :
    IsIso (T.twistedHomologyTotalToOuter L k) :=
  have := T.quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction L r hr hH
  inferInstance

end DR

end General

section Subsets

variable {X : TopCat.{v}} {A B : Set X} (hBA : B ⊆ A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

section DeformationRetraction

variable (r : C(A, B)) (hr : ∀ b, r (ContinuousMap.inclusion hBA b) = b)
  (hH : ((ContinuousMap.inclusion hBA).comp r).Homotopic (ContinuousMap.id A))
include r hr hH

/-- Under a deformation retraction of `A` onto `B`, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-iso. -/
theorem quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction :
    QuasiIso ((ofSubset hBA).twistedChainComplexTotalToOuter L) :=
  (ofSubset hBA).quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction L r hr hH

/-- Homology isomorphism for `ofSubset` under a deformation retraction of `A` onto `B`. -/
theorem isIso_twistedHomologyTotalToOuter_ofSubset_of_deformationRetraction (k : ℕ) :
    IsIso ((ofSubset hBA).twistedHomologyTotalToOuter L k) :=
  have := quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction hBA L r hr hH
  inferInstance

end DeformationRetraction

section WeakDeformationRetraction

variable (H : unitInterval × A → X) (hH : Continuous H) (hHA : ∀ p, H p ∈ A)
  (h₀ : ∀ x : A, H (0, x) = x) (h₁ : ∀ x : A, H (1, x) ∈ B)
  (hHB : ∀ t (x : A), (x : X) ∈ B → H (t, x) ∈ B)
include H hH hHA h₀ h₁ hHB

/-- Under a weak deformation retraction of `A` to `B`, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-iso. -/
theorem quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_weakDeformationRetraction :
    QuasiIso ((ofSubset hBA).twistedChainComplexTotalToOuter L) :=
  (ofSubset hBA).quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L
    (.ofWeakDeformationRetraction hBA H hH hHA h₀ h₁ hHB)
    (ContinuousMap.ext fun b ↦ Subtype.ext
      (ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply hBA H hH hHA h₀ h₁ hHB b))

/-- Homology isomorphism for `ofSubset` under a weak deformation retraction of `A` onto `B`. -/
theorem isIso_twistedHomologyTotalToOuter_ofSubset_of_weakDeformationRetraction (k : ℕ) :
    IsIso ((ofSubset hBA).twistedHomologyTotalToOuter L k) :=
  have := quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_weakDeformationRetraction
    hBA L H hH hHA h₀ h₁ hHB; inferInstance

end WeakDeformationRetraction

end Subsets

end TauCeti.TopTriple
