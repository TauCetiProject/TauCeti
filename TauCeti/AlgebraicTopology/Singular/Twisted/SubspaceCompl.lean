/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl
public import TauCeti.AlgebraicTopology.Singular.Twisted.Acyclic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple

/-!
# Twisted homology modulo the preimage of the complement of a subspace

This file is the counterpart with local coefficients of
`TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl`.

**Acyclic open covers.** Let `U` and `V` be open subsets of a space `X` and `L` a local
coefficient system on `X`, and suppose that `X` is acyclic modulo `U` and modulo `V`:
`Hₙ(X, U; L) = Hₙ(X, V; L) = 0` for all `n`. Then
`Hₙ₊₁(X, U ∪ V; L) ≅ Hₙ(X, U ∩ V; L)` (`TopPair.twistedHomologyOfSubsetUnionIso`) and
`H₀(X, U ∪ V; L) = 0` (`TopPair.isZero_twistedHomology_ofSubset_union_zero`). This is what the
relative Mayer–Vietoris sequence gives for constant coefficients. Here it is obtained from the long
exact sequences of the triples `(X, U ∪ V, U)` and `(X, V, U ∩ V)` and excision of the pair
`(V, U ∩ V) ⟶ (U ∪ V, U)` (`TopPair.isIso_twistedHomologyMap_unionExcisionMap`):

`Hₙ₊₁(X, U ∪ V) ≅ Hₙ(U ∪ V, U) ≅ Hₙ(V, U ∩ V) ≅ Hₙ(X, U ∩ V)`.

**The complement of a subspace.** Let `q : X → F` be a continuous map to a real normed space of
finite dimension. Suppose that `X` is acyclic modulo the preimage of the complement of every closed
half-subspace `{y ∈ W | φ y ≤ 0}` of `F` with `φ v = 1` for some `v ∈ W`, with coefficients in
`L`. Removing one dimension at a time along the extensions by a line of
`Submodule.lineExtension`, as for constant coefficients, gives:

* `Hₙ(X, q⁻¹(F ∖ W); L) = 0` for `n` below the codimension of `W`
  (`TauCeti.isZero_twistedHomology_subspaceComplPair`);
* `Hₘ(X, q⁻¹(F ∖ W); L) ≅ Hₙ(X; L)` for `W` of codimension `c` and `m = n + c`
  (`TauCeti.subspaceComplPairTwistedHomologyIso`).

For the projection `B × F → F` these compute the homology of the Thom pair of a product bundle with
local coefficients (`TauCeti.prodThomPairTwistedHomologyIso`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1 (the long exact sequence of a triple and
  excision) and Section 3.H (local coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits Module TauCeti

universe u v w

namespace TopPair

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
      (fun b : Bool ↦ bif b then {x | x.1 ∈ U} else {x | x.1 ∈ V}) ?_ ?_ ?_ n
  · rintro x ⟨y, hy⟩
    exact ⟨⟨x.1, (congrArg Subtype.val hy).symm ▸ y.2, x.2⟩, rfl⟩
  · rintro (_ | _)
    exacts [hV.preimage continuous_subtype_val, hU.preimage continuous_subtype_val]
  · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    rcases x.2 with h | h
    exacts [⟨true, h⟩, ⟨false, h⟩]
  · rintro (_ | _)
    exacts [Or.inr fun x hx ↦ ⟨⟨x.1, hx⟩, rfl⟩, Or.inl fun x hx ↦ ⟨⟨x.1, hx⟩, rfl⟩]

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
    (TopTriple.instEpiModuleCatTwistedHomologyTotalToOuterOfNatNat T L) h₀

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

end TopPair

namespace TauCeti

variable {R : Type u} [Ring R] {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : TopCat.{v}} (q : C(X, F)) (L : LocalCoefficientSystem.{u, v, max v w} R X)

namespace SubspaceComplPair

variable {W : Submodule ℝ F}

/-- The relative twisted homology of `(X, q⁻¹(F ∖ W))` is that of `X` modulo the union of the two
half-subspace complements of a step. -/
private def twistedHomologyUnionIso (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q W).twistedHomology L n ≅
      (TopPair.ofSubset (half q s.W' (extension s) ∪ half q s.W' (-extension s))).twistedHomology
        L n :=
  eqToIso (by rw [← Set.preimage_union, s.compl_union_compl (extension_comp s)])

/-- The relative twisted homology of `X` modulo the intersection of the two half-subspace
complements of a step is that of `(X, q⁻¹(F ∖ W'))`. -/
private def twistedHomologyInterIso (s : W.LineExtension) (n : ℕ) :
    (TopPair.ofSubset (half q s.W' (extension s) ∩ half q s.W' (-extension s))).twistedHomology
        L n ≅
      (subspaceComplPair q s.W').twistedHomology L n :=
  eqToIso (by rw [← Set.preimage_inter, s.compl_inter_compl])

variable (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
  IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).twistedHomology L n))
include hq

private lemma isZero_half (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (half q s.W' (extension s))).twistedHomology L n) :=
  hq _ _ _ s.v.2 (extension_apply_v s) n

private lemma isZero_half_neg (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (half q s.W' (-extension s))).twistedHomology L n) :=
  hq _ _ _ (neg_mem s.v.2) (by simp [extension_apply_v]) n

/-- One step of the computation: `Hₙ₊₁(X, q⁻¹(F ∖ W); L) ≅ Hₙ(X, q⁻¹(F ∖ W'); L)`. -/
private def twistedStepIso [FiniteDimensional ℝ F] (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q W).twistedHomology L (n + 1) ≅
      (subspaceComplPair q s.W').twistedHomology L n :=
  twistedHomologyUnionIso q L s (n + 1) ≪≫
    TopPair.twistedHomologyOfSubsetUnionIso (isZero_half q L hq s) (isOpen_half q _ _)
      (isOpen_half q _ _) (isZero_half_neg q L hq s) n ≪≫
    twistedHomologyInterIso q L s n

private lemma isZero_twistedHomology_zero (s : W.LineExtension) :
    IsZero ((subspaceComplPair q W).twistedHomology L 0) :=
  (TopPair.isZero_twistedHomology_ofSubset_union_zero (V := half q s.W' (-extension s))
    (isZero_half q L hq s)).of_iso (twistedHomologyUnionIso q L s 0)

end SubspaceComplPair

open SubspaceComplPair

variable [FiniteDimensional ℝ F]
  (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).twistedHomology L n))
include hq

/-- **Vanishing below the codimension, with local coefficients.** If `X` is acyclic modulo the
preimage under `q` of the complement of every closed half-subspace of `F`, with coefficients in
`L`, then `Hₙ(X, q⁻¹(F ∖ W); L) = 0` whenever `n` is less than the codimension of `W`. -/
theorem isZero_twistedHomology_subspaceComplPair :
    ∀ (n : ℕ) (W : Submodule ℝ F), n + finrank ℝ W < finrank ℝ F →
      IsZero ((subspaceComplPair q W).twistedHomology L n)
  | 0, W, h => isZero_twistedHomology_zero q L hq
      (W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne)
  | n + 1, W, h =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    (isZero_twistedHomology_subspaceComplPair n s.W' (by rw [s.finrank_eq]; omega)).of_iso
      (twistedStepIso q L hq s n)

/-- **The twisted homology modulo the preimage of the complement of a subspace.** If `X` is acyclic
modulo the preimage under `q` of the complement of every closed half-subspace of `F`, with
coefficients in `L`, then `Hₘ(X, q⁻¹(F ∖ W); L) ≅ Hₙ(X, ∅; L)` for `W` of codimension `c` and
`m = n + c`.

The isomorphism is the composite of `c` steps `TopPair.twistedHomologyOfSubsetUnionIso`, for the
fixed choice of a flag of subspaces of `F` given by `Submodule.lineExtension`. -/
def subspaceComplPairTwistedHomologyIso :
    ∀ (c : ℕ) (W : Submodule ℝ F), finrank ℝ W + c = finrank ℝ F → ∀ (n m : ℕ), n + c = m →
      ((subspaceComplPair q W).twistedHomology L m ≅
        (subspaceComplPair q (⊤ : Submodule ℝ F)).twistedHomology L n)
  | 0, _, hW, n, _, rfl => eqToIso (by rw [Submodule.eq_top_of_finrank_eq hW, add_zero])
  | c + 1, W, hW, n, _, rfl =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    twistedStepIso q L hq s (n + c) ≪≫
      subspaceComplPairTwistedHomologyIso c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl

end TauCeti
