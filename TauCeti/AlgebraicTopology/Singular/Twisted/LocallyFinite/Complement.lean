/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower
public import TauCeti.Topology.Compactness.SigmaCompact

/-!
# Borel–Moore homology of the complement of a closed set

Let `A` be a subset of a space `X` and let `L` be a local coefficient system on `X`. Suppose that
the complement `U = X \ A` is exhausted by closed compact sets `K₀ ⊆ K₁ ⊆ ⋯` of `X` with
`Kₙ ⊆ interior Kₙ₊₁`, and that each of the open neighbourhoods `X \ Kₙ` of `A` has vanishing
relative homology `H_*(X \ Kₙ, A; L)`. This holds, for instance, when each `X \ Kₙ` deformation
retracts onto `A`, which is the situation of a subcomplex `A` of a finite simplicial complex `X`
with its cofinal regular neighbourhoods. Then the Borel–Moore homology of `U`, with coefficients
in the restriction of `L`, is the relative homology of the pair `(X, A)`
(`TauCeti.LocalCoefficientSystem.borelMooreHomologyComplEquiv`):
`H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)`.

The argument identifies the tower of relative groups `H_j(U, U \ Kₙ; L)`, whose limit computes
Borel–Moore homology by the Milnor sequence, with a constant tower. Excision of the closed set `A`
from the open set `X \ Kₙ` identifies `H_j(U, U \ Kₙ; L)` with `H_j(X, X \ Kₙ; L)`, and by the
long exact sequence of the triple `(X, X \ Kₙ, A)` the quotient `H_j(X, A; L) ⟶ H_j(X, X \ Kₙ; L)`
is an isomorphism. These isomorphisms are compatible with the transition maps of the tower, which
are therefore bijective. Hence the `lim¹` term of the Milnor sequence vanishes and the limit is
`H_j(X, A; L)`. The isomorphism is characterized by its components: composed with the quotient to
`H_j(X, X \ Kₙ; L)` it is the relative class of a locally finite chain in `H_j(U, U \ Kₙ; L)`,
followed by excision
(`TauCeti.LocalCoefficientSystem.twistedHomologyTotalToOuter_borelMooreHomologyComplEquiv`).

For example, `X = [0, 1]`, `A = {0, 1}` and `Kₙ = [1/(n+3), 1 - 1/(n+3)]` satisfy these hypotheses,
giving `H₁^{BM}((0, 1)) ≃ H₁([0, 1], {0, 1})`, while the ordinary homology `H₁((0, 1))` vanishes.

## Main declarations

* `TauCeti.LocalCoefficientSystem.borelMooreHomologyComplEquiv`: the isomorphism
  `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)`.
* `TauCeti.LocalCoefficientSystem.twistedHomologyTotalToOuter_borelMooreHomologyComplEquiv`: its
  characterization through the relative classes of locally finite chains and excision.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.22, for the comparison of
  `H_*(X, A)` with `H_*(X, V)` and `H_*(X \ A, V \ A)` for a neighbourhood `V` of `A`.
* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341, for `lim¹`.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Topology

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)
  {A : Set X} {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (hKc : ∀ n, IsClosed (K n))
  (hKA : ∀ n, A ⊆ (K n)ᶜ) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
  (hcover : ∀ x ∉ A, ∃ n, x ∈ K n)
  (hzero : ∀ n k, IsZero ((TopPair.ofInclusion (hKA n)).twistedHomology
    ((TopPair.ofSubset (K n)ᶜ).subspaceSystem L) k))

/-- The compact exhaustion of `X \ A` traced by the sets `Kₙ`. -/
private abbrev complExhaustion : CompactExhaustion (TopCat.of ↥Aᶜ) :=
  CompactExhaustion.subtype Aᶜ K hK (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
    fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)

/-- The restriction of `L` to the complement of `A`. -/
private abbrev complSystem (L : LocalCoefficientSystem.{u, v, max v w} R X) (A : Set X) :
    LocalCoefficientSystem.{u, v, max v w} R (TopCat.of ↥Aᶜ) :=
  (pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L

/-- The transition maps of the tower of `(U, U \ Kₙ)` correspond under excision to the quotients
`C(X, X \ Kₙ₊₁; L) ⟶ C(X, X \ Kₙ; L)`. -/
private lemma relativeChainComplexTower_map_comp_excision (n : ℕ) :
    (relativeChainComplexTower (complSystem L A) (complExhaustion hK hKA hsub hcover)).map
        (homOfLE (Nat.le_succ n)).op ≫
      TopPair.twistedChainComplexMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L =
    TopPair.twistedChainComplexMap (TopPair.excisionMap Aᶜ (K (n + 1))ᶜ) L ≫
      (TopTriple.ofSubset (Set.compl_subset_compl.2 ((hsub n).trans interior_subset))
        ).twistedChainComplexTotalToOuter L := by
  rw [relativeChainComplexTower_map_succ]
  refine TopPair.twistedChainComplex_hom_ext _ _ ?_
  -- Both sides are induced by the inclusion `U → X` on ambient chains. The pairs of the tower and
  -- of the triples agree with `TopPair.ofSubset` and `TopPair.interPair` only up to unfolding, so
  -- `rw` cannot match them; the final `rfl` identifies the two excision maps' ambient inclusions.
  erw [TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    TopTriple.twistedChainComplexπ_comp_totalToOuter]
  rfl

include hzero in
/-- The quotient `H_j(X, A; L) ⟶ H_j(X, X \ Kₙ; L)` is an isomorphism. -/
private lemma isIso_twistedHomologyTotalToOuter (n j : ℕ) :
    IsIso ((TopTriple.ofSubset (hKA n)).twistedHomologyTotalToOuter L j) :=
  TopTriple.isIso_twistedHomologyTotalToOuter_of_isZero (TopTriple.ofSubset (hKA n)) L j
    (hzero n j) fun m _ ↦ hzero n m

/-- The quotient `H_j(X, A; L) ⟶ H_j(X, X \ Kₙ; L)` as an isomorphism. -/
private def outerIso (n j : ℕ) :=
  @asIso _ _ _ _ ((TopTriple.ofSubset (hKA n)).twistedHomologyTotalToOuter L j)
    (isIso_twistedHomologyTotalToOuter L hKA hzero n j)

include hKc hKA hsub hcover in
/-- Excision `H_j(U, U \ Kₙ; L) ⟶ H_j(X, X \ Kₙ; L)` is an isomorphism. -/
private lemma isIso_twistedHomologyMap_excisionMap (n j : ℕ) :
    IsIso (TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L j) :=
  TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset L
    (isOpen_of_subset_interior_succ (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
      fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)) (hKc n) (Set.subset_compl_comm.1 (hKA n)) j

/-- The comparison `H_j(U, U \ Kₙ; L) ⟶ H_j(X, A; L)`: excision to `H_j(X, X \ Kₙ; L)` followed by
the inverse of the quotient `H_j(X, A; L) ⟶ H_j(X, X \ Kₙ; L)`. -/
private def towerToRelative (n j : ℕ) :
    ((relativeChainComplexTower (complSystem L A) (complExhaustion hK hKA hsub hcover)).homology
      j).obj (op n) ⟶ (TopPair.ofSubset A).twistedHomology L j :=
  TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L j ≫ (outerIso L hKA hzero n j).inv

include hKc in
private lemma isIso_towerToRelative (n j : ℕ) :
    IsIso (towerToRelative L hK hKA hsub hcover hzero n j) :=
  IsIso.comp_isIso' (isIso_twistedHomologyMap_excisionMap L hKc hKA hsub hcover n j)
    (Iso.isIso_inv _)

/-- The comparisons are compatible with the transition maps of the tower. -/
private lemma homology_map_comp_towerToRelative (n j : ℕ) :
    ((relativeChainComplexTower (complSystem L A) (complExhaustion hK hKA hsub hcover)).homology
        j).map (homOfLE (Nat.le_succ n)).op ≫ towerToRelative L hK hKA hsub hcover hzero n j =
      towerToRelative L hK hKA hsub hcover hzero (n + 1) j := by
  have hKK := Set.compl_subset_compl.2 ((hsub n).trans interior_subset)
  have h₂ : (TopTriple.ofSubset hKK).twistedHomologyTotalToOuter L j ≫
      (outerIso L hKA hzero n j).inv = (outerIso L hKA hzero (n + 1) j).inv :=
    (Iso.comp_inv_eq _).2 <| (Iso.eq_inv_comp _).2 <|
      TopTriple.twistedHomologyTotalToOuter_ofSubset_comp (hKA (n + 1)) hKK L j
  have h₁ := (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · j)
      (relativeChainComplexTower_map_comp_excision L hK hKA hsub hcover n)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))
  rw [towerToRelative, towerToRelative, ← h₂]
  exact (reassoc_of% h₁) _

/-- The comparisons agree on the components of an element of the limit of the tower. -/
private lemma towerToRelative_limπ {j : ℕ}
    (z : ((relativeChainComplexTower (complSystem L A)
      (complExhaustion hK hKA hsub hcover)).homology j).lim) (n : ℕ) :
    (towerToRelative L hK hKA hsub hcover hzero n j).hom (ModuleTower.limπ _ n z) =
      (towerToRelative L hK hKA hsub hcover hzero 0 j).hom (ModuleTower.limπ _ 0 z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, ← homology_map_comp_towerToRelative, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleTower.limπ_apply, ModuleTower.limπ_apply, ← ModuleTower.transition_def,
      (ModuleTower.mem_lim _).1 z.property n]

include hKc hzero in
/-- The transition maps of the tower of relative homology groups are bijective. -/
private lemma transition_bijective (j n : ℕ) :
    Function.Bijective (((relativeChainComplexTower (complSystem L A)
      (complExhaustion hK hKA hsub hcover)).homology j).transition n) := by
  have := isIso_towerToRelative L hK hKc hKA hsub hcover hzero n j
  have := isIso_towerToRelative L hK hKc hKA hsub hcover hzero (n + 1) j
  have : IsIso (((relativeChainComplexTower (complSystem L A)
      (complExhaustion hK hKA hsub hcover)).homology j).map (homOfLE (Nat.le_succ n)).op ≫
        towerToRelative L hK hKA hsub hcover hzero n j) := by
    rw [homology_map_comp_towerToRelative]
    infer_instance
  have := IsIso.of_isIso_comp_right (((relativeChainComplexTower (complSystem L A)
      (complExhaustion hK hKA hsub hcover)).homology j).map (homOfLE (Nat.le_succ n)).op)
    (towerToRelative L hK hKA hsub hcover hzero n j)
  rw [ModuleTower.transition_def]
  exact ConcreteCategory.bijective_of_isIso _

/-- The map from Borel–Moore homology of the complement to the relative homology of the pair. -/
private def toTwistedHomology (j : ℕ) :
    borelMooreHomology (complSystem L A) j →ₗ[R] (TopPair.ofSubset A).twistedHomology L j :=
  (towerToRelative L hK hKA hsub hcover hzero 0 j).hom ∘ₗ ModuleTower.limπ _ 0 ∘ₗ
    borelMooreHomologyToLim (complSystem L A) (complExhaustion hK hKA hsub hcover) j

private lemma toTwistedHomology_apply (j : ℕ) (x : borelMooreHomology (complSystem L A) j) :
    toTwistedHomology L hK hKA hsub hcover hzero j x =
      (towerToRelative L hK hKA hsub hcover hzero 0 j).hom (ModuleTower.limπ _ 0
        (borelMooreHomologyToLim (complSystem L A) (complExhaustion hK hKA hsub hcover) j x)) :=
  (rfl)

include hKc in
private lemma toTwistedHomology_bijective (j : ℕ) :
    Function.Bijective (toTwistedHomology L hK hKA hsub hcover hzero j) := by
  set KU := complExhaustion hK hKA hsub hcover
  set C := relativeChainComplexTower (complSystem L A) KU
  have (n : ℕ) := isIso_towerToRelative L hK hKc hKA hsub hcover hzero n j
  -- The inverses of the comparisons are compatible bijections onto the terms of the tower, so they
  -- identify `H_j(X, A; L)` with its limit, with inverse the comparison at stage `0`.
  let f (n : ℕ) := (inv (towerToRelative L hK hKA hsub hcover hzero n j)).hom
  have hf (n : ℕ) : (C.homology j).transition n ∘ₗ f (n + 1) = f n := by
    rw [ModuleTower.transition_def, ← ModuleCat.hom_comp]
    exact congrArg ModuleCat.Hom.hom <| (IsIso.inv_comp_eq _).2 <| (IsIso.eq_comp_inv _).2 <|
      homology_map_comp_towerToRelative L hK hKA hsub hcover hzero n j
  have hlift := (C.homology j).limLift_bijective_of_le f hf 0 fun n _ ↦
    ConcreteCategory.bijective_of_isIso (inv (towerToRelative L hK hKA hsub hcover hzero n j))
  have hleft : (towerToRelative L hK hKA hsub hcover hzero 0 j).hom ∘ₗ ModuleTower.limπ _ 0 ∘ₗ
      (C.homology j).limLift f hf = LinearMap.id := by
    rw [ModuleTower.limπ_comp_limLift, ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id]
  -- The Milnor map is bijective because `lim¹` vanishes for a tower with bijective transitions.
  have : Subsingleton (C.homology (j + 1)).limOne :=
    ModuleTower.subsingleton_limOne_of_surjective _ fun n ↦
      (transition_bijective L hK hKc hKA hsub hcover hzero (j + 1) n).2
  have htoLim := borelMooreHomologyToLim_bijective (complSystem L A) KU j
  have hcomp : Function.Bijective
      ((towerToRelative L hK hKA hsub hcover hzero 0 j).hom ∘ₗ ModuleTower.limπ _ 0) :=
    (Function.Bijective.of_comp_iff _ hlift).1 <| by
      rw [← LinearMap.coe_comp, LinearMap.comp_assoc, hleft]
      exact Function.bijective_id
  exact hcomp.comp htoLim

/-- **Borel–Moore homology of a complement.** Let `A ⊆ X`, and let `Kₙ` be closed compact subsets
of `X` covering `X \ A`, disjoint from `A`, with `Kₙ ⊆ interior Kₙ₊₁`. If the relative homology
`H_*(X \ Kₙ, A; L)` of each open neighbourhood `X \ Kₙ` of `A` vanishes, then the Borel–Moore
homology of `X \ A`, with coefficients in the restriction of `L`, is the relative homology of
`(X, A)`: `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)`. -/
def borelMooreHomologyComplEquiv (j : ℕ) :
    borelMooreHomology
        ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L) j ≃ₗ[R]
      (TopPair.ofSubset A).twistedHomology L j :=
  LinearEquiv.ofBijective (toTwistedHomology L hK hKA hsub hcover hzero j)
    (toTwistedHomology_bijective L hK hKc hKA hsub hcover hzero j)

/-- The isomorphism `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)` followed by the quotient to
`H_j(X, X \ Kₙ; L)` sends a class to the relative class of its locally finite representatives in
`H_j(X \ A, X \ (A ∪ Kₙ); L)`, followed by excision. -/
theorem twistedHomologyTotalToOuter_borelMooreHomologyComplEquiv (j n : ℕ)
    (x : borelMooreHomology
      ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L) j) :
    ((TopTriple.ofSubset (hKA n)).twistedHomologyTotalToOuter L j).hom
        (borelMooreHomologyComplEquiv L hK hKc hKA hsub hcover hzero j x) =
      (TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L j).hom
        ((HomologicalComplex.homologyMap (TopPair.locallyFiniteChainComplexToRelative
          (TopPair.ofSubset (X := TopCat.of ↥Aᶜ) (Subtype.val ⁻¹' K n)ᶜ) _
          (IsCompact.compl_range_ofSubset_compl_map (CompactExhaustion.isCompact
            (CompactExhaustion.subtype Aᶜ K hK (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
              fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)) n))) j).hom x) := by
  have hc :=
    limπ_borelMooreHomologyToLim (complSystem L A) (complExhaustion hK hKA hsub hcover) j n x
  rw [borelMooreHomologyComplEquiv, LinearEquiv.ofBijective_apply, toTwistedHomology_apply,
    ← towerToRelative_limπ L hK hKA hsub hcover hzero _ n, hc]
  unfold towerToRelative
  -- The target of the excision map is `TopPair.ofSubset (K n)ᶜ` while the inverse quotient starts
  -- at the outer pair of the triple; they agree up to unfolding, which `rw` does not see.
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f _) (outerIso L hKA hzero n j).inv_hom_id

end TauCeti.LocalCoefficientSystem
