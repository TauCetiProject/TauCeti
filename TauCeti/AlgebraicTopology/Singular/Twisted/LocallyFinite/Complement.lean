/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Tower
public import TauCeti.Topology.Compactness.SigmaCompact
import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler

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

include hKA hsub hcover in
/-- The complement of `A` is the union of the interiors of the sets `Kₙ`, so it is open. -/
private lemma isOpen_compl_of_exhaustion : IsOpen Aᶜ := by
  have : Aᶜ = ⋃ n, interior (K (n + 1)) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨n, hn⟩ := hcover x hx
      exact Set.mem_iUnion.2 ⟨n, hsub n hn⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
      exact fun hxA ↦ hKA (n + 1) hxA (interior_subset hn)
  rw [this]
  exact isOpen_iUnion fun _ ↦ isOpen_interior

/-- The restriction of `L` to the complement of `A`. -/
private abbrev complSystem (L : LocalCoefficientSystem.{u, v, max v w} R X) (A : Set X) :
    LocalCoefficientSystem.{u, v, max v w} R (TopCat.of ↥Aᶜ) :=
  (pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtype_val⟩).obj L

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

include hKc hKA hsub hcover in
/-- Excision `H_j(U, U \ Kₙ; L) ⟶ H_j(X, X \ Kₙ; L)` is an isomorphism. -/
private lemma isIso_twistedHomologyMap_excisionMap (n j : ℕ) :
    IsIso (TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L j) :=
  TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset L
    (isOpen_compl_of_exhaustion hKA hsub hcover) (hKc n) (Set.subset_compl_comm.1 (hKA n)) j

/-- The comparison `H_j(U, U \ Kₙ; L) ⟶ H_j(X, A; L)`: excision to `H_j(X, X \ Kₙ; L)` followed by
the inverse of the quotient `H_j(X, A; L) ⟶ H_j(X, X \ Kₙ; L)`. -/
private def towerToRelative (n j : ℕ) :
    ((relativeChainComplexTower (complSystem L A) (complExhaustion hK hKA hsub hcover)).homology
      j).obj (op n) ⟶ (TopPair.ofSubset A).twistedHomology L j :=
  TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L j ≫
    (@asIso _ _ _ _ ((TopTriple.ofSubset (hKA n)).twistedHomologyTotalToOuter L j)
      (isIso_twistedHomologyTotalToOuter L hKA hzero n j)).inv

include hKc in
private lemma isIso_towerToRelative (n j : ℕ) :
    IsIso (towerToRelative L hK hKA hsub hcover hzero n j) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_twistedHomologyMap_excisionMap L hKc hKA hsub hcover n j)
    (Iso.isIso_inv _)

/-- The comparisons are compatible with the transition maps of the tower. -/
private lemma homology_map_comp_towerToRelative (n j : ℕ) :
    ((relativeChainComplexTower (complSystem L A) (complExhaustion hK hKA hsub hcover)).homology
        j).map (homOfLE (Nat.le_succ n)).op ≫ towerToRelative L hK hKA hsub hcover hzero n j =
      towerToRelative L hK hKA hsub hcover hzero (n + 1) j := by
  have hKK := Set.compl_subset_compl.2 ((hsub n).trans interior_subset)
  have h₁ := (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · j)
      (relativeChainComplexTower_map_comp_excision L hK hKA hsub hcover n)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))
  have h₂ : (TopTriple.ofSubset hKK).twistedHomologyTotalToOuter L j ≫
      (@asIso _ _ _ _ ((TopTriple.ofSubset (hKA n)).twistedHomologyTotalToOuter L j)
        (isIso_twistedHomologyTotalToOuter L hKA hzero n j)).inv =
      (@asIso _ _ _ _ ((TopTriple.ofSubset (hKA (n + 1))).twistedHomologyTotalToOuter L j)
        (isIso_twistedHomologyTotalToOuter L hKA hzero (n + 1) j)).inv :=
    (Iso.comp_inv_eq _).2 <| (Iso.eq_inv_comp _).2 <|
      TopTriple.twistedHomologyTotalToOuter_ofSubset_comp (hKA (n + 1)) hKK L j
  unfold towerToRelative
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₁).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂)

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
      (ModuleTower.mem_lim _).1 z.2 n]

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
  have hψ (n : ℕ) : Function.Bijective (towerToRelative L hK hKA hsub hcover hzero n j).hom := by
    have := isIso_towerToRelative L hK hKc hKA hsub hcover hzero n j
    exact ConcreteCategory.bijective_of_isIso _
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · -- Two classes with the same image have the same relative classes at every stage, so they
    -- differ by an element of `lim¹`, which vanishes because the transitions are bijective.
    have : Subsingleton (C.homology (j + 1)).limOne :=
      ModuleTower.subsingleton_limOne_of_isMittagLeffler _ <|
        ModuleTower.isMittagLeffler_of_surjective _ fun n ↦
          (transition_bijective L hK hKc hKA hsub hcover hzero (j + 1) n).2
    have hlim : borelMooreHomologyToLim (complSystem L A) KU j x =
        borelMooreHomologyToLim (complSystem L A) KU j y := by
      refine Subtype.ext <| funext fun n ↦ (hψ n).1 ?_
      have := towerToRelative_limπ L hK hKA hsub hcover hzero
        (borelMooreHomologyToLim (complSystem L A) KU j x) n
      rw [← ModuleTower.limπ_apply, ← ModuleTower.limπ_apply, this,
        towerToRelative_limπ L hK hKA hsub hcover hzero
          (borelMooreHomologyToLim (complSystem L A) KU j y) n]
      exact hxy
    rw [← sub_eq_zero, ← map_sub] at hlim
    rw [← sub_eq_zero]
    obtain ⟨a, ha⟩ :=
      (exact_limOneToBorelMooreHomology_borelMooreHomologyToLim (complSystem L A) KU j _).1 hlim
    rw [← ha, Subsingleton.elim a 0, map_zero]
  · -- The preimages of `y` under the comparisons form an element of the limit of the tower.
    choose z hz using fun n ↦ (hψ n).2 y
    have hzlim : z ∈ (C.homology j).lim := (ModuleTower.mem_lim _).2 fun n ↦ (hψ n).1 <| by
      rw [hz n, ← hz (n + 1), ModuleTower.transition_def, ← LinearMap.comp_apply,
        ← ModuleCat.hom_comp, homology_map_comp_towerToRelative]
    obtain ⟨x, hx⟩ := borelMooreHomologyToLim_surjective (complSystem L A) KU j ⟨z, hzlim⟩
    rw [← hz 0]
    exact ⟨x, by rw [toTwistedHomology_apply, hx, ModuleTower.limπ_apply]⟩

/-- **Borel–Moore homology of a complement.** Let `A ⊆ X`, and let `Kₙ` be closed compact subsets
of `X` covering `X \ A`, disjoint from `A`, with `Kₙ ⊆ interior Kₙ₊₁`. If the relative homology
`H_*(X \ Kₙ, A; L)` of each open neighbourhood `X \ Kₙ` of `A` vanishes, then the Borel–Moore
homology of `X \ A`, with coefficients in the restriction of `L`, is the relative homology of
`(X, A)`: `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)`. -/
def borelMooreHomologyComplEquiv (j : ℕ) :
    borelMooreHomology
        ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtype_val⟩).obj L) j ≃ₗ[R]
      (TopPair.ofSubset A).twistedHomology L j :=
  LinearEquiv.ofBijective (toTwistedHomology L hK hKA hsub hcover hzero j)
    (toTwistedHomology_bijective L hK hKc hKA hsub hcover hzero j)

/-- The isomorphism `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)` followed by the quotient to
`H_j(X, X \ Kₙ; L)` sends a class to the relative class of its locally finite representatives in
`H_j(X \ A, X \ (A ∪ Kₙ); L)`, followed by excision. -/
theorem twistedHomologyTotalToOuter_borelMooreHomologyComplEquiv (j n : ℕ)
    (x : borelMooreHomology
      ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtype_val⟩).obj L) j) :
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
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f _)
    (@asIso _ _ _ _ _ (isIso_twistedHomologyTotalToOuter L hKA hzero n j)).inv_hom_id

end TauCeti.LocalCoefficientSystem
