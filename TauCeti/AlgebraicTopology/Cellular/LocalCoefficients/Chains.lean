/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Chains
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple

/-!
# The cellular chain complex with local coefficients

Let `C ⊆ X` be a relative CW complex with skeleta `Xⁿ = skeletonLT C (n + 1)` and base
`X⁻¹ = skeletonLT C 0`, and let `L` be a local coefficient system on `X`. Restricting `L` to the
skeleta (`TauCeti.skeletonSystem`), the relative twisted homology groups `Hₙ(Xⁿ, Xⁿ⁻¹; L)` with the
connecting morphisms of the triples `(Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)` of consecutive skeleta form a chain complex
(`TauCeti.twistedCellularChainComplex`), the cellular chain complex of `C` with coefficients in
`L`. It is the local-coefficient form of `TauCeti.cellularChainComplex`.

Consecutive differentials compose to zero for the same reason as for constant coefficients: the
triple connecting morphism factors as the connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ; L)` of
the pair `(Xⁿ⁺¹, Xⁿ)` followed by `Hₙ(Xⁿ; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)`
(`TauCeti.twistedCellularDifferential_eq`), and `Hₙ₊₁(Xⁿ⁺¹; L) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ; L)`
are consecutive maps in the long exact sequence of that pair. The only new ingredient is the
canonical comparison between restricting `L` to `Xⁿ⁺¹` and then to `Xⁿ`, and restricting it to
`Xⁿ` directly (`TauCeti.skeletonPairSubspaceSystemIso`).

The homology of this complex is computed in
`TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology`. With coefficients in the local
system of fibre homology of a fibration over a CW complex, this homology is the group
`H_p(B; H_q(F))` of the second page of the Serre spectral sequence.

## Main definitions

* `TauCeti.skeletonSystem C L n`: the restriction of `L` to the stage `skeletonLT C n`.
* `TauCeti.twistedCellularChainGroup C L n`: the group `Hₙ(Xⁿ, Xⁿ⁻¹; L)`.
* `TauCeti.twistedCellularDifferential C L n`: the connecting morphism of the triple
  `(Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)`.
* `TauCeti.twistedCellularChainComplex C L`: the cellular chain complex with coefficients in `L`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of X))

/-- The restriction of a local coefficient system `L` on `X` to the stage
`skeletonObj C n = skeletonLT C n` of the skeletal filtration of a relative CW complex, that is,
its pullback along the inclusion. -/
abbrev skeletonSystem (n : ℕ) : LocalCoefficientSystem.{u, w, max w v} R (skeletonObj C n) :=
  (LocalCoefficientSystem.pullback (⟨Subtype.val, continuous_subtype_val⟩ :
    C(skeletonObj C n, TopCat.of X))).obj L

/-- Restricting `skeletonSystem C L (n + 1)` further to the subspace `skeletonLT C n` of the
skeletal pair `(Xⁿ, Xⁿ⁻¹)` gives `skeletonSystem C L n`: both are pullbacks of `L` along the
same inclusion. -/
def skeletonPairSubspaceSystemIso (n : ℕ) :
    (skeletonPair C n).subspaceSystem (skeletonSystem C L (n + 1)) ≅ skeletonSystem C L n :=
  ((LocalCoefficientSystem.pullbackCompIso (R := R) (skeletonPair C n).map.hom
    (⟨Subtype.val, continuous_subtype_val⟩ : C(skeletonObj C (n + 1), TopCat.of X))).app L).symm

/-- The cellular chain group of a relative CW complex in degree `n` with coefficients in a local
system `L`: the relative twisted homology `Hₙ(Xⁿ, Xⁿ⁻¹; L)` of the pair of consecutive skeleta. -/
abbrev twistedCellularChainGroup (n : ℕ) : ModuleCat.{max w v} R :=
  (skeletonPair C n).twistedHomology (skeletonSystem C L (n + 1)) n

/-- The cellular differential `Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` with coefficients in a local
system: the connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)` of consecutive skeleta, followed
by the identification of the coefficients `TauCeti.skeletonPairSubspaceSystemIso`. -/
def twistedCellularDifferential (n : ℕ) :
    twistedCellularChainGroup C L (n + 1) ⟶ twistedCellularChainGroup C L n :=
  (skeletonTriple C n).twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n ≫
    (skeletonPair C n).twistedHomologyCoefficientMap
      (skeletonPairSubspaceSystemIso C L (n + 1)).hom n

/-- The cellular differential is the connecting morphism of the triple of consecutive skeleta,
followed by the coefficient identification. -/
lemma twistedCellularDifferential_def (n : ℕ) :
    twistedCellularDifferential C L n =
      (skeletonTriple C n).twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n ≫
        (skeletonPair C n).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L (n + 1)).hom n :=
  (rfl)

/-- The cellular differential is the connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ; L)` of the
pair `(Xⁿ⁺¹, Xⁿ)`, followed by the map `Hₙ(Xⁿ; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` and the coefficient
identification. -/
lemma twistedCellularDifferential_eq (n : ℕ) :
    twistedCellularDifferential C L n =
      (skeletonPair C (n + 1)).twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n rfl ≫
        (skeletonPair C n).twistedHomologyπ
          ((skeletonPair C (n + 1)).subspaceSystem (skeletonSystem C L (n + 1 + 1))) n ≫
        (skeletonPair C n).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L (n + 1)).hom n := by
  rw [twistedCellularDifferential,
    (skeletonTriple C n).twistedHomologyδ_eq_comp_twistedHomologyπ _ (n + 1) n rfl]
  exact Category.assoc _ _ _

/-- The map `Hₙ₊₁(Xⁿ⁺¹; L) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L)`, after the coefficient identification, followed by
the connecting morphism of the pair `(Xⁿ⁺¹, Xⁿ)` is zero. -/
private lemma twistedHomologyπ_comp_coefficientMap_comp_twistedHomologyδ (n : ℕ) :
    ((skeletonPair C (n + 1)).twistedHomologyπ
        ((skeletonPair C (n + 1 + 1)).subspaceSystem (skeletonSystem C L (n + 1 + 1 + 1))) (n + 1) ≫
      (skeletonPair C (n + 1)).twistedHomologyCoefficientMap
        (skeletonPairSubspaceSystemIso C L (n + 1 + 1)).hom (n + 1)) ≫
      (skeletonPair C (n + 1)).twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n rfl =
      0 := by
  have := (skeletonPair C (n + 1)).twistedHomologyπ_comp_twistedHomologyCoefficientMap
    (skeletonPairSubspaceSystemIso C L (n + 1 + 1)).hom (n + 1)
  -- The ambient space of the pair `(Xⁿ⁺¹, Xⁿ)` is the subspace of the next pair only up to
  -- unfolding `MorphismProperty.Arrow.mk`, so `erw` is needed to match the composites.
  erw [this, Category.assoc,
    (skeletonPair C (n + 1)).twistedHomologyπ_comp_twistedHomologyδ _ (n + 1) n rfl, comp_zero]

/-- Two consecutive cellular differentials with local coefficients compose to zero. -/
@[simp]
lemma twistedCellularDifferential_comp_twistedCellularDifferential (n : ℕ) :
    twistedCellularDifferential C L (n + 1) ≫ twistedCellularDifferential C L n = 0 := by
  rw [twistedCellularDifferential_eq, twistedCellularDifferential_eq]
  simp only [Category.assoc]
  -- As above, the middle composite is only matched up to unfolding the pair constructors.
  erw [← Category.assoc _ ((skeletonPair C (n + 1)).twistedHomologyδ _ (n + 1) n rfl),
    twistedHomologyπ_comp_coefficientMap_comp_twistedHomologyδ C L n, zero_comp, comp_zero]

/-- The cellular chain complex of a relative CW complex with coefficients in a local system `L`
on `X`. -/
def twistedCellularChainComplex : ChainComplex (ModuleCat.{max w v} R) ℕ :=
  ChainComplex.of (twistedCellularChainGroup C L) (twistedCellularDifferential C L)
    (twistedCellularDifferential_comp_twistedCellularDifferential C L)

/-- The objects of the cellular chain complex with local coefficients are the cellular chain
groups. -/
@[simp]
lemma twistedCellularChainComplex_X (n : ℕ) :
    (twistedCellularChainComplex C L).X n = twistedCellularChainGroup C L n := (rfl)

/-- The differentials of the cellular chain complex with local coefficients are the cellular
differentials, transported across `TauCeti.twistedCellularChainComplex_X`. -/
@[simp]
lemma twistedCellularChainComplex_d (n : ℕ) :
    (twistedCellularChainComplex C L).d (n + 1) n =
      eqToHom (twistedCellularChainComplex_X C L (n + 1)) ≫ twistedCellularDifferential C L n ≫
        eqToHom (twistedCellularChainComplex_X C L n).symm := by
  -- The object equations hold by definition, so both transports are identities; the body of
  -- `twistedCellularChainComplex` is not exposed, so reducing its differential needs an `unfold`.
  have h : ∀ m : ℕ, twistedCellularChainComplex_X C L m = rfl := fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold twistedCellularChainComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

end TauCeti
