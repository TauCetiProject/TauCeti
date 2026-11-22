/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Chains
public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# The homology of the cellular chain complex with local coefficients

Let `C ⊆ X` be a relative CW complex with skeleta `Xⁿ` and base `X⁻¹`, and let `L` be a local
coefficient system on `C`. This file computes the homology of the cellular chain complex
`TauCeti.twistedCellularChainComplex C L`, following the constant-coefficient argument of
`TauCeti.AlgebraicTopology.Cellular.Homology` and `TauCeti.AlgebraicTopology.Cellular.Comparison`.
The input is the vanishing `Hₖ(Xⁿ, Xⁿ⁻¹; L) = 0` for `k ≠ n`
(`TauCeti.isZero_twistedHomology_skeletonPair_of_ne`), fed into the long exact sequences of the
triples `(Xⁿ⁺¹, Xⁿ, X⁻¹)`.

* `Hₖ(Xⁿ, X⁻¹; L) = 0` for `n < k` (`TauCeti.isZero_twistedHomology_skeletonBasePair_of_lt`).
* The cellular differential factors as the connecting morphism
  `Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ, X⁻¹; L)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`
  (`TauCeti.twistedSkeletonBaseTripleδ`) followed by the monomorphism
  `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` (`TauCeti.twistedCellularCyclesι`).
* Hence the cellular cycles are `Hₙ(Xⁿ, X⁻¹; L)` (`TauCeti.twistedCellularCyclesIso`), and the
  cellular homology in degree `n` is `Hₙ(Xⁿ⁺¹, X⁻¹; L)` (`TauCeti.twistedCellularHomologyIso`).
* The inclusions `(Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹, X⁻¹)` induce isomorphisms on `Hₖ` for `k < n`
  (`TauCeti.isIso_twistedHomologySkeletonBasePairToSucc`).
* Hence the inclusion `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism on `Hₖ` for `k < m`
  (`TauCeti.isIso_twistedHomologySkeletonBasePairToComplex`), with no dimension bound on the
  complex.
* So the cellular homology is the twisted relative singular homology `Hₙ(C, D; L)` of the complex
  (`TauCeti.twistedCellularSingularHomologyIso`).

The comparison with the whole complex is the compact-support argument of
`TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic`, made on relative chains. A
relative chain of `(C, X⁻¹)` is the class of a chain of `C` supported on finitely many simplices.
Their images form a compact set, which lies in a skeleton
(`TauCeti.exists_subset_skeletonLT_of_isCompact`). The relative chains of the pairs `(Xʲ, X⁻¹)`
inject into those of `(C, X⁻¹)`, because the subspace is the same
(`TopPair.twistedChainComplexMap_f_injective`). So a class of `Hₖ(C, X⁻¹; L)` comes from some
`Hₖ(Xʲ, X⁻¹; L)`, and a class of `Hₖ(Xᵐ, X⁻¹; L)` vanishing in `Hₖ(C, X⁻¹; L)` already vanishes in
some `Hₖ(Xʲ, X⁻¹; L)`. For `k < m ≤ j` the map `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(Xʲ, X⁻¹; L)` is an isomorphism.
With coefficients in the local system of fibre homology of a fibration over a CW complex `B`, this
identifies the cellular homology with the groups `H_p(B; H_q(F))`, with no finiteness or dimension
assumption on `B`.

The base `X⁻¹` is `skeletonLT C 0`, as in `TauCeti.skeletonBasePair`. In degree `0` the pairs
`(X⁰, X⁻¹)` and `(X⁰, X⁻¹)` of `TauCeti.skeletonBasePair` and `TauCeti.skeletonPair` coincide, and
`TauCeti.twistedCellularCyclesι` is the identity there.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34 and Theorem 2.35, Section 3.H, and
  Proposition A.1 of the Appendix for compact subsets of CW complexes.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

/-! ### The maps of the triples `(Xⁿ⁺¹, Xⁿ, X⁻¹)` -/

/-- The map `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` induced by the identity of `Xⁿ`. For `n = 0` the two
pairs are `(X⁰, X⁻¹)` and the map is the identity. -/
def twistedCellularCyclesι : (n : ℕ) →
    ((skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) n ⟶
      twistedCellularChainGroup C L n)
  | 0 => 𝟙 _
  | n + 1 => (skeletonBaseTriple C n).twistedHomologyTotalToOuter
      (skeletonSystem C L (n + 1 + 1)) (n + 1)

@[simp]
lemma twistedCellularCyclesι_zero : twistedCellularCyclesι C L 0 = 𝟙 _ := (rfl)

lemma twistedCellularCyclesι_succ (n : ℕ) :
    twistedCellularCyclesι C L (n + 1) = (skeletonBaseTriple C n).twistedHomologyTotalToOuter
      (skeletonSystem C L (n + 1 + 1)) (n + 1) :=
  (rfl)

/-- The connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ, X⁻¹; L)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`,
followed by the coefficient identification `TauCeti.skeletonPairSubspaceSystemIso`. -/
def twistedSkeletonBaseTripleδ (n : ℕ) :
    twistedCellularChainGroup C L (n + 1) ⟶
      (skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) n :=
  (skeletonBaseTriple C n).twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n rfl ≫
    (skeletonBasePair C n).twistedHomologyCoefficientMap
      (skeletonPairSubspaceSystemIso C L (n + 1)).hom n

lemma twistedSkeletonBaseTripleδ_def (n : ℕ) :
    twistedSkeletonBaseTripleδ C L n =
      (skeletonBaseTriple C n).twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n rfl ≫
        (skeletonBasePair C n).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L (n + 1)).hom n :=
  (rfl)

/-- The map `Hₖ(Xⁿ, X⁻¹; L) ⟶ Hₖ(Xⁿ⁺¹, X⁻¹; L)` induced by the inclusion of pairs, after the
coefficient identification `TauCeti.skeletonPairSubspaceSystemIso`. -/
def twistedHomologySkeletonBasePairToSucc (n k : ℕ) :
    (skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) k ⟶
      (skeletonBasePair C (n + 1)).twistedHomology (skeletonSystem C L (n + 1 + 1)) k :=
  (skeletonBasePair C n).twistedHomologyCoefficientMap
      (skeletonPairSubspaceSystemIso C L (n + 1)).inv k ≫
    TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1)) k

lemma twistedHomologySkeletonBasePairToSucc_def (n k : ℕ) :
    twistedHomologySkeletonBasePairToSucc C L n k =
      (skeletonBasePair C n).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L (n + 1)).inv k ≫
        TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
          (skeletonSystem C L (n + 1 + 1)) k :=
  (rfl)

/-- The connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` followed by the map
`Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ⁺¹, X⁻¹; L)` is zero. -/
@[reassoc (attr := simp)]
lemma twistedSkeletonBaseTripleδ_comp_twistedHomologySkeletonBasePairToSucc (n : ℕ) :
    twistedSkeletonBaseTripleδ C L n ≫ twistedHomologySkeletonBasePairToSucc C L n n = 0 := by
  rw [twistedSkeletonBaseTripleδ, twistedHomologySkeletonBasePairToSucc]
  -- The coefficient maps live on `skeletonBasePair C n`, which is the inner pair of the triple
  -- only up to unfolding the pair constructors; `erw` cancels them.
  erw [Category.assoc, TopPair.twistedHomologyCoefficientMap_hom_inv_id_assoc (skeletonBasePair C n)
    (skeletonPairSubspaceSystemIso C L (n + 1)) n]
  exact (skeletonBaseTriple C n).twistedHomologyδ_comp _ (n + 1) n rfl

/-- The map `Hₙ₊₁(Xⁿ⁺¹, X⁻¹; L) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L)` followed by the connecting morphism
`Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ, X⁻¹; L)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` is zero. -/
@[reassoc (attr := simp)]
lemma twistedCellularCyclesι_comp_twistedSkeletonBaseTripleδ (n : ℕ) :
    twistedCellularCyclesι C L (n + 1) ≫ twistedSkeletonBaseTripleδ C L n = 0 := by
  rw [twistedCellularCyclesι, twistedSkeletonBaseTripleδ]
  -- `comp_twistedHomologyδ_assoc` is stated for the triple's own pairs; `erw` matches them.
  erw [(skeletonBaseTriple C n).comp_twistedHomologyδ_assoc _ (n + 1) n rfl, zero_comp]
  rfl

/-- The quotient `Hₙ(Xⁿ; L) ⟶ Hₙ(Xⁿ, X⁻¹; L)` followed by `TauCeti.twistedCellularCyclesι` is the
quotient `Hₙ(Xⁿ; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)`. -/
@[reassoc (attr := simp)]
lemma twistedHomologyπ_comp_twistedCellularCyclesι (n : ℕ) :
    (skeletonBasePair C n).twistedHomologyπ (skeletonSystem C L (n + 1)) n ≫
        twistedCellularCyclesι C L n =
      (skeletonPair C n).twistedHomologyπ (skeletonSystem C L (n + 1)) n := by
  cases n with
  | zero => exact Category.comp_id _
  | succ n =>
    rw [twistedCellularCyclesι, TopTriple.twistedHomologyTotalToOuter]
    -- The chain-level identity `twistedChainComplexπ_comp_totalToOuter` is stated for the
    -- triple's total and outer pairs, which are the base and skeletal pairs after unfolding.
    erw [← HomologicalComplex.homologyMap_comp,
      (skeletonBaseTriple C n).twistedChainComplexπ_comp_totalToOuter]
    rfl

private lemma twistedHomologyπ_comp_coefficientMap_comp_twistedCellularCyclesι (n : ℕ) :
    (skeletonBasePair C n).twistedHomologyπ
        ((skeletonPair C (n + 1)).subspaceSystem (skeletonSystem C L (n + 1 + 1))) n ≫
      (skeletonBasePair C n).twistedHomologyCoefficientMap
        (skeletonPairSubspaceSystemIso C L (n + 1)).hom n ≫ twistedCellularCyclesι C L n =
    (skeletonPair C n).twistedHomologyπ
        ((skeletonPair C (n + 1)).subspaceSystem (skeletonSystem C L (n + 1 + 1))) n ≫
      (skeletonPair C n).twistedHomologyCoefficientMap
        (skeletonPairSubspaceSystemIso C L (n + 1)).hom n := by
  -- Both sides change coefficients on the ambient space first; the pairs agree after unfolding.
  erw [TopPair.twistedHomologyπ_comp_twistedHomologyCoefficientMap_assoc,
    twistedHomologyπ_comp_twistedCellularCyclesι,
    TopPair.twistedHomologyπ_comp_twistedHomologyCoefficientMap]
  rfl

/-- **The cellular differential factors through the base pair**: it is the connecting morphism
`Hₙ₊₁(Xⁿ⁺¹, Xⁿ; L) ⟶ Hₙ(Xⁿ, X⁻¹; L)` of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` followed by the map
`Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)`. -/
lemma twistedCellularDifferential_eq_twistedSkeletonBaseTripleδ_comp (n : ℕ) :
    twistedCellularDifferential C L n =
      twistedSkeletonBaseTripleδ C L n ≫ twistedCellularCyclesι C L n := by
  rw [twistedCellularDifferential_eq_twistedHomologyδ_comp_twistedHomologyπ,
    twistedSkeletonBaseTripleδ,
    (skeletonBaseTriple C n).twistedHomologyδ_eq_comp_twistedHomologyπ _ (n + 1) n rfl]
  -- Both sides begin with the connecting morphism of the pair `(Xⁿ⁺¹, Xⁿ)`. The outer and inner
  -- pairs of the triple are `skeletonPair C n` and `skeletonBasePair C n` only after unfolding the
  -- pair constructors, so the composites are matched by terms rather than by rewriting.
  exact (congrArg (_ ≫ ·)
    (twistedHomologyπ_comp_coefficientMap_comp_twistedCellularCyclesι C L n).symm).trans
      (Category.assoc _ _ _).symm

/-! ### Vanishing and the stable range -/

/-- **The homology of a skeleton relative to the base vanishes above its dimension**:
`Hₖ(Xⁿ, X⁻¹; K) = 0` for `n < k` and every local coefficient system `K` on `Xⁿ`. -/
theorem isZero_twistedHomology_skeletonBasePair_of_lt {n k : ℕ} (hk : n < k)
    (K : LocalCoefficientSystem.{u, w, max w v} R (skeletonBasePair C n).fst) :
    IsZero ((skeletonBasePair C n).twistedHomology K k) := by
  induction n with
  | zero => exact isZero_twistedHomology_skeletonPair_of_ne C hk.ne' K
  | succ n ih =>
    exact ((skeletonBaseTriple C n).twistedHomology_exact_total K k).isZero_X₂
      ((ih (by lia) _).eq_of_src _ _)
      ((isZero_twistedHomology_skeletonPair_of_ne C (by lia) K).eq_of_tgt _ _)

/-- The map `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` is a monomorphism: its kernel is a quotient of
`Hₙ(Xⁿ⁻¹, X⁻¹; L) = 0`. -/
instance mono_twistedCellularCyclesι (n : ℕ) : Mono (twistedCellularCyclesι C L n) := by
  cases n with
  | zero => exact inferInstanceAs (Mono (𝟙 _))
  | succ n =>
    exact ((skeletonBaseTriple C n).twistedHomology_exact_total _ (n + 1)).mono_g
      ((isZero_twistedHomology_skeletonBasePair_of_lt C (by lia) _).eq_of_src _ _)

/-- The map `Hₖ(Xⁿ, X⁻¹; L) ⟶ Hₖ(Xⁿ⁺¹, X⁻¹; L)` is surjective for `k ≠ n + 1`: its cokernel
embeds in `Hₖ(Xⁿ⁺¹, Xⁿ; L) = 0`. -/
theorem epi_twistedHomologySkeletonBasePairToSucc {n k : ℕ} (hk : k ≠ n + 1) :
    Epi (twistedHomologySkeletonBasePairToSucc C L n k) := by
  have h : Epi (TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1)) k) :=
    ((skeletonBaseTriple C n).twistedHomology_exact_total _ k).epi_f
      ((isZero_twistedHomology_skeletonPair_of_ne C hk _).eq_of_tgt _ _)
  -- The coefficient isomorphisms below live on ambient spaces that agree with that of
  -- `skeletonBasePair C n` only after unfolding the pair constructors, so instance search does
  -- not find their `IsIso` instances; they are supplied explicitly.
  have := @TopPair.isIso_twistedHomologyCoefficientMap _ _ (skeletonBasePair C n) _ _
    (skeletonPairSubspaceSystemIso C L (n + 1)).inv (Iso.isIso_inv _) k
  exact epi_comp' inferInstance h

instance epi_twistedHomologySkeletonBasePairToSucc_self (n : ℕ) :
    Epi (twistedHomologySkeletonBasePairToSucc C L n n) :=
  epi_twistedHomologySkeletonBasePairToSucc C L (by lia)

/-- The map `Hₖ(Xⁿ, X⁻¹; L) ⟶ Hₖ(Xⁿ⁺¹, X⁻¹; L)` is an isomorphism for `k < n`: the adjacent groups
`Hₖ₊₁(Xⁿ⁺¹, Xⁿ; L)` and `Hₖ(Xⁿ⁺¹, Xⁿ; L)` vanish. -/
theorem isIso_twistedHomologySkeletonBasePairToSucc {n k : ℕ} (hk : k < n) :
    IsIso (twistedHomologySkeletonBasePairToSucc C L n k) := by
  have := epi_twistedHomologySkeletonBasePairToSucc C L (n := n) (k := k) (by lia)
  have h : Mono (TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1)) k) :=
    ((skeletonBaseTriple C n).twistedHomology_exact_inner _ (k + 1) k rfl).mono_g
      ((isZero_twistedHomology_skeletonPair_of_ne C (by lia) _).eq_of_src _ _)
  have := @TopPair.isIso_twistedHomologyCoefficientMap _ _ (skeletonBasePair C n) _ _
    (skeletonPairSubspaceSystemIso C L (n + 1)).inv (Iso.isIso_inv _) k
  have : Mono (twistedHomologySkeletonBasePairToSucc C L n k) := mono_comp' inferInstance h
  exact isIso_of_mono_of_epi _

/-! ### The left homology datum -/

/-- The map `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)`, read in the cellular chain complex. -/
private def twistedCellularCyclesιX (n : ℕ) :
    (skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) n ⟶
      (twistedCellularChainComplex C L).X n :=
  twistedCellularCyclesι C L n ≫ eqToHom (twistedCellularChainComplex_X C L n).symm

private instance (n : ℕ) : Mono (twistedCellularCyclesιX C L n) := by
  unfold twistedCellularCyclesιX
  infer_instance

/-- The differential of the cellular chain complex with local coefficients out of degree `n + 1`
factors through the connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
private lemma twistedCellularChainComplex_d_eq (n : ℕ) :
    (twistedCellularChainComplex C L).d (n + 1) n =
      eqToHom (twistedCellularChainComplex_X C L (n + 1)) ≫ twistedSkeletonBaseTripleδ C L n ≫
        twistedCellularCyclesιX C L n := by
  rw [twistedCellularChainComplex_d, twistedCellularDifferential_eq_twistedSkeletonBaseTripleδ_comp]
  simp only [twistedCellularCyclesιX, Category.assoc]

private lemma twistedCellularCyclesι_comp_d (n : ℕ) :
    twistedCellularCyclesιX C L n ≫ (twistedCellularChainComplex C L).d n (n - 1) = 0 := by
  cases n with
  | zero =>
    rw [(twistedCellularChainComplex C L).shape 0 (0 - 1) (by simp)]
    exact comp_zero
  | succ n =>
    rw [Nat.add_sub_cancel, twistedCellularChainComplex_d_eq]
    simp [twistedCellularCyclesιX]

private lemma twistedCellularCycles_exact (n : ℕ) :
    (ShortComplex.mk _ _ (twistedCellularCyclesι_comp_d C L n)).Exact := by
  cases n with
  | zero =>
    rw [ShortComplex.exact_iff_epi _ ((twistedCellularChainComplex C L).shape 0 0 (by simp))]
    dsimp only [twistedCellularCyclesιX]
    rw [twistedCellularCyclesι_zero, Category.id_comp]
    infer_instance
  | succ n =>
    let φ : ShortComplex.mk _ _
        ((skeletonBaseTriple C n).comp_twistedHomologyδ (skeletonSystem C L (n + 1 + 1)) (n + 1) n
          rfl) ⟶ ShortComplex.mk _ _ (twistedCellularCyclesι_comp_d C L (n + 1)) :=
      { τ₁ := 𝟙 _
        τ₂ := eqToHom (twistedCellularChainComplex_X C L (n + 1)).symm
        τ₃ := (skeletonBasePair C n).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L (n + 1)).hom n ≫ twistedCellularCyclesιX C L n
        comm₁₂ := (Category.id_comp _).trans (by
          dsimp only [twistedCellularCyclesιX]
          rw [twistedCellularCyclesι_succ]
          -- The two `eqToHom`s start at `twistedCellularChainGroup C L (n + 1)` and at the
          -- homology of the triple's outer pair; these are the same object only after unfolding
          -- the pair constructors, so `rfl` rather than `rw` closes the goal.
          rfl)
        comm₂₃ := by
          -- `change` projects the components of `ShortComplex.mk` and reduces the index
          -- `n + 1 - 1` to `n`; rewriting with `Nat.add_sub_cancel` instead fails because the
          -- right-hand side lands in the chain group of index `n`.
          change eqToHom (twistedCellularChainComplex_X C L (n + 1)).symm ≫
            (twistedCellularChainComplex C L).d (n + 1) n = _
          rw [twistedCellularChainComplex_d_eq, eqToHom_trans_assoc,
            eqToHom_refl, Category.id_comp, twistedSkeletonBaseTripleδ]
          exact Category.assoc _ _ _ }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso φ.τ₂ :=
      inferInstanceAs (IsIso (eqToHom (twistedCellularChainComplex_X C L (n + 1)).symm))
    have : Mono φ.τ₃ := mono_comp' (@TopPair.isIso_twistedHomologyCoefficientMap _ _
      (skeletonBasePair C n) _ _ (skeletonPairSubspaceSystemIso C L (n + 1)).hom
      (Iso.isIso_hom _) n).mono_of_iso
      inferInstance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      ((skeletonBaseTriple C n).twistedHomology_exact_outer _ (n + 1) n rfl)

/-- Exactness at `Hₙ(Xⁿ, X⁻¹; L)` in the sequence of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
lemma skeletonBaseTriple_twistedHomology_exact_inner (n : ℕ) :
    (ShortComplex.mk _ _
      (twistedSkeletonBaseTripleδ_comp_twistedHomologySkeletonBasePairToSucc C L n)).Exact := by
  let φ : ShortComplex.mk _ _
      ((skeletonBaseTriple C n).twistedHomologyδ_comp (skeletonSystem C L (n + 1 + 1)) (n + 1) n
        rfl) ⟶
      ShortComplex.mk _ _
        (twistedSkeletonBaseTripleδ_comp_twistedHomologySkeletonBasePairToSucc C L n) :=
    { τ₁ := 𝟙 _
      τ₂ := (skeletonBasePair C n).twistedHomologyCoefficientMap
        (skeletonPairSubspaceSystemIso C L (n + 1)).hom n
      τ₃ := 𝟙 _
      comm₁₂ := (Category.id_comp _).trans (twistedSkeletonBaseTripleδ_def C L n)
      comm₂₃ := (by
        dsimp only
        unfold twistedHomologySkeletonBasePairToSucc
        exact (TopPair.twistedHomologyCoefficientMap_hom_inv_id_assoc
          (skeletonBasePair C n) (skeletonPairSubspaceSystemIso C L (n + 1)) n _).trans
            (Category.comp_id _).symm) }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ.τ₂ := @TopPair.isIso_twistedHomologyCoefficientMap _ _
    (skeletonBasePair C n) _ _ (skeletonPairSubspaceSystemIso C L (n + 1)).hom (Iso.isIso_hom _) n
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    ((skeletonBaseTriple C n).twistedHomology_exact_inner _ (n + 1) n rfl)

/-- The kernel lift of the incoming cellular differential through `Hₙ(Xⁿ, X⁻¹; L)` is the
connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
private lemma twistedCellularCycles_lift_eq (n : ℕ) :
    (twistedCellularCycles_exact C L n).fIsKernel.lift
        (KernelFork.ofι ((twistedCellularChainComplex C L).d (n + 1) n)
          ((twistedCellularChainComplex C L).d_comp_d (n + 1) n (n - 1))) =
      eqToHom (twistedCellularChainComplex_X C L (n + 1)) ≫ twistedSkeletonBaseTripleδ C L n := by
  rw [← cancel_mono (twistedCellularCyclesιX C L n), Category.assoc,
    ← twistedCellularChainComplex_d_eq]
  exact Fork.IsLimit.lift_ι _

/-- The cellular homology with local coefficients as a left homology datum. -/
private def twistedCellularLeftHomologyData (n : ℕ) :
    ((twistedCellularChainComplex C L).sc' (n + 1) n (n - 1)).LeftHomologyData where
  K := (skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) n
  H := (skeletonBasePair C (n + 1)).twistedHomology (skeletonSystem C L (n + 1 + 1)) n
  i := twistedCellularCyclesιX C L n
  wi := twistedCellularCyclesι_comp_d C L n
  hi := (twistedCellularCycles_exact C L n).fIsKernel
  π := twistedHomologySkeletonBasePairToSucc C L n n
  wπ := by
    refine (congrArg (· ≫ _) (twistedCellularCycles_lift_eq C L n)).trans ?_
    rw [Category.assoc, twistedSkeletonBaseTripleδ_comp_twistedHomologySkeletonBasePairToSucc]
    exact comp_zero
  hπ := isCokernelEpiComp (skeletonBaseTriple_twistedHomology_exact_inner C L n).gIsCokernel
    (eqToHom (twistedCellularChainComplex_X C L (n + 1))) (twistedCellularCycles_lift_eq C L n)

/-- The cycles of the cellular chain complex with local coefficients in degree `n` are
`Hₙ(Xⁿ, X⁻¹; L)`. -/
def twistedCellularCyclesIso (n : ℕ) :
    (twistedCellularChainComplex C L).cycles n ≅
      (skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) n :=
  (twistedCellularChainComplex C L).cyclesIsoSc' (n + 1) n (n - 1) (by simp)
    (by cases n <;> simp) ≪≫ (twistedCellularLeftHomologyData C L n).cyclesIso

@[reassoc (attr := simp)]
lemma twistedCellularCyclesIso_inv_comp_iCycles (n : ℕ) :
    (twistedCellularCyclesIso C L n).inv ≫ (twistedCellularChainComplex C L).iCycles n =
      twistedCellularCyclesι C L n ≫ eqToHom (twistedCellularChainComplex_X C L n).symm :=
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((twistedCellularChainComplex C L).cyclesIsoSc'_inv_iCycles _ _ _ _ _)).trans
      (twistedCellularLeftHomologyData C L n).cyclesIso_inv_comp_iCycles

/-- **The homology of the cellular chain complex with local coefficients** in degree `n` is
`Hₙ(Xⁿ⁺¹, X⁻¹; L)`. -/
def twistedCellularHomologyIso (n : ℕ) :
    (twistedCellularChainComplex C L).homology n ≅
      (skeletonBasePair C (n + 1)).twistedHomology (skeletonSystem C L (n + 1 + 1)) n :=
  (twistedCellularChainComplex C L).homologyIsoSc' (n + 1) n (n - 1) (by simp)
    (by cases n <;> simp) ≪≫ (twistedCellularLeftHomologyData C L n).homologyIso

@[reassoc (attr := simp)]
lemma homologyπ_comp_twistedCellularHomologyIso_hom (n : ℕ) :
    (twistedCellularChainComplex C L).homologyπ n ≫ (twistedCellularHomologyIso C L n).hom =
      (twistedCellularCyclesIso C L n).hom ≫ twistedHomologySkeletonBasePairToSucc C L n n := by
  have h := (twistedCellularChainComplex C L).π_homologyIsoSc'_hom_assoc (n + 1) n (n - 1)
    (by simp) (by cases n <;> simp) (twistedCellularLeftHomologyData C L n).homologyIso.hom
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom] at h
  exact h.trans (Category.assoc _ _ _).symm

/-! ### Comparison with the whole complex -/

/-- Pulling `L` back along the inclusion of the `m`-skeleton into the complex, as a map of pairs,
gives `skeletonSystem C L (m + 1)`. -/
lemma skeletonSystem_eq_pullback (m : ℕ) :
    skeletonSystem C L (m + 1) = (LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (skeletonBasePairToComplex C m)).hom).obj L := by
  rw [skeletonBasePairToComplex_fst]
  rfl

/-- `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)`, induced by the inclusion of the `m`-skeleton. -/
def twistedHomologySkeletonBasePairToComplex (m k : ℕ) :
    (skeletonBasePair C m).twistedHomology (skeletonSystem C L (m + 1)) k ⟶
      (complexBasePair C).twistedHomology L k :=
  (skeletonBasePair C m).twistedHomologyCoefficientMap
      (eqToHom (skeletonSystem_eq_pullback C L m)) k ≫
    TopPair.twistedHomologyMap (skeletonBasePairToComplex C m) L k

lemma twistedHomologySkeletonBasePairToComplex_def (m k : ℕ) :
    twistedHomologySkeletonBasePairToComplex C L m k =
      (skeletonBasePair C m).twistedHomologyCoefficientMap
          (eqToHom (skeletonSystem_eq_pullback C L m)) k ≫
        TopPair.twistedHomologyMap (skeletonBasePairToComplex C m) L k :=
  (rfl)

/-- The map of relative twisted chains inducing `TauCeti.twistedHomologySkeletonBasePairToSucc`. -/
private def twistedChainSkeletonBasePairToSucc (n : ℕ) :
    (skeletonBasePair C n).twistedChainComplex (skeletonSystem C L (n + 1)) ⟶
      (skeletonBasePair C (n + 1)).twistedChainComplex (skeletonSystem C L (n + 1 + 1)) :=
  (skeletonBasePair C n).twistedChainComplexCoefficientMap
      (skeletonPairSubspaceSystemIso C L (n + 1)).inv ≫
    TopPair.twistedChainComplexMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1))

/-- The map of relative twisted chains inducing
`TauCeti.twistedHomologySkeletonBasePairToComplex`. -/
private def twistedChainSkeletonBasePairToComplex (m : ℕ) :
    (skeletonBasePair C m).twistedChainComplex (skeletonSystem C L (m + 1)) ⟶
      (complexBasePair C).twistedChainComplex L :=
  (skeletonBasePair C m).twistedChainComplexCoefficientMap
      (eqToHom (skeletonSystem_eq_pullback C L m)) ≫
    TopPair.twistedChainComplexMap (skeletonBasePairToComplex C m) L

/-- `twistedChainSkeletonBasePairToComplex` starts with the isomorphism of relative twisted chains
given by the coefficient identification. -/
private lemma twistedChainSkeletonBasePairToComplex_eq (m : ℕ) :
    twistedChainSkeletonBasePairToComplex C L m =
      ((skeletonBasePair C m).twistedChainComplexCoefficientIso
          (eqToIso (skeletonSystem_eq_pullback C L m))).hom ≫
        TopPair.twistedChainComplexMap (skeletonBasePairToComplex C m) L :=
  congrArg (· ≫ _) (TopPair.twistedChainComplexCoefficientIso_hom (skeletonBasePair C m)
    (eqToIso (skeletonSystem_eq_pullback C L m))).symm

private lemma homologyMap_twistedChainSkeletonBasePairToSucc (n k : ℕ) :
    HomologicalComplex.homologyMap (twistedChainSkeletonBasePairToSucc C L n) k =
      twistedHomologySkeletonBasePairToSucc C L n k :=
  HomologicalComplex.homologyMap_comp _ _ _

private lemma homologyMap_twistedChainSkeletonBasePairToComplex (m k : ℕ) :
    HomologicalComplex.homologyMap (twistedChainSkeletonBasePairToComplex C L m) k =
      twistedHomologySkeletonBasePairToComplex C L m k :=
  HomologicalComplex.homologyMap_comp _ _ _

/-- The inclusion of the `m`-skeleton into the complex factors through the `(m + 1)`-skeleton, on
relative twisted chains. -/
private lemma twistedChainSkeletonBasePairToSucc_comp_twistedChainSkeletonBasePairToComplex
    (m : ℕ) :
    twistedChainSkeletonBasePairToSucc C L m ≫ twistedChainSkeletonBasePairToComplex C L (m + 1) =
      twistedChainSkeletonBasePairToComplex C L m := by
  have h : (TopTriple.innerToTotal.app (skeletonBaseTriple C m) ≫
      skeletonBasePairToComplex C (m + 1) : skeletonBasePair C m ⟶ complexBasePair C) =
      skeletonBasePairToComplex C m :=
    (congrArg (· ≫ skeletonBasePairToComplex C (m + 1))
      ((skeletonBasePairToSucc_def C m).symm.trans (skeletonBasePairInclusion_succ C m).symm)).trans
      (skeletonBasePairInclusion_comp_toComplex C m.le_succ)
  have e₁ := TopPair.twistedChainComplexMap_comp (P := skeletonBasePair C m)
    (Q := skeletonBasePair C (m + 1)) (TopTriple.innerToTotal.app (skeletonBaseTriple C m))
    (skeletonBasePairToComplex C (m + 1)) L
  have e₂ := TopPair.twistedChainComplexMap_naturality_assoc (P := skeletonBasePair C m)
    (Q := skeletonBasePair C (m + 1)) (TopTriple.innerToTotal.app (skeletonBaseTriple C m))
    (skeletonSystem C L (m + 1 + 1)) (eqToHom (skeletonSystem_eq_pullback C L (m + 1)))
    (TopPair.twistedChainComplexMap (skeletonBasePairToComplex C (m + 1)) L)
  -- Write both sides as a coefficient map followed by the maps induced by the inclusions
  -- `(Xᵐ, X⁻¹) ⟶ (Xᵐ⁺¹, X⁻¹) ⟶ (C, X⁻¹)`; the triple's inner and total pairs are the base pairs
  -- only after unfolding the pair constructors, so `e₁` and `e₂` are applied by `erw`.
  rw [twistedChainSkeletonBasePairToSucc, twistedChainSkeletonBasePairToComplex,
    twistedChainSkeletonBasePairToComplex, TopPair.twistedChainComplexMap_congr L h.symm]
  erw [e₁, Category.assoc, e₂]
  erw [← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc]
  refine congrArg (fun η ↦ (skeletonBasePair C m).twistedChainComplexCoefficientMap η ≫ _) ?_
  refine NatTrans.ext (funext fun x ↦ ?_)
  -- Every coefficient identification is the identity or an `eqToHom` on each fibre. The fibres
  -- are those of systems on `(skeletonBasePair C m).fst`, which is `skeletonObj C (m + 1)` only
  -- after unfolding the pair constructors, so the components are computed by `erw`.
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    skeletonPairSubspaceSystemIso_inv_app, TopPair.fstPullbackCompIso_hom_app, Category.id_comp,
    Category.comp_id, LocalCoefficientSystem.pullback_map_app, eqToHom_app, eqToHom_app,
    eqToHom_app, eqToHom_trans]
  rfl

/-- The inclusion of the `m`-skeleton into the complex factors through the `(m + 1)`-skeleton. -/
@[reassoc (attr := simp)]
lemma twistedHomologySkeletonBasePairToSucc_comp_twistedHomologySkeletonBasePairToComplex
    (m k : ℕ) :
    twistedHomologySkeletonBasePairToSucc C L m k ≫
        twistedHomologySkeletonBasePairToComplex C L (m + 1) k =
      twistedHomologySkeletonBasePairToComplex C L m k := by
  rw [← homologyMap_twistedChainSkeletonBasePairToSucc,
    ← homologyMap_twistedChainSkeletonBasePairToComplex,
    ← homologyMap_twistedChainSkeletonBasePairToComplex, ← HomologicalComplex.homologyMap_comp,
    twistedChainSkeletonBasePairToSucc_comp_twistedChainSkeletonBasePairToComplex]

/-- If the `m`-skeleton is the whole complex, `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` is an
isomorphism. -/
theorem isIso_twistedHomologySkeletonBasePairToComplex_of_eq {m : ℕ}
    (hm : (skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) = C) (k : ℕ) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L m k) := by
  have := isIso_skeletonBasePairToComplex_of_eq C m hm
  have := LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_isIso L
    (skeletonBasePairToComplex C m) k
  have := @TopPair.isIso_twistedHomologyCoefficientMap _ _ (skeletonBasePair C m) _ _
    (eqToHom (skeletonSystem_eq_pullback C L m))
    (Iso.isIso_hom (eqToIso (skeletonSystem_eq_pullback C L m))) k
  exact IsIso.comp_isIso

/-! ### Comparison with the whole complex: compact supports -/

/-- Every relative twisted chain of the whole complex comes from the relative twisted chains of a
skeleton: an ambient chain is supported on finitely many simplices, whose images form a compact
set, and a compact subset of a CW complex lies in a finite skeleton. -/
private lemma exists_twistedChainSkeletonBasePairToComplex_f_eq (n : ℕ) {k : ℕ}
    (y : ((complexBasePair C).twistedChainComplex L).X k) :
    ∃ (d : ℕ) (z : ((skeletonBasePair C (n + d)).twistedChainComplex
        (skeletonSystem C L (n + d + 1))).X k),
      ((twistedChainSkeletonBasePairToComplex C L (n + d)).f k).hom z = y := by
  obtain ⟨c, rfl⟩ := (complexBasePair C).twistedChainComplexπ_f_surjective L y
  -- The chain `c` is supported in a compact subset `K` of the complex, which lies in a skeleton.
  obtain ⟨K, hK, hc⟩ :=
    LocalCoefficientSystem.exists_isCompact_forall_mem_range_twistedChainComplexMap_f L c
  obtain ⟨d, hd⟩ := exists_subset_skeletonLT_of_isCompact (C := C)
    (hK.image continuous_subtypeVal) (by rintro _ ⟨x, -, rfl⟩; exact x.property)
  set m := n + d
  let ι : skeletonObj C (m + 1) ⟶ TopCat.of C :=
    TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C ((m + 1 : ℕ) : ℕ∞)).subset_complex)
  have hι : Set.range ι = {x : C | (x : X) ∈ skeletonLT C ((m + 1 : ℕ) : ℕ∞)} := by
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  -- So `c` is the pushforward of a chain `c'` of the skeleton.
  obtain ⟨c', hc'⟩ : c ∈ LinearMap.range ((LocalCoefficientSystem.twistedChainComplexMap
      (TopPair.Hom.fst (skeletonBasePairToComplex C m)) L).f k).hom := by
    -- After rewriting the ambient map to `ι`, its codomain is `(complexBasePair C).fst`, which is
    -- `TopCat.of C` only after unfolding the pair constructor, so the range lemmas apply by `erw`.
    rw [skeletonBasePairToComplex_fst]
    erw [LocalCoefficientSystem.range_twistedChainComplexMap_f ι L
      (Topology.IsEmbedding.inclusion (skeletonLT C ((m + 1 : ℕ) : ℕ∞)).subset_complex).isInducing,
      hι, ← LocalCoefficientSystem.range_twistedChainComplexMap_subtypeVal_f]
    exact hc _ fun x hx ↦
      skeletonLT_mono (by exact_mod_cast (by lia : d ≤ m + 1)) (hd ⟨x, hx, rfl⟩)
  let e := (skeletonBasePair C m).twistedChainComplexCoefficientIso
    (eqToIso (skeletonSystem_eq_pullback C L m))
  have hφ : e.inv ≫ twistedChainSkeletonBasePairToComplex C L m =
      TopPair.twistedChainComplexMap (skeletonBasePairToComplex C m) L := by
    rw [twistedChainSkeletonBasePairToComplex_eq, e.inv_hom_id_assoc]
  refine ⟨d, (e.inv.f k) (((skeletonBasePair C m).twistedChainComplexπ _).f k c'), ?_⟩
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, hφ]
  exact (TopPair.twistedChainComplexMap_f_twistedChainComplexπ_f_apply
    (skeletonBasePairToComplex C m) L c').trans
      (congrArg (fun x ↦ (((complexBasePair C).twistedChainComplexπ L).f k).hom x) hc')

/-- The maps of relative twisted chains from the `m`-skeleton to the `(m + d)`-skeleton, composed
of the maps to the next skeleton. -/
private def twistedChainSkeletonBasePairIter (m : ℕ) : (d : ℕ) →
    ((skeletonBasePair C m).twistedChainComplex (skeletonSystem C L (m + 1)) ⟶
      (skeletonBasePair C (m + d)).twistedChainComplex (skeletonSystem C L (m + d + 1)))
  | 0 => 𝟙 _
  | d + 1 => twistedChainSkeletonBasePairIter m d ≫ twistedChainSkeletonBasePairToSucc C L (m + d)

private lemma twistedChainSkeletonBasePairIter_comp (m d : ℕ) :
    twistedChainSkeletonBasePairIter C L m d ≫ twistedChainSkeletonBasePairToComplex C L (m + d) =
      twistedChainSkeletonBasePairToComplex C L m := by
  induction d with
  | zero => exact Category.id_comp _
  | succ d ih =>
    rw [twistedChainSkeletonBasePairIter, Category.assoc]
    -- The skeleton `m + (d + 1)` is `m + d + 1` only up to unfolding the addition, hence `erw`.
    erw [twistedChainSkeletonBasePairToSucc_comp_twistedChainSkeletonBasePairToComplex]
    exact ih

private lemma isIso_homologyMap_twistedChainSkeletonBasePairIter {m k : ℕ} (hk : k < m) (d : ℕ) :
    IsIso (HomologicalComplex.homologyMap (twistedChainSkeletonBasePairIter C L m d) k) := by
  induction d with
  | zero => rw [twistedChainSkeletonBasePairIter, HomologicalComplex.homologyMap_id]; infer_instance
  | succ d ih =>
    rw [twistedChainSkeletonBasePairIter, HomologicalComplex.homologyMap_comp,
      homologyMap_twistedChainSkeletonBasePairToSucc]
    have := isIso_twistedHomologySkeletonBasePairToSucc C L (n := m + d) (k := k) (by lia)
    infer_instance

/-- The maps of relative twisted chains from the skeleta into the whole complex are injective:
the skeleton and the complex have the same subspace `X⁻¹`. -/
private lemma twistedChainSkeletonBasePairToComplex_f_injective (m k : ℕ) :
    Function.Injective ((twistedChainSkeletonBasePairToComplex C L m).f k).hom := by
  have : Mono (TopPair.Hom.fst (skeletonBasePairToComplex C m)) := by
    rw [skeletonBasePairToComplex_fst]
    exact (TopCat.mono_iff_injective _).2
      (Set.inclusion_injective (skeletonLT C ((m + 1 : ℕ) : ℕ∞)).subset_complex)
  rw [twistedChainSkeletonBasePairToComplex_eq, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  refine (TopPair.twistedChainComplexMap_f_injective (skeletonBasePairToComplex C m) L ?_
    k).comp ?_
  · -- A point of the skeleton lying in `X⁻¹` as a point of the complex lies in `X⁻¹`.
    rintro x ⟨b, hb⟩
    rw [skeletonBasePairToComplex_fst] at hb
    exact ⟨b, Subtype.ext (congrArg Subtype.val hb :)⟩
  · -- The coefficient identification is an isomorphism of complexes, so injective in each degree.
    exact (ConcreteCategory.bijective_of_isIso _).1

/-- **Homology of the whole pair from a skeleton, with local coefficients.** For every relative CW
complex, with no dimension bound, the inclusion `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism
`Hₖ(Xᵐ, X⁻¹; L) ≅ Hₖ(C, X⁻¹; L)` for `k < m`. -/
theorem isIso_twistedHomologySkeletonBasePairToComplex {m k : ℕ} (hk : k < m) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L m k) := by
  rw [← homologyMap_twistedChainSkeletonBasePairToComplex,
    ConcreteCategory.isIso_iff_bijective]
  let K (j : ℕ) := (skeletonBasePair C j).twistedChainComplex (skeletonSystem C L (j + 1))
  let φ (d : ℕ) : K (m + d) ⟶ (complexBasePair C).twistedChainComplex L :=
    twistedChainSkeletonBasePairToComplex C L (m + d)
  have hφ (d i : ℕ) : Function.Injective ((φ d).f i).hom :=
    twistedChainSkeletonBasePairToComplex_f_injective C L (m + d) i
  refine ⟨fun y y' h ↦ ?_, fun z ↦ ?_⟩
  · -- A class vanishing in the complex vanishes in a larger skeleton, where it came from
    -- isomorphically.
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero]
    obtain ⟨d, -, hd⟩ := HomologicalComplex.exists_homologyMap_eq_zero_of_injective k φ
      (fun d ↦ hφ d k) (ChainComplex.prev ℕ k) (i := 0) (P := fun _ ↦ True)
      (fun d _ ↦ twistedChainSkeletonBasePairIter C L m d)
      (fun d _ ↦ twistedChainSkeletonBasePairIter_comp C L m d)
      (fun x ↦ by
        obtain ⟨d, z, hz⟩ := exists_twistedChainSkeletonBasePairToComplex_f_eq C L m x
        exact ⟨d, trivial, z, hz⟩) (y - y') h
    have := isIso_homologyMap_twistedChainSkeletonBasePairIter C L hk d
    exact (ConcreteCategory.isIso_iff_bijective _).1 this |>.1 (hd.trans (map_zero _).symm)
  · -- A class of the complex comes from a larger skeleton, hence from the `m`-skeleton.
    obtain ⟨d, y, rfl⟩ := HomologicalComplex.exists_homologyMap_eq_of_injective k φ
      (fun d ↦ hφ d _) (fun x ↦ exists_twistedChainSkeletonBasePairToComplex_f_eq C L m x) z
    have := isIso_homologyMap_twistedChainSkeletonBasePairIter C L hk d
    obtain ⟨y', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 this).2 y
    refine ⟨y', ?_⟩
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      twistedChainSkeletonBasePairIter_comp]

/-- For every relative CW complex, `(Xⁿ⁺¹, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism on `Hₙ` with
local coefficients. -/
instance isIso_twistedHomologySkeletonBasePairToComplex_succ (n : ℕ) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L (n + 1) n) :=
  isIso_twistedHomologySkeletonBasePairToComplex C L (by lia)

variable (n : ℕ)

/-- **Cellular homology with local coefficients is twisted singular homology**: the homology of
the cellular chain complex with coefficients in `L` is the twisted relative singular homology
`Hₙ(C, X⁻¹; L)` of the complex, for every relative CW complex. The second map is induced by the
inclusion of the `(n + 1)`-skeleton into the complex, an isomorphism on `Hₙ`
(`TauCeti.isIso_twistedHomologySkeletonBasePairToComplex_succ`). -/
def twistedCellularSingularHomologyIso :
    (twistedCellularChainComplex C L).homology n ≅ (complexBasePair C).twistedHomology L n :=
  twistedCellularHomologyIso C L n ≪≫
    asIso (twistedHomologySkeletonBasePairToComplex C L (n + 1) n)

/-- The cellular–singular comparison with local coefficients on cycles is the map induced by the
inclusion of the `n`-skeleton into the complex. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_twistedCellularSingularHomologyIso_hom :
    (twistedCellularChainComplex C L).homologyπ n ≫
        (twistedCellularSingularHomologyIso C L n).hom =
      (twistedCellularCyclesIso C L n).hom ≫ twistedHomologySkeletonBasePairToComplex C L n n := by
  rw [twistedCellularSingularHomologyIso, Iso.trans_hom, asIso_hom,
    homologyπ_comp_twistedCellularHomologyIso_hom_assoc,
    twistedHomologySkeletonBasePairToSucc_comp_twistedHomologySkeletonBasePairToComplex]

end TauCeti
