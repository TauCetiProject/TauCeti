/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Chains
public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence

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
  (`TauCeti.isIso_twistedHomologySkeletonBasePairToSucc`), so for a finite-dimensional complex the
  inclusion `(Xᵐ, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism on `Hₖ` for `k < m`
  (`TauCeti.isIso_twistedHomologySkeletonBasePairToComplex`). Whenever this holds for `m = n + 1`
  and `k = n`, the cellular homology is the twisted relative singular homology `Hₙ(C, D; L)` of the
  complex (`TauCeti.twistedCellularSingularHomologyIso`).

For infinite-dimensional complexes the isomorphism hypothesis of
`TauCeti.twistedCellularSingularHomologyIso` is not established here: it needs the compact-support
property of twisted singular homology.

The base `X⁻¹` is `skeletonLT C 0`, as in `TauCeti.skeletonBasePair`. In degree `0` the pairs
`(X⁰, X⁻¹)` and `(X⁰, X⁻¹)` of `TauCeti.skeletonBasePair` and `TauCeti.skeletonPair` coincide, and
`TauCeti.twistedCellularCyclesι` is the identity there.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34 and Theorem 2.35, and Section 3.H.
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

/-- The inclusion of the `m`-skeleton into the complex factors through the `(m + 1)`-skeleton. -/
@[reassoc (attr := simp)]
lemma twistedHomologySkeletonBasePairToSucc_comp_twistedHomologySkeletonBasePairToComplex
    (m k : ℕ) :
    twistedHomologySkeletonBasePairToSucc C L m k ≫
        twistedHomologySkeletonBasePairToComplex C L (m + 1) k =
      twistedHomologySkeletonBasePairToComplex C L m k := by
  have h : (TopTriple.innerToTotal.app (skeletonBaseTriple C m) ≫
      skeletonBasePairToComplex C (m + 1) : skeletonBasePair C m ⟶ complexBasePair C) =
      skeletonBasePairToComplex C m :=
    (congrArg (· ≫ skeletonBasePairToComplex C (m + 1))
      ((skeletonBasePairToSucc_def C m).symm.trans (skeletonBasePairInclusion_succ C m).symm)).trans
      (skeletonBasePairInclusion_comp_toComplex C m.le_succ)
  have e₁ := TopPair.twistedHomologyMap_comp (P := skeletonBasePair C m)
    (Q := skeletonBasePair C (m + 1)) (TopTriple.innerToTotal.app (skeletonBaseTriple C m))
    (skeletonBasePairToComplex C (m + 1)) L k
  have e₂ := TopPair.twistedHomologyMap_naturality_assoc (P := skeletonBasePair C m)
    (Q := skeletonBasePair C (m + 1)) (TopTriple.innerToTotal.app (skeletonBaseTriple C m))
    (skeletonSystem C L (m + 1 + 1)) (eqToHom (skeletonSystem_eq_pullback C L (m + 1))) k
    (TopPair.twistedHomologyMap (skeletonBasePairToComplex C (m + 1)) L k)
  -- Write both sides as a coefficient map followed by the maps induced by the inclusions
  -- `(Xᵐ, X⁻¹) ⟶ (Xᵐ⁺¹, X⁻¹) ⟶ (C, X⁻¹)`; the triple's inner and total pairs are the base pairs
  -- only after unfolding the pair constructors, so `e₁` and `e₂` are applied by `erw`.
  rw [twistedHomologySkeletonBasePairToSucc, twistedHomologySkeletonBasePairToComplex,
    twistedHomologySkeletonBasePairToComplex, TopPair.twistedHomologyMap_congr L h.symm]
  erw [e₁, Category.assoc, e₂]
  erw [← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  refine congrArg (fun η ↦ (skeletonBasePair C m).twistedHomologyCoefficientMap η k ≫ _) ?_
  refine NatTrans.ext (funext fun x ↦ ?_)
  -- Every coefficient identification is the identity or an `eqToHom` on each fibre. The fibres
  -- are those of systems on `(skeletonBasePair C m).fst`, which is `skeletonObj C (m + 1)` only
  -- after unfolding the pair constructors, so the components are computed by `erw`.
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    skeletonPairSubspaceSystemIso_inv_app, TopPair.fstPullbackCompIso_hom_app, Category.id_comp,
    Category.comp_id, LocalCoefficientSystem.pullback_map_app, eqToHom_app, eqToHom_app,
    eqToHom_app, eqToHom_trans]
  rfl

/-- If the `m`-skeleton is the whole complex, `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` is an
isomorphism. -/
theorem isIso_twistedHomologySkeletonBasePairToComplex_of_eq {m : ℕ}
    (hm : (skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) = C) (k : ℕ) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L m k) := by
  have := isIso_skeletonBasePairToComplex_of_eq C m hm
  have : IsIso (TopPair.twistedHomologyMap (skeletonBasePairToComplex C m) L k) :=
    LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_homotopyInverse _ _
      (inv (skeletonBasePairToComplex C m))
      ⟨(IsIso.hom_inv_id (skeletonBasePairToComplex C m)) ▸ TopPair.Homotopy.refl _⟩
      ⟨(IsIso.inv_hom_id (skeletonBasePairToComplex C m)) ▸ TopPair.Homotopy.refl _⟩ k
  have := @TopPair.isIso_twistedHomologyCoefficientMap _ _ (skeletonBasePair C m) _ _
    (eqToHom (skeletonSystem_eq_pullback C L m))
    (Iso.isIso_hom (eqToIso (skeletonSystem_eq_pullback C L m))) k
  exact IsIso.comp_isIso

/-- If the `(m + j)`-skeleton is the whole complex, `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` is an
isomorphism for `k < m`: it factors through the isomorphisms
`TauCeti.isIso_twistedHomologySkeletonBasePairToSucc`. -/
theorem isIso_twistedHomologySkeletonBasePairToComplex_of_lt_of_eq {m k : ℕ} (hk : k < m) (j : ℕ)
    (hj : (skeletonLT C ((m + j + 1 : ℕ) : ℕ∞) : Set X) = C) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L m k) := by
  induction j generalizing m with
  | zero => exact isIso_twistedHomologySkeletonBasePairToComplex_of_eq C L hj k
  | succ j ih =>
    have := isIso_twistedHomologySkeletonBasePairToSucc C L hk
    have := ih (m := m + 1) (by lia) (by rwa [Nat.add_right_comm m 1 j])
    rw [← twistedHomologySkeletonBasePairToSucc_comp_twistedHomologySkeletonBasePairToComplex]
    infer_instance

/-- For a finite-dimensional relative CW complex, `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` is an
isomorphism for `k < m`. -/
theorem isIso_twistedHomologySkeletonBasePairToComplex [FiniteDimensional C] {m k : ℕ}
    (hk : k < m) : IsIso (twistedHomologySkeletonBasePairToComplex C L m k) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  exact isIso_twistedHomologySkeletonBasePairToComplex_of_lt_of_eq C L hk N
    (skeletonLT_eq_complex_of_isEmpty_cell C (m + N + 1) fun j hj ↦ hN j (by lia))

/-- For a finite-dimensional relative CW complex, `(Xⁿ⁺¹, X⁻¹) ⟶ (C, X⁻¹)` induces an isomorphism
on `Hₙ` with local coefficients. -/
instance isIso_twistedHomologySkeletonBasePairToComplex_succ_of_finiteDimensional
    [FiniteDimensional C] (n : ℕ) :
    IsIso (twistedHomologySkeletonBasePairToComplex C L (n + 1) n) :=
  isIso_twistedHomologySkeletonBasePairToComplex C L (by lia)

variable (n : ℕ) [IsIso (twistedHomologySkeletonBasePairToComplex C L (n + 1) n)]

/-- **Cellular homology with local coefficients is twisted singular homology**: the homology of
the cellular chain complex with coefficients in `L` is the twisted relative singular homology
`Hₙ(C, X⁻¹; L)` of the complex. The second map is induced by the inclusion of the
`(n + 1)`-skeleton into the complex, an isomorphism on `Hₙ` for every finite-dimensional complex
(`TauCeti.isIso_twistedHomologySkeletonBasePairToComplex_succ_of_finiteDimensional`). -/
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
