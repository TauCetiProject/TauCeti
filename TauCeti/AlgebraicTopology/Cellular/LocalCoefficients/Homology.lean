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
coefficient system on `X`. This file computes the homology of the cellular chain complex
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
  (`TauCeti.isIso_twistedSkeletonBasePairToSucc`), so `Hₙ(Xⁿ⁺¹, X⁻¹; L)` is the homology of every
  higher skeleton (`TauCeti.twistedSkeletonBasePairIsoAdd`). When a skeleton is the whole complex,
  the cellular homology is the twisted relative singular homology `Hₙ(C, D; L)` of the complex
  (`TauCeti.twistedCellularSingularHomologyIsoOfEq`); in particular this holds for every
  finite-dimensional complex (`TauCeti.nonempty_twistedCellularHomology_iso_twistedHomology`).

Infinite-dimensional complexes are not treated here: for them the comparison with the whole
complex needs the compact-support property of twisted singular homology.

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
  (C : Set X) [RelCWComplex C D] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of X))

/-! ### Coefficient isomorphisms

The coefficient systems below live on ambient spaces of different pairs which agree only up to
unfolding `MorphismProperty.Arrow.mk`. These lemmas fix the pair `P` first, so that instance
search and rewriting see the isomorphism `e` in the category of local systems on `P.fst`. -/

private lemma isIso_twistedHomologyCoefficientMap_hom {P : TopPair.{w}}
    {K K' : LocalCoefficientSystem.{u, w, max w v} R P.fst} (e : K ≅ K') (k : ℕ) :
    IsIso (P.twistedHomologyCoefficientMap e.hom k) :=
  inferInstance

private lemma isIso_twistedHomologyCoefficientMap_inv {P : TopPair.{w}}
    {K K' : LocalCoefficientSystem.{u, w, max w v} R P.fst} (e : K ≅ K') (k : ℕ) :
    IsIso (P.twistedHomologyCoefficientMap e.inv k) :=
  inferInstance

@[reassoc]
private lemma twistedHomologyCoefficientMap_hom_inv_id {P : TopPair.{w}}
    {K K' : LocalCoefficientSystem.{u, w, max w v} R P.fst} (e : K ≅ K') (k : ℕ) :
    P.twistedHomologyCoefficientMap e.hom k ≫ P.twistedHomologyCoefficientMap e.inv k = 𝟙 _ := by
  rw [← TopPair.twistedHomologyCoefficientMap_comp, e.hom_inv_id,
    TopPair.twistedHomologyCoefficientMap_id]

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
def twistedSkeletonBasePairToSucc (n k : ℕ) :
    (skeletonBasePair C n).twistedHomology (skeletonSystem C L (n + 1)) k ⟶
      (skeletonBasePair C (n + 1)).twistedHomology (skeletonSystem C L (n + 1 + 1)) k :=
  (skeletonBasePair C n).twistedHomologyCoefficientMap
      (skeletonPairSubspaceSystemIso C L (n + 1)).inv k ≫
    TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1)) k

lemma twistedSkeletonBasePairToSucc_def (n k : ℕ) :
    twistedSkeletonBasePairToSucc C L n k =
      (skeletonBasePair C n).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L (n + 1)).inv k ≫
        TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
          (skeletonSystem C L (n + 1 + 1)) k :=
  (rfl)

/-- The connecting morphism of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` followed by the map
`Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ⁺¹, X⁻¹; L)` is zero. -/
@[reassoc (attr := simp)]
lemma twistedSkeletonBaseTripleδ_comp_twistedSkeletonBasePairToSucc (n : ℕ) :
    twistedSkeletonBaseTripleδ C L n ≫ twistedSkeletonBasePairToSucc C L n n = 0 := by
  rw [twistedSkeletonBaseTripleδ, twistedSkeletonBasePairToSucc]
  -- The coefficient maps live on `skeletonBasePair C n`, which is the inner pair of the triple
  -- only up to unfolding the pair constructors; `erw` cancels them.
  erw [Category.assoc, ← Category.assoc ((skeletonBasePair C n).twistedHomologyCoefficientMap _ n),
    ← TopPair.twistedHomologyCoefficientMap_comp, Iso.hom_inv_id,
    TopPair.twistedHomologyCoefficientMap_id, Category.id_comp]
  exact (skeletonBaseTriple C n).twistedHomologyδ_comp _ (n + 1) n rfl

/-- The map `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` followed by the connecting morphism of the triple
`(Xⁿ, Xⁿ⁻¹, X⁻¹)` is zero. -/
@[reassoc (attr := simp)]
lemma twistedCellularCyclesι_comp_twistedSkeletonBaseTripleδ (n : ℕ) :
    twistedCellularCyclesι C L (n + 1) ≫ twistedSkeletonBaseTripleδ C L n = 0 := by
  rw [twistedCellularCyclesι, twistedSkeletonBaseTripleδ]
  -- `comp_twistedHomologyδ_assoc` is stated for the triple's own pairs; `erw` matches them.
  erw [(skeletonBaseTriple C n).comp_twistedHomologyδ_assoc _ (n + 1) n rfl, zero_comp]
  rfl

/-- The quotient `Hₙ(Xⁿ; L) ⟶ Hₙ(Xⁿ, X⁻¹; L)` followed by `TauCeti.twistedCellularCyclesι` is the
quotient `Hₙ(Xⁿ; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)`. -/
private lemma twistedHomologyπ_comp_twistedCellularCyclesι (n : ℕ) :
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
  rw [twistedCellularDifferential_eq, twistedSkeletonBaseTripleδ,
    (skeletonBaseTriple C n).twistedHomologyδ_eq_comp_twistedHomologyπ _ (n + 1) n rfl]
  -- Both sides begin with the connecting morphism of the pair `(Xⁿ⁺¹, Xⁿ)`.
  exact (congrArg (_ ≫ ·)
    (twistedHomologyπ_comp_coefficientMap_comp_twistedCellularCyclesι C L n).symm).trans rfl

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
theorem epi_twistedSkeletonBasePairToSucc {n k : ℕ} (hk : k ≠ n + 1) :
    Epi (twistedSkeletonBasePairToSucc C L n k) := by
  have h : Epi (TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1)) k) :=
    ((skeletonBaseTriple C n).twistedHomology_exact_total _ k).epi_f
      ((isZero_twistedHomology_skeletonPair_of_ne C hk _).eq_of_tgt _ _)
  have := isIso_twistedHomologyCoefficientMap_inv (P := skeletonBasePair C n)
    (skeletonPairSubspaceSystemIso C L (n + 1)) k
  exact epi_comp' inferInstance h

instance epi_twistedSkeletonBasePairToSucc_self (n : ℕ) :
    Epi (twistedSkeletonBasePairToSucc C L n n) :=
  epi_twistedSkeletonBasePairToSucc C L (by lia)

/-- The map `Hₖ(Xⁿ, X⁻¹; L) ⟶ Hₖ(Xⁿ⁺¹, X⁻¹; L)` is an isomorphism for `k < n`: the adjacent groups
`Hₖ₊₁(Xⁿ⁺¹, Xⁿ; L)` and `Hₖ(Xⁿ⁺¹, Xⁿ; L)` vanish. -/
theorem isIso_twistedSkeletonBasePairToSucc {n k : ℕ} (hk : k < n) :
    IsIso (twistedSkeletonBasePairToSucc C L n k) := by
  have := epi_twistedSkeletonBasePairToSucc C L (n := n) (k := k) (by lia)
  have h : Mono (TopPair.twistedHomologyMap (TopTriple.innerToTotal.app (skeletonBaseTriple C n))
      (skeletonSystem C L (n + 1 + 1)) k) :=
    ((skeletonBaseTriple C n).twistedHomology_exact_inner _ (k + 1) k rfl).mono_g
      ((isZero_twistedHomology_skeletonPair_of_ne C (by lia) _).eq_of_src _ _)
  have := isIso_twistedHomologyCoefficientMap_inv (P := skeletonBasePair C n)
    (skeletonPairSubspaceSystemIso C L (n + 1)) k
  have : Mono (twistedSkeletonBasePairToSucc C L n k) := mono_comp' inferInstance h
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
    change Epi (twistedCellularCyclesι C L 0 ≫ eqToHom _)
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
        comm₁₂ := by simp [twistedCellularCyclesιX]; rfl
        comm₂₃ := by
          change eqToHom (twistedCellularChainComplex_X C L (n + 1)).symm ≫
            (twistedCellularChainComplex C L).d (n + 1) n = _
          rw [twistedCellularChainComplex_d_eq, eqToHom_trans_assoc,
            eqToHom_refl, Category.id_comp, twistedSkeletonBaseTripleδ]
          exact Category.assoc _ _ _ }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso φ.τ₂ :=
      inferInstanceAs (IsIso (eqToHom (twistedCellularChainComplex_X C L (n + 1)).symm))
    have : Mono φ.τ₃ := mono_comp' (isIso_twistedHomologyCoefficientMap_hom
      (P := skeletonBasePair C n) (skeletonPairSubspaceSystemIso C L (n + 1)) n).mono_of_iso
      inferInstance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      ((skeletonBaseTriple C n).twistedHomology_exact_outer _ (n + 1) n rfl)

/-- Exactness at `Hₙ(Xⁿ, X⁻¹; L)` in the sequence of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
lemma twistedSkeletonBaseTriple_exact_inner (n : ℕ) :
    (ShortComplex.mk _ _
      (twistedSkeletonBaseTripleδ_comp_twistedSkeletonBasePairToSucc C L n)).Exact := by
  let φ : ShortComplex.mk _ _
      ((skeletonBaseTriple C n).twistedHomologyδ_comp (skeletonSystem C L (n + 1 + 1)) (n + 1) n
        rfl) ⟶
      ShortComplex.mk _ _ (twistedSkeletonBaseTripleδ_comp_twistedSkeletonBasePairToSucc C L n) :=
    { τ₁ := 𝟙 _
      τ₂ := (skeletonBasePair C n).twistedHomologyCoefficientMap
        (skeletonPairSubspaceSystemIso C L (n + 1)).hom n
      τ₃ := 𝟙 _
      comm₁₂ := (Category.id_comp _).trans (by dsimp only; unfold twistedSkeletonBaseTripleδ; rfl)
      comm₂₃ := (by
        dsimp only
        unfold twistedSkeletonBasePairToSucc
        exact (twistedHomologyCoefficientMap_hom_inv_id_assoc
          (P := skeletonBasePair C n) (skeletonPairSubspaceSystemIso C L (n + 1)) n _).trans
            (Category.comp_id _).symm) }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ.τ₂ := isIso_twistedHomologyCoefficientMap_hom
    (P := skeletonBasePair C n) (skeletonPairSubspaceSystemIso C L (n + 1)) n
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
  π := twistedSkeletonBasePairToSucc C L n n
  wπ := by
    refine (congrArg (· ≫ _) (twistedCellularCycles_lift_eq C L n)).trans ?_
    rw [Category.assoc, twistedSkeletonBaseTripleδ_comp_twistedSkeletonBasePairToSucc]
    exact comp_zero
  hπ := isCokernelEpiComp (twistedSkeletonBaseTriple_exact_inner C L n).gIsCokernel
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
      (twistedCellularCyclesIso C L n).hom ≫ twistedSkeletonBasePairToSucc C L n n := by
  have h := (twistedCellularChainComplex C L).π_homologyIsoSc'_hom_assoc (n + 1) n (n - 1)
    (by simp) (by cases n <;> simp) (twistedCellularLeftHomologyData C L n).homologyIso.hom
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom] at h
  exact h.trans (Category.assoc _ _ _).symm

/-! ### Comparison with the whole complex -/

/-- Stabilization along the skeleta: `Hₙ(Xⁿ⁺¹, X⁻¹; L) ≅ Hₙ(Xⁿ⁺¹⁺ʲ, X⁻¹; L)`, composed of the
isomorphisms `TauCeti.isIso_twistedSkeletonBasePairToSucc`. -/
def twistedSkeletonBasePairIsoAdd (n : ℕ) : (j : ℕ) →
    ((skeletonBasePair C (n + 1)).twistedHomology (skeletonSystem C L (n + 1 + 1)) n ≅
      (skeletonBasePair C (n + 1 + j)).twistedHomology (skeletonSystem C L (n + 1 + j + 1)) n)
  | 0 => Iso.refl _
  | j + 1 => twistedSkeletonBasePairIsoAdd n j ≪≫
      haveI := isIso_twistedSkeletonBasePairToSucc C L (n := n + 1 + j) (k := n) (by lia)
      asIso (twistedSkeletonBasePairToSucc C L (n + 1 + j) n)

@[simp]
lemma twistedSkeletonBasePairIsoAdd_zero_hom (n : ℕ) :
    (twistedSkeletonBasePairIsoAdd C L n 0).hom = 𝟙 _ :=
  (rfl)

@[simp]
lemma twistedSkeletonBasePairIsoAdd_succ_hom (n j : ℕ) :
    (twistedSkeletonBasePairIsoAdd C L n (j + 1)).hom =
      (twistedSkeletonBasePairIsoAdd C L n j).hom ≫
        twistedSkeletonBasePairToSucc C L (n + 1 + j) n :=
  (rfl)

/-- The restriction of a local coefficient system on `X` to the relative CW complex `C`. -/
abbrev complexSystem : LocalCoefficientSystem.{u, w, max w v} R (complexBasePair C).fst :=
  (LocalCoefficientSystem.pullback (⟨Subtype.val, continuous_subtype_val⟩ :
    C(TopCat.of C, TopCat.of X))).obj L

/-- Pulling the restriction of `L` to the complex back to the `m`-skeleton gives
`skeletonSystem C L (m + 1)`. -/
def skeletonComplexSystemIso (m : ℕ) :
    skeletonSystem C L (m + 1) ≅ (LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (skeletonBasePairToComplex C m)).hom).obj (complexSystem C L) :=
  eqToIso (by rw [skeletonBasePairToComplex_fst]; rfl) ≪≫
    (LocalCoefficientSystem.pullbackCompIso (R := R)
      (TopPair.Hom.fst (skeletonBasePairToComplex C m)).hom
      (⟨Subtype.val, continuous_subtype_val⟩ : C(TopCat.of C, TopCat.of X))).app L

/-- `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)`, induced by the inclusion of the `m`-skeleton. -/
def twistedSkeletonBasePairToComplex (m k : ℕ) :
    (skeletonBasePair C m).twistedHomology (skeletonSystem C L (m + 1)) k ⟶
      (complexBasePair C).twistedHomology (complexSystem C L) k :=
  (skeletonBasePair C m).twistedHomologyCoefficientMap (skeletonComplexSystemIso C L m).hom k ≫
    TopPair.twistedHomologyMap (skeletonBasePairToComplex C m) (complexSystem C L) k

lemma twistedSkeletonBasePairToComplex_def (m k : ℕ) :
    twistedSkeletonBasePairToComplex C L m k =
      (skeletonBasePair C m).twistedHomologyCoefficientMap (skeletonComplexSystemIso C L m).hom k ≫
        TopPair.twistedHomologyMap (skeletonBasePairToComplex C m) (complexSystem C L) k :=
  (rfl)

/-- If the `m`-skeleton is the whole complex, `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` is an
isomorphism. -/
theorem isIso_twistedSkeletonBasePairToComplex_of_eq {m : ℕ}
    (hm : (skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) = C) (k : ℕ) :
    IsIso (twistedSkeletonBasePairToComplex C L m k) := by
  have := isIso_skeletonBasePairToComplex_of_eq C m hm
  have : IsIso (TopPair.twistedHomologyMap (skeletonBasePairToComplex C m) (complexSystem C L) k) :=
    LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_homotopyInverse _ _
      (inv (skeletonBasePairToComplex C m))
      ⟨(IsIso.hom_inv_id (skeletonBasePairToComplex C m)) ▸ TopPair.Homotopy.refl _⟩
      ⟨(IsIso.inv_hom_id (skeletonBasePairToComplex C m)) ▸ TopPair.Homotopy.refl _⟩ k
  have := isIso_twistedHomologyCoefficientMap_hom (P := skeletonBasePair C m)
    (skeletonComplexSystemIso C L m) k
  exact IsIso.comp_isIso

/-- **Cellular homology with local coefficients is twisted singular homology**, for a complex
whose `(n + 1 + j)`-skeleton is the whole complex. -/
def twistedCellularSingularHomologyIsoOfEq (n j : ℕ)
    (hj : (skeletonLT C ((n + 1 + j + 1 : ℕ) : ℕ∞) : Set X) = C) :
    (twistedCellularChainComplex C L).homology n ≅
      (complexBasePair C).twistedHomology (complexSystem C L) n :=
  twistedCellularHomologyIso C L n ≪≫ twistedSkeletonBasePairIsoAdd C L n j ≪≫
    haveI := isIso_twistedSkeletonBasePairToComplex_of_eq C L hj n
    asIso (twistedSkeletonBasePairToComplex C L (n + 1 + j) n)

lemma twistedCellularSingularHomologyIsoOfEq_hom (n j : ℕ)
    (hj : (skeletonLT C ((n + 1 + j + 1 : ℕ) : ℕ∞) : Set X) = C) :
    (twistedCellularSingularHomologyIsoOfEq C L n j hj).hom =
      (twistedCellularHomologyIso C L n).hom ≫ (twistedSkeletonBasePairIsoAdd C L n j).hom ≫
        twistedSkeletonBasePairToComplex C L (n + 1 + j) n :=
  (rfl)

/-- On a cellular cycle, the comparison `TauCeti.twistedCellularSingularHomologyIsoOfEq` is the
map induced by the inclusion `(Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹⁺ʲ, X⁻¹)` followed by the inclusion of the
`(n + 1 + j)`-skeleton into the complex. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_twistedCellularSingularHomologyIsoOfEq_hom (n j : ℕ)
    (hj : (skeletonLT C ((n + 1 + j + 1 : ℕ) : ℕ∞) : Set X) = C) :
    (twistedCellularChainComplex C L).homologyπ n ≫
        (twistedCellularSingularHomologyIsoOfEq C L n j hj).hom =
      (twistedCellularCyclesIso C L n).hom ≫ twistedSkeletonBasePairToSucc C L n n ≫
        (twistedSkeletonBasePairIsoAdd C L n j).hom ≫
          twistedSkeletonBasePairToComplex C L (n + 1 + j) n := by
  rw [twistedCellularSingularHomologyIsoOfEq_hom,
    homologyπ_comp_twistedCellularHomologyIso_hom_assoc]

/-- For a finite-dimensional relative CW complex, the homology of the cellular chain complex with
local coefficients is the twisted relative singular homology of the complex. -/
theorem nonempty_twistedCellularHomology_iso_twistedHomology [FiniteDimensional C] (n : ℕ) :
    Nonempty ((twistedCellularChainComplex C L).homology n ≅
      (complexBasePair C).twistedHomology (complexSystem C L) n) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  refine ⟨twistedCellularSingularHomologyIsoOfEq C L n N ?_⟩
  exact skeletonLT_eq_complex_of_isEmpty_cell C (n + 1 + N + 1) fun j hj ↦ hN j (by lia)

end TauCeti
