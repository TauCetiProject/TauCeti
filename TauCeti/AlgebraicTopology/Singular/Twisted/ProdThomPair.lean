/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.SubspaceCompl

/-!
# The Thom pair of a product bundle with local coefficients

Let `B` be a topological space, `F` a real normed space of finite dimension `r`, and `L` a local
coefficient system on the total space `B × F` of the product bundle, with arbitrary module fibres
over an arbitrary ring. This file computes the homology of the Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) with coefficients in `L`:

* it vanishes below the rank, `Hₙ(B × F, B × (F ∖ {0}); L) = 0` for `n < r`
  (`TauCeti.isZero_twistedHomology_prodThomPair`);
* in degree `n + r` it is the homology of the base with coefficients in the restriction of `L` to
  the zero section `s : B → B × F`, `Hₙ₊ᵣ(B × F, B × (F ∖ {0}); L) ≅ Hₙ(B; s⁎L)`
  (`TauCeti.prodThomPairTwistedHomologyIso`).

This is the Thom isomorphism in homology with local coefficients over a trivializing set, the case
from which the Thom isomorphism of a vector bundle with twisted coefficients is assembled over
unions of trivializing sets. The orientation system of a product bundle is trivial, so no twist by
it appears here. For constant coefficients the same statements are
`TauCeti.isZero_singularHomology_prodThomPair` and `TauCeti.prodThomPairSingularHomologyIso`.

The proof is the computation of `TauCeti.AlgebraicTopology.Singular.Twisted.SubspaceCompl` for the
projection `B × F → F`. Its hypothesis holds because `B × F` deforms into the complement of
`B × H` for every closed half-subspace `H = {y ∈ W | φ y ≤ 0}` with `φ v = 1` for some `v ∈ W`,
along straight lines towards `v` in each fibre. The last step, `Hₙ(B × F; L) ≅ Hₙ(B; s⁎L)`, holds
because the zero section is a homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients) and Section 4.D, the proof of
  Theorem 4D.10 (the Thom isomorphism, first over a trivializing set).
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe u v w

namespace TauCeti

variable {R : Type u} [Ring R] {B : Type v} [TopologicalSpace B]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ProdThomPair

/-- The projection `B × F → F`. -/
private abbrev proj : C(TopCat.of (B × F), F) :=
  ContinuousMap.snd

/-- The complement in `B × F` of `B` times a closed half-subspace `{y ∈ W | φ y ≤ 0}` with
`φ v = 1` for some `v ∈ W` is acyclic with every local coefficient system: `B × F` deforms into it
along straight lines towards `v`. -/
private lemma isZero_twistedHomology_halfCompl
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (B × F))) (W : Submodule ℝ F)
    (φ : F →ₗ[ℝ] ℝ) (v : F) (hv : v ∈ W) (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset (SubspaceComplPair.halfCompl proj W φ)).twistedHomology L n) := by
  obtain ⟨ρ, H, hS, hρ⟩ := exists_homotopy_halfCompl B W φ v hv hφv
  exact TopPair.isZero_twistedHomology_ofSubset_of_homotopy H hS hρ L n

/-- The Thom pair of the product bundle is the pair `(B × F, B × (F ∖ ⊥))`. -/
private lemma setOf_snd_ne_zero_eq :
    ({p | p.2 ≠ 0} : Set (TopCat.of (B × F))) = ∅ ∪ proj ⁻¹' ((⊥ : Submodule ℝ F) : Set F)ᶜ := by
  ext p
  simp

/-- The twisted homology of the Thom pair of the product bundle is that of the pair
`(B × F, B × (F ∖ ⊥))`. -/
private def twistedHomologyBotIso
    (L : LocalCoefficientSystem.{u, v, max v w} R (prodThomPair B F).fst) (n : ℕ) :
    (prodThomPair B F).twistedHomology L n ≅
      (subspaceComplPair (proj (B := B) (F := F)) ∅ ⊥).twistedHomology L n :=
  eqToIso (congrArg (fun S ↦ (TopPair.ofSubset S).twistedHomology L n) setOf_snd_ne_zero_eq)

end ProdThomPair

open ProdThomPair

variable [FiniteDimensional ℝ F]
  (L : LocalCoefficientSystem.{u, v, max v w} R (prodThomPair B F).fst)

/-- **The Thom pair of a product bundle has no homology with local coefficients below the rank**:
`Hₙ(B × F, B × (F ∖ {0}); L) = 0` for `n < dim F`, for every local coefficient system `L` on
`B × F`. -/
theorem isZero_twistedHomology_prodThomPair {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((prodThomPair B F).twistedHomology L n) := by
  exact (isZero_twistedHomology_subspaceComplPair _ L (isZero_twistedHomology_halfCompl L) n ⊥
    (by simpa using hn)).of_iso (twistedHomologyBotIso L n)

/-- **The Thom isomorphism of a product bundle in homology with local coefficients**: for `F` of
dimension `r`, `m = n + r` and every local coefficient system `L` on `B × F`,
`Hₘ(B × F, B × (F ∖ {0}); L) ≅ Hₙ(B; s⁎L)`, where `s⁎L` is the restriction of `L` to the zero
section `s` (`ContinuousMap.HomotopyEquiv.prodZeroSection`). In particular
`Hᵣ(B × F, B × (F ∖ {0}); L) ≅ H₀(B; s⁎L)`.

The isomorphism is the composite of `r` connecting maps of triples and excisions
(`TopPair.twistedHomologyOfSubsetUnionIso`), for choices of subspaces and functionals of `F` that
do not depend on `B` or `L`, followed by the identification of `Hₙ(B × F; L)` with `Hₙ(B; s⁎L)`
along the zero section. -/
def prodThomPairTwistedHomologyIso (n m : ℕ) (h : n + finrank ℝ F = m := by lia) :
    (prodThomPair B F).twistedHomology L m ≅
      ((LocalCoefficientSystem.pullback
          (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection B F).toFun).hom).obj
        L).twistedHomology n :=
  -- The global instance for `subspaceComplPair q ∅ ⊤` is not found here: its key keeps the
  -- carrier of a general space, while the carrier of `TopCat.of (B × F)` reduces to `B × F`.
  have : IsEmpty (subspaceComplPair (proj (B := B) (F := F)) ∅ ⊤).snd :=
    ⟨fun p ↦ p.property.elim id fun h ↦ h Submodule.mem_top⟩
  twistedHomologyBotIso L m ≪≫
    subspaceComplPairTwistedHomologyIso _ L (isZero_twistedHomology_halfCompl L) (finrank ℝ F) ⊥
      (by simp) n m h ≪≫
    -- The instances are passed explicitly: searching for them runs out of time.
    (@asIso _ _ _ _ ((subspaceComplPair (proj (B := B) (F := F)) ∅ ⊤).twistedHomologyπ L n)
      (TopPair.isIso_twistedHomologyπ_of_isEmpty (subspaceComplPair (proj (B := B) (F := F)) ∅ ⊤)
        L n)).symm ≪≫
    (@asIso _ _ _ _ (LocalCoefficientSystem.twistedHomologyMap
        (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection B F).toFun) L n)
      ((ContinuousMap.HomotopyEquiv.prodZeroSection B F).isIso_twistedHomologyMap L n)).symm

end TauCeti
