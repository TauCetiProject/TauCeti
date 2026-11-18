/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
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

variable {R : Type u} [Ring R] (B : Type v) [TopologicalSpace B]
  (F : Type v) [NormedAddCommGroup F]

/-- The zero section `b ↦ (b, 0)` of the product bundle `B × F → B`. -/
def prodZeroSection : TopCat.of B ⟶ TopCat.of (B × F) :=
  TopCat.ofHom ⟨fun b ↦ (b, 0), by fun_prop⟩

@[simp]
lemma prodZeroSection_apply (b : B) : prodZeroSection B F b = (b, 0) :=
  (rfl)

variable [NormedSpace ℝ F]

/-- The zero section of the product bundle is a homotopy equivalence, with homotopy inverse the
projection: `(b, x) ↦ (b, t • x)` contracts `B × F` onto the zero section. -/
def prodZeroSectionHomotopyEquiv : ContinuousMap.HomotopyEquiv B (B × F) where
  toFun := (prodZeroSection B F).hom
  invFun := ContinuousMap.fst
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨{
    toFun := fun p ↦ (p.2.1, (p.1 : ℝ) • p.2.2)
    continuous_toFun := by fun_prop
    map_zero_left := fun p ↦ by simp [prodZeroSection]
    map_one_left := fun p ↦ by simp }⟩

namespace ProdThomPair

variable {B F}

/-- The projection `B × F → F`. -/
private abbrev proj : C(TopCat.of (B × F), F) :=
  ContinuousMap.snd

/-- The complement in `B × F` of `B` times a closed half-subspace `{y ∈ W | φ y ≤ 0}` with
`φ v = 1` for some `v ∈ W` is acyclic with every local coefficient system: `B × F` deforms into it
along straight lines towards `v`. -/
private lemma isZero_twistedHomology_halfCompl
    (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (B × F))) (W : Submodule ℝ F)
    (φ : F →ₗ[ℝ] ℝ) (v : F) (hv : v ∈ W) (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset (proj ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).twistedHomology L n) := by
  let c : TopCat.of (B × F) ⟶ TopCat.of (B × F) := TopCat.ofHom ⟨fun p ↦ (p.1, v), by fun_prop⟩
  let H : (TopCat.Hom.hom (𝟙 (TopCat.of (B × F)))).Homotopy c.hom :=
    { toFun q := (q.2.1, (q.1 : ℝ) • v + (1 - (q.1 : ℝ)) • q.2.2)
      continuous_toFun := by fun_prop
      map_zero_left _ := by simp
      map_one_left _ := by simp [c] }
  exact TopPair.isZero_twistedHomology_ofSubset_of_homotopy H
    (fun τ p hp ↦ starConvex_compl_setOf_mem_and_nonpos hv (by simp [hφv]) hp τ.2.1
      (sub_nonneg.2 τ.2.2) (add_sub_cancel _ _))
    (fun _ h ↦ (hφv ▸ one_pos : 0 < φ v).not_ge h.2) L n

/-- The Thom pair of the product bundle is the pair `(B × F, B × (F ∖ ⊥))`. -/
private lemma setOf_snd_ne_zero_eq :
    ({p | p.2 ≠ 0} : Set (TopCat.of (B × F))) = proj ⁻¹' ((⊥ : Submodule ℝ F) : Set F)ᶜ := by
  ext p
  simp

/-- The twisted homology of the Thom pair of the product bundle is that of the pair
`(B × F, B × (F ∖ ⊥))`. -/
private def twistedHomologyBotIso
    (L : LocalCoefficientSystem.{u, v, max v w} R (prodThomPair B F).fst) (n : ℕ) :
    (prodThomPair B F).twistedHomology L n ≅
      (subspaceComplPair (proj (B := B) (F := F)) ⊥).twistedHomology L n :=
  eqToIso (congrArg (fun S ↦ (TopPair.ofSubset S).twistedHomology L n) setOf_snd_ne_zero_eq)

end ProdThomPair

open ProdThomPair

variable {B F} [FiniteDimensional ℝ F]
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
section `s` (`TauCeti.prodZeroSection`). In particular `Hᵣ(B × F, B × (F ∖ {0}); L) ≅ H₀(B; s⁎L)`.

The isomorphism is the composite of `r` connecting maps of triples and excisions
(`TopPair.twistedHomologyOfSubsetUnionIso`), for choices of subspaces and functionals of `F` that
do not depend on `B` or `L`, followed by the identification of `Hₙ(B × F; L)` with `Hₙ(B; s⁎L)`
along the zero section. -/
def prodThomPairTwistedHomologyIso (n m : ℕ) (h : n + finrank ℝ F = m := by lia) :
    (prodThomPair B F).twistedHomology L m ≅
      ((LocalCoefficientSystem.pullback (prodZeroSection B F).hom).obj L).twistedHomology n :=
  have : IsEmpty (subspaceComplPair (proj (B := B) (F := F)) ⊤).snd :=
    ⟨fun p ↦ p.2 Submodule.mem_top⟩
  twistedHomologyBotIso L m ≪≫
    subspaceComplPairTwistedHomologyIso _ L (isZero_twistedHomology_halfCompl L) (finrank ℝ F) ⊥
      (by simp) n m h ≪≫
    -- The instances are passed explicitly: searching for them runs out of time.
    (@asIso _ _ _ _ ((subspaceComplPair (proj (B := B) (F := F)) ⊤).twistedHomologyπ L n)
      (TopPair.isIso_twistedHomologyπ_of_isEmpty (subspaceComplPair (proj (B := B) (F := F)) ⊤)
        L n)).symm ≪≫
    (@asIso _ _ _ _ (LocalCoefficientSystem.twistedHomologyMap (prodZeroSection B F) L n)
      ((prodZeroSectionHomotopyEquiv B F).isIso_twistedHomologyMap L n)).symm

end TauCeti
