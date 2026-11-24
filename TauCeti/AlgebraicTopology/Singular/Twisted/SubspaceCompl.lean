/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl
public import TauCeti.AlgebraicTopology.Singular.Twisted.Acyclic

/-!
# Twisted homology modulo the preimage of the complement of a subspace

This file is the counterpart with local coefficients of
`TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl`.

Let `q : X → F` be a continuous map to a real normed space of finite dimension and `L` a local
coefficient system on `X`. Suppose that `X` is acyclic modulo the preimage of the complement of
every closed half-subspace `{y ∈ W | φ y ≤ 0}` of `F` with `φ v = 1` for some `v ∈ W`, with
coefficients in `L`. Removing one dimension at a time along the extensions by a line of
`Submodule.lineExtension`, as for constant coefficients, gives the statements below. Each step
computes the homology modulo a union of two acyclic open sets
(`TopPair.twistedHomologyOfSubsetUnionIso`).

* `Hₙ(X, q⁻¹(F ∖ W); L) = 0` for `n` below the codimension of `W`
  (`TauCeti.isZero_twistedHomology_subspaceComplPair`);
* `Hₘ(X, q⁻¹(F ∖ W); L) ≅ Hₙ(X, ∅; L)` for `W` of codimension `c` and `m = n + c`
  (`TauCeti.subspaceComplPairTwistedHomologyIso`), which agrees with `Hₙ(X; L)` by
  `TopPair.isIso_twistedHomologyπ_of_isEmpty`.

For the projection `B × F → F` these compute the homology of the Thom pair of a product bundle with
local coefficients (`TauCeti.prodThomPairTwistedHomologyIso`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1 (relative homology) and Section 3.H (local
  coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits Module TauCeti

universe u v w

namespace TauCeti

variable {R : Type u} [Ring R] {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : TopCat.{v}} (q : C(X, F)) (L : LocalCoefficientSystem.{u, v, max v w} R X)

namespace SubspaceComplPair

variable {W : Submodule ℝ F}

/-- The relative twisted homology of `(X, q⁻¹(F ∖ W))` is that of `X` modulo the union of the two
half-subspace complements of a step. -/
private def twistedHomologyUnionIso (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q ∅ W).twistedHomology L n ≅
      (TopPair.ofSubset
        (halfCompl q s.W' s.extension ∪ halfCompl q s.W' (-s.extension))).twistedHomology L n :=
  eqToIso (congrArg (fun S ↦ (TopPair.ofSubset S).twistedHomology L n)
    (by rw [Set.empty_union, ← Set.preimage_union, s.compl_union_compl s.extension_comp]))

/-- The relative twisted homology of `X` modulo the intersection of the two half-subspace
complements of a step is that of `(X, q⁻¹(F ∖ W'))`. -/
private def twistedHomologyInterIso (s : W.LineExtension) (n : ℕ) :
    (TopPair.ofSubset
        (halfCompl q s.W' s.extension ∩ halfCompl q s.W' (-s.extension))).twistedHomology L n ≅
      (subspaceComplPair q ∅ s.W').twistedHomology L n :=
  eqToIso (congrArg (fun S ↦ (TopPair.ofSubset S).twistedHomology L n)
    (by rw [Set.empty_union, ← Set.preimage_inter, s.compl_inter_compl]))

variable (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
  IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).twistedHomology L n))
include hq

private lemma isZero_halfCompl (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (halfCompl q s.W' s.extension)).twistedHomology L n) :=
  hq _ _ _ s.v.property s.extension_apply_v n

private lemma isZero_halfCompl_neg (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (halfCompl q s.W' (-s.extension))).twistedHomology L n) :=
  hq _ _ _ (neg_mem s.v.property) (by simp) n

/-- One step of the computation: `Hₙ₊₁(X, q⁻¹(F ∖ W); L) ≅ Hₙ(X, q⁻¹(F ∖ W'); L)`. -/
private def twistedStepIso [FiniteDimensional ℝ F] (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q ∅ W).twistedHomology L (n + 1) ≅
      (subspaceComplPair q ∅ s.W').twistedHomology L n :=
  twistedHomologyUnionIso q L s (n + 1) ≪≫
    TopPair.twistedHomologyOfSubsetUnionIso (isZero_halfCompl q L hq s) (isOpen_halfCompl q _ _)
      (isOpen_halfCompl q _ _) (isZero_halfCompl_neg q L hq s) n ≪≫
    twistedHomologyInterIso q L s n

private lemma isZero_twistedHomology_zero (s : W.LineExtension) :
    IsZero ((subspaceComplPair q ∅ W).twistedHomology L 0) :=
  (TopPair.isZero_twistedHomology_ofSubset_union_zero (V := halfCompl q s.W' (-s.extension))
    (isZero_halfCompl q L hq s)).of_iso (twistedHomologyUnionIso q L s 0)

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
      IsZero ((subspaceComplPair q ∅ W).twistedHomology L n)
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
      ((subspaceComplPair q ∅ W).twistedHomology L m ≅
        (subspaceComplPair q ∅ (⊤ : Submodule ℝ F)).twistedHomology L n)
  | 0, _, hW, n, _, rfl => eqToIso (by rw [Submodule.eq_top_of_finrank_eq hW, add_zero])
  | c + 1, W, hW, n, _, rfl =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    twistedStepIso q L hq s (n + c) ≪≫
      subspaceComplPairTwistedHomologyIso c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl

end TauCeti
