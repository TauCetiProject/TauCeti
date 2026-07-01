/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.NormalSubgroupFiberQuotient

/-!
# Equality criteria for normal deck-subgroup fibre quotients

For a normal subgroup `H ≤ Deck p`, the quotient of a regular-cover fibre by `H` is already
identified with the normalizer quotient `N(H) / H`. This file records the corresponding
consumer lemmas: two translated fibre points define the same `H`-orbit exactly when the
associated normalizer-quotient representatives agree, and a translated fibre point has the
base orbit exactly when the translating deck transformation lies in `H`.

These are bookkeeping lemmas for the universal-covers roadmap. In the cover-classification
lane, the deck group of the cover associated to a normal subgroup is computed as the quotient
`π₁(X, x₀) / H`; the statements here are the deck-action fibre analogues needed before that
comparison is specialized to fundamental groups.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq`: equality of
  `H`-orbits of `φ • e` and `ψ • e` is equality of the corresponding inverse representatives
  in `N(H) / H`.
* `TauCeti.Deck.subgroupFiberOrbitClass_smul_eq_base_iff`: the class of `φ • e` is the base
  class exactly when `φ ∈ H`.
* Regular-cover wrappers for both criteria.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 8: the regular-cover bookkeeping around the normalizer quotient `N(H)/H` and its normal
case `π₁(X, x₀) / H`. No Mathlib infrastructure is vendored.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- Equality of normal-subgroup fibre-orbit classes is equality of the corresponding
normalizer-quotient classes, with the inverse orientation inherited from Mathlib's
subgroup-orbit quotient convention. -/
lemma subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      Subgroup.normalizerQuotientMk H
          ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨ψ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  constructor
  · intro h
    have h' := congrArg (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e) h
    rw [subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul,
      subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul] at h'
    exact h'
  · intro h
    apply (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).injective
    rw [subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul,
      subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
    exact h

/-- For a regular cover, equality of normal-subgroup fibre-orbit classes is equality of the
corresponding normalizer-quotient classes. -/
lemma regularSubgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      Subgroup.normalizerQuotientMk H
          ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨ψ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq H e φ ψ

/-- The inverse-translate spelling of
`subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq`: the class of `φ⁻¹ • e`
corresponds to the representative `φ` in the normalizer quotient. -/
lemma subgroupFiberOrbitClass_inv_smul_eq_iff_normalizerQuotientMk_eq
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ⁻¹ • e) = subgroupFiberOrbitClass H (ψ⁻¹ • e) ↔
      Subgroup.normalizerQuotientMk H
          ⟨φ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨ψ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  simpa using subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq H e φ⁻¹ ψ⁻¹

/-- For a regular cover, the inverse-translate spelling of the normalizer-quotient equality
criterion. -/
lemma regularSubgroupFiberOrbitClass_inv_smul_eq_iff_normalizerQuotientMk_eq
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ⁻¹ • e) = subgroupFiberOrbitClass H (ψ⁻¹ • e) ↔
      Subgroup.normalizerQuotientMk H
          ⟨φ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨ψ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_inv_smul_eq_iff_normalizerQuotientMk_eq H e φ ψ

/-- A deck translate of the chosen fibre point has the same normal-subgroup orbit class as
the chosen point exactly when the translating deck transformation lies in the subgroup. -/
lemma subgroupFiberOrbitClass_smul_eq_base_iff
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H e ↔ φ ∈ H := by
  have hbase :
      subgroupFiberOrbitClass H e = subgroupFiberOrbitClass H ((1 : Deck p) • e) := by
    simp
  rw [hbase]
  rw [subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq H e φ 1]
  constructor
  · intro h
    have hmem := (Subgroup.normalizerQuotientMk_eq_iff_div_mem H _ _).mp h
    have hφinv : φ⁻¹ ∈ H := by simpa [div_eq_mul_inv] using hmem
    simpa using H.inv_mem hφinv
  · intro hφ
    apply (Subgroup.normalizerQuotientMk_eq_iff_div_mem H _ _).mpr
    simpa [div_eq_mul_inv] using H.inv_mem hφ

/-- For a regular cover, a deck translate of the chosen fibre point has the same
normal-subgroup orbit class as the chosen point exactly when the translating deck
transformation lies in the subgroup. -/
lemma regularSubgroupFiberOrbitClass_smul_eq_base_iff
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H e ↔ φ ∈ H := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_smul_eq_base_iff H e φ

/-- The chosen fibre point has the same normal-subgroup orbit class as a deck translate
exactly when the translating deck transformation lies in the subgroup. -/
lemma subgroupFiberOrbitClass_base_eq_smul_iff
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitClass H e = subgroupFiberOrbitClass H (φ • e) ↔ φ ∈ H := by
  rw [eq_comm, subgroupFiberOrbitClass_smul_eq_base_iff H e φ]

/-- For a regular cover, the chosen fibre point has the same normal-subgroup orbit class as
a deck translate exactly when the translating deck transformation lies in the subgroup. -/
lemma regularSubgroupFiberOrbitClass_base_eq_smul_iff
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitClass H e = subgroupFiberOrbitClass H (φ • e) ↔ φ ∈ H := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_base_eq_smul_iff H e φ

end Deck

end TauCeti
