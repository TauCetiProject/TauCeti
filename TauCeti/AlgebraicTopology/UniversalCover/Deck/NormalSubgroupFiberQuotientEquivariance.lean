/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.NormalSubgroupFiberQuotient
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.NormalizerQuotientFiberAction

/-!
# Equivariance for normal deck-subgroup fibre quotients

For a normal subgroup `H ≤ Deck p`, the quotient of a fibre by `H` is already identified
with the normalizer quotient `N(H) / H`. This file records how that identification interacts
with the descended `N(H) / H` action on the fibre quotient.

The orientation is important: the existing fibre-quotient equivalence sends the orbit class
of `φ • e` to the normalizer-quotient class of `φ⁻¹`. Consequently, acting on the fibre
quotient by a normalizer-quotient element `a` corresponds, under this equivalence, to right
multiplication by `a⁻¹`.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul`:
  the `N(H) / H` action becomes right multiplication by the inverse.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul`:
  the same statement for a regular preconnected covering map.
* Inverse-form lemmas for applying the inverse equivalence after right multiplication.

## References

This supplies a small bookkeeping prerequisite for
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8: the deck group of the cover
attached to `H` is `N(H) / H`, with the normal case specializing to a quotient by `H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- Under the normal-subgroup fibre quotient equivalence, the descended normalizer-quotient
action is right multiplication by the inverse. This is the representative-free form of the
convention that `φ • e` maps to the class of `φ⁻¹`. -/
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (a : Subgroup.normalizerQuotient H) (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e (a • x) =
      subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e x * a⁻¹ := by
  obtain ⟨α, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H a
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
  rw [← hφ]
  change subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        ((Subgroup.normalizerQuotientMk H α) • subgroupFiberOrbitClass H (φ • e)) =
      subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
          (subgroupFiberOrbitClass H (φ • e)) *
        (Subgroup.normalizerQuotientMk H α)⁻¹
  rw [Subgroup.normalizerQuotientMk_apply, normalizerQuotient_smul_subgroupFiberOrbitClass,
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  change subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        (subgroupFiberOrbitClass H (((α : Deck p) * φ) • e)) =
      Subgroup.normalizerQuotientMk H
          ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ *
        (α : Subgroup.normalizerQuotient H)⁻¹
  rw [subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  simp [mul_inv_rev]

/-- For a regular preconnected covering map, the normal-subgroup fibre quotient equivalence
turns the descended normalizer-quotient action into right multiplication by the inverse. -/
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (a : Subgroup.normalizerQuotient H) (x : SubgroupFiberOrbitQuotient H b) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e (a • x) =
      regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e x * a⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  obtain ⟨α, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H a
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
  rw [← hφ]
  change regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        ((Subgroup.normalizerQuotientMk H α) • subgroupFiberOrbitClass H (φ • e)) =
      regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
          (subgroupFiberOrbitClass H (φ • e)) *
        (Subgroup.normalizerQuotientMk H α)⁻¹
  rw [Subgroup.normalizerQuotientMk_apply, normalizerQuotient_smul_subgroupFiberOrbitClass,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  change regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        (subgroupFiberOrbitClass H (((α : Deck p) * φ) • e)) =
      Subgroup.normalizerQuotientMk H
          ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ *
        (α : Subgroup.normalizerQuotient H)⁻¹
  rw [regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  simp [mul_inv_rev]

/-- Applying the inverse normal-subgroup fibre quotient equivalence after right multiplication
by `a⁻¹` is the same as acting by `a` on the fibre quotient. -/
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (a y : Subgroup.normalizerQuotient H) :
    (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm (y * a⁻¹) =
      a • (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm y := by
  apply (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).injective
  rw [Equiv.apply_symm_apply, subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul,
    Equiv.apply_symm_apply]

/-- For a regular preconnected covering map, applying the inverse normal-subgroup fibre
quotient equivalence after right multiplication by `a⁻¹` is the same as acting by `a` on the
fibre quotient. -/
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (a y : Subgroup.normalizerQuotient H) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        (y * a⁻¹) =
      a • (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        y := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  apply (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).injective
  rw [Equiv.apply_symm_apply,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul,
    Equiv.apply_symm_apply]

end Deck

end TauCeti
