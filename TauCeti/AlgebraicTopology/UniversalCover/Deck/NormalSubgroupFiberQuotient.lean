/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbitQuotientGroup

/-!
# Normal deck-subgroup fibre quotients

For a regular preconnected covering map, the quotient of one fibre by a subgroup
`H ≤ Deck p` is already identified with the coset quotient `Deck p ⧸ H`. When `H` is normal,
the universal-covers roadmap uses this quotient as the regular-cover specialization of the
normalizer quotient `N(H) / H`. This file records that specialization directly, so later
deck-group computations for quotient covers can move between fibre quotients and
normalizer quotients without redoing the algebraic comparison.

## Main declarations

* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal`: for a
  regular preconnected cover and a normal subgroup `H ≤ Deck p`, the quotient of a fibre by
  `H` is equivalent to `N(H) / H`.
* Simp lemmas for the image of the chosen lift, its deck translates, and representatives of
  the inverse map.

## References

This is a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8:
in the regular case `H ◁ π₁(X, x₀)`, the deck group of the cover attached to `H` is
`π₁(X, x₀) / H`. The file combines the existing Tau Ceti regular fibre-quotient equivalence
with the algebraic normalizer-quotient comparison; no Mathlib infrastructure is vendored.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b : B}

/-- For a regular preconnected covering and a normal subgroup `H ≤ Deck p`, the quotient of a
fibre by the restricted `H`-action is the normalizer quotient `N(H) / H`.

Under normality, `N(H) = Deck p`, so this is the fibre-level version of the regular-cover
specialization from `N(H) / H` to `Deck p / H`. -/
noncomputable def regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Subgroup.normalizerQuotient H :=
  (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).trans
    (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.symm

/-- The normal-subgroup fibre quotient equivalence, followed by the normalizer quotient's
normal-case comparison, is the existing equivalence to `Deck p ⧸ H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e x) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x := by
  exact (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.apply_symm_apply
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x)

/-- The chosen fibre point maps to the identity class in the normalizer quotient. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_base
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        (subgroupFiberOrbitClass H e) =
      Subgroup.normalizerQuotientMk H
        ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  simpa using
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
      hp hreg H e (1 : Deck p)

/-- The normal-subgroup fibre quotient equivalence sends the class of `φ • e` to the
normalizer-quotient class of `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        (subgroupFiberOrbitClass H (φ • e)) =
      Subgroup.normalizerQuotientMk H
        ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv,
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  rfl

/-- The normal-subgroup fibre quotient equivalence sends the class of `φ⁻¹ • e` to the
normalizer-quotient class of `φ`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_inv_smul
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      Subgroup.normalizerQuotientMk H
        ⟨φ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  simpa using
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul
      hp hreg H e φ⁻¹

/-- The inverse equivalence sends a normalizer representative to the fibre-orbit class of its
inverse acting on the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        (Subgroup.normalizerQuotientMk H φ) =
      subgroupFiberOrbitClass H ((φ : Deck p)⁻¹ • e) := by
  apply (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).injective
  rw [Equiv.apply_symm_apply,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [Subgroup.normalizerQuotientEquivQuotientOfNormal_mk,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  simp

/-- In particular, the inverse equivalence sends the identity normalizer quotient class to the
chosen fibre-orbit class. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_one
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        (Subgroup.normalizerQuotientMk H
          ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩) =
      subgroupFiberOrbitClass H e := by
  simpa using
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk
      hp hreg H e ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩

end Deck

end TauCeti
