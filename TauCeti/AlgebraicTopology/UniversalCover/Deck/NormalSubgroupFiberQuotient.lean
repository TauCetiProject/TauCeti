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

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal`: for a normal
  subgroup `H ≤ Deck p`, identifies the subgroup fibre-orbit quotient with `N(H) / H` when
  the deck action on the chosen fibre is free and transitive.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal`: the
  regular-cover specialization.
* Simp lemmas for the image of the chosen fibre point, its deck translates, and
  representatives of the inverse map.

## References

This is a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8:
in the regular case `H ◁ π₁(X, x₀)`, the deck group of the cover attached to `H` is
`π₁(X, x₀) / H`. The file combines the existing Tau Ceti regular fibre-quotient equivalence
with the algebraic normalizer-quotient comparison; no Mathlib infrastructure is vendored.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- For a normal subgroup `H ≤ Deck p`, the quotient of a fibre by the restricted `H`-action
is the normalizer quotient `N(H) / H`, once the deck action on the fibre is free and
transitive.

Under normality, `N(H) = Deck p`, so this is the fibre-level version of the regular-cover
specialization from `N(H) / H` to `Deck p / H`. -/
noncomputable def subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Subgroup.normalizerQuotient H :=
  (subgroupFiberOrbitQuotientEquivQuotientGroup H e).trans
    (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.symm

/-- For a regular preconnected covering and a normal subgroup `H ≤ Deck p`, the quotient of a
fibre by the restricted `H`-action is the normalizer quotient `N(H) / H`. -/
noncomputable def regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Subgroup.normalizerQuotient H :=
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e

/-- The normal-subgroup fibre quotient equivalence, followed by the normalizer quotient's
normal-case comparison, is the existing equivalence to `Deck p ⧸ H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e x) =
      subgroupFiberOrbitQuotientEquivQuotientGroup H e x := by
  exact (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.apply_symm_apply
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e x)

/-- For a regular cover, the normal-subgroup fibre quotient equivalence, followed by the
normalizer quotient's normal-case comparison, is the existing equivalence to `Deck p ⧸ H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e x) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
  rw [← hφ]
  -- The regular wrapper unfolds, with the two instances above, to the fibre-action equivalence.
  change
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
          (subgroupFiberOrbitClass H (φ • e))) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ • e))
  rw [normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]

/-- The chosen fibre point maps to the identity class in the normalizer quotient. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_base
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        (subgroupFiberOrbitClass H e) =
      Subgroup.normalizerQuotientMk H
        ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e (1 : Deck p)

/-- For a regular cover, the chosen fibre point maps to the identity class in the normalizer
quotient. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_base
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
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
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        (subgroupFiberOrbitClass H (φ • e)) =
      Subgroup.normalizerQuotientMk H
        ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  rfl

/-- For a regular cover, the normal-subgroup fibre quotient equivalence sends the class of
`φ • e` to the normalizer-quotient class of `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
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
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_inv_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      Subgroup.normalizerQuotientMk H
        ⟨φ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  simpa using
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul H e φ⁻¹

/-- For a regular cover, the normal-subgroup fibre quotient equivalence sends the class of
`φ⁻¹ • e` to the normalizer-quotient class of `φ`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_inv_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
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
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm
        (Subgroup.normalizerQuotientMk H φ) =
      subgroupFiberOrbitClass H ((φ : Deck p)⁻¹ • e) := by
  apply (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).injective
  rw [Equiv.apply_symm_apply,
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [Subgroup.normalizerQuotientEquivQuotientOfNormal_mk,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  simp

/-- For a regular cover, the inverse equivalence sends a normalizer representative to the
fibre-orbit class of its inverse acting on the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
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
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_one
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm
        (Subgroup.normalizerQuotientMk H
          ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩) =
      subgroupFiberOrbitClass H e := by
  simpa using
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk
      H e ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩

/-- For a regular cover, the inverse equivalence sends the identity normalizer quotient class
to the chosen fibre-orbit class. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_one
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
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
