/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit.QuotientGroup

/-!
# Normal deck-subgroup fibre quotients

For a regular preconnected covering map, the quotient of one fibre by a subgroup
`H ≤ deck p` is already identified with the coset quotient `deck p ⧸ H`. When `H` is normal,
this quotient is the regular-cover specialization of the normalizer quotient `N(H) / H`. This
file records that specialization directly, so deck-group computations for quotient covers can
move between fibre quotients and normalizer quotients without redoing the algebraic comparison.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal`: for a normal
  subgroup `H ≤ deck p`, identifies the subgroup fibre-orbit quotient with `N(H) / H` when
  the deck action on the chosen fibre is free and transitive.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal`: the
  regular-cover specialization.
* Simp lemmas for the image of the chosen fibre point, its deck translates, and
  representatives of the inverse map.

## References

In the regular case `H ◁ π₁(X, x₀)`, the deck group of the cover attached to `H` is
`π₁(X, x₀) / H`. The file combines Tau Ceti's regular fibre-quotient equivalence with the
algebraic normalizer-quotient comparison.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- For a normal subgroup `H ≤ deck p`, the quotient of a fibre by the restricted `H`-action
is the normalizer quotient `N(H) / H`, once the deck action on the fibre is free and
transitive.

Under normality, `N(H) = deck p`, so this is the fibre-level version of the regular-cover
specialization from `N(H) / H` to `deck p / H`. -/
noncomputable def subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Subgroup.normalizerQuotient H :=
  TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal
    (G := deck p) (X := p ⁻¹' {b}) H e

/-- For a regular preconnected covering and a normal subgroup `H ≤ deck p`, the quotient of a
fibre by the restricted `H`-action is the normalizer quotient `N(H) / H`. -/
noncomputable def regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Subgroup.normalizerQuotient H :=
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e

/-- The normal-subgroup fibre quotient equivalence, followed by the normalizer quotient's
normal-case comparison, is the existing equivalence to `deck p ⧸ H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e x) =
      subgroupFiberOrbitQuotientEquivQuotientGroup H e x := by
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (deck p) e e'
  rw [← hφ]
  -- The deck-specific normalizer quotient equivalence is a wrapper around the generic
  -- orbit-relation equivalence; the quotient-group equivalence is kept opaque.
  change
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal
          (G := deck p) (X := p ⁻¹' {b}) H e
          (Quotient.mk'' (φ • e) : _root_.MulAction.orbitRel.Quotient H (p ⁻¹' {b}))) =
      subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H (φ • e))
  rw [TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  rfl

/-- For a regular cover, the normal-subgroup fibre quotient equivalence, followed by the
normalizer quotient's normal-case comparison, is the existing equivalence to `deck p ⧸ H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e x) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (deck p) e e'
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
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        (subgroupFiberOrbitClass H e) =
      Subgroup.normalizerQuotientMk H
        ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  simp

/-- For a regular cover, the chosen fibre point maps to the identity class in the normalizer
quotient. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_base
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        (subgroupFiberOrbitClass H e) =
      Subgroup.normalizerQuotientMk H
        ⟨1, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  rw [normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv,
    Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  simpa using
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
      hp hreg H e (1 : deck p)

/-- The normal-subgroup fibre quotient equivalence sends the class of `φ • e` to the
normalizer-quotient class of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : deck p) :
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
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : deck p) :
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
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_inv_smul
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : deck p) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      Subgroup.normalizerQuotientMk H
        ⟨φ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  simpa only [inv_inv] using
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul H e φ⁻¹

/-- For a regular cover, the normal-subgroup fibre quotient equivalence sends the class of
`φ⁻¹ • e` to the normalizer-quotient class of `φ`. -/
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_inv_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ : deck p) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      Subgroup.normalizerQuotientMk H
        ⟨φ, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  simp

/-- Equality of subgroup fibre-orbit classes of two deck translates is equality of the
corresponding inverse representatives in the normalizer quotient. -/
lemma subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ ψ : deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      Subgroup.normalizerQuotientMk H
          ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨ψ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  exact TauCeti.MulAction.orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq
    (G := deck p) (X := p ⁻¹' {b}) H e φ ψ

/-- For a preconnected cover, equality of subgroup fibre-orbit classes of two deck translates is
equality of the corresponding inverse representatives in the normalizer quotient. -/
lemma subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq_of_isCoveringMap
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p)
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) (φ ψ : deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      Subgroup.normalizerQuotientMk H
          ⟨φ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨ψ⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  let := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_eq_iff_normalizerQuotientMk_inv_eq H e φ ψ

/-- The inverse equivalence sends a normalizer representative to the fibre-orbit class of its
inverse acting on the chosen fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b})
    (φ : _root_.Subgroup.normalizer (H : Set (deck p))) :
    (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm
        (φ : Subgroup.normalizerQuotient H) =
      subgroupFiberOrbitClass H ((φ : deck p)⁻¹ • e) := by
  rw [← Subgroup.normalizerQuotientMk_apply]
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
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b})
    (φ : _root_.Subgroup.normalizer (H : Set (deck p))) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        (φ : Subgroup.normalizerQuotient H) =
      subgroupFiberOrbitClass H ((φ : deck p)⁻¹ • e) := by
  rw [← Subgroup.normalizerQuotientMk_apply]
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
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm
        (1 : Subgroup.normalizerQuotient H) =
      subgroupFiberOrbitClass H e := by
  rw [← QuotientGroup.mk_one, subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk]
  simp

/-- For a regular cover, the inverse equivalence sends the identity normalizer quotient class
to the chosen fibre-orbit class. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_one
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        (1 : Subgroup.normalizerQuotient H) =
      subgroupFiberOrbitClass H e := by
  rw [← QuotientGroup.mk_one,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mk]
  simp

end Deck

end TauCeti
