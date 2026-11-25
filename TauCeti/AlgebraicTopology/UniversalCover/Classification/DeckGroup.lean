/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.Normalizer

/-!
# The deck group of the cover attached to a subgroup

For `H ≤ π₁(X, x₀)`, the orbit quotient `UniversalCover x₀ / H` is a covering space of `X`
through `UniversalCover.subgroupQuotientProj`. This file computes its deck transformation
group:

  `deck (subgroupQuotientProj x₀ H) ≃* N(H) ⧸ H`,

and, when `H` is normal, `deck (subgroupQuotientProj x₀ H) ≃* π₁(X, x₀) ⧸ H`. Both are the
specialisation to the universal cover of
`IsQuotientCoveringMap.normalizerQuotientDeckMulEquiv`.

The isomorphism is stated for the left action of `π₁(X, x₀)` on the universal cover, in which
a loop class acts by prepending its inverse; this is the same convention as
`IsQuotientCoveringMap.deckMulEquiv`, and it is why no `ᵐᵒᵖ` appears here, unlike
in the monodromy identification `UniversalCover.deckFundamentalGroupEquiv`.

Taking `H = ⊥` recovers the deck group of the universal cover itself; taking `H` normal and
`H = ⊥` gives `π₁(X, x₀)` again.

In the geometric fundamental group `TauCeti.GeometricFundamentalGroup X x₀ = π₁(X, x₀)ᵐᵒᵖ`, whose
product is first-traverse concatenation, the quotient by a normal subgroup `N` is the deck group of
the cover attached to the image of `N` under inversion
(`TauCeti.UniversalCover.geometricDeckQuotientEquiv`), and the deck transformation of the class
of `a` is the one induced by the deck transformation `(deckFundamentalGroupEquiv x₀).symm a` of
the universal cover
(`TauCeti.UniversalCover.geometricDeckQuotientEquiv_mk_apply_subgroupQuotientMap`).

## Main declarations

* `TauCeti.UniversalCover.deckSubgroupQuotientProjEquiv`: **the deck group of the cover
  attached to `H` is `N(H) ⧸ H`.**
* `TauCeti.UniversalCover.deckSubgroupQuotientProjEquivOfNormal`: for normal `H` this reads
  `π₁(X, x₀) ⧸ H`.
* `TauCeti.UniversalCover.deckSubgroupQuotientProjKerEquivRange`: for the kernel of a
  homomorphism `φ` out of `π₁(X, x₀)` this reads `φ.range`.
* `TauCeti.UniversalCover.deckSubgroupQuotientProjKerEquivOfSurjective`: for the kernel of a
  surjective homomorphism `φ : π₁(X, x₀) →* G` this reads `G`.
* `TauCeti.UniversalCover.geometricDeckQuotientEquiv`: for a normal subgroup `N` of the geometric
  fundamental group, the quotient by `N` is the deck group of the cover attached to the image of
  `N` under inversion.

## References

It consumes the based-path universal cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), Mathlib's
quotient-covering-map interface due to Junyan Xu, and the covering-map property of
`subgroupQuotientProj` proved in
`TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence`.
-/

public section
noncomputable section

variable {X : Type*} [TopologicalSpace X]

namespace TauCeti.UniversalCover

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
variable (x₀ : X) (H : Subgroup (FundamentalGroup X x₀))

/-- **The deck group of the cover attached to `H ≤ π₁(X, x₀)` is the normalizer quotient
`N(H) ⧸ H`.** A normalizer class acts by descending its translation of the universal cover. -/
def deckSubgroupQuotientProjEquiv :
    (Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) ⧸
        H.subgroupOf (Subgroup.normalizer (H : Set (FundamentalGroup X x₀)))
      ≃* deck (subgroupQuotientProj x₀ H) :=
  (isQuotientCoveringMap (x₀ := x₀)).normalizerQuotientDeckMulEquiv
    (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
    (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H)
    (isCoveringMap_subgroupQuotientProj x₀ H)

/-- The normalizer class of `g` acts on the cover attached to `H` by sending the class of `e`
to the class of `g • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquiv_mk_apply
    (g : Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquiv x₀ H (QuotientGroup.mk g)).val (Quotient.mk'' e) =
      Quotient.mk'' ((g : FundamentalGroup X x₀) • e) := by
  simpa [deckSubgroupQuotientProjEquiv] using
    (isQuotientCoveringMap (x₀ := x₀)).normalizerDeckHom_apply
      (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

/-- The inverse of the deck transformation attached to the normalizer class of `g` sends the
class of `e` to the class of `g⁻¹ • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquiv_mk_symm_apply
    (g : Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquiv x₀ H (QuotientGroup.mk g)).val.symm (Quotient.mk'' e) =
      Quotient.mk'' ((g : FundamentalGroup X x₀)⁻¹ • e) := by
  simpa [deckSubgroupQuotientProjEquiv] using
    (isQuotientCoveringMap (x₀ := x₀)).normalizerDeckHom_symm_apply
      (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

/-- **For a normal subgroup `H ◁ π₁(X, x₀)`, the deck group of the cover attached to `H` is
`π₁(X, x₀) ⧸ H`**, so that cover is regular. -/
def deckSubgroupQuotientProjEquivOfNormal [H.Normal] :
    FundamentalGroup X x₀ ⧸ H ≃* deck (subgroupQuotientProj x₀ H) :=
  (isQuotientCoveringMap (x₀ := x₀)).quotientDeckMulEquivOfNormal
    (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
    (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H)
    (isCoveringMap_subgroupQuotientProj x₀ H)

/-- For normal `H`, the class of `g` acts on the cover attached to `H` by sending the class of
`e` to the class of `g • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquivOfNormal_mk_apply [H.Normal]
    (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquivOfNormal x₀ H (QuotientGroup.mk g)).val
        (Quotient.mk'' e) = Quotient.mk'' (g • e) := by
  simpa [deckSubgroupQuotientProjEquivOfNormal] using
    (isQuotientCoveringMap (x₀ := x₀)).deckHomOfNormal_apply
      (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

/-- For normal `H`, the inverse of the deck transformation attached to the class of `g` sends
the class of `e` to the class of `g⁻¹ • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquivOfNormal_mk_symm_apply [H.Normal]
    (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquivOfNormal x₀ H (QuotientGroup.mk g)).val.symm
        (Quotient.mk'' e) = Quotient.mk'' (g⁻¹ • e) := by
  simpa [deckSubgroupQuotientProjEquivOfNormal] using
    (isQuotientCoveringMap (x₀ := x₀)).deckHomOfNormal_symm_apply
      (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

section Ker

variable {G : Type*} [Group G] (φ : FundamentalGroup X x₀ →* G)

/-- **The deck group of the cover attached to the kernel of `φ : π₁(X, x₀) →* G` is the range
of `φ`**: the deck transformation of the class of `g` is labelled by `φ g`. -/
def deckSubgroupQuotientProjKerEquivRange : deck (subgroupQuotientProj x₀ φ.ker) ≃* φ.range :=
  (deckSubgroupQuotientProjEquivOfNormal x₀ φ.ker).symm.trans
    (QuotientGroup.quotientKerEquivRange φ)

/-- The deck transformation of the class of `g` is labelled by `φ g`. -/
@[simp]
theorem deckSubgroupQuotientProjKerEquivRange_deckSubgroupQuotientProjEquivOfNormal_mk
    (g : FundamentalGroup X x₀) :
    deckSubgroupQuotientProjKerEquivRange x₀ φ
        (deckSubgroupQuotientProjEquivOfNormal x₀ φ.ker (QuotientGroup.mk g)) =
      φ.rangeRestrict g := by
  simp [deckSubgroupQuotientProjKerEquivRange, Subtype.ext_iff]

/-- The deck transformation labelled by `φ g` sends the class of `e` to the class of `g • e`. -/
@[simp]
theorem deckSubgroupQuotientProjKerEquivRange_symm_rangeRestrict_apply_mk
    (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    ((deckSubgroupQuotientProjKerEquivRange x₀ φ).symm (φ.rangeRestrict g)).val
        (Quotient.mk'' e) = Quotient.mk'' (g • e) := by
  rw [← deckSubgroupQuotientProjKerEquivRange_deckSubgroupQuotientProjEquivOfNormal_mk,
    MulEquiv.symm_apply_apply, deckSubgroupQuotientProjEquivOfNormal_mk_apply]

/-- **The deck group of the cover attached to the kernel of a surjective `φ : π₁(X, x₀) →* G` is
`G`**: the deck transformation of the class of `g` is labelled by `φ g`. -/
def deckSubgroupQuotientProjKerEquivOfSurjective (hφ : Function.Surjective φ) :
    deck (subgroupQuotientProj x₀ φ.ker) ≃* G :=
  (deckSubgroupQuotientProjEquivOfNormal x₀ φ.ker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

/-- For surjective `φ`, the deck transformation of the class of `g` is labelled by `φ g`. -/
@[simp]
theorem deckSubgroupQuotientProjKerEquivOfSurjective_deckSubgroupQuotientProjEquivOfNormal_mk
    (hφ : Function.Surjective φ) (g : FundamentalGroup X x₀) :
    deckSubgroupQuotientProjKerEquivOfSurjective x₀ φ hφ
        (deckSubgroupQuotientProjEquivOfNormal x₀ φ.ker (QuotientGroup.mk g)) = φ g := by
  rw [deckSubgroupQuotientProjKerEquivOfSurjective, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- For surjective `φ`, the deck transformation labelled by `φ g` sends the class of `e` to the
class of `g • e`. -/
@[simp]
theorem deckSubgroupQuotientProjKerEquivOfSurjective_symm_apply_mk
    (hφ : Function.Surjective φ) (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    ((deckSubgroupQuotientProjKerEquivOfSurjective x₀ φ hφ).symm (φ g)).val
        (Quotient.mk'' e) = Quotient.mk'' (g • e) := by
  rw [← deckSubgroupQuotientProjKerEquivOfSurjective_deckSubgroupQuotientProjEquivOfNormal_mk
      _ _ hφ,
    MulEquiv.symm_apply_apply, deckSubgroupQuotientProjEquivOfNormal_mk_apply]

end Ker

section Geometric

open _root_.MulOpposite

variable (N : Subgroup (GeometricFundamentalGroup X x₀)) [N.Normal]

/-- For a normal subgroup `N` of the geometric fundamental group, the quotient by `N` is the deck
group of the cover attached to the image of `N` under inversion `op g ↦ g⁻¹`, written as the
preimage of `N` under the inverse isomorphism `MulEquiv.inv'`, `g ↦ op g⁻¹`. -/
def geometricDeckQuotientEquiv :
    GeometricFundamentalGroup X x₀ ⧸ N ≃*
      deck (subgroupQuotientProj x₀
        (N.comap (MulEquiv.inv' (FundamentalGroup X x₀) : FundamentalGroup X x₀ →* _))) :=
  (QuotientGroup.congr N _ (MulEquiv.inv' _).symm
    (by rw [N.map_equiv_eq_comap_symm, MulEquiv.symm_symm])).trans
    (deckSubgroupQuotientProjEquivOfNormal x₀ _)

/-- The deck transformation of the class of `op g` sends the class of `e` to the class of
`g⁻¹ • e`, as `(deckFundamentalGroupEquiv x₀).symm (op g)` does on the universal cover. -/
@[simp]
theorem geometricDeckQuotientEquiv_mk_op_apply (g : FundamentalGroup X x₀)
    (e : UniversalCover x₀) :
    (geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk (op g))).val (Quotient.mk'' e) =
      Quotient.mk'' (g⁻¹ • e) := by
  rw [geometricDeckQuotientEquiv, MulEquiv.trans_apply, QuotientGroup.congr_mk]
  simp

/-- The inverse of the deck transformation of the class of `op g` sends the class of `e` to the
class of `g • e`. -/
@[simp]
theorem geometricDeckQuotientEquiv_mk_op_symm_apply (g : FundamentalGroup X x₀)
    (e : UniversalCover x₀) :
    (geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk (op g))).val.symm (Quotient.mk'' e) =
      Quotient.mk'' (g • e) := by
  rw [geometricDeckQuotientEquiv, MulEquiv.trans_apply, QuotientGroup.congr_mk]
  -- Plain `simp` moves the inversion out through `deckSubgroupQuotientProjEquivOfNormal` and
  -- gets stuck at `(φ g)⁻¹.symm`, so `inv'` is unfolded first and `inv_inv` cancels it.
  simp only [MulEquiv.inv'_symm_apply, Function.comp_apply, unop_op,
    deckSubgroupQuotientProjEquivOfNormal_mk_symm_apply, inv_inv]

/-- **Descent of deck transformations.** The deck transformation of the class of `a` on the cover
attached to `N` is induced by the deck transformation `(deckFundamentalGroupEquiv x₀).symm a` of
the universal cover: it commutes with the quotient map `subgroupQuotientMap`. -/
theorem geometricDeckQuotientEquiv_mk_apply_subgroupQuotientMap
    (a : GeometricFundamentalGroup X x₀) (e : UniversalCover x₀) :
    (geometricDeckQuotientEquiv x₀ N (QuotientGroup.mk a)).val
        (subgroupQuotientMap x₀ _ e) =
      subgroupQuotientMap x₀ _ (((deckFundamentalGroupEquiv x₀).symm a).val e) := by
  induction a using MulOpposite.rec' with
  | _ g => simp

end Geometric

end TauCeti.UniversalCover
