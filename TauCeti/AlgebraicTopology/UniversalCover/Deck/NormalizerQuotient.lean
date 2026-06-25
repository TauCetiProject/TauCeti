/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The normalizer quotient of a subgroup

This file packages the algebraic quotient `N(H) / H`, where `N(H)` is the normalizer of a
subgroup `H ≤ G`. This is the group that occurs in the universal-covers roadmap when the
deck group of the connected cover associated to `H ≤ π₁(X, x₀)` is identified with
`N(H) / H`.

The construction is deliberately only a thin local API around Mathlib's `Subgroup.normalizer`,
`Subgroup.subgroupOf`, and quotient groups. Mathlib already proves that `H` is normal in its
normalizer; this file gives the quotient a stable name and records its canonical quotient map,
kernel, equality criterion, and the comparison with `G / H` in the normal case.

## Main declarations

* `TauCeti.Subgroup.normalizerQuotient`: the quotient `N(H) / H`.
* `TauCeti.Subgroup.normalizerQuotientMk`: the canonical map `N(H) →* N(H) / H`.
* `TauCeti.Subgroup.normalizerQuotientToQuotientOfNormal`: when `H` is normal in `G`,
  the natural map `N(H) / H →* G / H`.
* `TauCeti.Subgroup.normalizerQuotientEquivQuotientOfNormal`: when `H` is normal in `G`,
  the normalizer quotient is canonically isomorphic to `G / H`.

## References

This supplies the algebraic normalizer-quotient prerequisite named in
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2: for the cover associated to
`H ≤ π₁(X, x₀)`, the deck group is `N(H) / H`, and in the regular case `H ◁ π₁(X, x₀)`
this becomes `π₁(X, x₀) / H`.
-/

public section

namespace TauCeti

namespace Subgroup

variable {G : Type*} [Group G]

/-- The normalizer of a subgroup, as a subgroup of the ambient group. Mathlib's
`Subgroup.normalizer` is stated for a set, so this abbreviation fixes the coercion for the
normalizer quotient API below. -/
abbrev subgroupNormalizer (H : Subgroup G) : Subgroup G :=
  _root_.Subgroup.normalizer (H : Set G)

/-- The normalizer quotient `N(H) / H` of a subgroup `H ≤ G`. Here `H` is viewed as a normal
subgroup of its normalizer, using Mathlib's `Subgroup.normal_in_normalizer` instance. -/
abbrev normalizerQuotient (H : Subgroup G) : Type _ :=
  subgroupNormalizer H ⧸ H.subgroupOf (subgroupNormalizer H)

/-- The canonical quotient map from the normalizer of `H` to `N(H) / H`. -/
@[expose] def normalizerQuotientMk (H : Subgroup G) :
    subgroupNormalizer H →* normalizerQuotient H :=
  QuotientGroup.mk' (H.subgroupOf (subgroupNormalizer H))

/-- The canonical quotient map evaluates as the quotient-group constructor. -/
@[simp]
lemma normalizerQuotientMk_apply (H : Subgroup G) (g : subgroupNormalizer H) :
    normalizerQuotientMk H g = (g : normalizerQuotient H) :=
  rfl

/-- The canonical quotient map to `N(H) / H` is surjective. -/
lemma normalizerQuotientMk_surjective (H : Subgroup G) :
    Function.Surjective (normalizerQuotientMk H) :=
  QuotientGroup.mk'_surjective (H.subgroupOf (subgroupNormalizer H))

/-- The kernel of the canonical quotient map `N(H) →* N(H) / H` is `H`, viewed as a
subgroup of its normalizer. -/
@[simp]
lemma normalizerQuotientMk_ker (H : Subgroup G) :
    MonoidHom.ker (normalizerQuotientMk H) = H.subgroupOf (subgroupNormalizer H) :=
  QuotientGroup.ker_mk' (H.subgroupOf (subgroupNormalizer H))

/-- A normalizer element maps to the identity in `N(H) / H` exactly when its underlying
element of `G` lies in `H`. -/
@[simp]
lemma normalizerQuotientMk_eq_one_iff (H : Subgroup G) (g : subgroupNormalizer H) :
    normalizerQuotientMk H g = 1 ↔ (g : G) ∈ H := by
  rw [← MonoidHom.mem_ker, normalizerQuotientMk_ker]
  rfl

/-- Two elements of the normalizer have the same image in `N(H) / H` exactly when their
quotient lies in `H`. -/
lemma normalizerQuotientMk_eq_iff (H : Subgroup G) (g k : subgroupNormalizer H) :
    normalizerQuotientMk H g = normalizerQuotientMk H k ↔ (g : G) / (k : G) ∈ H := by
  simpa [normalizerQuotientMk, normalizerQuotient, _root_.Subgroup.mem_subgroupOf]
    using QuotientGroup.eq_iff_div_mem (N := H.subgroupOf (subgroupNormalizer H))
      (x := g) (y := k)

/-- A version of the equality criterion using multiplication by an element of `H`. -/
lemma normalizerQuotientMk_eq_iff_exists_mul (H : Subgroup G) (g k : subgroupNormalizer H) :
    normalizerQuotientMk H g = normalizerQuotientMk H k ↔
      ∃ h ∈ H, h * (k : G) = g := by
  rw [normalizerQuotientMk_eq_iff]
  constructor
  · intro hgk
    exact ⟨(g : G) / k, hgk, by simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨h, hh, hg⟩
    rw [← hg]
    simpa [div_eq_mul_inv, mul_assoc] using hh

section Normal

variable (H : Subgroup G) [H.Normal]

/-- When `H` is normal in `G`, every element of `G` lies in the normalizer of `H`. -/
@[expose] def toNormalizerOfNormal : G →* subgroupNormalizer H where
  toFun g := ⟨g, by simp [subgroupNormalizer, _root_.Subgroup.normalizer_eq_top (H := H)]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The coercion of `toNormalizerOfNormal` is the identity on points. -/
@[simp]
lemma toNormalizerOfNormal_apply_coe (g : G) :
    (toNormalizerOfNormal H g : G) = g :=
  rfl

/-- Under normality, `toNormalizerOfNormal` is surjective because the normalizer is all of
`G`. -/
lemma toNormalizerOfNormal_surjective :
    Function.Surjective (toNormalizerOfNormal H) := by
  intro g
  exact ⟨g, Subtype.ext rfl⟩

/-- When `H` is normal in `G`, the normalizer quotient maps naturally to the ordinary quotient
`G / H` by forgetting that representatives lie in the normalizer. -/
@[expose] def normalizerQuotientToQuotientOfNormal :
    normalizerQuotient H →* G ⧸ H :=
  QuotientGroup.lift (H.subgroupOf (subgroupNormalizer H))
    ((QuotientGroup.mk' H).comp (subgroupNormalizer H).subtype)
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := H) (x := (g : G))).mpr hg)

/-- The comparison map from `N(H) / H` to `G / H` sends a normalizer representative to its
ordinary quotient class. -/
@[simp]
lemma normalizerQuotientToQuotientOfNormal_mk (g : subgroupNormalizer H) :
    normalizerQuotientToQuotientOfNormal H (normalizerQuotientMk H g) =
      QuotientGroup.mk' H (g : G) :=
  rfl

/-- The ordinary quotient map `G →* G / H`, factored through the normalizer under normality,
agrees with the comparison map from `N(H) / H`. -/
@[simp]
lemma normalizerQuotientToQuotientOfNormal_comp_mk :
    (normalizerQuotientToQuotientOfNormal H).comp (normalizerQuotientMk H) =
      (QuotientGroup.mk' H).comp (subgroupNormalizer H).subtype :=
  rfl

/-- The comparison map `N(H) / H →* G / H` is surjective when `H` is normal in `G`. -/
lemma normalizerQuotientToQuotientOfNormal_surjective :
    Function.Surjective (normalizerQuotientToQuotientOfNormal H) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h g =>
      refine ⟨normalizerQuotientMk H (toNormalizerOfNormal H g), ?_⟩
      rw [normalizerQuotientToQuotientOfNormal_mk]
      rfl

/-- The comparison map `N(H) / H →* G / H` is injective when `H` is normal in `G`. -/
lemma normalizerQuotientToQuotientOfNormal_injective :
    Function.Injective (normalizerQuotientToQuotientOfNormal H) := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | h g =>
      induction r using Quotient.inductionOn' with
      | h k =>
          change normalizerQuotientMk H g = normalizerQuotientMk H k
          apply (normalizerQuotientMk_eq_iff H g k).mpr
          change (normalizerQuotientToQuotientOfNormal H) (normalizerQuotientMk H g) =
              (normalizerQuotientToQuotientOfNormal H) (normalizerQuotientMk H k) at hqr
          rw [normalizerQuotientToQuotientOfNormal_mk,
            normalizerQuotientToQuotientOfNormal_mk] at hqr
          exact (QuotientGroup.eq_iff_div_mem (N := H) (x := (g : G)) (y := (k : G))).mp
            hqr

/-- If `H` is normal in `G`, then `N(H) / H` is canonically isomorphic to `G / H`. This is
the algebraic form of the regular-cover specialization from `N(H) / H` to `π₁(X, x₀) / H`. -/
@[expose] noncomputable def normalizerQuotientEquivQuotientOfNormal :
    normalizerQuotient H ≃* G ⧸ H :=
  MulEquiv.ofBijective (normalizerQuotientToQuotientOfNormal H)
    ⟨normalizerQuotientToQuotientOfNormal_injective H,
      normalizerQuotientToQuotientOfNormal_surjective H⟩

/-- The normal-case equivalence sends a normalizer representative to its ordinary quotient
class in `G / H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_mk (g : subgroupNormalizer H) :
    normalizerQuotientEquivQuotientOfNormal H (normalizerQuotientMk H g) =
      QuotientGroup.mk' H (g : G) :=
  rfl

end Normal

end Subgroup

end TauCeti
