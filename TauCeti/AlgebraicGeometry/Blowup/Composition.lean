/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Product
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentation
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.FlatBaseChange

/-!
# Composition of blowups

Let `b₁ : Bl_I X ⟶ X` be the blowup of a scheme `X` along an ideal sheaf `I`, and let
`b₂ : Bl_J (Bl_I X) ⟶ Bl_I X` be a second blowup along an ideal sheaf `J` on `Bl_I X`. This file
shows that the composite `b₂ ≫ b₁` is isomorphic over `X` to a single blowup `Bl_K X ⟶ X`
whenever there is an ideal sheaf `K₁` on `X` such that

`K₁.comap b₁ = E * J`

for an effective Cartier divisor `E` on `Bl_I X` (for example `E = I.comap b₁ ^ d` for `d : ℕ`),
namely for the product centre `K = I * K₁`.

## Mathematical overview

1. *Universal-property comparison on an arbitrary scheme.* Multiplying `K₁` by `I` ensures that on
   `Bl_{I * K₁} X` both `I` and `K₁` pull back to effective Cartier divisors
   (`isEffectiveCartier_comap_blowupToBase_mul_left`,
   `isEffectiveCartier_comap_blowupToBase_mul_right`), giving the canonical projection
   `π₁ = I.blowupMulFst K₁ : Bl_{I * K₁} X ⟶ Bl_I X` over `X`. Pulling `K₁.comap b₁ = E * J`
   back along `π₁` expresses the effective Cartier divisor `K₁.comap (I * K₁).blowupToBase` as
   `E.comap π₁ * J.comap π₁`; factor descent (`IsEffectiveCartier.of_mul_right`) then makes
   `J.comap π₁` effective Cartier, so `π₁` lifts to `Bl_J (Bl_I X)`. Conversely, on `Bl_J (Bl_I X)`
   both `E.comap b₂` (`IsEffectiveCartier.comap_blowupToBase`) and `J.comap b₂` are effective
   Cartier, so `(I * K₁).comap (b₂ ≫ b₁)` is effective Cartier and `b₂ ≫ b₁` lifts to
   `Bl_{I * K₁} X`. By uniqueness of lifts to blowups, the two morphisms are mutually inverse
   (`blowupCompIso`). Away from `V(I)` the first blowup `b₁` is an isomorphism, so when
   `K₁.comap b₁ = E * J`, the support `V(I * K₁)` equals `V(I) ∪ b₁(V(E)) ∪ b₁(V(J))`
   (`coe_support_mul_of_comap_blowupToBase_eq`), and `V(I * K₁)` avoids `s ⊆ X` iff `V(I)` avoids
   `s` while `V(E)` and `V(J)` avoid `b₁⁻¹(s)`
   (`disjoint_support_mul_of_comap_blowupToBase_eq_iff`); when `E = I.comap b₁ ^ d`,
   `b₁(V(E)) ⊆ V(I)`, simplifying the support to `V(I) ∪ b₁(V(J))`
   (`coe_support_mul_of_comap_blowupToBase_eq_pow_mul`,
   `disjoint_support_mul_of_comap_blowupToBase_eq_pow_mul_iff`).

2. *Clearing denominators on an affine blowup.* For a finitely generated ideal `I ≤ R` and an
   ideal sheaf `J` of finite type on `Proj R[It]`, finitely many charts `Spec R[I/aᵢ]` cover
   `Proj R[It]`. On each chart `R[I/aᵢ] ⊆ R_{aᵢ}`, a finite generating family of `J` clears
   denominators against a common power `aᵢ^{mᵢ}` (`Ideal.mem_affineBlowup_iff`). On any second
   chart `Spec R[I/aⱼ]`, the overlap with `D₊(aᵢ t)` is the basic open of `aᵢ / aⱼ`
   (`affineBlowupι_preimage_basicOpen`), so some power `(aᵢ / aⱼ)^k` multiplies the numerator into
   `aⱼ^{mᵢ} J(D₊(aⱼ t))`; multiplying by `aⱼ^k` shows that `aᵢ^k` times the numerator lands in
   `aⱼ^{mᵢ + k} J(D₊(aⱼ t))`. Taking `d` at least the maximum of all `mᵢ + k` produces a finitely
   generated ideal `K₀ ≤ R` whose pullback to `Proj R[It]` is `I.comap π ^ d * J`
   (`exists_fg_ideal_comap_toSpecCoeff_eq`), and sandwiching via the `comap`/`map` adjunction shows
   that the schematic image `((I.comap π ^ d * J).map π)` has the same pullback
   (`exists_comap_map_toSpecCoeff_eq`). No Noetherian assumption on `R` is required.

3. *Global quasi-compact, affine, and locally Noetherian bases.* On a quasi-compact scheme `X`,
   finitely many affine charts `Spec Γ(X, V) ⟶ X` cover `X`. Since `b₁` is proper for finite-type
   `I`, schematic images commute with flat base change along `Spec Γ(X, V) ⟶ X`
   (`comap_map_of_isPullback_of_flat`), so choosing `d` above the bounds on each `V` gives
   `K₁ = (I.comap b₁ ^ d * J).map b₁` with `K₁.comap b₁ = I.comap b₁ ^ d * J`
   (`exists_comap_map_blowupToBase_eq`). Combining this with `blowupCompIso` yields
   `exists_blowup_comp_of_compactSpace` (including properness of `K.blowupToBase` and its exact
   support `V(I) ∪ b₁(V(J))`), the finite-type centre refinement
   `exists_blowup_comp_of_isAffine` over any affine base, and `exists_blowup_comp` on any
   quasi-compact locally Noetherian scheme, together with their `U`-admissible corollaries.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.blowupCompHom`: the comparison morphism
  `J.blowup ⟶ (I * K₁).blowup` over `X` when `K₁.comap I.blowupToBase = E * J` for an effective
  Cartier divisor `E`.
* `AlgebraicGeometry.Scheme.IdealSheafData.blowupCompInv`: the inverse morphism
  `(I * K₁).blowup ⟶ J.blowup` lifting `I.blowupMulFst K₁`.
* `AlgebraicGeometry.Scheme.IdealSheafData.blowupCompIso`: the resulting isomorphism
  `J.blowup ≅ (I * K₁).blowup` over `X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_mul_of_comap_blowupToBase_eq`,
  `AlgebraicGeometry.Scheme.IdealSheafData.disjoint_support_mul_of_comap_blowupToBase_eq_iff`: when
  `K₁.comap b₁ = E * J`, the support of `I * K₁` is `V(I) ∪ b₁(V(E)) ∪ b₁(V(J))`, so `V(I * K₁)`
  is disjoint from `s` iff `V(I)` is disjoint from `s` and `V(E)`, `V(J)` are disjoint from
  `b₁⁻¹(s)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_mul_of_comap_blowupToBase_eq_pow_mul`,
  `Scheme.IdealSheafData.disjoint_support_mul_of_comap_blowupToBase_eq_pow_mul_iff`: when
  `K₁.comap b₁ = I.comap b₁ ^ d * J`, `b₁(V(I.comap b₁ ^ d)) ⊆ V(I)` and the support reduces
  to `V(I) ∪ b₁(V(J))`.
* `TauCeti.AlgebraicGeometry.exists_fg_ideal_comap_toSpecCoeff_eq`: over `Spec R`, for finitely
  generated `I` and finite-type `J`, every sufficiently large `d` admits a finitely generated ideal
  `K₀ ≤ R` pulling back to `I.comap π ^ d * J`.
* `TauCeti.AlgebraicGeometry.exists_comap_map_toSpecCoeff_eq`: for every sufficiently large `d`,
  pushing `I.comap π ^ d * J` forward along `π` and pulling back recovers `I.comap π ^ d * J`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_map_blowupToBase_eq`: the global schematic
  image identity `((I.comap b₁ ^ d * J).map b₁).comap b₁ = I.comap b₁ ^ d * J` on a quasi-compact
  scheme for finite-type `I` and `J`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp_of_compactSpace`,
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp_of_compactSpace_of_disjoint_support`:
  composition of two blowups along finite-type centres on a quasi-compact scheme is isomorphic over
  `X` to a proper blowup with support `V(I) ∪ b₁(V(J))` (and avoiding `U` when `I` and `J` do).
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp_of_isAffine`,
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp_of_isAffine_of_disjoint_support`: over
  an affine scheme (without Noetherianity), the composite centre can be chosen of finite type.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp`,
  `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp_of_disjoint_support`: on a
  quasi-compact locally Noetherian scheme, the composite of any two blowups is isomorphic over `X`
  to a single proper blowup with support `V(I) ∪ b₁(V(J))`
  (and avoiding `U` when `I` and `J` do).

## References

* [The Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B): composition of
  blowups along finite-type quasi-coherent sheaves of ideals on a quasi-compact scheme, and
  existence of a finite-type centre over an affine base.
* [The Stacks Project, Tag 0F3V](https://stacks.math.columbia.edu/tag/0F3V): composition of
  `U`-admissible blowups in the proof of Nagata compactification.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace reesAlgebra

universe u

/-! ### Universal-property comparison on an arbitrary scheme -/

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {I K₁ : X.IdealSheafData} {E J : I.blowup.IdealSheafData}

/-- When `K₁` pulls back on `Bl_I X` to `E * J` for an effective Cartier divisor `E`, the product
centre `I * K₁` pulls back along `b₂ ≫ b₁ : Bl_J (Bl_I X) ⟶ X` to an effective Cartier divisor. -/
theorem isEffectiveCartier_comap_mul_blowupToBase_comp_of_comap_eq
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    ((I * K₁).comap (J.blowupToBase ≫ I.blowupToBase)).IsEffectiveCartier := by
  rw [comap_mul, comap_comp, comap_comp, hK₁, comap_mul]
  exact TauCeti.isEffectiveCartier_mul
    (I.isEffectiveCartier_comap_blowupToBase.comap_blowupToBase J)
    (TauCeti.isEffectiveCartier_mul (hE.comap_blowupToBase J)
      J.isEffectiveCartier_comap_blowupToBase)

/-- When `K₁` pulls back on `Bl_I X` to `E * J`, the second centre `J` pulls back along
`I.blowupMulFst K₁ : Bl_{I * K₁} X ⟶ Bl_I X` to an effective Cartier divisor, by factor descent
from `K₁.comap (I * K₁).blowupToBase`. -/
theorem isEffectiveCartier_comap_blowupMulFst_of_comap_eq
    (hK₁ : K₁.comap I.blowupToBase = E * J) :
    (J.comap (I.blowupMulFst K₁)).IsEffectiveCartier := by
  have hK : (K₁.comap (I.blowupMulFst K₁ ≫ I.blowupToBase)).IsEffectiveCartier := by
    rw [blowupMulFst_blowupToBase]
    exact I.isEffectiveCartier_comap_blowupToBase_mul_right K₁
  rw [comap_comp, hK₁, comap_mul] at hK
  exact hK.of_mul_right

/-- **The forward comparison for a composite blowup.** When `K₁.comap I.blowupToBase = E * J` for
an effective Cartier divisor `E`, the composite blowup `J.blowupToBase ≫ I.blowupToBase` lifts to
`(I * K₁).blowup`. -/
def blowupCompHom (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    J.blowup ⟶ (I * K₁).blowup :=
  (I * K₁).blowupLift (J.blowupToBase ≫ I.blowupToBase)
    (isEffectiveCartier_comap_mul_blowupToBase_comp_of_comap_eq hE hK₁)

/-- **The inverse comparison for a composite blowup.** When `K₁.comap I.blowupToBase = E * J`, the
first-factor projection `I.blowupMulFst K₁ : (I * K₁).blowup ⟶ I.blowup` lifts to `J.blowup`. -/
def blowupCompInv (hK₁ : K₁.comap I.blowupToBase = E * J) :
    (I * K₁).blowup ⟶ J.blowup :=
  J.blowupLift (I.blowupMulFst K₁) (isEffectiveCartier_comap_blowupMulFst_of_comap_eq hK₁)

/-- `blowupCompHom` is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem blowupCompHom_blowupToBase
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    blowupCompHom hE hK₁ ≫ (I * K₁).blowupToBase = J.blowupToBase ≫ I.blowupToBase :=
  (I * K₁).blowupLift_blowupToBase _ _

/-- `blowupCompInv` lifts `I.blowupMulFst K₁` through `J.blowupToBase`. -/
@[reassoc (attr := simp)]
theorem blowupCompInv_blowupToBase
    (hK₁ : K₁.comap I.blowupToBase = E * J) :
    blowupCompInv hK₁ ≫ J.blowupToBase = I.blowupMulFst K₁ :=
  J.blowupLift_blowupToBase _ _

/-- Followed by `I.blowupMulFst K₁`, the forward comparison recovers `J.blowupToBase`. -/
@[reassoc (attr := simp)]
theorem blowupCompHom_blowupMulFst
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    blowupCompHom hE hK₁ ≫ I.blowupMulFst K₁ = J.blowupToBase := by
  apply I.blowup_hom_ext
  · rw [Category.assoc, blowupMulFst_blowupToBase, blowupCompHom_blowupToBase]
  · rw [Category.assoc, blowupMulFst_blowupToBase, blowupCompHom_blowupToBase, comap_comp]
    exact I.isEffectiveCartier_comap_blowupToBase.comap_blowupToBase J

/-- `blowupCompHom` and `blowupCompInv` compose to the identity on `J.blowup`. -/
@[reassoc (attr := simp)]
theorem blowupCompHom_blowupCompInv
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    blowupCompHom hE hK₁ ≫ blowupCompInv hK₁ = 𝟙 J.blowup := by
  apply J.blowup_hom_ext
  · rw [Category.assoc, blowupCompInv_blowupToBase, blowupCompHom_blowupMulFst, Category.id_comp]
  · rw [Category.assoc, blowupCompInv_blowupToBase, blowupCompHom_blowupMulFst]
    exact J.isEffectiveCartier_comap_blowupToBase

/-- `blowupCompInv` and `blowupCompHom` compose to the identity on `(I * K₁).blowup`. -/
@[reassoc (attr := simp)]
theorem blowupCompInv_blowupCompHom
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    blowupCompInv hK₁ ≫ blowupCompHom hE hK₁ = 𝟙 (I * K₁).blowup := by
  apply (I * K₁).blowup_hom_ext
  · rw [Category.assoc, blowupCompHom_blowupToBase, blowupCompInv_blowupToBase_assoc,
      blowupMulFst_blowupToBase, Category.id_comp]
  · rw [Category.assoc, blowupCompHom_blowupToBase, blowupCompInv_blowupToBase_assoc,
      blowupMulFst_blowupToBase]
    exact (I * K₁).isEffectiveCartier_comap_blowupToBase

/-- **Isomorphism of a composite blowup with a single blowup.** On any scheme `X`, if
`K₁.comap I.blowupToBase = E * J` for an effective Cartier divisor `E`, then the iterated blowup
`J.blowup` is canonically isomorphic over `X` to `(I * K₁).blowup`. -/
def blowupCompIso (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    J.blowup ≅ (I * K₁).blowup where
  hom := blowupCompHom hE hK₁
  inv := blowupCompInv hK₁
  hom_inv_id := blowupCompHom_blowupCompInv hE hK₁
  inv_hom_id := blowupCompInv_blowupCompHom hE hK₁

/-- The forward direction of `blowupCompIso` is `blowupCompHom`. -/
@[simp]
theorem blowupCompIso_hom
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    (blowupCompIso hE hK₁).hom = blowupCompHom hE hK₁ :=
  (rfl)

/-- The inverse direction of `blowupCompIso` is `blowupCompInv`. -/
@[simp]
theorem blowupCompIso_inv
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    (blowupCompIso hE hK₁).inv = blowupCompInv hK₁ :=
  (rfl)

/-- The forward composite-blowup comparison is an isomorphism. -/
instance isIso_blowupCompHom
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    IsIso (blowupCompHom hE hK₁) :=
  ⟨blowupCompInv hK₁, blowupCompHom_blowupCompInv hE hK₁, blowupCompInv_blowupCompHom hE hK₁⟩

/-- The inverse composite-blowup comparison is an isomorphism when `E` is effective Cartier. -/
theorem isIso_blowupCompInv
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    IsIso (blowupCompInv hK₁) :=
  ⟨blowupCompHom hE hK₁, blowupCompInv_blowupCompHom hE hK₁, blowupCompHom_blowupCompInv hE hK₁⟩

/-- The categorical inverse of `blowupCompHom` is `blowupCompInv`. -/
@[simp]
theorem inv_blowupCompHom
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J) :
    inv (blowupCompHom hE hK₁) = blowupCompInv hK₁ :=
  (IsIso.eq_inv_of_hom_inv_id (blowupCompHom_blowupCompInv hE hK₁)).symm

/-- The categorical inverse of `blowupCompInv` is `blowupCompHom`. -/
@[simp]
theorem inv_blowupCompInv
    (hE : E.IsEffectiveCartier) (hK₁ : K₁.comap I.blowupToBase = E * J)
    [IsIso (blowupCompInv hK₁)] :
    inv (blowupCompInv hK₁) = blowupCompHom hE hK₁ :=
  (IsIso.eq_inv_of_hom_inv_id (blowupCompInv_blowupCompHom hE hK₁)).symm

/-- When `K₁.comap b₁ = E * J`, the support of the product centre `I * K₁` is the union of `V(I)`,
`b₁(V(E))`, and `b₁(V(J))`: away from `V(I)`, the first blowup `b₁` is an isomorphism, so every
point of `V(K₁) \ V(I)` lifts to a point of `V(E) ∪ V(J)`. -/
theorem coe_support_mul_of_comap_blowupToBase_eq
    (hK₁ : K₁.comap I.blowupToBase = E * J) :
    ((I * K₁).support : Set X) =
      (I.support : Set X) ∪ I.blowupToBase '' (E.support : Set I.blowup) ∪
        I.blowupToBase '' (J.support : Set I.blowup) := by
  rw [support_mul, Closeds.coe_sup]
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rcases hx with hxI | hxK₁
    · exact Or.inl (Or.inl hxI)
    · by_cases hxI : x ∈ (I.support : Set X)
      · exact Or.inl (Or.inl hxI)
      · have hxU : x ∈ I.support.compl := by simpa [Closeds.compl] using hxI
        obtain ⟨z, hz⟩ := (I.blowupToBase ∣_ I.support.compl).surjective ⟨x, hxU⟩
        have hz' : I.blowupToBase z.val = x :=
          (morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)
        have hzK : z.val ∈ ((K₁.comap I.blowupToBase).support : Set I.blowup) := by
          rw [support_comap, Closeds.coe_preimage, Set.mem_preimage, hz']
          exact hxK₁
        rw [hK₁, support_mul, Closeds.coe_sup] at hzK
        rcases hzK with hzE | hzJ
        · exact Or.inl (Or.inr ⟨z.val, hzE, hz'⟩)
        · exact Or.inr ⟨z.val, hzJ, hz'⟩
  · rcases hx with (hxI | ⟨z, hzE, rfl⟩) | ⟨z, hzJ, rfl⟩
    · exact Or.inl hxI
    all_goals
      have hzK : z ∈ ((K₁.comap I.blowupToBase).support : Set I.blowup) := by
        rw [hK₁, support_mul, Closeds.coe_sup]
        first | exact Or.inl hzE | exact Or.inr hzJ
      rw [support_comap, Closeds.coe_preimage, Set.mem_preimage] at hzK
      exact Or.inr hzK

/-- For any `s : Set X` and `K₁` satisfying `K₁.comap b₁ = E * J`, the product centre `V(I * K₁)`
is disjoint from `s` if and only if `V(I)` is disjoint from `s` and both `V(E)` and `V(J)` are
disjoint from `b₁⁻¹(s)`. -/
theorem disjoint_support_mul_of_comap_blowupToBase_eq_iff {s : Set X}
    (hK₁ : K₁.comap I.blowupToBase = E * J) :
    Disjoint s ((I * K₁).support : Set X) ↔
      Disjoint s (I.support : Set X) ∧
        Disjoint (I.blowupToBase ⁻¹' s) (E.support : Set I.blowup) ∧
        Disjoint (I.blowupToBase ⁻¹' s) (J.support : Set I.blowup) := by
  rw [coe_support_mul_of_comap_blowupToBase_eq hK₁, Set.disjoint_union_right,
    Set.disjoint_union_right, Set.disjoint_image_right, Set.disjoint_image_right, and_assoc]

/-- When `K₁.comap b₁ = I.comap b₁ ^ d * J`, the support of the product centre `I * K₁` simplifies
to `V(I) ∪ b₁(V(J))` because `b₁(V(I.comap b₁ ^ d)) ⊆ V(I)`. -/
theorem coe_support_mul_of_comap_blowupToBase_eq_pow_mul {d : ℕ}
    (hK₁ : K₁.comap I.blowupToBase = I.comap I.blowupToBase ^ d * J) :
    ((I * K₁).support : Set X) =
      (I.support : Set X) ∪ I.blowupToBase '' (J.support : Set I.blowup) := by
  have hsub :
      I.blowupToBase '' ((I.comap I.blowupToBase ^ d).support : Set I.blowup) ⊆
        (I.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    cases d with
    | zero =>
      simp only [pow_zero, one_eq_top, support_top, Closeds.coe_bot, Set.mem_empty_iff_false] at hz
    | succ n =>
      rwa [support_pow_succ, support_comap, Closeds.coe_preimage, Set.mem_preimage] at hz
  rw [coe_support_mul_of_comap_blowupToBase_eq hK₁, Set.union_eq_self_of_subset_right hsub]

/-- For any `s : Set X` and `K₁` satisfying `K₁.comap b₁ = I.comap b₁ ^ d * J`, the product centre
`V(I * K₁)` is disjoint from `s` if and only if `V(I)` is disjoint from `s` and `V(J)` is disjoint
from `b₁⁻¹(s)`. -/
theorem disjoint_support_mul_of_comap_blowupToBase_eq_pow_mul_iff {s : Set X} {d : ℕ}
    (hK₁ : K₁.comap I.blowupToBase = I.comap I.blowupToBase ^ d * J) :
    Disjoint s ((I * K₁).support : Set X) ↔
      Disjoint s (I.support : Set X) ∧
        Disjoint (I.blowupToBase ⁻¹' s) (J.support : Set I.blowup) := by
  rw [coe_support_mul_of_comap_blowupToBase_eq_pow_mul hK₁, Set.disjoint_union_right,
    Set.disjoint_image_right]

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Clearing denominators across the affine charts of `Proj R[It]` -/

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.IdealSheafData

section AffineBlowupCharts

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- The ideal of the affine blowup algebra `R[I/a]` corresponding to the restriction of an ideal
sheaf `J` on `Proj R[It]` to the chart `Spec R[I/a]`. -/
private def chartIdeal {a : R} (ha : a ∈ I) (J : (Proj (grade I)).IdealSheafData) :
    Ideal (I.affineBlowup a (Localization.Away a)) :=
  (equivOfIsAffine (J.comap (affineBlowupι (Localization.Away a) ha))).map
    (Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).hom.hom

/-- If `J` is of finite type on `Proj R[It]`, its ideal on each affine blowup chart `R[I/a]` is
finitely generated. -/
private theorem chartIdeal_fg {a : R} (ha : a ∈ I) (J : (Proj (grade I)).IdealSheafData)
    (hJ : ∀ W : (Proj (grade I)).affineOpens, (J.ideal W).FG) :
    (chartIdeal ha J).FG := by
  rw [chartIdeal, equivOfIsAffine_apply]
  have : LocallyOfFinitePresentation J.subschemeι :=
    (locallyOfFinitePresentation_subschemeι_iff J).mpr hJ
  exact Ideal.FG.map ((J.comap _).fg_ideal ⟨⊤, isAffineOpen_top _⟩) _

/-- On the chart `Spec R[I/a]`, the ideal sheaf `I.comap π ^ d * J` is generated by
`a ^ d * chartIdeal ha J`. -/
private theorem comap_affineBlowupι_pow_mul_eq {a : R} (ha : a ∈ I)
    (J : (Proj (grade I)).IdealSheafData) (d : ℕ) :
    (((ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
        (Proj.toSpecCoeff (grade I)) ^ d * J).comap (affineBlowupι (Localization.Away a) ha)) =
      ofIdealTop ((Ideal.span {algebraMap R _ a ^ d} * chartIdeal ha J).map
        (Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).inv.hom) := by
  set B := CommRingCat.of (I.affineBlowup a (Localization.Away a))
  have hJ : J.comap (affineBlowupι (Localization.Away a) ha) =
      ofIdealTop ((chartIdeal ha J).map (Scheme.ΓSpecIso B).inv.hom) := by
    rw [chartIdeal, Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      Ideal.map_id, ← equivOfIsAffine_symm_apply, equivOfIsAffine.symm_apply_apply]
  have hI : ((ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
      (Proj.toSpecCoeff (grade I))).comap (affineBlowupι (Localization.Away a) ha) =
      ofIdealTop ((Ideal.span {algebraMap R B a}).map (Scheme.ΓSpecIso B).inv.hom) := by
    rw [← comap_comp, toSpecCoeff_reesAlgebra, comap_affineBlowupι_eq_ofIdealTop,
      Ideal.map_span, Set.image_singleton]
  rw [comap_mul, comap_pow, hI, hJ, ← ofIdealTop_pow, ← ofIdealTop_mul, ← Ideal.map_pow,
    ← Ideal.map_mul, Ideal.span_singleton_pow]

/-- Clearing denominators for a finitely generated chart ideal `chartIdeal ha J` in `R[I/a]`: there
exist a single exponent `m` and finitely many elements `c l ∈ R` that land in
`a ^ m * chartIdeal ha J` and whose `a ^ (d - m)`-multiples generate `a ^ d * chartIdeal ha J` for
every `d ≥ m`. -/
private theorem exists_fin_clear_chartIdeal {a : R} (ha : a ∈ I)
    (J : (Proj (grade I)).IdealSheafData) (hJ : (chartIdeal ha J).FG) :
    ∃ (n m : ℕ) (c : Fin n → R),
      (∀ l, algebraMap R (I.affineBlowup a (Localization.Away a)) (c l) ∈
        Ideal.span {algebraMap R _ a ^ m} * chartIdeal ha J) ∧
      ∀ d : ℕ, m ≤ d →
        Ideal.span {algebraMap R _ a ^ d} * chartIdeal ha J ≤
          Ideal.span (Set.range fun l ↦ algebraMap R _ (a ^ (d - m) * c l)) := by
  let B := I.affineBlowup a (Localization.Away a)
  obtain ⟨n, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  have hmem (l : Fin n) :
      ∃ k : ℕ, ∃ y ∈ I ^ k, algebraMap R B a ^ k * z l = algebraMap R B y := by
    obtain ⟨k, y, hy, hky⟩ := (Ideal.mem_affineBlowup_iff ha).mp (z l).property
    exact ⟨k, y, hy, Subtype.ext hky⟩
  choose k y _ hky using hmem
  let m := Finset.univ.sup k
  let c : Fin n → R := fun l ↦ a ^ (m - k l) * y l
  have hc_eq (l : Fin n) : algebraMap R B (c l) = algebraMap R B a ^ m * z l := by
    have hkl : k l ≤ m := Finset.le_sup (Finset.mem_univ l)
    rw [map_mul, map_pow, ← hky l, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hkl]
  refine ⟨n, m, c, fun l ↦ ?_, fun d hd ↦ ?_⟩
  · rw [hc_eq l]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
      (hz ▸ Ideal.subset_span ⟨l, rfl⟩)
  · rw [← hz, Ideal.span_mul_span, Ideal.span_le]
    rintro _ ⟨_, rfl, _, ⟨l, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨l, ?_⟩
    dsimp only
    rw [map_mul, map_pow, hc_eq l, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hd]

/-- On `B_b = R[I/b]`, if `(a / b) ^ k` multiplies `c` into `b ^ m * J_b`, then `a ^ (d - m) * c`
lands in `b ^ d * J_b` for every `d ≥ m + k`. -/
private theorem algebraMap_pow_sub_mul_mem_of_divBy_pow_mul_mem {a b : R} (ha : a ∈ I)
    {J_b : Ideal (I.affineBlowup b (Localization.Away b))} {m k : ℕ} {c : R}
    (hk : (⟨TauCeti.Localization.divBy a b, Ideal.divBy_mem_affineBlowup ha⟩ :
        I.affineBlowup b (Localization.Away b)) ^ k *
      algebraMap R _ c ∈ Ideal.span {algebraMap R _ b ^ m} * J_b)
    {d : ℕ} (hd : m + k ≤ d) :
    algebraMap R (I.affineBlowup b (Localization.Away b)) (a ^ (d - m) * c) ∈
      Ideal.span {algebraMap R _ b ^ d} * J_b := by
  let g : I.affineBlowup b (Localization.Away b) :=
    ⟨TauCeti.Localization.divBy a b, Ideal.divBy_mem_affineBlowup ha⟩
  have hbg : algebraMap R (I.affineBlowup b (Localization.Away b)) b * g =
      algebraMap R _ a := by
    ext
    simp [g]
  have hkc : algebraMap R (I.affineBlowup b (Localization.Away b)) (a ^ k * c) ∈
      Ideal.span {algebraMap R _ b ^ (m + k)} * J_b := by
    have hmul : algebraMap R (I.affineBlowup b (Localization.Away b)) (a ^ k * c) =
        algebraMap R _ b ^ k * (g ^ k * algebraMap R _ c) := by
      rw [map_mul, map_pow, ← hbg, mul_pow, mul_assoc]
    rw [hmul, add_comm m k, pow_add, ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hk
  have har : algebraMap R (I.affineBlowup b (Localization.Away b)) (a ^ (d - (m + k))) ∈
      Ideal.span {algebraMap R _ b ^ (d - (m + k))} := by
    rw [← Ideal.span_singleton_pow, map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton.mpr ⟨g, hbg.symm⟩) _
  have hprod := Ideal.mul_mem_mul har hkc
  rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← pow_add,
    Nat.sub_add_cancel hd] at hprod
  have hexp : a ^ (d - (m + k)) * (a ^ k * c) = a ^ (d - m) * c := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rwa [← map_mul, hexp] at hprod

/-- Overlap step between two charts `Spec R[I/a]` and `Spec R[I/b]`: if `c ∈ R` maps into
`a ^ m * chartIdeal ha J` on the `a`-chart, then some `k : ℕ` makes `a ^ (d - m) * c` map into
`b ^ d * chartIdeal hb J` on the `b`-chart for every `d ≥ m + k`. -/
private theorem exists_pow_mul_mem_chartIdeal_other {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (J : (Proj (grade I)).IdealSheafData) {m : ℕ} {c : R}
    (hc : algebraMap R (I.affineBlowup a (Localization.Away a)) c ∈
      Ideal.span {algebraMap R _ a ^ m} * chartIdeal ha J) :
    ∃ k : ℕ, ∀ d : ℕ, m + k ≤ d →
      algebraMap R (I.affineBlowup b (Localization.Away b)) (a ^ (d - m) * c) ∈
        Ideal.span {algebraMap R _ b ^ d} * chartIdeal hb J := by
  let ιa := affineBlowupι (Localization.Away a) ha
  let ιb := affineBlowupι (Localization.Away b) hb
  let Bb := CommRingCat.of (I.affineBlowup b (Localization.Away b))
  let g : Bb := ⟨TauCeti.Localization.divBy a b, Ideal.divBy_mem_affineBlowup ha⟩
  let U : (Spec Bb).Opens := PrimeSpectrum.basicOpen g
  set Lc := (ofIdealTop ((Ideal.span {c}).map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
    (Proj.toSpecCoeff (grade I))
  set M := (ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
    (Proj.toSpecCoeff (grade I)) ^ m * J
  have hLc {x : R} (hx : x ∈ I) :
      Lc.comap (affineBlowupι (Localization.Away x) hx) =
        ofIdealTop ((Ideal.span {algebraMap R (I.affineBlowup x (Localization.Away x)) c}).map
          (Scheme.ΓSpecIso (.of _)).inv.hom) := by
    rw [← comap_comp, toSpecCoeff_reesAlgebra, comap_affineBlowupι_ofIdealTop_map, Ideal.map_span,
      Set.image_singleton]
  have hle_a : Lc.comap ιa ≤ M.comap ιa := by
    rw [hLc ha, comap_affineBlowupι_pow_mul_eq ha J m, ← equivOfIsAffine_symm_apply,
      ← equivOfIsAffine_symm_apply, map_le_map_iff]
    exact Ideal.map_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hc))
  have hrange : Set.range (U.ι ≫ ιb) ⊆ Set.range ιa := by
    have hbasic : U = ιb ⁻¹ᵁ ιa.opensRange :=
      (affineBlowupι_preimage_basicOpen (Localization.Away b) hb ha).symm.trans
        (congrArg (ιb ⁻¹ᵁ ·) (opensRange_affineBlowupι (Localization.Away a) ha).symm)
    rintro _ ⟨y, rfl⟩
    have hy : y.val ∈ ιb ⁻¹ᵁ ιa.opensRange := hbasic ▸ y.property
    have hι : U.ι y = y.val := Scheme.Opens.ι_apply U ⟨y.val, y.property⟩
    rw [Scheme.Hom.comp_apply, hι, ← Scheme.Hom.coe_opensRange]
    exact (Scheme.Hom.mem_preimage _).mp hy
  have hle_b : (Lc.comap ιb).comap U.ι ≤ (M.comap ιb).comap U.ι := by
    let u := IsOpenImmersion.lift ιa (U.ι ≫ ιb) hrange
    have hfac : u ≫ ιa = U.ι ≫ ιb := IsOpenImmersion.lift_fac _ _ hrange
    have hle_u : (Lc.comap ιa).comap u ≤ (M.comap ιa).comap u := comap_mono u hle_a
    simpa only [← comap_comp, hfac] using hle_u
  rw [hLc hb, comap_affineBlowupι_pow_mul_eq hb J m] at hle_b
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_of_comap_basicOpen_le g hle_b
    (Ideal.mem_span_singleton_self _)
  exact ⟨k, fun d hd ↦ algebraMap_pow_sub_mul_mem_of_divBy_pow_mul_mem ha hk hd⟩

/-- **Clearing denominators on `Proj R[It]`.** Let `I` be a finitely generated ideal of `R` and let
`J` be an ideal sheaf of finite type on `Proj R[It]`. Then for every sufficiently large `d : ℕ`
there exists a finitely generated ideal `K₀` of `R` whose pullback along
`π = Proj.toSpecCoeff (grade I)` equals `I.comap π ^ d * J`. -/
theorem exists_fg_ideal_comap_toSpecCoeff_eq (hI : I.FG)
    (J : (Proj (grade I)).IdealSheafData)
    (hJ : ∀ W : (Proj (grade I)).affineOpens, (J.ideal W).FG) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ K₀ : Ideal R, K₀.FG ∧
      (ofIdealTop (K₀.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
        (Proj.toSpecCoeff (grade I)) =
      (ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
        (Proj.toSpecCoeff (grade I)) ^ d * J := by
  obtain ⟨r, a, haI⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have ha (i : Fin r) : a i ∈ I := haI ▸ Ideal.subset_span ⟨i, rfl⟩
  choose n m c hc_mem hc_le using fun i : Fin r ↦
    exists_fin_clear_chartIdeal (ha i) J (chartIdeal_fg (ha i) J hJ)
  choose k hk using fun (i : Fin r) (l : Fin (n i)) (j : Fin r) ↦
    exists_pow_mul_mem_chartIdeal_other (ha i) (ha j) J (hc_mem i l)
  let N : ℕ := Finset.univ.sup m ⊔
    Finset.univ.sup (fun p : (Σ i : Fin r, Fin (n i)) × Fin r ↦
      m p.fst.fst + k p.fst.fst p.fst.snd p.snd)
  refine ⟨N, fun d hd ↦ ?_⟩
  let gen : (Σ i : Fin r, Fin (n i)) → R := fun p ↦ a p.fst ^ (d - m p.fst) * c p.fst p.snd
  let K₀ : Ideal R := Ideal.span (Set.range gen)
  refine ⟨K₀, Submodule.fg_span (Set.finite_range gen), ?_⟩
  refine ext_of_comap_iSup_opensRange_eq_top
    (fun j : Fin r ↦ affineBlowupι (Localization.Away (a j)) (ha j))
    (iSup_opensRange_affineBlowupι haI) fun j ↦ ?_
  rw [comap_affineBlowupι_pow_mul_eq (ha j) J d, ← comap_comp, toSpecCoeff_reesAlgebra,
    comap_affineBlowupι_ofIdealTop_map]
  congr 2
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_span, Ideal.span_le, Set.image_subset_iff]
    rintro _ ⟨⟨i, l⟩, rfl⟩
    exact hk i l j d (((Finset.le_sup (f := fun p : (Σ i : Fin r, Fin (n i)) × Fin r ↦
      m p.fst.fst + k p.fst.fst p.fst.snd p.snd) (Finset.mem_univ (⟨i, l⟩, j))).trans
      le_sup_right).trans hd)
  · refine (hc_le j d ((Finset.le_sup (Finset.mem_univ j)).trans (le_sup_left.trans hd))).trans ?_
    rw [Ideal.map_span]
    refine Ideal.span_mono ?_
    rintro _ ⟨l, rfl⟩
    exact ⟨gen ⟨j, l⟩, ⟨⟨j, l⟩, rfl⟩, rfl⟩

/-- **Schematic image recovery on `Proj R[It]`.** For finitely generated `I ≤ R` and finite-type
`J` on `Proj R[It]`, every sufficiently large `d : ℕ` satisfies
`((I.comap π ^ d * J).map π).comap π = I.comap π ^ d * J`. -/
theorem exists_comap_map_toSpecCoeff_eq (hI : I.FG)
    (J : (Proj (grade I)).IdealSheafData)
    (hJ : ∀ W : (Proj (grade I)).affineOpens, (J.ideal W).FG) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      (((ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
          (Proj.toSpecCoeff (grade I)) ^ d * J).map
        (Proj.toSpecCoeff (grade I))).comap (Proj.toSpecCoeff (grade I)) =
      (ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
        (Proj.toSpecCoeff (grade I)) ^ d * J := by
  obtain ⟨N, hN⟩ := exists_fg_ideal_comap_toSpecCoeff_eq hI J hJ
  refine ⟨N, fun d hd ↦ ?_⟩
  obtain ⟨K₀, -, hK₀⟩ := hN d hd
  rw [← hK₀]
  exact (map_gc _).l_u_l_eq_l _

end AffineBlowupCharts

end TauCeti.AlgebraicGeometry

/-! ### Global composition of blowups on quasi-compact, affine, and locally Noetherian schemes -/

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Over an affine open `V ⊆ X`, if `I(V)` is finitely generated and `J` is of finite type on
`Bl_I X`, every sufficiently large `d : ℕ` admits a finitely generated `K₀ ≤ Γ(X, V)` pulling
back on `I.blowupChart hV` to `(I.comap b₁ ^ d * J).comap (I.blowupChart hV)`. -/
private theorem exists_fg_ideal_comap_blowupChart_eq (I : X.IdealSheafData)
    {V : X.Opens} (hV : IsAffineOpen V) (hIV : (I.ideal ⟨V, hV⟩).FG)
    (J : I.blowup.IdealSheafData) (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ K₀ : Ideal Γ(X, V), K₀.FG ∧
      (ofIdealTop (K₀.map (Scheme.ΓSpecIso Γ(X, V)).inv.hom)).comap
          (Proj.toSpecCoeff (grade (I.ideal ⟨V, hV⟩))) =
        (I.comap I.blowupToBase ^ d * J).comap (I.blowupChart hV) := by
  have : LocallyOfFinitePresentation J.subschemeι :=
    (locallyOfFinitePresentation_subschemeι_iff J).mpr hJ
  obtain ⟨N, hN⟩ := exists_fg_ideal_comap_toSpecCoeff_eq hIV (J.comap (I.blowupChart hV))
    ((J.comap (I.blowupChart hV)).fg_ideal)
  refine ⟨N, fun d hd ↦ ?_⟩
  obtain ⟨K₀, hK₀fg, hK₀⟩ := hN d hd
  refine ⟨K₀, hK₀fg, ?_⟩
  rw [comap_mul, comap_pow, I.comap_blowupChart_comap_blowupToBase hV]
  -- `CommRingCat.of Γ(X, V) = Γ(X, V)` (`CommRingCat.of_carrier`); reducible transparency avoids
  -- unfolding `IdealSheafData` during unification.
  dsimp only [CommRingCat.of_carrier] at hK₀
  with_reducible exact hK₀

/-- Over a single affine open `V ⊆ X`, pushing `I.comap b₁ ^ d * J` forward along a quasi-compact
blowup `b₁ = I.blowupToBase` and pulling back agrees on `I.blowupChart hV` for all sufficiently
large `d`. -/
private theorem exists_comap_map_blowupToBase_comap_blowupChart_eq (I : X.IdealSheafData)
    [QuasiCompact I.blowupToBase] {V : X.Opens} (hV : IsAffineOpen V) (hIV : (I.ideal ⟨V, hV⟩).FG)
    (J : I.blowup.IdealSheafData) (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      (((I.comap I.blowupToBase ^ d * J).map I.blowupToBase).comap I.blowupToBase).comap
          (I.blowupChart hV) =
        (I.comap I.blowupToBase ^ d * J).comap (I.blowupChart hV) := by
  obtain ⟨N, hN⟩ := exists_fg_ideal_comap_blowupChart_eq I hV hIV J hJ
  refine ⟨N, fun d hd ↦ ?_⟩
  obtain ⟨K₀, -, hK₀⟩ := hN d hd
  set M := I.comap I.blowupToBase ^ d * J
  rw [← comap_comp, blowupChart_blowupToBase, comap_comp,
    M.comap_map_of_isPullback_of_flat hV.fromSpec (I.isPullback_blowupChart_fromSpec hV), ← hK₀]
  exact (map_gc _).l_u_l_eq_l _

/-- **Global schematic image identity for blowups.** On a quasi-compact scheme `X`, let `I` be an
ideal sheaf of finite type on `X` and `J` an ideal sheaf of finite type on `Bl_I X`. Then for
every sufficiently large `d : ℕ`, pushing `I.comap b₁ ^ d * J` forward along `b₁ = I.blowupToBase`
and pulling back recovers `I.comap b₁ ^ d * J`. -/
theorem exists_comap_map_blowupToBase_eq [CompactSpace X] (I : X.IdealSheafData)
    (hI : ∀ V : X.affineOpens, (I.ideal V).FG) (J : I.blowup.IdealSheafData)
    (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ((I.comap I.blowupToBase ^ d * J).map I.blowupToBase).comap I.blowupToBase =
        I.comap I.blowupToBase ^ d * J := by
  have := I.isProper_blowupToBase hI
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.val : Set X)) (fun V ↦ V.val.isOpen) (by
      rw [← Opens.coe_top, ← iSup_affineOpens_eq_top X, Opens.coe_iSup])
  -- `X.affineOpens` is `{U : X.Opens | IsAffineOpen U}`, so
  -- `V.val.property : IsAffineOpen V.val.val`.
  have hV (V : s) : IsAffineOpen V.val.val := V.val.property
  choose N hN using fun V : s ↦
    exists_comap_map_blowupToBase_comap_blowupChart_eq I (hV V) (hI V.val) J hJ
  refine ⟨Finset.univ.sup N, fun d hd ↦ ?_⟩
  have hcover : ⨆ V : s, (I.blowupChart (hV V)).opensRange = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨V, hVs, hyV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (I.blowupToBase y)))
    refine Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, ?_⟩
    rw [opensRange_blowupChart]
    exact hyV
  exact ext_of_comap_iSup_opensRange_eq_top (fun V : s ↦ I.blowupChart (hV V)) hcover fun V ↦
    hN V d ((Finset.le_sup (Finset.mem_univ V)).trans hd)

/-- **Composition of blowups on a quasi-compact scheme.** Let `X` be a quasi-compact scheme, `I` a
finite-type ideal sheaf on `X`, and `J` a finite-type ideal sheaf on `Bl_I X`. Then there exist an
ideal sheaf `K` on `X` and an isomorphism `J.blowup ≅ K.blowup` over `X` such that
`K.blowupToBase` is proper and `V(K) = V(I) ∪ b₁(V(J))`. -/
theorem exists_blowup_comp_of_compactSpace [CompactSpace X] (I : X.IdealSheafData)
    (hI : ∀ V : X.affineOpens, (I.ideal V).FG) (J : I.blowup.IdealSheafData)
    (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG) :
    ∃ (K : X.IdealSheafData) (e : J.blowup ≅ K.blowup),
      IsProper K.blowupToBase ∧
        (K.support : Set X) =
          (I.support : Set X) ∪ I.blowupToBase '' (J.support : Set I.blowup) ∧
        e.hom ≫ K.blowupToBase = J.blowupToBase ≫ I.blowupToBase := by
  have := I.isProper_blowupToBase hI
  have := J.isProper_blowupToBase hJ
  obtain ⟨N, hN⟩ := I.exists_comap_map_blowupToBase_eq hI J hJ
  set K₁ := (I.comap I.blowupToBase ^ N * J).map I.blowupToBase
  have hK₁ : K₁.comap I.blowupToBase = I.comap I.blowupToBase ^ N * J := hN N le_rfl
  have hE : (I.comap I.blowupToBase ^ N).IsEffectiveCartier :=
    TauCeti.isEffectiveCartier_pow I.isEffectiveCartier_comap_blowupToBase N
  have hproper : IsProper (I * K₁).blowupToBase := by
    rw [(blowupCompIso hE hK₁).eq_inv_comp.mpr (blowupCompHom_blowupToBase hE hK₁)]
    infer_instance
  exact ⟨I * K₁, blowupCompIso hE hK₁, hproper,
    coe_support_mul_of_comap_blowupToBase_eq_pow_mul hK₁, blowupCompHom_blowupToBase hE hK₁⟩

/-- If `V(K) = V(I) ∪ b₁(V(J))` while `V(I)` avoids `U` and `V(J)` avoids `b₁⁻¹(U)`, then `V(K)`
also avoids `U`, so `K.blowupToBase` restricts to an isomorphism over `U`. -/
private theorem disjoint_support_and_isIso_blowupToBase_restrict {I K : X.IdealSheafData}
    {J : I.blowup.IdealSheafData} {U : X.Opens}
    (hsupp : (K.support : Set X) =
      (I.support : Set X) ∪ I.blowupToBase '' (J.support : Set I.blowup))
    (hIU : Disjoint (U : Set X) (I.support : Set X))
    (hJU : Disjoint (I.blowupToBase ⁻¹' (U : Set X)) (J.support : Set I.blowup)) :
    Disjoint (U : Set X) (K.support : Set X) ∧ IsIso (K.blowupToBase ∣_ U) := by
  have hdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [hsupp, Set.disjoint_union_right, Set.disjoint_image_right]
    exact ⟨hIU, hJU⟩
  exact ⟨hdisj, K.isIso_blowupToBase_restrict_of_disjoint_support hdisj⟩

/-- **Composition of admissible blowups on a quasi-compact scheme.** Corollary of
`exists_blowup_comp_of_compactSpace` when `V(I)` avoids an open `U ⊆ X` and `V(J)` avoids
`b₁⁻¹(U)`. -/
theorem exists_blowup_comp_of_compactSpace_of_disjoint_support [CompactSpace X]
    (I : X.IdealSheafData) (hI : ∀ V : X.affineOpens, (I.ideal V).FG)
    (J : I.blowup.IdealSheafData) (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG)
    (U : X.Opens) (hIU : Disjoint (U : Set X) (I.support : Set X))
    (hJU : Disjoint (I.blowupToBase ⁻¹' (U : Set X)) (J.support : Set I.blowup)) :
    ∃ (K : X.IdealSheafData) (e : J.blowup ≅ K.blowup),
      IsProper K.blowupToBase ∧ Disjoint (U : Set X) (K.support : Set X) ∧
        IsIso (K.blowupToBase ∣_ U) ∧
        e.hom ≫ K.blowupToBase = J.blowupToBase ≫ I.blowupToBase := by
  obtain ⟨K, e, hproper, hsupp, he⟩ := exists_blowup_comp_of_compactSpace I hI J hJ
  obtain ⟨hdisj, hiso⟩ := disjoint_support_and_isIso_blowupToBase_restrict hsupp hIU hJU
  exact ⟨K, e, hproper, hdisj, hiso, he⟩

/-- **Composition of finite-type blowups over an affine scheme.** When `X` is affine (with no
Noetherian assumption), the composite of two blowups along finite-type centres is isomorphic over
`X` to the blowup along a *finite-type* centre `K` (and hence with proper blowup morphism) having
exact support `V(I) ∪ b₁(V(J))`. -/
theorem exists_blowup_comp_of_isAffine [IsAffine X] (I : X.IdealSheafData)
    (hI : (I.ideal ⟨⊤, isAffineOpen_top X⟩).FG) (J : I.blowup.IdealSheafData)
    (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG) :
    ∃ (K : X.IdealSheafData) (e : J.blowup ≅ K.blowup),
      (∀ V : X.affineOpens, (K.ideal V).FG) ∧ IsProper K.blowupToBase ∧
        (K.support : Set X) =
          (I.support : Set X) ∪ I.blowupToBase '' (J.support : Set I.blowup) ∧
        e.hom ≫ K.blowupToBase = J.blowupToBase ≫ I.blowupToBase := by
  have : IsIso (I.blowupChart (isAffineOpen_top X)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [opensRange_blowupChart, Scheme.Hom.preimage_top]
  obtain ⟨N, hN⟩ :=
    exists_fg_ideal_comap_blowupChart_eq I (isAffineOpen_top X) hI J hJ
  obtain ⟨K₀, hK₀fg, hK₀⟩ := hN N le_rfl
  let K₁ : X.IdealSheafData := ofIdealTop K₀
  have hLHS :
      (K₁.comap I.blowupToBase).comap (I.blowupChart (isAffineOpen_top X)) =
        (ofIdealTop (K₀.map (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv.hom)).comap
          (Proj.toSpecCoeff (grade (I.ideal ⟨⊤, isAffineOpen_top X⟩))) := by
    rw [← comap_comp, blowupChart_blowupToBase, comap_comp, comap_fromSpec_eq_ofIdealTop]
    have htop : K₁.ideal ⟨⊤, isAffineOpen_top X⟩ = K₀ := by
      simpa only [K₁, ← equivOfIsAffine_apply, ← equivOfIsAffine_symm_apply] using
        equivOfIsAffine.apply_symm_apply K₀
    rw [htop]
  have hK₁_eq : K₁.comap I.blowupToBase = I.comap I.blowupToBase ^ N * J :=
    comap_injective_of_isIso (I.blowupChart (isAffineOpen_top X)) (hLHS.trans hK₀)
  have hE : (I.comap I.blowupToBase ^ N).IsEffectiveCartier :=
    TauCeti.isEffectiveCartier_pow I.isEffectiveCartier_comap_blowupToBase N
  have hKfg (V : X.affineOpens) : ((I * K₁).ideal V).FG := by
    rw [ideal_mul, Pi.mul_apply, ofIdealTop_ideal,
      ← I.map_ideal (U := V) (V := ⟨⊤, isAffineOpen_top X⟩) (le_top : V.val ≤ ⊤)]
    exact (Ideal.FG.map hI _).mul (Ideal.FG.map hK₀fg _)
  exact ⟨I * K₁, blowupCompIso hE hK₁_eq, hKfg, (I * K₁).isProper_blowupToBase hKfg,
    coe_support_mul_of_comap_blowupToBase_eq_pow_mul hK₁_eq, blowupCompHom_blowupToBase hE hK₁_eq⟩

/-- **Composition of admissible finite-type blowups over an affine scheme.** Corollary of
`exists_blowup_comp_of_isAffine` when `V(I)` avoids an open `U ⊆ X` and `V(J)` avoids
`b₁⁻¹(U)`. -/
theorem exists_blowup_comp_of_isAffine_of_disjoint_support [IsAffine X] (I : X.IdealSheafData)
    (hI : (I.ideal ⟨⊤, isAffineOpen_top X⟩).FG) (J : I.blowup.IdealSheafData)
    (hJ : ∀ W : I.blowup.affineOpens, (J.ideal W).FG) (U : X.Opens)
    (hIU : Disjoint (U : Set X) (I.support : Set X))
    (hJU : Disjoint (I.blowupToBase ⁻¹' (U : Set X)) (J.support : Set I.blowup)) :
    ∃ (K : X.IdealSheafData) (e : J.blowup ≅ K.blowup),
      (∀ V : X.affineOpens, (K.ideal V).FG) ∧ IsProper K.blowupToBase ∧
        Disjoint (U : Set X) (K.support : Set X) ∧ IsIso (K.blowupToBase ∣_ U) ∧
        e.hom ≫ K.blowupToBase = J.blowupToBase ≫ I.blowupToBase := by
  obtain ⟨K, e, hKfg, hproper, hsupp, he⟩ := exists_blowup_comp_of_isAffine I hI J hJ
  obtain ⟨hdisj, hiso⟩ := disjoint_support_and_isIso_blowupToBase_restrict hsupp hIU hJU
  exact ⟨K, e, hKfg, hproper, hdisj, hiso, he⟩

/-- **Composition of blowups on a quasi-compact locally Noetherian scheme.** Let `X` be a
quasi-compact locally Noetherian scheme, `I` an ideal sheaf on `X`, and `J` an ideal sheaf on
`Bl_I X`. Then the composite `J.blowupToBase ≫ I.blowupToBase` is isomorphic over `X` to a single
proper blowup `K.blowupToBase` whose centre has exact support `V(I) ∪ b₁(V(J))`. -/
theorem exists_blowup_comp [CompactSpace X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) :
    ∃ (K : X.IdealSheafData) (e : J.blowup ≅ K.blowup),
      IsProper K.blowupToBase ∧
        (K.support : Set X) =
          (I.support : Set X) ∪ I.blowupToBase '' (J.support : Set I.blowup) ∧
        e.hom ≫ K.blowupToBase = J.blowupToBase ≫ I.blowupToBase := by
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  exact I.exists_blowup_comp_of_compactSpace I.fg_ideal J J.fg_ideal

/-- **Composition of admissible blowups on a quasi-compact locally Noetherian scheme.** Corollary of
`exists_blowup_comp_of_compactSpace_of_disjoint_support` when `V(I)` avoids an open `U ⊆ X` and
`V(J)` avoids `b₁⁻¹(U)`. -/
theorem exists_blowup_comp_of_disjoint_support [CompactSpace X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (U : X.Opens)
    (hIU : Disjoint (U : Set X) (I.support : Set X))
    (hJU : Disjoint (I.blowupToBase ⁻¹' (U : Set X)) (J.support : Set I.blowup)) :
    ∃ (K : X.IdealSheafData) (e : J.blowup ≅ K.blowup),
      IsProper K.blowupToBase ∧ Disjoint (U : Set X) (K.support : Set X) ∧
        IsIso (K.blowupToBase ∣_ U) ∧
        e.hom ≫ K.blowupToBase = J.blowupToBase ≫ I.blowupToBase := by
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  exact I.exists_blowup_comp_of_compactSpace_of_disjoint_support
    I.fg_ideal J J.fg_ideal U hIU hJU

end AlgebraicGeometry.Scheme.IdealSheafData
