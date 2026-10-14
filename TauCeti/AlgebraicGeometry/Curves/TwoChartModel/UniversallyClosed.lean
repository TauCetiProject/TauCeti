/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ValuativeCriterion
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure

/-!
# The two-chart model of a function field is universally closed

Let `F / k` be an algebraic function field and `x ∈ F` nonzero. The scheme
`TauCeti.AlgebraicGeometry.twoChartModel hF hx` is glued from `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}`, where
`𝒪_x` and `𝒪_{x⁻¹}` are the functions regular wherever `x`, respectively `x⁻¹`, is regular. This
file proves that its structure morphism to `Spec k` is universally closed.

Universal closedness is what properness over `k` adds to separatedness and local finite type. It
is also, through the existence part of the valuative criterion, the hypothesis under which every
place of the function field is centred at a point of the scheme
(`TauCeti.AlgebraicGeometry.CodimensionOnePoint.toPlace_surjective`).

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.valuativeCriterion_existence`: the structure morphism
  of `twoChartModel` to `Spec k` satisfies the existence part of the valuative criterion.
* the instance `UniversallyClosed (twoChartModel hF hx ↘ Spec (.of k))`.

## Implementation notes

This is the argument showing that the projective line is universally closed, carried out on the
normalizations of its two charts. Let `R` be a valuation ring with fraction field `K`. A
`K`-point of the scheme lies in one of the charts, so it is a ring map `φ : 𝒪_x → K` or
`𝒪_{x⁻¹} → K`. The functions of `𝒪_x` are integral over `k[x]` and `R` is integrally closed, so
`φ` takes values in `R` as soon as `φ x` does, and then the `K`-point extends to an `R`-point. If
`φ x ∉ R`, then `φ x` is nonzero and `(φ x)⁻¹ ∈ R`, because `R` is a valuation ring; the point lies
on the overlap of the two charts, where `x` is a unit, and the same argument applies on the chart
at infinity to `x⁻¹`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorems II.4.7 and II.4.9.
* The Stacks Project, Tag 01KF, the valuative criterion for universal closedness.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- A `K`-point of a scheme over `k` that factors through `Spec 𝒪_t`, by a ring map sending `t`
into the valuation ring `R`, extends to an `R`-point: `𝒪_t` is integral over `k[t]`, and `R` is
integrally closed and contains the image of `k`. -/
private theorem hasLift_of_mem_range (hF : IsFunctionField k F) {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (S : ValuativeCommSq (X ↘ Spec (.of k))) {t : F}
    (c : Spec (.of (holomorphyRing {P : Place k F | t ∈ P.integers})) ⟶ X)
    (hc : c ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k _)))
    (φ : CommRingCat.of (holomorphyRing {P : Place k F | t ∈ P.integers}) ⟶ .of S.K)
    (hφ : Spec.map φ ≫ c = S.i₁)
    (ht : IsLocalization.IsInteger S.R (φ ⟨t, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩)) :
    S.commSq.HasLift := by
  have := (ValuationRing.integers S.R S.K).isIntegrallyClosed
  -- The constants go to `R`, through the given `R`-point of `Spec k`.
  obtain ⟨κ, hκ⟩ := Spec.map_surjective S.i₂
  have hk : CommRingCat.ofHom (algebraMap k _) ≫ φ =
      κ ≫ CommRingCat.ofHom (algebraMap S.R S.K) := by
    -- Both sides induce the composite `Spec K ⟶ Spec k` around the valuative square.
    have h : Spec.map φ ≫ c ≫ (X ↘ Spec (.of k)) = S.i₁ ≫ (X ↘ Spec (.of k)) := by
      rw [reassoc_of% hφ]
    rw [← Spec.map_inj]
    simpa [hκ, ← hc, h] using S.commSq.w
  refine S.hasLift_of_specMap_comp c φ hφ fun a ↦ IsIntegrallyClosed.isIntegral_iff.mp <|
    isIntegral_map_holomorphyRing_setOf_mem hF φ.hom (fun c ↦ ?_) ?_ a
  · exact IsIntegrallyClosed.isIntegral_iff.mpr ⟨κ c, congr($hk c).symm⟩
  · obtain ⟨r, hr⟩ := ht
    exact IsIntegrallyClosed.isIntegral_iff.mpr ⟨r, hr⟩

/-- Moving a `K`-point between two charts through their overlap: if `T = S₁ ∩ {P | s⁻¹ ∈ 𝒪_P}`
is the overlap of the charts `Spec 𝒪_{S₁}` and `Spec 𝒪_{S₂}`, and a `K`-point `Spec φ` of the
first chart sends `s` to a nonzero element, then it lies in the overlap, where `s` is a unit. It
is therefore a `K`-point `Spec ψ` of the second chart, and `ψ` sends an inverse of `s` to
`(φ s)⁻¹`. -/
private theorem exists_specMap_comp_eq (hF : IsFunctionField k F) {X : Scheme.{u}}
    {S₁ S₂ T : Set (Place k F)} (h₁ : T ⊆ S₁) (h₂ : T ⊆ S₂)
    (c₁ : Spec (.of (holomorphyRing S₁)) ⟶ X) (c₂ : Spec (.of (holomorphyRing S₂)) ⟶ X)
    (w : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (holomorphyRing_antitone h₁)).toRingHom)
        ≫ c₁ =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (holomorphyRing_antitone h₂)).toRingHom)
        ≫ c₂)
    (s : holomorphyRing S₁) (s' : holomorphyRing S₂) (hss' : (s : F) * s' = 1)
    (hT : T = S₁ ∩ {P : Place k F | (s : F)⁻¹ ∈ P.integers}) {K : Type u} [Field K]
    (φ : CommRingCat.of (holomorphyRing S₁) ⟶ .of K) (hφ : φ s ≠ 0) :
    ∃ ψ : CommRingCat.of (holomorphyRing S₂) ⟶ .of K,
      Spec.map ψ ≫ c₂ = Spec.map φ ≫ c₁ ∧ ψ s' = (φ s)⁻¹ := by
  let ι₁ := Subalgebra.inclusion (holomorphyRing_antitone h₁)
  let ι₂ := Subalgebra.inclusion (holomorphyRing_antitone h₂)
  let _ : Algebra (holomorphyRing S₁) (holomorphyRing T) := ι₁.toRingHom.toAlgebra
  have : IsScalarTower (holomorphyRing S₁) (holomorphyRing T) F :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      (Subalgebra.coe_inclusion (holomorphyRing_antitone h₁) a).symm
  have := isLocalization_away_holomorphyRing_inter hF s (left_ne_zero_of_mul_eq_one hss') hT
  -- `φ` extends to the overlap, the localization of `𝒪_{S₁}` away from `s`.
  have hu : IsUnit (φ s) := isUnit_iff_ne_zero.mpr hφ
  let l := IsLocalization.Away.lift s (S := holomorphyRing T) (g := φ.hom) hu
  have hl : CommRingCat.ofHom ι₁.toRingHom ≫ CommRingCat.ofHom l = φ :=
    CommRingCat.hom_ext (IsLocalization.Away.lift_comp s hu)
  have hls : l (ι₂ s') * φ s = 1 := by
    rw [← IsLocalization.Away.lift_eq (S := holomorphyRing T) s hu s, ← map_mul, ← map_one l]
    have hs : (algebraMap (holomorphyRing S₁) (holomorphyRing T) s : F) = s :=
      (IsScalarTower.algebraMap_apply (holomorphyRing S₁) (holomorphyRing T) F s).symm
    have hs' : (ι₂ s' : F) = s' := Subalgebra.coe_inclusion _ s'
    refine congrArg l (Subtype.ext ?_)
    rw [Subalgebra.coe_mul, hs, hs', mul_comm, hss', Subalgebra.coe_one]
  refine ⟨CommRingCat.ofHom ι₂.toRingHom ≫ CommRingCat.ofHom l, ?_, eq_inv_of_mul_eq_one_left hls⟩
  -- Factor `Spec φ ≫ c₁` through the overlap using `hl`, then move to the second chart by `w`.
  have h : Spec.map φ ≫ c₁ =
      Spec.map (CommRingCat.ofHom l) ≫ Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ c₁ := by
    rw [← hl, Spec.map_comp_assoc]
  rw [Spec.map_comp_assoc, h, w]

variable {hF : IsFunctionField k F} {x : F} {hx : x ≠ 0}

variable (hF hx) in
/-- **The two-chart model satisfies the existence part of the valuative criterion** over `Spec k`:
for a valuation ring `R` with fraction field `K`, every `K`-point of `twoChartModel hF hx` over an
`R`-point of `Spec k` extends to an `R`-point. -/
theorem valuativeCriterion_existence :
    ValuativeCriterion.Existence (twoChartModel hF hx ↘ Spec (.of k)) := by
  intro S
  -- `Spec K` is a single point, so the `K`-point factors through any chart containing its image.
  obtain ⟨q⟩ : Nonempty (Spec (.of S.K)) := inferInstanceAs (Nonempty (PrimeSpectrum S.K))
  have hsub {Y : Scheme.{u}} (ι : Y ⟶ twoChartModel hF hx) (h : S.i₁ q ∈ Set.range ι) :
      Set.range S.i₁ ⊆ Set.range ι := by
    rintro _ ⟨q', rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum S.K) q' q]
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  -- `x` and `x⁻¹` as functions on the finite chart and on the chart at infinity.
  let xf : holomorphyRing {P : Place k F | x ∈ P.integers} :=
    ⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩
  let xi : holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers} :=
    ⟨x⁻¹, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩
  rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF hx) (S.i₁ q)).mpr trivial with
    hq | hq
  · let φ := Spec.preimage (IsOpenImmersion.lift (ιFinite hF hx) S.i₁ (hsub _ hq))
    have hφ : Spec.map φ ≫ ιFinite hF hx = S.i₁ := by
      simp only [φ, Spec.map_preimage, IsOpenImmersion.lift_fac]
    by_cases hR : IsLocalization.IsInteger S.R (φ xf)
    · exact hasLift_of_mem_range hF S _ (ιFinite_over hF hx) φ hφ hR
    -- Otherwise `φ x` is nonzero with inverse in `R`, and the point lies on the chart at infinity.
    have h0 : φ xf ≠ 0 := fun h ↦ hR (h ▸ IsLocalization.isInteger_zero)
    obtain ⟨ψ, hψ, hψx⟩ := exists_specMap_comp_eq hF Set.inter_subset_left Set.inter_subset_right
      _ _ (condition hF hx) xf xi hxinv rfl φ h0
    refine hasLift_of_mem_range hF S _ (ιInfinity_over hF hx) ψ (hψ.trans hφ) ?_
    exact hψx ▸ (ValuationRing.isInteger_or_isInteger S.R (φ xf)).resolve_left hR
  · let ψ := Spec.preimage (IsOpenImmersion.lift (ιInfinity hF hx) S.i₁ (hsub _ hq))
    have hψ : Spec.map ψ ≫ ιInfinity hF hx = S.i₁ := by
      simp only [ψ, Spec.map_preimage, IsOpenImmersion.lift_fac]
    by_cases hR : IsLocalization.IsInteger S.R (ψ xi)
    · exact hasLift_of_mem_range hF S _ (ιInfinity_over hF hx) ψ hψ hR
    -- Otherwise `ψ x⁻¹` is nonzero with inverse in `R`, and the point lies on the finite chart.
    have h0 : ψ xi ≠ 0 := fun h ↦ hR (h ▸ IsLocalization.isInteger_zero)
    obtain ⟨φ, hφ, hφx⟩ := exists_specMap_comp_eq hF Set.inter_subset_right Set.inter_subset_left
      _ _ (condition hF hx).symm xi xf (by rw [mul_comm]; exact hxinv)
      (by rw [inv_inv, Set.inter_comm]) ψ h0
    refine hasLift_of_mem_range hF S _ (ιFinite_over hF hx) φ (hφ.trans hψ) ?_
    exact hφx ▸ (ValuationRing.isInteger_or_isInteger S.R (ψ xi)).resolve_left hR

/-- **The two-chart model is universally closed over `Spec k`**, by the valuative criterion: it
is quasi-compact, being covered by two affine charts. -/
instance universallyClosed : UniversallyClosed (twoChartModel hF hx ↘ Spec (.of k)) :=
  UniversallyClosed.of_valuativeCriterion _ (valuativeCriterion_existence hF hx)

end TauCeti.AlgebraicGeometry.twoChartModel
