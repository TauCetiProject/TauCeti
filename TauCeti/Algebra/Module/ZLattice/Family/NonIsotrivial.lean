/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair

import Mathlib.Topology.Separation.CompletelyRegular
import TauCeti.Analysis.Complex.RiemannSurface.ComplexTorus

/-!
# Families of elliptic curves with varying periods are not isotrivial

Let `P : Y → (Λ →ₗ[ℤ] ℂ)` be a holomorphic family of full period lattices in `ℂ` over a complex
manifold `Y`, with family of one-dimensional complex tori `(Y × ℂ)/Λ → Y`. Suppose the family maps
holomorphically and injectively over `Y` into a product `Y × ℂ / L` with one fixed torus; a
biholomorphic product trivialization is such a map. On the fibre over `y` this gives an injective
holomorphic map `ℂ / LinearMap.range (P y) → ℂ / L`, so `LinearMap.range (P y)` is carried onto
`L` by a homothety `z ↦ u z` (`TauCeti.exists_units_smul_range_eq_of_injective`).

Over a preconnected base this pins down the periods up to a common scalar: for any two points `y`
and `y'` there is `c ≠ 0` with `P y' l = c * P y l` for every mark `l`
(`TauCeti.exists_units_forall_apply_eq_mul_of_injective`). Indeed a ratio of two periods
`P y l₂ / P y l₁` is continuous in `y`, and by the homothety it is a ratio of two vectors of `L`.
It therefore takes values in a countable set, and a continuous function on a preconnected space
with countable range is constant.

For the family `ℂ / (ℤ ω₁(y) + ℤ ω₂(y))` of a holomorphically varying period pair, the period
ratio `ω₁(y) / ω₂(y)` is therefore constant (`TauCeti.periodPair_ω₁_div_ω₂_eq_of_injective`). In
particular the family `ℂ / (ℤ τ(y) + ℤ)` of a nonconstant holomorphic `τ : Y → ℍ` admits no
biholomorphism over `Y` onto a product `Y × ℂ / L`
(`TauCeti.exists_fst_ne_torusFamilyProjection_periodPair`). So the real-linear smooth
trivialization `TauCeti.torusFamilyDiffeomorphProd` of a family of tori is not holomorphic in
general, and a holomorphic trivialization such as `TauCeti.torusFamilyLinearDiffeomorphProd` needs
an isotriviality hypothesis.

## Main results

* `TauCeti.exists_units_smul_range_eq_of_injective`: an injective holomorphic map over `Y` into
  `Y × ℂ / L` makes every period lattice homothetic to `L`.
* `TauCeti.exists_units_forall_apply_eq_mul_of_injective`: over a preconnected base, the periods at
  any two points then differ by a common nonzero scalar.
* `TauCeti.periodPair_ω₁_div_ω₂_eq_of_injective`: the same for a varying period pair, in terms of
  the period ratio `ω₁ / ω₂`.
* `TauCeti.exists_fst_ne_torusFamilyProjection_periodPair`: the family `ℂ / (ℤ τ(y) + ℤ)` with
  nonconstant `τ` is not biholomorphic over `Y` to a product with a fixed torus.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Proposition 1.2.1 and
  Chapter 8 (families of complex tori and period data).
-/

public section

open Set
open scoped Manifold Pointwise UpperHalfPlane

namespace TauCeti

section Homothety

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℂ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] ℂ) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hinj : ∀ y, Function.Injective (P y))
  {n : WithTop ℕ∞} [IsManifold I n Y] (hP : ∀ l, ContMDiff I 𝓘(ℂ) n fun y ↦ P y l)
  {L : Submodule ℤ ℂ} [DiscreteTopology L]
  {Φ : letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × ℂ) → Y × AddAction.orbitRel.Quotient L ℂ}

include hinj hP in
/-- **Fibrewise homothety.** If a holomorphic family of one-dimensional complex tori maps
holomorphically and injectively over `Y` into the product `Y × ℂ / L` with one fixed torus, then
every period lattice `LinearMap.range (P y)` is carried onto `L` by multiplication by a unit. -/
theorem exists_units_smul_range_eq_of_injective (hn : n ≠ 0)
    (hΦ : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) n Φ)
    (hΦinj : Function.Injective Φ) (hΦP : ∀ x, (Φ x).1 = torusFamilyProjection P x) (y : Y) :
    ∃ u : ℂˣ, u • LinearMap.range (P y) = L := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  -- The fibre over `y`, read in the fixed torus `ℂ / L`.
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n fun z ↦ (Φ (torusFamilyFiberMap P y z)).2 :=
    contMDiff_snd.comp (hΦ.comp (contMDiff_torusFamilyFiberMap P hinj hP y))
  have hfinj : Function.Injective fun z ↦ (Φ (torusFamilyFiberMap P y z)).2 := by
    intro z w h
    refine torusFamilyFiberMap_injective P y (hΦinj (Prod.ext ?_ h))
    rw [hΦP, hΦP, torusFamilyProjection_fiberMap, torusFamilyProjection_fiberMap]
  obtain ⟨u, hu, -⟩ := hf.exists_units_smul_eq_of_injective hn hfinj
  exact ⟨u, hu⟩

include hinj hP in
/-- **Holomorphic maps to a product force constant periods.** If a holomorphic family of
one-dimensional complex tori over a preconnected base maps holomorphically and injectively over `Y`
into the product `Y × ℂ / L` with one fixed torus, then the periods at any two points differ by a
common nonzero scalar: `P y' l = c * P y l` for every mark `l`. In particular every ratio of two
periods is independent of the point. -/
theorem exists_units_forall_apply_eq_mul_of_injective [PreconnectedSpace Y] (hn : n ≠ 0)
    (hΦ : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ContMDiff (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) n Φ)
    (hΦinj : Function.Injective Φ) (hΦP : ∀ x, (Φ x).1 = torusFamilyProjection P x) (y y' : Y) :
    ∃ c : ℂˣ, ∀ l, P y' l = c * P y l := by
  choose u hu using exists_units_smul_range_eq_of_injective P hinj hP hn hΦ hΦinj hΦP
  have hmem (z : Y) (l : Λ) : (u z : ℂ) * P z l ∈ L := by
    rw [← hu z]
    exact Submodule.smul_mem_pointwise_smul _ (u z) _ (LinearMap.mem_range_self _ l)
  -- A mark `l₀` with nonzero periods: the periods at `y` span `ℂ` over `ℝ`.
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, P y l₀ ≠ 0 := by
    refine (DFunLike.ne_iff (f := P y) (g := 0)).mp fun h ↦ ?_
    simpa [LinearMap.range_eq_bot.mpr h] using
      IsZLattice.span_top (K := ℝ) (L := LinearMap.range (P y))
  have hne (z : Y) : P z l₀ ≠ 0 := fun h ↦
    hl₀ (by rw [(hinj z).eq_iff' (map_zero _) |>.mp h, map_zero])
  -- Each ratio `P z l / P z l₀` is continuous with values in the countable set `L / L`.
  have hratio (l : Λ) : P y' l / P y' l₀ = P y l / P y l₀ := by
    have hL : (L : Set ℂ).Countable := countable_coe_iff.mp
      (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)
    have hS : (image2 (· / ·) (L : Set ℂ) L).Countable := hL.image2 hL _
    have hcont : Continuous fun z ↦ P z l / P z l₀ :=
      (hP l).continuous.div (hP l₀).continuous hne
    refine hS.isTotallyDisconnected _ ?_ (isPreconnected_range hcont)
      (mem_range_self y') (mem_range_self y)
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hmem z l, _, hmem z l₀, mul_div_mul_left _ _ (u z).ne_zero⟩
  refine ⟨Units.mk0 (P y' l₀ / P y l₀) (div_ne_zero (hne y') (hne y)), fun l ↦ ?_⟩
  have := hratio l
  rw [Units.val_mk0]
  field_simp [hne y, hne y'] at this ⊢
  linear_combination this

end Homothety

section PeriodPair

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℂ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  {n : WithTop ℕ∞}

variable [T2Space Y] [LocallyCompactSpace Y] [PreconnectedSpace Y] [IsManifold I n Y]
  {L : Submodule ℤ ℂ} [DiscreteTopology L]

/-- **Holomorphic maps to a product fix the period ratio.** For a period pair `ω y`
varying holomorphically over a preconnected complex manifold `Y`, if the family of tori
`ℂ / (ℤ ω₁(y) + ℤ ω₂(y))` maps holomorphically and injectively over `Y` into the product
`Y × ℂ / L` with one fixed torus, then the period ratio `ω₁(y) / ω₂(y)` does not depend on `y`. -/
theorem periodPair_ω₁_div_ω₂_eq_of_injective {ω : Y → PeriodPair}
    (hω₁ : ContMDiff I 𝓘(ℂ) n fun y ↦ (ω y).ω₁) (hω₂ : ContMDiff I 𝓘(ℂ) n fun y ↦ (ω y).ω₂)
    (hn : n ≠ 0)
    {Φ : letI := periodAddAction fun y ↦ (ω y).periodMap
      AddAction.orbitRel.Quotient (ℤ × ℤ) (Y × ℂ) → Y × AddAction.orbitRel.Quotient L ℂ}
    (hΦ : letI := periodAddAction fun y ↦ (ω y).periodMap
      letI := torusFamilyChartedSpace (H := H) (fun y ↦ (ω y).periodMap)
        (fun l ↦ (contMDiff_periodMap_apply hω₁ hω₂ l).continuous)
        fun y ↦ (ω y).injective_periodMap
      ContMDiff (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) n Φ)
    (hΦinj : Function.Injective Φ)
    (hΦP : ∀ x, (Φ x).1 = torusFamilyProjection (fun y ↦ (ω y).periodMap) x) (y y' : Y) :
    (ω y').ω₁ / (ω y').ω₂ = (ω y).ω₁ / (ω y).ω₂ := by
  obtain ⟨c, hc⟩ := exists_units_forall_apply_eq_mul_of_injective (fun y ↦ (ω y).periodMap)
    (fun y ↦ (ω y).injective_periodMap) (contMDiff_periodMap_apply hω₁ hω₂) hn hΦ hΦinj hΦP y y'
  rw [← PeriodPair.periodMap_one_zero, ← PeriodPair.periodMap_zero_one, hc, hc,
    PeriodPair.periodMap_one_zero, PeriodPair.periodMap_zero_one, mul_div_mul_left _ _ c.ne_zero]

/-- **A family of elliptic curves with varying modulus is not isotrivial.** Let `τ : Y → ℍ` be
holomorphic on a preconnected complex manifold, with `τ y₁ ≠ τ y₂` for two points. Then no
biholomorphism from the family of tori `ℂ / (ℤ τ(y) + ℤ)` onto a product `Y × ℂ / L` with one fixed
torus lies over `Y`: for some point `x` of the family, the base coordinate of `Φ x` differs from
the base point `TauCeti.torusFamilyProjection _ x` of `x`. -/
theorem exists_fst_ne_torusFamilyProjection_periodPair {τ : Y → ℍ}
    (hτ : ContMDiff I 𝓘(ℂ) n fun y ↦ (τ y : ℂ)) (hn : n ≠ 0) {y₁ y₂ : Y} (hne : τ y₁ ≠ τ y₂)
    (Φ : letI := periodAddAction fun y ↦ (τ y).periodPair.periodMap
      letI := torusFamilyChartedSpace (H := H) (fun y ↦ (τ y).periodPair.periodMap)
        (fun l ↦ (contMDiff_periodPair_periodMap_apply hτ l).continuous)
        fun y ↦ (τ y).periodPair.injective_periodMap
      Diffeomorph (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) (AddAction.orbitRel.Quotient (ℤ × ℤ) (Y × ℂ))
        (Y × AddAction.orbitRel.Quotient L ℂ) n) :
    ∃ x, (Φ x).1 ≠ torusFamilyProjection (fun y ↦ (τ y).periodPair.periodMap) x := by
  let _ := periodAddAction fun y ↦ (τ y).periodPair.periodMap
  let _ := torusFamilyChartedSpace (H := H) (fun y ↦ (τ y).periodPair.periodMap)
    (fun l ↦ (contMDiff_periodPair_periodMap_apply hτ l).continuous)
    fun y ↦ (τ y).periodPair.injective_periodMap
  by_contra! hΦP
  refine hne (UpperHalfPlane.ext ?_)
  simpa using periodPair_ω₁_div_ω₂_eq_of_injective
    (ω := fun y ↦ (τ y).periodPair) (by simpa using hτ) (by simpa using contMDiff_const) hn
    Φ.contMDiff Φ.injective hΦP y₂ y₁

end PeriodPair

end TauCeti
