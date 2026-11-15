/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Map
public import TauCeti.RingTheory.PowerSeries.OpenDisc.AnalyticSubst

/-!
# Coefficient maps on open-disc power series

A bounded ring homomorphism `φ : R →+* S`, `‖φ x‖ ≤ C * ‖x‖`, acts coefficientwise on series on
the open disc of radius `R₀`, giving a ring homomorphism
`TauCeti.PowerSeries.OnOpenDisc.mapHom` from `OnOpenDisc.subring R R₀` to
`OnOpenDisc.subring S R₀`. Over ultrametric rings, restricting to any smaller positive closed disc
identifies `mapHom` with `TauCeti.MvPowerSeries.restrictedMap`, which yields closed-disc Gauss-norm
bounds and uniform continuity for the open-disc Gauss uniformities without requiring a positive
radius or norm-one identity. Along a strictly surjective bounded homomorphism, open-disc series
lift with the same coefficientwise norm bound.

Over complete coefficient rings, `mapHom` commutes with point evaluation on the open disc,
rescaling, Taylor translation, affine coordinate changes, and analytic substitution
(`TauCeti.PowerSeries.OnOpenDisc.mapHom_analyticSubst`).

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.mapHom`: the coefficientwise ring homomorphism on open-disc
  series induced by a bounded ring homomorphism.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.evalAt_mapHom`: point evaluation on an open disc commutes with
  bounded coefficient homomorphisms.
* `TauCeti.PowerSeries.OnOpenDisc.restrict_mapHom`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_mapHom_le`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_mapHom`: comparison with `restrictedMap` on
  each smaller closed disc, Gauss-norm bounds, and uniform continuity.
* `TauCeti.PowerSeries.OnOpenDisc.exists_mapHom_eq_and_norm_coeff_le` and
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_surjective`: coefficientwise bounded lifts along strict
  surjections.
* `TauCeti.PowerSeries.OnOpenDisc.mapHom_rescaleHom`,
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_taylorHom`,
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_affineHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_analyticSubst`: compatibility with rescaling, Taylor
  translation, affine changes of coordinates, and analytic substitution.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section NormedRing

variable {R S : Type*} [NormedRing R] [NormedRing S] {R₀ : ℝ}

section FixedHom

variable (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- The coefficientwise ring homomorphism on open-disc power series induced by a bounded ring
homomorphism `φ : R →+* S` satisfying `‖φ x‖ ≤ C * ‖x‖`. -/
noncomputable def mapHom : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring S R₀ :=
  ((PowerSeries.map φ).comp (OnOpenDisc.subring R R₀).subtype).codRestrict _ fun f ↦
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).map φ hφ)

/-- `mapHom` acts as `PowerSeries.map` on the underlying formal power series. -/
@[simp]
theorem coe_mapHom (f : OnOpenDisc.subring R R₀) :
    (mapHom φ hφ f : S⟦X⟧) = PowerSeries.map φ (f : R⟦X⟧) :=
  (rfl)

/-- `mapHom` acts on each coefficient by `φ`. -/
theorem coeff_mapHom (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (mapHom φ hφ f : S⟦X⟧) = φ (coeff n (f : R⟦X⟧)) := by
  rw [coe_mapHom, coeff_map]

/-- The kernel of `mapHom` consists of the open-disc series whose coefficients all lie in the
kernel of `φ`. -/
theorem mapHom_eq_zero_iff (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ f = 0 ↔ ∀ n, φ (coeff n (f : R⟦X⟧)) = 0 := by
  constructor
  · intro h n
    have hn := congrArg (fun g : OnOpenDisc.subring S R₀ ↦ coeff n (g : S⟦X⟧)) h
    simpa only [coe_mapHom, coeff_map, ZeroMemClass.coe_zero, map_zero] using hn
  · intro h
    apply Subtype.ext
    ext n
    simpa only [coe_mapHom, coeff_map, ZeroMemClass.coe_zero, map_zero] using h n

/-- An injective bounded ring homomorphism induces an injective map on open-disc series. -/
theorem mapHom_injective (hφ_inj : Function.Injective φ) :
    Function.Injective (mapHom (R₀ := R₀) φ hφ) := fun f g h ↦
  Subtype.ext <| PowerSeries.ext fun n ↦ hφ_inj <| by
    simpa only [coe_mapHom, coeff_map] using
      congrArg (fun k : OnOpenDisc.subring S R₀ ↦ coeff n (k : S⟦X⟧)) h

/-- Bounded coefficient maps commute with the polynomial inclusion into open-disc series. -/
@[simp]
theorem mapHom_polynomialHom (p : Polynomial R) :
    mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom p) = OnOpenDisc.polynomialHom (p.map φ) :=
  Subtype.ext <| PowerSeries.ext fun n ↦ by simp

/-- A uniform bound for coefficient lifts gives an open-disc lift with the same norm bound at each
coefficient. Neither ultrametricity nor completeness is required. -/
theorem exists_mapHom_eq_and_norm_coeff_le {C' : ℝ}
    (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖)
    (g : OnOpenDisc.subring S R₀) :
    ∃ f : OnOpenDisc.subring R R₀, mapHom φ hφ f = g ∧
      ∀ n, ‖coeff n (f : R⟦X⟧)‖ ≤ C' * ‖coeff n (g : S⟦X⟧)‖ := by
  choose l hl hln using hlift
  let f₀ : R⟦X⟧ := PowerSeries.mk fun n ↦ l (coeff n (g : S⟦X⟧))
  have hcoeff (n : ℕ) : coeff n f₀ = l (coeff n (g : S⟦X⟧)) := coeff_mk n _
  have hf₀ : f₀.OnOpenDisc R₀ := onOpenDisc_iff.mpr fun r hr hrR ↦ by
    have hg := (isRestricted_iff' r (g : S⟦X⟧)).mp
      (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp g.2) r hr hrR)
    refine (isRestricted_iff' r f₀).mpr <| squeeze_zero (fun _ ↦ by positivity) (fun n ↦ ?_)
      (by simpa only [mul_zero] using hg.const_mul C')
    simpa only [hcoeff, mul_assoc] using mul_le_mul_of_nonneg_right (hln _) (pow_nonneg hr.le n)
  refine ⟨⟨f₀, OnOpenDisc.mem_subring.mpr hf₀⟩, Subtype.ext ?_,
    fun n ↦ by simpa only [hcoeff] using hln _⟩
  ext n
  rw [coeff_mapHom, hcoeff, hl]

/-- If every `s ∈ S` lifts along `φ` to some `r ∈ R` with `‖r‖ ≤ C' * ‖s‖`, then the induced map
on open-disc series is surjective. -/
theorem mapHom_surjective {C' : ℝ} (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) :
    Function.Surjective (mapHom (R₀ := R₀) φ hφ) := fun g ↦ by
  obtain ⟨f, hf, -⟩ := exists_mapHom_eq_and_norm_coeff_le φ hφ hlift g
  exact ⟨f, hf⟩

end FixedHom

/-- The identity ring homomorphism induces the identity on open-disc series. -/
@[simp]
theorem mapHom_id {C : ℝ} (hC : ∀ x : R, ‖RingHom.id R x‖ ≤ C * ‖x‖) :
    mapHom (R₀ := R₀) (RingHom.id R) hC = RingHom.id _ :=
  RingHom.ext fun _ ↦ Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- Bounded coefficient maps compose functorially on open-disc series. -/
theorem mapHom_comp {T : Type*} [NormedRing T] (φ : R →+* S) {C₁ : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖) (ψ : S →+* T) {C₂ C₃ : ℝ} (hψ : ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (hψφ : ∀ x, ‖ψ.comp φ x‖ ≤ C₃ * ‖x‖) :
    mapHom (R₀ := R₀) (ψ.comp φ) hψφ = (mapHom ψ hψ).comp (mapHom φ hφ) :=
  RingHom.ext fun _ ↦ Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- Applying two induced coefficient maps in turn applies the map induced by their composite. -/
@[simp]
theorem mapHom_mapHom {T : Type*} [NormedRing T] (φ : R →+* S) {C₁ : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖) (ψ : S →+* T) {C₂ : ℝ} (hψ : ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (f : OnOpenDisc.subring R R₀) :
    mapHom ψ hψ (mapHom φ hφ f) =
      mapHom (ψ.comp φ) (C := max C₂ 0 * C₁) (fun x ↦ by
        rw [mul_assoc]
        exact (hψ (φ x)).trans <| (mul_le_mul_of_nonneg_right (le_max_left C₂ 0)
          (norm_nonneg _)).trans <| mul_le_mul_of_nonneg_left (hφ x) (le_max_right C₂ 0)) f :=
  Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

end NormedRing

section Ultrametric

variable {R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedRing S] [IsUltrametricDist S] {R₀ : ℝ}

attribute [local instance] radius_pos

section FixedUltrametricHom

variable (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- Restricting `mapHom` to a smaller positive closed disc agrees with
`TauCeti.MvPowerSeries.restrictedMap`. -/
@[simp]
theorem restrict_mapHom (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    restrict r (mapHom φ hφ f) = TauCeti.MvPowerSeries.restrictedMap φ hφ (restrict r f) :=
  Subtype.ext <| by
    rw [coe_restrict, coe_mapHom, TauCeti.PowerSeries.coe_restrictedMap_powerSeries, coe_restrict]

/-- On every smaller positive closed disc, `mapHom` is bounded by the same constant as `φ`. -/
theorem norm_restrict_mapHom_le (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (mapHom φ hφ f)‖ ≤ C * ‖restrict r f‖ := by
  rw [restrict_mapHom]
  exact TauCeti.MvPowerSeries.norm_restrictedMap_le φ hφ (restrict r f)

/-- A norm-preserving coefficient homomorphism preserves every smaller-radius Gauss norm. -/
theorem norm_restrict_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) (r : Set.Ioo (0 : ℝ) R₀)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (mapHom φ hφ f)‖ = ‖restrict r f‖ := by
  rw [restrict_mapHom]
  exact TauCeti.MvPowerSeries.norm_restrictedMap φ hφ hφ' (restrict r f)

/-- Bounded coefficient maps are uniformly continuous for the open-disc Gauss uniformities. -/
theorem uniformContinuous_mapHom : UniformContinuous (mapHom (R₀ := R₀) φ hφ) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  have hlip := TauCeti.MvPowerSeries.lipschitzWith_restrictedMap
    (c := fun _ : Unit ↦ (r : ℝ)) φ hφ
  have hfun : (fun f ↦ restrict r (mapHom φ hφ f)) =
      TauCeti.MvPowerSeries.restrictedMap φ hφ ∘ restrict r :=
    funext (restrict_mapHom φ hφ r)
  rw [hfun]
  exact hlip.uniformContinuous.comp (uniformContinuous_restrict r)

/-- Bounded coefficient maps are continuous for the open-disc Gauss topologies. -/
@[continuity]
theorem continuous_mapHom : Continuous (mapHom (R₀ := R₀) φ hφ) :=
  (uniformContinuous_mapHom φ hφ).continuous

end FixedUltrametricHom

end Ultrametric

section CommRing

/-- Point evaluation on an open disc commutes with `mapHom`. -/
theorem evalAt_mapHom {R S : Type*} [NormedCommRing R] [CompleteSpace R] [NormedCommRing S]
    {R₀ : ℝ} (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) {b : R} (hb : ‖b‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    (mapHom φ hφ f : S⟦X⟧).evalAt (φ b) = φ ((f : R⟦X⟧).evalAt b) :=
  (OnOpenDisc.mem_subring.mp f.2).evalAt_map φ (AddMonoidHomClass.continuous_of_bound φ C hφ) hb

/-- Bounded coefficient maps commute with rescaling on open discs. -/
theorem mapHom_rescaleHom {R S : Type*} [NormedCommRing R] [NormedCommRing S] {R₀ S₀ : ℝ}
    (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) {u : R}
    (hu : ‖u‖ * S₀ ≤ R₀) (hφu : ‖φ u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (rescaleHom hu f) = rescaleHom hφu (mapHom φ hφ f) :=
  Subtype.ext (by simp [PowerSeries.rescale_map])

section CompleteUltrametric

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] {R₀ S₀ : ℝ}

attribute [local instance] radius_pos

/-- Bounded coefficient maps commute with Taylor translation on open discs. -/
theorem mapHom_taylorHom (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) {a : R}
    (ha : ‖a‖ < R₀) (hφa : ‖φ a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (taylorHom ha f) = taylorHom hφa (mapHom φ hφ f) := by
  apply Subtype.ext
  ext n
  rw [coe_mapHom, coe_taylorHom, coeff_map, coeff_taylor, coe_taylorHom, coeff_taylor,
    coe_mapHom, hasseDeriv_map]
  exact (((OnOpenDisc.mem_subring.mp f.2).hasseDeriv n).evalAt_map φ
    (AddMonoidHomClass.continuous_of_bound φ C hφ) ha).symm

/-- Bounded coefficient maps commute with affine changes of coordinates on open discs. -/
theorem mapHom_affineHom (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) {a u : R}
    (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (hφa : ‖φ a‖ < R₀) (hφu : ‖φ u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (affineHom ha hu f) = affineHom hφa hφu (mapHom φ hφ f) := by
  rw [affineHom_apply, affineHom_apply, mapHom_rescaleHom φ hφ hu hφu,
    mapHom_taylorHom φ hφ ha hφa]

/-- Bounded coefficient maps commute with analytic substitution whenever both inner series satisfy
the target-to-source closed-disc radius condition. -/
theorem mapHom_analyticSubst [Fact (0 < S₀)] (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)
    (g : OnOpenDisc.subring R S₀) (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (hφg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s (mapHom φ hφ g)‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (analyticSubst g hg f) =
      analyticSubst (mapHom φ hφ g) hφg (mapHom φ hφ f) := by
  have heq : (mapHom φ hφ).comp (analyticSubst g hg) =
      (analyticSubst (mapHom φ hφ g) hφg).comp (mapHom φ hφ) := by
    apply ringHom_ext
    · exact (continuous_mapHom φ hφ).comp (continuous_analyticSubst g hg)
    · exact (continuous_analyticSubst _ hφg).comp (continuous_mapHom φ hφ)
    · intro a
      simp
    · simp
  exact RingHom.congr_fun heq f

end CompleteUltrametric

end CommRing

end TauCeti.PowerSeries.OnOpenDisc
