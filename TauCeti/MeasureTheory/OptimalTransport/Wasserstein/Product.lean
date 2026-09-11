/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Product
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Tensorization of the Wasserstein distance

The `p`-Wasserstein distance of two product laws is computed by the two factors:

`W_p (μ₁ ⊗ μ₂, ν₁ ⊗ ν₂) ^ p = W_p (μ₁, ν₁) ^ p + W_p (μ₂, ν₂) ^ p`.

The identity is a statement about a *specific* ground distance on the product: the `ℓ^p` product
of the two ground distances, which in Lean is the one carried by `WithLp p (X × Y)` and not the
supremum distance that `X × Y` carries by default. Accordingly the product law appears here as
`(μ₁.prod μ₂).map (WithLp.toLp p)`, the product measure read on the `ℓ^p` type synonym; the
measurable structure of `WithLp p (X × Y)` is the one pulled back from `X × Y`, so this pushforward
changes nothing but the distance.

Tensorization holds because raising the `ℓ^p` product distance to the power `p` makes the ground
cost additively separable across the two factors, so the two coordinates of a transport problem on
the product never interact. The identity holds in `ℝ≥0∞`, with no finiteness assumption on either
factor distance.

The exponent is finite throughout. At `p = ∞` the `ℓ^p` product distance is the maximum of the two
factor distances rather than an `ℓ^p` sum, so tensorization there is a maximum formula and a
separate statement; it is not obtained from the identity below.

## Main statements

* `TauCeti.wassersteinEDist_map_toLp_prod_rpow` and `TauCeti.wassersteinEDist_map_toLp_prod` — the
  tensorization identity, in its `p`-th power form and its root form;
* `TauCeti.wassersteinEDist_map_toLp_prod_left` and
  `TauCeti.wassersteinEDist_map_toLp_prod_right` — tensorizing two laws with a common first, resp.
  second, factor leaves their Wasserstein distance unchanged;
* `TauCeti.hasFiniteMoment_map_toLp_prod_iff` — a product law has finite `p`-moment exactly when
  both factors do.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  tensorization of `W_p` is recorded for the `ℓ^p` product distance.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 5.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type u} {Y : Type v}
  [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

section Tensorization

variable {μ₁ ν₁ : Measure X} {μ₂ ν₂ : Measure Y}
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]

/-- **Tensorization of the Wasserstein distance.** For the `ℓ^p` product distance and a finite
exponent, the `p`-th power of the `p`-Wasserstein distance of two product laws is the sum of the
`p`-th powers of the two factor distances.

Both sides are `∞` as soon as one factor distance is, so no finiteness hypothesis is needed. -/
theorem wassersteinEDist_map_toLp_prod_rpow (hp : p ≠ ∞)
    (hdX : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) :
    wassersteinEDist p ((μ₁.prod μ₂).map (WithLp.toLp p)) ((ν₁.prod ν₂).map (WithLp.toLp p))
        ^ p.toReal
      = wassersteinEDist p μ₁ ν₁ ^ p.toReal + wassersteinEDist p μ₂ ν₂ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hcZ : Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦
      edist w.1 w.2 ^ p.toReal :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_edist_toLp_prod hp hdX hdY)
  have hcX : Measurable fun z : X × X ↦ edist z.1 z.2 ^ p.toReal :=
    ENNReal.continuous_rpow_const.measurable.comp hdX
  have hcY : Measurable fun z : Y × Y ↦ edist z.1 z.2 ^ p.toReal :=
    ENNReal.continuous_rpow_const.measurable.comp hdY
  rw [wassersteinEDist_rpow_eq_transportCost hp0 hp, wassersteinEDist_rpow_eq_transportCost hp0 hp,
    wassersteinEDist_rpow_eq_transportCost hp0 hp, ← MeasurableEquiv.coe_toLp p (X × Y),
    ← transportCost_comp_prodMap (MeasurableEquiv.toLp p (X × Y))
      (MeasurableEquiv.toLp p (X × Y)) hcZ]
  have hsep : (fun z : (X × Y) × X × Y ↦
        edist (MeasurableEquiv.toLp p (X × Y) z.1) (MeasurableEquiv.toLp p (X × Y) z.2)
          ^ p.toReal)
      = fun z : (X × Y) × X × Y ↦
        edist z.1.1 z.2.1 ^ p.toReal + edist z.1.2 z.2.2 ^ p.toReal :=
    funext fun z ↦ edist_toLp_rpow hp z.1 z.2
  rw [hsep]
  exact transportCost_prod_add hcX hcY

/-- **Tensorization of the Wasserstein distance**, in root form. -/
theorem wassersteinEDist_map_toLp_prod (hp : p ≠ ∞)
    (hdX : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) :
    wassersteinEDist p ((μ₁.prod μ₂).map (WithLp.toLp p)) ((ν₁.prod ν₂).map (WithLp.toLp p))
      = (wassersteinEDist p μ₁ ν₁ ^ p.toReal + wassersteinEDist p μ₂ ν₂ ^ p.toReal)
          ^ (1 / p.toReal) := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  rw [← wassersteinEDist_map_toLp_prod_rpow hp hdX hdY, ← ENNReal.rpow_mul,
    mul_one_div_cancel hr.ne', ENNReal.rpow_one]

omit [IsProbabilityMeasure ν₁] in
/-- Tensorizing two laws with a common first factor leaves their `p`-Wasserstein distance
unchanged: the common factor contributes a vanishing term to the tensorization identity. -/
theorem wassersteinEDist_map_toLp_prod_left (hp : p ≠ ∞)
    (hdX : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) :
    wassersteinEDist p ((μ₁.prod μ₂).map (WithLp.toLp p)) ((μ₁.prod ν₂).map (WithLp.toLp p))
      = wassersteinEDist p μ₂ ν₂ := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have h := wassersteinEDist_map_toLp_prod_rpow (μ₁ := μ₁) (ν₁ := μ₁) (μ₂ := μ₂) (ν₂ := ν₂)
    hp hdX hdY
  rw [wassersteinEDist_self_of_measurable_edist hdX, ENNReal.zero_rpow_of_pos hr, zero_add] at h
  exact ENNReal.rpow_left_injective hr.ne' h

omit [IsProbabilityMeasure ν₂] in
/-- Tensorizing two laws with a common second factor leaves their `p`-Wasserstein distance
unchanged: the common factor contributes a vanishing term to the tensorization identity. -/
theorem wassersteinEDist_map_toLp_prod_right (hp : p ≠ ∞)
    (hdX : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) :
    wassersteinEDist p ((μ₁.prod μ₂).map (WithLp.toLp p)) ((ν₁.prod μ₂).map (WithLp.toLp p))
      = wassersteinEDist p μ₁ ν₁ := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have h := wassersteinEDist_map_toLp_prod_rpow (μ₁ := μ₁) (ν₁ := ν₁) (μ₂ := μ₂) (ν₂ := μ₂)
    hp hdX hdY
  rw [wassersteinEDist_self_of_measurable_edist hdY, ENNReal.zero_rpow_of_pos hr, add_zero] at h
  exact ENNReal.rpow_left_injective hr.ne' h

/-- A product law has finite `p`-moment for the `ℓ^p` product distance exactly when both of its
factors do. -/
@[simp]
theorem hasFiniteMoment_map_toLp_prod_iff (hp : p ≠ ∞)
    (hdX : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) :
    HasFiniteMoment p ((μ₁.prod μ₂).map (WithLp.toLp p)) ↔
      HasFiniteMoment p μ₁ ∧ HasFiniteMoment p μ₂ := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hd : Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦ edist w.1 w.2 :=
    measurable_edist_toLp_prod hp hdX hdY
  have key : ∀ x₀ : X, ∀ y₀ : Y,
      wassersteinEDist p (Measure.dirac (WithLp.toLp p (x₀, y₀)))
          ((μ₁.prod μ₂).map (WithLp.toLp p)) ≠ ∞ ↔
        wassersteinEDist p (Measure.dirac x₀) μ₁ ≠ ∞ ∧
          wassersteinEDist p (Measure.dirac y₀) μ₂ ≠ ∞ := fun x₀ y₀ ↦ by
    have hdir : (Measure.dirac (WithLp.toLp p (x₀, y₀)) : Measure (WithLp p (X × Y)))
        = ((Measure.dirac x₀).prod (Measure.dirac y₀)).map (WithLp.toLp p) := by
      rw [Measure.dirac_prod_dirac, Measure.map_dirac' (WithLp.measurable_toLp p (X × Y))]
    have hsum := wassersteinEDist_map_toLp_prod_rpow (μ₁ := Measure.dirac x₀)
      (μ₂ := Measure.dirac y₀) (ν₁ := μ₁) (ν₂ := μ₂) hp hdX hdY
    rw [hdir, ← not_or, not_iff_not]
    calc wassersteinEDist p (((Measure.dirac x₀).prod (Measure.dirac y₀)).map (WithLp.toLp p))
            ((μ₁.prod μ₂).map (WithLp.toLp p)) = ∞
        ↔ wassersteinEDist p (((Measure.dirac x₀).prod (Measure.dirac y₀)).map (WithLp.toLp p))
            ((μ₁.prod μ₂).map (WithLp.toLp p)) ^ p.toReal = ∞ :=
          (ENNReal.rpow_eq_top_iff_of_pos hr).symm
      _ ↔ wassersteinEDist p (Measure.dirac x₀) μ₁ ^ p.toReal
            + wassersteinEDist p (Measure.dirac y₀) μ₂ ^ p.toReal = ∞ := by rw [hsum]
      _ ↔ wassersteinEDist p (Measure.dirac x₀) μ₁ ^ p.toReal = ∞ ∨
            wassersteinEDist p (Measure.dirac y₀) μ₂ ^ p.toReal = ∞ := ENNReal.add_eq_top
      _ ↔ wassersteinEDist p (Measure.dirac x₀) μ₁ = ∞ ∨
            wassersteinEDist p (Measure.dirac y₀) μ₂ = ∞ := by
          rw [ENNReal.rpow_eq_top_iff_of_pos hr, ENNReal.rpow_eq_top_iff_of_pos hr]
  constructor
  · intro h
    obtain ⟨⟨⟨x₀, y₀⟩⟩, hz₀⟩ := hasFiniteMoment_def.mp h
    have hk := (key x₀ y₀).mp ((memLp_edist_iff_wassersteinEDist_dirac_ne_top hd _ _).mp hz₀)
    exact ⟨hasFiniteMoment_def.mpr
        ⟨x₀, (memLp_edist_iff_wassersteinEDist_dirac_ne_top hdX x₀ μ₁).mpr hk.1⟩,
      hasFiniteMoment_def.mpr
        ⟨y₀, (memLp_edist_iff_wassersteinEDist_dirac_ne_top hdY y₀ μ₂).mpr hk.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨x₀, hx₀⟩ := hasFiniteMoment_def.mp h₁
    obtain ⟨y₀, hy₀⟩ := hasFiniteMoment_def.mp h₂
    exact hasFiniteMoment_def.mpr ⟨WithLp.toLp p (x₀, y₀),
      (memLp_edist_iff_wassersteinEDist_dirac_ne_top hd _ _).mpr ((key x₀ y₀).mpr
        ⟨(memLp_edist_iff_wassersteinEDist_dirac_ne_top hdX x₀ μ₁).mp hx₀,
          (memLp_edist_iff_wassersteinEDist_dirac_ne_top hdY y₀ μ₂).mp hy₀⟩)⟩

end Tensorization

end TauCeti
