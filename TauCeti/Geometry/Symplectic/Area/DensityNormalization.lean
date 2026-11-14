/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Normalizing an area density on the strip

Let `ρ` be a positive density, continuous on the closed strip `ℝ × [0, 1]` (`TauCeti.unitStrip`),
the universal cover of the closed annulus `(ℝ / ℤ) × [0, 1]`, which is `1`-periodic in the first
coordinate. Put

`s(x) = ∫₀¹ ρ(x, r) dr`  (`TauCeti.stripColumnMass`),  `a = ∫₀¹ s(x) dx`  (`TauCeti.stripMass`).

This file studies the map `Φ(x, y) = (u, v)` (`TauCeti.stripNormalization`) with

`u = a⁻¹ ∫₀ˣ s(t) dt`,  `v = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr`.

If `ρ` is `C^1` on the strip, then `Φ` carries the area form `ρ dx ∧ dy` to `a` times the standard
area form: at every point `p` of the strip, `a · det dΦ_p = ρ(p)`, the derivative being taken
within the strip (`TauCeti.stripMass_mul_det_fderivWithin_stripNormalization`). It is a bijection
of the strip onto itself (`TauCeti.bijOn_stripNormalization`) which commutes with the deck
translation `(x, y) ↦ (x + 1, y)` (`TauCeti.stripNormalization_add_one`), maps each boundary line
to itself (`TauCeti.stripNormalization_mk_zero`, `TauCeti.stripNormalization_mk_one`), and is as
smooth on the strip as `ρ` (`TauCeti.contDiffOn_stripNormalization`). Its first coordinate
depends only on `x` and is strictly increasing (`TauCeti.stripNormalizedAngle_strictMono`), so for
a boundary lift `f : ℝ → ℝ` the displacements `f x - x` and `u (f x) - u x` have the same sign.
For the constant density `1` it is the identity (`TauCeti.stripNormalization_one`); for the
density `1 + y` it is `(x, y) ↦ (x, (2 y + y²) / 3)` (`TauCeti.stripNormalization_one_add_snd`).

Conjugation by `Φ` compares area-preserving maps for the two forms. If `ρ` is `C^1` on the strip
and `Φ ∘ F = G ∘ Φ` on the strip, then `ρ(F p) · det dF_p = ρ(p) · det dG_(Φ p)` at every point `p`
of the strip such that `F` is differentiable within the strip at `p` and `G` is differentiable
within the strip at `Φ p` (`TauCeti.mul_det_fderivWithin_eq_of_stripNormalization_conj`), so `G`
preserves `dx ∧ dy` at `Φ p` exactly when `F` preserves `ρ dx ∧ dy` at `p`
(`TauCeti.det_fderivWithin_eq_one_iff_of_stripNormalization_conj`). This is the reduction of
statements about area-preserving maps of the annulus for a positive area form `ρ dx ∧ dy`, such as
the Poincaré–Birkhoff theorem, to the standard area form. It needs the conjugate `G` to be
differentiable; smoothness of the inverse of `Φ` is not proved here.

All derivatives are taken within the closed strip, where they are unique; only the values of `ρ` on
the strip enter. The vertical integral is rewritten as `y ∫₀¹ ρ(x, y t) dt`, an integral over a
fixed compact parameter interval, so that its smoothness up to the boundary of the strip follows
from `Convex.contDiffOn_integral_smul_of_contDiffOn`.

## Main definitions

* `TauCeti.unitStrip`: the closed strip `ℝ × [0, 1]`.
* `TauCeti.stripColumnMass ρ x`: the mass `∫₀¹ ρ(x, r) dr` of the vertical segment over `x`.
* `TauCeti.stripMass ρ`: the mass of the fundamental domain `[0, 1] × [0, 1]`.
* `TauCeti.stripNormalizedAngle ρ x`: the normalized mass `a⁻¹ ∫₀ˣ s` to the left of `x`.
* `TauCeti.stripNormalization ρ`: the normalization map `Φ`.

## Main results

* `TauCeti.contDiffOn_stripNormalization`: `Φ` is `C^n` on the strip when `ρ` is.
* `TauCeti.bijOn_stripNormalization`: `Φ` is a bijection of the strip onto itself.
* `TauCeti.stripNormalization_add_one`: `Φ` commutes with the deck translation.
* `TauCeti.stripMass_mul_det_fderivWithin_stripNormalization`: `a · det dΦ = ρ` for a `C^1`
  density.
* `TauCeti.det_fderivWithin_eq_one_iff_of_stripNormalization_conj`: for a `C^1` density,
  conjugating by `Φ` turns preservation of `ρ dx ∧ dy` into preservation of `dx ∧ dy`.

## References

* Charles Conley and Eduard Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* Patrice Le Calvez and Jian Wang, *Some remarks on the Poincaré–Birkhoff theorem*, Proc. Amer.
  Math. Soc. 138 (2010), 703–715.
-/

public section

noncomputable section

open MeasureTheory Set Filter intervalIntegral
open scoped ContDiff unitInterval Topology

namespace TauCeti

/-! ### The strip -/

/-- The closed strip `ℝ × [0, 1]`, the universal cover of the closed annulus `(ℝ / ℤ) × [0, 1]`. -/
def unitStrip : Set (ℝ × ℝ) := univ ×ˢ Icc 0 1

theorem unitStrip_def : unitStrip = univ ×ˢ Icc (0 : ℝ) 1 :=
  (rfl)

@[simp]
theorem mem_unitStrip {p : ℝ × ℝ} : p ∈ unitStrip ↔ p.2 ∈ Icc (0 : ℝ) 1 := by
  simp [unitStrip]

theorem convex_unitStrip : Convex ℝ unitStrip :=
  convex_univ.prod (convex_Icc 0 1)

theorem uniqueDiffOn_unitStrip : UniqueDiffOn ℝ unitStrip :=
  uniqueDiffOn_univ.prod (uniqueDiffOn_Icc zero_lt_one)

theorem isClosed_unitStrip : IsClosed unitStrip :=
  isClosed_univ.prod isClosed_Icc

/-! ### Masses of a density -/

/-- The mass `s(x) = ∫₀¹ ρ(x, r) dr` of a density `ρ` on the vertical segment of the strip over
`x`. -/
def stripColumnMass (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, ρ (x, r)

/-- The mass `a = ∫₀¹ s(x) dx` of a density `ρ` on the fundamental domain `[0, 1] × [0, 1]` of the
strip, the area of the annulus for `ρ dx ∧ dy`. -/
def stripMass (ρ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, stripColumnMass ρ x

/-- The normalized mass `u(x) = a⁻¹ ∫₀ˣ s(t) dt` of a density `ρ` on the part of the strip between
the vertical lines over `0` and `x`, the first coordinate of `TauCeti.stripNormalization ρ`. -/
def stripNormalizedAngle (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, stripColumnMass ρ t) / stripMass ρ

/-- The **normalization** `Φ(x, y) = (a⁻¹ ∫₀ˣ s(t) dt, s(x)⁻¹ ∫₀ʸ ρ(x, r) dr)` of a density `ρ` on
the strip. For a positive periodic density continuous on the strip it is a bijection of the strip
that commutes with the deck translation and maps each boundary line to itself; if the density is
also `C^1` on the strip, then `a · det dΦ = ρ`. -/
def stripNormalization (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (stripNormalizedAngle ρ p.1, (∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) / stripColumnMass ρ p.1)

variable {ρ : ℝ × ℝ → ℝ}

theorem stripColumnMass_def (x : ℝ) : stripColumnMass ρ x = ∫ r in (0 : ℝ)..1, ρ (x, r) :=
  (rfl)

theorem stripMass_def : stripMass ρ = ∫ x in (0 : ℝ)..1, stripColumnMass ρ x :=
  (rfl)

theorem stripNormalizedAngle_def (x : ℝ) :
    stripNormalizedAngle ρ x = (∫ t in (0 : ℝ)..x, stripColumnMass ρ t) / stripMass ρ :=
  (rfl)

theorem stripNormalization_def (p : ℝ × ℝ) :
    stripNormalization ρ p =
      (stripNormalizedAngle ρ p.1, (∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) / stripColumnMass ρ p.1) :=
  (rfl)

@[simp]
theorem stripNormalization_fst (p : ℝ × ℝ) :
    (stripNormalization ρ p).1 = stripNormalizedAngle ρ p.1 :=
  (rfl)

theorem stripNormalization_snd (p : ℝ × ℝ) :
    (stripNormalization ρ p).2 = (∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) / stripColumnMass ρ p.1 :=
  (rfl)

/-- The column masses of the constant density `1` are `1`. -/
@[simp]
theorem stripColumnMass_one : stripColumnMass (1 : ℝ × ℝ → ℝ) = 1 := by
  funext x
  simp [stripColumnMass_def]

/-- The constant density `1` gives the fundamental domain mass `1`. -/
@[simp]
theorem stripMass_one : stripMass (1 : ℝ × ℝ → ℝ) = 1 := by
  simp [stripMass_def]

/-- A density continuous on the strip is continuous on each vertical segment. -/
private theorem continuousOn_comp_mk_left (hρ : ContinuousOn ρ unitStrip) (x : ℝ) :
    ContinuousOn (fun r ↦ ρ (x, r)) (Icc 0 1) :=
  hρ.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hr ↦ mem_unitStrip.2 hr

/-- A density continuous on the strip is integrable along each vertical segment of the strip. -/
private theorem intervalIntegrable_comp_mk_left (hρ : ContinuousOn ρ unitStrip) (x : ℝ)
    {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r ↦ ρ (x, r)) volume y y' :=
  ((continuousOn_comp_mk_left hρ x).mono (uIcc_subset_Icc hy hy')).intervalIntegrable

/-- A density continuous and positive on the strip has positive column masses. -/
theorem stripColumnMass_pos (hρ : ContinuousOn ρ unitStrip) (hpos : ∀ p ∈ unitStrip, 0 < ρ p)
    (x : ℝ) : 0 < stripColumnMass ρ x :=
  intervalIntegral_pos_of_pos_on
    (intervalIntegrable_comp_mk_left hρ x ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
    (fun _ hr ↦ hpos _ (mem_unitStrip.2 (Ioo_subset_Icc_self hr))) zero_lt_one

/-- The column mass of a periodic density is periodic. -/
theorem stripColumnMass_add_one (hper : ∀ p ∈ unitStrip, ρ (p.1 + 1, p.2) = ρ p) (x : ℝ) :
    stripColumnMass ρ (x + 1) = stripColumnMass ρ x :=
  integral_congr fun r hr ↦ hper (x, r) (mem_unitStrip.2 (by simpa using hr))

/-- The column mass of a `C^n` density on the strip is `C^n`. -/
theorem contDiff_stripColumnMass {n : ℕ∞} (hρ : ContDiffOn ℝ n ρ unitStrip) :
    ContDiff ℝ n (stripColumnMass ρ) := by
  rw [← contDiffOn_univ]
  refine (convex_univ.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    (g := fun _ ↦ (1 : ℝ)) (integrable_const 1) continuous_subtype_val uniqueDiffOn_univ
    uniqueDiffOn_unitStrip hρ fun _ _ t ↦ mem_unitStrip.2 t.2).congr fun x _ ↦ ?_
  simp [stripColumnMass_def, intervalIntegral_eq_integral_unitInterval]

theorem continuous_stripColumnMass (hρ : ContinuousOn ρ unitStrip) :
    Continuous (stripColumnMass ρ) :=
  (contDiff_stripColumnMass (n := 0) (contDiffOn_zero.2 hρ)).continuous

/-- A density continuous and positive on the strip gives the fundamental domain positive mass. -/
theorem stripMass_pos (hρ : ContinuousOn ρ unitStrip) (hpos : ∀ p ∈ unitStrip, 0 < ρ p) :
    0 < stripMass ρ :=
  intervalIntegral_pos_of_pos_on ((continuous_stripColumnMass hρ).intervalIntegrable 0 1)
    (fun x _ ↦ stripColumnMass_pos hρ hpos x) zero_lt_one

/-! ### The first coordinate -/

@[simp]
theorem stripNormalizedAngle_zero : stripNormalizedAngle ρ 0 = 0 := by
  simp [stripNormalizedAngle_def]

/-- For a density giving the fundamental domain nonzero mass, `u(1) = 1`. -/
theorem stripNormalizedAngle_one (h : stripMass ρ ≠ 0) : stripNormalizedAngle ρ 1 = 1 := by
  rw [stripNormalizedAngle_def, ← stripMass_def, div_self h]

/-- The first coordinate of the normalization of the constant density `1` is the identity. -/
@[simp]
theorem stripNormalizedAngle_one_left : stripNormalizedAngle (1 : ℝ × ℝ → ℝ) = id := by
  funext x
  simp [stripNormalizedAngle_def]

/-- The derivative of the first coordinate of the normalization is `s(x) / a`. -/
theorem hasDerivAt_stripNormalizedAngle (hρ : ContinuousOn ρ unitStrip) (x : ℝ) :
    HasDerivAt (stripNormalizedAngle ρ) (stripColumnMass ρ x / stripMass ρ) x :=
  ((continuous_stripColumnMass hρ).integral_hasStrictDerivAt 0 x).hasDerivAt.div_const _

/-- The first coordinate of the normalization is `C^(n + 1)` when the density is `C^n` on the
strip. -/
theorem contDiff_stripNormalizedAngle {n : ℕ∞} (hρ : ContDiffOn ℝ n ρ unitStrip) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) (stripNormalizedAngle ρ) := by
  have hc : ContinuousOn ρ unitStrip := hρ.continuousOn
  have hd : deriv (stripNormalizedAngle ρ) = fun x ↦ stripColumnMass ρ x / stripMass ρ :=
    funext fun x ↦ (hasDerivAt_stripNormalizedAngle hc x).deriv
  exact contDiff_succ_iff_deriv.2 ⟨fun x ↦ (hasDerivAt_stripNormalizedAngle hc x).differentiableAt,
    fun h ↦ absurd h (by simp), hd ▸ (contDiff_stripColumnMass hρ).div_const _⟩

theorem continuous_stripNormalizedAngle (hρ : ContinuousOn ρ unitStrip) :
    Continuous (stripNormalizedAngle ρ) :=
  (contDiff_stripNormalizedAngle (n := 0) (contDiffOn_zero.2 hρ)).continuous

/-- For a density continuous and positive on the strip the first coordinate of the normalization is
strictly increasing. -/
theorem stripNormalizedAngle_strictMono (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) : StrictMono (stripNormalizedAngle ρ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_stripNormalizedAngle hρ)
    fun x ↦ div_pos (stripColumnMass_pos hρ hpos x) (stripMass_pos hρ hpos)

/-- For a periodic density continuous and positive on the strip the first coordinate of the
normalization commutes with the unit translation: `u(x + 1) = u(x) + 1`. -/
theorem stripNormalizedAngle_add_one (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (hper : ∀ p ∈ unitStrip, ρ (p.1 + 1, p.2) = ρ p)
    (x : ℝ) : stripNormalizedAngle ρ (x + 1) = stripNormalizedAngle ρ x + 1 := by
  have hs := continuous_stripColumnMass hρ
  have hperiodic : Function.Periodic (stripColumnMass ρ) 1 := stripColumnMass_add_one hper
  rw [stripNormalizedAngle_def, stripNormalizedAngle_def,
    ← integral_add_adjacent_intervals (hs.intervalIntegrable 0 x) (hs.intervalIntegrable x (x + 1)),
    hperiodic.intervalIntegral_add_eq x 0, zero_add, add_div, ← stripMass_def,
    div_self (stripMass_pos hρ hpos).ne']

/-- For a periodic density continuous and positive on the strip the first coordinate of the
normalization is onto `ℝ`: it is a continuous lift of a degree-one circle map. -/
theorem stripNormalizedAngle_surjective (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (hper : ∀ p ∈ unitStrip, ρ (p.1 + 1, p.2) = ρ p) :
    Function.Surjective (stripNormalizedAngle ρ) :=
  let u : CircleDeg1Lift :=
    ⟨⟨stripNormalizedAngle ρ, (stripNormalizedAngle_strictMono hρ hpos).monotone⟩,
      stripNormalizedAngle_add_one hρ hpos hper⟩
  u.continuous_iff_surjective.1 (continuous_stripNormalizedAngle hρ)

/-! ### The second coordinate -/

/-- The normalization maps the lower boundary line of the strip to itself. -/
@[simp]
theorem stripNormalization_mk_zero (x : ℝ) :
    stripNormalization ρ (x, 0) = (stripNormalizedAngle ρ x, 0) := by
  simp [stripNormalization]

/-- For a density continuous and positive on the strip the normalization maps the upper boundary
line of the strip to itself. -/
theorem stripNormalization_mk_one (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (x : ℝ) :
    stripNormalization ρ (x, 1) = (stripNormalizedAngle ρ x, 1) :=
  Prod.ext rfl (div_self (stripColumnMass_pos hρ hpos x).ne')

/-- On each vertical segment of the strip, the second coordinate of the normalization is strictly
increasing. -/
theorem stripNormalization_snd_strictMonoOn (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (x : ℝ) :
    StrictMonoOn (fun y ↦ (stripNormalization ρ (x, y)).2) (Icc 0 1) := by
  intro y hy y' hy' hlt
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  simp only [stripNormalization_snd]
  rw [div_lt_div_iff_of_pos_right (stripColumnMass_pos hρ hpos x), ← sub_pos,
    integral_interval_sub_left (intervalIntegrable_comp_mk_left hρ x h0 hy')
      (intervalIntegrable_comp_mk_left hρ x h0 hy)]
  exact intervalIntegral_pos_of_pos_on (intervalIntegrable_comp_mk_left hρ x hy hy')
    (fun r hr ↦ hpos _ (mem_unitStrip.2 ⟨hy.1.trans hr.1.le, hr.2.le.trans hy'.2⟩)) hlt

/-- On each vertical segment of the strip, the second coordinate of the normalization is
continuous. -/
theorem continuousOn_stripNormalization_snd (hρ : ContinuousOn ρ unitStrip) (x : ℝ) :
    ContinuousOn (fun y ↦ (stripNormalization ρ (x, y)).2) (Icc 0 1) := by
  have h := continuousOn_primitive_interval (μ := volume) (a := 0) (b := 1)
    (by rw [uIcc_of_le zero_le_one]; exact (continuousOn_comp_mk_left hρ x).integrableOn_Icc)
  rw [uIcc_of_le zero_le_one] at h
  simpa only [stripNormalization_snd] using h.div_const (stripColumnMass ρ x)

/-- On each vertical segment of the strip, the second coordinate of the normalization is a
bijection of `[0, 1]`. -/
theorem bijOn_stripNormalization_snd (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (x : ℝ) :
    BijOn (fun y ↦ (stripNormalization ρ (x, y)).2) (Icc 0 1) (Icc 0 1) := by
  have hmono := stripNormalization_snd_strictMonoOn hρ hpos x
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hv0 : (stripNormalization ρ (x, 0)).2 = 0 := by rw [stripNormalization_mk_zero]
  have hv1 : (stripNormalization ρ (x, 1)).2 = 1 := by rw [stripNormalization_mk_one hρ hpos]
  refine ⟨fun y hy ↦ ⟨?_, ?_⟩, hmono.injOn, ?_⟩
  · exact hv0 ▸ hmono.monotoneOn h0 hy hy.1
  · exact hv1 ▸ hmono.monotoneOn hy h1 hy.2
  · intro v hv
    have h := intermediate_value_Icc zero_le_one (continuousOn_stripNormalization_snd hρ x)
    rw [hv0, hv1] at h
    exact h hv

/-! ### The normalization map -/

/-- For a density continuous and positive on the strip the normalization maps the strip to
itself. -/
theorem mapsTo_stripNormalization (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) : MapsTo (stripNormalization ρ) unitStrip unitStrip :=
  fun p hp ↦ mem_unitStrip.2 ((bijOn_stripNormalization_snd hρ hpos p.1).mapsTo
    (mem_unitStrip.1 hp))

/-- **The normalization is a bijection of the strip.** -/
theorem bijOn_stripNormalization (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (hper : ∀ p ∈ unitStrip, ρ (p.1 + 1, p.2) = ρ p) :
    BijOn (stripNormalization ρ) unitStrip unitStrip := by
  refine ⟨mapsTo_stripNormalization hρ hpos, ?_, ?_⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
    have hx : x = x' := (stripNormalizedAngle_strictMono hρ hpos).injective (congrArg Prod.fst h)
    subst hx
    exact Prod.ext rfl ((bijOn_stripNormalization_snd hρ hpos x).injOn (mem_unitStrip.1 hp)
      (mem_unitStrip.1 hp') (congrArg Prod.snd h))
  · rintro ⟨u, v⟩ hq
    obtain ⟨x, rfl⟩ := stripNormalizedAngle_surjective hρ hpos hper u
    obtain ⟨y, hy, hyv⟩ := (bijOn_stripNormalization_snd hρ hpos x).surjOn (mem_unitStrip.1 hq)
    exact ⟨(x, y), mem_unitStrip.2 hy, Prod.ext rfl hyv⟩

/-- **The normalization commutes with the deck translation** `(x, y) ↦ (x + 1, y)` of the strip. -/
theorem stripNormalization_add_one (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) (hper : ∀ p ∈ unitStrip, ρ (p.1 + 1, p.2) = ρ p)
    {p : ℝ × ℝ} (hp : p ∈ unitStrip) :
    stripNormalization ρ (p.1 + 1, p.2) = stripNormalization ρ p + (1, 0) := by
  refine Prod.ext (stripNormalizedAngle_add_one hρ hpos hper p.1) ?_
  simp only [stripNormalization_snd, stripColumnMass_add_one hper, Prod.snd_add, add_zero]
  congr 1
  refine integral_congr fun r hr ↦ hper (p.1, r) (mem_unitStrip.2 ?_)
  exact uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ (mem_unitStrip.1 hp) hr

/-- The normalization of the constant density `1`, the standard area form, is the identity. -/
@[simp]
theorem stripNormalization_one : stripNormalization 1 = id := by
  funext p
  simp [stripNormalization_def]

/-- For the density `1 + y`, with column masses `3 / 2`, the normalization is
`(x, y) ↦ (x, (2 y + y²) / 3)`. -/
theorem stripNormalization_one_add_snd (p : ℝ × ℝ) :
    stripNormalization (fun q ↦ 1 + q.2) p = (p.1, (2 * p.2 + p.2 ^ 2) / 3) := by
  have hint (y : ℝ) : ∫ r in (0 : ℝ)..y, (1 + r) = y + y ^ 2 / 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id]
    simp
  have hs (x : ℝ) : stripColumnMass (fun q : ℝ × ℝ ↦ 1 + q.2) x = 3 / 2 := by
    rw [stripColumnMass_def, hint]
    norm_num
  have ha : stripMass (fun q : ℝ × ℝ ↦ 1 + q.2) = 3 / 2 := by
    simp [stripMass_def, hs]
  refine Prod.ext ?_ ?_
  · simp only [stripNormalization_fst, stripNormalizedAngle_def, hs, ha,
      intervalIntegral.integral_const]
    field_simp
    ring
  · rw [stripNormalization_snd, hs, hint]
    ring

/-! ### Smoothness -/

/-- The vertical primitive `(x, y) ↦ ∫₀ʸ ρ(x, r) dr` of a `C^n` density is `C^n` on the strip. -/
private theorem contDiffOn_integral_comp_mk_left {n : ℕ∞} (hρ : ContDiffOn ℝ n ρ unitStrip) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) unitStrip := by
  have hW : UniqueDiffOn ℝ (unitStrip ×ˢ Icc (0 : ℝ) 1) :=
    uniqueDiffOn_unitStrip.prod (uniqueDiffOn_Icc zero_lt_one)
  have hmaps : MapsTo (fun q : (ℝ × ℝ) × ℝ ↦ (q.1.1, q.1.2 * q.2)) (unitStrip ×ˢ Icc (0 : ℝ) 1)
      unitStrip := by
    rintro ⟨⟨x, y⟩, t⟩ ⟨hy, ht⟩
    simp only [mem_unitStrip, mem_Icc] at hy ht ⊢
    exact ⟨mul_nonneg hy.1 ht.1, (mul_le_of_le_one_right hy.1 ht.2).trans hy.2⟩
  have hF : ContDiffOn ℝ n (fun q : (ℝ × ℝ) × ℝ ↦ q.1.2 * ρ (q.1.1, q.1.2 * q.2))
      (unitStrip ×ˢ Icc (0 : ℝ) 1) :=
    (contDiff_fst.snd.contDiffOn).mul (hρ.comp (by fun_prop) hmaps)
  refine (convex_unitStrip.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    (g := fun _ ↦ (1 : ℝ)) (integrable_const 1) continuous_subtype_val uniqueDiffOn_unitStrip hW
    hF fun p hp t ↦ ⟨hp, t.2⟩).congr fun p _ ↦ ?_
  simp [intervalIntegral_zero_eq_integral_unitInterval_smul fun r ↦ ρ (p.1, r)]

/-- **The normalization is as smooth as the density**, up to the boundary of the strip. -/
theorem contDiffOn_stripNormalization {n : ℕ∞} (hρ : ContDiffOn ℝ n ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) : ContDiffOn ℝ n (stripNormalization ρ) unitStrip :=
  (((contDiff_stripNormalizedAngle hρ).of_le le_self_add).comp contDiff_fst).contDiffOn.prodMk
    ((contDiffOn_integral_comp_mk_left hρ).div
      ((contDiff_stripColumnMass hρ).comp contDiff_fst).contDiffOn
      fun p _ ↦ (stripColumnMass_pos hρ.continuousOn hpos p.1).ne')

theorem continuousOn_stripNormalization (hρ : ContinuousOn ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) : ContinuousOn (stripNormalization ρ) unitStrip :=
  (contDiffOn_stripNormalization (n := 0) (contDiffOn_zero.2 hρ) hpos).continuousOn

/-! ### The Jacobian -/

/-- **The normalization rescales the area form `ρ dx ∧ dy` to the standard one**: for a positive
density `C^1` on the strip, at every point `p` of the strip, `a · det dΦ_p = ρ(p)`, where `a` is
the mass of the fundamental domain and the derivative is taken within the strip. -/
theorem stripMass_mul_det_fderivWithin_stripNormalization (hρ : ContDiffOn ℝ 1 ρ unitStrip)
    (hpos : ∀ p ∈ unitStrip, 0 < ρ p) {p : ℝ × ℝ} (hp : p ∈ unitStrip) :
    stripMass ρ * (fderivWithin ℝ (stripNormalization ρ) unitStrip p).det = ρ p := by
  obtain ⟨x, y⟩ := p
  have hy : y ∈ Icc (0 : ℝ) 1 := mem_unitStrip.1 hp
  have hc : ContinuousOn ρ unitStrip := hρ.continuousOn
  have hs := (stripColumnMass_pos hc hpos x).ne'
  have ha := (stripMass_pos hc hpos).ne'
  set D := fderivWithin ℝ (stripNormalization ρ) unitStrip (x, y)
  have hΦ : HasFDerivWithinAt (stripNormalization ρ) D unitStrip (x, y) :=
    ((contDiffOn_stripNormalization (n := 1) hρ hpos).differentiableOn one_ne_zero _
      hp).hasFDerivWithinAt
  -- the horizontal derivative of the first coordinate is `s(x) / a`
  have hh : (D (1, 0)).1 = stripColumnMass ρ x / stripMass ρ := by
    have hline : HasDerivAt (fun x' : ℝ ↦ ((x', y) : ℝ × ℝ)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    have hcomp := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x
      ((hΦ.comp_hasDerivWithinAt x hline.hasDerivWithinAt
        fun x' _ ↦ mem_unitStrip.2 hy).hasDerivAt univ_mem)
    exact hcomp.unique (hasDerivAt_stripNormalizedAngle hc x)
  -- the vertical derivative is `(0, ρ(x, y) / s(x))`
  have hv : D (0, 1) = (0, ρ (x, y) / stripColumnMass ρ x) := by
    have hline : HasDerivWithinAt (fun y' : ℝ ↦ ((x, y') : ℝ × ℝ)) (0, 1) (Icc 0 1) y :=
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).hasDerivWithinAt
    have hcomp := hΦ.comp_hasDerivWithinAt y hline fun y' hy' ↦ mem_unitStrip.2 hy'
    have : Fact (y ∈ Icc (0 : ℝ) 1) := ⟨hy⟩
    have hint : HasDerivWithinAt (fun y' ↦ ∫ r in (0 : ℝ)..y', ρ (x, r)) (ρ (x, y)) (Icc 0 1) y :=
      integral_hasDerivWithinAt_right
        (intervalIntegrable_comp_mk_left hc x ⟨le_rfl, zero_le_one⟩ hy)
        ((continuousOn_comp_mk_left hc x).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc y)
        (continuousOn_comp_mk_left hc x y hy)
    have hexplicit : HasDerivWithinAt (fun y' ↦ stripNormalization ρ (x, y'))
        (0, ρ (x, y) / stripColumnMass ρ x) (Icc 0 1) y :=
      (hasDerivWithinAt_const y _ (stripNormalizedAngle ρ x)).prodMk
        (hint.div_const (stripColumnMass ρ x))
    exact (uniqueDiffOn_Icc zero_lt_one y hy).eq_deriv _ hcomp hexplicit
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp only [ContinuousLinearMap.coe_coe, hh, hv]
  field_simp
  ring

/-- **Conjugating by the normalization.** Let `ρ` be a positive density `C^1` on the strip. If
`Φ ∘ F = G ∘ Φ` on the strip, where `F` maps the strip to itself, then
`ρ(F p) · det dF_p = ρ(p) · det dG_(Φ p)` at every point `p` of the strip such that `F` is
differentiable within the strip at `p` and `G` is differentiable within the strip at `Φ p`. -/
theorem mul_det_fderivWithin_eq_of_stripNormalization_conj
    (hρ : ContDiffOn ℝ 1 ρ unitStrip) (hpos : ∀ p ∈ unitStrip, 0 < ρ p) {F G : ℝ × ℝ → ℝ × ℝ}
    (hF : MapsTo F unitStrip unitStrip)
    (hconj : EqOn (stripNormalization ρ ∘ F) (G ∘ stripNormalization ρ) unitStrip)
    {p : ℝ × ℝ} (hp : p ∈ unitStrip) (hFd : DifferentiableWithinAt ℝ F unitStrip p)
    (hGd : DifferentiableWithinAt ℝ G unitStrip (stripNormalization ρ p)) :
    ρ (F p) * (fderivWithin ℝ F unitStrip p).det =
      ρ p * (fderivWithin ℝ G unitStrip (stripNormalization ρ p)).det := by
  have hΦd : DifferentiableOn ℝ (stripNormalization ρ) unitStrip :=
    (contDiffOn_stripNormalization (n := 1) hρ hpos).differentiableOn one_ne_zero
  have hchain := fderivWithin_congr' (𝕜 := ℝ) hconj hp
  rw [fderivWithin_comp p (hΦd _ (hF hp)) hFd hF (uniqueDiffOn_unitStrip p hp),
    fderivWithin_comp p hGd (hΦd p hp) (mapsTo_stripNormalization hρ.continuousOn hpos)
      (uniqueDiffOn_unitStrip p hp)] at hchain
  have hdet := congrArg ContinuousLinearMap.det hchain
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp] at hdet
  rw [← stripMass_mul_det_fderivWithin_stripNormalization hρ hpos (hF hp),
    ← stripMass_mul_det_fderivWithin_stripNormalization hρ hpos hp, mul_assoc, hdet]
  ring

/-- **Conjugating by the normalization turns `ρ dx ∧ dy` into `dx ∧ dy`.** Let `ρ` be a positive
density `C^1` on the strip. If `Φ ∘ F = G ∘ Φ` on the strip, where `F` maps the strip to itself,
then at a point `p` of the strip such that `F` is differentiable within the strip at `p` and `G`
is differentiable within the strip at `Φ p`, `G` preserves the standard area form at `Φ p` exactly
when `F` preserves `ρ dx ∧ dy` at `p`, that is `ρ(F p) · det dF_p = ρ(p)`. -/
theorem det_fderivWithin_eq_one_iff_of_stripNormalization_conj
    (hρ : ContDiffOn ℝ 1 ρ unitStrip) (hpos : ∀ p ∈ unitStrip, 0 < ρ p) {F G : ℝ × ℝ → ℝ × ℝ}
    (hF : MapsTo F unitStrip unitStrip)
    (hconj : EqOn (stripNormalization ρ ∘ F) (G ∘ stripNormalization ρ) unitStrip)
    {p : ℝ × ℝ} (hp : p ∈ unitStrip) (hFd : DifferentiableWithinAt ℝ F unitStrip p)
    (hGd : DifferentiableWithinAt ℝ G unitStrip (stripNormalization ρ p)) :
    (fderivWithin ℝ G unitStrip (stripNormalization ρ p)).det = 1 ↔
      ρ (F p) * (fderivWithin ℝ F unitStrip p).det = ρ p := by
  rw [mul_det_fderivWithin_eq_of_stripNormalization_conj hρ hpos hF hconj hp hFd hGd,
    mul_eq_left₀ (hpos p hp).ne']

end TauCeti
