/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Normalizing an area form on the strip

Let `ρ` be a positive density on the closed strip `ℝ × [0, 1]` which is invariant under the deck
translation `(x, y) ↦ (x + 1, y)` and smooth on a neighbourhood of the strip
(`TauCeti.IsStripDensity`), so that `ρ dx ∧ dy` is a positive area form on the annulus
`(ℝ / ℤ) × [0, 1]`. Put

`s(x) = ∫₀¹ ρ(x, r) dr`,  `a = ∫₀¹ s(x) dx`

(`TauCeti.stripFiberMass`, `TauCeti.stripMass`). The coordinates

`u(x) = a⁻¹ ∫₀ˣ s(t) dt`,  `v(x, y) = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr`

(`TauCeti.stripMassCoord`, `TauCeti.stripDensityNormalization`) normalize the area form:
`ρ dx ∧ dy = a du ∧ dv`. The map `Φ = (u, v)` commutes with the deck translation, maps each
boundary line of the strip to itself, increasingly, and is a diffeomorphism of the closed strip.
It is defined and smooth with nonvanishing Jacobian `ρ / a` on the open set of points joined to
the lower boundary line by a vertical segment along which `ρ` is smooth and positive
(`TauCeti.stripDensityDomain`), and injective there because `u` and `v(x, ·)` are strictly
increasing. The inverse function theorem makes it a diffeomorphism from this set onto an open
subset of the plane, which contains the strip.

Consequently, conjugating by `Φ` turns a lift `F` to the strip of a diffeomorphism of the annulus
preserving `ρ dx ∧ dy` into one preserving `dx ∧ dy`, without changing the boundary behaviour,
the deck equivariance or the fixed points in a fundamental domain. This reduces the strict
annulus fixed-point theorem (the Poincaré–Birkhoff theorem) for an arbitrary smooth area form to
the standard one (`TauCeti.IsStripDensity.exists_two_fixedPoints_of_det_eq_one`).

## Main definitions

* `TauCeti.IsStripDensity n ρ U`: `ρ` is a positive deck-invariant density on the strip, `C^n` on
  an open neighbourhood `U` of the strip.
* `TauCeti.stripDensityNormalization ρ`: the normalizing coordinates `(u, v)`.
* `TauCeti.IsStripDensity.stripDensityPartialHomeomorph`: the normalization as a homeomorphism
  between open subsets of the plane.

## Main results

* `TauCeti.IsStripDensity.stripMass_mul_det_fderiv`: `a det DΦ = ρ`, that is
  `ρ dx ∧ dy = a du ∧ dv`.
* `TauCeti.IsStripDensity.contDiffOn_stripDensityNormalization`,
  `TauCeti.IsStripDensity.contDiffOn_stripDensityPartialHomeomorph_symm`: the normalization and
  its inverse are `C^n`.
* `TauCeti.IsStripDensity.bijOn_stripDensityNormalization`: it maps the closed strip bijectively
  onto itself, and the boundary lines to themselves
  (`TauCeti.stripDensityNormalization_mk_zero`,
  `TauCeti.IsStripDensity.stripDensityNormalization_mk_one`).
* `TauCeti.IsStripDensity.stripDensityNormalization_add_one`: it commutes with the deck
  translation.
* `TauCeti.IsStripDensity.det_fderiv_conj_eq_one`: conjugation by the normalization turns maps
  preserving `ρ dx ∧ dy` into maps preserving `dx ∧ dy`.
* `TauCeti.IsStripDensity.exists_two_fixedPoints_of_det_eq_one`: the strict annulus fixed-point
  theorem for `dx ∧ dy` implies it for `ρ dx ∧ dy`.
* `TauCeti.stripDensityNormalization_one`, `TauCeti.stripDensityNormalization_one_add_snd`: the
  normalization of the constant density is the identity, and that of `1 + y` is
  `(x, y) ↦ (x, (2 y + y²) / 3)`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* P. Le Calvez and J. Wang, *Some remarks on the Poincaré–Birkhoff theorem*, Proc. Amer. Math.
  Soc. 138 (2010), 703–715.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped ContDiff Topology Interval

namespace TauCeti

/-- A positive density on the closed strip `ℝ × [0, 1]` which is invariant under the deck
translation `(x, y) ↦ (x + 1, y)`, so that `ρ dx ∧ dy` descends to a positive area form on the
annulus `(ℝ / ℤ) × [0, 1]`, and which is `C^n` on an open neighbourhood `U` of the strip. -/
structure IsStripDensity (n : ℕ∞) (ρ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop where
  isOpen : IsOpen U
  strip_subset : univ ×ˢ Icc (0 : ℝ) 1 ⊆ U
  contDiffOn : ContDiffOn ℝ n ρ U
  pos : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, 0 < ρ p
  add_one : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, ρ (p.1 + 1, p.2) = ρ p

/-- The mass `s(x) = ∫₀¹ ρ(x, r) dr` of the vertical fibre of the strip over `x`. -/
def stripFiberMass (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, ρ (x, r)

/-- The total mass `a = ∫₀¹ s(x) dx` of a fundamental domain `[0, 1] × [0, 1]` of the strip. -/
def stripMass (ρ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, stripFiberMass ρ x

/-- The horizontal normalized coordinate `u(x) = a⁻¹ ∫₀ˣ s(t) dt`, the fraction of the total mass
`a` lying over `[0, x]`. -/
def stripMassCoord (ρ : ℝ × ℝ → ℝ) (x : ℝ) : ℝ :=
  (stripMass ρ)⁻¹ * ∫ t in (0 : ℝ)..x, stripFiberMass ρ t

/-- The coordinates `(u, v)` normalizing the density `ρ` on the strip:
`u = a⁻¹ ∫₀ˣ s(t) dt` and `v = s(x)⁻¹ ∫₀ʸ ρ(x, r) dr`, where `s` is the fibre mass and `a` the
total mass. In these coordinates `ρ dx ∧ dy = a du ∧ dv`. -/
def stripDensityNormalization (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (stripMassCoord ρ p.1, (stripFiberMass ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r))

/-- The open set of points `(x, y)` such that the vertical segment from `(x, 0)` to `(x, y)` lies
in `U` and `ρ` is positive along it. It contains the strip when `ρ` is a density on the strip with
neighbourhood `U`, and the normalization of `ρ` is a diffeomorphism from it onto its image. -/
def stripDensityDomain (ρ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∀ t ∈ Icc (0 : ℝ) 1, (p.1, p.2 * t) ∈ U ∧ 0 < ρ (p.1, p.2 * t)}

variable {n : ℕ∞} {ρ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}

theorem stripFiberMass_def (ρ : ℝ × ℝ → ℝ) (x : ℝ) :
    stripFiberMass ρ x = ∫ r in (0 : ℝ)..1, ρ (x, r) :=
  (rfl)

theorem stripMass_def (ρ : ℝ × ℝ → ℝ) : stripMass ρ = ∫ x in (0 : ℝ)..1, stripFiberMass ρ x :=
  (rfl)

theorem stripMassCoord_def (ρ : ℝ × ℝ → ℝ) (x : ℝ) :
    stripMassCoord ρ x = (stripMass ρ)⁻¹ * ∫ t in (0 : ℝ)..x, stripFiberMass ρ t :=
  (rfl)

@[simp]
theorem stripDensityNormalization_fst (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (stripDensityNormalization ρ p).1 = stripMassCoord ρ p.1 :=
  (rfl)

@[simp]
theorem stripDensityNormalization_snd (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (stripDensityNormalization ρ p).2 =
      (stripFiberMass ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r) :=
  (rfl)

theorem stripDensityNormalization_def (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    stripDensityNormalization ρ p =
      (stripMassCoord ρ p.1, (stripFiberMass ρ p.1)⁻¹ * ∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) :=
  (rfl)

theorem mem_stripDensityDomain_iff {p : ℝ × ℝ} :
    p ∈ stripDensityDomain ρ U ↔ ∀ t ∈ Icc (0 : ℝ) 1, (p.1, p.2 * t) ∈ U ∧ 0 < ρ (p.1, p.2 * t) :=
  Iff.rfl

@[simp]
theorem stripMassCoord_zero (ρ : ℝ × ℝ → ℝ) : stripMassCoord ρ 0 = 0 := by
  simp [stripMassCoord_def]

/-- The normalization maps the lower boundary line `y = 0` into itself. -/
@[simp]
theorem stripDensityNormalization_mk_zero (ρ : ℝ × ℝ → ℝ) (x : ℝ) :
    stripDensityNormalization ρ (x, 0) = (stripMassCoord ρ x, 0) := by
  simp [stripDensityNormalization_def]

/-- A point of the segment `[[0, c]]` is `c * t` for some `t ∈ [0, 1]`. -/
private theorem exists_mem_Icc_eq_mul_of_mem_uIcc {c r : ℝ} (hr : r ∈ [[0, c]]) :
    ∃ t ∈ Icc (0 : ℝ) 1, r = c * t := by
  have h : [[0, c]] = (c * ·) '' Icc 0 1 := by
    rw [← uIcc_of_le zero_le_one, image_const_mul_uIcc, mul_zero, mul_one]
  obtain ⟨t, ht, rfl⟩ := h ▸ hr
  exact ⟨t, ht, rfl⟩

/-- Along the vertical segment from `(p.1, 0)` to a point `p` of the domain, `ρ` is defined and
positive. -/
theorem mem_and_pos_of_mem_stripDensityDomain {p : ℝ × ℝ} (hp : p ∈ stripDensityDomain ρ U)
    {r : ℝ} (hr : r ∈ [[0, p.2]]) : (p.1, r) ∈ U ∧ 0 < ρ (p.1, r) := by
  obtain ⟨t, ht, rfl⟩ := exists_mem_Icc_eq_mul_of_mem_uIcc hr
  exact hp t ht

/-- The domain contains, with each point, the vertical segment joining it to the lower boundary
line. -/
theorem mk_mem_stripDensityDomain {p : ℝ × ℝ} (hp : p ∈ stripDensityDomain ρ U) {r : ℝ}
    (hr : r ∈ [[0, p.2]]) : (p.1, r) ∈ stripDensityDomain ρ U := by
  obtain ⟨t₀, ht₀, rfl⟩ := exists_mem_Icc_eq_mul_of_mem_uIcc hr
  intro t ht
  have ht' : t₀ * t ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht₀.1 ht.1, by nlinarith [ht₀.1, ht₀.2, ht.1, ht.2]⟩
  simpa [mul_assoc] using hp (t₀ * t) ht'

/-- The vertical slices of the domain are intervals. -/
theorem ordConnected_stripDensityDomain_slice (x : ℝ) :
    OrdConnected {y | (x, y) ∈ stripDensityDomain ρ U} := by
  refine ⟨fun y₁ h₁ y₂ h₂ y hy ↦ ?_⟩
  rcases le_or_gt 0 y with h | h
  · exact mk_mem_stripDensityDomain h₂ (mem_uIcc.2 (Or.inl ⟨h, hy.2⟩))
  · exact mk_mem_stripDensityDomain h₁ (mem_uIcc.2 (Or.inr ⟨hy.1, h.le⟩))

namespace IsStripDensity

variable (hρ : IsStripDensity n ρ U)
include hρ

/-- A density is continuous on the closed strip. -/
theorem continuousOn_strip : ContinuousOn ρ (univ ×ˢ Icc (0 : ℝ) 1) :=
  hρ.contDiffOn.continuousOn.mono hρ.strip_subset

/-- The fibre mass of a `C^n` density is `C^n`. -/
theorem contDiff_stripFiberMass : ContDiff ℝ n (stripFiberMass ρ) := by
  have h : ContDiffOn ℝ n (Function.uncurry fun x r ↦ ρ (x, r)) (univ ×ˢ [[(0 : ℝ), 1]]) := by
    rw [uIcc_of_le zero_le_one]
    exact hρ.contDiffOn.mono hρ.strip_subset
  exact contDiffOn_univ.1 (h.parametric_intervalIntegral (μ := volume) isOpen_univ)

theorem continuous_stripFiberMass : Continuous (stripFiberMass ρ) :=
  hρ.contDiff_stripFiberMass.continuous

/-- The fibre mass of a positive density is positive. -/
theorem stripFiberMass_pos (x : ℝ) : 0 < stripFiberMass ρ x := by
  have hc : ContinuousOn (fun r ↦ ρ (x, r)) (Icc 0 1) :=
    hρ.continuousOn_strip.comp (by fun_prop) fun r hr ↦ ⟨mem_univ x, hr⟩
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (hc.intervalIntegrable_of_Icc zero_le_one) (fun r hr ↦ ?_) zero_lt_one
  exact hρ.pos (x, r) ⟨mem_univ x, Ioo_subset_Icc_self hr⟩

/-- The fibre mass is invariant under the deck translation. -/
theorem stripFiberMass_add_one (x : ℝ) : stripFiberMass ρ (x + 1) = stripFiberMass ρ x := by
  refine intervalIntegral.integral_congr fun r hr ↦ ?_
  rw [uIcc_of_le zero_le_one] at hr
  exact hρ.add_one (x, r) ⟨mem_univ x, hr⟩

theorem periodic_stripFiberMass : Function.Periodic (stripFiberMass ρ) 1 :=
  hρ.stripFiberMass_add_one

/-- The total mass of a positive density is positive. -/
theorem stripMass_pos : 0 < stripMass ρ :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (hρ.continuous_stripFiberMass.intervalIntegrable 0 1) (fun x _ ↦ hρ.stripFiberMass_pos x)
    zero_lt_one

/-! ### The horizontal coordinate -/

/-- The horizontal coordinate has derivative `s(x) / a`. -/
theorem hasDerivAt_stripMassCoord (x : ℝ) :
    HasDerivAt (stripMassCoord ρ) ((stripMass ρ)⁻¹ * stripFiberMass ρ x) x :=
  ((hρ.continuous_stripFiberMass.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul _

/-- The horizontal coordinate is strictly increasing. -/
theorem strictMono_stripMassCoord : StrictMono (stripMassCoord ρ) :=
  strictMono_of_hasDerivAt_pos hρ.hasDerivAt_stripMassCoord fun x ↦
    mul_pos (inv_pos.2 hρ.stripMass_pos) (hρ.stripFiberMass_pos x)

/-- The horizontal coordinate commutes with the deck translation. -/
theorem stripMassCoord_add_one (x : ℝ) : stripMassCoord ρ (x + 1) = stripMassCoord ρ x + 1 := by
  have h := hρ.periodic_stripFiberMass.intervalIntegral_add_eq_add 0 x
    fun a b ↦ hρ.continuous_stripFiberMass.intervalIntegrable a b
  rw [zero_add, ← stripMass_def] at h
  rw [stripMassCoord_def, stripMassCoord_def, h, mul_add, inv_mul_cancel₀ hρ.stripMass_pos.ne']

/-- The horizontal coordinate of a `C^n` density is `C^n`. -/
theorem contDiff_stripMassCoord : ContDiff ℝ n (stripMassCoord ρ) := by
  -- Rescale the variable interval `[0, x]` to `[0, 1]`.
  have h : stripMassCoord ρ = fun x ↦
      (stripMass ρ)⁻¹ * (x * ∫ t in (0 : ℝ)..1, stripFiberMass ρ (x * t)) := by
    funext x
    have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (stripFiberMass ρ) x
    simp only [smul_eq_mul, mul_zero, mul_one] at this
    rw [stripMassCoord_def, this]
  rw [h]
  have hs : ContDiff ℝ n fun z : ℝ × ℝ ↦ stripFiberMass ρ (z.1 * z.2) :=
    hρ.contDiff_stripFiberMass.comp (contDiff_fst.mul contDiff_snd)
  exact contDiff_const.mul (contDiff_id.mul (hs.parametric_intervalIntegral (μ := volume)))

theorem continuous_stripMassCoord : Continuous (stripMassCoord ρ) :=
  hρ.contDiff_stripMassCoord.continuous

/-- The horizontal coordinate is a continuous lift of a degree-one circle map, hence onto. -/
theorem stripMassCoord_surjective : Function.Surjective (stripMassCoord ρ) :=
  let f : CircleDeg1Lift :=
    { toFun := stripMassCoord ρ
      monotone' := hρ.strictMono_stripMassCoord.monotone
      map_add_one' := hρ.stripMassCoord_add_one }
  f.continuous_iff_surjective.1 hρ.continuous_stripMassCoord

theorem stripMassCoord_one : stripMassCoord ρ 1 = 1 := by
  simpa using hρ.stripMassCoord_add_one 0

/-- The horizontal coordinate maps `[0, 1)` onto itself, and its complement onto its
complement. -/
theorem stripMassCoord_mem_Ico_iff {x : ℝ} : stripMassCoord ρ x ∈ Ico 0 1 ↔ x ∈ Ico 0 1 := by
  conv_lhs => rw [← stripMassCoord_zero ρ, ← hρ.stripMassCoord_one]
  simp only [mem_Ico, hρ.strictMono_stripMassCoord.le_iff_le,
    hρ.strictMono_stripMassCoord.lt_iff_lt]

/-! ### The normalization on the strip -/

/-- The normalization maps the upper boundary line `y = 1` into itself. -/
theorem stripDensityNormalization_mk_one (x : ℝ) :
    stripDensityNormalization ρ (x, 1) = (stripMassCoord ρ x, 1) := by
  rw [stripDensityNormalization_def, ← stripFiberMass_def,
    inv_mul_cancel₀ (hρ.stripFiberMass_pos x).ne']

/-- The normalization commutes with the deck translation on the strip. -/
theorem stripDensityNormalization_add_one {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    stripDensityNormalization ρ (p.1 + 1, p.2) =
      ((stripDensityNormalization ρ p).1 + 1, (stripDensityNormalization ρ p).2) := by
  simp only [stripDensityNormalization_def, hρ.stripMassCoord_add_one, hρ.stripFiberMass_add_one]
  congr 2
  refine intervalIntegral.integral_congr fun r hr ↦ hρ.add_one (p.1, r) ⟨mem_univ _, ?_⟩
  exact uIcc_subset_Icc (left_mem_Icc.2 zero_le_one) hp.2 hr

/-! ### The domain of the normalization -/

/-- The domain of the normalization is open. -/
theorem isOpen_stripDensityDomain : IsOpen (stripDensityDomain ρ U) := by
  have hV : IsOpen (U ∩ ρ ⁻¹' Ioi 0) :=
    hρ.contDiffOn.continuousOn.isOpen_inter_preimage hρ.isOpen isOpen_Ioi
  refine isOpen_iff_eventually.2 fun p hp ↦ ?_
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦ ?_
  exact (hV.preimage (by fun_prop : Continuous fun z : (ℝ × ℝ) × ℝ ↦ (z.1.1, z.1.2 * z.2))).mem_nhds
    (hp t ht)

/-- The domain of the normalization contains the closed strip. -/
theorem strip_subset_stripDensityDomain :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ stripDensityDomain ρ U := by
  intro p hp t ht
  have hmem : (p.1, p.2 * t) ∈ univ ×ˢ Icc (0 : ℝ) 1 :=
    ⟨mem_univ _, mul_nonneg hp.2.1 ht.1, by nlinarith [hp.2.1, hp.2.2, ht.1, ht.2]⟩
  exact ⟨hρ.strip_subset hmem, hρ.pos _ hmem⟩

/-! ### Smoothness and the Jacobian -/

/-- On the domain, the partial integral `∫₀ʸ ρ(x, r) dr` has `y`-derivative `ρ(x, y)`. -/
theorem hasDerivAt_intervalIntegral {p : ℝ × ℝ} (hp : p ∈ stripDensityDomain ρ U) :
    HasDerivAt (fun y ↦ ∫ r in (0 : ℝ)..y, ρ (p.1, r)) (ρ p) p.2 := by
  have hW : IsOpen {r : ℝ | (p.1, r) ∈ U} := hρ.isOpen.preimage (by fun_prop)
  have hc : ContinuousOn (fun r ↦ ρ (p.1, r)) {r | (p.1, r) ∈ U} :=
    hρ.contDiffOn.continuousOn.comp (by fun_prop) fun r hr ↦ hr
  have hseg : [[0, p.2]] ⊆ {r | (p.1, r) ∈ U} := fun r hr ↦
    (mem_and_pos_of_mem_stripDensityDomain hp hr).1
  have hp₂ : p.2 ∈ {r | (p.1, r) ∈ U} := hseg right_mem_uIcc
  simpa using intervalIntegral.integral_hasDerivAt_right (hc.mono hseg).intervalIntegrable
    (hc.stronglyMeasurableAtFilter hW _ hp₂) (hc.continuousAt (hW.mem_nhds hp₂))

/-- The partial integral `∫₀ʸ ρ(x, r) dr` is `C^n` on the domain. -/
theorem contDiffOn_intervalIntegral :
    ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) (stripDensityDomain ρ U) := by
  -- Rescale the variable interval `[0, y]` to `[0, 1]`.
  have h : (fun p : ℝ × ℝ ↦ ∫ r in (0 : ℝ)..p.2, ρ (p.1, r)) =
      fun p ↦ p.2 * ∫ t in (0 : ℝ)..1, ρ (p.1, p.2 * t) := by
    funext p
    have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (fun r ↦ ρ (p.1, r)) p.2
    simp only [smul_eq_mul, mul_zero, mul_one] at this
    exact this.symm
  rw [h]
  have hg : ContDiffOn ℝ n (Function.uncurry fun (p : ℝ × ℝ) (t : ℝ) ↦ ρ (p.1, p.2 * t))
      (stripDensityDomain ρ U ×ˢ [[(0 : ℝ), 1]]) := by
    rw [uIcc_of_le zero_le_one]
    exact hρ.contDiffOn.comp (by fun_prop) fun z hz ↦ (hz.1 z.2 hz.2).1
  exact contDiff_snd.contDiffOn.mul
    (hg.parametric_intervalIntegral (μ := volume) hρ.isOpen_stripDensityDomain)

/-- The normalization is `C^n` on its domain. -/
theorem contDiffOn_stripDensityNormalization :
    ContDiffOn ℝ n (stripDensityNormalization ρ) (stripDensityDomain ρ U) :=
  (hρ.contDiff_stripMassCoord.comp contDiff_fst).contDiffOn.prodMk
    (((hρ.contDiff_stripFiberMass.comp contDiff_fst).contDiffOn.inv fun p _ ↦
      (hρ.stripFiberMass_pos p.1).ne').mul hρ.contDiffOn_intervalIntegral)

/-- The vertical coordinate has `y`-derivative `ρ(x, y) / s(x)` on the domain. -/
theorem hasDerivAt_stripDensityNormalization_snd {p : ℝ × ℝ}
    (hp : p ∈ stripDensityDomain ρ U) :
    HasDerivAt (fun y ↦ (stripDensityNormalization ρ (p.1, y)).2)
      ((stripFiberMass ρ p.1)⁻¹ * ρ p) p.2 :=
  (hρ.hasDerivAt_intervalIntegral hp).const_mul (stripFiberMass ρ p.1)⁻¹

/-- The vertical coordinate is strictly increasing along every vertical slice of the domain. -/
theorem strictMonoOn_stripDensityNormalization_snd (x : ℝ) :
    StrictMonoOn (fun y ↦ (stripDensityNormalization ρ (x, y)).2)
      {y | (x, y) ∈ stripDensityDomain ρ U} := by
  have hd : ∀ y ∈ {y | (x, y) ∈ stripDensityDomain ρ U},
      HasDerivAt (fun y ↦ (stripDensityNormalization ρ (x, y)).2)
        ((stripFiberMass ρ x)⁻¹ * ρ (x, y)) y := fun y hy ↦
    hρ.hasDerivAt_stripDensityNormalization_snd hy
  refine strictMonoOn_of_deriv_pos (ordConnected_stripDensityDomain_slice x).convex
    (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt) fun y hy ↦ ?_
  have hy := interior_subset hy
  rw [(hd y hy).deriv]
  exact mul_pos (inv_pos.2 (hρ.stripFiberMass_pos x))
    (mem_and_pos_of_mem_stripDensityDomain hy right_mem_uIcc).2

/-- The normalization is injective on its domain. -/
theorem injOn_stripDensityNormalization :
    InjOn (stripDensityNormalization ρ) (stripDensityDomain ρ U) := by
  intro p hp q hq h
  have h₁ : p.1 = q.1 := hρ.strictMono_stripMassCoord.injective (congrArg Prod.fst h)
  have hq' : (p.1, q.2) ∈ stripDensityDomain ρ U := by rwa [h₁]
  have h₂ : p.2 = q.2 := (hρ.strictMonoOn_stripDensityNormalization_snd p.1).injOn
    (by simpa using hp) hq' (by simpa [h₁] using congrArg Prod.snd h)
  exact Prod.ext h₁ h₂

/-- **The Jacobian of the normalization.** In the coordinates `(u, v)` the area form `ρ dx ∧ dy`
is `a du ∧ dv`: the Jacobian determinant of `(x, y) ↦ (u, v)` is `ρ(x, y) / a`. -/
theorem stripMass_mul_det_fderiv (hn : 1 ≤ n) {p : ℝ × ℝ} (hp : p ∈ stripDensityDomain ρ U) :
    stripMass ρ * (fderiv ℝ (stripDensityNormalization ρ) p).det = ρ p := by
  set D := fderiv ℝ (stripDensityNormalization ρ) p
  have hD : HasFDerivAt (stripDensityNormalization ρ) D p :=
    ((hρ.contDiffOn_stripDensityNormalization.contDiffAt
      (hρ.isOpen_stripDensityDomain.mem_nhds hp)).differentiableAt
        (by exact_mod_cast (one_pos.trans_le hn).ne')).hasFDerivAt
  -- The horizontal coordinate depends on `x` alone, with derivative `s(x) / a`.
  have h₁ : (ContinuousLinearMap.fst ℝ ℝ ℝ).comp D =
      ((stripMass ρ)⁻¹ * stripFiberMass ρ p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ :=
    (hasFDerivAt_fst.comp p hD).unique
      ((hρ.hasDerivAt_stripMassCoord p.1).comp_hasFDerivAt p hasFDerivAt_fst)
  -- The vertical coordinate has `y`-derivative `ρ(x, y) / s(x)`.
  have h₂ : (D (0, 1)).2 = (stripFiberMass ρ p.1)⁻¹ * ρ p := by
    have hγ : HasDerivAt (fun y : ℝ ↦ (p.1, y)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have := hasFDerivAt_snd.comp_hasDerivAt p.2 (hD.comp_hasDerivAt_of_eq p.2 hγ (by simp))
    exact this.unique (hρ.hasDerivAt_stripDensityNormalization_snd hp)
  have h₁₀ := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ ↦ L (1, 0)) h₁
  have h₀₁ := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ ↦ L (0, 1)) h₁
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_one, mul_zero] at h₁₀ h₀₁
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp only [ContinuousLinearMap.coe_coe, h₁₀, h₀₁, h₂, mul_zero, sub_zero]
  field_simp [hρ.stripMass_pos.ne', (hρ.stripFiberMass_pos p.1).ne']

/-- The Jacobian determinant of the normalization does not vanish on its domain. -/
theorem det_fderiv_stripDensityNormalization_ne_zero (hn : 1 ≤ n) {p : ℝ × ℝ}
    (hp : p ∈ stripDensityDomain ρ U) : (fderiv ℝ (stripDensityNormalization ρ) p).det ≠ 0 := by
  intro h
  have := hρ.stripMass_mul_det_fderiv hn hp
  rw [h, mul_zero] at this
  exact (mem_and_pos_of_mem_stripDensityDomain hp right_mem_uIcc).2.ne' (by simpa using this.symm)

/-- At every point of its domain, the normalization has an invertible strict derivative. -/
theorem hasStrictFDerivAt_stripDensityNormalization (hn : 1 ≤ n) {p : ℝ × ℝ}
    (hp : p ∈ stripDensityDomain ρ U) :
    HasStrictFDerivAt (stripDensityNormalization ρ)
      ((fderiv ℝ (stripDensityNormalization ρ) p).toContinuousLinearEquivOfDetNeZero
        (hρ.det_fderiv_stripDensityNormalization_ne_zero hn hp) : ℝ × ℝ →L[ℝ] ℝ × ℝ) p := by
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (one_pos.trans_le hn).ne'
  have hc := hρ.contDiffOn_stripDensityNormalization.contDiffAt
    (hρ.isOpen_stripDensityDomain.mem_nhds hp)
  rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  exact hc.hasStrictFDerivAt ((hc.differentiableAt hn').hasFDerivAt) hn'

/-! ### The normalization as a diffeomorphism -/

/-- The normalization of a `C^n` density, `1 ≤ n`, as a homeomorphism from its open domain onto
an open subset of the plane. It is `C^n` with `C^n` inverse
(`TauCeti.IsStripDensity.contDiffOn_stripDensityPartialHomeomorph_symm`) and restricts to a
bijection of the closed strip (`TauCeti.IsStripDensity.bijOn_stripDensityNormalization`). -/
def stripDensityPartialHomeomorph (hn : 1 ≤ n) : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hρ.injOn_stripDensityNormalization.toPartialEquiv _ _)
    hρ.contDiffOn_stripDensityNormalization.continuousOn
    (isOpenMap_iff_nhds_le.2 fun p ↦ by
      have hp : (p : ℝ × ℝ) ∈ stripDensityDomain ρ U := p.2
      rw [Set.domRestrict_eq, ← map_map, map_nhds_subtype_val]
      -- The source of the partial equivalence is the open domain itself.
      exact ((hρ.hasStrictFDerivAt_stripDensityNormalization hn hp).map_nhds_eq_of_equiv.symm.trans
        (congrArg _ (nhdsWithin_eq_nhds.2 (hρ.isOpen_stripDensityDomain.mem_nhds hp)).symm)).le)
    hρ.isOpen_stripDensityDomain

@[simp]
theorem coe_stripDensityPartialHomeomorph (hn : 1 ≤ n) :
    ⇑(hρ.stripDensityPartialHomeomorph hn) = stripDensityNormalization ρ :=
  (rfl)

@[simp]
theorem stripDensityPartialHomeomorph_source (hn : 1 ≤ n) :
    (hρ.stripDensityPartialHomeomorph hn).source = stripDensityDomain ρ U :=
  (rfl)

@[simp]
theorem stripDensityPartialHomeomorph_target (hn : 1 ≤ n) :
    (hρ.stripDensityPartialHomeomorph hn).target =
      stripDensityNormalization ρ '' stripDensityDomain ρ U :=
  (rfl)

/-- The inverse of the normalization is `C^n`. -/
theorem contDiffOn_stripDensityPartialHomeomorph_symm (hn : 1 ≤ n) :
    ContDiffOn ℝ n (hρ.stripDensityPartialHomeomorph hn).symm
      (hρ.stripDensityPartialHomeomorph hn).target := by
  intro q hq
  set e := hρ.stripDensityPartialHomeomorph hn
  have hp : e.symm q ∈ stripDensityDomain ρ U := e.map_target hq
  exact (e.contDiffAt_symm hq
    (hρ.hasStrictFDerivAt_stripDensityNormalization hn hp).hasFDerivAt
    (hρ.contDiffOn_stripDensityNormalization.contDiffAt
      (hρ.isOpen_stripDensityDomain.mem_nhds hp))).contDiffWithinAt

/-! ### The normalization of the closed strip -/

private theorem mem_slice_of_mem_Icc (x : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    y ∈ {y | (x, y) ∈ stripDensityDomain ρ U} :=
  hρ.strip_subset_stripDensityDomain ⟨mem_univ x, hy⟩

/-- The vertical coordinate `v(x, ·)` is strictly increasing on `[0, 1]`. -/
theorem strictMonoOn_stripDensityNormalization_snd_Icc (x : ℝ) :
    StrictMonoOn (fun y ↦ (stripDensityNormalization ρ (x, y)).2) (Icc 0 1) :=
  (hρ.strictMonoOn_stripDensityNormalization_snd x).mono fun _ ↦ hρ.mem_slice_of_mem_Icc x

private theorem stripDensityNormalization_snd_mk_one (x : ℝ) :
    (stripDensityNormalization ρ (x, 1)).2 = 1 := by
  rw [hρ.stripDensityNormalization_mk_one]

/-- On the strip, `v(x, y)` lies in `(0, 1)` exactly when `y` does. -/
theorem stripDensityNormalization_snd_mem_Ioo_iff {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    (stripDensityNormalization ρ p).2 ∈ Ioo 0 1 ↔ p.2 ∈ Ioo 0 1 := by
  have h := hρ.strictMonoOn_stripDensityNormalization_snd_Icc p.1
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hz : (stripDensityNormalization ρ (p.1, 0)).2 = 0 := by simp
  conv_lhs => rw [← hz,
    ← hρ.stripDensityNormalization_snd_mk_one p.1]
  simp only [mem_Ioo, ← h.lt_iff_lt h₀ hp.2, ← h.lt_iff_lt hp.2 h₁, Prod.mk.eta]

/-- The normalization maps the closed strip bijectively onto itself. -/
theorem bijOn_stripDensityNormalization :
    BijOn (stripDensityNormalization ρ) (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1) := by
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  refine ⟨fun p hp ↦ ⟨mem_univ _, ?_⟩,
    hρ.injOn_stripDensityNormalization.mono hρ.strip_subset_stripDensityDomain, ?_⟩
  · have h := (hρ.strictMonoOn_stripDensityNormalization_snd_Icc p.1).monotoneOn
    refine ⟨?_, ?_⟩
    · calc (0 : ℝ) = (stripDensityNormalization ρ (p.1, 0)).2 := by simp
        _ ≤ (stripDensityNormalization ρ p).2 := h h₀ hp.2 hp.2.1
    · calc (stripDensityNormalization ρ p).2 ≤ (stripDensityNormalization ρ (p.1, 1)).2 :=
            h hp.2 h₁ hp.2.2
        _ = 1 := hρ.stripDensityNormalization_snd_mk_one p.1
  · rintro ⟨w, z⟩ ⟨-, hz⟩
    obtain ⟨x, rfl⟩ := hρ.stripMassCoord_surjective w
    -- The vertical coordinate runs continuously from `0` to `1` along `[0, 1]`.
    have hc : ContinuousOn (fun y ↦ (stripDensityNormalization ρ (x, y)).2) (Icc 0 1) :=
      fun y hy ↦ (hρ.hasDerivAt_stripDensityNormalization_snd
        (hρ.mem_slice_of_mem_Icc x hy)).continuousAt.continuousWithinAt
    have h₀ : (stripDensityNormalization ρ (x, 0)).2 = 0 := by simp
    have h₁ := hρ.stripDensityNormalization_snd_mk_one x
    obtain ⟨y, hy, hyz⟩ := intermediate_value_Icc zero_le_one hc (by simpa only [h₀, h₁] using hz)
    exact ⟨(x, y), ⟨mem_univ x, hy⟩, Prod.ext rfl hyz⟩

/-- The image of the normalization contains the closed strip. -/
theorem strip_subset_stripDensityPartialHomeomorph_target (hn : 1 ≤ n) :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ (hρ.stripDensityPartialHomeomorph hn).target := by
  rw [stripDensityPartialHomeomorph_target, ← hρ.bijOn_stripDensityNormalization.image_eq]
  exact image_mono hρ.strip_subset_stripDensityDomain

/-- The inverse of the normalization maps the closed strip onto itself. -/
theorem mapsTo_stripDensityPartialHomeomorph_symm (hn : 1 ≤ n) :
    MapsTo (hρ.stripDensityPartialHomeomorph hn).symm (univ ×ˢ Icc (0 : ℝ) 1)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hρ.bijOn_stripDensityNormalization.surjOn hq
  rw [← coe_stripDensityPartialHomeomorph hρ hn,
    (hρ.stripDensityPartialHomeomorph hn).left_inv (hρ.strip_subset_stripDensityDomain hp)]
  exact hp

/-- A point of the strip lies in the fundamental domain `[0, 1) × (0, 1)` of the interior of the
annulus exactly when its normalization does. -/
theorem stripDensityNormalization_mem_fundamentalDomain_iff {p : ℝ × ℝ}
    (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    stripDensityNormalization ρ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ↔
      p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [mem_prod, mem_prod, stripDensityNormalization_fst, hρ.stripMassCoord_mem_Ico_iff,
    hρ.stripDensityNormalization_snd_mem_Ioo_iff hp]

/-- The inverse of the normalization commutes with the deck translation on the strip. -/
theorem stripDensityPartialHomeomorph_symm_add_one (hn : 1 ≤ n) {q : ℝ × ℝ}
    (hq : q ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    (hρ.stripDensityPartialHomeomorph hn).symm (q.1 + 1, q.2) =
      (((hρ.stripDensityPartialHomeomorph hn).symm q).1 + 1,
        ((hρ.stripDensityPartialHomeomorph hn).symm q).2) := by
  set e := hρ.stripDensityPartialHomeomorph hn
  have hp := hρ.mapsTo_stripDensityPartialHomeomorph_symm hn hq
  have hp' : ((e.symm q).1 + 1, (e.symm q).2) ∈ e.source :=
    hρ.strip_subset_stripDensityDomain ⟨mem_univ _, hp.2⟩
  have he : e (e.symm q) = q :=
    e.right_inv (hρ.strip_subset_stripDensityPartialHomeomorph_target hn hq)
  conv_lhs => rw [← he]
  rw [← e.left_inv hp']
  congr 1
  simp only [e, coe_stripDensityPartialHomeomorph] at he ⊢
  rw [hρ.stripDensityNormalization_add_one hp, he]

/-- The inverse of the normalization on the lower boundary line. -/
theorem stripDensityPartialHomeomorph_symm_mk_zero (hn : 1 ≤ n) (x : ℝ) :
    (hρ.stripDensityPartialHomeomorph hn).symm (stripMassCoord ρ x, 0) = (x, 0) := by
  rw [← stripDensityNormalization_mk_zero, ← hρ.coe_stripDensityPartialHomeomorph hn,
    OpenPartialHomeomorph.left_inv _ (hρ.strip_subset_stripDensityDomain ⟨mem_univ x, by simp⟩)]

/-- The inverse of the normalization on the upper boundary line. -/
theorem stripDensityPartialHomeomorph_symm_mk_one (hn : 1 ≤ n) (x : ℝ) :
    (hρ.stripDensityPartialHomeomorph hn).symm (stripMassCoord ρ x, 1) = (x, 1) := by
  rw [← hρ.stripDensityNormalization_mk_one, ← hρ.coe_stripDensityPartialHomeomorph hn,
    OpenPartialHomeomorph.left_inv _ (hρ.strip_subset_stripDensityDomain ⟨mem_univ x, by simp⟩)]

/-- The inverse of the normalization maps the fundamental domain `[0, 1) × (0, 1)` of the
interior of the annulus into itself. -/
theorem mapsTo_stripDensityPartialHomeomorph_symm_fundamentalDomain (hn : 1 ≤ n) :
    MapsTo (hρ.stripDensityPartialHomeomorph hn).symm (Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
      (Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  intro p hp
  have hpS : p ∈ univ ×ˢ Icc (0 : ℝ) 1 := ⟨mem_univ _, Ioo_subset_Icc_self hp.2⟩
  rw [← hρ.stripDensityNormalization_mem_fundamentalDomain_iff
      (hρ.mapsTo_stripDensityPartialHomeomorph_symm hn hpS),
    ← hρ.coe_stripDensityPartialHomeomorph hn,
    OpenPartialHomeomorph.right_inv _ (hρ.strip_subset_stripDensityPartialHomeomorph_target hn hpS)]
  exact hp

/-! ### Conjugating area-preserving maps -/

/-- **Conjugation to the standard area form.** If a map `F` preserves the area form `ρ dx ∧ dy`
at `q`, that is `ρ(F q) det DF_q = ρ(q)`, then its conjugate `Φ ∘ F ∘ Φ⁻¹` by the normalization
`Φ` preserves `dx ∧ dy` at `Φ q`. -/
theorem det_fderiv_conj_eq_one (hn : 1 ≤ n) {F : ℝ × ℝ → ℝ × ℝ} {q : ℝ × ℝ}
    (hq : q ∈ stripDensityDomain ρ U) (hFq : F q ∈ stripDensityDomain ρ U)
    (hF : DifferentiableAt ℝ F q) (harea : ρ (F q) * (fderiv ℝ F q).det = ρ q) :
    (fderiv ℝ (stripDensityNormalization ρ ∘ F ∘ (hρ.stripDensityPartialHomeomorph hn).symm)
      (stripDensityNormalization ρ q)).det = 1 := by
  set e := hρ.stripDensityPartialHomeomorph hn
  set A := (fderiv ℝ (stripDensityNormalization ρ) q).toContinuousLinearEquivOfDetNeZero
    (hρ.det_fderiv_stripDensityNormalization_ne_zero hn hq)
  have hq' : e.symm (stripDensityNormalization ρ q) = q := e.left_inv hq
  have hsymm : HasFDerivAt e.symm (A.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) (stripDensityNormalization ρ q) :=
    e.hasFDerivAt_symm (e.map_source hq) (by
      rw [hq']; exact (hρ.hasStrictFDerivAt_stripDensityNormalization hn hq).hasFDerivAt)
  have hΦF : HasFDerivAt (stripDensityNormalization ρ ∘ F)
      ((fderiv ℝ (stripDensityNormalization ρ) (F q)).comp (fderiv ℝ F q))
      (e.symm (stripDensityNormalization ρ q)) := by
    rw [hq']
    exact ((hρ.contDiffOn_stripDensityNormalization.contDiffAt
      (hρ.isOpen_stripDensityDomain.mem_nhds hFq)).differentiableAt
        (by exact_mod_cast (one_pos.trans_le hn).ne')).hasFDerivAt.comp q hF.hasFDerivAt
  have hcomp := hΦF.comp (stripDensityNormalization ρ q) hsymm
  have hdet_comp (L M : ℝ × ℝ →L[ℝ] ℝ × ℝ) : (L.comp M).det = L.det * M.det := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  rw [← Function.comp_assoc, hcomp.fderiv, hdet_comp, hdet_comp,
    ContinuousLinearEquiv.det_coe_symm, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  have h₁ := hρ.stripMass_mul_det_fderiv hn hFq
  have h₂ := hρ.stripMass_mul_det_fderiv hn hq
  have hdet := hρ.det_fderiv_stripDensityNormalization_ne_zero hn hq
  field_simp
  -- Multiply by the total mass and use the Jacobians of the normalization at `q` and `F q`.
  refine mul_left_cancel₀ hρ.stripMass_pos.ne' ?_
  linear_combination (fderiv ℝ F q).det * h₁ + harea - h₂

omit hρ in
/-- **Reduction of the strict annulus fixed-point theorem to the standard area form.**

Suppose every lift `G` to the strip of a smooth diffeomorphism of the closed annulus which
commutes with the deck translation, preserves `dx ∧ dy` and each boundary circle, and displaces
the two boundary circles strictly in opposite directions, has two fixed points which are distinct
points of the interior of the annulus. Then so does every such lift `F` preserving the area form
`ρ dx ∧ dy` of a smooth positive invariant density `ρ`.

The map `G` is the conjugate of `F` by the normalization of `ρ`, which takes `ρ dx ∧ dy` to a
constant multiple of `dx ∧ dy`, preserves both boundary lines, commutes with the deck translation
and is increasing on the boundary lines. -/
theorem exists_two_fixedPoints_of_det_eq_one (hρ : IsStripDensity ⊤ ρ U)
    (H : ∀ G : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      univ ×ˢ Icc (0 : ℝ) 1 ⊆ G.source → univ ×ˢ Icc (0 : ℝ) 1 ⊆ G.target →
      ContDiffOn ℝ ∞ G G.source → ContDiffOn ℝ ∞ G.symm G.target →
      MapsTo G (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1) →
      MapsTo G.symm (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1) →
      (∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, G (p.1 + 1, p.2) = ((G p).1 + 1, (G p).2)) →
      (∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ G p).det = 1) →
      (∀ x : ℝ, (G (x, 0)).2 = 0 ∧ (G (x, 0)).1 < x) →
      (∀ x : ℝ, (G (x, 1)).2 = 1 ∧ x < (G (x, 1)).1) →
      ∃ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∃ q ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        p ≠ q ∧ G p = p ∧ G q = q)
    (F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (hsource : univ ×ˢ Icc (0 : ℝ) 1 ⊆ F.source) (htarget : univ ×ˢ Icc (0 : ℝ) 1 ⊆ F.target)
    (hsmooth : ContDiffOn ℝ ∞ F F.source) (hinverse : ContDiffOn ℝ ∞ F.symm F.target)
    (hstrip : MapsTo F (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1))
    (hstrip_inv : MapsTo F.symm (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ Icc (0 : ℝ) 1))
    (hdeck : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, F (p.1 + 1, p.2) = ((F p).1 + 1, (F p).2))
    (harea : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, ρ (F p) * (fderiv ℝ F p).det = ρ p)
    (hlower : ∀ x : ℝ, (F (x, 0)).2 = 0 ∧ (F (x, 0)).1 < x)
    (hupper : ∀ x : ℝ, (F (x, 1)).2 = 1 ∧ x < (F (x, 1)).1) :
    ∃ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∃ q ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      p ≠ q ∧ F p = p ∧ F q = q := by
  set S : Set (ℝ × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  have hn : (1 : ℕ∞) ≤ ⊤ := le_top
  set e := hρ.stripDensityPartialHomeomorph hn
  have heS : S ⊆ e.source := hρ.strip_subset_stripDensityDomain
  have heT : S ⊆ e.target := hρ.strip_subset_stripDensityPartialHomeomorph_target hn
  have he : MapsTo e S S := hρ.bijOn_stripDensityNormalization.mapsTo
  have he' : MapsTo e.symm S S := hρ.mapsTo_stripDensityPartialHomeomorph_symm hn
  set G := (e.symm.trans F).trans e
  have hG : ∀ p, G p = e (F (e.symm p)) := fun p ↦ rfl
  have hGsymm : ∀ p, G.symm p = e (F.symm (e.symm p)) := fun p ↦ by simp [G]
  have hGsrc : ∀ p, p ∈ G.source ↔
      p ∈ e.target ∧ e.symm p ∈ F.source ∧ F (e.symm p) ∈ e.source := fun p ↦ by
    simp [G, and_assoc]
  have hGtgt : ∀ p, p ∈ G.target ↔
      p ∈ e.target ∧ e.symm p ∈ F.target ∧ F.symm (e.symm p) ∈ e.source := fun p ↦ by
    simp [G]
  -- The conjugate satisfies the hypotheses for the standard area form.
  have hGS : S ⊆ G.source := fun p hp ↦
    (hGsrc p).2 ⟨heT hp, hsource (he' hp), heS (hstrip (he' hp))⟩
  have hGT : S ⊆ G.target := fun p hp ↦
    (hGtgt p).2 ⟨heT hp, htarget (he' hp), heS (hstrip_inv (he' hp))⟩
  have hsymm := hρ.contDiffOn_stripDensityPartialHomeomorph_symm hn
  have hGsmooth : ContDiffOn ℝ ∞ G G.source := by
    have h := hρ.contDiffOn_stripDensityNormalization.comp
      (hsmooth.comp (hsymm.mono fun p hp ↦ ((hGsrc p).1 hp).1) fun p hp ↦ ((hGsrc p).1 hp).2.1)
      fun p hp ↦ ((hGsrc p).1 hp).2.2
    exact h.congr fun p _ ↦ hG p
  have hGinv : ContDiffOn ℝ ∞ G.symm G.target := by
    have h := hρ.contDiffOn_stripDensityNormalization.comp
      (hinverse.comp (hsymm.mono fun p hp ↦ ((hGtgt p).1 hp).1) fun p hp ↦ ((hGtgt p).1 hp).2.1)
      fun p hp ↦ ((hGtgt p).1 hp).2.2
    exact h.congr fun p _ ↦ hGsymm p
  have hGstrip : MapsTo G S S := fun p hp ↦ he (hstrip (he' hp))
  have hGstrip_inv : MapsTo G.symm S S := fun p hp ↦ by
    rw [hGsymm]; exact he (hstrip_inv (he' hp))
  have hGdeck : ∀ p ∈ S, G (p.1 + 1, p.2) = ((G p).1 + 1, (G p).2) := fun p hp ↦ by
    rw [hG, hG, hρ.stripDensityPartialHomeomorph_symm_add_one hn hp, hdeck _ (he' hp)]
    exact hρ.stripDensityNormalization_add_one (hstrip (he' hp))
  have hGarea : ∀ p ∈ S, (fderiv ℝ G p).det = 1 := fun p hp ↦ by
    have hq := he' hp
    have hpq : stripDensityNormalization ρ (e.symm p) = p := e.right_inv (heT hp)
    have h := hρ.det_fderiv_conj_eq_one hn (heS hq) (heS (hstrip hq))
      ((hsmooth.contDiffAt (F.open_source.mem_nhds (hsource hq))).differentiableAt
        (by simp)) (harea _ hq)
    rwa [hpq] at h
  -- On the boundary lines the normalization is the increasing map `u`.
  have hGlower : ∀ x : ℝ, (G (x, 0)).2 = 0 ∧ (G (x, 0)).1 < x := fun x ↦ by
    obtain ⟨x₀, rfl⟩ := hρ.stripMassCoord_surjective x
    have hF₀ : F (x₀, 0) = ((F (x₀, 0)).1, 0) := Prod.ext rfl (hlower x₀).1
    rw [hG, hρ.stripDensityPartialHomeomorph_symm_mk_zero hn, hF₀]
    simpa [e] using hρ.strictMono_stripMassCoord (hlower x₀).2
  have hGupper : ∀ x : ℝ, (G (x, 1)).2 = 1 ∧ x < (G (x, 1)).1 := fun x ↦ by
    obtain ⟨x₀, rfl⟩ := hρ.stripMassCoord_surjective x
    have hF₁ : F (x₀, 1) = ((F (x₀, 1)).1, 1) := Prod.ext rfl (hupper x₀).1
    rw [hG, hρ.stripDensityPartialHomeomorph_symm_mk_one hn, hF₁]
    simpa [e, hρ.stripDensityNormalization_mk_one] using
      hρ.strictMono_stripMassCoord (hupper x₀).2
  obtain ⟨p, hp, q, hq, hpq, hGp, hGq⟩ :=
    H G hGS hGT hGsmooth hGinv hGstrip hGstrip_inv hGdeck hGarea hGlower hGupper
  -- Fixed points of the conjugate are images of fixed points of `F`.
  have hfix : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, G p = p →
      e.symm p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∧ F (e.symm p) = e.symm p := fun p hp hGp ↦ by
    refine ⟨hρ.mapsTo_stripDensityPartialHomeomorph_symm_fundamentalDomain hn hp, ?_⟩
    rw [← e.left_inv (heS (hstrip (he' ⟨mem_univ _, Ioo_subset_Icc_self hp.2⟩)))]
    exact congrArg e.symm hGp
  obtain ⟨hp', hFp⟩ := hfix p hp hGp
  obtain ⟨hq', hFq⟩ := hfix q hq hGq
  refine ⟨e.symm p, hp', e.symm q, hq', fun h ↦ hpq ?_, hFp, hFq⟩
  exact e.symm.injOn (heT ⟨mem_univ _, Ioo_subset_Icc_self hp.2⟩)
    (heT ⟨mem_univ _, Ioo_subset_Icc_self hq.2⟩) h

end IsStripDensity

/-! ### Examples -/

/-- The standard area form: the constant density `1`. -/
theorem isStripDensity_one : IsStripDensity n (fun _ ↦ (1 : ℝ)) univ :=
  ⟨isOpen_univ, subset_univ _, contDiffOn_const, fun _ _ ↦ one_pos, fun _ _ ↦ rfl⟩

/-- The normalization of the standard area form is the identity. -/
@[simp]
theorem stripDensityNormalization_one : stripDensityNormalization (fun _ ↦ (1 : ℝ)) = id := by
  funext p
  simp [stripDensityNormalization_def, stripMassCoord_def, stripMass_def, stripFiberMass_def]

/-- The density `1 + y`, which is not constant along the fibres. -/
theorem isStripDensity_one_add_snd : IsStripDensity n (fun p : ℝ × ℝ ↦ 1 + p.2) univ :=
  ⟨isOpen_univ, subset_univ _, (contDiff_const.add contDiff_snd).contDiffOn,
    fun p hp ↦ by linarith [hp.2.1], fun _ _ ↦ rfl⟩

/-- The normalization of the density `1 + y` has fibre mass and total mass `3 / 2`, and is
`(x, y) ↦ (x, (2 y + y²) / 3)`. -/
theorem stripDensityNormalization_one_add_snd (p : ℝ × ℝ) :
    stripDensityNormalization (fun q : ℝ × ℝ ↦ 1 + q.2) p = (p.1, (2 * p.2 + p.2 ^ 2) / 3) := by
  have hint (y : ℝ) : ∫ r in (0 : ℝ)..y, (1 + r) = y + y ^ 2 / 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    simp [integral_id]
  have hs (x : ℝ) : stripFiberMass (fun q : ℝ × ℝ ↦ 1 + q.2) x = 3 / 2 := by
    rw [stripFiberMass_def, hint]; norm_num
  have ha : stripMass (fun q : ℝ × ℝ ↦ 1 + q.2) = 3 / 2 := by
    simp [stripMass_def, hs]
  rw [stripDensityNormalization_def, stripMassCoord_def, ha]
  simp only [hs, hint, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ext <;> simp <;> ring

end TauCeti
