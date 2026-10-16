/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.BranchValues
public import TauCeti.Geometry.Manifold.Instances.OnePoint

/-!
# The power maps of the Riemann sphere

For `n ≠ 0`, the power map `z ↦ z ^ n` of `ℂ` extends to the Riemann sphere `OnePoint ℂ` by
sending `∞` to `∞`; this extension is Mathlib's `OnePoint.map`. In the affine chart it is
`z ↦ z ^ n`, and in the inverted chart at `∞` it is again `w ↦ w ^ n`, because
`(w⁻¹ ^ n)⁻¹ = w ^ n`. So it is holomorphic, it has local multiplicity `n` at `0` and at `∞`, and
local multiplicity `1` everywhere else, where its derivative `n z ^ (n - 1)` does not vanish.

Its fibre over `0` is the single point `0`, so its degree is `n`, and its only possible branch
values are `0` and `∞`. Together with the identity (`n = 1`), these are the simplest finite
holomorphic maps of the sphere, and the basic examples of branched covers of the sphere with
few branch values: `z ↦ z ^ n` is the local model of every branched cover near a ramification
point of index `n`.

## Main declarations

* `TauCeti.RiemannSurface.mdifferentiable_onePointMap_pow`: the extension of `z ↦ z ^ n` to the
  Riemann sphere is holomorphic.
* `TauCeti.RiemannSurface.localMultiplicity_onePointMap_pow_zero`,
  `TauCeti.RiemannSurface.localMultiplicity_onePointMap_pow_infty`,
  `TauCeti.RiemannSurface.localMultiplicity_onePointMap_pow_coe_of_ne_zero`: its local
  multiplicities are `n` at `0` and `∞`, and `1` elsewhere.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.spherePow`: the power map as a finite holomorphic
  map of the Riemann sphere.
* `TauCeti.RiemannSurface.degree_onePointMap_pow`: it has degree `n`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.branchValues_spherePow_subset`: its branch values
  lie in `{0, ∞}`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1.5 (c) (the charts of the Riemann sphere) and §2 (the local behaviour of
  holomorphic maps, `z ↦ z ^ k`).
-/

public noncomputable section

open Filter Function OnePoint Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {n : ℕ}

/-- In the inverted chart at `∞`, the extension of `z ↦ z ^ n` to the Riemann sphere is again
`w ↦ w ^ n`. -/
theorem invChart_onePointMap_pow_invChart_symm (hn : n ≠ 0) (w : ℂ) :
    invChart (OnePoint.map (fun z : ℂ ↦ z ^ n) (invChart.symm w)) = w ^ n := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [zero_pow hn]
  · simp [hw, inv_pow]

/-- Near `∞`, the extension of `z ↦ z ^ n` to the Riemann sphere is `w ↦ w ^ n` read in the
inverted chart. -/
private theorem onePointMap_pow_eventuallyEq_infty (hn : n ≠ 0) :
    (OnePoint.map fun z : ℂ ↦ z ^ n) =ᶠ[𝓝 (∞ : OnePoint ℂ)]
      ((invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm ∘ (fun w : ℂ ↦ w ^ n) ∘
        invChart) := by
  filter_upwards [invChart.open_source.mem_nhds (by simp : (∞ : OnePoint ℂ) ∈ invChart.source)]
    with x hx
  have hfx : OnePoint.map (fun z : ℂ ↦ z ^ n) x ∈ invChart.source := by
    induction x using OnePoint.rec with
    | infty => simp
    | coe z =>
      have hz : z ≠ 0 := by simpa using hx
      simpa using fun h ↦ hz (pow_eq_zero_iff hn |>.1 (coe_injective h))
  rw [comp_apply, comp_apply, ← invChart_onePointMap_pow_invChart_symm hn, invChart.left_inv hx,
    invChart.left_inv hfx]

/-- **The power maps of the Riemann sphere are holomorphic.** For `n ≠ 0`, the extension of
`z ↦ z ^ n` to `OnePoint ℂ`, sending `∞` to `∞`, is holomorphic. -/
theorem mdifferentiable_onePointMap_pow (hn : n ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (OnePoint.map fun z : ℂ ↦ z ^ n) := by
  intro x
  induction x using OnePoint.rec with
  | infty =>
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ (onePointMap_pow_eventuallyEq_infty hn)
    exact (mdifferentiableAt_atlas_symm (Or.inr rfl) (by simp)).comp _
      ((differentiableAt_pow n).mdifferentiableAt.comp _
        (mdifferentiableAt_atlas (Or.inr rfl) (by simp)))
  | coe z =>
    -- Off `∞`, the map is `z ↦ z ^ n` read in the affine chart.
    have h : (OnePoint.map fun z : ℂ ↦ z ^ n) =ᶠ[𝓝 (z : OnePoint ℂ)]
        (((↑) : ℂ → OnePoint ℂ) ∘ (fun w : ℂ ↦ w ^ n) ∘ affineChart) := by
      filter_upwards [affineChart.open_source.mem_nhds
        (by simp : (z : OnePoint ℂ) ∈ affineChart.source)] with x hx
      induction x using OnePoint.rec with
      | infty => simp at hx
      | coe w => simp
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ h
    exact ((contMDiff_coe _).mdifferentiableAt (by simp)).comp _
      ((differentiableAt_pow n).mdifferentiableAt.comp _
        (mdifferentiableAt_atlas (Or.inl rfl) (by simp)))

/-- At a finite point `z`, the local multiplicity of the extension of `z ↦ z ^ n` to the Riemann
sphere is the order of vanishing of `w ↦ w ^ n - z ^ n` at `z`: both charts are the affine
chart. -/
private theorem localMultiplicity_onePointMap_pow_coe (z : ℂ) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (z : OnePoint ℂ) =
      analyticOrderNatAt (fun w ↦ w ^ n - z ^ n) z := by
  simp [localMultiplicity_def]

/-- The extension of `z ↦ z ^ n` to the Riemann sphere has local multiplicity `n` at `0`. -/
@[simp]
theorem localMultiplicity_onePointMap_pow_zero :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) ((0 : ℂ) : OnePoint ℂ) = n := by
  simpa [localMultiplicity_onePointMap_pow_coe] using localMultiplicity_pow_zero n

/-- The extension of `z ↦ z ^ n` to the Riemann sphere has local multiplicity `n` at `∞`, where
it is `w ↦ w ^ n` in the inverted chart. -/
@[simp]
theorem localMultiplicity_onePointMap_pow_infty (hn : n ≠ 0) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (∞ : OnePoint ℂ) = n := by
  simpa [localMultiplicity_def, invChart_onePointMap_pow_invChart_symm hn, zero_pow hn] using
    localMultiplicity_pow_zero n

/-- Away from `0` and `∞`, the extension of `z ↦ z ^ n` to the Riemann sphere has local
multiplicity `1`: there the derivative `n z ^ (n - 1)` does not vanish. -/
theorem localMultiplicity_onePointMap_pow_coe_of_ne_zero (hn : n ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (z : OnePoint ℂ) = 1 := by
  rw [localMultiplicity_onePointMap_pow_coe, analyticOrderNatAt,
    (analyticAt_id.pow n).analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp [hn, hz]),
    ENat.toNat_one]

namespace FiniteHolomorphicMap

/-- The **power map** `z ↦ z ^ n` of the Riemann sphere, for `n ≠ 0`, sending `∞` to `∞`, as a
finite holomorphic map. -/
def spherePow (hn : n ≠ 0) : FiniteHolomorphicMap (OnePoint ℂ) (OnePoint ℂ) :=
  .ofMDifferentiable (mdifferentiable_onePointMap_pow hn)
    ⟨(0 : ℂ), ∞, by simp⟩

@[simp]
theorem coe_spherePow (hn : n ≠ 0) :
    ⇑(spherePow hn) = OnePoint.map fun z : ℂ ↦ z ^ n :=
  coe_ofMDifferentiable _ _

/-- The branch values of the power map `z ↦ z ^ n` of the Riemann sphere lie in `{0, ∞}`. -/
theorem branchValues_spherePow_subset (hn : n ≠ 0) :
    (spherePow hn).branchValues ⊆ {((0 : ℂ) : OnePoint ℂ), ∞} := by
  intro y hy
  obtain ⟨x, rfl, hx⟩ := (mem_branchValues_iff _ _).1 hy
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · simp [zero_pow hn]
    · simp [localMultiplicity_onePointMap_pow_coe_of_ne_zero hn hz] at hx

end FiniteHolomorphicMap

open FiniteHolomorphicMap in
/-- The power map `z ↦ z ^ n` of the Riemann sphere has degree `n`: its fibre over `0` is the
single point `0`, of local multiplicity `n`. -/
@[simp]
theorem degree_onePointMap_pow (hn : n ≠ 0) :
    degree (OnePoint.map fun z : ℂ ↦ z ^ n) = n := by
  have hfib : (OnePoint.map fun z : ℂ ↦ z ^ n) ⁻¹' {((0 : ℂ) : OnePoint ℂ)} =
      {((0 : ℂ) : OnePoint ℂ)} := by
    ext x
    induction x using OnePoint.rec with
    | infty => simp
    | coe z => simp [pow_eq_zero_iff hn]
  have hne : ∀ x, ¬ EventuallyConst (OnePoint.map fun z : ℂ ↦ z ^ n) (𝓝 x) := by
    simpa using (spherePow hn).not_eventuallyConst
  rw [← fiberMultiplicitySum_eq_degree (mdifferentiable_onePointMap_pow hn) hne
    ((0 : ℂ) : OnePoint ℂ), fiberMultiplicitySum_def, hfib, finsum_mem_singleton,
    localMultiplicity_onePointMap_pow_zero]

end TauCeti.RiemannSurface
