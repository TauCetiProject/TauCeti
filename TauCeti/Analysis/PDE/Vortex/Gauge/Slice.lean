/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Laplacian
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.EquationMap
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The infinitesimal Coulomb slice of the framed plane vortex fields

The framed degree-`m` plane vortex fields form the affine space `A_m^k = x_m + H^k`
(`TauCeti.Vortex.framedFieldSpace`), acted on by the Sobolev framed gauge group `G_(k+1)`. At a
field `x`, the infinitesimal gauge action `d₀ = TauCeti.Vortex.gaugeDirection x` sends a real phase
`u` to the variation `(-∂₁u, -∂₂u, -u q, u p)`, and its formal `L²` adjoint
`d₀* = TauCeti.Vortex.gaugeAdjoint x` is the Coulomb gauge-fixing operator. Their composite is the
gauge Laplacian `d₀* d₀ u = -Δu + (p² + q²) u` (`TauCeti.Vortex.gaugeAdjoint_gaugeDirection`).

This file proves that the Coulomb condition `d₀* y = 0` is a slice for the infinitesimal gauge
action on the tangent space `H^k` of `A_m^k`: every variation splits uniquely as an infinitesimal
gauge transformation plus a Coulomb variation,

`y = d₀ u + (y - d₀ u)`,  `d₀* (y - d₀ u) = 0`,  `u ∈ H^(k+1)`.

Here `x` is a continuous field of `A_m^k` and `y` a continuous variation in `H^k`, with `k ≥ 3`, so
that `y` is `C¹` by the Sobolev embedding and `d₀* y` is defined pointwise.

* **Existence** (`TauCeti.Vortex.exists_gaugeAdjoint_sub_gaugeDirection_eq_zero`). The phase `u`
  solves `d₀* d₀ u = d₀* y`. Since `d₀* y ∈ H^(k-1)`
  (`TauCeti.Vortex.gaugeAdjoint_mem_realSobolevFunctions`), the gauge Laplacian has a weak solution
  `u ∈ H^(k+1)`
  (`TauCeti.Vortex.exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq`),
  whose continuous representative is `C²`. A `C²` weak solution is a classical solution
  (`TauCeti.Vortex.gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq`), so the Coulomb condition
  holds at every point, and `d₀ u ∈ H^k` (`TauCeti.Vortex.gaugeDirection_mem_sobolevFields`).
* **Uniqueness** (`TauCeti.Vortex.existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero`). No
  nonzero infinitesimal gauge transformation is Coulomb: a `C²` solution of `d₀* d₀ u = 0` tending
  to zero at infinity vanishes (`TauCeti.Vortex.eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero`),
  and a continuous `u ∈ H^(k+1)` tends to zero at infinity by the Sobolev embedding.

At a vortex the infinitesimal gauge transformations solve the linearized equation,
`d₁ d₀ = 0` (`TauCeti.Vortex.linearizedEquation_gaugeDirection_eq_zero`). The splitting then
carries a solution `y ∈ H^k` of the linearized equation `d₁ y = 0` to the element `y - d₀ u` of the
kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.exists_gaugeFixedOperator_sub_gaugeDirection_eq_zero`). As consequences of
these results, not statements of this file: with uniqueness, the continuous solutions of
`d₁ y = 0` in `H^k` are the direct sum of the infinitesimal gauge transformations `d₀ u`,
`u ∈ H^(k+1)` continuous, and the continuous variations in `H^k` lying in the kernel of `L_x`;
so these elements of the kernel of the gauge-fixed operator represent the first cohomology
`ker d₁ / im d₀` of the deformation complex at `x`.

The statements concern the linearized gauge action on fields as functions; the nonlinear slice,
which puts a field of `A_m^k` near `x` into the Coulomb slice `d₀* (· - x) = 0` by an element of
`G_(k+1)`, is not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution Filter Topology
open scoped Laplacian ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- For `k ≥ 3`, a continuous field of `A_m^k` and a continuous variation in `H^k` are `C¹`, by
the Sobolev embedding. -/
private theorem contDiff_one_of_three_le {k : ℕ} (hk : 3 ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hxc : Continuous x) {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k)
    (hyc : Continuous y) : ContDiff ℝ 1 x ∧ ContDiff ℝ 1 y := by
  have hk1 : ((1 : ℕ) : ℝ) + 1 < k := by exact_mod_cast (by omega : 1 + 1 < k)
  refine ⟨?_, contDiff_of_mem_sobolevFields hk1 hy hyc⟩
  simpa using (contDiff_of_mem_sobolevFields hk1 (mem_framedFieldSpace.1 hx)
    (hxc.sub (contDiff_referenceField f m).continuous)).add
    ((contDiff_referenceField f m).of_le (by simp))

/-- The Coulomb defect of `y - d₀ u` is that of `y` minus the gauge Laplacian of `u`. -/
private theorem gaugeAdjoint_sub_gaugeDirection (hx : ContDiff ℝ 1 x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (z : ℂ) :
    gaugeAdjoint x (y - gaugeDirection x u) z =
      gaugeAdjoint x y z - (-Δ u z + (x z 2 ^ 2 + x z 3 ^ 2) * u z) := by
  have hx' := differentiableAt_euclidean.1 (hx.differentiable one_ne_zero z)
  have hy' := differentiableAt_euclidean.1 (hy.differentiable one_ne_zero z)
  have hdu := differentiableAt_euclidean.1
    (differentiableAt_gaugeDirection hu.contDiffAt (hx' 2) (hx' 3))
  rw [gaugeAdjoint_sub x (hy' 0) (hy' 1) (hdu 0) (hdu 1),
    gaugeAdjoint_gaugeDirection x hu.contDiffAt]

/-- **The infinitesimal Coulomb slice.** Let `x` be a continuous field of `A_m^k`, `k ≥ 3`, and `y`
a continuous variation in `H^k`. Then there is a `C²` phase `u ∈ H^(k+1)` whose infinitesimal gauge
transformation `d₀ u` lies in `H^k` and moves `y` into the Coulomb slice: `d₀* (y - d₀ u) = 0` at
every point. The phase is unique by
`TauCeti.Vortex.existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero`. -/
theorem exists_gaugeAdjoint_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hxc : Continuous x) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields k) (hyc : Continuous y) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 1) 2, ContDiff ℝ 2 u ∧
      gaugeDirection x u ∈ sobolevFields k ∧
        ∀ z, gaugeAdjoint x (y - gaugeDirection x u) z = 0 := by
  obtain ⟨hx1, hy1⟩ := contDiff_one_of_three_le hk hx hxc hy hyc
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := Nat.cast_succ n
  rw [hcast] at hx hy ⊢
  -- The source `d₀* y` lies in `H^n` and is continuous.
  have hg : gaugeAdjoint x y ∈ realSobolevFunctions ℂ n 2 :=
    gaugeAdjoint_mem_realSobolevFunctions (by omega) hx hy hy1
  have hgc : Continuous (gaugeAdjoint x y) := continuous_gaugeAdjoint hxc hy1
  -- Solve `d₀* d₀ u₀ = d₀* y` weakly with `u₀ ∈ H^(n+2)`, and take a `C²` representative `u`.
  obtain ⟨u₀, hu₀, hw₀⟩ :=
    exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq (k := n + 1)
      (j := n) (by omega) (by omega) (by exact_mod_cast hx) hxc hg
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  obtain ⟨u, hu2, hu₀u⟩ := exists_contDiff_ae_eq_of_mem_realSobolevFunctions (k := 2)
    (by rw [Complex.finrank_real_complex]; push_cast; linarith) hu₀
  have hu : u ∈ realSobolevFunctions ℂ (n + 2) 2 := mem_realSobolevFunctions_of_ae_eq hu₀ hu₀u
  have hw (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, gaugeAdjoint x y z * φ z := by
    rw [← hw₀ φ (hφ.of_le (by simp)) hφc]
    exact integral_congr_ae (hu₀u.mono fun z hz ↦ by simp only [hz])
  have hcl := gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq hxc hu2 hgc hw
  refine ⟨u, by convert hu using 2; ring, hu2,
    gaugeDirection_mem_sobolevFields (by omega) hx (by convert hu using 2) (hu2.of_le one_le_two),
    fun z ↦ ?_⟩
  rw [gaugeAdjoint_sub_gaugeDirection hx1 hy1 hu2, ← gaugeAdjoint_gaugeDirection x hu2.contDiffAt,
    hcl z, sub_self]

/-- **Uniqueness of the infinitesimal Coulomb slice.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`, and `y` a continuous variation in `H^k`. Exactly one continuous phase `u ∈ H^(k+1)`
satisfies `d₀* (y - d₀ u) = 0` at every point. -/
theorem existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hxc : Continuous x) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields k) (hyc : Continuous y) :
    ∃! u : ℂ → ℝ, (u ∈ realSobolevFunctions ℂ (k + 1) 2 ∧ Continuous u) ∧
      ∀ z, gaugeAdjoint x (y - gaugeDirection x u) z = 0 := by
  obtain ⟨u, hu, hu2, -, hcoul⟩ := exists_gaugeAdjoint_sub_gaugeDirection_eq_zero hk hx hxc hy hyc
  refine ⟨u, ⟨⟨hu, hu2.continuous⟩, hcoul⟩, fun v ⟨⟨hv, hvc⟩, hvcoul⟩ ↦ ?_⟩
  -- A continuous phase in `H^(k+1)` is `C²` and tends to zero at infinity.
  have hs : (Module.finrank ℝ ℂ : ℝ) + 2 * 2 < 2 * (k + 1) := by
    rw [Complex.finrank_real_complex]
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith
  have hv2 : ContDiff ℝ 2 v := contDiff_of_mem_realSobolevFunctions hs hv hvc
  have hlim (w : ℂ → ℝ) (hw : w ∈ realSobolevFunctions ℂ (k + 1) 2) (hwc : Continuous w) :
      Tendsto w (cocompact ℂ) (𝓝 0) :=
    tendsto_cocompact_of_mem_realSobolevFunctions (by linarith) hw hwc
  obtain ⟨hx1, hy1⟩ := contDiff_one_of_three_le hk hx hxc hy hyc
  -- The difference `v - u` is an infinitesimal gauge transformation in the Coulomb slice.
  have hdiff : ∀ z, gaugeAdjoint x (gaugeDirection x (v - u)) z = 0 := by
    intro z
    have h₁ := hvcoul z
    have h₂ := hcoul z
    rw [gaugeAdjoint_sub_gaugeDirection hx1 hy1 hv2] at h₁
    rw [gaugeAdjoint_sub_gaugeDirection hx1 hy1 hu2] at h₂
    rw [gaugeAdjoint_gaugeDirection (f := v - u) x (hv2.sub hu2).contDiffAt,
      hv2.contDiffAt.laplacian_sub hu2.contDiffAt, Pi.sub_apply]
    linear_combination h₂ - h₁
  have h0 := eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero x (hv2.sub hu2)
    (by simpa using (hlim v hv hvc).sub (hlim u hu hu2.continuous)) hdiff
  exact sub_eq_zero.1 h0

/-- **Every linearized solution is gauge-equivalent to an element of `ker L_x`.** Let `x` be a
continuous vortex of `A_m^k`, `k ≥ 3`, and `y` a continuous variation in `H^k` solving the
linearized equation `d₁ y = 0`. Then there is a `C²` phase `u ∈ H^(k+1)`, with `d₀ u ∈ H^k`, such
that `y - d₀ u` lies in the kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`. Among continuous
phases in `H^(k+1)` this `u` is unique
(`TauCeti.Vortex.existsUnique_gaugeAdjoint_sub_gaugeDirection_eq_zero`); in particular no nonzero
`d₀ v` with `v` continuous in `H^(k+1)` lies in `ker L_x`. -/
theorem exists_gaugeFixedOperator_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hxc : Continuous x) (hsol : ∀ z, equation x z = 0)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) (hyc : Continuous y)
    (hlin : ∀ z, linearizedEquation x y z = 0) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 1) 2, ContDiff ℝ 2 u ∧
      gaugeDirection x u ∈ sobolevFields k ∧
        ∀ z, gaugeFixedOperator x (y - gaugeDirection x u) z = 0 := by
  obtain ⟨u, hu, hu2, hdu, hcoul⟩ :=
    exists_gaugeAdjoint_sub_gaugeDirection_eq_zero hk hx hxc hy hyc
  refine ⟨u, hu, hu2, hdu, fun z ↦ ?_⟩
  obtain ⟨hx1, hy1⟩ := contDiff_one_of_three_le hk hx hxc hy hyc
  have hxi := differentiableAt_euclidean.1 (hx1.differentiable one_ne_zero z)
  -- `L_x` is additive, and `L_x (d₀ u)` has vanishing equation rows since `d₁ d₀ = 0`.
  have hsplit := gaugeFixedOperator_sub x (hy1.differentiable one_ne_zero z)
    (differentiableAt_gaugeDirection hu2.contDiffAt (hxi 2) (hxi 3))
  have hL := linearizedEquation_gaugeDirection_eq_zero (hxi 2) (hxi 3) hu2.contDiffAt (hsol z)
  ext i
  fin_cases i
  · simpa using hcoul z
  all_goals simp [hsplit, hlin z, hL]

end TauCeti.Vortex
