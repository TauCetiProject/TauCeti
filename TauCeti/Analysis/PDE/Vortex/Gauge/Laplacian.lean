/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.PDE.Vortex.Multiplier

/-!
# The gauge Laplacian of a framed plane vortex field on the Sobolev scale

At a plane vortex field `x = (b₁, b₂, p, q)`, with section `α = 2 (p + i q)`, the infinitesimal
gauge action `d₀ = TauCeti.Vortex.gaugeDirection x` and its formal adjoint
`d₀* = TauCeti.Vortex.gaugeAdjoint x` compose to the **gauge Laplacian**

`d₀* d₀ f = -Δf + (p² + q²) f = -Δf + (|α|² / 4) f`

(`TauCeti.Vortex.gaugeAdjoint_gaugeDirection`), a Schrödinger operator. Accordingly `u` is a weak
solution of `d₀* d₀ u = g`, that is `∫ u · d₀* d₀ φ = ∫ g φ` for every compactly supported smooth
`φ`, exactly when `∫ u (-Δφ + (p² + q²) φ) = ∫ g φ` for every such `φ`
(`TauCeti.Vortex.integral_mul_gaugeAdjoint_gaugeDirection`), so the results of
`TauCeti.Analysis.PDE.Schrodinger.Stationary` apply.

The potential `p² + q²` vanishes at the zeros of `α`, but for a continuous field of the affine
space `A_m^s = x_m + H^s`, `s > 1`, it tends to `1 / 4` at infinity
(`TauCeti.Vortex.tendsto_normSq_of_mem_framedFieldSpace`). This file proves that, whenever
`x` is a continuous field of `A_m^k` with `j ≤ k` and `k ≥ 2`, for every `g ∈ H^j(ℂ)` the
equation `d₀* d₀ u = g` has a weak solution in `L²(ℂ)` which is unique up to null sets and lies
in `H^(j+2)(ℂ)`.

* Uniqueness (`TauCeti.Vortex.ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq`): two weak
  solutions in `L²(ℂ)` agree almost everywhere, by the coercivity of the gauge Laplacian on
  `H¹(ℂ)` (`TauCeti.ae_eq_of_integral_mul_neg_laplacian_add_mul_eq`).
* Regularity
  (`TauCeti.Vortex.mem_realSobolevFunctions_of_integral_mul_gaugeAdjoint_gaugeDirection_eq`): a
  weak solution in `L²(ℂ)` with `g ∈ H^j(ℂ)` lies in `H^(j+2)(ℂ)`. The first step only uses that the
  potential is bounded. After that, multiplication by the coordinates `p, q` of a field of `A_m^k`
  preserves `H^n(ℂ)` for `1 < n ≤ k`
  (`TauCeti.Vortex.mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`), so the potential term
  is as regular as the solution
  (`TauCeti.Vortex.sq_add_sq_mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`), and the
  resolvent of the Laplacian gains two derivatives at each
  step (`TauCeti.mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq`).
* Existence
  (`TauCeti.Vortex.exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq`):
  for every `g ∈ H^j(ℂ)` there is a weak solution `u ∈ H^(j+2)(ℂ)`, by the existence of an `H²`
  weak solution of the Schrödinger equation
  (`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`) and the
  regularity above.

For `j = k - 1` this gives unique weak solvability of `d₀* d₀ u = g` with an `H^(k+1)(ℂ)`
solution for every `g ∈ H^(k-1)(ℂ)`, at a continuous field `x₀` of `A_m^k`. This is the analytic
input for the invertibility of the linearization at the identity of the Coulomb gauge condition
`d₀* (u · x₀ - x₀) = 0` for the action of the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`). The statements concern weak solutions as functions, not
bounded operators between completed Sobolev spaces.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution Filter Metric
open scoped Laplacian ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- At a continuous field of `A_m^s`, `s > 1`, the potential `p² + q²` of the gauge Laplacian is
bounded and at least `1 / 8` outside a disc. -/
private theorem potential_bounds {s : ℝ} (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) :
    MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ (volume : Measure ℂ) ∧
      ∃ R, ∀ z, R < ‖z‖ → 1 / 8 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by
  have hlim := tendsto_normSq_of_mem_framedFieldSpace hs hx hcont
  have hVc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have _ : Continuous fun z ↦ x z 2 := by fun_prop
    have _ : Continuous fun z ↦ x z 3 := by fun_prop
    fun_prop
  obtain ⟨R₁, -, hR₁⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  refine ⟨?_, R₁, fun z hz ↦ (hR₁ z hz).le⟩
  -- Outside a disc the potential is below `1 / 2`; inside it is bounded by compactness.
  have he := hlim.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  rw [← Metric.cobounded_eq_cocompact] at he
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp he
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hVc.continuousOn
  refine memLp_top_of_bound hVc.aestronglyMeasurable (max C (1 / 2))
    (Eventually.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ closedBall (0 : ℂ) R
  · exact (hC z hz).trans (le_max_left _ _)
  · have hzR : R ≤ ‖z‖ := (lt_of_not_ge (by simpa using hz)).le
    have h := hR hzR
    simp only [Set.mem_ofPred_eq] at h
    have h0 : 0 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact le_max_of_le_right (by linarith)

/-- At a field of `A_m^n`, `n > 1`, multiplication by the potential `p² + q²` of the gauge
Laplacian preserves `H^n(ℂ)`. -/
theorem sq_add_sq_mul_mem_realSobolevFunctions_of_mem_framedFieldSpace {n : ℕ} (hn : 1 < n)
    (hx : x ∈ framedFieldSpace f m n) {u : ℂ → ℝ} (hu : u ∈ realSobolevFunctions ℂ n 2) :
    (fun z ↦ (x z 2 ^ 2 + x z 3 ^ 2) * u z) ∈ realSobolevFunctions ℂ n 2 := by
  have h2 := mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx 2
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx 2 hu)
  have h3 := mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx 3
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx 3 hu)
  convert add_mem h2 h3 using 1
  ext z
  simp only [Pi.add_apply]
  ring

/-- **The gauge Laplacian is a Schrödinger operator.** Testing a function `u` against the gauge
Laplacian `d₀* d₀ φ` of a `C²` function `φ` is testing it against `-Δφ + (p² + q²) φ`. -/
theorem integral_mul_gaugeAdjoint_gaugeDirection {u φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z =
      ∫ z, u z * (-Δ φ z + (x z 2 ^ 2 + x z 3 ^ 2) * φ z) :=
  integral_congr_ae (Eventually.of_forall fun z ↦ by
    simp only [gaugeAdjoint_gaugeDirection x hφ.contDiffAt])

/-- **Uniqueness for the gauge Laplacian.** At a continuous field of `A_m^s`, `s > 1`, two
functions `u₁, u₂ ∈ L²(ℂ)` with `d₀* d₀ u₁ = d₀* d₀ u₂ = g` weakly, that is
`∫ uᵢ · d₀* d₀ φ = ∫ g φ` for every compactly supported smooth `φ`, agree almost everywhere. -/
theorem ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq {s : ℝ} (hs : 1 < s)
    (hx : x ∈ framedFieldSpace f m s) (hcont : Continuous x) {u₁ u₂ g : ℂ → ℝ}
    (hu₁ : MemLp u₁ 2 (volume : Measure ℂ)) (hu₂ : MemLp u₂ 2 (volume : Measure ℂ))
    (hw₁ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u₁ z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z)
    (hw₂ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u₂ z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z) :
    u₁ =ᵐ[volume] u₂ := by
  obtain ⟨hV, R, hR⟩ := potential_bounds hs hx hcont
  exact ae_eq_of_integral_mul_neg_laplacian_add_mul_eq hV (ae_of_all _ fun z ↦ by positivity)
    (by norm_num : (0 : ℝ) < 1 / 8) (ae_of_all _ hR) hu₁ hu₂
    (fun φ hφ hc ↦ by rw [← integral_mul_gaugeAdjoint_gaugeDirection (hφ.of_le (by simp)),
      hw₁ φ hφ hc])
    (fun φ hφ hc ↦ by rw [← integral_mul_gaugeAdjoint_gaugeDirection (hφ.of_le (by simp)),
      hw₂ φ hφ hc])

/-- **Elliptic regularity for the gauge Laplacian.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 2`, and `j ≤ k`. A function `u ∈ L²(ℂ)` with `d₀* d₀ u = g` weakly, for some
`g ∈ H^j(ℂ)`, lies in `H^(j+2)(ℂ)`. -/
theorem mem_realSobolevFunctions_of_integral_mul_gaugeAdjoint_gaugeDirection_eq {k j : ℕ}
    (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    {u g : ℂ → ℝ} (hu : MemLp u 2 (volume : Measure ℂ)) (hg : g ∈ realSobolevFunctions ℂ j 2)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z) :
    u ∈ realSobolevFunctions ℂ (j + 2) 2 := by
  obtain ⟨hV, -⟩ := potential_bounds (by exact_mod_cast hk) hx hcont
  -- The weak equation of the Schrödinger operator `-Δ + (p² + q²)`.
  have heq (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      ∫ z, u z * (-Δ φ z + (x z 2 ^ 2 + x z 3 ^ 2) * φ z) = ∫ z, g z * φ z := by
    rw [← integral_mul_gaugeAdjoint_gaugeDirection (hφ.of_le (by simp)), hweak φ hφ hc]
  -- Bootstrap: `u ∈ H^(n+2)` for every `n ≤ j`.
  suffices h : ∀ n ≤ j, u ∈ realSobolevFunctions ℂ ((n : ℝ) + 2) 2 from h j le_rfl
  intro n hn
  induction n with
  | zero =>
    simpa using mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq hV hu
      (memLp_of_mem_realSobolevFunctions hg) heq
  | succ n ih =>
    have hu' := ih (by omega)
    -- The potential term `(p² + q²) u` is as regular as `u`, measured at the order
    -- `N = min (n + 2) k`, which satisfies `1 < N`, `n + 1 ≤ N` and `N ≤ k`.
    obtain ⟨N, hN⟩ : ∃ N, N = min (n + 2) k := ⟨_, rfl⟩
    have hN2 : 1 < N := by omega
    have hxN : x ∈ framedFieldSpace f m (N : ℝ) :=
      framedFieldSpace_mono f m (by exact_mod_cast (by omega : N ≤ k)) hx
    have huN : u ∈ realSobolevFunctions ℂ (N : ℝ) 2 :=
      realSobolevFunctions_mono (by norm_num) (by norm_num)
        (by exact_mod_cast (by omega : N ≤ n + 2)) hu'
    have hVu : (fun z ↦ (x z 2 ^ 2 + x z 3 ^ 2) * u z) ∈
        realSobolevFunctions ℂ ((n + 1 : ℕ) : ℝ) 2 :=
      realSobolevFunctions_mono (by norm_num) (by norm_num)
        (by exact_mod_cast (by omega : n + 1 ≤ N))
        (sq_add_sq_mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hN2 hxN huN)
    have hun : u ∈ realSobolevFunctions ℂ ((n + 1 : ℕ) : ℝ) 2 :=
      realSobolevFunctions_mono (by norm_num) (by norm_num) (by push_cast; linarith) hu'
    have hgn : g ∈ realSobolevFunctions ℂ ((n + 1 : ℕ) : ℝ) 2 :=
      realSobolevFunctions_mono (by norm_num) (by norm_num) (by exact_mod_cast hn) hg
    exact_mod_cast mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq hun
      hVu hgn heq

/-- **Existence for the gauge Laplacian.** Let `x` be a continuous field of `A_m^k`, `k ≥ 2`,
and `j ≤ k`. For every `g ∈ H^j(ℂ)` there is `u ∈ H^(j+2)(ℂ)` with `d₀* d₀ u = g` weakly:
`∫ u · d₀* d₀ φ = ∫ g φ` for every compactly supported `C²` function `φ`. By
`TauCeti.Vortex.ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq` it is unique up to null
sets, even among weak solutions in `L²(ℂ)`. -/
theorem exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq {k j : ℕ}
    (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    {g : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ j 2) :
    ∃ u ∈ realSobolevFunctions ℂ (j + 2) 2, ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z := by
  obtain ⟨hV, R, hR⟩ := potential_bounds (by exact_mod_cast hk) hx hcont
  obtain ⟨u, hu, heq⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hV (ae_of_all _ fun z ↦ by positivity) (by norm_num : (0 : ℝ) < 1 / 8) (ae_of_all _ hR)
    (memLp_of_mem_realSobolevFunctions hg)
  have hweak (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z := by
    rw [integral_mul_gaugeAdjoint_gaugeDirection hφ, heq φ hφ hc]
  exact ⟨u, mem_realSobolevFunctions_of_integral_mul_gaugeAdjoint_gaugeDirection_eq hk hjk hx
    hcont (memLp_of_mem_realSobolevFunctions hu) hg fun φ hφ hc ↦ hweak φ (hφ.of_le (by simp)) hc,
    hweak⟩

end TauCeti.Vortex
