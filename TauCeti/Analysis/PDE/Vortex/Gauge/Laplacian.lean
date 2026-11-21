/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
public import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Measure.Restrict

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
* Classical solutions
  (`TauCeti.Vortex.gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq`): a `C²` weak solution with
  continuous `g` solves `d₀* d₀ u = g` at every point. A `C²` solution of `d₀* d₀ u = 0` tending to
  zero at infinity vanishes, at any field
  (`TauCeti.Vortex.eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero`), since `Δu = (p² + q²) u` gives
  `u Δu ≥ 0` and the weak maximum principle applies.

For `j = k - 1` this gives unique weak solvability of `d₀* d₀ u = g` with an `H^(k+1)(ℂ)`
solution for every `g ∈ H^(k-1)(ℂ)`, at a continuous field `x₀` of `A_m^k`.

These statements concern weak solutions as functions. On the completed Sobolev spaces
`W^{n,2}(ℂ) = H^n(ℂ)` (`TauCeti.Wkp`, identified with `H^n` by Calderón's theorem
`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`) they assemble into a bounded
operator with bounded inverse. With the weak Laplacian `TauCeti.Wkp.laplacianL`, the gauge
Laplacian `-Δ + (p² + q²)` is a continuous linear isomorphism

`TauCeti.Vortex.sobolevGaugeLaplacianEquiv : W^{j+2,2}(ℂ) ≃L[ℝ] W^{j,2}(ℂ)`

for every `j ≤ k`. It is well defined because multiplication by the potential maps
`W^{j+2,2}(ℂ)` into `W^{j,2}(ℂ)`, and it is characterized by the weak equation
`∫ w · d₀* d₀ φ = ∫ (d₀* d₀ w) φ` (`TauCeti.Vortex.sobolevGaugeLaplacianEquiv_eq_iff`). Its graph
is closed, because integration against a fixed square-integrable function is continuous on
`W^{n,2}(ℂ)`, so it is bounded by the closed graph theorem; uniqueness and existence above make it
bijective, and the open mapping theorem bounds its inverse, which solves the weak equation
(`TauCeti.Vortex.sobolevGaugeLaplacianEquiv_symm_apply_eq_iff`). For `j = k - 1` this is the
analytic input for the invertibility of the linearization at the identity of the Coulomb gauge
condition
`d₀* (u · x₀ - x₀) = 0`, as a map `H^(k+1)(ℂ) → H^(k-1)(ℂ)`, for the action of the Sobolev framed
gauge group `G_(k+1)` (`TauCeti.Vortex.sobolevGaugeGroup`) on `A_m^k`: the input of the
implicit function theorem for the gauge slice.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution Filter Metric Topology
open scoped Laplacian ContDiff Distributions

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- At a continuous field, the potential `p² + q²` of the gauge Laplacian is continuous. -/
private theorem continuous_sq_add_sq (hcont : Continuous x) :
    Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
  have _ : Continuous fun z ↦ x z 2 := by fun_prop
  have _ : Continuous fun z ↦ x z 3 := by fun_prop
  fun_prop

/-- At a continuous field of `A_m^s`, `s > 1`, the potential `p² + q²` of the gauge Laplacian is
bounded and at least `1 / 8` outside a disc. -/
private theorem potential_bounds {s : ℝ} (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) :
    MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ (volume : Measure ℂ) ∧
      ∃ R, ∀ z, R < ‖z‖ → 1 / 8 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by
  have hlim := tendsto_normSq_of_mem_framedFieldSpace hs hx hcont
  have hVc := continuous_sq_add_sq hcont
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

/-- **No nonzero decaying infinitesimal gauge transformation is Coulomb.** At any field `x`, a
`C²` phase `u` tending to zero at infinity with `d₀* d₀ u = 0` vanishes: the equation reads
`Δu = (p² + q²) u`, so `u Δu ≥ 0`. -/
theorem eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hlim : Tendsto u (cocompact ℂ) (𝓝 0))
    (h : ∀ z, gaugeAdjoint x (gaugeDirection x u) z = 0) : u = 0 := by
  refine eq_zero_of_tendsto_cocompact_of_mul_laplacian_nonneg hu (fun z ↦ ?_) hlim
  have hz := h z
  rw [gaugeAdjoint_gaugeDirection x hu.contDiffAt] at hz
  have hΔ : Δ u z = (x z 2 ^ 2 + x z 3 ^ 2) * u z := by linarith
  rw [hΔ, show u z * ((x z 2 ^ 2 + x z 3 ^ 2) * u z) = (x z 2 ^ 2 + x z 3 ^ 2) * u z ^ 2 by ring]
  positivity

/-- **`C²` weak solutions of the gauge Laplacian are classical.** At a continuous field `x`, a `C²`
phase `u` with `d₀* d₀ u = g` weakly, for a continuous `g`, satisfies `d₀* d₀ u = g` at every
point. -/
theorem gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq (hx : Continuous x) {u g : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : Continuous g)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z) (z : ℂ) :
    gaugeAdjoint x (gaugeDirection x u) z = g z := by
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  have hP : Continuous P := continuous_sq_add_sq hx
  -- The weak equation says that the distributional Laplacian of `u` is `P u - g`.
  have hΔ : Set.EqOn (Δ u) (fun z ↦ P z * u z - g z) (⊤ : TopologicalSpace.Opens ℂ) := by
    refine hu.contDiffOn.eqOn_laplacian_of_forall_integral_laplacian_smul_eq (μ := volume)
      ((hP.mul hu.continuous).sub hg).continuousOn fun φ ↦ ?_
    have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
    have hφc := φ.hasCompactSupport
    have hint (a : ℂ → ℝ) (ha : Continuous a) : Integrable (fun z ↦ φ z * a z) volume :=
      (φ.continuous.mul ha).integrable_of_hasCompactSupport hφc.mul_right
    have hΔφ : Integrable (fun z ↦ Δ (φ : ℂ → ℝ) z * u z) volume :=
      (hφ2.continuous_laplacian.mul hu.continuous).integrable_of_hasCompactSupport
        hφc.laplacian.mul_right
    have hweak := hw φ φ.contDiff hφc
    rw [integral_mul_gaugeAdjoint_gaugeDirection hφ2] at hweak
    simpa only [smul_eq_mul] using integral_mul_eq_integral_mul_sub_of_integral_mul_neg_add_mul_eq
      hΔφ (hint _ (hP.mul hu.continuous)) (hint g hg) hweak
  rw [gaugeAdjoint_gaugeDirection x hu.contDiffAt, hΔ (Set.mem_univ z)]
  ring

/-! ### The gauge Laplacian as an isomorphism of Sobolev spaces -/

section Isomorphism

open TopologicalSpace

/-- An element of `W^{n,2}(ℂ)` is determined by its integrals against smooth compactly supported
functions. -/
private theorem wkp_eq_of_forall_integral_value_mul_eq {n : ℕ}
    {g g' : Wkp (volume : Measure ℂ) ⊤ 2 n}
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, Wkp.value n g z * φ z = ∫ z, Wkp.value n g' z * φ z) : g = g' :=
  Wkp.ext_of_forall_integral_smul_value_eq fun φ ↦ by
    simpa only [smul_eq_mul, mul_comm (φ _)] using h φ φ.contDiff φ.hasCompactSupport

/-- Integration against a fixed square-integrable function is continuous on `W^{n,2}(ℂ)`. -/
private theorem tendsto_integral_wkp_value_mul {n : ℕ} {ψ : ℂ → ℝ} (hψ : MemLp ψ 2 volume)
    {w : ℕ → Wkp (volume : Measure ℂ) ⊤ 2 n} {w₀ : Wkp (volume : Measure ℂ) ⊤ 2 n}
    (h : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun i ↦ ∫ z, Wkp.value n (w i) z * ψ z) atTop
      (𝓝 (∫ z, Wkp.value n w₀ z * ψ z)) := by
  simpa only [Measure.restrict_coe_opens_top, Function.comp_def] using
    ((Wkp.continuous_integral_value_mul n (hψ.restrict _)).tendsto w₀).comp h

variable {k j : ℕ}

/-- At a field of `A_m^k` and for `j ≤ k`, the product of `w ∈ W^{j+2,2}(ℂ)` with the potential
`p² + q²` of the gauge Laplacian lies in `W^{j,2}(ℂ)`. -/
private theorem exists_wkp_value_ae_eq_sq_add_sq_mul (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) :
    ∃ g : Wkp (volume : Measure ℂ) ⊤ 2 j, (Wkp.value j g : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ (x z 2 ^ 2 + x z 3 ^ 2) * Wkp.value (j + 2) w z := by
  -- measure the product at the order `N = min (j + 2) k`, with `1 < N`, `j ≤ N` and `N ≤ k`
  obtain ⟨N, hN⟩ : ∃ N, N = min (j + 2) k := ⟨_, rfl⟩
  have hxN : x ∈ framedFieldSpace f m (N : ℝ) :=
    framedFieldSpace_mono f m (by exact_mod_cast (by omega : N ≤ k)) hx
  have hwN : (Wkp.value (j + 2) w : ℂ → ℝ) ∈ realSobolevFunctions ℂ (N : ℝ) 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num)
      (by exact_mod_cast (by omega : N ≤ j + 2))
      (Wkp.value_mem_realSobolevFunctions (by norm_num) (by norm_num) w)
  exact exists_wkp_value_ae_eq_of_mem_realSobolevFunctions (by norm_num) (by norm_num)
    (by exact_mod_cast (by omega : j ≤ N))
    (sq_add_sq_mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hxN hwN)

/-- Multiplication by the potential `p² + q²` of the gauge Laplacian, as a linear map
`W^{j+2,2}(ℂ) → W^{j,2}(ℂ)`. -/
private noncomputable def sqAddSqMul (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) :
    Wkp (volume : Measure ℂ) ⊤ 2 (j + 2) →ₗ[ℝ] Wkp (volume : Measure ℂ) ⊤ 2 j where
  toFun w := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w).choose
  map_add' w w' := by
    set a := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w).choose
    set a' := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w').choose
    have h₁ := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx (w + w')).choose_spec
    have h₂ := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w).choose_spec
    have h₃ := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w').choose_spec
    have h₄ := (Wkp.value_add_ae _ w w').filter_mono Measure.ae_le_ae_restrict_coe_opens_top
    have h₅ := (Wkp.value_add_ae _ a a').filter_mono Measure.ae_le_ae_restrict_coe_opens_top
    refine Wkp.ext j (Lp.ext (ae_restrict_of_ae ?_))
    filter_upwards [h₁, h₂, h₃, h₄, h₅] with z e₁ e₂ e₃ e₄ e₅
    rw [e₁, e₅, Pi.add_apply, e₂, e₃, e₄, Pi.add_apply, mul_add]
  map_smul' c w := by
    set a := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w).choose
    have h₁ := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx (c • w)).choose_spec
    have h₂ := (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w).choose_spec
    have h₃ := (Wkp.value_smul_ae _ c w).filter_mono Measure.ae_le_ae_restrict_coe_opens_top
    have h₄ := (Wkp.value_smul_ae _ c a).filter_mono Measure.ae_le_ae_restrict_coe_opens_top
    refine Wkp.ext j (Lp.ext (ae_restrict_of_ae ?_))
    filter_upwards [h₁, h₂, h₃, h₄] with z e₁ e₂ e₃ e₄
    rw [RingHom.id_apply, e₁, e₄, Pi.smul_apply, e₂, e₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

private theorem sqAddSqMul_ae (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) :
    (Wkp.value j (sqAddSqMul hk hjk hx w) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ (x z 2 ^ 2 + x z 3 ^ 2) * Wkp.value (j + 2) w z :=
  (exists_wkp_value_ae_eq_sq_add_sq_mul hk hjk hx w).choose_spec

/-- The gauge Laplacian `-Δ + (p² + q²)` as a linear map `W^{j+2,2}(ℂ) → W^{j,2}(ℂ)`. -/
private noncomputable def gaugeLaplacianₗ (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) :
    Wkp (volume : Measure ℂ) ⊤ 2 (j + 2) →ₗ[ℝ] Wkp (volume : Measure ℂ) ⊤ 2 j :=
  -(Wkp.laplacianL j).toLinearMap + sqAddSqMul hk hjk hx

private theorem gaugeLaplacianₗ_ae (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) :
    (Wkp.value j (gaugeLaplacianₗ hk hjk hx w) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ -Wkp.value j (Wkp.laplacianL j w) z +
        (x z 2 ^ 2 + x z 3 ^ 2) * Wkp.value (j + 2) w z := by
  rw [gaugeLaplacianₗ, LinearMap.add_apply, LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
  have h₁ := (Wkp.value_add_ae _ (-Wkp.laplacianL j w) (sqAddSqMul hk hjk hx w)).filter_mono
    Measure.ae_le_ae_restrict_coe_opens_top
  have h₂ := (Wkp.value_neg_ae _ (Wkp.laplacianL j w)).filter_mono
    Measure.ae_le_ae_restrict_coe_opens_top
  filter_upwards [h₁, h₂, sqAddSqMul_ae hk hjk hx w] with z e₁ e₂ e₃
  rw [e₁, Pi.add_apply, e₂, Pi.neg_apply, e₃]

/-- The weak equation of the gauge Laplacian on `W^{j+2,2}(ℂ)`. -/
private theorem integral_value_mul_gaugeAdjoint_gaugeDirection_eq_gaugeLaplacianₗ (hk : 1 < k)
    (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z, Wkp.value (j + 2) w z * gaugeAdjoint x (gaugeDirection x φ) z =
      ∫ z, Wkp.value j (gaugeLaplacianₗ hk hjk hx w) z * φ z := by
  set ψ : 𝓓((⊤ : Opens ℂ), ℝ) := ⟨φ, hφ, hc, by simp⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hV := continuous_sq_add_sq hcont
  have hw := Wkp.memLp_value _ w
  have hΔw := Wkp.memLp_value _ (Wkp.laplacianL j w)
  have hφL2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hΔφ : MemLp (Δ φ) 2 volume :=
    hφ2.continuous_laplacian.memLp_of_hasCompactSupport hc.laplacian
  have hVφ : MemLp (fun z ↦ (x z 2 ^ 2 + x z 3 ^ 2) * φ z) 2 volume :=
    (hV.mul hφ.continuous).memLp_of_hasCompactSupport hc.mul_left
  -- the Laplacian term is the weak Laplacian of `w`
  have hL : ∫ z, Δ φ z * Wkp.value (j + 2) w z =
      ∫ z, Wkp.value j (Wkp.laplacianL j w) z * φ z := by
    have h := Wkp.integral_laplacian_smul_value_eq_laplacianL j w ψ
    simpa only [ψ, TestFunction.coe_mk, smul_eq_mul, mul_comm (φ _)] using h
  have i₁ : Integrable (fun z ↦ -(Δ φ z * Wkp.value (j + 2) w z)) volume :=
    (hΔφ.integrable_mul hw).neg
  have i₂ : Integrable (fun z ↦ Wkp.value (j + 2) w z * ((x z 2 ^ 2 + x z 3 ^ 2) * φ z))
      volume :=
    hw.integrable_mul hVφ
  have i₃ : Integrable (fun z ↦ -Wkp.value j (Wkp.laplacianL j w) z * φ z) volume :=
    (hΔw.integrable_mul hφL2).neg.congr
      (ae_of_all _ fun z ↦ by simp only [Pi.neg_apply, Pi.mul_apply, neg_mul])
  calc ∫ z, Wkp.value (j + 2) w z * gaugeAdjoint x (gaugeDirection x φ) z
      = ∫ z, (-(Δ φ z * Wkp.value (j + 2) w z) +
          Wkp.value (j + 2) w z * ((x z 2 ^ 2 + x z 3 ^ 2) * φ z)) := by
        rw [integral_mul_gaugeAdjoint_gaugeDirection hφ2]
        congr 1 with z
        ring
    _ = (-∫ z, Wkp.value j (Wkp.laplacianL j w) z * φ z) +
          ∫ z, Wkp.value (j + 2) w z * ((x z 2 ^ 2 + x z 3 ^ 2) * φ z) := by
        rw [integral_add i₁ i₂, integral_neg, hL]
    _ = ∫ z, (-Wkp.value j (Wkp.laplacianL j w) z * φ z +
          Wkp.value (j + 2) w z * ((x z 2 ^ 2 + x z 3 ^ 2) * φ z)) := by
        rw [integral_add i₃ i₂]
        simp only [neg_mul, integral_neg]
    _ = ∫ z, Wkp.value j (gaugeLaplacianₗ hk hjk hx w) z * φ z := by
        refine integral_congr_ae ?_
        filter_upwards [gaugeLaplacianₗ_ae hk hjk hx w] with z hz
        rw [hz]
        ring

/-- The gauge Laplacian on `W^{j+2,2}(ℂ)` has a closed graph. -/
private theorem gaugeLaplacianₗ_closedGraph (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    (w : ℕ → Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) (w₀ : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2))
    (g₀ : Wkp (volume : Measure ℂ) ⊤ 2 j) (hw : Tendsto w atTop (𝓝 w₀))
    (hg : Tendsto (gaugeLaplacianₗ hk hjk hx ∘ w) atTop (𝓝 g₀)) :
    g₀ = gaugeLaplacianₗ hk hjk hx w₀ := by
  refine wkp_eq_of_forall_integral_value_mul_eq fun φ hφ hc ↦ ?_
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hV := continuous_sq_add_sq hcont
  -- `d₀* d₀ φ = -Δφ + (p² + q²) φ` is continuous with compact support, hence square integrable
  have hLφ : MemLp (fun z ↦ gaugeAdjoint x (gaugeDirection x φ) z) 2 volume := by
    have hc' : Continuous fun z ↦ -Δ φ z + (x z 2 ^ 2 + x z 3 ^ 2) * φ z :=
      hφ2.continuous_laplacian.neg.add (hV.mul hφ.continuous)
    refine (hc'.memLp_of_hasCompactSupport (hc.laplacian.neg.add hc.mul_left)).congr_norm ?_
      (ae_of_all _ fun z ↦ by rw [gaugeAdjoint_gaugeDirection x hφ2.contDiffAt])
    exact (hc'.congr fun z ↦
      (gaugeAdjoint_gaugeDirection x hφ2.contDiffAt).symm).aestronglyMeasurable
  have h₁ := tendsto_integral_wkp_value_mul (hφ.continuous.memLp_of_hasCompactSupport hc) hg
  have h₂ := tendsto_integral_wkp_value_mul hLφ hw
  simp_rw [Function.comp_apply, ← integral_value_mul_gaugeAdjoint_gaugeDirection_eq_gaugeLaplacianₗ
    hk hjk hx hcont _ hφ hc] at h₁
  rw [← integral_value_mul_gaugeAdjoint_gaugeDirection_eq_gaugeLaplacianₗ hk hjk hx hcont _ hφ hc]
  exact tendsto_nhds_unique h₁ h₂

/-- The gauge Laplacian `-Δ + (p² + q²)` as a bounded operator `W^{j+2,2}(ℂ) → W^{j,2}(ℂ)`. -/
private noncomputable def gaugeLaplacianCLM (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) :
    Wkp (volume : Measure ℂ) ⊤ 2 (j + 2) →L[ℝ] Wkp (volume : Measure ℂ) ⊤ 2 j :=
  ContinuousLinearMap.ofSeqClosedGraph (g := gaugeLaplacianₗ hk hjk hx)
    (gaugeLaplacianₗ_closedGraph hk hjk hx hcont)

/-- The gauge Laplacian on `W^{j+2,2}(ℂ)` is injective, by uniqueness of weak solutions. -/
private theorem gaugeLaplacianₗ_injective (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) :
    Function.Injective (gaugeLaplacianₗ hk hjk hx) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  have hzero : ∀ φ : ℂ → ℝ, ∫ z, (0 : ℂ → ℝ) z * φ z = 0 := fun φ ↦ by simp
  have hzero_ae (n : ℕ) : (Wkp.value n (0 : Wkp (volume : Measure ℂ) ⊤ 2 n) : ℂ → ℝ) =ᵐ[volume] 0 :=
    (Wkp.value_zero_ae n).filter_mono Measure.ae_le_ae_restrict_coe_opens_top
  have hae := ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq (s := k)
    (by exact_mod_cast hk) hx hcont (Wkp.memLp_value _ w) (MemLp.zero' (ε := ℝ)) (g := 0)
    (fun φ hφ hc ↦ by
      rw [integral_value_mul_gaugeAdjoint_gaugeDirection_eq_gaugeLaplacianₗ hk hjk hx hcont w hφ
        hc, hw, hzero]
      exact (integral_congr_ae ((hzero_ae j).mono fun z hz ↦ by rw [hz])).trans (hzero φ))
    (fun φ _ _ ↦ by simp)
  exact Wkp.ext _ (Lp.ext (ae_restrict_of_ae (hae.trans (hzero_ae (j + 2)).symm)))

/-- The gauge Laplacian on `W^{j+2,2}(ℂ)` is onto `W^{j,2}(ℂ)`, by existence and regularity of
weak solutions. -/
private theorem gaugeLaplacianₗ_surjective (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) :
    Function.Surjective (gaugeLaplacianₗ hk hjk hx) := by
  intro g
  obtain ⟨u, hu, hweak⟩ :=
    exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq hk hjk hx hcont
      (Wkp.value_mem_realSobolevFunctions (p := 2) (by norm_num) (by norm_num) g)
  obtain ⟨w, hw⟩ := exists_wkp_value_ae_eq_of_mem_realSobolevFunctions (p := 2) (k := j + 2)
    (by norm_num) (by norm_num) (by push_cast; exact le_rfl) hu
  refine ⟨w, wkp_eq_of_forall_integral_value_mul_eq fun φ hφ hc ↦ ?_⟩
  rw [← integral_value_mul_gaugeAdjoint_gaugeDirection_eq_gaugeLaplacianₗ hk hjk hx hcont w hφ hc,
    ← hweak φ (hφ.of_le (by simp)) hc]
  exact integral_congr_ae (hw.mono fun z hz ↦ by simp only [hz])

/-- **The gauge Laplacian as an isomorphism of Sobolev spaces.** At a continuous field `x` of
`A_m^k`, `k ≥ 2`, and for `j ≤ k`, the gauge Laplacian `d₀* d₀ = -Δ + (p² + q²)` is a continuous
linear isomorphism `W^{j+2,2}(ℂ) ≃ W^{j,2}(ℂ)`, where `Δ` is the weak Laplacian
`TauCeti.Wkp.laplacianL` (`TauCeti.Vortex.value_sobolevGaugeLaplacianEquiv_ae_eq`). It is
characterized by the weak equation `∫ w · d₀* d₀ φ = ∫ (d₀* d₀ w) φ` for smooth compactly
supported `φ` (`TauCeti.Vortex.sobolevGaugeLaplacianEquiv_eq_iff`). As a continuous linear
isomorphism it has a bounded inverse: for `j = k - 1`, the solution `u ∈ W^{k+1,2}(ℂ)` of
`d₀* d₀ u = g` depends continuously on `g ∈ W^{k-1,2}(ℂ)`, and it is characterized by the weak
equation (`TauCeti.Vortex.sobolevGaugeLaplacianEquiv_symm_apply_eq_iff`). -/
noncomputable def sobolevGaugeLaplacianEquiv (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) :
    Wkp (volume : Measure ℂ) ⊤ 2 (j + 2) ≃L[ℝ] Wkp (volume : Measure ℂ) ⊤ 2 j :=
  ContinuousLinearEquiv.ofBijective (gaugeLaplacianCLM hk hjk hx hcont)
    (LinearMap.ker_eq_bot.2 (gaugeLaplacianₗ_injective hk hjk hx hcont))
    (LinearMap.range_eq_top.2 (gaugeLaplacianₗ_surjective hk hjk hx hcont))

private theorem sobolevGaugeLaplacianEquiv_apply (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) :
    sobolevGaugeLaplacianEquiv hk hjk hx hcont w = gaugeLaplacianₗ hk hjk hx w := by
  rw [sobolevGaugeLaplacianEquiv, ContinuousLinearEquiv.coeFn_ofBijective, gaugeLaplacianCLM,
    ContinuousLinearMap.coeFn_ofSeqClosedGraph]

/-- **The gauge Laplacian is `-Δ + (p² + q²)`** on `W^{j+2,2}(ℂ)`, with the weak Laplacian
`TauCeti.Wkp.laplacianL`. -/
theorem value_sobolevGaugeLaplacianEquiv_ae_eq (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) :
    (Wkp.value j (sobolevGaugeLaplacianEquiv hk hjk hx hcont w) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ -Wkp.value j (Wkp.laplacianL j w) z +
        (x z 2 ^ 2 + x z 3 ^ 2) * Wkp.value (j + 2) w z := by
  rw [sobolevGaugeLaplacianEquiv_apply]
  exact gaugeLaplacianₗ_ae hk hjk hx w

/-- **The weak equation of the gauge Laplacian**: for `w ∈ W^{j+2,2}(ℂ)` and a smooth compactly
supported `φ`, `∫ w · d₀* d₀ φ = ∫ (d₀* d₀ w) φ`. -/
theorem integral_value_mul_gaugeAdjoint_gaugeDirection_eq_sobolevGaugeLaplacianEquiv (hk : 1 < k)
    (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    (w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z, Wkp.value (j + 2) w z * gaugeAdjoint x (gaugeDirection x φ) z =
      ∫ z, Wkp.value j (sobolevGaugeLaplacianEquiv hk hjk hx hcont w) z * φ z := by
  rw [sobolevGaugeLaplacianEquiv_apply]
  exact integral_value_mul_gaugeAdjoint_gaugeDirection_eq_gaugeLaplacianₗ hk hjk hx hcont w hφ hc

/-- **The gauge Laplacian is determined by its weak equation**: `d₀* d₀ w = g` in `W^{j,2}(ℂ)`
exactly when `∫ w · d₀* d₀ φ = ∫ g φ` for every smooth compactly supported `φ`. -/
theorem sobolevGaugeLaplacianEquiv_eq_iff (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    {w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)} {g : Wkp (volume : Measure ℂ) ⊤ 2 j} :
    sobolevGaugeLaplacianEquiv hk hjk hx hcont w = g ↔
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ z, Wkp.value (j + 2) w z * gaugeAdjoint x (gaugeDirection x φ) z =
          ∫ z, Wkp.value j g z * φ z := by
  refine ⟨fun h φ hφ hc ↦ ?_, fun h ↦ wkp_eq_of_forall_integral_value_mul_eq fun φ hφ hc ↦ ?_⟩
  · rw [integral_value_mul_gaugeAdjoint_gaugeDirection_eq_sobolevGaugeLaplacianEquiv hk hjk hx
      hcont w hφ hc, h]
  · rw [← integral_value_mul_gaugeAdjoint_gaugeDirection_eq_sobolevGaugeLaplacianEquiv hk hjk hx
      hcont w hφ hc, h φ hφ hc]

/-- **The inverse of the gauge Laplacian solves the weak equation**: for `g ∈ W^{j,2}(ℂ)`, the
inverse image of `g` is the unique `w ∈ W^{j+2,2}(ℂ)` with `∫ w · d₀* d₀ φ = ∫ g φ` for every
smooth compactly supported `φ`. -/
theorem sobolevGaugeLaplacianEquiv_symm_apply_eq_iff (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    {g : Wkp (volume : Measure ℂ) ⊤ 2 j} {w : Wkp (volume : Measure ℂ) ⊤ 2 (j + 2)} :
    (sobolevGaugeLaplacianEquiv hk hjk hx hcont).symm g = w ↔
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ z, Wkp.value (j + 2) w z * gaugeAdjoint x (gaugeDirection x φ) z =
          ∫ z, Wkp.value j g z * φ z := by
  rw [ContinuousLinearEquiv.symm_apply_eq, eq_comm,
    sobolevGaugeLaplacianEquiv_eq_iff hk hjk hx hcont]

end Isomorphism

end TauCeti.Vortex
