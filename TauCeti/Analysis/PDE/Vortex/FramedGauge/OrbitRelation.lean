/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Limit
public import TauCeti.Analysis.Sobolev.BesselPotential.UniformConvergence

/-!
# The gauge orbit relation on `A_m^k` is closed for Sobolev convergence

The framed degree-`m` plane vortex fields form the affine space
`A_m^k = (a_m, α_m) + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), on which the Sobolev
gauge group `G_(k+1)` (`TauCeti.Vortex.sobolevGaugeGroup`) acts by `(a, α) ↦ (a - u⁻¹ du, u α)`.
The moduli space of framed vortices is a quotient of a subset of `A_m^k` by this action, and its
Hausdorff property rests on the orbit relation being closed for the Sobolev topology of `A_m^k`.
This file proves that closedness, for continuous fields.

Fields are pointwise representatives in the real coordinates `x = (b₁, b₂, p, q)`. A family of
fields `x i` converges to `x` in `H^s` (`TauCeti.Vortex.TendstoInSobolev`) when every coordinate of
`x i - x` agrees almost everywhere with an `L²` function of `H^s(ℂ)` and these functions tend to
zero in `H^s(ℂ)`. For `s > 1` the Sobolev embedding `H^s(ℂ) ⊆ C_b(ℂ)` turns this into uniform
convergence of the continuous fields on the whole plane
(`TauCeti.Vortex.TendstoInSobolev.tendstoUniformly`, from
`TemperedDistribution.tendstoUniformly_of_tendsto_toBesselPotentialSpace`). The limit theorems of
`TauCeti.Analysis.PDE.Vortex.FramedGauge.Limit`, which take locally uniform convergence, then
apply. Hence, for `k ≥ 3` and any order `s > 1` of convergence, the orbit relation of `G_(k+1)` on
the continuous fields of `A_m^k` is closed under convergence in `H^s`
(`TauCeti.Vortex.mem_orbit_sobolevGaugeGroup_of_tendstoInSobolev`). In particular, taking `s = k`,
it is closed under convergence in the Sobolev norm of `A_m^k` itself. Composing
`TauCeti.Vortex.TendstoInSobolev.tendstoUniformly` with
`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly` also
shows that the relating gauges converge locally uniformly to an element of `G_(k+1)`.

Continuity of the representatives is a normalization rather than a restriction: for `k > 1` every
field of `A_m^k` agrees almost everywhere with exactly one continuous field. Convergence of the
gauges in the `H^(k+1)` norm and the slice theorem are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Module TemperedDistribution Topology
open scoped SchwartzMap

variable {ι : Type*} {l : Filter ι}

/-- **Convergence of plane fields in `H^s`.** The fields `ys i` converge to `y` in `H^s` along
`l` when, for every real coordinate `j`, the differences `ys i · j - y · j` agree almost everywhere
with complex `L²` functions `u i` of `H^s(ℂ)` whose elements of `H^s(ℂ)` tend to zero. Since
`u i` is determined almost everywhere by `ys i - y`, this is convergence of `ys i - y` to zero in
the Sobolev norm, and it makes no regularity assumption beyond the existence of such `u i`. -/
def TendstoInSobolev (s : ℝ) (ys : ι → ℂ → EuclideanSpace ℝ (Fin 4)) (l : Filter ι)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) : Prop :=
  ∀ j : Fin 4, ∃ (u : ι → Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ i, MemSobolev s 2 (u i : 𝓢'(ℂ, ℂ))),
    (∀ i, u i =ᵐ[volume] fun z ↦ ((ys i z j - y z j : ℝ) : ℂ)) ∧
      Tendsto (fun i ↦ (hu i).toBesselPotentialSpace) l (𝓝 0)

/-- Moving a field along a fixed direction of `sobolevFields s` by amounts tending to zero
converges in `H^s`: if `w ∈ H^s` and `c i → 0`, then `y + c i • w → y` in `H^s`. -/
theorem tendstoInSobolev_add_smul {s : ℝ} {y w : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hw : w ∈ sobolevFields s) {c : ι → ℝ} (hc : Tendsto c l (𝓝 0)) :
    TendstoInSobolev s (fun i ↦ y + c i • w) l y := by
  intro j
  obtain ⟨v, hvw, hv⟩ := mem_realSobolevFunctions.1 (mem_sobolevFields.1 hw j)
  set V : Lp ℂ 2 (volume : Measure ℂ) := Complex.ofRealCLM.compLp v
  refine ⟨fun i ↦ (c i : ℂ) • V, fun i ↦ hv.toTemperedDistribution_smul (c i),
    fun i ↦ ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul (c i : ℂ) V, Complex.ofRealCLM.coeFn_compLp (p := 2)
      (μ := (volume : Measure ℂ)) v, hvw] with z h₁ h₂ h₃
    rw [h₁, Pi.smul_apply, h₂, h₃]
    simp
  · simp only [MemSobolev.toBesselPotentialSpace_toTemperedDistribution_smul _ hv]
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp hc).smul_const
      hv.toBesselPotentialSpace

/-- **Convergence in `H^s`, `s > 1`, is uniform convergence of continuous fields.** If continuous
fields `ys i` converge in `H^s` to a continuous field `y`, then they converge to `y` uniformly on
the plane, by the Sobolev embedding `H^s(ℂ) ⊆ C_b(ℂ)`. -/
theorem TendstoInSobolev.tendstoUniformly {s : ℝ} (hs : 1 < s)
    {ys : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (h : TendstoInSobolev s ys l y) (hys : ∀ i, Continuous (ys i)) (hy : Continuous y) :
    TendstoUniformly ys y l := by
  -- Each real coordinate converges uniformly, by the Sobolev embedding for complex functions.
  have hcoord (j : Fin 4) : TendstoUniformly (fun i z ↦ ys i z j) (fun z ↦ y z j) l := by
    obtain ⟨u, hu, hae, htend⟩ := h j
    have hC : TendstoUniformly (fun i z ↦ ((ys i z j : ℝ) : ℂ)) (fun z ↦ ((y z j : ℝ) : ℂ)) l :=
      tendstoUniformly_of_tendsto_toBesselPotentialSpace (finrank_real_complex_lt_two_mul hs)
        (fun i ↦ by fun_prop) (by fun_prop) hu
        (fun i ↦ (hae i).trans (.of_forall fun z ↦ by simp)) htend
    simpa using hC.re
  -- Coordinatewise uniform convergence is uniform convergence for the supremum distance on
  -- `Fin 4 → ℝ`, which is uniformly equivalent to the Euclidean distance.
  have hpi : TendstoUniformly (fun i z ↦ WithLp.ofLp (ys i z)) (fun z ↦ WithLp.ofLp (y z)) l := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [eventually_all.2 fun j ↦ Metric.tendstoUniformly_iff.1 (hcoord j) ε hε]
      with i hi z
    exact (dist_pi_lt_iff hε).2 fun j ↦ hi j z
  have h := (PiLp.uniformContinuous_toLp 2 _).comp_tendstoUniformly hpi
  simp only [Function.comp_def, WithLp.toLp_ofLp] at h
  exact h

/-- **The orbit relation of `G_(k+1)` on `A_m^k` is closed for Sobolev convergence**, `k ≥ 3`:
if continuous fields `x i → x` and `y i → y` of `A_m^k` converge in `H^s` for some `s > 1`, with
`x`, `y` continuous and each `y i` in the `G_(k+1)`-orbit of `x i`, then `y` lies in the
`G_(k+1)`-orbit of `x`. Taking `s = k` gives closedness for the Sobolev norm of `A_m^k`. The
fields `y i` are continuous because the elements of `G_(k+1)` are `C¹`. -/
theorem mem_orbit_sobolevGaugeGroup_of_tendstoInSobolev [l.NeBot] {k : ℕ} [Fact (1 < k)]
    (hk : 2 < k) {hs : 1 < (k : ℝ) + 1} {s : ℝ} (hs' : 1 < s) {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} {xs ys : ι → framedFieldSpace f m k} {x y : framedFieldSpace f m k}
    (hxy : ∀ i, ys i ∈ MulAction.orbit (sobolevGaugeGroup hs) (xs i))
    (hxs : ∀ i, Continuous (xs i : ℂ → EuclideanSpace ℝ (Fin 4)))
    (hx : TendstoInSobolev s (fun i ↦ (xs i : ℂ → EuclideanSpace ℝ (Fin 4))) l x)
    (hy : TendstoInSobolev s (fun i ↦ (ys i : ℂ → EuclideanSpace ℝ (Fin 4))) l y)
    (hxc : Continuous (x : ℂ → EuclideanSpace ℝ (Fin 4)))
    (hyc : Continuous (y : ℂ → EuclideanSpace ℝ (Fin 4))) :
    y ∈ MulAction.orbit (sobolevGaugeGroup hs) x := by
  have hys (i : ι) : Continuous (ys i : ℂ → EuclideanSpace ℝ (Fin 4)) := by
    obtain ⟨u, hu⟩ := hxy i
    have h1 : ContDiff ℝ (0 + 1) (fun z ↦ ((u : ℂ → Circle) z : ℂ)) := by
      have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
      simpa using contDiff_of_mem_sobolevGaugeGroup (k := 1) (by push_cast; linarith) u.2
    rw [← hu, coe_sobolevGaugeGroup_smul]
    exact (contDiff_gaugeTransform h1 (contDiff_zero.2 (hxs i))).continuous
  exact mem_orbit_sobolevGaugeGroup_of_tendstoLocallyUniformly hk hxy
    (hx.tendstoUniformly hs' hxs hxc).tendstoLocallyUniformly
    (hy.tendstoUniformly hs' hys hyc).tendstoLocallyUniformly hxc hyc

end TauCeti.Vortex
