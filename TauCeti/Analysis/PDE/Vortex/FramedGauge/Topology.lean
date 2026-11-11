/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The Sobolev framed gauge group is a topological group

For a real order `s > 1`, the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`. This file records
`u - 1` as an element `sobolevGaugeSubOne hs u` of Mathlib's Bessel-potential space `H^s(ℂ)`,
and topologizes `G_s` by the `H^s` distances of `u - 1` and of `u⁻¹ - 1 = conj u - 1`.

Since `H^s(ℂ)` is an algebra for `s > 1`, with the pointwise product a continuous bilinear map
`BesselPotentialSpace.mulCLM`, the coordinate of a product is a polynomial in the coordinates of
the factors:

`(u v - 1) = (u - 1) + (v - 1) + (u - 1) (v - 1)`

(`sobolevGaugeSubOne_mul`). Applied to `u` and to `u⁻¹`, this makes multiplication continuous,
and inversion exchanges the two coordinates. The coordinate map is injective, because two
continuous functions which agree almost everywhere agree everywhere
(`sobolevGaugeSubOne_injective`). Hence `G_s`, with the topology induced by
`u ↦ (u - 1, u⁻¹ - 1) ∈ H^s(ℂ) × H^s(ℂ)` (`sobolevGaugeTopology`), is a Hausdorff topological group
(`isTopologicalGroup_sobolevGaugeTopology`, `t2Space_sobolevGaugeTopology`).

Both coordinates are recorded because complex conjugation is not yet known to be continuous on
`H^s(ℂ)`. The topology is not registered as an instance: as a subtype of `ℂ → Circle`, the group
`G_s` already carries the subspace topology of pointwise convergence, and a second instance would
compete with it.

These are the multiplication and inversion of the Banach gauge group of the framed vortex field
space `A_m^k`, whose gauge group is `G_(k+1)`. The exponential charts
(`TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential`) and the continuity of the action on
`A_m^k` are not treated here.

## Main definitions

* `TauCeti.Vortex.sobolevGaugeSubOne hs u`: the element `u - 1` of `H^s(ℂ)` for `u ∈ G_s`.
* `TauCeti.Vortex.sobolevGaugeTopology hs`: the topology on `G_s` induced by
  `u ↦ (u - 1, u⁻¹ - 1)`.

## Main results

* `TauCeti.Vortex.toDistr_sobolevGaugeSubOne_of_ae_eq`: `sobolevGaugeSubOne hs u` is every `L²`
  function equal to `u - 1` almost everywhere.
* `TauCeti.Vortex.sobolevGaugeSubOne_injective`: a gauge is determined by its coordinate.
* `TauCeti.Vortex.sobolevGaugeSubOne_mul`: the coordinate of a product.
* `TauCeti.Vortex.isTopologicalGroup_sobolevGaugeTopology`: `G_s` is a topological group.
* `TauCeti.Vortex.t2Space_sobolevGaugeTopology`: its topology is Hausdorff.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Module TemperedDistribution BesselPotentialSpace
open scoped SchwartzMap BesselPotentialSpace

variable {s : ℝ} {hs : 1 < s}

/-- **The coordinate `u - 1` of a Sobolev gauge**: for `u ∈ G_s`, the element of `H^s(ℂ)`
represented by the `L²` function `u - 1`. -/
def sobolevGaugeSubOne (hs : 1 < s) (u : sobolevGaugeGroup hs) : H^{s}(ℂ) :=
  (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2).choose_spec.2.toBesselPotentialSpace

/-- **Characterization of the coordinate `u - 1`.** For `u ∈ G_s`, `sobolevGaugeSubOne hs u` is
every `L²` function equal to `u - 1` almost everywhere. -/
theorem toDistr_sobolevGaugeSubOne_of_ae_eq (u : sobolevGaugeGroup hs)
    {h : Lp ℂ 2 (volume : Measure ℂ)} (hh : h =ᵐ[volume] fun z ↦ (u.1 z : ℂ) - 1) :
    (sobolevGaugeSubOne hs u).toDistr = h := by
  have hc := (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2).choose_spec
  rw [sobolevGaugeSubOne, MemSobolev.toBesselPotentialSpace_toDistr]
  congr 1
  exact Lp.ext (hc.1.trans hh.symm)

/-- The coordinate of the identity gauge is zero. -/
@[simp]
theorem sobolevGaugeSubOne_one : sobolevGaugeSubOne hs 1 = 0 := by
  ext1
  rw [toDistr_sobolevGaugeSubOne_of_ae_eq 1 (h := 0) (by
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
      simp),
    Lp.toTemperedDistribution_zero, toDistr_zero]

/-- **A Sobolev gauge is determined by its coordinate `u - 1`.** -/
theorem sobolevGaugeSubOne_injective (hs : 1 < s) : Function.Injective (sobolevGaugeSubOne hs) := by
  intro u v huv
  obtain ⟨a, ha, -⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2
  obtain ⟨b, hb, -⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup v.2
  have hab : a = b := LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    rw [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistributionCLM_apply, ← toDistr_sobolevGaugeSubOne_of_ae_eq u ha,
      ← toDistr_sobolevGaugeSubOne_of_ae_eq v hb, huv]
  have hcont (w : sobolevGaugeGroup hs) : Continuous fun z ↦ (w.1 z : ℂ) - 1 :=
    (continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 w.2).1).sub continuous_const
  have hfun := ((hcont u).ae_eq_iff_eq volume (hcont v)).1 (ha.symm.trans (hab ▸ hb))
  ext z : 3
  simpa using congrFun hfun z

/-- **The coordinate of a product of Sobolev gauges.** For `u, v ∈ G_s`,
`u v - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)` in `H^s(ℂ)`. -/
theorem sobolevGaugeSubOne_mul (u v : sobolevGaugeGroup hs) :
    sobolevGaugeSubOne hs (u * v) = sobolevGaugeSubOne hs u + sobolevGaugeSubOne hs v +
      mulCLM (finrank_real_complex_lt_two_mul hs) (sobolevGaugeSubOne hs u)
        (sobolevGaugeSubOne hs v) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨a, ha, has⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2
  obtain ⟨b, hb, -⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup v.2
  set p := (has.memLp_mul hs' b).toLp _
  have hp : p =ᵐ[volume] fun z ↦ a z * b z := MemLp.coeFn_toLp _
  ext1
  rw [toDistr_add, toDistr_add, toDistr_sobolevGaugeSubOne_of_ae_eq u ha,
    toDistr_sobolevGaugeSubOne_of_ae_eq v hb,
    toDistr_mulCLM_of_ae_eq hs' (toDistr_sobolevGaugeSubOne_of_ae_eq u ha)
      (toDistr_sobolevGaugeSubOne_of_ae_eq v hb) hp,
    ← Lp.toTemperedDistribution_add, ← Lp.toTemperedDistribution_add]
  refine toDistr_sobolevGaugeSubOne_of_ae_eq (u * v) ?_
  filter_upwards [Lp.coeFn_add (a + b) p, Lp.coeFn_add a b, hp, ha, hb] with z h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, h₄, h₅]
  simp only [Subgroup.coe_mul, Pi.mul_apply, Circle.coe_mul]
  ring

/-- **The topology of the Sobolev gauge group** `G_s`, `s > 1`: the topology induced by the
coordinates `u ↦ (u - 1, u⁻¹ - 1) ∈ H^s(ℂ) × H^s(ℂ)`. Here `u⁻¹ - 1 = conj u - 1`. -/
@[implicit_reducible]
def sobolevGaugeTopology (hs : 1 < s) : TopologicalSpace (sobolevGaugeGroup hs) :=
  .induced (fun u ↦ (sobolevGaugeSubOne hs u, sobolevGaugeSubOne hs u⁻¹)) inferInstance

/-- **The Sobolev gauge group is a topological group.** For `s > 1`, multiplication and inversion
on `G_s` are continuous for `sobolevGaugeTopology`. -/
theorem isTopologicalGroup_sobolevGaugeTopology (hs : 1 < s) :
    @IsTopologicalGroup (sobolevGaugeGroup hs) (sobolevGaugeTopology hs) _ := by
  let := sobolevGaugeTopology hs
  have hs' := finrank_real_complex_lt_two_mul hs
  have hcoord : Continuous fun u : sobolevGaugeGroup hs ↦
      (sobolevGaugeSubOne hs u, sobolevGaugeSubOne hs u⁻¹) :=
    continuous_induced_dom
  have h₁ : Continuous (sobolevGaugeSubOne hs) := continuous_fst.comp hcoord
  have h₂ : Continuous fun u : sobolevGaugeGroup hs ↦ sobolevGaugeSubOne hs u⁻¹ :=
    continuous_snd.comp hcoord
  -- In coordinates, the product is the polynomial `x + y + x y`.
  have hpoly {f g : sobolevGaugeGroup hs × sobolevGaugeGroup hs → sobolevGaugeGroup hs}
      (hf : Continuous fun p ↦ sobolevGaugeSubOne hs (f p))
      (hg : Continuous fun p ↦ sobolevGaugeSubOne hs (g p)) :
      Continuous fun p ↦ sobolevGaugeSubOne hs (f p * g p) := by
    simp only [sobolevGaugeSubOne_mul]
    exact (hf.add hg).add ((mulCLM hs').continuous₂.comp (hf.prodMk hg))
  refine { continuous_mul := continuous_induced_rng.2 ?_, continuous_inv := ?_ }
  · refine (hpoly (h₁.comp continuous_fst) (h₁.comp continuous_snd)).prodMk ?_
    simp only [mul_inv]
    exact hpoly (h₂.comp continuous_fst) (h₂.comp continuous_snd)
  · refine continuous_induced_rng.2 (h₂.prodMk ?_)
    simpa only [inv_inv] using h₁

/-- **The topology of the Sobolev gauge group is Hausdorff**, since a gauge is determined by its
coordinate `u - 1`. -/
theorem t2Space_sobolevGaugeTopology (hs : 1 < s) :
    @T2Space (sobolevGaugeGroup hs) (sobolevGaugeTopology hs) := by
  let := sobolevGaugeTopology hs
  refine (Topology.IsEmbedding.mk ⟨rfl⟩ fun u v huv ↦ ?_).t2Space
  exact sobolevGaugeSubOne_injective hs (congrArg Prod.fst huv)

end TauCeti.Vortex
