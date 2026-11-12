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

For a real order `s > 1` the Sobolev framed gauge group `G_s` (`TauCeti.Vortex.sobolevGaugeGroup`)
consists of the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`. The
**increment** `u - 1`, as an element of the Bessel-potential space `H^s(ℂ)`
(`TauCeti.Vortex.sobolevGaugeIncrement`), determines `u`, so `G_s` embeds into the Hilbert space
`H^s(ℂ)`. This file gives `G_s` the topology of `H^s` convergence of the increments
(`TauCeti.Vortex.sobolevGaugeTopology`) and proves that it makes `G_s` a topological group.

Write `h_u = u - 1`. Since `uv - 1 = h_u + h_v + h_u h_v`, the increment of a product is

`h_(uv) = h_u + h_v + h_u h_v`

(`TauCeti.Vortex.sobolevGaugeIncrement_mul`), with the product of `H^s(ℂ)`, `s > 1`, a bounded
bilinear map (`BesselPotentialSpace.mul`). So multiplication is continuous. For inversion, the
identity `u⁻¹ - v⁻¹ = (v - u) u⁻¹ v⁻¹`, with `u⁻¹ = 1 + h_(u⁻¹)`, gives the bound
`‖h_(u⁻¹) - h_(v⁻¹)‖ ≤ (1 + C ‖h_(u⁻¹)‖) (1 + C ‖h_(v⁻¹)‖) ‖h_u - h_v‖`
(`TauCeti.Vortex.norm_sobolevGaugeIncrement_inv_sub_le`), where `C` is the norm of the product.
Absorbing the term in `‖h_(u⁻¹)‖` for `u` near `v` shows that inversion is continuous.

The `H^s` topology is finer than the topology of uniform convergence: by the Sobolev embedding,
`|u(z) - v(z)| ≤ C ‖h_u - h_v‖_{H^s}` for all `z`
(`TauCeti.Vortex.exists_norm_sub_le_mul_norm_sobolevGaugeIncrement_sub`). In particular it is finer
than the topology of pointwise convergence, which `G_s` carries as a subgroup of `ℂ → Circle`
(`TauCeti.Vortex.sobolevGaugeTopology_le`). For this reason the `H^s` topology is not an instance:
it is a separate topology on the same type.

## Main definitions

* `TauCeti.Vortex.sobolevGaugeIncrement hs u`: the increment `u - 1` of `u ∈ G_s` in `H^s(ℂ)`.
* `TauCeti.Vortex.sobolevGaugeTopology hs`: the topology on `G_s` induced by the increment.

## Main results

* `TauCeti.Vortex.sobolevGaugeIncrement_injective`: the increment determines the gauge.
* `TauCeti.Vortex.sobolevGaugeIncrement_one` and `TauCeti.Vortex.sobolevGaugeIncrement_mul`: the
  increment of `1` is `0` and that of a product is `h_u + h_v + h_u h_v`.
* `TauCeti.Vortex.isTopologicalGroup_sobolevGaugeTopology`: `G_s` is a topological group for the
  `H^s` topology.
* `TauCeti.Vortex.isEmbedding_sobolevGaugeIncrement`: the increment embeds `G_s` into `H^s(ℂ)`.
* `TauCeti.Vortex.sobolevGaugeTopology_le`: the `H^s` topology is finer than the topology of
  pointwise convergence.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Topology TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace SchwartzMap

variable {s : ℝ} {hs : 1 < s}

/-- The **increment** `u - 1` of a gauge `u ∈ G_s`, as an element of the Bessel-potential space
`H^s(ℂ)`. It is characterized by `TauCeti.Vortex.sobolevGaugeIncrement_eq`. -/
def sobolevGaugeIncrement (hs : 1 < s) (u : sobolevGaugeGroup hs) : H^{s}(ℂ) :=
  (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2).choose_spec.2.toBesselPotentialSpace

/-- The increment of `u ∈ G_s` is the element of `H^s(ℂ)` defined by any `L²` function equal to
`u - 1` almost everywhere. -/
theorem sobolevGaugeIncrement_eq (u : sobolevGaugeGroup hs) {h : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : h =ᵐ[volume] fun z ↦ ((u : ℂ → Circle) z : ℂ) - 1)
    (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) :
    sobolevGaugeIncrement hs u = hh.toBesselPotentialSpace := by
  have hc := (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2).choose_spec
  refine BesselPotentialSpace.ext ?_
  simp only [sobolevGaugeIncrement, MemSobolev.toBesselPotentialSpace_toDistr]
  exact congrArg _ (Lp.ext (hc.1.trans hu.symm))

/-- The `L²` function of the increment of `u ∈ G_s` is `u - 1`. -/
theorem toLp_inclusion_sobolevGaugeIncrement (h : 0 ≤ s) (u : sobolevGaugeGroup hs) :
    (inclusion h (sobolevGaugeIncrement hs u)).toLp =ᵐ[volume]
      fun z ↦ ((u : ℂ → Circle) z : ℂ) - 1 := by
  obtain ⟨g, hg, hgs⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2
  rw [sobolevGaugeIncrement_eq u hg hgs, toLp_inclusion_toBesselPotentialSpace]
  exact hg

/-- Elements of `G_s` are continuous as complex-valued maps. -/
private theorem continuous_coe (u : sobolevGaugeGroup hs) :
    Continuous fun z ↦ ((u : ℂ → Circle) z : ℂ) :=
  continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 u.2).1

/-- **The increment determines the gauge.** Two elements of `G_s` with the same increment in
`H^s(ℂ)` are equal. -/
theorem sobolevGaugeIncrement_injective : Function.Injective (sobolevGaugeIncrement hs) := by
  intro u v huv
  have h0 : (0 : ℝ) ≤ s := by linarith
  have hae := (toLp_inclusion_sobolevGaugeIncrement h0 u).symm.trans
    (huv ▸ toLp_inclusion_sobolevGaugeIncrement h0 v)
  have heq := ((continuous_coe u).sub continuous_const).ae_eq_iff_eq volume
    ((continuous_coe v).sub continuous_const) |>.1 hae
  exact Subtype.ext <| funext fun z ↦ Subtype.ext <| sub_left_inj.1 (congrFun heq z)

/-- The increment of the identity is `0`. -/
@[simp]
theorem sobolevGaugeIncrement_one : sobolevGaugeIncrement hs 1 = 0 := by
  have hh : MemSobolev s 2 ((0 : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
    rw [← Lp.toTemperedDistributionCLM_apply, map_zero]
    exact memSobolev_fun_zero ℂ ℂ s 2
  rw [sobolevGaugeIncrement_eq 1 (Lp.coeFn_zero ℂ 2 volume |>.trans (.of_forall fun z ↦ by simp))
    hh]
  exact BesselPotentialSpace.ext (by simp [← Lp.toTemperedDistributionCLM_apply])

/-- **The increment of a product.** For `u, v ∈ G_s`, `uv - 1 = (u - 1) + (v - 1) + (u - 1)(v - 1)`,
so the increment of `uv` is `h_u + h_v + h_u h_v`, with the product of `H^s(ℂ)`. -/
theorem sobolevGaugeIncrement_mul (u v : sobolevGaugeGroup hs) :
    sobolevGaugeIncrement hs (u * v) = sobolevGaugeIncrement hs u + sobolevGaugeIncrement hs v +
      mul (finrank_real_complex_lt_two_mul hs) (sobolevGaugeIncrement hs u)
        (sobolevGaugeIncrement hs v) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨a, ha, has⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2
  obtain ⟨b, hb, hbs⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup v.2
  set k := a + b + (has.memLp_mul hs' b).toLp
  have hks : MemSobolev s 2 (k : 𝓢'(ℂ, ℂ)) := by
    simp only [k, Lp.toTemperedDistribution_add]
    exact (has.add hbs).add (has.mul hs' hbs)
  have hk : k =ᵐ[volume] fun z ↦ (((u * v : sobolevGaugeGroup hs) : ℂ → Circle) z : ℂ) - 1 := by
    filter_upwards [Lp.coeFn_add (a + b) (has.memLp_mul hs' b).toLp, Lp.coeFn_add a b,
      (has.memLp_mul hs' b).coeFn_toLp, ha, hb] with z h₁ h₂ h₃ h₄ h₅
    simp only [Subgroup.coe_mul, Pi.mul_apply, Circle.coe_mul] at h₄ h₅ ⊢
    rw [h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, h₄, h₅]
    ring
  rw [sobolevGaugeIncrement_eq _ hk hks, sobolevGaugeIncrement_eq u ha has,
    sobolevGaugeIncrement_eq v hb hbs, mul_toBesselPotentialSpace]
  exact BesselPotentialSpace.ext (by simp [k, Lp.toTemperedDistribution_add])

/-- The difference of the increments of `u, v ∈ G_s` is the element of `H^s(ℂ)` defined by the
difference of any `L²` functions equal to `u - 1` and `v - 1` almost everywhere. -/
private theorem sobolevGaugeIncrement_sub_eq {u v : sobolevGaugeGroup hs}
    {a b : Lp ℂ 2 (volume : Measure ℂ)} (ha : a =ᵐ[volume] fun z ↦ ((u : ℂ → Circle) z : ℂ) - 1)
    (has : MemSobolev s 2 (a : 𝓢'(ℂ, ℂ)))
    (hb : b =ᵐ[volume] fun z ↦ ((v : ℂ → Circle) z : ℂ) - 1)
    (hbs : MemSobolev s 2 (b : 𝓢'(ℂ, ℂ)))
    (hab : MemSobolev s 2 ((a - b : Lp ℂ 2 volume) : 𝓢'(ℂ, ℂ))) :
    sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v = hab.toBesselPotentialSpace := by
  rw [sobolevGaugeIncrement_eq u ha has, sobolevGaugeIncrement_eq v hb hbs]
  exact BesselPotentialSpace.ext (by simp [Lp.toTemperedDistribution_sub])

/-- The increments of inverses. For `u, v ∈ G_s` put `δ = h_u - h_v`, `g = h_(u⁻¹)` and
`g' = h_(v⁻¹)`. Then `h_(u⁻¹) - h_(v⁻¹) = -(1 + g)(1 + g') δ`, expanded with the product of
`H^s(ℂ)`; this is `u⁻¹ - v⁻¹ = -u⁻¹ v⁻¹ (u - v)`. -/
private theorem sobolevGaugeIncrement_inv_sub_inv (u v : sobolevGaugeGroup hs) :
    sobolevGaugeIncrement hs u⁻¹ - sobolevGaugeIncrement hs v⁻¹ =
      -((sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v) +
        mul (finrank_real_complex_lt_two_mul hs) (sobolevGaugeIncrement hs u⁻¹)
          (sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v) +
        mul (finrank_real_complex_lt_two_mul hs) (sobolevGaugeIncrement hs v⁻¹)
          (sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v) +
        mul (finrank_real_complex_lt_two_mul hs) (sobolevGaugeIncrement hs u⁻¹)
          (mul (finrank_real_complex_lt_two_mul hs) (sobolevGaugeIncrement hs v⁻¹)
            (sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v))) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨a, ha, has⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2
  obtain ⟨b, hb, hbs⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup v.2
  obtain ⟨c, hc, hcs⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u⁻¹.2
  obtain ⟨d, hd, hds⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup v⁻¹.2
  set e := a - b
  have hes : MemSobolev s 2 (e : 𝓢'(ℂ, ℂ)) := by
    simp only [e, Lp.toTemperedDistribution_sub]
    exact has.sub hbs
  set q := (hds.memLp_mul hs' e).toLp
  rw [sobolevGaugeIncrement_sub_eq ha has hb hbs hes, sobolevGaugeIncrement_eq _ hc hcs,
    sobolevGaugeIncrement_eq _ hd hds]
  simp only [mul_toBesselPotentialSpace]
  refine BesselPotentialSpace.ext ?_
  simp only [toDistr_sub, toDistr_neg, toDistr_add, MemSobolev.toBesselPotentialSpace_toDistr,
    ← Lp.toTemperedDistribution_sub, ← Lp.toTemperedDistribution_add,
    ← Lp.toTemperedDistribution_neg]
  refine congrArg _ (Lp.ext ?_)
  filter_upwards [Lp.coeFn_sub c d, Lp.coeFn_neg (e + (hcs.memLp_mul hs' e).toLp + q +
      (hcs.memLp_mul hs' q).toLp),
    Lp.coeFn_add (e + (hcs.memLp_mul hs' e).toLp + q) (hcs.memLp_mul hs' q).toLp,
    Lp.coeFn_add (e + (hcs.memLp_mul hs' e).toLp) q, Lp.coeFn_add e (hcs.memLp_mul hs' e).toLp,
    Lp.coeFn_sub a b, (hcs.memLp_mul hs' e).coeFn_toLp, (hds.memLp_mul hs' e).coeFn_toLp,
    (hcs.memLp_mul hs' q).coeFn_toLp, ha, hb, hc, hd] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ ha hb hc hd
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Subgroup.coe_inv, Pi.inv_apply, Circle.coe_inv] at hc hd
  have hu0 := Circle.coe_ne_zero ((u : ℂ → Circle) z)
  have hv0 := Circle.coe_ne_zero ((v : ℂ → Circle) z)
  rw [h₁, h₂, h₃, h₄, h₅, h₉, h₇, h₈, h₆, hc, hd, ha, hb]
  field_simp
  ring

/-- **Inversion is locally Lipschitz for the increments.** With `C` the norm of the product of
`H^s(ℂ)`, `‖h_(u⁻¹) - h_(v⁻¹)‖ ≤ (1 + C ‖h_(u⁻¹)‖) (1 + C ‖h_(v⁻¹)‖) ‖h_u - h_v‖`. -/
theorem norm_sobolevGaugeIncrement_inv_sub_le (u v : sobolevGaugeGroup hs) :
    ‖sobolevGaugeIncrement hs u⁻¹ - sobolevGaugeIncrement hs v⁻¹‖ ≤
      (1 + ‖mul (finrank_real_complex_lt_two_mul hs)‖ * ‖sobolevGaugeIncrement hs u⁻¹‖) *
        (1 + ‖mul (finrank_real_complex_lt_two_mul hs)‖ * ‖sobolevGaugeIncrement hs v⁻¹‖) *
          ‖sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v‖ := by
  rw [sobolevGaugeIncrement_inv_sub_inv, norm_neg]
  set μ := mul (finrank_real_complex_lt_two_mul hs)
  set g := sobolevGaugeIncrement hs u⁻¹
  set g' := sobolevGaugeIncrement hs v⁻¹
  set δ := sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v
  have h₁ := μ.le_opNorm₂ g δ
  have h₂ := μ.le_opNorm₂ g' δ
  have h₃ := μ.le_opNorm₂ g (μ g' δ)
  calc ‖δ + μ g δ + μ g' δ + μ g (μ g' δ)‖
      ≤ ‖δ‖ + ‖μ g δ‖ + ‖μ g' δ‖ + ‖μ g (μ g' δ)‖ := norm_add₄_le
    _ ≤ ‖δ‖ + ‖μ‖ * ‖g‖ * ‖δ‖ + ‖μ‖ * ‖g'‖ * ‖δ‖ + ‖μ‖ * ‖g‖ * (‖μ‖ * ‖g'‖ * ‖δ‖) := by
        gcongr
        exact h₃.trans (by gcongr)
    _ = (1 + ‖μ‖ * ‖g‖) * (1 + ‖μ‖ * ‖g'‖) * ‖δ‖ := by ring

variable (hs) in
/-- The **`H^s` topology** on the Sobolev framed gauge group `G_s`: the topology induced by the
increment `u ↦ u - 1 ∈ H^s(ℂ)`. It is not an instance, since `G_s` already carries the topology of
pointwise convergence as a subgroup of `ℂ → Circle`; the `H^s` topology is finer
(`TauCeti.Vortex.sobolevGaugeTopology_le`). -/
@[instance_reducible]
def sobolevGaugeTopology : TopologicalSpace (sobolevGaugeGroup hs) :=
  .induced (sobolevGaugeIncrement hs) inferInstance

variable (hs) in
/-- The increment embeds `G_s`, with its `H^s` topology, into `H^s(ℂ)`. -/
theorem isEmbedding_sobolevGaugeIncrement :
    @Topology.IsEmbedding _ _ (sobolevGaugeTopology hs) _ (sobolevGaugeIncrement hs) :=
  sobolevGaugeIncrement_injective.isEmbedding_induced

/-- In the `H^s` topology, `‖h_u - h_v‖ → 0` as `u → v`. -/
private theorem tendsto_norm_sobolevGaugeIncrement_sub (v : sobolevGaugeGroup hs) :
    Tendsto (fun u ↦ ‖sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v‖)
      (@nhds _ (sobolevGaugeTopology hs) v) (𝓝 0) := by
  let _ : TopologicalSpace (sobolevGaugeGroup hs) := sobolevGaugeTopology hs
  exact tendsto_iff_norm_sub_tendsto_zero.1 <|
    (continuous_induced_dom (f := sobolevGaugeIncrement hs)).tendsto v

variable (hs) in
/-- **`G_s` is a topological group** for the `H^s` topology: multiplication and inversion are
continuous. -/
theorem isTopologicalGroup_sobolevGaugeTopology :
    @IsTopologicalGroup (sobolevGaugeGroup hs) (sobolevGaugeTopology hs) _ := by
  let _ : TopologicalSpace (sobolevGaugeGroup hs) := sobolevGaugeTopology hs
  have hi : Continuous (sobolevGaugeIncrement hs) := continuous_induced_dom
  set μ := mul (finrank_real_complex_lt_two_mul hs)
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · -- `h_(uv) = h_u + h_v + h_u h_v` depends continuously on `(h_u, h_v)`.
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, sobolevGaugeIncrement_mul]
    exact ((hi.comp continuous_fst).add (hi.comp continuous_snd)).add
      (μ.continuous₂.comp ((hi.comp continuous_fst).prodMk (hi.comp continuous_snd)))
  · -- Near `v`, absorb the term `C ‖h_(u⁻¹) - h_(v⁻¹)‖ ‖h_u - h_v‖` of the Lipschitz bound.
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun v ↦ ?_)
    set A := 1 + ‖μ‖ * ‖sobolevGaugeIncrement hs v⁻¹‖
    have hδ := tendsto_norm_sobolevGaugeIncrement_sub v
    have hsmall : ∀ᶠ u in 𝓝 v,
        ‖μ‖ * A * ‖sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v‖ ≤ 1 / 2 := by
      have h := hδ.const_mul (‖μ‖ * A)
      rw [mul_zero] at h
      exact h.eventually (eventually_le_nhds (by norm_num))
    refine tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _)
      (hsmall.mono fun u hu ↦ ?_) (by simpa using hδ.const_mul (2 * A ^ 2))
    set X := ‖sobolevGaugeIncrement hs u⁻¹ - sobolevGaugeIncrement hs v⁻¹‖
    set δ := ‖sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v‖
    have hle := norm_sobolevGaugeIncrement_inv_sub_le u v
    have hg : ‖sobolevGaugeIncrement hs u⁻¹‖ ≤ ‖sobolevGaugeIncrement hs v⁻¹‖ + X := by
      simpa [add_comm] using norm_le_norm_add_norm_sub' (sobolevGaugeIncrement hs u⁻¹)
        (sobolevGaugeIncrement hs v⁻¹)
    have h₁ : 1 + ‖μ‖ * ‖sobolevGaugeIncrement hs u⁻¹‖ ≤ A + ‖μ‖ * X := by
      have := mul_le_mul_of_nonneg_left hg (norm_nonneg μ)
      simp only [A]
      linarith
    have hX : X ≤ (A + ‖μ‖ * X) * A * δ :=
      hle.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h₁ (by positivity)) (norm_nonneg _))
    have hX0 : 0 ≤ X := norm_nonneg _
    have : ‖μ‖ * A * δ * X ≤ X / 2 := by nlinarith
    simp only [Function.comp_apply]
    exact (by nlinarith : X ≤ 2 * A ^ 2 * δ)

/-- **The Sobolev embedding for gauges.** There is `C` such that
`|u(z) - v(z)| ≤ C ‖h_u - h_v‖_{H^s}` for all `u, v ∈ G_s` and all `z`: convergence in the `H^s`
topology implies uniform convergence. -/
theorem exists_norm_sub_le_mul_norm_sobolevGaugeIncrement_sub (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ (u v : sobolevGaugeGroup hs) (z : ℂ),
      ‖((u : ℂ → Circle) z : ℂ) - (v : ℂ → Circle) z‖ ≤
        C * ‖sobolevGaugeIncrement hs u - sobolevGaugeIncrement hs v‖ := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨C, hC, hsup⟩ := exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (F := ℂ) hs'
  refine ⟨C, hC, fun u v ↦ ?_⟩
  obtain ⟨a, ha, has⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2
  obtain ⟨b, hb, hbs⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup v.2
  have hes : MemSobolev s 2 ((a - b : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
    rw [Lp.toTemperedDistribution_sub]
    exact has.sub hbs
  rw [sobolevGaugeIncrement_sub_eq ha has hb hbs hes]
  set K := C * ‖hes.toBesselPotentialSpace‖
  -- The bound holds almost everywhere, and both sides are continuous.
  have hf : Continuous fun z ↦ ‖((u : ℂ → Circle) z : ℂ) - (v : ℂ → Circle) z‖ :=
    ((continuous_coe u).sub (continuous_coe v)).norm
  have hae : (fun z ↦ min ‖((u : ℂ → Circle) z : ℂ) - (v : ℂ → Circle) z‖ K) =ᵐ[volume]
      fun z ↦ ‖((u : ℂ → Circle) z : ℂ) - (v : ℂ → Circle) z‖ := by
    filter_upwards [hsup hes, Lp.coeFn_sub a b, ha, hb] with z hz h₁ h₂ h₃
    rw [h₁, Pi.sub_apply, h₂, h₃, sub_sub_sub_cancel_right] at hz
    exact min_eq_left hz
  have heq := ((hf.min continuous_const).ae_eq_iff_eq volume hf).1 hae
  exact fun z ↦ min_eq_left_iff.1 (congrFun heq z)

variable (hs) in
/-- The `H^s` topology on `G_s` is finer than its topology of pointwise convergence as a subgroup
of `ℂ → Circle`. -/
theorem sobolevGaugeTopology_le :
    sobolevGaugeTopology hs ≤ (inferInstance : TopologicalSpace (sobolevGaugeGroup hs)) := by
  let _ : TopologicalSpace (sobolevGaugeGroup hs) := sobolevGaugeTopology hs
  obtain ⟨C, -, hC⟩ := exists_norm_sub_le_mul_norm_sobolevGaugeIncrement_sub hs
  refine continuous_id_iff_le.1 (continuous_induced_rng.2 (continuous_pi fun z ↦ ?_))
  refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun v ↦ ?_)
  refine tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun u ↦ hC u v z) ?_
  simpa using (tendsto_norm_sobolevGaugeIncrement_sub v).const_mul C

end TauCeti.Vortex
