/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev topology on the framed gauge group of plane vortices

For a real order `s > 1`, the Sobolev framed gauge group `G_s = {1 + h : h ∈ H^s, |1 + h| = 1}`
(`TauCeti.Vortex.sobolevGaugeGroup`) is a subgroup of `ℂ → Circle`, and as such it carries the
topology of pointwise convergence. The gauge group of the vortex field space `A_m^k` is instead
modelled on the Hilbert space `H^s(ℂ)`: two gauges are close when `u - v` is small in `H^s`. This
file constructs that topology and shows that `G_s` is a Hausdorff topological group for it.

Since `G_s` already has the pointwise topology, the Sobolev topology lives on a type synonym,
`TauCeti.Vortex.SobolevTopologicalGaugeGroup hs`, identified with the subgroup by
`TauCeti.Vortex.SobolevTopologicalGaugeGroup.toSubgroup`. An element `u` determines the element
`subOne u` of `H^s(ℂ)` whose `L²` function is `u - 1`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne`), and `u` is
determined by it (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_injective`), since `u` is
continuous.

The group laws in these coordinates are

`(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)`,    `u⁻¹ - 1 = conj (u - 1)`.

The topology is induced by `u ↦ u - 1 ∈ H^s(ℂ)`, so it is that of the distance `‖u - v‖_{H^s}`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.isEmbedding_subOne`). The product law is polynomial,
and continuous for the `H^s` norm because pointwise multiplication is a continuous bilinear map on
`H^s(ℂ)`, `s > 1` (`BesselPotentialSpace.mulCLM`). Inversion is continuous without discussing
complex conjugation on `H^s`: the coordinate `u⁻¹ - 1` is a locally Lipschitz function of `u - 1`,
and only the algebra structure of `H^s(ℂ)` enters. The element `w = u⁻¹ - 1` is the quasi-inverse
of `h = u - 1`, `h + w + h w = 0`. If `c`, `w₀` are the coordinates of `v`, `v⁻¹`, and `δ`, `ε`
are the differences of the coordinates of `u, v` and of `u⁻¹, v⁻¹`, the quasi-inverse relations
give `ε + c ε = X` with `X = -δ - δ w`, and multiplying by the quasi-inverse `1 + w₀` of `1 + c`
gives `ε = X + w₀ X`.

## Main definitions

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup hs`: the group `G_s`, `s > 1`, with its Sobolev
  topology.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne`: the element `u - 1` of `H^s(ℂ)`.

## Main results

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_mul`: the product law
  `(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)` in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne_inv`: the `L²`
  function of `u⁻¹ - 1` is `conj u - 1`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_inv`: `u⁻¹ - 1` is the quasi-inverse of
  `u - 1` in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.norm_subOne_inv_sub_le`: `u⁻¹ - 1` is a locally
  Lipschitz function of `u - 1` for the `H^s` norm.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.tendsto_subOne_inv`: if `u - 1` converges in
  `H^s(ℂ)`, then so does `u⁻¹ - 1`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isEmbedding_subOne`: the topology of `G_s` is
  induced by the injective map `u ↦ u - 1` into `H^s(ℂ)`, that is, by the distance
  `‖u - v‖_{H^s}`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.continuous_iff`: a map into `G_s` is continuous
  exactly when `u - 1` depends continuously on the parameter in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instIsTopologicalGroup`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instT2Space`: `G_s` is a Hausdorff topological group.

The Banach charts of `G_s`, its completeness and the continuity of its action on the field space
`A_m^k` are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, §3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace

variable {s : ℝ}

/-- **The Sobolev framed gauge group `G_s` with its Sobolev topology**, `s > 1`. As a group it is
the subgroup `sobolevGaugeGroup hs` of `ℂ → Circle` (`SobolevTopologicalGaugeGroup.toSubgroup`);
its topology is that of `u - 1` in `H^s(ℂ)` (`SobolevTopologicalGaugeGroup.isEmbedding_subOne`),
rather than the pointwise topology of the subgroup. -/
def SobolevTopologicalGaugeGroup (hs : 1 < s) : Type := sobolevGaugeGroup hs

namespace SobolevTopologicalGaugeGroup

variable {hs : 1 < s}

private theorem nonneg (hs : 1 < s) : 0 ≤ s := zero_le_one.trans hs.le

instance : Group (SobolevTopologicalGaugeGroup hs) := inferInstanceAs (Group (sobolevGaugeGroup hs))

variable (hs) in
/-- The identification of `SobolevTopologicalGaugeGroup hs` with the subgroup
`sobolevGaugeGroup hs` of `ℂ → Circle`. -/
def toSubgroup : SobolevTopologicalGaugeGroup hs ≃* sobolevGaugeGroup hs := MulEquiv.refl _

/-- **The element `u - 1` of `H^s(ℂ)`** of a Sobolev gauge `u ∈ G_s`: its `L²` function is `u - 1`
(`SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne`). -/
def subOne (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) :=
  (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup
    (toSubgroup hs u).2).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of `subOne u` is `u - 1`. -/
theorem coeFn_toLp_inclusion_subOne (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusion h (subOne u)).toLp =ᵐ[volume]
      fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1 := by
  obtain ⟨hae, -⟩ :=
    (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup (toSubgroup hs u).2).choose_spec
  rw [subOne, toLp_inclusion_toBesselPotentialSpace h _ rfl]
  exact hae

/-- The `L²` function of `subOne u⁻¹` is `conj u - 1`. -/
theorem coeFn_toLp_inclusion_subOne_inv (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusion h (subOne u⁻¹)).toLp =ᵐ[volume]
      fun z ↦ (starRingEnd ℂ) ((toSubgroup hs u : ℂ → Circle) z) - 1 := by
  filter_upwards [coeFn_toLp_inclusion_subOne h u⁻¹] with z hz
  rw [hz, map_inv]
  simp only [InvMemClass.coe_inv, Pi.inv_apply, Circle.coe_inv_eq_conj]

/-- A Sobolev gauge is determined by its element `u - 1` of `H^s(ℂ)`. -/
theorem subOne_injective :
    Function.Injective (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  intro u v huv
  have h := nonneg hs
  have hae := (coeFn_toLp_inclusion_subOne h u).symm.trans
    ((congrArg (fun a ↦ ⇑(inclusion h a).toLp) huv).eventuallyEq.trans
      (coeFn_toLp_inclusion_subOne h v))
  -- Both gauges are continuous, so almost everywhere equality is equality.
  have hcont (w : SobolevTopologicalGaugeGroup hs) :
      Continuous fun z ↦ ((toSubgroup hs w : ℂ → Circle) z : ℂ) - 1 :=
    (continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 (toSubgroup hs w).2).1).sub
      continuous_const
  have heq := (hcont u).ae_eq_iff_eq volume (hcont v) |>.1 hae
  apply (toSubgroup hs).injective
  refine Subtype.ext (funext fun z ↦ Subtype.ext ?_)
  simpa using congrFun heq z

/-- The identity gauge has `u - 1 = 0`. -/
@[simp]
theorem subOne_one : subOne (1 : SobolevTopologicalGaugeGroup hs) = 0 := by
  have h := nonneg hs
  refine toLp_inclusion_injective h (Lp.ext ?_)
  filter_upwards [coeFn_toLp_inclusion_subOne h (1 : SobolevTopologicalGaugeGroup hs),
    Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z h₁ h₂
  rw [h₁, map_zero, toLp_zero, h₂, map_one]
  simp

/-- **The product law in `H^s(ℂ)`:** `(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)`. -/
theorem subOne_mul (u v : SobolevTopologicalGaugeGroup hs) :
    subOne (u * v) = subOne u + subOne v +
      mulCLM (finrank_real_complex_lt_two_mul hs) (subOne u) (subOne v) := by
  have h := nonneg hs
  refine toLp_inclusion_injective h (Lp.ext ?_)
  have hs' := finrank_real_complex_lt_two_mul hs
  filter_upwards [coeFn_toLp_inclusion_subOne h (u * v),
    coeFn_toLp_inclusion_add h (subOne u + subOne v) (mulCLM hs' (subOne u) (subOne v)),
    coeFn_toLp_inclusion_add h (subOne u) (subOne v),
    coeFn_toLp_inclusion_mulCLM hs' h (subOne u) (subOne v),
    coeFn_toLp_inclusion_subOne h u, coeFn_toLp_inclusion_subOne h v]
    with z h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, Pi.add_apply, h₃, Pi.add_apply, h₄, h₅, h₆, map_mul]
  simp only [Subgroup.coe_mul, Pi.mul_apply, Circle.coe_mul]
  ring

/-- **Inversion in `H^s(ℂ)`:** `w = u⁻¹ - 1` is the quasi-inverse of `h = u - 1`,
`h + w + h w = 0`, that is `w = -h - h w`. -/
theorem subOne_inv (u : SobolevTopologicalGaugeGroup hs) :
    subOne u⁻¹ = -subOne u -
      mulCLM (finrank_real_complex_lt_two_mul hs) (subOne u) (subOne u⁻¹) := by
  have h := subOne_mul u u⁻¹
  rw [mul_inv_cancel, subOne_one] at h
  linear_combination (norm := module) -h

/-- **Inversion in `G_s` is locally Lipschitz for the `H^s` distance.** Let `M` be the norm of the
multiplication of `H^s(ℂ)` and `K = 1 + M ‖v⁻¹ - 1‖_{H^s}`. If `2 K M ‖u - v‖_{H^s} ≤ 1`, then
`‖u⁻¹ - v⁻¹‖_{H^s} ≤ 2 K² ‖u - v‖_{H^s}`. -/
theorem norm_subOne_inv_sub_le {u v : SobolevTopologicalGaugeGroup hs}
    (h : 2 * (1 + ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖ * ‖subOne v⁻¹‖) *
      ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖ * ‖subOne u - subOne v‖ ≤ 1) :
    ‖subOne u⁻¹ - subOne v⁻¹‖ ≤
      2 * (1 + ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖ * ‖subOne v⁻¹‖) ^ 2 *
        ‖subOne u - subOne v‖ := by
  have hw := subOne_inv u
  have hw₀ := subOne_inv v
  have h₀ := subOne_mul v v⁻¹
  rw [mul_inv_cancel, subOne_one] at h₀
  set B := mulCLM (finrank_real_complex_lt_two_mul hs)
  set M := ‖B‖
  set c := subOne v
  set w₀ := subOne v⁻¹
  set w := subOne u⁻¹
  set K := 1 + M * ‖w₀‖
  set δ := subOne u - c
  set ε := w - w₀
  set X := -δ - B δ w
  -- `ε` solves `ε + c ε = X`; multiplying by `1 + w₀`, the quasi-inverse of `1 + c`, gives
  -- `ε = X + w₀ X`.
  have key₁ : ε + B c ε = X := by
    simp only [ε, X, δ, map_sub, sub_apply]
    linear_combination (norm := module) hw - hw₀
  have key₂ : X + B w₀ X = ε := by
    have hassoc : B w₀ (B c ε) = B (B w₀ c) ε := (mulCLM_assoc _ _ _ _).symm
    have hcomm : B w₀ c = B c w₀ := mulCLM_comm _ _ _
    rw [← key₁, map_add, hassoc, hcomm]
    calc ε + B c ε + (B w₀ ε + B (B c w₀) ε) = ε + B (c + w₀ + B c w₀) ε := by
          simp only [map_add, add_apply]
          abel
      _ = ε := by rw [← h₀, map_zero, zero_apply, add_zero]
  have hK : 0 ≤ K := by positivity
  have hε : ‖ε‖ ≤ K * ‖X‖ := by
    rw [← key₂]
    calc ‖X + B w₀ X‖ ≤ ‖X‖ + M * ‖w₀‖ * ‖X‖ := (norm_add_le _ _).trans (by
          gcongr; exact B.le_opNorm₂ w₀ X)
      _ = K * ‖X‖ := by ring
  have hX : ‖X‖ ≤ ‖δ‖ + M * ‖δ‖ * (‖w₀‖ + ‖ε‖) := by
    calc ‖X‖ ≤ ‖δ‖ + M * ‖δ‖ * ‖w‖ := (norm_sub_le _ _).trans (by
          rw [norm_neg]; gcongr; exact B.le_opNorm₂ _ _)
      _ ≤ ‖δ‖ + M * ‖δ‖ * (‖w₀‖ + ‖ε‖) := by
          gcongr
          calc ‖w‖ = ‖w₀ + ε‖ := by rw [add_sub_cancel]
            _ ≤ ‖w₀‖ + ‖ε‖ := norm_add_le _ _
  have h₁ := mul_le_mul_of_nonneg_left hX hK
  have h₂ := mul_le_mul_of_nonneg_right h (norm_nonneg ε)
  nlinarith [norm_nonneg δ, norm_nonneg ε]

/-- **Inversion is continuous in the coordinate `u - 1` alone:** if `u - 1` converges in
`H^s(ℂ)`, then so does `u⁻¹ - 1`. -/
theorem tendsto_subOne_inv {α : Type*} {l : Filter α} {f : α → SobolevTopologicalGaugeGroup hs}
    {u : SobolevTopologicalGaugeGroup hs}
    (hf : Tendsto (fun a ↦ subOne (f a)) l (𝓝 (subOne u))) :
    Tendsto (fun a ↦ subOne (f a)⁻¹) l (𝓝 (subOne u⁻¹)) := by
  set M := ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖
  set K := 1 + M * ‖subOne u⁻¹‖
  have hd := tendsto_iff_norm_sub_tendsto_zero.1 hf
  have hsmall : ∀ᶠ a in l, 2 * K * M * ‖subOne (f a) - subOne u‖ ≤ 1 := by
    have := hd.const_mul (2 * K * M)
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds zero_lt_one)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun a ↦ norm_nonneg _) ?_
    (by simpa using hd.const_mul (2 * K ^ 2))
  filter_upwards [hsmall] with a ha
  exact norm_subOne_inv_sub_le ha

/-- **The Sobolev topology of `G_s`**, induced by `u ↦ u - 1 ∈ H^s(ℂ)`. -/
instance : TopologicalSpace (SobolevTopologicalGaugeGroup hs) :=
  .induced subOne inferInstance

/-- **The Sobolev topology of `G_s` is that of the distance `‖u - v‖_{H^s}`**: it is induced by
`u ↦ u - 1`, which is injective. -/
theorem isEmbedding_subOne :
    IsEmbedding (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) :=
  ⟨⟨rfl⟩, subOne_injective⟩

/-- **Continuity into `G_s`.** A map into `G_s` is continuous exactly when `u - 1` depends
continuously on the parameter in `H^s(ℂ)`. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → SobolevTopologicalGaugeGroup hs} :
    Continuous f ↔ Continuous (fun x ↦ subOne (f x)) :=
  isEmbedding_subOne.continuous_iff

/-- `u ↦ u - 1` is continuous from `G_s` to `H^s(ℂ)`. -/
@[fun_prop, continuity]
theorem continuous_subOne : Continuous (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) :=
  isEmbedding_subOne.continuous

/-- `u ↦ u⁻¹ - 1` is continuous from `G_s` to `H^s(ℂ)`, since `u⁻¹ - 1` depends continuously on
`u - 1` (`tendsto_subOne_inv`). -/
@[fun_prop, continuity]
theorem continuous_subOne_inv :
    Continuous (fun u : SobolevTopologicalGaugeGroup hs ↦ subOne u⁻¹) :=
  continuous_iff_continuousAt.2 fun u ↦
    tendsto_subOne_inv (f := id) (continuous_subOne.tendsto u)

/-- **`G_s` is a topological group** for its Sobolev topology: by `subOne_mul`, multiplication
acts on `u - 1` by a continuous polynomial map of `H^s(ℂ)`, and inversion is continuous by
`continuous_subOne_inv`. -/
instance instIsTopologicalGroup : IsTopologicalGroup (SobolevTopologicalGaugeGroup hs) where
  continuous_mul := continuous_iff.2 <| by simp only [subOne_mul]; fun_prop
  continuous_inv := continuous_iff.2 continuous_subOne_inv

/-- `G_s` is Hausdorff for its Sobolev topology, since `u ↦ u - 1` is injective. -/
instance instT2Space : T2Space (SobolevTopologicalGaugeGroup hs) :=
  isEmbedding_subOne.t2Space

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
