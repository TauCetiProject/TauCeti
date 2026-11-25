/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Conj

/-!
# The Sobolev topology on the framed gauge group of plane vortices

For a real order `s > 1`, the Sobolev framed gauge group `G_s = {1 + h : h ∈ H^s, |1 + h| = 1}`
(`TauCeti.Vortex.sobolevGaugeGroup`) is a subgroup of `ℂ → Circle`, and as such it carries the
topology of pointwise convergence. The gauge group of the vortex field space `A_m^k` is instead
modelled on the Hilbert space `H^s(ℂ)`: two gauges are close when `u - v` is small in `H^s`. This
file constructs that topology and shows that `G_s` is a Hausdorff topological group for it, and
that it is complete: `G_s` is a closed subset of the affine Hilbert space `1 + H^s(ℂ)`.

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
complex conjugation on `H^s`: the element `u⁻¹ - 1` is the quasi-inverse of `u - 1`, and the
algebra structure of `H^s(ℂ)` alone then bounds `‖u⁻¹ - v⁻¹‖_{H^s}` linearly in `‖u - v‖_{H^s}`
for `u` near each `v`.

Completeness uses complex conjugation on `H^s(ℂ)`, an isometry
(`TemperedDistribution.MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj`); in particular
`‖u⁻¹ - 1‖_{H^s} = ‖u - 1‖_{H^s}`. If `uₙ - 1 → h` in `H^s(ℂ)`, the values converge almost
everywhere by the Sobolev embedding, so the continuous representative of `h` satisfies
`|1 + h| = 1`; and the real and imaginary parts of `h` lie in `H^s` because conjugation preserves
`H^s(ℂ)` (`TemperedDistribution.re_mem_realSobolevFunctions`,
`TemperedDistribution.im_mem_realSobolevFunctions`). So `1 + h` is again an element of `G_s`.

## Main definitions

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup hs`: the group `G_s`, `s > 1`, with its Sobolev
  topology.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne`: the element `u - 1` of `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.reSubOne`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.imPart`: the elements `Re u - 1` and `Im u` of
  `H^s(ℂ)`, which depend continuously on `u`.

## Main results

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_mul`: the product law
  `(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)` in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne_inv`: the `L²`
  function of `u⁻¹ - 1` is `conj u - 1`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_inv`: `u⁻¹ - 1` is the quasi-inverse of
  `u - 1` in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.norm_subOne_inv_sub_le`: a Lipschitz bound for
  inversion at a point `v`: `‖u⁻¹ - v⁻¹‖_{H^s} ≤ 2 K² ‖u - v‖_{H^s}` once `‖u - v‖_{H^s}` is small
  compared with `K = 1 + M ‖v⁻¹ - 1‖_{H^s}`, where `M` is the norm of the multiplication
  `BesselPotentialSpace.mulCLM` of `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.tendsto_subOne_inv`: if `u_a - 1 → u - 1` in
  `H^s(ℂ)` for some `u ∈ G_s`, then `u_a⁻¹ - 1 → u⁻¹ - 1`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isEmbedding_subOne`: the topology of `G_s` is
  induced by the injective map `u ↦ u - 1` into `H^s(ℂ)`, that is, by the distance
  `‖u - v‖_{H^s}`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.continuous_iff`: a map into `G_s` is continuous
  exactly when `u - 1` depends continuously on the parameter in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instIsTopologicalGroup`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instT2Space`: `G_s` is a Hausdorff topological group.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.norm_subOne_inv`: `‖u⁻¹ - 1‖_{H^s} = ‖u - 1‖_{H^s}`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isClosed_range_subOne`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isClosedEmbedding_subOne`: `u ↦ u - 1` is a closed
  embedding of `G_s` into `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.exists_tendsto_of_cauchySeq`: `G_s` is complete for
  the distance `‖u - v‖_{H^s}`.

The Banach charts of `G_s` are not treated here; the continuity of its action on the field space
`A_m^k` is in `TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
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

/-- `G_s` is commutative: gauges multiply pointwise. -/
instance : CommGroup (SobolevTopologicalGaugeGroup hs) :=
  inferInstanceAs (CommGroup (sobolevGaugeGroup hs))

variable (hs) in
/-- The identification of `SobolevTopologicalGaugeGroup hs` with the subgroup
`sobolevGaugeGroup hs` of `ℂ → Circle`. -/
def toSubgroup : SobolevTopologicalGaugeGroup hs ≃* sobolevGaugeGroup hs := MulEquiv.refl _

/-- **The element `u - 1` of `H^s(ℂ)`** of a Sobolev gauge `u ∈ G_s`: its `L²` function is `u - 1`
(`SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne`). -/
def subOne (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) :=
  (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup
    (toSubgroup hs u).property).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of `subOne u` is `u - 1`. -/
theorem coeFn_toLp_inclusion_subOne (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusion h (subOne u)).toLp =ᵐ[volume]
      fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1 := by
  obtain ⟨hae, -⟩ :=
    (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup (toSubgroup hs u).property).choose_spec
  rw [subOne, toLp_inclusion_toBesselPotentialSpace h _ rfl]
  exact hae

/-- The `L²` function of `subOne u⁻¹` is `conj u - 1`. -/
theorem coeFn_toLp_inclusion_subOne_inv (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusion h (subOne u⁻¹)).toLp =ᵐ[volume]
      fun z ↦ (starRingEnd ℂ) ((toSubgroup hs u : ℂ → Circle) z) - 1 := by
  filter_upwards [coeFn_toLp_inclusion_subOne h u⁻¹] with z hz
  rw [hz, map_inv]
  simp only [InvMemClass.coe_inv, Pi.inv_apply, Circle.coe_inv_eq_conj]

/-- A Sobolev gauge is continuous as a map into `ℂ`. -/
theorem continuous_coe_toSubgroup (u : SobolevTopologicalGaugeGroup hs) :
    Continuous fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) :=
  continuous_subtypeVal.comp ((mem_sobolevGaugeGroup hs _).1 (toSubgroup hs u).property).1

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
    (continuous_coe_toSubgroup w).sub continuous_const
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

/-- **A Lipschitz bound for inversion in `G_s` at `v`, for the `H^s` distance.** Let `M` be the
norm of the multiplication of `H^s(ℂ)` and `K = 1 + M ‖v⁻¹ - 1‖_{H^s}`. If
`2 K M ‖u - v‖_{H^s} ≤ 1`, then `‖u⁻¹ - v⁻¹‖_{H^s} ≤ 2 K² ‖u - v‖_{H^s}`. The radius and the
constant depend on `v`. -/
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
  -- `ε` solves `ε + c ε = X`; multiplying by `1 + w₀`, the inverse of `1 + c`, gives
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

/-- **Inversion is continuous in the coordinate `u - 1` alone:** if `f a - 1 → u - 1` in
`H^s(ℂ)` along `l` for some `u ∈ G_s`, then `(f a)⁻¹ - 1 → u⁻¹ - 1`. -/
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

/-- **The element `Re u - 1` of `H^s(ℂ)`** of a Sobolev gauge `u ∈ G_s`, namely
`((u - 1) + (u⁻¹ - 1)) / 2`: its `L²` function is `Re u - 1`
(`SobolevTopologicalGaugeGroup.coeFn_inclusionLp_reSubOne`). -/
def reSubOne (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) :=
  (2 : ℂ)⁻¹ • (subOne u + subOne u⁻¹)

/-- **The element `Im u` of `H^s(ℂ)`** of a Sobolev gauge `u ∈ G_s`, namely
`-i ((u - 1) - (u⁻¹ - 1)) / 2`: its `L²` function is `Im u`
(`SobolevTopologicalGaugeGroup.coeFn_inclusionLp_imPart`). -/
def imPart (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) :=
  (-(Complex.I / 2)) • (subOne u - subOne u⁻¹)

/-- `Re u - 1` is the average `((u - 1) + (u⁻¹ - 1)) / 2` in `H^s(ℂ)`. -/
theorem reSubOne_def (u : SobolevTopologicalGaugeGroup hs) :
    reSubOne u = (2 : ℂ)⁻¹ • (subOne u + subOne u⁻¹) :=
  (rfl)

/-- `Im u` is `-i ((u - 1) - (u⁻¹ - 1)) / 2` in `H^s(ℂ)`. -/
theorem imPart_def (u : SobolevTopologicalGaugeGroup hs) :
    imPart u = (-(Complex.I / 2)) • (subOne u - subOne u⁻¹) :=
  (rfl)

/-- The identity gauge has `Re u - 1 = 0`. -/
@[simp]
theorem reSubOne_one : reSubOne (1 : SobolevTopologicalGaugeGroup hs) = 0 := by
  simp [reSubOne_def]

/-- The identity gauge has `Im u = 0`. -/
@[simp]
theorem imPart_one : imPart (1 : SobolevTopologicalGaugeGroup hs) = 0 := by
  simp [imPart_def]

/-- `u ↦ Re u - 1` is continuous from `G_s` to `H^s(ℂ)`. -/
@[fun_prop, continuity]
theorem continuous_reSubOne :
    Continuous (reSubOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  unfold reSubOne
  fun_prop

/-- `u ↦ Im u` is continuous from `G_s` to `H^s(ℂ)`. -/
@[fun_prop, continuity]
theorem continuous_imPart :
    Continuous (imPart : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  unfold imPart
  fun_prop

/-- The `L²` function of `reSubOne u` is `Re u - 1`. -/
theorem coeFn_inclusionLp_reSubOne (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusionLp h (reSubOne u)) =ᵐ[volume]
      fun z ↦ ((((toSubgroup hs u : ℂ → Circle) z : ℂ).re - 1 : ℝ) : ℂ) := by
  have h₁ := coeFn_toLp_inclusion_subOne h u
  have h₂ := coeFn_toLp_inclusion_subOne_inv h u
  rw [toLp_inclusion] at h₁ h₂
  filter_upwards [coeFn_inclusionLp_smul_ae_eq h (2 : ℂ)⁻¹
    (coeFn_inclusionLp_add_ae_eq h h₁ h₂)] with z hz
  rw [reSubOne_def, hz]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The `L²` function of `imPart u` is `Im u`. -/
theorem coeFn_inclusionLp_imPart (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusionLp h (imPart u)) =ᵐ[volume]
      fun z ↦ ((((toSubgroup hs u : ℂ → Circle) z : ℂ).im : ℝ) : ℂ) := by
  have h₁ := coeFn_toLp_inclusion_subOne h u
  have h₂ := coeFn_toLp_inclusion_subOne_inv h u
  rw [toLp_inclusion] at h₁ h₂
  filter_upwards [coeFn_inclusionLp_smul_ae_eq h (-(Complex.I / 2))
    (coeFn_inclusionLp_sub_ae_eq h h₁ h₂)] with z hz
  rw [imPart_def, hz]
  apply Complex.ext
  · simp
    ring
  · simp

/-- **`G_s` is a topological group** for its Sobolev topology: by `subOne_mul`, multiplication
acts on `u - 1` by a continuous polynomial map of `H^s(ℂ)`, and inversion is continuous by
`continuous_subOne_inv`. -/
instance instIsTopologicalGroup : IsTopologicalGroup (SobolevTopologicalGaugeGroup hs) where
  continuous_mul := continuous_iff.2 <| by simp only [subOne_mul]; fun_prop
  continuous_inv := continuous_iff.2 continuous_subOne_inv

/-- `G_s` is Hausdorff for its Sobolev topology, since `u ↦ u - 1` is injective. -/
instance instT2Space : T2Space (SobolevTopologicalGaugeGroup hs) :=
  isEmbedding_subOne.t2Space

/-- **Inversion preserves the distance to the identity:** `‖u⁻¹ - 1‖_{H^s} = ‖u - 1‖_{H^s}`, since
`u⁻¹ - 1 = conj (u - 1)` and complex conjugation is an isometry of `H^s(ℂ)`. -/
@[simp]
theorem norm_subOne_inv (u : SobolevTopologicalGaugeGroup hs) : ‖subOne u⁻¹‖ = ‖subOne u‖ := by
  have h := nonneg hs
  have hae : ⇑(inclusion h (subOne u⁻¹)).toLp =ᵐ[volume]
      fun z ↦ (starRingEnd ℂ) ((inclusion h (subOne u)).toLp z) := by
    filter_upwards [coeFn_toLp_inclusion_subOne_inv h u, coeFn_toLp_inclusion_subOne h u]
      with z h₁ h₂
    rw [h₁, h₂, map_sub, map_one]
  simp only [toLp_inclusion] at hae
  have hn := (memSobolev_inclusionLp h (subOne u)).norm_toBesselPotentialSpace_of_ae_eq_conj
    hae (memSobolev_inclusionLp h (subOne u⁻¹))
  rwa [toBesselPotentialSpace_memSobolev_inclusionLp,
    toBesselPotentialSpace_memSobolev_inclusionLp] at hn

/-- **The range of `u ↦ u - 1` is closed in `H^s(ℂ)`.** If gauges `uₙ ∈ G_s` have `uₙ - 1 → h` in
`H^s(ℂ)`, then `h = u - 1` for a gauge `u ∈ G_s`: the continuous representative of `h` has
`|1 + h| = 1`, as an almost everywhere limit of the values of `uₙ - 1`, and the real and imaginary
parts of `h` lie in `H^s` because complex conjugation preserves `H^s(ℂ)`. -/
theorem isClosed_range_subOne :
    IsClosed (Set.range (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ))) := by
  have h0 := nonneg hs
  have hs' := finrank_real_complex_lt_two_mul hs
  refine isClosed_of_closure_subset fun h hh ↦ ?_
  obtain ⟨x, hx, hxh⟩ := mem_closure_iff_seq_limit.1 hh
  choose u hu using hx
  set H : Lp ℂ 2 (volume : Measure ℂ) := inclusionLp h0 h
  have hH : MemSobolev s 2 (H : 𝓢'(ℂ, ℂ)) := memSobolev_inclusionLp h0 h
  obtain ⟨g, hg⟩ := hH.exists_zeroAtInftyContinuousMap_ae_eq hs'
  -- The values of `uₙ - 1` converge almost everywhere to those of `h`, so `|1 + g| = 1` almost
  -- everywhere, hence everywhere by continuity.
  have hlim := ae_tendsto_of_tendsto_toBesselPotentialSpace hs'
    (fun n ↦ memSobolev_inclusionLp h0 (subOne (u n))) hH (by
      simpa only [toBesselPotentialSpace_memSobolev_inclusionLp, hu] using hxh)
  have hgc : Continuous fun z ↦ 1 + g z := continuous_const.add g.continuous
  have hnorm : ∀ z, ‖1 + g z‖ = 1 := by
    refine congrFun ((hgc.norm.ae_eq_iff_eq volume continuous_const).1 ?_)
    filter_upwards [hlim, hg, ae_all_iff.2 fun n ↦ coeFn_toLp_inclusion_subOne h0 (u n)]
      with z hz hgz hun
    have h₁ := (hz.const_add 1).norm
    simp only [← toLp_inclusion, hun, add_sub_cancel, Circle.norm_coe] at h₁
    rw [← hgz]
    exact (tendsto_nhds_unique tendsto_const_nhds h₁).symm
  set w : ℂ → Circle := fun z ↦ ⟨1 + g z, mem_sphere_zero_iff_norm.2 (hnorm z)⟩
  have hw : w ∈ sobolevGaugeGroup hs := by
    refine (mem_sobolevGaugeGroup hs w).2 ⟨hgc.subtype_mk _, ?_, ?_⟩
    · refine mem_realSobolevFunctions_of_ae_eq (re_mem_realSobolevFunctions hH) ?_
      filter_upwards [hg] with z hz
      simp [w, hz]
    · refine mem_realSobolevFunctions_of_ae_eq (im_mem_realSobolevFunctions hH) ?_
      filter_upwards [hg] with z hz
      simp [w, hz]
  refine ⟨(toSubgroup hs).symm ⟨w, hw⟩, inclusionLp_injective h0 (Lp.ext ?_)⟩
  filter_upwards [coeFn_toLp_inclusion_subOne h0 ((toSubgroup hs).symm ⟨w, hw⟩), hg]
    with z h₁ h₂
  rw [← toLp_inclusion, h₁, h₂]
  simp [w]

/-- **`G_s` is a closed subset of `1 + H^s(ℂ)`:** `u ↦ u - 1` is a closed embedding of `G_s`, with
its Sobolev topology, into `H^s(ℂ)`. -/
theorem isClosedEmbedding_subOne :
    IsClosedEmbedding (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) :=
  ⟨isEmbedding_subOne, isClosed_range_subOne⟩

/-- The range of `u ↦ u - 1` is a complete subset of `H^s(ℂ)`. -/
theorem isComplete_range_subOne :
    IsComplete (Set.range (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ))) :=
  isClosed_range_subOne.isComplete

/-- **`G_s` is complete for the `H^s` distance:** if `uₙ - 1` is a Cauchy sequence in `H^s(ℂ)`,
then `uₙ` converges in `G_s`. -/
theorem exists_tendsto_of_cauchySeq {u : ℕ → SobolevTopologicalGaugeGroup hs}
    (hu : CauchySeq fun n ↦ subOne (u n)) : ∃ v, Tendsto u atTop (𝓝 v) := by
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete hu
  obtain ⟨v, rfl⟩ := isClosed_range_subOne.mem_of_tendsto hh (.of_forall fun n ↦ ⟨u n, rfl⟩)
  exact ⟨v, isEmbedding_subOne.tendsto_nhds_iff.2 hh⟩

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
