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
# Multiplication and inversion in the Sobolev framed gauge group are continuous

For a real order `s > 1`, the Sobolev framed gauge group `G_s` (`TauCeti.Vortex.sobolevGaugeGroup`)
consists of the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`. It is the
gauge group of the affine space `A_m^k` of framed plane vortex fields, for `s = k + 1`. This file
measures distances in `G_s` by the `H^s` norm of `u - v = (u - 1) - (v - 1)`, and shows that the
group operations are continuous for it.

The `H^s` coordinate `TauCeti.Vortex.sobolevGaugeCoord u ∈ H^s(ℂ)` of `u ∈ G_s` is `u - 1`, as an
element of Mathlib's bundled Bessel-potential space: its `L²` function is `u - 1` almost everywhere
(`TauCeti.Vortex.sobolevGaugeCoord_eq_iff`). It is injective, because the elements of `G_s` are
continuous (`TauCeti.Vortex.sobolevGaugeCoord_injective`). Since `s > 1 = dim ℂ / 2`, `H^s(ℂ)` is an
algebra under pointwise multiplication (`BesselPotentialSpace.mulCLM`), and the group law of `G_s`
reads, in coordinates,

`(1 + h) (1 + g) = 1 + (h + g + h g)`

(`TauCeti.Vortex.sobolevGaugeCoord_mul`). The coordinate `w` of `u⁻¹` is the quasi-inverse of the
coordinate `h` of `u`: `h + w + h w = 0` (`TauCeti.Vortex.sobolevGaugeCoord_inv`).

* **Multiplication is continuous** (`Filter.Tendsto.sobolevGaugeCoord_mul`), since the product of
  `H^s(ℂ)` is a continuous bilinear map.
* **Inversion is continuous** (`Filter.Tendsto.sobolevGaugeCoord_inv`). It is in fact locally
  Lipschitz: with `M` the norm of the multiplication of `H^s(ℂ)` and `K = 1 + M ‖v⁻¹ - 1‖`,
  `‖u⁻¹ - v⁻¹‖ ≤ 2 K² ‖u - v‖` as soon as `2 K M ‖u - v‖ ≤ 1`, all norms in `H^s`
  (`TauCeti.Vortex.norm_sobolevGaugeCoord_inv_sub_le`). Only the algebra structure of `H^s(ℂ)`
  enters: if `c`, `w₀` and `w` are the coordinates of `v`, `v⁻¹` and `u⁻¹`, and `δ`, `ε` are the
  differences of the coordinates of `u, v` and of `u⁻¹, v⁻¹`, the quasi-inverse relations give
  `ε + c ε = X` with `X = -δ - δ w`, and multiplying by the quasi-inverse `1 + w₀` of `1 + c` gives
  `ε = X + w₀ X`.

So `G_s`, with the distance `‖u - v‖_{H^s}`, is a topological group. The type
`↥(sobolevGaugeGroup hs)` already carries the subspace topology of pointwise convergence from
`ℂ → Circle`, so no topology instance is added; continuity is stated through `sobolevGaugeCoord`.
Charts of `G_s`, given by the exponential of `TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential`,
are not treated here.

## Main results

* `TauCeti.Vortex.sobolevGaugeCoord`: the `H^s` coordinate `u - 1` of `u ∈ G_s`.
* `TauCeti.Vortex.sobolevGaugeCoord_injective`: it determines `u`.
* `TauCeti.Vortex.sobolevGaugeCoord_mul`, `TauCeti.Vortex.sobolevGaugeCoord_inv`: the group law in
  coordinates.
* `Filter.Tendsto.sobolevGaugeCoord_mul`, `Filter.Tendsto.sobolevGaugeCoord_inv`: multiplication and
  inversion are continuous for the `H^s` distance.
* `TauCeti.Vortex.norm_sobolevGaugeCoord_inv_sub_le`: inversion is locally Lipschitz.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open BesselPotentialSpace Filter MeasureTheory Module TemperedDistribution
open scoped Topology BesselPotentialSpace

variable {s : ℝ} {hs : 1 < s}

/-- **The `H^s` coordinate of a Sobolev gauge.** For `u ∈ G_s`, the element `u - 1` of `H^s(ℂ)`:
its `L²` function is `u - 1` almost everywhere (`TauCeti.Vortex.sobolevGaugeCoord_eq_iff`). -/
def sobolevGaugeCoord (u : sobolevGaugeGroup hs) : H^{s}(ℂ) :=
  (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of the `H^s` coordinate of `u ∈ G_s` is `u - 1` almost everywhere. -/
theorem toL2_sobolevGaugeCoord (h0 : 0 ≤ s) (u : sobolevGaugeGroup hs) :
    toL2 h0 (sobolevGaugeCoord u) =ᵐ[volume] fun z ↦ ((u : ℂ → Circle) z : ℂ) - 1 := by
  rw [sobolevGaugeCoord, toL2_toBesselPotentialSpace]
  exact (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.2).choose_spec.1

/-- The `H^s` coordinate of `u ∈ G_s` is the element of `H^s(ℂ)` whose `L²` function is `u - 1`
almost everywhere. -/
theorem sobolevGaugeCoord_eq_iff (h0 : 0 ≤ s) {u : sobolevGaugeGroup hs} {h : H^{s}(ℂ)} :
    sobolevGaugeCoord u = h ↔ toL2 h0 h =ᵐ[volume] fun z ↦ ((u : ℂ → Circle) z : ℂ) - 1 := by
  refine ⟨fun e ↦ e ▸ toL2_sobolevGaugeCoord h0 u, fun e ↦ ext_ae h0 ?_⟩
  exact (toL2_sobolevGaugeCoord h0 u).trans e.symm

/-- A Sobolev gauge is determined by its `H^s` coordinate. -/
theorem sobolevGaugeCoord_injective :
    Function.Injective (sobolevGaugeCoord (hs := hs)) := by
  intro u v e
  have h0 : 0 ≤ s := by linarith
  have hae : (fun z ↦ ((u : ℂ → Circle) z : ℂ)) =ᵐ[volume] fun z ↦ ((v : ℂ → Circle) z : ℂ) := by
    filter_upwards [toL2_sobolevGaugeCoord h0 u, toL2_sobolevGaugeCoord h0 v] with z hu hv
    rw [e] at hu
    simpa using hu.symm.trans hv
  have hc : ∀ w : sobolevGaugeGroup hs, Continuous fun z ↦ ((w : ℂ → Circle) z : ℂ) :=
    fun w ↦ continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 w.2).1
  have := (Continuous.ae_eq_iff_eq volume (hc u) (hc v)).1 hae
  exact Subtype.ext (funext fun z ↦ Circle.ext (congrFun this z))

/-- The `H^s` coordinate of the identity gauge is `0`. -/
@[simp]
theorem sobolevGaugeCoord_one : sobolevGaugeCoord (1 : sobolevGaugeGroup hs) = 0 := by
  rw [sobolevGaugeCoord_eq_iff (by linarith : (0 : ℝ) ≤ s), map_zero]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
  simp

/-- The `H^s` coordinate of `u ∈ G_s` vanishes exactly when `u` is the identity. -/
@[simp]
theorem sobolevGaugeCoord_eq_zero_iff {u : sobolevGaugeGroup hs} :
    sobolevGaugeCoord u = 0 ↔ u = 1 :=
  sobolevGaugeCoord_one (hs := hs) ▸ sobolevGaugeCoord_injective.eq_iff

/-- **The group law of `G_s` in `H^s` coordinates**: `(1 + h) (1 + g) = 1 + (h + g + h g)`. -/
theorem sobolevGaugeCoord_mul (u v : sobolevGaugeGroup hs) :
    sobolevGaugeCoord (u * v) = sobolevGaugeCoord u + sobolevGaugeCoord v +
      mulCLM (finrank_real_complex_lt_two_mul hs) (sobolevGaugeCoord u) (sobolevGaugeCoord v) := by
  have h0 : 0 ≤ s := by linarith
  rw [sobolevGaugeCoord_eq_iff h0, map_add, map_add]
  filter_upwards [Lp.coeFn_add (toL2 h0 (sobolevGaugeCoord u) + toL2 h0 (sobolevGaugeCoord v))
      (toL2 h0 (mulCLM (finrank_real_complex_lt_two_mul hs) (sobolevGaugeCoord u)
        (sobolevGaugeCoord v))),
    Lp.coeFn_add (toL2 h0 (sobolevGaugeCoord u)) (toL2 h0 (sobolevGaugeCoord v)),
    toL2_mulCLM (finrank_real_complex_lt_two_mul hs) h0 (sobolevGaugeCoord u)
      (sobolevGaugeCoord v),
    toL2_sobolevGaugeCoord h0 u, toL2_sobolevGaugeCoord h0 v] with z h₁ h₂ h₃ hu hv
  simp only [h₁, h₂, h₃, hu, hv, Pi.add_apply, Subgroup.coe_mul, Pi.mul_apply, Circle.coe_mul]
  ring

/-- **Inversion in `G_s` in `H^s` coordinates.** The coordinate `w` of `u⁻¹` is the quasi-inverse
of the coordinate `h` of `u`, `h + w + h w = 0`, that is `w = -h - h w`. -/
theorem sobolevGaugeCoord_inv (u : sobolevGaugeGroup hs) :
    sobolevGaugeCoord u⁻¹ = -sobolevGaugeCoord u - mulCLM (finrank_real_complex_lt_two_mul hs)
      (sobolevGaugeCoord u) (sobolevGaugeCoord u⁻¹) := by
  have h := sobolevGaugeCoord_mul u u⁻¹
  rw [mul_inv_cancel, sobolevGaugeCoord_one] at h
  linear_combination (norm := module) -h

/-- **Multiplication in `G_s` is continuous for the `H^s` distance.** -/
theorem _root_.Filter.Tendsto.sobolevGaugeCoord_mul {α : Type*} {l : Filter α}
    {f g : α → sobolevGaugeGroup hs} {u v : sobolevGaugeGroup hs}
    (hf : Tendsto (fun a ↦ sobolevGaugeCoord (f a)) l (𝓝 (sobolevGaugeCoord u)))
    (hg : Tendsto (fun a ↦ sobolevGaugeCoord (g a)) l (𝓝 (sobolevGaugeCoord v))) :
    Tendsto (fun a ↦ sobolevGaugeCoord (f a * g a)) l (𝓝 (sobolevGaugeCoord (u * v))) := by
  rw [funext fun a ↦ TauCeti.Vortex.sobolevGaugeCoord_mul (f a) (g a),
    TauCeti.Vortex.sobolevGaugeCoord_mul]
  exact (hf.add hg).add (((mulCLM _).continuous₂.tendsto _).comp (hf.prodMk_nhds hg))

/-- **Inversion in `G_s` is locally Lipschitz for the `H^s` distance.** Let `M` be the norm of the
multiplication of `H^s(ℂ)` and `K = 1 + M ‖v⁻¹ - 1‖_{H^s}`. If `2 K M ‖u - v‖_{H^s} ≤ 1`, then
`‖u⁻¹ - v⁻¹‖_{H^s} ≤ 2 K² ‖u - v‖_{H^s}`. -/
theorem norm_sobolevGaugeCoord_inv_sub_le {u v : sobolevGaugeGroup hs}
    (h : 2 * (1 + ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖ * ‖sobolevGaugeCoord v⁻¹‖) *
      ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖ *
        ‖sobolevGaugeCoord u - sobolevGaugeCoord v‖ ≤ 1) :
    ‖sobolevGaugeCoord u⁻¹ - sobolevGaugeCoord v⁻¹‖ ≤
      2 * (1 + ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖ * ‖sobolevGaugeCoord v⁻¹‖) ^ 2 *
        ‖sobolevGaugeCoord u - sobolevGaugeCoord v‖ := by
  have hw := sobolevGaugeCoord_inv u
  have hw₀ := sobolevGaugeCoord_inv v
  have h₀ := sobolevGaugeCoord_mul v v⁻¹
  rw [mul_inv_cancel, sobolevGaugeCoord_one] at h₀
  set B := mulCLM (finrank_real_complex_lt_two_mul hs)
  set M := ‖B‖
  set c := sobolevGaugeCoord v
  set w₀ := sobolevGaugeCoord v⁻¹
  set w := sobolevGaugeCoord u⁻¹
  set K := 1 + M * ‖w₀‖
  set δ := sobolevGaugeCoord u - c
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

/-- **Inversion in `G_s` is continuous for the `H^s` distance.** -/
theorem _root_.Filter.Tendsto.sobolevGaugeCoord_inv {α : Type*} {l : Filter α}
    {f : α → sobolevGaugeGroup hs} {u : sobolevGaugeGroup hs}
    (hf : Tendsto (fun a ↦ sobolevGaugeCoord (f a)) l (𝓝 (sobolevGaugeCoord u))) :
    Tendsto (fun a ↦ sobolevGaugeCoord (f a)⁻¹) l (𝓝 (sobolevGaugeCoord u⁻¹)) := by
  set M := ‖mulCLM (finrank_real_complex_lt_two_mul hs)‖
  set K := 1 + M * ‖sobolevGaugeCoord u⁻¹‖
  have hd := tendsto_iff_norm_sub_tendsto_zero.1 hf
  have hsmall : ∀ᶠ a in l, 2 * K * M * ‖sobolevGaugeCoord (f a) - sobolevGaugeCoord u‖ ≤ 1 := by
    have := hd.const_mul (2 * K * M)
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds zero_lt_one)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun a ↦ norm_nonneg _) ?_
    (by simpa using hd.const_mul (2 * K ^ 2))
  filter_upwards [hsmall] with a ha
  exact norm_sobolevGaugeCoord_inv_sub_le ha

end TauCeti.Vortex
