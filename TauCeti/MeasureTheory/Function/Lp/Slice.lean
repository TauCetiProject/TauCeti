/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Continuity of the `Lᵖ` classes of the slices of a continuous family

Let `Φ : X → Y → E` be jointly continuous, with every slice `Φ w` vanishing outside one compact
set `K ⊆ Y`. For a locally finite measure `ν` on `Y` and `1 ≤ p < ∞`, the `Lᵖ` classes of the
slices then depend continuously on the parameter: `w ↦ [Φ w] ∈ Lᵖ(Y, ν; E)` is continuous
(`MeasureTheory.Lp.continuous_of_ae_eq_of_continuous_uncurry`). Indeed
`‖[Φ w] - [Φ w₀]‖ ^ p = ∫_K ‖Φ w z - Φ w₀ z‖ ^ p dν(z)` is a parametric integral over a compact set
of a continuous function, hence continuous in `w`, and it vanishes at `w₀`.

Such slices arise for a compactly supported family `Φ` on a product: each slice `Φ (w, ·)`
vanishes outside the projection of the support of `Φ` to `Y`, and the slices vanish altogether
for `w` outside its projection to `X`, so the family of their classes has compact support
(`MeasureTheory.Lp.hasCompactSupport_of_ae_eq_of_hasCompactSupport_uncurry`). Composing with a
continuous operator on `Lᵖ` and a norm, as for the distance of a slice to a closed subspace of
`L²`, then gives continuous compactly supported, hence integrable, functions of the parameter.
-/

public section

namespace MeasureTheory

open Filter Topology
open scoped ENNReal

variable {X Y E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [NormedAddCommGroup E]
  {ν : Measure Y} [IsLocallyFiniteMeasure ν]

/-- **Slices of a continuous family depend continuously on the parameter in `Lᵖ`.** Let
`Φ : X → Y → E` be jointly continuous, with every slice `Φ w` vanishing outside a fixed compact set
`K`, and let `u w ∈ Lᵖ(Y, ν; E)`, `1 ≤ p < ∞`, be the class of `Φ w`. Then `u` is continuous. -/
theorem Lp.continuous_of_ae_eq_of_continuous_uncurry {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {Φ : X → Y → E} (hΦ : Continuous (Function.uncurry Φ)) {K : Set Y} (hK : IsCompact K)
    (hΦK : ∀ w, ∀ z ∉ K, Φ w z = 0) {u : X → Lp E p ν} (hu : ∀ w, u w =ᵐ[ν] Φ w) :
    Continuous u := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine continuous_iff_continuousAt.2 fun w₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  -- The `p`-th power of the distance to the slice at `w₀` is a parametric integral over `K`.
  set G : X → ℝ := fun w ↦ ∫ z in K, ‖Φ w z - Φ w₀ z‖ ^ p.toReal ∂ν
  have hd : Continuous fun q : X × Y ↦ ‖Φ q.1 q.2 - Φ w₀ q.2‖ ^ p.toReal :=
    (hΦ.sub (hΦ.comp ((continuous_const (y := w₀)).prodMk continuous_snd))).norm.rpow_const
      fun _ ↦ .inr hr.le
  have hG : Continuous G :=
    continuous_parametric_integral_of_continuous (f := fun w z ↦ ‖Φ w z - Φ w₀ z‖ ^ p.toReal) hd hK
  have hnorm (w : X) : ‖u w - u w₀‖ = G w ^ p.toReal⁻¹ := by
    rw [← Real.rpow_rpow_inv (norm_nonneg (u w - u w₀)) hr.ne',
      ← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp]
    congr 1
    refine (integral_congr_ae ?_).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_).symm
    · filter_upwards [Lp.coeFn_sub (u w) (u w₀), hu w, hu w₀] with z hz hw hw₀
      rw [hz, Pi.sub_apply, hw, hw₀]
    · simp [hΦK w z hz, hΦK w₀ z hz, hr.ne']
  have hG₀ : G w₀ = 0 := by simp [G, hr.ne']
  simp_rw [hnorm]
  simpa [hG₀, hr.ne'] using (hG.tendsto w₀).rpow_const (.inr (inv_nonneg.2 hr.le))

omit [FirstCountableTopology X] [LocallyCompactSpace X] [OpensMeasurableSpace Y]
  [IsLocallyFiniteMeasure ν] in
/-- **Slices of a compactly supported family form a compactly supported family in `Lᵖ`.** Let
`Φ : X → Y → E` have compact support as a function on `X × Y`, and let `u w ∈ Lᵖ(Y, ν; E)` be the
class of `Φ w`. Then `u` has compact support: `u w = 0` off the projection of the support of `Φ`
to `X`. -/
theorem Lp.hasCompactSupport_of_ae_eq_of_hasCompactSupport_uncurry [R1Space X] {p : ℝ≥0∞}
    {Φ : X → Y → E} (hΦ : HasCompactSupport (Function.uncurry Φ)) {u : X → Lp E p ν}
    (hu : ∀ w, u w =ᵐ[ν] Φ w) : HasCompactSupport u := by
  refine HasCompactSupport.intro (hΦ.image continuous_fst) fun w hw ↦ ?_
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact (hu w).trans (.of_forall fun z ↦
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry Φ) (x := (w, z))
      fun h ↦ hw ⟨(w, z), h, rfl⟩)

end MeasureTheory
