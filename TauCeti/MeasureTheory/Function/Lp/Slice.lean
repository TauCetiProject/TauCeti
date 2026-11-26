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
# Continuity of the `L²` classes of the slices of a continuous family

Let `Φ : X → Y → E` be jointly continuous, with every slice `Φ w` vanishing outside one compact
set `K ⊆ Y`. For a locally finite measure `ν` on `Y`, the `L²` classes of the slices then depend
continuously on the parameter: `w ↦ [Φ w] ∈ L²(Y, ν; E)` is continuous
(`MeasureTheory.Lp.continuous_of_ae_eq_of_continuous_uncurry`). Indeed
`‖[Φ w] - [Φ w₀]‖² = ∫_K ‖Φ w z - Φ w₀ z‖² dν(z)` is a parametric integral over a compact set of a
continuous function, hence continuous in `w`, and it vanishes at `w₀`.

Such slices arise for a compactly supported family `Φ` on a product: each slice `Φ (w, ·)`
vanishes outside the projection of the support of `Φ` to `Y`, and the slices vanish altogether
for `w` outside its projection to `X`, so the family of their classes has compact support
(`MeasureTheory.Lp.hasCompactSupport_of_ae_eq_of_hasCompactSupport_uncurry`). Composing with a
continuous operator on `L²` and a norm, as for the distance of a slice to a closed subspace, then
gives continuous compactly supported, hence integrable, functions of the parameter.
-/

public section

namespace MeasureTheory

open Filter Topology

variable {X Y E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [NormedAddCommGroup E]
  {ν : Measure Y} [IsLocallyFiniteMeasure ν]

/-- **Slices of a continuous family depend continuously on the parameter in `L²`.** Let
`Φ : X → Y → E` be jointly continuous, with every slice `Φ w` vanishing outside a fixed compact set
`K`, and let `u w ∈ L²(Y, ν; E)` be the class of `Φ w`. Then `u` is continuous. -/
theorem Lp.continuous_of_ae_eq_of_continuous_uncurry {Φ : X → Y → E}
    (hΦ : Continuous (Function.uncurry Φ)) {K : Set Y} (hK : IsCompact K)
    (hΦK : ∀ w, ∀ z ∉ K, Φ w z = 0) {u : X → Lp E 2 ν} (hu : ∀ w, u w =ᵐ[ν] Φ w) :
    Continuous u := by
  refine continuous_iff_continuousAt.2 fun w₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  -- The squared distance to the slice at `w₀` is a parametric integral over `K`.
  set G : X → ℝ := fun w ↦ ∫ z in K, ‖Φ w z - Φ w₀ z‖ ^ 2 ∂ν
  have hd : Continuous fun p : X × Y ↦ ‖Φ p.1 p.2 - Φ w₀ p.2‖ ^ 2 :=
    (hΦ.sub (hΦ.comp ((continuous_const (y := w₀)).prodMk continuous_snd))).norm.pow 2
  have hG : Continuous G :=
    continuous_parametric_integral_of_continuous (f := fun w z ↦ ‖Φ w z - Φ w₀ z‖ ^ 2) hd hK
  have hm (w : X) : MemLp (Φ w) 2 ν := (Lp.memLp (u w)).ae_eq (hu w)
  have hnorm (w : X) : ‖u w - u w₀‖ = √(G w) := by
    have hw : u w = (hm w).toLp (Φ w) := Lp.ext ((hu w).trans (hm w).coeFn_toLp.symm)
    have hw₀ : u w₀ = (hm w₀).toLp (Φ w₀) := Lp.ext ((hu w₀).trans (hm w₀).coeFn_toLp.symm)
    rw [hw, hw₀, ← MemLp.toLp_sub, ← Real.sqrt_sq (norm_nonneg _), MemLp.norm_toLp_sq]
    congr 1
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_).symm
    simp [hΦK w z hz, hΦK w₀ z hz]
  have hG₀ : G w₀ = 0 := by simp [G]
  simp_rw [hnorm]
  simpa [hG₀] using (hG.tendsto w₀).sqrt

omit [FirstCountableTopology X] [LocallyCompactSpace X] [OpensMeasurableSpace Y]
  [IsLocallyFiniteMeasure ν] in
/-- **Slices of a compactly supported family form a compactly supported family in `L²`.** Let
`Φ : X → Y → E` have compact support as a function on `X × Y`, and let `u w ∈ L²(Y, ν; E)` be the
class of `Φ w`. Then `u` has compact support: `u w = 0` off the projection of the support of `Φ`
to `X`. -/
theorem Lp.hasCompactSupport_of_ae_eq_of_hasCompactSupport_uncurry [R1Space X] {Φ : X → Y → E}
    (hΦ : HasCompactSupport (Function.uncurry Φ)) {u : X → Lp E 2 ν}
    (hu : ∀ w, u w =ᵐ[ν] Φ w) : HasCompactSupport u := by
  refine HasCompactSupport.intro (hΦ.image continuous_fst) fun w hw ↦ ?_
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact (hu w).trans (.of_forall fun z ↦
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry Φ) (x := (w, z))
      fun h ↦ hw ⟨(w, z), h, rfl⟩)

end MeasureTheory
