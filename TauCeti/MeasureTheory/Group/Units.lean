/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.Algebra.GroupWithZero.Units.Basic
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measures pulled back to the units of a group with zero

Let `K` be a group with zero with measurable singletons and `μ` a measure on `K` that does not
charge `0`. Pulling `μ` back along the measurable embedding `Units.val : Kˣ → K`
(`Units.measurableEmbedding_val₀`) loses nothing, since the range of `Units.val` is `{0}ᶜ`: the
pushforward of the pullback is `μ` again, so integrals and integrability of functions of `x : K`
over `Kˣ` are those over `K`. If `μ` is invariant under multiplication by every unit, its pullback
is a left-invariant measure on the group `Kˣ`.

On a nontrivially normed field, the pullback of an additive Haar measure with a density
that is continuous and positive away from `0` is finite on compact sets and positive on nonempty
open sets of `Kˣ`, the topological conditions of a Haar measure.

## Main results

* `Units.map_val_comap_val`: `(μ.comap Units.val).map Units.val = μ`.
* `Units.integral_comap_val`, `Units.integrable_comap_val_iff`: integrals and integrability over
  `Kˣ` against `μ.comap Units.val` are those over `K` against `μ`.
* `Units.isMulLeftInvariant_comap_val`: the pullback of a measure invariant under multiplication
  by units is left-invariant.
* `Units.isFiniteMeasureOnCompacts_comap_val_withDensity`,
  `Units.isOpenPosMeasure_comap_val_withDensity`: pulled-back densities continuous and positive
  away from `0`.
-/

public section

open MeasureTheory Measure Set Topology

namespace Units

section GroupWithZero

variable {K : Type*} [GroupWithZero K] [MeasurableSpace K] [MeasurableSingletonClass K]
  {μ : Measure K} {E : Type*} [NormedAddCommGroup E]

/-- Pushing forward to `K` the pullback to `Kˣ` of a measure that does not charge `0` recovers the
measure. -/
theorem map_val_comap_val [NullSingletonClass μ] : (μ.comap Units.val).map Units.val = μ := by
  rw [measurableEmbedding_val₀.map_comap, range_val_eq_compl_zero, restrict_compl_singleton]

/-- Integrating a function of `x : K` over `Kˣ` against the pullback of a measure that does not
charge `0` is integrating it over `K`. -/
theorem integral_comap_val [NormedSpace ℝ E] [NullSingletonClass μ] (g : K → E) :
    ∫ x : Kˣ, g x ∂μ.comap Units.val = ∫ y, g y ∂μ := by
  rw [← measurableEmbedding_val₀.integral_map, map_val_comap_val]

/-- A function of `x : K` is integrable over `Kˣ` against the pullback of a measure that does not
charge `0` exactly when it is integrable over `K`. -/
theorem integrable_comap_val_iff [NullSingletonClass μ] {g : K → E} :
    Integrable (fun x : Kˣ ↦ g x) (μ.comap Units.val) ↔ Integrable g μ := by
  have h := measurableEmbedding_val₀.integrable_map_iff (μ := μ.comap Units.val) (g := g)
  rw [map_val_comap_val, Function.comp_def] at h
  exact h.symm

/-- The pullback to `Kˣ` of a measure invariant under multiplication by units is left invariant. -/
theorem isMulLeftInvariant_comap_val [MeasurableMul K] (h : ∀ b : Kˣ, μ.map ((b : K) * ·) = μ) :
    (μ.comap Units.val).IsMulLeftInvariant where
  map_mul_left_eq_self b := by
    have he := measurableEmbedding_val₀ (G₀ := K)
    have hb : Measurable (b * · : Kˣ → Kˣ) := he.measurable_comp_iff.1 <| by
      simpa [Function.comp_def] using (measurable_const_mul (b : K)).comp he.measurable
    ext S hS
    rw [map_apply hb hS, he.comap_apply, he.comap_apply]
    have himage : Units.val '' ((b * ·) ⁻¹' S) = ((b : K) * ·) ⁻¹' (Units.val '' S) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨b * u, hu, rfl⟩
      · rintro ⟨v, hv, hvy⟩
        refine ⟨b⁻¹ * v, by simpa using hv, ?_⟩
        rw [val_mul, hvy, ← mul_assoc, ← val_mul, inv_mul_cancel, val_one, one_mul]
    rw [himage, ← map_apply (measurable_const_mul _) (he.measurableSet_image.2 hS), h b]

end GroupWithZero

section NormedField

variable {K : Type*} [NontriviallyNormedField K] [MeasurableSpace K]
  [BorelSpace K] (ν : Measure K) {ρ : K → ℝ}

/-- The pullback to `Kˣ` of a measure finite on compact sets, with a density that is continuous
away from `0`, is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_comap_val_withDensity [IsFiniteMeasureOnCompacts ν]
    (hρ : ContinuousOn ρ {0}ᶜ) :
    IsFiniteMeasureOnCompacts ((ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)).comap Units.val) := by
  have he := measurableEmbedding_val₀ (G₀ := K)
  refine ⟨fun C hC ↦ ?_⟩
  rw [he.comap_apply, withDensity_apply _ (he.measurableSet_image.2 hC.isClosed.measurableSet)]
  have hC' := hC.image continuous_val
  obtain ⟨M, hM⟩ := hC'.bddAbove_image
    (hρ.mono fun _ ⟨u, _, hu⟩ ↦ hu ▸ u.ne_zero)
  calc ∫⁻ x in Units.val '' C, ENNReal.ofReal (ρ x) ∂ν
      ≤ ∫⁻ _ in Units.val '' C, ENNReal.ofReal M ∂ν :=
        setLIntegral_mono measurable_const fun x hx ↦
          ENNReal.ofReal_le_ofReal (hM (mem_image_of_mem ρ hx))
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC'.measure_lt_top

/-- The pullback to `Kˣ` of a measure positive on nonempty open sets, with a measurable density
that is positive away from `0`, is positive on nonempty open sets. -/
theorem isOpenPosMeasure_comap_val_withDensity [ν.IsOpenPosMeasure] (hρm : Measurable ρ)
    (hρpos : ∀ x ≠ 0, 0 < ρ x) :
    ((ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)).comap Units.val).IsOpenPosMeasure := by
  have he := measurableEmbedding_val₀ (G₀ := K)
  refine ⟨fun U hU hne ↦ ?_⟩
  rw [he.comap_apply, Ne, withDensity_apply_eq_zero' (f := fun x ↦ ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρm).aemeasurable]
  have hset : {x | ENNReal.ofReal (ρ x) ≠ 0} ∩ Units.val '' U = Units.val '' U := by
    refine inter_eq_right.2 ?_
    rintro _ ⟨u, -, rfl⟩
    simpa using hρpos u u.ne_zero
  rw [hset]
  exact (isOpenEmbedding_val.isOpenMap U hU).measure_ne_zero ν (hne.image _)

end NormedField

end Units
