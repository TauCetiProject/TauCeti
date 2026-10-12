/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete

/-!
# `A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)` is not uniform

Let `A` be a nonzero Hausdorff Tate ring and `A⟨X₁, …, Xₖ⟩` the ring of restricted power series
over it. For each variable `Xᵢ` the quotient `A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)`, with the quotient topology,
is not uniform.

The class of `Xᵢ` is nilpotent, while in a uniform Tate ring every nilpotent lies in the closure
of zero (`TauCeti.Huber.IsUniform.nilradical_le_closure_bot`): every rescaling `ϖ⁻ⁿ Xᵢ` is
nilpotent, hence power-bounded. But the coefficient of the monomial `Xᵢ` is continuous and
vanishes on `(Xᵢ²)`, so `Xᵢ` is not in the closure of `(Xᵢ²)`.

## Main results

* `TauCeti.Huber.not_isUniform_quotient_span_weightedX_sq`: `A⟨X⟩ ⧸ (Xᵢ²)` is not uniform for
  every nonzero Hausdorff Tate ring `A`.

## References

* D. Hansen, K. S. Kedlaya, *Sheafiness criteria for Huber rings*, Definition 2.3.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [T0Space A] {k : ℕ}

/-- Every element of `closure (Xᵢ²)` in `A⟨X₁, …, Xₖ⟩` has zero coefficient at the monomial
`Xᵢ`: every multiple of `Xᵢ²` does, and that coefficient is continuous with closed zero set. -/
private theorem coeff_single_eq_zero_of_mem_closure_span_weightedX_sq (i : Fin k)
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hf : f ∈ closure (Ideal.span
      {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2} : Set _)) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f : MvPowerSeries (Fin k) A) = 0 := by
  refine closure_minimal (fun g hg ↦ ?_) (isClosed_singleton.preimage
    (continuous_coeff_one_weight (Finsupp.single i 1))) hf
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hg
  simp [coe_weightedX, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]

/-- **`A⟨X₁, …, Xₖ⟩ ⧸ (Xᵢ²)` is not uniform** over a nonzero Hausdorff Tate ring `A`. The class
of `Xᵢ` is nilpotent, so in a uniform Tate ring it would lie in the closure of zero; but every
element of the closure of `(Xᵢ²)` has zero coefficient at `Xᵢ`. -/
theorem not_isUniform_quotient_span_weightedX_sq [Nontrivial A] (i : Fin k) :
    ¬ IsUniform (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ⧸
        Ideal.span
          {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}) := by
  intro h
  set J := Ideal.span {weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i ^ 2}
  have hX : Ideal.Quotient.mk J (weightedX _ isWeightFamily_one_weight i) ∈
      (⊥ : Ideal _).closure := h.nilradical_le_closure_bot (mem_nilradical.mpr ⟨2, by
    rw [← map_pow (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩)
  rw [← SetLike.mem_coe, Ideal.coe_closure, Submodule.bot_coe, ← Set.mem_preimage,
    (QuotientRing.isOpenQuotientMap_mk J).isOpenMap.preimage_closure_eq_closure_preimage
      continuous_quot_mk] at hX
  have := coeff_single_eq_zero_of_mem_closure_span_weightedX_sq i
    (closure_mono (fun _ ↦ Ideal.Quotient.eq_zero_iff_mem.mp) hX)
  simp [coe_weightedX, MvPowerSeries.coeff_X] at this

end TauCeti.Huber
