/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.Sets.Opens

/-!
# Gluing first-order Sobolev functions along finite open covers

Let `V i` be a finite family of open sets lying in an open set `Ω` and covering it. Sobolev
functions `w i ∈ W^{1,p}(V i)` whose values agree almost everywhere with one function `u` come
from a single `v ∈ W^{1,p}(Ω)` with value `u`, which restricts to `w i` on each `V i` and
satisfies `‖v‖ ≤ ∑ᵢ ‖w i‖` (`TauCeti.W1p.exists_glue`). No boundary regularity of the sets is
used.

The weak gradients are glued with `TauCeti.exists_hasWeakFDerivOn_iSup`. The norm of `W^{1,p}`
is the `Lᵖ` norm of the pointwise Euclidean norm of the value-gradient jet, so the norm bound is
a single estimate for gluing `Lᵖ` classes along a finite cover
(`MeasureTheory.Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion`), applied to the jets.

## Main results

* `TauCeti.W1p.exists_glue`: gluing along a finite open cover with prescribed value.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1 (localization of Sobolev
  functions with a finite cover).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*}

/-- **Gluing first-order Sobolev functions along a finite open cover.** Let the open sets `V i`,
finitely many, cover `Ω` and lie in `Ω`. If `w i ∈ W^{1,p}(V i)` has value `u` almost everywhere
on `V i` for every `i`, then some `v ∈ W^{1,p}(Ω)` has value `u` almost everywhere on `Ω`,
restricts to `w i` on each `V i`, and satisfies `‖v‖ ≤ ∑ᵢ ‖w i‖`. -/
theorem W1p.exists_glue [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (w : ∀ i, W1p mu (V i) p) {u : E → ℝ}
    (hw : ∀ i, W1p.value (w i) =ᵐ[mu.restrict (V i : Set E)] u) :
    ∃ v : W1p mu Omega p, W1p.value v =ᵐ[mu.restrict (Omega : Set E)] u ∧
      (∀ i, W1p.restrictL (hle i) v = w i) ∧ ‖v‖ ≤ ∑ i, ‖w i‖ := by
  have hloc : ∀ i, HasWeakFDerivOn mu (V i) u (fun x => innerSL ℝ (W1p.gradient (w i) x)) :=
    fun i => (W1p.hasWeakFDerivOn (w i)).congr_ae (hw i)
  obtain ⟨U, hU, hUi⟩ := exists_hasWeakFDerivOn_iSup V _ hloc
  let G : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (U x)
  have hGU : ∀ x, innerSL ℝ (G x) = U x := fun x => by
    ext y
    simp only [G, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
  have hG : ∀ i, W1p.gradient (w i) =ᵐ[mu.restrict (V i : Set E)] G := fun i => by
    filter_upwards [hUi i] with x hx
    apply (innerSL_inj (𝕜 := ℝ)).1
    rw [hGU, hx]
  have hsub := Opens.le_iSup_iff_subset_iUnion.1 hcov
  obtain ⟨u', hu', -⟩ :=
    Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion hsub (fun i => W1p.value (w i)) hw
  obtain ⟨G', hG', -⟩ :=
    Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion hsub (fun i => W1p.gradient (w i)) hG
  have hmk : HasWeakFDerivOn mu Omega u' (fun x => innerSL ℝ (G' x)) := by
    refine ((hU.mono hcov).congr_ae hu'.symm).congr_ae_deriv ?_
    filter_upwards [hG'] with x hx
    rw [hx, hGU]
  have hv : W1p.value (W1p.mk u' G' hmk) =ᵐ[mu.restrict (Omega : Set E)] u :=
    (W1p.value_mk u' G' hmk).symm ▸ hu'
  refine ⟨W1p.mk u' G' hmk, hv, fun i => W1p.restrictL_eq_of_value_ae_eq (hle i)
    (Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 (hle i)) hv) (hw i).symm), ?_⟩
  let J : E → WithLp 2 (ℝ × E) := fun x => WithLp.toLp 2 (u x, G x)
  obtain ⟨K, hK, hKn⟩ := Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion (g := J) hsub
    (fun i => (w i : Sobolev1JetLp mu (V i) p)) fun i => by
      filter_upwards [W1p.coe_ae_eq_toLp_value_gradient (w i), hw i, hG i] with x h₀ h₁ h₂
      rw [h₀, h₁, h₂]
  have hvK : (W1p.mk u' G' hmk : Sobolev1JetLp mu Omega p) = K := by
    apply Lp.ext
    filter_upwards [W1p.coe_ae_eq_toLp_value_gradient (W1p.mk u' G' hmk), hu', hG', hK]
      with x h₀ h₁ h₂ h₃
    rw [h₀, h₃, W1p.value_mk, W1p.gradient_mk, h₁, h₂]
  rw [← Submodule.norm_coe, hvK]
  simpa only [Submodule.norm_coe] using hKn

end TauCeti
