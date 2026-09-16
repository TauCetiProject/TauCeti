/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
# The flow law for maximal integral curves

The maximal integral curve of an autonomous vector field can be restarted at any time in its
interval of existence. Its new maximal interval is the translate of the original interval, and
the restarted curve is the corresponding translate of the original curve. These are the domain
and value laws that turn the family `maximalIntegralCurve v` into a partial flow.

The domain statement is essential: `maximalIntegralCurve` is total only by assigning its initial
point as a junk value outside the interval of existence, so an unconditional flow equation would
be false. The results below always carry the precise membership hypotheses.

## Main results

* `mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff`: the maximal interval after
  restarting at `t` is exactly the translate by `-t` of the original interval.
* `maximalIntegralCurve_add`: the domain-aware flow law
  `φ x (t + s) = φ (φ x t) s`.

## References

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012],
  Chapter 9, especially Theorem 9.12.
-/

public section

open Function Manifold Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {s t : ℝ} {x : M}

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- Any two times in the maximal interval lie in a common open subinterval on which the maximal
curve is an integral curve. -/
private theorem exists_common_Ioo_maximalIntegralCurveInterval
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x)
    (hs : s ∈ maximalIntegralCurveInterval v x) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Ioo a b ∧ t ∈ Ioo a b ∧ s ∈ Ioo a b ∧
      IsMIntegralCurveOn (maximalIntegralCurve v x) v (Ioo a b) := by
  obtain ⟨γ, a₁, b₁, hγ, hγx, hγ0, ht, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  obtain ⟨δ, a₂, b₂, hδ, hδx, hδ0, hs, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq hs
  refine ⟨min a₁ a₂, max b₁ b₂,
    ⟨(min_le_left _ _).trans_lt hγ0.1, hγ0.2.trans_le (le_max_left _ _)⟩,
    ⟨lt_of_le_of_lt (min_le_left _ _) ht.1, ht.2.trans_le (le_max_left _ _)⟩,
    ⟨lt_of_le_of_lt (min_le_right _ _) hs.1, hs.2.trans_le (le_max_right _ _)⟩, ?_⟩
  refine (isMIntegralCurveOn_maximalIntegralCurve hv).mono fun r hr ↦ ?_
  rcases lt_or_ge r 0 with hr0 | hr0
  · rcases min_choice a₁ a₂ with hmin | hmin
    · exact hγ.subset_maximalIntegralCurveInterval hγ0 hγx
        ⟨hmin ▸ hr.1, hr0.trans hγ0.2⟩
    · exact hδ.subset_maximalIntegralCurveInterval hδ0 hδx
        ⟨hmin ▸ hr.1, hr0.trans hδ0.2⟩
  · rcases max_choice b₁ b₂ with hmax | hmax
    · exact hγ.subset_maximalIntegralCurveInterval hγ0 hγx
        ⟨hγ0.1.trans_le hr0, hmax ▸ hr.2⟩
    · exact hδ.subset_maximalIntegralCurveInterval hδ0 hδx
        ⟨hδ0.1.trans_le hr0, hmax ▸ hr.2⟩

/-- If `s` and `t` belong to the maximal interval through `x`, then `s - t` belongs to the
maximal interval through the point reached at time `t`. This is the domain half of restarting an
autonomous integral curve at time `t`. -/
private theorem sub_mem_maximalIntegralCurveInterval
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x)
    (hs : s ∈ maximalIntegralCurveInterval v x) :
    s - t ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x t) := by
  obtain ⟨a, b, h0, ht', hs', hγ⟩ :=
    exists_common_Ioo_maximalIntegralCurveInterval hv ht hs
  have hshift : IsMIntegralCurveOn (maximalIntegralCurve v x ∘ (· + t)) v
      (Ioo (a - t) (b - t)) :=
    (hγ.comp_add t).mono fun r hr ↦ by
      simp only [mem_ofPred_eq]
      constructor <;> linarith [hr.1, hr.2]
  exact hshift.subset_maximalIntegralCurveInterval
    ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ (by simp)
    ⟨by linarith [hs'.1], by linarith [hs'.2]⟩

/-- **The flow law for the maximal integral curve.** If both `t` and `t + s` lie in the maximal
interval through `x`, restarting the curve at time `t` and running it for time `s` gives its value
at time `t + s`. -/
theorem maximalIntegralCurve_add
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x)
    (hts : t + s ∈ maximalIntegralCurveInterval v x) :
    maximalIntegralCurve v x (t + s) =
      maximalIntegralCurve v (maximalIntegralCurve v x t) s := by
  obtain ⟨a, b, h0, ht', hst', hγ⟩ :=
    exists_common_Ioo_maximalIntegralCurveInterval hv ht hts
  have hshift : IsMIntegralCurveOn (maximalIntegralCurve v x ∘ (· + t)) v
      (Ioo (a - t) (b - t)) :=
    (hγ.comp_add t).mono fun r hr ↦ by
      simp only [mem_ofPred_eq]
      constructor <;> linarith [hr.1, hr.2]
  have h0shift : (0 : ℝ) ∈ Ioo (a - t) (b - t) :=
    ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hsshift : s ∈ Ioo (a - t) (b - t) :=
    ⟨by linarith [hst'.1], by linarith [hst'.2]⟩
  symm
  simpa only [comp_apply, add_comm] using
    hshift.eqOn_maximalIntegralCurve hv h0shift (by simp) hsshift

/-- Restarting a maximal integral curve at time `t` translates its maximal interval by `-t`.
This characterizes the domain of the partial flow without reference to the chosen integral-curve
witnesses. -/
theorem mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x) :
    s ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x t) ↔
      t + s ∈ maximalIntegralCurveInterval v x := by
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x := by
    obtain ⟨γ, a, b, hγ, hγx, hγ0, -, -⟩ :=
      exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
    exact hγ.subset_maximalIntegralCurveInterval hγ0 hγx hγ0
  have hneg : -t ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x t) := by
    simpa only [zero_sub] using sub_mem_maximalIntegralCurveInterval hv ht h0
  have hback : maximalIntegralCurve v (maximalIntegralCurve v x t) (-t) = x := by
    rw [← maximalIntegralCurve_add hv ht]
    · simpa only [add_neg_cancel] using maximalIntegralCurve_zero h0
    · simpa using h0
  constructor
  · intro hs
    have := sub_mem_maximalIntegralCurveInterval hv hneg hs
    rw [hback] at this
    simpa only [sub_neg_eq_add, add_comm] using this
  · intro hst
    simpa only [add_sub_cancel_left] using
      sub_mem_maximalIntegralCurveInterval hv ht hst

/-- Set form of `mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff`: the maximal interval
after restarting at `t` is the preimage of the original interval under translation by `t`. -/
theorem maximalIntegralCurveInterval_maximalIntegralCurve_eq_preimage
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x) :
    maximalIntegralCurveInterval v (maximalIntegralCurve v x t) =
      (fun s : ℝ ↦ t + s) ⁻¹' maximalIntegralCurveInterval v x := by
  ext s
  exact mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv ht
