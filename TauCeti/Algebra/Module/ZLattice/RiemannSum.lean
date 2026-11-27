/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Algebra.Module.ZLattice.GaugeBasis
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Riemann sums over a translated lattice

Let `L` be a full lattice in a finite-dimensional real normed space `E` and `μ` a Haar measure on
`E`. For a Lipschitz function `f` of compact support, the sum of `f` over a translate `t + L` is
a Riemann sum for `∫ f ∂μ / covolume L μ`: if some fundamental domain `F` of `L` lies in the
closed ball of radius `h` about the origin, then

```text
|∑ ℓ ∈ L, f (t + ℓ) - ∫ f ∂μ / covolume L μ| ≤ c * h * #{ℓ ∈ L | t + ℓ ∈ cthickening h (support f)},
```

where `c` is the Lipschitz constant of `f`. The point `t + ℓ` stands for the cell `t + ℓ + F`, on
which `f` varies by at most `c * h`, and only the cells meeting the support of `f` contribute, so
the error is counted by the points of `t + L` near the support of `f`. The bound is uniform in the
lattice: it sees `L` only through the radius `h`.

A fundamental domain of small radius exists as soon as `L` contains `n = dim E` linearly
independent vectors of norm at most `s`: by Cassels' lemma `ZLattice.exists_basis_gauge_le`,
`L` then has a `ℤ`-basis of vectors of norm at most `n * s`, whose parallelepiped lies in the
closed ball of radius `n ^ 2 * s`.

## Main results

* `ZLattice.abs_tsum_sub_integral_div_covolume_le`: the Riemann-sum estimate above.
* `ZLattice.finite_setOf_add_mem`: a translate of a discrete lattice meets a bounded set in
  finitely many points, so the sum above has finitely many nonzero terms.
* `ZLattice.exists_isAddFundamentalDomain_subset_closedBall`: a fundamental domain inside the
  closed ball of radius `n ^ 2 * s`, from `n` linearly independent lattice vectors of norm at
  most `s`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter V.
* S. Lang, *Algebraic Number Theory*, Chapter VI.
-/

public section

open MeasureTheory Metric Module Set Function Bornology
open scoped NNReal

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A translate `t + L` of a discrete lattice meets a bounded set in finitely many points. -/
theorem finite_setOf_add_mem (L : Submodule ℤ E) [DiscreteTopology L] {s : Set E}
    (hs : IsBounded s) (t : E) : {ℓ : L | t + (ℓ : E) ∈ s}.Finite := by
  refine ((L.toAddSubgroup.finite_inter (hs.vadd (-t))).preimage
    Subtype.val_injective.injOn).subset fun ℓ hℓ ↦ ⟨?_, ℓ.property⟩
  exact ⟨t + ℓ, hℓ, by simp⟩

variable [MeasurableSpace E]

/-- **A fundamental domain of small radius.** If a discrete subgroup `L` of `E` contains
`n = finrank ℝ E` linearly independent vectors of norm at most `s`, then some fundamental domain
of `L`, for any measure, lies in the closed ball of radius `n ^ 2 * s` about the origin. -/
theorem exists_isAddFundamentalDomain_subset_closedBall [OpensMeasurableSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (μ : Measure E) {a : Fin (finrank ℝ E) → E}
    (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a) {s : ℝ} (hs : ∀ i, ‖a i‖ ≤ s) :
    ∃ F : Set E, IsAddFundamentalDomain L F μ ∧ F ⊆ closedBall 0 (finrank ℝ E ^ 2 * s) := by
  -- The independent vectors span `E`, so `L` is a full lattice.
  have : IsZLattice ℝ L := ⟨eq_top_iff.2 <| (ha.span_eq_top_of_card_eq_finrank' (by simp)).ge.trans
    (Submodule.span_mono (Set.range_subset_iff.2 haL))⟩
  have hg (x : E) : gauge (closedBall (0 : E) 1) x = ‖x‖ := by
    rw [gauge_closedBall zero_le_one, div_one]
  obtain ⟨b, hb⟩ := exists_basis_gauge_le L (convex_closedBall 0 1)
    (fun x hx ↦ by simpa using hx) (absorbent_nhds_zero (closedBall_mem_nhds 0 one_pos)) rfl haL ha
  -- Cassels' bound `max ‖a j‖ ((∑ i ≤ j, ‖a i‖) / 2)` is at most `n * s`.
  have hbn (j : Fin (finrank ℝ E)) : ‖(b j : E)‖ ≤ finrank ℝ E * s := by
    have hs0 : 0 ≤ s := (norm_nonneg _).trans (hs j)
    have hn : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast j.pos
    have hsum : ∑ i ∈ Finset.Iic j, ‖a i‖ ≤ finrank ℝ E * s := by
      calc ∑ i ∈ Finset.Iic j, ‖a i‖ ≤ ∑ _i ∈ Finset.Iic j, s := Finset.sum_le_sum fun i _ ↦ hs i
        _ ≤ ∑ _i : Fin (finrank ℝ E), s :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ hs0
        _ = finrank ℝ E * s := by simp
    have := hb j
    simp only [hg] at this
    refine this.trans (max_le ((hs j).trans (le_mul_of_one_le_left hs0 hn)) ?_)
    linarith [mul_nonneg (zero_le_one.trans hn) hs0]
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L), ZLattice.isAddFundamentalDomain b μ,
    fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff, ← ZSpan.fract_eq_self.2 hx]
  refine (ZSpan.norm_fract_le _ _).trans ?_
  calc ∑ j, ‖b.ofZLatticeBasis ℝ L j‖ ≤ ∑ _j : Fin (finrank ℝ E), finrank ℝ E * s :=
        Finset.sum_le_sum fun j _ ↦ by simpa using hbn j
    _ = finrank ℝ E ^ 2 * s := by simp; ring

variable [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Comparing a value of `f` with its average over a translated fundamental domain: if `F` lies in
the closed ball of radius `h` and has measure `V`, then `f y` and `∫ x in F, f (y + x) ∂μ / V`
differ by at most `c * h`. -/
private theorem abs_sub_setIntegral_div_le {F : Set E} (hF : μ F < ⊤) (hF0 : 0 < μ.real F)
    {h : ℝ} (hFh : F ⊆ closedBall 0 h) {c : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith c f)
    (hfs : HasCompactSupport f) (y : E) :
    |f y - (∫ x in F, f (y + x) ∂μ) / μ.real F| ≤ c * h := by
  have hint : Integrable (fun x ↦ f (y + x)) μ :=
    (hf.continuous.comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
      (hfs.comp_homeomorph (Homeomorph.addLeft y))
  have heq : f y - (∫ x in F, f (y + x) ∂μ) / μ.real F =
      (∫ x in F, (f y - f (y + x)) ∂μ) / μ.real F := by
    rw [integral_sub (integrableOn_const hF.ne) hint.integrableOn, setIntegral_const, smul_eq_mul,
      sub_div, mul_div_cancel_left₀ _ hF0.ne']
  rw [heq, abs_div, abs_of_pos hF0, div_le_iff₀ hF0, ← Real.norm_eq_abs]
  refine norm_setIntegral_le_of_norm_le_const hF fun x hx ↦ ?_
  have hx' : ‖x‖ ≤ h := mem_closedBall_zero_iff.1 (hFh hx)
  calc ‖f y - f (y + x)‖ = dist (f y) (f (y + x)) := (dist_eq_norm _ _).symm
    _ ≤ c * dist y (y + x) := hf.dist_le_mul _ _
    _ ≤ c * h := by
        gcongr
        rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

/-- **Riemann sums over a translated lattice.** Let `L` be a full lattice in `E` with a
fundamental domain in the closed ball of radius `h`, and `f` a `c`-Lipschitz function of compact
support. Then the sum of `f` over the translate `t + L` differs from `∫ f ∂μ / covolume L μ` by at
most `c * h` times the number of points of `t + L` in the closed `h`-thickening of the support of
`f`. -/
theorem abs_tsum_sub_integral_div_covolume_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {F : Set E} (hF : IsAddFundamentalDomain L F μ) {h : ℝ}
    (hFh : F ⊆ closedBall 0 h) {c : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith c f)
    (hfs : HasCompactSupport f) (t : E) :
    |∑' ℓ : L, f (t + ℓ) - (∫ x, f x ∂μ) / covolume L μ| ≤
      c * h * {ℓ : L | t + (ℓ : E) ∈ cthickening h (support f)}.ncard := by
  set C := cthickening h (support f)
  set S := {ℓ : L | t + (ℓ : E) ∈ C}
  have hC : IsBounded C := (hfs.isCompact.isBounded.subset (subset_tsupport f)).cthickening
  -- Only finitely many points of `t + L` lie near the support of `f`.
  have hS : S.Finite := finite_setOf_add_mem L hC t
  have : MeasurableConstVAdd L E := (inferInstance : MeasurableConstVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  have hFV : covolume L μ = μ.real F := covolume_eq_measure_fundamentalDomain L μ hF
  have hFfin : μ F < ⊤ := (isBounded_closedBall.subset hFh).measure_lt_top
  have hF0 : 0 < μ.real F := hFV ▸ covolume_pos L μ
  -- A cell `t + ℓ + F` that meets the support of `f` has `t + ℓ` in the thickening.
  have hcell (ℓ : L) (hℓ : ℓ ∉ hS.toFinset) (x : E) (hx : x ∈ F) : f (t + (ℓ + x)) = 0 := by
    by_contra hne
    refine hℓ (hS.mem_toFinset.2 (mem_cthickening_of_dist_le _ _ _ _ hne ?_))
    rw [← add_assoc, dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.1 (hFh hx)
  have hsum : ∑' ℓ : L, f (t + ℓ) = ∑ ℓ ∈ hS.toFinset, f (t + ℓ) :=
    tsum_eq_sum fun ℓ hℓ ↦ by
      by_contra hne
      exact hℓ (hS.mem_toFinset.2 (self_subset_cthickening _ hne))
  -- Unfold the integral over the translates `t + ℓ + F` of the fundamental domain.
  have hint : Integrable (fun x ↦ f (t + x)) μ :=
    (hf.continuous.comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
      (hfs.comp_homeomorph (Homeomorph.addLeft t))
  have hI : ∫ x, f x ∂μ = ∑ ℓ ∈ hS.toFinset, ∫ x in F, f (t + (ℓ + x)) ∂μ := by
    rw [← integral_add_left_eq_self f t, hF.integral_eq_tsum'' _ hint]
    exact tsum_eq_sum fun ℓ hℓ ↦ setIntegral_eq_zero_of_forall_eq_zero (hcell ℓ hℓ)
  rw [hsum, hI, hFV, Finset.sum_div, ← Finset.sum_sub_distrib,
    Set.ncard_eq_toFinset_card S hS, mul_comm (c * h : ℝ)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun ℓ _ ↦ ?_
  simpa only [add_assoc] using abs_sub_setIntegral_div_le μ hFfin hF0 hFh hf hfs (t + ℓ)

end ZLattice
