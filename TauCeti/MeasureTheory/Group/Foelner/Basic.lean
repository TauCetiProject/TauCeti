/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FoelnerFilter
import TauCeti.MeasureTheory.Group.Action

/-!
# Filter compatibility and generating-set reductions for Følner families

Let a group `G` act on a measurable space `X` with a measure `μ`. Mathlib defines Følner families
`IsFoelner G μ l F` along a filter `l` and the maximal Følner filter `maxFoelner G μ`. This file
develops two basic tools for manipulating `IsFoelner` and `maxFoelner` (together with their
additive counterparts `IsAddFoelner` and `maxAddFoelner`):

1. **Filter and perturbation compatibility**: eventual equality (`IsFoelner.congr`), invariance of
   `IsFoelner` (for a `G`-invariant measure `μ` and an eventually measurable family `F'`) under
   asymptotically negligible relative symmetric-difference perturbations
   `μ (F i ∆ F' i) / μ (F i) → 0` and eventual `μ`-almost-everywhere equality, and invariance of
   ultrafilter density means `IsFoelner.mean` under such perturbations (without requiring
   invariance of `μ` or `IsFoelner` for `F'`).
2. **Generating-set reduction (Garrido Lemma 3.4, BDHV Remark G.5.3)**: for a `G`-invariant measure
   `μ`, the elements `g : G` with `μ ((g • F i) ∆ F i) / μ (F i) → 0` form a subgroup
   `TauCeti.vanishingSubgroup μ l F`. Consequently `IsFoelner`, `maxFoelner G μ`, and
   `(maxFoelner G μ).NeBot` can be tested purely on a generating set `S` with
   `Subgroup.closure S = ⊤`; for an arbitrary measure `μ` (without invariance),
   `(maxFoelner G μ).NeBot` is characterized by passing all finite tests over `G`.

## Main definitions

* `TauCeti.vanishingSubgroup`: the subgroup of group elements whose relative translation
  boundaries along `F` tend to zero.

## Main results

* `IsFoelner.congr`, `TauCeti.isFoelner_congr`: eventual-equality invariance of `IsFoelner`.
* `IsFoelner.of_tendsto_meas_symmDiff_div`, `IsFoelner.of_eventually_ae_eq`: stability of
  `IsFoelner` for a `G`-invariant measure under asymptotically small relative symmetric differences
  and eventual `μ`-a.e. equality.
* `IsFoelner.mean_eq_of_tendsto_meas_symmDiff_div`, `IsFoelner.mean_eq_of_eventually_ae_eq`:
  asymptotically equivalent families induce the same ultrafilter density mean.
* `IsFoelner.of_closure_eq_top`, `TauCeti.isFoelner_iff_of_closure_eq_top`: generating-set
  criterion for `IsFoelner`.
* `TauCeti.maxFoelner_eq_of_closure_eq_top`: `maxFoelner G μ` is determined by a generating set of
  `G`.
* `TauCeti.exists_isFoelner_atTop_of_closure_eq_top`: finite tests on subsets of a generating set
  `S` yield a Følner family indexed by `Finset S × ℕ` along `atTop`.
* `TauCeti.maxFoelner_neBot_iff_of_closure_eq_top`, `TauCeti.maxFoelner_neBot_iff`: finite-test
  characterizations of `(maxFoelner G μ).NeBot`.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Lemma 3.4.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5, Remark G.5.3.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Pointwise symmDiff Topology

section Foelner

variable {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  {l : Filter ι} {u : Ultrafilter ι} {F F' : ι → Set X}

namespace IsFoelner

/-! ### Eventual equality -/

/-- A family eventually equal to a Følner family along `l` is itself Følner. -/
@[to_additive
/-- A family eventually equal to an additive Følner family along `l` is itself Følner. -/]
theorem congr (hF : IsFoelner G μ l F) (h : F =ᶠ[l] F') : IsFoelner G μ l F' :=
  (isFoelner_iff_tendsto _ _).2 <| ((isFoelner_iff_tendsto _ _).1 hF).congr' h

end IsFoelner

/-- Eventual equality preserves `IsFoelner`. -/
@[to_additive isAddFoelner_congr /-- Eventual equality preserves `IsAddFoelner`. -/]
theorem TauCeti.isFoelner_congr (h : F =ᶠ[l] F') : IsFoelner G μ l F ↔ IsFoelner G μ l F' :=
  ⟨fun hF ↦ hF.congr h, fun hF' ↦ hF'.congr h.symm⟩

namespace IsFoelner

/-! ### Asymptotic symmetric-difference perturbations -/

/-- If `μ (F i ∆ F' i) / μ (F i) → 0` along a Følner family `F`, then `μ (F' i) / μ (F i) → 1`. -/
@[to_additive tendsto_meas_div_of_tendsto_meas_symmDiff_div
/-- If `μ (F i ∆ F' i) / μ (F i) → 0` along an additive Følner family `F`, then
`μ (F' i) / μ (F i) → 1`. -/]
theorem tendsto_meas_div_of_tendsto_meas_symmDiff_div (hF : IsFoelner G μ l F)
    (hdiff : Tendsto (fun i ↦ μ (F i ∆ F' i) / μ (F i)) l (𝓝 0)) :
    Tendsto (fun i ↦ μ (F' i) / μ (F i)) l (𝓝 1) := by
  have hlow : Tendsto (fun i ↦ 1 - μ (F i ∆ F' i) / μ (F i)) l (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hdiff (Or.inl ENNReal.one_ne_top)
  have hhigh : Tendsto (fun i ↦ 1 + μ (F i ∆ F' i) / μ (F i)) l (𝓝 1) := by
    simpa using tendsto_const_nhds.add hdiff
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi0 hitop
    rw [tsub_le_iff_right, ← ENNReal.div_self hi0 hitop, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (tsub_le_iff_left.1 le_measure_symmDiff) _
  · filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi0 hitop
    rw [← ENNReal.div_self hi0 hitop, ← ENNReal.add_div]
    refine ENNReal.div_le_div_right ?_ _
    simpa [symmDiff_comm] using tsub_le_iff_left.1 (le_measure_symmDiff (s₁ := F' i) (s₂ := F i))

/-- If `μ (F i ∆ F' i) / μ (F i) → 0` along a Følner family `F`, then `μ (F i) / μ (F' i) → 1`. -/
@[to_additive tendsto_div_meas_of_tendsto_meas_symmDiff_div
/-- If `μ (F i ∆ F' i) / μ (F i) → 0` along an additive Følner family `F`, then
`μ (F i) / μ (F' i) → 1`. -/]
theorem tendsto_div_meas_of_tendsto_meas_symmDiff_div (hF : IsFoelner G μ l F)
    (hdiff : Tendsto (fun i ↦ μ (F i ∆ F' i) / μ (F i)) l (𝓝 0)) :
    Tendsto (fun i ↦ μ (F i) / μ (F' i)) l (𝓝 1) := by
  have hinv : Tendsto (fun i ↦ (μ (F' i) / μ (F i))⁻¹) l (𝓝 1) := by
    simpa using tendsto_inv_iff.2 (hF.tendsto_meas_div_of_tendsto_meas_symmDiff_div hdiff)
  refine hinv.congr' ?_
  filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi0 hitop
  exact ENNReal.inv_div (Or.inl hitop) (Or.inl hi0)

/-- For a `G`-invariant measure `μ`, perturbing a Følner family `F` to an eventually measurable
family `F'` with `μ (F i ∆ F' i) / μ (F i) → 0` preserves `IsFoelner`. -/
@[to_additive of_tendsto_meas_symmDiff_div
/-- For a `G`-invariant measure `μ`, perturbing an additive Følner family `F` to an eventually
measurable family `F'` with `μ (F i ∆ F' i) / μ (F i) → 0` preserves `IsAddFoelner`. -/]
theorem of_tendsto_meas_symmDiff_div [SMulInvariantMeasure G X μ] (hF : IsFoelner G μ l F)
    (hmeas : ∀ᶠ i in l, MeasurableSet (F' i))
    (hdiff : Tendsto (fun i ↦ μ (F i ∆ F' i) / μ (F i)) l (𝓝 0)) :
    IsFoelner G μ l F' := by
  have hquot := hF.tendsto_meas_div_of_tendsto_meas_symmDiff_div hdiff
  have hpos := hquot.eventually (lt_mem_nhds zero_lt_one)
  have hlt := hquot.eventually (gt_mem_nhds ENNReal.one_lt_top)
  refine ⟨hmeas, ?_, ?_, fun g ↦ ?_⟩
  · filter_upwards [hpos] with i hi h0
    simp [h0] at hi
  · filter_upwards [hF.eventually_meas_ne_top, hlt] with i hitop hi htop
    rw [htop, ENNReal.top_div_of_ne_top hitop] at hi
    exact lt_irrefl _ hi
  · have hsum : Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i) +
        (μ (F i ∆ F' i) / μ (F i) + μ (F i ∆ F' i) / μ (F i))) l (𝓝 0) := by
      simpa using (hF.tendsto_meas_smul_symmDiff g).add (hdiff.add hdiff)
    have hnum : Tendsto (fun i ↦ μ ((g • F' i) ∆ F' i) / μ (F i)) l (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (.of_forall fun _ ↦ zero_le) <| .of_forall fun i ↦ by
          rw [← ENNReal.add_div, ← ENNReal.add_div]
          refine ENNReal.div_le_div_right ?_ _
          calc
            μ ((g • F' i) ∆ F' i)
              ≤ μ ((g • F' i) ∆ (g • F i)) + μ ((g • F i) ∆ F' i) := measure_symmDiff_le _ _ _
            _ ≤ μ (F' i ∆ F i) + (μ ((g • F i) ∆ F i) + μ (F i ∆ F' i)) := by
              rw [measure_smul_symmDiff_smul]
              exact add_le_add_right (measure_symmDiff_le _ _ _) _
            _ = μ ((g • F i) ∆ F i) + (μ (F i ∆ F' i) + μ (F i ∆ F' i)) := by
              rw [symmDiff_comm (F' i), add_left_comm]
    have hprod := ENNReal.Tendsto.mul hnum (Or.inr ENNReal.one_ne_top)
      (hF.tendsto_div_meas_of_tendsto_meas_symmDiff_div hdiff) (Or.inl one_ne_zero)
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi0 hitop
    exact ENNReal.div_mul_div_cancel hi0 hitop

/-- For a `G`-invariant measure `μ`, replacing a Følner family `F` by an eventually measurable
family `F'` that is eventually `μ`-almost-everywhere equal to `F` preserves `IsFoelner`. -/
@[to_additive
/-- For a `G`-invariant measure `μ`, replacing an additive Følner family `F` by an eventually
measurable family `F'` that is eventually `μ`-almost-everywhere equal to `F` preserves
`IsAddFoelner`. -/]
theorem of_eventually_ae_eq [SMulInvariantMeasure G X μ] (hF : IsFoelner G μ l F)
    (hmeas : ∀ᶠ i in l, MeasurableSet (F' i)) (hae : ∀ᶠ i in l, F i =ᵐ[μ] F' i) :
    IsFoelner G μ l F' := by
  refine hF.of_tendsto_meas_symmDiff_div hmeas (tendsto_const_nhds.congr' ?_)
  filter_upwards [hae] with i hi
  simp [measure_symmDiff_eq_zero_iff.2 hi]

/-- If `F` is a Følner family along an ultrafilter `u` and `μ (F i ∆ F' i) / μ (F i) → 0`, then
`F` and `F'` have the same density-limit mean on all subsets of `X` (without requiring `F'` to be
Følner or `μ` to be invariant). -/
@[to_additive mean_eq_of_tendsto_meas_symmDiff_div
/-- If `F` is an additive Følner family along an ultrafilter `u` and
`μ (F i ∆ F' i) / μ (F i) → 0`, then `F` and `F'` have the same density-limit mean on all subsets
of `X` (without requiring `F'` to be additive Følner or `μ` to be invariant). -/]
theorem mean_eq_of_tendsto_meas_symmDiff_div (hF : IsFoelner G μ u F)
    (hdiff : Tendsto (fun i ↦ μ (F i ∆ F' i) / μ (F i)) u (𝓝 0)) (s : Set X) :
    mean μ u F s = mean μ u F' s := by
  have hlow : Tendsto (fun i ↦ μ (s ∩ F i) / μ (F i) - μ (F i ∆ F' i) / μ (F i)) u
      (𝓝 (mean μ u F s)) := by
    simpa using ENNReal.Tendsto.sub (hF.tendsto_nhds_mean s) hdiff (Or.inr ENNReal.zero_ne_top)
  have hhigh : Tendsto (fun i ↦ μ (s ∩ F i) / μ (F i) + μ (F i ∆ F' i) / μ (F i)) u
      (𝓝 (mean μ u F s)) := by
    simpa using (hF.tendsto_nhds_mean s).add hdiff
  have hmid : Tendsto (fun i ↦ μ (s ∩ F' i) / μ (F i)) u (𝓝 (mean μ u F s)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
      (.of_forall fun i ↦ ?_) (.of_forall fun i ↦ ?_)
    · rw [tsub_le_iff_right, ← ENNReal.add_div]
      refine ENNReal.div_le_div_right (tsub_le_iff_left.1 ?_) _
      exact le_measure_symmDiff.trans <|
        measure_mono ((inter_symmDiff_distrib_left s _ _).symm ▸ inter_subset_right)
    · rw [← ENNReal.add_div]
      refine ENNReal.div_le_div_right (tsub_le_iff_left.1 ?_) _
      refine le_measure_symmDiff.trans ?_
      rw [symmDiff_comm]
      exact measure_mono ((inter_symmDiff_distrib_left s _ _).symm ▸ inter_subset_right)
  have hprod := ENNReal.Tendsto.mul hmid (Or.inr ENNReal.one_ne_top)
    (hF.tendsto_div_meas_of_tendsto_meas_symmDiff_div hdiff) (Or.inl one_ne_zero)
  rw [mul_one] at hprod
  have hlim : Tendsto (fun i ↦ μ (s ∩ F' i) / μ (F' i)) u (𝓝 (mean μ u F s)) := by
    refine hprod.congr' ?_
    filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi0 hitop
    exact ENNReal.div_mul_div_cancel hi0 hitop
  exact hlim.limUnder_eq.symm

/-- If `F` is a Følner family along an ultrafilter `u` and `F'` is eventually `μ`-almost-everywhere
equal to `F`, then `F` and `F'` have the same density-limit mean on all subsets of `X` (without
requiring `F'` to be Følner or `μ` to be invariant). -/
@[to_additive
/-- If `F` is an additive Følner family along an ultrafilter `u` and `F'` is eventually
`μ`-almost-everywhere equal to `F`, then `F` and `F'` have the same density-limit mean on all
subsets of `X` (without requiring `F'` to be additive Følner or `μ` to be invariant). -/]
theorem mean_eq_of_eventually_ae_eq (hF : IsFoelner G μ u F)
    (hae : ∀ᶠ i in (u : Filter ι), F i =ᵐ[μ] F' i) (s : Set X) :
    mean μ u F s = mean μ u F' s := by
  refine hF.mean_eq_of_tendsto_meas_symmDiff_div (tendsto_const_nhds.congr' ?_) s
  filter_upwards [hae] with i hi
  simp [measure_symmDiff_eq_zero_iff.2 hi]

end IsFoelner

/-! ### Generating-set reduction (Garrido Lemma 3.4) -/

namespace TauCeti

variable (μ l F) in
/-- For a `G`-invariant measure `μ`, the elements `g : G` whose relative translation boundaries
`μ ((g • F i) ∆ F i) / μ (F i)` tend to `0` along `l` form a subgroup of `G`. -/
@[to_additive
/-- For a `G`-invariant measure `μ`, the elements `g : G` whose relative translation boundaries
`μ ((g +ᵥ F i) ∆ F i) / μ (F i)` tend to `0` along `l` form an additive subgroup of `G`. -/]
def vanishingSubgroup [SMulInvariantMeasure G X μ] : Subgroup G where
  carrier := {g : G | Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)}
  one_mem' := by simp [tendsto_const_nhds]
  mul_mem' {g h} hg hh := by
    have hsum : Tendsto (fun i ↦
        μ ((g • F i) ∆ F i) / μ (F i) + μ ((h • F i) ∆ F i) / μ (F i)) l (𝓝 0) := by
      simpa using hg.add hh
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (.of_forall fun _ ↦ zero_le) (.of_forall fun i ↦ ?_)
    rw [← ENNReal.add_div]
    exact ENNReal.div_le_div_right (measure_mul_smul_symmDiff_le μ g h (F i)) _
  inv_mem' {g} hg := by
    simp_rw [Set.mem_ofPred_eq, measure_inv_smul_symmDiff_self] at hg ⊢
    exact hg

/-- An element `g : G` belongs to `TauCeti.vanishingSubgroup μ l F` if and only if its relative
translation boundary `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0` along `l`. -/
@[to_additive (attr := simp)
/-- An element `g : G` belongs to `TauCeti.vanishingAddSubgroup μ l F` if and only if its relative
translation boundary `μ ((g +ᵥ F i) ∆ F i) / μ (F i)` tends to `0` along `l`. -/]
theorem mem_vanishingSubgroup [SMulInvariantMeasure G X μ] {g : G} :
    g ∈ vanishingSubgroup μ l F ↔
      Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0) :=
  Iff.rfl

end TauCeti

namespace IsFoelner

/-- **Garrido Lemma 3.4 (measure-space form).** When `μ` is `G`-invariant and `S` generates `G`, a
family of eventually measurable sets of finite nonzero measure is Følner as soon as its relative
translation boundaries tend to zero for elements of `S`. -/
@[to_additive
/-- **Garrido Lemma 3.4 (additive measure-space form).** When `μ` is `G`-invariant and `S`
generates `G`, a family of eventually measurable sets of finite nonzero measure is additive Følner
as soon as its relative translation boundaries tend to zero for elements of `S`. -/]
theorem of_closure_eq_top [SMulInvariantMeasure G X μ] {S : Set G} (hS : Subgroup.closure S = ⊤)
    (hmeas : ∀ᶠ i in l, MeasurableSet (F i)) (hne0 : ∀ᶠ i in l, μ (F i) ≠ 0)
    (hnetop : ∀ᶠ i in l, μ (F i) ≠ ∞)
    (htendsto : ∀ g ∈ S, Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)) :
    IsFoelner G μ l F where
  eventually_measurableSet := hmeas
  eventually_meas_ne_zero := hne0
  eventually_meas_ne_top := hnetop
  tendsto_meas_smul_symmDiff g := by
    have hle : Subgroup.closure S ≤ TauCeti.vanishingSubgroup μ l F :=
      (Subgroup.closure_le (TauCeti.vanishingSubgroup μ l F)).2 htendsto
    exact hle (hS.symm ▸ Subgroup.mem_top g)

end IsFoelner

namespace TauCeti

/-- Generating-set characterization of `IsFoelner` for a `G`-invariant measure. -/
@[to_additive isAddFoelner_iff_of_closure_eq_top
/-- Generating-set characterization of `IsAddFoelner` for a `G`-invariant measure. -/]
theorem isFoelner_iff_of_closure_eq_top [SMulInvariantMeasure G X μ] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    IsFoelner G μ l F ↔
      (∀ᶠ i in l, MeasurableSet (F i)) ∧
        (∀ᶠ i in l, μ (F i) ≠ 0) ∧
        (∀ᶠ i in l, μ (F i) ≠ ∞) ∧
        ∀ g ∈ S, Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0) :=
  ⟨fun hF ↦ ⟨hF.eventually_measurableSet, hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top,
    fun g _ ↦ hF.tendsto_meas_smul_symmDiff g⟩,
    fun ⟨hmeas, hne0, hnetop, ht⟩ ↦ .of_closure_eq_top hS hmeas hne0 hnetop ht⟩

/-- When `μ` is `G`-invariant and `S` generates `G`, the maximal Følner filter `maxFoelner G μ` is
already cut out by the translation-boundary pullbacks for elements of `S`. -/
@[to_additive maxAddFoelner_eq_of_closure_eq_top
/-- When `μ` is `G`-invariant and `S` generates `G`, the maximal additive Følner filter
`maxAddFoelner G μ` is already cut out by the translation-boundary pullbacks for elements of
`S`. -/]
theorem maxFoelner_eq_of_closure_eq_top [SMulInvariantMeasure G X μ] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    maxFoelner G μ =
      𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
        ⨅ g ∈ S, comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0) := by
  refine le_antisymm (inf_le_inf_left _ <| le_iInf₂ fun g _ ↦ iInf_le _ g) ?_
  set r : Filter (Set X) :=
    𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
      ⨅ g ∈ S, comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0)
  have hmem : {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ∈ r :=
    mem_inf_of_left (mem_principal_self _)
  refine (isFoelner_iff_tendsto r id).1 (.of_closure_eq_top hS
    (Filter.Eventually.mono hmem fun _ h ↦ h.1)
    (Filter.Eventually.mono hmem fun _ h ↦ h.2.1)
    (Filter.Eventually.mono hmem fun _ h ↦ h.2.2) fun g hg ↦ ?_)
  exact tendsto_comap.mono_left (inf_le_right.trans <| iInf₂_le g hg)

/-- From finite translation-boundary tests on subsets of `S`, construct a family indexed by
`Finset S × ℕ` of measurable sets of finite nonzero measure tending along `atTop` to the
`S`-restricted Følner filter. -/
@[to_additive exists_tendsto_addFoelnerFilter_atTop]
private theorem exists_tendsto_foelnerFilter_atTop {S : Set G}
    (h : ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ s : Set X, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
        ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε) :
    ∃ F : Finset S × ℕ → Set X,
      (∀ i, MeasurableSet (F i) ∧ μ (F i) ≠ 0 ∧ μ (F i) ≠ ∞) ∧
        Tendsto F atTop (𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
          ⨅ g ∈ S, comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0)) := by
  classical
  choose F hmeas hne0 hnetop hlt using fun i : Finset S × ℕ ↦
    h (i.1.image Subtype.val) (by simp) ((i.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ (by simp)
  refine ⟨F, fun i ↦ ⟨hmeas i, hne0 i, hnetop i⟩, tendsto_inf.2
    ⟨tendsto_principal.2 (.of_forall fun i ↦ ⟨hmeas i, hne0 i, hnetop i⟩),
      tendsto_iInf.2 fun g ↦ tendsto_iInf.2 fun hg ↦ tendsto_comap_iff.2 ?_⟩⟩
  have hsnd : Tendsto (fun i : Finset S × ℕ ↦ i.2 + 1) atTop atTop :=
    tendsto_atTop_atTop_of_monotone
      (fun _ _ hij ↦ Nat.add_le_add_right (Prod.le_def.1 hij).2 1)
      fun n ↦ ⟨(∅, n), Nat.le_add_right n 1⟩
  have hbound : Tendsto (fun i : Finset S × ℕ ↦ ((i.2 + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp hsnd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop ({⟨g, hg⟩}, 0)] with i hi
  exact (hlt i g <| Finset.mem_image.2
    ⟨⟨g, hg⟩, (Prod.le_def.1 hi).1 (Finset.mem_singleton_self _), rfl⟩).le

/-- When `μ` is `G`-invariant and `S` generates `G`, passing all finite translation-boundary tests
on subsets of `S` yields a Følner family indexed by `Finset S × ℕ` along `atTop`. -/
@[to_additive exists_isAddFoelner_atTop_of_closure_eq_top
/-- When `μ` is `G`-invariant and `S` generates `G`, passing all finite additive
translation-boundary tests on subsets of `S` yields an additive Følner family indexed by
`Finset S × ℕ` along `atTop`. -/]
theorem exists_isFoelner_atTop_of_closure_eq_top [SMulInvariantMeasure G X μ] {S : Set G}
    (hS : Subgroup.closure S = ⊤)
    (h : ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ s : Set X, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
        ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε) :
    ∃ F : Finset S × ℕ → Set X,
      (∀ i, MeasurableSet (F i) ∧ μ (F i) ≠ 0 ∧ μ (F i) ≠ ∞) ∧ IsFoelner G μ atTop F := by
  obtain ⟨F, hF, htend⟩ := exists_tendsto_foelnerFilter_atTop h
  refine ⟨F, hF, ?_⟩
  rwa [isFoelner_iff_tendsto, maxFoelner_eq_of_closure_eq_top hS]

/-- Finite-test characterization of nontriviality of the Følner filter restricted to a subset `S`,
without assuming measure invariance. -/
@[to_additive addFoelnerFilter_neBot_iff]
private theorem foelnerFilter_neBot_iff {S : Set G} :
    (𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
        ⨅ g ∈ S, comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0)).NeBot ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ s : Set X, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
          ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε := by
  set r : Filter (Set X) :=
    𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
      ⨅ g ∈ S, comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0)
  constructor
  · intro hne K hKS ε hε
    have hmem : ∀ᶠ s in r, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ :=
      mem_inf_of_left (mem_principal_self _)
    have hK : ∀ᶠ s in r, ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε :=
      (eventually_all_finset K).2 fun g hg ↦
        (tendsto_comap.mono_left (inf_le_right.trans <| iInf₂_le g (hKS hg))).eventually
          (gt_mem_nhds (pos_iff_ne_zero.2 hε))
    obtain ⟨s, ⟨hm, h0, htop⟩, hsK⟩ := (hmem.and hK).exists
    exact ⟨s, hm, h0, htop, hsK⟩
  · intro h
    classical
    obtain ⟨_, _, htend⟩ := exists_tendsto_foelnerFilter_atTop h
    exact htend.neBot

/-- When `μ` is `G`-invariant and `S` generates `G`, `maxFoelner G μ` is nontrivial if and only if
every finite subset `K ⊆ S` and nonzero tolerance `ε : ℝ≥0∞` admit a measurable set of finite
nonzero measure passing the `K`-test. -/
@[to_additive maxAddFoelner_neBot_iff_of_closure_eq_top
/-- When `μ` is `G`-invariant and `S` generates `G`, `maxAddFoelner G μ` is nontrivial if and only
if every finite subset `K ⊆ S` and nonzero tolerance `ε : ℝ≥0∞` admit a measurable set of finite
nonzero measure passing the `K`-test. -/]
theorem maxFoelner_neBot_iff_of_closure_eq_top [SMulInvariantMeasure G X μ] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    (maxFoelner G μ).NeBot ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ s : Set X, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
          ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε := by
  rw [maxFoelner_eq_of_closure_eq_top hS]
  exact foelnerFilter_neBot_iff

/-- Finite-test characterization of nontriviality of `maxFoelner G μ` for any measure `μ`. -/
@[to_additive maxAddFoelner_neBot_iff
/-- Finite-test characterization of nontriviality of `maxAddFoelner G μ` for any measure `μ`. -/]
theorem maxFoelner_neBot_iff :
    (maxFoelner G μ).NeBot ↔
      ∀ K : Finset G, ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ s : Set X, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
          ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε := by
  have h : maxFoelner G μ =
      𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
        ⨅ g ∈ (univ : Set G), comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0) := by
    simp only [maxFoelner, mem_univ, iInf_pos]
  rw [h, foelnerFilter_neBot_iff]
  simp only [subset_univ, true_imp_iff]

end TauCeti

end Foelner
