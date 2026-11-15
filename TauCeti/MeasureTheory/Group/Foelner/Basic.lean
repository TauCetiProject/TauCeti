/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FoelnerFilter

/-!
# Filter compatibility and generating-set reductions for Følner families

Let a group `G` act on a measurable space `X` with a measure `μ`. Mathlib defines Følner families
`IsFoelner G μ l F` along a filter `l` and the maximal Følner filter `maxFoelner G μ`. This file
develops three basic tools for manipulating `IsFoelner` and `maxFoelner` (together with their
additive counterparts `IsAddFoelner` and `maxAddFoelner`):

1. **Measure-theoretic translation cocycle bounds** under `[SMulInvariantMeasure G X μ]`:
   invariance of `μ ((g • s) ∆ (g • t))`, inversion symmetry `μ ((g⁻¹ • s) ∆ s) = μ ((g • s) ∆ s)`,
   and subadditivity along products and list words.
2. **Filter and perturbation compatibility**: eventual equality (`IsFoelner.congr`), restriction to
   a principal filter or subtype, cofinal monotone reindexing along `atTop`, invariance of
   `IsFoelner` and ultrafilter density means `IsFoelner.mean` under asymptotically negligible
   relative symmetric-difference perturbations `μ (F i ∆ F' i) / μ (F i) → 0`, and eventual
   `μ`-almost-everywhere equality.
3. **Generating-set reduction (Garrido Lemma 3.4, BDHV Remark G.5.3)**: for an invariant measure
   `μ`, the elements `g : G` with `μ ((g • F i) ∆ F i) / μ (F i) → 0` form a subgroup
   `IsFoelner.vanishingSubgroup μ l F`. Consequently `IsFoelner`, `maxFoelner G μ`, and
   `(maxFoelner G μ).NeBot` can be tested purely on a generating set `S` with
   `Subgroup.closure S = ⊤`.

## Main definitions

* `IsFoelner.vanishingSubgroup`: the subgroup of group elements whose relative translation
  boundaries along `F` tend to zero.

## Main results

* `MeasureTheory.measure_mul_smul_symmDiff_le`:
  `μ (((g * h) • s) ∆ s) ≤ μ ((h • s) ∆ s) + μ ((g • s) ∆ s)`.
* `IsFoelner.congr`, `TauCeti.isFoelner_congr`: eventual-equality invariance of `IsFoelner`.
* `IsFoelner.of_tendsto_meas_symmDiff_div`, `IsFoelner.of_eventually_ae_eq`: stability of
  `IsFoelner` under asymptotically small relative symmetric differences and `ae`-equality.
* `IsFoelner.mean_eq_of_tendsto_meas_symmDiff_div`, `IsFoelner.mean_eq_of_eventually_ae_eq`:
  asymptotically equivalent Følner families induce the same ultrafilter density mean.
* `IsFoelner.of_closure_eq_top`, `TauCeti.isFoelner_iff_of_closure_eq_top`: generating-set
  criterion for `IsFoelner`.
* `TauCeti.maxFoelner_eq_of_closure_eq_top`: `maxFoelner G μ` is determined by a generating set of
  `G`.
* `TauCeti.maxFoelner_neBot_iff_of_closure_eq_top`, `TauCeti.maxFoelner_neBot_iff`: finite-test
  characterizations of `(maxFoelner G μ).NeBot`.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Lemma 3.4.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5, Remark G.5.3.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Pointwise symmDiff Topology

namespace MeasureTheory

section SMulSymmDiff

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- A measure-preserving group action preserves the measure of symmetric differences. -/
@[to_additive (attr := simp)
/-- A measure-preserving additive group action preserves the measure of symmetric differences. -/]
theorem measure_smul_symmDiff_smul (g : G) (s t : Set X) :
    μ ((g • s) ∆ (g • t)) = μ (s ∆ t) := by
  rw [← smul_set_symmDiff, measure_smul]

/-- Translating a set by `g⁻¹` gives a symmetric difference of the same invariant measure as
translating by `g`. -/
@[to_additive
/-- Translating a set by `-g` gives a symmetric difference of the same invariant measure as
translating by `g`. -/]
theorem measure_inv_smul_symmDiff_self (g : G) (s : Set X) :
    μ ((g⁻¹ • s) ∆ s) = μ ((g • s) ∆ s) := by
  rw [measure_inv_smul_symmDiff, symmDiff_comm]

/-- Subadditivity of `μ ((g • s) ∆ s)` under group multiplication. -/
@[to_additive
/-- Subadditivity of `μ ((g +ᵥ s) ∆ s)` under group addition. -/]
theorem measure_mul_smul_symmDiff_le (g h : G) (s : Set X) :
    μ (((g * h) • s) ∆ s) ≤ μ ((h • s) ∆ s) + μ ((g • s) ∆ s) :=
  calc
    μ (((g * h) • s) ∆ s) = μ ((g • (h • s)) ∆ s) := by rw [mul_smul]
    _ ≤ μ ((g • (h • s)) ∆ (g • s)) + μ ((g • s) ∆ s) := measure_symmDiff_le _ (g • s) _
    _ = μ ((h • s) ∆ s) + μ ((g • s) ∆ s) := by rw [measure_smul_symmDiff_smul]

/-- Subadditivity of `μ ((g • s) ∆ s)` along a list product in `G`. -/
@[to_additive
/-- Subadditivity of `μ ((g +ᵥ s) ∆ s)` along a list sum in `G`. -/]
theorem measure_list_prod_smul_symmDiff_le (L : List G) (s : Set X) :
    μ ((L.prod • s) ∆ s) ≤ (L.map fun g ↦ μ ((g • s) ∆ s)).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons, add_comm] using
      (measure_mul_smul_symmDiff_le μ g L.prod s).trans (add_le_add_left ih _)

end SMulSymmDiff

end MeasureTheory

section Foelner

variable {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  {l : Filter ι} {u : Ultrafilter ι} {F F' : ι → Set X}

namespace IsFoelner

/-! ### Eventual equality and subnet compatibility -/

/-- A family eventually equal to a Følner family along `l` is itself Følner. -/
@[to_additive
/-- A family eventually equal to an additive Følner family along `l` is itself Følner. -/]
theorem congr (hF : IsFoelner G μ l F) (h : F =ᶠ[l] F') : IsFoelner G μ l F' :=
  (isFoelner_iff_tendsto _ _).2 <| ((isFoelner_iff_tendsto _ _).1 hF).congr' h

/-- Restricting a Følner family to `l ⊓ 𝓟 s` preserves the Følner property. -/
@[to_additive
/-- Restricting an additive Følner family to `l ⊓ 𝓟 s` preserves the Følner property. -/]
theorem inf_principal (hF : IsFoelner G μ l F) (s : Set ι) :
    IsFoelner G μ (l ⊓ 𝓟 s) F :=
  hF.mono inf_le_left

/-- Restricting the index type of a Følner family to a subset via `Filter.comap (↑)` preserves the
Følner property. -/
@[to_additive
/-- Restricting the index type of an additive Følner family to a subset via `Filter.comap (↑)`
preserves the Følner property. -/]
theorem comap_subtype (hF : IsFoelner G μ l F) (s : Set ι) :
    IsFoelner G μ (comap ((↑) : s → ι) l) (fun i : s ↦ F i) :=
  hF.comp_tendsto tendsto_comap

/-- Reindexing a Følner family along `atTop` by a monotone cofinal map preserves `IsFoelner`. -/
@[to_additive
/-- Reindexing an additive Følner family along `atTop` by a monotone cofinal map preserves
`IsAddFoelner`. -/]
theorem comp_of_monotone_cofinal {ι' : Type*} [Preorder ι] [Preorder ι'] {φ : ι' → ι}
    (hF : IsFoelner G μ atTop F) (hmono : Monotone φ) (hcof : ∀ i, ∃ j, i ≤ φ j) :
    IsFoelner G μ atTop (F ∘ φ) :=
  hF.comp_tendsto (tendsto_atTop_atTop_of_monotone hmono hcof)

end IsFoelner

/-- Eventual equality preserves `IsFoelner`. -/
@[to_additive isAddFoelner_congr /-- Eventual equality preserves `IsAddFoelner`. -/]
theorem TauCeti.isFoelner_congr (h : F =ᶠ[l] F') : IsFoelner G μ l F ↔ IsFoelner G μ l F' :=
  ⟨fun hF ↦ hF.congr h, fun hF' ↦ hF'.congr h.symm⟩

namespace IsFoelner

/-! ### Asymptotic symmetric-difference perturbations -/

/-- If `μ (F i ∆ F' i) / μ (F i) → 0` along a Følner family `F`, then `μ (F' i) / μ (F i) → 1`. -/
@[to_additive
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
@[to_additive
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

/-- Perturbing a Følner family `F` to measurable sets `F'` with `μ (F i ∆ F' i) / μ (F i) → 0`
preserves `IsFoelner`. -/
@[to_additive
/-- Perturbing an additive Følner family `F` to measurable sets `F'` with
`μ (F i ∆ F' i) / μ (F i) → 0` preserves `IsAddFoelner`. -/]
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

/-- Replacing each set in a Følner family by an eventually measurable `μ`-almost-everywhere equal
set preserves `IsFoelner`. -/
@[to_additive
/-- Replacing each set in an additive Følner family by an eventually measurable
`μ`-almost-everywhere equal set preserves `IsAddFoelner`. -/]
theorem of_eventually_ae_eq [SMulInvariantMeasure G X μ] (hF : IsFoelner G μ l F)
    (hmeas : ∀ᶠ i in l, MeasurableSet (F' i)) (hae : ∀ᶠ i in l, F i =ᵐ[μ] F' i) :
    IsFoelner G μ l F' := by
  refine hF.of_tendsto_meas_symmDiff_div hmeas (tendsto_const_nhds.congr' ?_)
  filter_upwards [hae] with i hi
  simp [measure_symmDiff_eq_zero_iff.2 hi]

/-- Two Følner families along an ultrafilter `u` with `μ (F i ∆ F' i) / μ (F i) → 0` induce the
same density-limit mean on all subsets of `X`. -/
@[to_additive
/-- Two additive Følner families along an ultrafilter `u` with `μ (F i ∆ F' i) / μ (F i) → 0`
induce the same density-limit mean on all subsets of `X`. -/]
theorem mean_eq_of_tendsto_meas_symmDiff_div (hF : IsFoelner G μ u F) (hF' : IsFoelner G μ u F')
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
  refine (tendsto_nhds_unique (hF'.tendsto_nhds_mean s) (hprod.congr' ?_)).symm
  filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi0 hitop
  exact ENNReal.div_mul_div_cancel hi0 hitop

/-- Two Følner families along an ultrafilter `u` that are eventually `μ`-almost-everywhere equal
induce the same density-limit mean on all subsets of `X`. -/
@[to_additive
/-- Two additive Følner families along an ultrafilter `u` that are eventually
`μ`-almost-everywhere equal induce the same density-limit mean on all subsets of `X`. -/]
theorem mean_eq_of_eventually_ae_eq (hF : IsFoelner G μ u F) (hF' : IsFoelner G μ u F')
    (hae : ∀ᶠ i in (u : Filter ι), F i =ᵐ[μ] F' i) (s : Set X) :
    mean μ u F s = mean μ u F' s := by
  refine hF.mean_eq_of_tendsto_meas_symmDiff_div hF' (tendsto_const_nhds.congr' ?_) s
  filter_upwards [hae] with i hi
  simp [measure_symmDiff_eq_zero_iff.2 hi]

/-! ### Generating-set reduction (Garrido Lemma 3.4) -/

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
        μ ((h • F i) ∆ F i) / μ (F i) + μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0) := by
      simpa using hh.add hg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (.of_forall fun _ ↦ zero_le) (.of_forall fun i ↦ ?_)
    rw [← ENNReal.add_div]
    exact ENNReal.div_le_div_right (measure_mul_smul_symmDiff_le μ g h (F i)) _
  inv_mem' {g} hg := by
    simp_rw [Set.mem_ofPred_eq, measure_inv_smul_symmDiff_self] at hg ⊢
    exact hg

@[to_additive (attr := simp)]
theorem mem_vanishingSubgroup [SMulInvariantMeasure G X μ] {g : G} :
    g ∈ vanishingSubgroup μ l F ↔
      Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0) :=
  Iff.rfl

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
    have hle : Subgroup.closure S ≤ vanishingSubgroup μ l F :=
      (Subgroup.closure_le (vanishingSubgroup μ l F)).2 htendsto
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
  constructor
  · intro hne K _ ε hε
    have hF := isFoelner_maxFoelner G μ
    have hK : ∀ᶠ s in maxFoelner G μ, ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε :=
      (eventually_all_finset K).2 fun g _ ↦
        (hF.tendsto_meas_smul_symmDiff g).eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))
    obtain ⟨s, hm, h0, htop, hsK⟩ :=
      (hF.eventually_measurableSet.and (hF.eventually_meas_ne_zero.and
        (hF.eventually_meas_ne_top.and hK))).exists
    exact ⟨s, hm, h0, htop, hsK⟩
  · intro h
    classical
    choose F hmeas hne0 hnetop hlt using fun i : Finset S × ℕ ↦
      h (i.1.image Subtype.val) (by simp) ((i.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ (by simp)
    have hF : IsFoelner G μ atTop F := by
      refine .of_closure_eq_top hS (.of_forall hmeas) (.of_forall hne0) (.of_forall hnetop)
        fun g hg ↦ ?_
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
    exact ((isFoelner_iff_tendsto _ _).1 hF).neBot

/-- Finite-test characterization of nontriviality of `maxFoelner G μ` for an invariant measure. -/
@[to_additive maxAddFoelner_neBot_iff
/-- Finite-test characterization of nontriviality of `maxAddFoelner G μ` for an invariant
measure. -/]
theorem maxFoelner_neBot_iff [SMulInvariantMeasure G X μ] :
    (maxFoelner G μ).NeBot ↔
      ∀ K : Finset G, ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ s : Set X, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ ∧
          ∀ g ∈ K, μ ((g • s) ∆ s) / μ s < ε := by
  simpa using maxFoelner_neBot_iff_of_closure_eq_top (G := G) (μ := μ) Subgroup.closure_univ

end TauCeti

end Foelner
