/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dual scalar testing and separability obstructions for Banach-valued local Sobolev maps

For a complete real normed space `F`, continuous linear functionals `ℓ : StrongDual ℝ F` separate
points by Hahn–Banach. Consequently:

1. Applying any `ℓ : StrongDual ℝ F` (or any coordinate evaluation `lp.evalCLM` on `lp G r`)
   carries `MemLpLoc` and `MemWkpLoc` into the corresponding scalar or coordinate class.
2. Conversely, once a map `u : E → F` and a candidate derivative field `D : E → E →L[ℝ] F` are
   already known to lie in `MemLpLoc p U` (for `1 ≤ p`), scalar weak differentiability of `ℓ ∘ u`
   with derivative `x ↦ ℓ ∘L D x` for every `ℓ : StrongDual ℝ F` suffices to place `u` in
   `MemWkpLoc p U 1`.
3. Without prior Bochner measurability (`AEStronglyMeasurable`), scalar testing does **not**
   suffice on nonseparable targets: for the uncountable orthonormal family
   `u : E → lp (fun _ : E => ℝ) 2`, `x ↦ lp.single 2 x 1` on any nontrivial finite-dimensional
   real normed space `E`, Riesz representation and countable support of `ℓ²` sequences force
   `ℓ ∘ u = 0` almost everywhere for every `ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2)`, so every
   scalar composition `ℓ ∘ u` belongs to `MemWkpLoc p U k` of every order `k` and exponent `p`.
   Yet the pairwise distance `√2 ≥ 1` between distinct values prevents `u` from having an almost
   everywhere separable range on any set of positive measure (Pettis's measurability theorem), so
   `u` fails `MemLpLoc p U` and `MemWkpLoc p U k` on every domain with nonempty interior.

## Main declarations

* `TauCeti.MemLpLoc.comp_strongDual`, `TauCeti.MemWkpLoc.comp_strongDual`: composition with a
  continuous linear functional preserves `MemLpLoc` and `MemWkpLoc`.
* `TauCeti.memWkpLoc_one_of_forall_strongDual`,
  `TauCeti.memWkpLoc_one_opens_of_forall_strongDual`: sufficiency of dual testing for
  `MemWkpLoc p U 1` once `u` and `D` lie in `MemLpLoc p U` (`1 ≤ p`).
* `TauCeti.MemLpLoc.lp_eval`, `TauCeti.MemWkpLoc.lp_eval`, `TauCeti.MemLpLoc.lp_single`,
  `TauCeti.MemWkpLoc.lp_single`: coordinate projection and single-coordinate inclusion on `lp G r`.
* `TauCeti.strongDual_comp_lp_single_ae_eq_zero`: every continuous linear functional on
  `lp (fun _ : E => ℝ) 2` vanishes almost everywhere along `x ↦ lp.single 2 x 1` under any
  atomless measure.
* `TauCeti.not_aestronglyMeasurable_lp_single`: `x ↦ lp.single 2 x 1` is not Bochner
  a.e.-strongly measurable on any set of positive atomless measure.
* `TauCeti.forall_strongDual_memWkpLoc_and_not_memLpLoc_lp_single`: on any domain `U` with
  nonempty interior in a nontrivial finite-dimensional space, all scalar dual compositions and
  coordinates lie in `MemWkpLoc p U k`, whereas the map itself lies in neither `MemLpLoc p U` nor
  `MemWkpLoc p U k`.

## References

* W. Arendt, M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Theorem 1.1.20 (Pettis measurability theorem).
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-! ### Dual testing and Bochner integrability -/

section StrongDual

/-- Applying a continuous linear functional preserves local `Lᵖ` membership. -/
theorem MemLpLoc.comp_strongDual {E F : Type*} [TopologicalSpace E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {u : E → F}
    (hu : MemLpLoc p U u) (ℓ : StrongDual ℝ F) :
    MemLpLoc p U (fun x => ℓ (u x)) :=
  hu.clm_comp ℓ

/-- Applying a continuous linear functional preserves local Sobolev membership of every order. -/
theorem MemWkpLoc.comp_strongDual {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} {u : E → F} (hu : MemWkpLoc p U k u) (ℓ : StrongDual ℝ F) :
    MemWkpLoc p U k (fun x => ℓ (u x)) :=
  hu.clm_comp ℓ

/-- **Sufficiency of dual scalar testing for `MemWkpLoc` of order `1`.** Once `u : E → F` and a
candidate derivative field `D : E → E →L[ℝ] F` into a complete space `F` already belong to
`MemLpLoc p U` with `1 ≤ p`, `u` belongs to `MemWkpLoc p U 1` as soon as `ℓ ∘ u` has weak
derivative `x ↦ ℓ ∘L D x` on `interior U` for every `ℓ : StrongDual ℝ F`. -/
theorem memWkpLoc_one_of_forall_strongDual {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {p : ℝ≥0∞} {U : Set E} {u : E → F} (D : E → E →L[ℝ] F) (hp : 1 ≤ p)
    (hu : MemLpLoc p U u) (hD : MemLpLoc p U D)
    (h : ∀ ℓ : StrongDual ℝ F,
      HasWeakFDerivOn volume (Opens.interior U) (fun x => ℓ (u x)) (fun x => ℓ.comp (D x))) :
    MemWkpLoc p U 1 u := by
  have hu_int : LocallyIntegrableOn u (Opens.interior U) volume :=
    (hu.mono_set interior_subset).locallyIntegrableOn hp isOpen_interior.isLocallyClosed
  have hD_int : ∀ v : E, LocallyIntegrableOn (fun x => D x v) (Opens.interior U) volume := fun v =>
    ((hD.mono_set interior_subset).clm_comp
      (ContinuousLinearMap.apply ℝ F v)).locallyIntegrableOn hp isOpen_interior.isLocallyClosed
  exact memWkpLoc_one_iff.2 ⟨hu, D, hasWeakFDerivOn_of_forall_strongDual hu_int hD_int h, hD⟩

/-- **Sufficiency of dual scalar testing on an open set.** For an open set `Ω : Opens E` and
`1 ≤ p`, local `Lᵖ` bounds on `u` and `D` together with scalar weak differentiability against all
`ℓ : StrongDual ℝ F` give `MemWkpLoc p Ω 1 u`. -/
theorem memWkpLoc_one_opens_of_forall_strongDual {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (D : E → E →L[ℝ] F) (hp : 1 ≤ p)
    (hu : MemLpLoc p Ω u) (hD : MemLpLoc p Ω D)
    (h : ∀ ℓ : StrongDual ℝ F,
      HasWeakFDerivOn volume Ω (fun x => ℓ (u x)) (fun x => ℓ.comp (D x))) :
    MemWkpLoc p Ω 1 u := by
  refine memWkpLoc_one_of_forall_strongDual D hp hu hD fun ℓ => ?_
  rw [Opens.interior_coe]
  exact h ℓ

end StrongDual

/-! ### Sequence-space (`lp`) coordinate projections and single-coordinate embeddings -/

section lpSpace

variable {E ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, NormedSpace ℝ (G i)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- Evaluating an `lp`-valued locally `Lᵖ` map at any coordinate `i` gives a locally `Lᵖ` map. -/
theorem MemLpLoc.lp_eval [TopologicalSpace E] [MeasureSpace E] {p : ℝ≥0∞} {U : Set E}
    {u : E → lp G r} (hu : MemLpLoc p U u) (i : ι) :
    MemLpLoc p U (fun x => u x i) :=
  hu.clm_comp (lp.evalCLM ℝ G r i)

/-- Evaluating an `lp`-valued `MemWkpLoc` map at any coordinate `i` preserves `MemWkpLoc` of every
order. -/
theorem MemWkpLoc.lp_eval [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [OpensMeasurableSpace E] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {u : E → lp G r}
    (hu : MemWkpLoc p U k u) (i : ι) [CompleteSpace (G i)] :
    MemWkpLoc p U k (fun x => u x i) :=
  hu.clm_comp (lp.evalCLM ℝ G r i)

/-- Embedding a locally `Lᵖ` map into a single coordinate of `lp G r` preserves `MemLpLoc`. -/
theorem MemLpLoc.lp_single [DecidableEq ι] [TopologicalSpace E] [MeasureSpace E] {p : ℝ≥0∞}
    {U : Set E} {i : ι} {a : E → G i} (ha : MemLpLoc p U a) :
    MemLpLoc p U (fun x => lp.single r i (a x)) :=
  ha.clm_comp (lp.singleContinuousLinearMap ℝ G r i)

/-- Embedding a `MemWkpLoc` map into a single coordinate of `lp G r` preserves `MemWkpLoc` of every
order. -/
theorem MemWkpLoc.lp_single [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [∀ j, CompleteSpace (G j)] {p : ℝ≥0∞} {U : Set E}
    {k : ℕ} {i : ι} {a : E → G i} (ha : MemWkpLoc p U k a) :
    MemWkpLoc p U k (fun x => lp.single r i (a x)) :=
  ha.clm_comp (lp.singleContinuousLinearMap ℝ G r i)

end lpSpace

/-! ### Non-sufficiency of scalar testing without Bochner measurability -/

section NonseparableCounterexample

/-- Under any measure `μ` on `E` assigning zero mass to singletons, every continuous linear
functional `ℓ` on the nonseparable Hilbert space `lp (fun _ : E => ℝ) 2` vanishes `μ`-almost
everywhere along the orthonormal family `x ↦ lp.single 2 x 1`: by Riesz representation `ℓ` pairs
with an `ℓ²` family whose support is countable, hence `μ`-null. -/
theorem strongDual_comp_lp_single_ae_eq_zero {E : Type*} [DecidableEq E] [MeasurableSpace E]
    {μ : Measure E} [NullSingletonClass μ] (ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2)) :
    (fun x : E => ℓ (lp.single 2 x (1 : ℝ))) =ᵐ[μ] 0 := by
  let g : lp (fun _ : E => ℝ) 2 := (InnerProductSpace.toDual ℝ (lp (fun _ : E => ℝ) 2)).symm ℓ
  have hval : ∀ x : E, ℓ (lp.single 2 x (1 : ℝ)) = g x := fun x => by
    rw [← InnerProductSpace.toDual_symm_apply, lp.inner_single_right (G := fun _ : E => ℝ)]
    simp [g]
  have hsupp : {x : E | g x ≠ 0}.Countable := by
    refine ((g.prop.summable (by norm_num)).countable_support).mono fun x hx => ?_
    simp only [Function.mem_support, ne_eq]
    exact Real.rpow_ne_zero (norm_nonneg _) (by norm_num) |>.2 (norm_ne_zero_iff.2 hx)
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) (hsupp.measure_zero μ)
  simpa [hval x] using hx

/-- Distinct unit basis vectors in `lp (fun _ : E => ℝ) 2` lie at distance at least `1`. -/
private theorem one_le_dist_lp_single {E : Type*} [DecidableEq E] {x y : E} (hxy : x ≠ y) :
    (1 : ℝ) ≤ dist (lp.single (E := fun _ : E => ℝ) 2 x 1)
      (lp.single (E := fun _ : E => ℝ) 2 y 1) := by
  rw [dist_eq_norm]
  have hle := lp.norm_apply_le_norm (p := 2) (by norm_num)
    (lp.single (E := fun _ : E => ℝ) 2 x 1 - lp.single (E := fun _ : E => ℝ) 2 y 1) x
  rwa [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_single, lp.coeFn_single, Pi.single_eq_same,
    Pi.single_eq_of_ne hxy, sub_zero, norm_one] at hle

/-- Under any measure `μ` assigning zero mass to singletons, the unit-basis map
`x ↦ lp.single 2 x 1` into `lp (fun _ : E => ℝ) 2` is not Bochner `AEStronglyMeasurable` on any
set `s` of positive measure: any separable set in the codomain contains at most countably many
pairwise `1`-separated points, whose preimage has `μ`-measure zero. -/
theorem not_aestronglyMeasurable_lp_single {E : Type*} [DecidableEq E] [MeasurableSpace E]
    {μ : Measure E} [NullSingletonClass μ] {s : Set E} (hs : μ s ≠ 0) :
    ¬ AEStronglyMeasurable (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1)
      (μ.restrict s) := by
  intro hu
  obtain ⟨t, ⟨c, hc_count, htc⟩, hae⟩ := hu.isSeparable_ae_range
  let S : Set E := {x : E | lp.single (E := fun _ : E => ℝ) 2 x 1 ∈ t}
  have hnear : ∀ x : S, ∃ z : c,
      dist (lp.single (E := fun _ : E => ℝ) 2 x.1 1) z.1 < 1 / 2 := fun x => by
    obtain ⟨z, hzc, hxz⟩ := Metric.mem_closure_iff.1 (htc x.2) (1 / 2) (by norm_num)
    exact ⟨⟨z, hzc⟩, hxz⟩
  choose f hf using hnear
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have h1 : (1 : ℝ) ≤ dist (lp.single (E := fun _ : E => ℝ) 2 x.1 1)
        (lp.single (E := fun _ : E => ℝ) 2 y.1 1) :=
      one_le_dist_lp_single (Subtype.coe_ne_coe.2 hne)
    have hlt : dist (lp.single (E := fun _ : E => ℝ) 2 x.1 1)
        (lp.single (E := fun _ : E => ℝ) 2 y.1 1) < 1 := by
      calc dist (lp.single (E := fun _ : E => ℝ) 2 x.1 1)
            (lp.single (E := fun _ : E => ℝ) 2 y.1 1)
          ≤ dist (lp.single (E := fun _ : E => ℝ) 2 x.1 1) (f x).1 +
              dist (lp.single (E := fun _ : E => ℝ) 2 y.1 1) (f x).1 := dist_triangle_right _ _ _
        _ = dist (lp.single (E := fun _ : E => ℝ) 2 x.1 1) (f x).1 +
              dist (lp.single (E := fun _ : E => ℝ) 2 y.1 1) (f y).1 := by rw [hxy]
        _ < 1 / 2 + 1 / 2 := add_lt_add (hf x) (hf y)
        _ = 1 := by norm_num
    exact h1.not_gt hlt
  have : Countable c := hc_count.to_subtype
  have hS_count : S.Countable := Set.countable_coe_iff.1 (Function.Injective.countable hfinj)
  have hS_zero : (μ.restrict s) S = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le s S).trans (hS_count.measure_zero μ).le)
  have hSc_zero : (μ.restrict s) Sᶜ = 0 := ae_iff.1 hae
  have h_univ : (μ.restrict s) univ = 0 := nonpos_iff_eq_zero.1 <| by
    calc (μ.restrict s) univ
        ≤ (μ.restrict s) S + (μ.restrict s) Sᶜ := by
          simpa only [union_compl_self] using measure_union_le S Sᶜ
      _ = 0 := by simp [hS_zero, hSc_zero]
  rw [Measure.restrict_apply_univ] at h_univ
  exact hs h_univ

section NormedDomain

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

/-- On any nontrivial finite-dimensional real normed space, every continuous linear functional
composed with `x ↦ lp.single 2 x 1` belongs to `MemWkpLoc p U k` for every exponent `p`, set `U`,
and order `k`. -/
theorem memWkpLoc_strongDual_comp_lp_single (p : ℝ≥0∞) (U : Set E) (k : ℕ)
    (ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2)) :
    MemWkpLoc p U k (fun x : E => ℓ (lp.single (E := fun _ : E => ℝ) 2 x 1)) := by
  have hae : (0 : E → ℝ) =ᵐ[volume] fun x : E => ℓ (lp.single (E := fun _ : E => ℝ) 2 x 1) :=
    (strongDual_comp_lp_single_ae_eq_zero (μ := volume) ℓ).symm
  have hlp : MemLpLoc p U (fun x : E => ℓ (lp.single (E := fun _ : E => ℝ) 2 x 1)) :=
    memLpLoc_iff.2 fun _ _ _ => MemLp.zero.ae_eq (ae_restrict_of_ae hae)
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 hlp
  | succ k =>
    refine memWkpLoc_succ_iff.mpr ⟨hlp, 0, ?_, memWkpLoc_zero_fun⟩
    have h0 : HasWeakFDerivOn volume (Opens.interior U) (fun _ : E => (0 : ℝ)) 0 :=
      hasWeakFDerivOn_iff.mpr fun _ => hasWeakLineDerivOn_const (0 : ℝ)
    exact h0.congr_ae (ae_restrict_of_ae hae)

/-- On any set `U` with nonempty interior in a nontrivial finite-dimensional real normed space,
`x ↦ lp.single 2 x 1` fails `MemLpLoc p U` for every exponent `p : ℝ≥0∞` (including `0` and `∞`),
because it is not `AEStronglyMeasurable` on any closed ball of positive radius inside `U`. -/
theorem not_memLpLoc_lp_single {U : Set E} (hU : (interior U).Nonempty) (p : ℝ≥0∞) :
    ¬ MemLpLoc p U (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) := by
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  have hsub : Metric.closedBall x₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans (hball.trans interior_subset)
  have hpos_ball : 0 < (volume : Measure E) (Metric.ball x₀ (r / 2)) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.2 (half_pos hr))
  have hpos : (volume : Measure E) (Metric.closedBall x₀ (r / 2)) ≠ 0 :=
    (hpos_ball.trans_le (measure_mono Metric.ball_subset_closedBall)).ne'
  intro hmem
  exact not_aestronglyMeasurable_lp_single hpos
    (memLpLoc_iff.1 hmem (Metric.closedBall x₀ (r / 2)) hsub
      (isCompact_closedBall x₀ (r / 2))).aestronglyMeasurable

/-- On any set `U` with nonempty interior in a nontrivial finite-dimensional real normed space,
`x ↦ lp.single 2 x 1` fails `MemWkpLoc p U k` for every exponent `p : ℝ≥0∞` and order `k : ℕ`. -/
theorem not_memWkpLoc_lp_single {U : Set E} (hU : (interior U).Nonempty) (p : ℝ≥0∞) (k : ℕ) :
    ¬ MemWkpLoc p U k (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) := fun h =>
  not_memLpLoc_lp_single hU p h.memLpLoc

/-- **Scalar dual testing and coordinatewise membership do not imply `MemLpLoc` or `MemWkpLoc`
without Bochner measurability.** For `u : E → lp (fun _ : E => ℝ) 2`, `x ↦ lp.single 2 x 1` on any
domain `U` with nonempty interior in a nontrivial finite-dimensional space `E`, every scalar
composition `ℓ ∘ u` (`ℓ : StrongDual ℝ _`) and every coordinate `x ↦ u x y` belongs to
`MemWkpLoc p U k` for all `p` and `k`, while `u` itself belongs to neither `MemLpLoc p U` nor
`MemWkpLoc p U k`. -/
theorem forall_strongDual_memWkpLoc_and_not_memLpLoc_lp_single {U : Set E}
    (hU : (interior U).Nonempty) (p : ℝ≥0∞) (k : ℕ) :
    (∀ ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2),
      MemWkpLoc p U k (fun x : E => ℓ (lp.single (E := fun _ : E => ℝ) 2 x 1))) ∧
    (∀ y : E, MemWkpLoc p U k (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1 y)) ∧
    ¬ MemLpLoc p U (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) ∧
    ¬ MemWkpLoc p U k (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) :=
  ⟨memWkpLoc_strongDual_comp_lp_single p U k,
    fun y => memWkpLoc_strongDual_comp_lp_single p U k (lp.evalCLM ℝ (fun _ : E => ℝ) 2 y),
    not_memLpLoc_lp_single hU p, not_memWkpLoc_lp_single hU p k⟩

end NormedDomain

end NonseparableCounterexample

end TauCeti
