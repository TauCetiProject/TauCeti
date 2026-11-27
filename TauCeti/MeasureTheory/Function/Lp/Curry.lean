/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Iterated
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Fubini's theorem for Bochner spaces

For a finite exponent `1 ≤ p < ∞`, an arbitrary measure `μ` on `α` and a σ-finite measure `ν` on
`β`, a function of two variables in `Lᵖ(μ ⊗ ν; E)` is the same thing as a function of the first
variable with values in `Lᵖ(ν; E)`:

`Lᵖ(μ ⊗ ν; E) ≃ Lᵖ(μ; Lᵖ(ν; E))`, `F ↦ (s ↦ [F (s, ·)])`.

The map sends `F` to the class of its sections. It is a linear isometry, onto when `E` is
complete, and it sends the class of the indicator of a rectangle `A ×ˢ B` with value `x` to the
class of the indicator of `A` with value the class of the indicator of `B` with value `x`.

The section of a function `f : α × β → E` at `s` is recorded as an element of `Lᵖ(ν; E)` by
`MeasureTheory.curryLp p ν f s`, with the junk value `0` when the section is not in `Lᵖ(ν; E)`.
The essential point is that `s ↦ curryLp p ν f s` is almost everywhere strongly measurable as an
`Lᵖ(ν; E)`-valued function as soon as `f ∈ Lᵖ(μ ⊗ ν; E)`
(`MeasureTheory.MemLp.aestronglyMeasurable_curryLp`); its norm is then the iterated norm of `f`,
which is the norm of `f` by Tonelli's theorem (`TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm`).

The measurability is proved first for indicators of measurable sets. On a set `S` of finite
`ν`-measure, the sets `A ⊆ α × β` for which `s ↦ [𝟙_{A_s ∩ S} x]` is strongly measurable contain
the measurable rectangles and are closed under complements and countable disjoint unions, so they
are all measurable sets by the π-λ theorem. An exhaustion of `β` by such sets `S` removes the
truncation. The general case follows by approximation in `Lᵖ(μ ⊗ ν; E)`: convergence in
`Lᵖ(μ ⊗ ν; E)` is convergence of the section classes in `Lᵖ(μ; Lᵖ(ν; E))`, hence almost
everywhere along a subsequence.

Surjectivity follows from density of simple functions in `Lᵖ(μ; Lᵖ(ν; E))`: the image of the
isometry is closed when `E` is complete, and it contains the classes `𝟙_A c` with
`c ∈ Lᵖ(ν; E)`, namely the images of `(s, t) ↦ 𝟙_A(s) c(t)`.

## Main definitions and results

* `MeasureTheory.curryLp p ν f s`: the class in `Lᵖ(ν; E)` of the section `f (s, ·)`.
* `MeasureTheory.curryLp_indicator`, `MeasureTheory.curryLp_indicator_prod_univ`: the section
  classes of the indicator `𝟙_A c` of a set with finite sections, and of `(s, t) ↦ 𝟙_A(s) g(t)`.
* `MeasureTheory.MemLp.aestronglyMeasurable_curryLp`, `MeasureTheory.MemLp.memLp_curryLp`,
  `MeasureTheory.MemLp.eLpNorm_curryLp`: for `f ∈ Lᵖ(μ ⊗ ν; E)` the section classes form an
  element of `Lᵖ(μ; Lᵖ(ν; E))` with the same norm.
* `MeasureTheory.Lp.curryₗᵢ`: the linear isometry `Lᵖ(μ ⊗ ν; E) → Lᵖ(μ; Lᵖ(ν; E))`, with the
  section formula `MeasureTheory.Lp.ae_ae_curryₗᵢ_apply` and the rectangle formula
  `MeasureTheory.Lp.curryₗᵢ_indicatorConstLp_prod`.
* `MeasureTheory.Lp.curryEquiv`: for complete `E`, the linear isometric equivalence
  `Lᵖ(μ ⊗ ν; E) ≃ Lᵖ(μ; Lᵖ(ν; E))`, with the section formula for its inverse
  `MeasureTheory.Lp.ae_ae_curryEquiv_symm_apply`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, Proposition 1.2.24.
-/

public section

noncomputable section

open Filter Set
open scoped ENNReal Topology symmDiff

namespace MeasureTheory

section CurryLp

variable {α β E : Type*} [MeasurableSpace β] {ν : Measure β} [NormedAddCommGroup E] {p : ℝ≥0∞}

section Basic

/-- The class in `Lᵖ(ν; E)` of the section `y ↦ f (x, y)` of a function `f : α × β → E`, or `0`
when this section is not in `Lᵖ(ν; E)`. -/
def curryLp (p : ℝ≥0∞) (ν : Measure β) (f : α × β → E) (x : α) : Lp E p ν :=
  open Classical in
  if h : MemLp (fun y ↦ f (x, y)) p ν then h.toLp _ else 0

/-- A section in `Lᵖ(ν; E)` is sent to its class. -/
theorem curryLp_of_memLp {f : α × β → E} {x : α} (h : MemLp (fun y ↦ f (x, y)) p ν) :
    curryLp p ν f x = h.toLp _ := by
  simp [curryLp, h]

/-- A section outside `Lᵖ(ν; E)` is sent to `0`. -/
theorem curryLp_of_not_memLp {f : α × β → E} {x : α} (h : ¬MemLp (fun y ↦ f (x, y)) p ν) :
    curryLp p ν f x = 0 := by
  simp [curryLp, h]

/-- A section in `Lᵖ(ν; E)` is represented by its class. -/
theorem coeFn_curryLp {f : α × β → E} {x : α} (h : MemLp (fun y ↦ f (x, y)) p ν) :
    curryLp p ν f x =ᵐ[ν] fun y ↦ f (x, y) := by
  rw [curryLp_of_memLp h]
  exact h.coeFn_toLp

/-- The class of a section only depends on the section up to `ν`-null sets. -/
theorem curryLp_congr {f g : α × β → E} {x : α}
    (h : (fun y ↦ f (x, y)) =ᵐ[ν] fun y ↦ g (x, y)) : curryLp p ν f x = curryLp p ν g x := by
  by_cases hf : MemLp (fun y ↦ f (x, y)) p ν
  · rw [curryLp_of_memLp hf, curryLp_of_memLp (hf.ae_eq h)]
    exact MemLp.toLp_congr _ _ h
  · rw [curryLp_of_not_memLp hf, curryLp_of_not_memLp fun hg ↦ hf (hg.ae_eq h.symm)]

/-- The sections of the zero function have class `0`. -/
@[simp]
theorem curryLp_zero : curryLp p ν (0 : α × β → E) = 0 := by
  ext1 x
  rw [curryLp_of_memLp (by exact MemLp.zero), Pi.zero_apply]
  exact MemLp.toLp_zero _

/-- The class of the section of a sum is the sum of the classes when both sections are in
`Lᵖ(ν; E)`. -/
theorem curryLp_add {f g : α × β → E} {x : α} (hf : MemLp (fun y ↦ f (x, y)) p ν)
    (hg : MemLp (fun y ↦ g (x, y)) p ν) :
    curryLp p ν (f + g) x = curryLp p ν f x + curryLp p ν g x := by
  rw [curryLp_of_memLp (hf.add hg), curryLp_of_memLp hf, curryLp_of_memLp hg, ← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (.of_forall fun _ ↦ Pi.add_apply _ _ _)

/-- The class of the section of a difference is the difference of the classes when both sections
are in `Lᵖ(ν; E)`. -/
theorem curryLp_sub {f g : α × β → E} {x : α} (hf : MemLp (fun y ↦ f (x, y)) p ν)
    (hg : MemLp (fun y ↦ g (x, y)) p ν) :
    curryLp p ν (f - g) x = curryLp p ν f x - curryLp p ν g x := by
  rw [curryLp_of_memLp (hf.sub hg), curryLp_of_memLp hf, curryLp_of_memLp hg, ← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _ (.of_forall fun _ ↦ Pi.sub_apply _ _ _)

/-- The class of the section of a negation is the negation of the class when the section is in
`Lᵖ(ν; E)`. -/
theorem curryLp_neg {f : α × β → E} {x : α} (hf : MemLp (fun y ↦ f (x, y)) p ν) :
    curryLp p ν (-f) x = -curryLp p ν f x := by
  rw [curryLp_of_memLp hf.neg, curryLp_of_memLp hf, ← MemLp.toLp_neg]
  exact MemLp.toLp_congr _ _ (.of_forall fun _ ↦ Pi.neg_apply _ _)

/-- The class of the section of a scalar multiple is the scalar multiple of the class when the
section is in `Lᵖ(ν; E)`. -/
theorem curryLp_const_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (c : 𝕜)
    {f : α × β → E} {x : α} (hf : MemLp (fun y ↦ f (x, y)) p ν) :
    curryLp p ν (c • f) x = c • curryLp p ν f x := by
  rw [curryLp_of_memLp (hf.const_smul c), curryLp_of_memLp hf, ← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _ (.of_forall fun _ ↦ Pi.smul_apply _ _ _)

/-- The norm of the class of a section in `Lᵖ(ν; E)` is the `Lᵖ(ν)` seminorm of the section. -/
theorem eNorm_curryLp {f : α × β → E} {x : α} (h : MemLp (fun y ↦ f (x, y)) p ν) :
    ‖curryLp p ν f x‖ₑ = eLpNorm (fun y ↦ f (x, y)) p ν := by
  rw [curryLp_of_memLp h, Lp.eNorm_toLp]

omit [MeasurableSpace β] in
/-- The section at `x` of the indicator of `A ⊆ α × β` is the indicator of the section of `A`. -/
private theorem indicator_section (A : Set (α × β)) (c : E) (x : α) :
    (fun y ↦ A.indicator (fun _ ↦ c) (x, y)) = (Prod.mk x ⁻¹' A).indicator fun _ ↦ c :=
  funext fun _ ↦ (indicator_comp_right (Prod.mk x)).symm

/-- The section classes of `(x, y) ↦ 𝟙_s(x) g(y)` are `𝟙_s g`. -/
theorem curryLp_indicator_prod_univ {s : Set α} (g : Lp E p ν) :
    curryLp p ν ((s ×ˢ univ).indicator fun z ↦ g z.2) = s.indicator fun _ ↦ g := by
  ext1 x
  by_cases hx : x ∈ s
  · have hsec : (fun y ↦ (s ×ˢ univ).indicator (fun z : α × β ↦ g z.2) (x, y)) = g :=
      funext fun y ↦ by simp [hx]
    rw [indicator_of_mem hx, curryLp_of_memLp (hsec.symm ▸ Lp.memLp g)]
    simp only [hsec, Lp.toLp_coeFn]
  · rw [indicator_of_notMem hx, curryLp_congr (g := 0) (.of_forall fun y ↦ by simp [hx]),
      curryLp_zero, Pi.zero_apply]

variable [MeasurableSpace α] {μ : Measure α}

/-- Functions that agree almost everywhere for `μ ⊗ ν` have almost everywhere equal section
classes. -/
theorem curryLp_congr_ae [SFinite ν] {f g : α × β → E} (h : f =ᵐ[μ.prod ν] g) :
    curryLp p ν f =ᵐ[μ] curryLp p ν g := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx using curryLp_congr hx

end Basic

section Measurability

variable [MeasurableSpace α]

/-- For a measurable set `A ⊆ α × β` and a measurable set `S ⊆ β` of finite measure, the class in
`Lᵖ(ν; E)` of the indicator of the truncated section `A_x ∩ S` depends strongly measurably on `x`.
The sets `A` with this property contain the measurable rectangles and are closed under
complements and countable disjoint unions. -/
private theorem stronglyMeasurable_indicatorConstLp_inter [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {S : Set β} (hS : MeasurableSet S) (hνS : ν S ≠ ∞) (c : E) :
    ∀ (A : Set (α × β)) (hA : MeasurableSet A), StronglyMeasurable fun x : α ↦
      indicatorConstLp p ((measurable_prodMk_left (x := x) hA).inter hS)
        (ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)) c := by
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
  · -- The empty set has empty sections.
    convert (stronglyMeasurable_const (b := (0 : Lp E p ν))) using 1
    ext1 x
    rw [← indicatorConstLp_empty (μ := ν) (p := p) (c := c)]
    congr
    simp
  · -- A rectangle `B ×ˢ C` has sections `C` over `B` and `∅` elsewhere.
    rintro _ ⟨B, hB, C, hC, rfl⟩
    have hνC : ν (C ∩ S) ≠ ∞ := ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)
    convert (stronglyMeasurable_const (b := indicatorConstLp p (hC.inter hS) hνC c)).indicator
      (s := B) hB using 1
    ext1 x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      congr 1
      rw [mk_preimage_prod_right hx]
    · rw [indicator_of_notMem hx, ← indicatorConstLp_empty (μ := ν) (p := p) (c := c)]
      congr 1
      rw [mk_preimage_prod_right_eq_empty hx, empty_inter]
  · -- The section of a complement is the relative complement in `S` of the section.
    intro A hA hmeas
    convert (stronglyMeasurable_const (b := indicatorConstLp p hS hνS c)).sub hmeas using 1
    ext1 x
    rw [Pi.sub_apply, ← TauCeti.indicatorConstLp_sdiff hS
      ((measurable_prodMk_left (x := x) hA).inter hS) hνS inter_subset_right]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff]
    tauto
  · -- The section of a disjoint union is the disjoint union of the sections.
    intro A hd hA hmeas
    refine stronglyMeasurable_of_tendsto atTop
      (fun n ↦ Finset.stronglyMeasurable_sum (Finset.range n) fun i _ ↦ hmeas i)
      (tendsto_pi_nhds.2 fun x ↦ ?_)
    have hd' : Pairwise (Function.onFun Disjoint fun i ↦ Prod.mk x ⁻¹' A i ∩ S) :=
      fun i j hij ↦ ((hd hij).preimage _).mono inter_subset_left inter_subset_left
    have hU : (Prod.mk x ⁻¹' ⋃ i, A i) ∩ S = ⋃ i, (Prod.mk x ⁻¹' A i ∩ S) := by
      rw [preimage_iUnion, iUnion_inter]
    have hνU : ν (⋃ i, (Prod.mk x ⁻¹' A i ∩ S)) ≠ ∞ := by
      rw [← hU]
      exact ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)
    have hsum := (TauCeti.hasSum_indicatorConstLp hp
      (fun i ↦ (measurable_prodMk_left (hA i)).inter hS) hd' hνU c).tendsto_sum_nat
    -- The limits differ only in how the union of the sections is written, which is `hU`.
    simp only [Finset.sum_apply, hU]
    exact hsum

/-- The section classes of the indicator of a measurable set with finite sections are the
indicator classes of the sections. -/
theorem curryLp_indicator {A : Set (α × β)} (hA : MeasurableSet A) (c : E) {x : α}
    (hx : ν (Prod.mk x ⁻¹' A) ≠ ∞) :
    curryLp p ν (A.indicator fun _ ↦ c) x =
      indicatorConstLp p (measurable_prodMk_left hA) hx c := by
  have hmem : MemLp (fun y ↦ A.indicator (fun _ ↦ c) (x, y)) p ν := by
    rw [indicator_section]
    exact memLp_indicator_const p (measurable_prodMk_left hA).nullMeasurableSet c (.inr hx)
  refine Lp.ext ((coeFn_curryLp hmem).trans ?_)
  rw [indicator_section]
  exact indicatorConstLp_coeFn.symm

/-- For a σ-finite `ν` and a measurable set `A ⊆ α × β`, the section classes of the indicator
`𝟙_A c` form a strongly measurable function. Truncating the sections to the sets of an exhaustion
of `β` by sets of finite measure reduces this to the finite case. -/
private theorem stronglyMeasurable_curryLp_indicator [Fact (1 ≤ p)] (hp : p ≠ ∞) [SigmaFinite ν]
    {A : Set (α × β)} (hA : MeasurableSet A) (c : E) :
    StronglyMeasurable (curryLp p ν (A.indicator fun _ ↦ c)) := by
  by_cases hc : c = 0
  · rw [hc, indicator_zero, ← Pi.zero_def, curryLp_zero]
    exact stronglyMeasurable_zero
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set G := {x : α | ν (Prod.mk x ⁻¹' A) < ∞}
  have hG : MeasurableSet G := measurableSet_lt (measurable_measure_prodMk_left hA) measurable_const
  have hS (k : ℕ) : ν (spanningSets ν k) ≠ ∞ := (measure_spanningSets_lt_top ν k).ne
  refine stronglyMeasurable_of_tendsto atTop (fun k ↦
    (stronglyMeasurable_indicatorConstLp_inter hp (measurableSet_spanningSets ν k) (hS k) c A
      hA).indicator hG) (tendsto_pi_nhds.2 fun x ↦ ?_)
  by_cases hx : x ∈ G
  · simp only [indicator_of_mem hx]
    rw [curryLp_indicator hA c hx.ne]
    refine tendsto_indicatorConstLp_set hp ?_
    -- The truncations `A_x ∩ S k` exhaust the finite-measure section `A_x`.
    have hdiff (k : ℕ) : ((Prod.mk x ⁻¹' A) ∩ spanningSets ν k) ∆ (Prod.mk x ⁻¹' A) =
        (Prod.mk x ⁻¹' A) \ spanningSets ν k := by
      rw [symmDiff_of_le inter_subset_left]
      ext y
      simp only [Set.mem_sdiff, mem_inter_iff]
      tauto
    simp_rw [hdiff]
    have hlim := tendsto_measure_iInter_atTop (μ := ν)
      (s := fun k ↦ (Prod.mk x ⁻¹' A) \ spanningSets ν k)
      (fun k ↦ ((measurable_prodMk_left hA).diff
        (measurableSet_spanningSets ν k)).nullMeasurableSet)
      (fun i j hij ↦ sdiff_le_sdiff_left (monotone_spanningSets ν hij))
      ⟨0, ne_top_of_le_ne_top hx.ne (measure_mono sdiff_subset)⟩
    rwa [← sdiff_iUnion, iUnion_spanningSets, sdiff_univ, measure_empty] at hlim
  · simp only [indicator_of_notMem hx]
    rw [curryLp_of_not_memLp]
    · exact tendsto_const_nhds
    intro hmem
    have hx' : ν (Prod.mk x ⁻¹' A) = ∞ := not_lt_top_iff.1 hx
    rw [memLp_iff, indicator_section,
      eLpNorm_indicator_const (measurable_prodMk_left hA).nullMeasurableSet hp0 hp, hx',
      ENNReal.top_rpow_of_pos (by simp [ENNReal.toReal_pos hp0 hp]),
      ENNReal.mul_top (by simpa using hc)] at hmem
    exact lt_irrefl _ hmem

variable {μ : Measure α}

/-- The `Lᵖ(ν)` distance of the section classes of two functions in `Lᵖ(μ ⊗ ν; E)` is, at almost
every point, the `Lᵖ(ν)` seminorm of the section of their difference. -/
private theorem ae_dist_curryLp [Fact (1 ≤ p)] [SFinite ν] {f g : α × β → E}
    (hf : MemLp f p (μ.prod ν)) (hg : MemLp g p (μ.prod ν)) :
    ∀ᵐ x ∂μ, dist (curryLp p ν f x) (curryLp p ν g x) =
      (eLpNorm (fun y ↦ (f - g) (x, y)) p ν).toReal := by
  filter_upwards [hf.ae_memLp_prod_right, hg.ae_memLp_prod_right] with x hfx hgx
  rw [dist_eq_norm, ← curryLp_sub hfx hgx, ← toReal_eNorm, eNorm_curryLp (hfx.sub hgx)]

/-- The functions in `Lᵖ(μ ⊗ ν; E)` whose section classes are almost everywhere strongly
measurable form a closed set: convergence in `Lᵖ(μ ⊗ ν; E)` is convergence in `μ`-measure of
the section classes, by Tonelli's theorem, hence almost everywhere along a subsequence. -/
private theorem isClosed_setOf_aestronglyMeasurable_curryLp [Fact (1 ≤ p)] [SFinite ν] :
    IsClosed {F : Lp E p (μ.prod ν) | AEStronglyMeasurable (curryLp p ν ⇑F) μ} := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  refine IsSeqClosed.isClosed fun F F₀ hF hlim ↦ ?_
  set g : ℕ → α → ℝ≥0∞ := fun n x ↦ eLpNorm (fun y ↦ (⇑(F n) - ⇑F₀) (x, y)) p ν
  have hsub (n : ℕ) : MemLp (⇑(F n) - ⇑F₀) p (μ.prod ν) := (Lp.memLp (F n)).sub (Lp.memLp F₀)
  have hg (n : ℕ) : AEStronglyMeasurable (g n) μ :=
    (hsub n).aestronglyMeasurable.eLpNorm_prod_right
  have hnorm (n : ℕ) :
      eLpNorm (fun x ↦ (g n x).toReal) p μ = eLpNorm (⇑(F n) - ⇑F₀) p (μ.prod ν) := by
    rw [TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm (hsub n).aestronglyMeasurable]
    refine eLpNorm_congr_eNorm_ae (hg n).aemeasurable.ennreal_toReal.aestronglyMeasurable (hg n) ?_
    filter_upwards [(hsub n).ae_memLp_prod_right] with x hx
    rw [Real.eNorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne, eNorm_eq_self]
  have hr : TendstoInMeasure μ (fun n x ↦ (g n x).toReal) atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 (by
      simpa only [sub_zero, hnorm] using (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim)
  obtain ⟨ns, -, hns⟩ := hr.exists_seq_tendsto_ae
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun k ↦ hF (ns k)) ?_
  filter_upwards [hns, ae_all_iff.2 fun n ↦ ae_dist_curryLp (Lp.memLp (F n)) (Lp.memLp F₀)]
    with x hx hdist
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [hdist]
  exact hx

/-- **Measurability of the section map.** For `f ∈ Lᵖ(μ ⊗ ν; E)` with `p` finite and `ν`
σ-finite, the section classes `x ↦ [f (x, ·)]` form an almost everywhere strongly measurable
`Lᵖ(ν; E)`-valued function. -/
theorem MemLp.aestronglyMeasurable_curryLp [Fact (1 ≤ p)] (hp : p ≠ ∞) [SigmaFinite ν]
    {f : α × β → E} (hf : MemLp f p (μ.prod ν)) :
    AEStronglyMeasurable (curryLp p ν f) μ := by
  refine MemLp.induction hp (fun f ↦ AEStronglyMeasurable (curryLp p ν f) μ)
    (fun c A hA _ ↦ (stronglyMeasurable_curryLp_indicator hp hA c).aestronglyMeasurable)
    (fun f g _ hf hg hf' hg' ↦ (hf'.add hg').congr ?_)
    isClosed_setOf_aestronglyMeasurable_curryLp
    (fun f g hfg _ hf ↦ hf.congr (curryLp_congr_ae hfg)) hf
  filter_upwards [hf.ae_memLp_prod_right, hg.ae_memLp_prod_right] with x hfx hgx
  exact (curryLp_add hfx hgx).symm

/-- **Iterated norm of the section map.** For `f ∈ Lᵖ(μ ⊗ ν; E)`, the `Lᵖ(μ)` seminorm of the
section classes `x ↦ [f (x, ·)]` is the `Lᵖ(μ ⊗ ν)` seminorm of `f`, provided the section
classes are almost everywhere strongly measurable. -/
theorem MemLp.eLpNorm_curryLp [Fact (1 ≤ p)] [SFinite ν] {f : α × β → E} (hf : MemLp f p (μ.prod ν))
    (hmeas : AEStronglyMeasurable (curryLp p ν f) μ) :
    eLpNorm (curryLp p ν f) p μ = eLpNorm f p (μ.prod ν) := by
  rw [TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm hf.aestronglyMeasurable]
  refine eLpNorm_congr_eNorm_ae hmeas hf.aestronglyMeasurable.eLpNorm_prod_right ?_
  filter_upwards [hf.ae_memLp_prod_right] with x hx
  rw [eNorm_curryLp hx, eNorm_eq_self]

/-- For `f ∈ Lᵖ(μ ⊗ ν; E)` with `p` finite and `ν` σ-finite, the section classes form an element
of `Lᵖ(μ; Lᵖ(ν; E))`. -/
theorem MemLp.memLp_curryLp [Fact (1 ≤ p)] (hp : p ≠ ∞) [SigmaFinite ν] {f : α × β → E}
    (hf : MemLp f p (μ.prod ν)) : MemLp (curryLp p ν f) p μ := by
  rw [memLp_iff, hf.eLpNorm_curryLp (hf.aestronglyMeasurable_curryLp hp)]
  exact hf

end Measurability

end CurryLp

namespace Lp

variable (𝕜 : Type*) {α β : Type*} (E : Type*) [MeasurableSpace α] [MeasurableSpace β]
  [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (μ : Measure α)
  (ν : Measure β)
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [SigmaFinite ν]

/-- **Fubini's theorem for Bochner spaces**, isometric part: for a finite exponent `p` and a
σ-finite `ν`, sending `F ∈ Lᵖ(μ ⊗ ν; E)` to the classes of its sections `x ↦ [F (x, ·)]` is a
linear isometry `Lᵖ(μ ⊗ ν; E) → Lᵖ(μ; Lᵖ(ν; E))`. -/
def curryₗᵢ (hp : p ≠ ∞) : Lp E p (μ.prod ν) →ₗᵢ[𝕜] Lp (Lp E p ν) p μ where
  toFun F := ((Lp.memLp F).memLp_curryLp hp).toLp _
  map_add' F G := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [curryLp_congr_ae (Lp.coeFn_add F G), (Lp.memLp F).ae_memLp_prod_right,
      (Lp.memLp G).ae_memLp_prod_right] with x hx hF hG
    rw [hx, Pi.add_apply, ← curryLp_add hF hG]
  map_smul' c F := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [curryLp_congr_ae (Lp.coeFn_smul c F), (Lp.memLp F).ae_memLp_prod_right]
      with x hx hF
    rw [hx, Pi.smul_apply, ← curryLp_const_smul c hF]
  norm_map' F := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      (Lp.memLp F).eLpNorm_curryLp ((Lp.memLp F).aestronglyMeasurable_curryLp hp), Lp.norm_def]

variable {E μ ν}

/-- The image of `F` under `Lp.curryₗᵢ` is represented by the classes of the sections of `F`. -/
theorem coeFn_curryₗᵢ (hp : p ≠ ∞) (F : Lp E p (μ.prod ν)) :
    curryₗᵢ 𝕜 E μ ν hp F =ᵐ[μ] curryLp p ν F :=
  MemLp.coeFn_toLp ((Lp.memLp F).memLp_curryLp hp)

/-- **Section formula.** For almost every `x`, the value of `Lp.curryₗᵢ F` at `x` is represented
by the section `y ↦ F (x, y)`. -/
theorem ae_ae_curryₗᵢ_apply (hp : p ≠ ∞) (F : Lp E p (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, curryₗᵢ 𝕜 E μ ν hp F x y = F (x, y) := by
  filter_upwards [coeFn_curryₗᵢ 𝕜 hp F, (Lp.memLp F).ae_memLp_prod_right] with x hx hFx
  rw [hx]
  exact coeFn_curryLp hFx

/-- **Rectangle formula.** `Lp.curryₗᵢ` sends the class of the indicator of a rectangle `s ×ˢ t`
with value `c` to the class of the indicator of `s` whose value is the class of the indicator of
`t` with value `c`. -/
theorem curryₗᵢ_indicatorConstLp_prod (hp : p ≠ ∞) {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞) (c : E) :
    curryₗᵢ 𝕜 E μ ν hp (indicatorConstLp p (hs.prod ht)
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) c) =
      indicatorConstLp p hs hμs (indicatorConstLp p ht hνt c) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_curryₗᵢ (E := E) (μ := μ) (ν := ν) 𝕜 hp _, curryLp_congr_ae
      (indicatorConstLp_coeFn (p := p) (μ := μ.prod ν) (hs := hs.prod ht) (c := c)),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := indicatorConstLp p ht hνt c)]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ s
  · have hsec : Prod.mk x ⁻¹' s ×ˢ t = t := mk_preimage_prod_right hx
    rw [indicator_of_mem hx, curryLp_indicator (hs.prod ht) c (by rwa [hsec])]
    simp only [hsec]
  · have hsec : Prod.mk x ⁻¹' s ×ˢ t = ∅ := mk_preimage_prod_right_eq_empty hx
    rw [indicator_of_notMem hx, curryLp_indicator (hs.prod ht) c (by simp [hsec]),
      ← indicatorConstLp_empty (μ := ν) (p := p) (c := c)]
    simp only [hsec]

/-- Every indicator class `𝟙_s g` with `g ∈ Lᵖ(ν; E)` is in the image of `Lp.curryₗᵢ`: it is the
image of the class of `(x, y) ↦ 𝟙_s(x) g(y)`. -/
private theorem indicatorConstLp_mem_range_curryₗᵢ (hp : p ≠ ∞) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (g : Lp E p ν) :
    indicatorConstLp p hs hμs g ∈ range (curryₗᵢ 𝕜 E μ ν hp) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set f := (s ×ˢ univ).indicator fun z : α × β ↦ g z.2
  have hf : AEStronglyMeasurable f (μ.prod ν) :=
    ((Lp.stronglyMeasurable g).comp_measurable measurable_snd).indicator
      (hs.prod MeasurableSet.univ) |>.aestronglyMeasurable
  have hmem : MemLp f p (μ.prod ν) := by
    -- The section seminorms are `𝟙_s ‖g‖`, by Tonelli's theorem.
    have hsec : (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) =
        s.indicator fun _ ↦ eLpNorm g p ν := by
      ext1 x
      by_cases hx : x ∈ s <;> simp [f, hx]
    rw [memLp_iff, TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm hf, hsec,
      eLpNorm_indicator_const hs.nullMeasurableSet hp0 hp, eNorm_eq_self]
    exact ENNReal.mul_lt_top (Lp.eLpNorm_lt_top g)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hμs)
  refine ⟨hmem.toLp f, Lp.ext ?_⟩
  filter_upwards [coeFn_curryₗᵢ 𝕜 hp (hmem.toLp f), curryLp_congr_ae hmem.coeFn_toLp,
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := g)] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, curryLp_indicator_prod_univ]

/-- `Lp.curryₗᵢ` is onto when `E` is complete. -/
theorem curryₗᵢ_surjective [CompleteSpace E] (hp : p ≠ ∞) :
    Function.Surjective (curryₗᵢ 𝕜 E μ ν hp) := by
  intro G
  refine Lp.induction hp (fun G ↦ G ∈ range (curryₗᵢ 𝕜 E μ ν hp))
    (fun c s hs hμs ↦ ?_) (fun f g hf hg _ hF hG ↦ ?_)
    (curryₗᵢ 𝕜 E μ ν hp).isometry.isClosedEmbedding.isClosed_range G
  · rw [Lp.simpleFunc.coe_indicatorConst]
    exact indicatorConstLp_mem_range_curryₗᵢ 𝕜 hp hs hμs.ne c
  · obtain ⟨F, hF⟩ := hF
    obtain ⟨G, hG⟩ := hG
    exact ⟨F + G, by rw [map_add, hF, hG]⟩

variable (E μ ν) in
/-- **Fubini's theorem for Bochner spaces.** For a finite exponent `1 ≤ p < ∞`, a σ-finite `ν`
and a complete `E`, sending `F ∈ Lᵖ(μ ⊗ ν; E)` to the classes of its sections
`x ↦ [F (x, ·)]` is a linear isometric equivalence `Lᵖ(μ ⊗ ν; E) ≃ Lᵖ(μ; Lᵖ(ν; E))`. -/
def curryEquiv [CompleteSpace E] (hp : p ≠ ∞) : Lp E p (μ.prod ν) ≃ₗᵢ[𝕜] Lp (Lp E p ν) p μ :=
  LinearIsometryEquiv.ofSurjective (curryₗᵢ 𝕜 E μ ν hp) (curryₗᵢ_surjective 𝕜 hp)

/-- `Lp.curryEquiv` acts as `Lp.curryₗᵢ`. -/
@[simp]
theorem curryEquiv_apply [CompleteSpace E] (hp : p ≠ ∞) (F : Lp E p (μ.prod ν)) :
    curryEquiv 𝕜 E μ ν hp F = curryₗᵢ 𝕜 E μ ν hp F :=
  (rfl)

/-- **Section formula for the inverse.** For `G ∈ Lᵖ(μ; Lᵖ(ν; E))`, for almost every `x` the
value `G x` is represented by the section `y ↦ (Lp.curryEquiv).symm G (x, y)`. -/
theorem ae_ae_curryEquiv_symm_apply [CompleteSpace E] (hp : p ≠ ∞) (G : Lp (Lp E p ν) p μ) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, G x y = (curryEquiv 𝕜 E μ ν hp).symm G (x, y) := by
  have h := ae_ae_curryₗᵢ_apply 𝕜 hp ((curryEquiv 𝕜 E μ ν hp).symm G)
  rwa [← curryEquiv_apply, LinearIsometryEquiv.apply_symm_apply] at h

end Lp

end MeasureTheory
