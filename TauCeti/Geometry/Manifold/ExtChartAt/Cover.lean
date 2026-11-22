/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Order.Disjointed
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Finite open chart covers and disjointed cover integrals

`TauCeti.ChartCover I s` packages a finite cover of `s ⊆ M` by open subsets of preferred extended
chart sources, with disjointed chart-measurable pieces (`piece`), compact-set choice (`choose`),
chart prepending (`cons`), Bochner cover integrals (`integral`, `integral_cons`, `integral_eq`,
`integral_eq_integral_of_ae_support`), overlap Jacobian invariance
(`extChartAt_coordChange_setIntegral_and_integrableOn`), and `integrable_of_open_cover_extChartAt`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A finite open cover of `s ⊆ M` by open sets inside preferred extended chart sources. -/
structure ChartCover (I : ModelWithCorners 𝕜 E H) (s : Set M) where
  /-- Number of charts in the cover. -/
  n : ℕ
  /-- Base points of the preferred extended charts. -/
  center : Fin n → M
  /-- Open sets covering `s`, each inside its preferred extended chart source. -/
  domain : Fin n → Set M
  /-- Each covering set is open. -/
  isOpen_domain : ∀ i, IsOpen (domain i)
  /-- Each covering set lies inside its preferred extended chart source. -/
  domain_subset : ∀ i, domain i ⊆ (extChartAt I (center i)).source
  /-- The open sets cover `s`. -/
  covers : s ⊆ ⋃ i, domain i

namespace ChartCover

/-- Choose a finite open chart cover of a compact subset when `H` is locally compact. -/
def choose (I : ModelWithCorners 𝕜 E H) [LocallyCompactSpace H] {s : Set M} (hc : IsCompact s) :
    ChartCover I s :=
  let h := exists_finite_precompact_chart_cover (I := I) hc
  let hp := h.choose_spec.choose_spec.choose_spec.choose_spec
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    fun i ↦ (hp.1 i).1, fun i ↦ (hp.1 i).2.1, hp.2⟩

/-- The `i`-th disjointed piece of a chart cover. -/
def piece {s : Set M} (c : ChartCover I s) (i : Fin c.n) : Set M := disjointed c.domain i

/-- The `i`-th disjointed piece equals `disjointed c.domain i`. -/
theorem piece_eq_disjointed {s : Set M} (c : ChartCover I s) (i : Fin c.n) :
    c.piece i = disjointed c.domain i := by rw [piece]

/-- Each disjointed piece lies inside its preferred extended chart source. -/
theorem piece_subset {s : Set M} (c : ChartCover I s) (i : Fin c.n) :
    c.piece i ⊆ (extChartAt I (c.center i)).source :=
  (disjointed_subset c.domain i).trans (c.domain_subset i)

/-- The disjointed pieces still cover `s`. -/
theorem piece_covers {s : Set M} (c : ChartCover I s) : s ⊆ ⋃ i, c.piece i := by
  simpa only [piece, iUnion_disjointed] using c.covers

/-- Distinct disjointed pieces are pairwise disjoint. -/
theorem pairwise_disjoint {s : Set M} (c : ChartCover I s) :
    Pairwise fun i j ↦ Disjoint (c.piece i) (c.piece j) := disjoint_disjointed c.domain

/-- Prepend `(x₀, (extChartAt I x₀).source)` as the first chart of a chart cover. -/
def cons {s : Set M} (c : ChartCover I s) (x₀ : M) : ChartCover I s :=
  ⟨c.n + 1, Fin.cons x₀ c.center, Fin.cons (extChartAt I x₀).source c.domain,
    Fin.cases (isOpen_extChartAt_source x₀) c.isOpen_domain, Fin.cases Subset.rfl c.domain_subset,
    c.covers.trans (iUnion_subset fun i ↦ subset_iUnion_of_subset i.succ (by simp))⟩

section Measurable

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Every disjointed piece of a chart cover is chart measurable. -/
theorem isChartMeasurable_piece {s : Set M} (c : ChartCover I s) (i : Fin c.n) :
    IsChartMeasurable I (c.piece i) := by
  rw [piece, disjointed_apply, Finset.sup_set_eq_biUnion]
  exact (c.isOpen_domain i).isChartMeasurable.diff
    (isOpen_biUnion fun j _ ↦ c.isOpen_domain j).isChartMeasurable

/-- The coordinate image of each disjointed piece in its preferred chart is measurable. -/
theorem measurableSet_image_piece {s : Set M} (c : ChartCover I s) (i : Fin c.n) :
    MeasurableSet ((extChartAt I (c.center i)) '' c.piece i) :=
  (c.isChartMeasurable_piece i).image_extChartAt (c.center i) (c.piece_subset i)

end Measurable

section Integral

variable [MeasurableSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Sum of Bochner set integrals of `F` over the coordinate images of the disjointed pieces. -/
def integral {s : Set M} (c : ChartCover I s) (F : M → E → G) (ν : Measure E) : G :=
  ∑ i, ∫ y in (extChartAt I (c.center i)) '' c.piece i, F (c.center i) y ∂ν

/-- Explicit sum formula for a cover integral. -/
theorem integral_eq_sum {s : Set M} (c : ChartCover I s) (F : M → E → G) (ν : Measure E) :
    c.integral F ν = ∑ i, ∫ y in (extChartAt I (c.center i)) '' c.piece i, F (c.center i) y ∂ν := by
  rw [integral]

/-- Prepending `x₀` splits the cover integral into the target integral at `x₀` plus the integrals
over the remaining pieces outside `(extChartAt I x₀).source`. -/
theorem integral_cons {s : Set M} (c : ChartCover I s) (x₀ : M) (F : M → E → G) (ν : Measure E) :
    (c.cons x₀).integral F ν = (∫ y in (extChartAt I x₀).target, F x₀ y ∂ν) +
      ∑ i : Fin c.n, ∫ y in (extChartAt I (c.center i)) '' (c.piece i \ (extChartAt I x₀).source),
        F (c.center i) y ∂ν := by
  unfold integral piece cons; dsimp only; rw [Fin.sum_univ_succ]; congr 1
  · rw [Fin.cons_zero, disjointed_cons_zero, (extChartAt I x₀).image_source_eq_target]
  · simp only [Fin.cons_succ, disjointed_cons_succ]

/-- The cover integral of the zero chart family vanishes. -/
@[simp] theorem integral_zero {s : Set M} (c : ChartCover I s) (ν : Measure E) :
    c.integral (0 : M → E → G) ν = 0 := by simp [integral]

/-- Constant scalar multiplication pulls out of a cover integral. -/
theorem integral_smul {s : Set M} (c : ChartCover I s) (r : ℝ) (F : M → E → G) (ν : Measure E) :
    c.integral (fun α y ↦ r • F α y) ν = r • c.integral F ν := by
  unfold integral; simp_rw [MeasureTheory.integral_smul, Finset.smul_sum]

/-- Cover integrals are additive when both integrands are integrable on each coordinate piece. -/
theorem integral_add {s : Set M} (c : ChartCover I s) {F F' : M → E → G} (ν : Measure E)
    (hF : ∀ i, IntegrableOn (F (c.center i)) ((extChartAt I (c.center i)) '' c.piece i) ν)
    (hF' : ∀ i, IntegrableOn (F' (c.center i)) ((extChartAt I (c.center i)) '' c.piece i) ν) :
    c.integral (fun α y ↦ F α y + F' α y) ν = c.integral F ν + c.integral F' ν := by
  unfold integral; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ MeasureTheory.integral_add (hF i) (hF' i)

/-- Equal compact sets yield the same chosen cover integral. -/
theorem integral_choose_congr [LocallyCompactSpace H] {s t : Set M} (hs : IsCompact s)
    (ht : IsCompact t) (hst : s = t) (F : M → E → G) (ν : Measure E) :
    (ChartCover.choose I hs).integral F ν = (ChartCover.choose I ht).integral F ν := by
  subst hst; rfl

variable [OpensMeasurableSpace E]

/-- Refine a set integral in chart `α` over a chart-measurable `u` into the sum over `u ∩ c.piece i`
when `F α` vanishes at chart images of points outside `s`. -/
theorem setIntegral_eq_sum_inter_piece {s : Set M} (c : ChartCover I s) (F : M → E → G)
    (ν : Measure E) (α : M) {u : Set M} (hu : IsChartMeasurable I u)
    (hus : u ⊆ (extChartAt I α).source) (hint : IntegrableOn (F α) ((extChartAt I α) '' u) ν)
    (hzero : ∀ x ∈ u, x ∉ s → F α (extChartAt I α x) = 0) :
    (∫ y in (extChartAt I α) '' u, F α y ∂ν) =
      ∑ i, ∫ y in (extChartAt I α) '' (u ∩ c.piece i), F α y ∂ν := by
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hu.image_extChartAt α hus)
    (iUnion_subset fun _ ↦ image_mono inter_subset_left) ?_).trans (integral_iUnion_fintype
      (fun i ↦ (hu.inter (c.isChartMeasurable_piece i)).image_extChartAt α
        (inter_subset_left.trans hus))
      (fun _ _ hij ↦ ((c.pairwise_disjoint hij).mono inter_subset_right inter_subset_right).image
        (extChartAt I α).injOn (inter_subset_left.trans hus) (inter_subset_left.trans hus))
      fun _ ↦ hint.mono_set (image_mono inter_subset_left))
  rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
  exact hzero x hx fun hxs ↦ let ⟨i, hi⟩ := mem_iUnion.mp (c.piece_covers hxs)
    hn (mem_iUnion.mpr ⟨i, mem_image_of_mem _ ⟨hx, hi⟩⟩)

/-- Two chart covers yield the same cover integral under overlap set-integral invariance. -/
theorem integral_eq {s t : Set M} (c : ChartCover I s) (d : ChartCover I t) (F : M → E → G)
    (ν : Measure E)
    (hintc : ∀ i, IntegrableOn (F (c.center i)) ((extChartAt I (c.center i)) '' c.piece i) ν)
    (hintd : ∀ j, IntegrableOn (F (d.center j)) ((extChartAt I (d.center j)) '' d.piece j) ν)
    (hzeroc : ∀ i, ∀ x ∈ c.piece i, x ∉ t → F (c.center i) (extChartAt I (c.center i) x) = 0)
    (hzerod : ∀ j, ∀ x ∈ d.piece j, x ∉ s → F (d.center j) (extChartAt I (d.center j) x) = 0)
    (hchange : ∀ (i : Fin c.n) (j : Fin d.n),
      (∫ y in (extChartAt I (c.center i)) '' (c.piece i ∩ d.piece j), F (c.center i) y ∂ν) =
        ∫ y in (extChartAt I (d.center j)) '' (c.piece i ∩ d.piece j), F (d.center j) y ∂ν) :
    c.integral F ν = d.integral F ν := by
  unfold integral
  trans ∑ i, ∑ j, ∫ y in (extChartAt I (c.center i)) '' (c.piece i ∩ d.piece j), F (c.center i) y ∂ν
  · exact Finset.sum_congr rfl fun i _ ↦ d.setIntegral_eq_sum_inter_piece F ν (c.center i)
      (c.isChartMeasurable_piece i) (c.piece_subset i) (hintc i) (hzeroc i)
  · rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [c.setIntegral_eq_sum_inter_piece F ν (d.center j) (d.isChartMeasurable_piece j)
      (d.piece_subset j) (hintd j) (hzerod j)]
    exact Finset.sum_congr rfl fun i _ ↦ by simpa only [inter_comm] using hchange i j

/-- A cover integral reduces to `∫ y, F α y ∂ν` when every cover piece vanishes a.e. outside the
overlap with `α` and set integrals are overlap-invariant. -/
theorem integral_eq_integral_of_ae_support {s : Set M} (c : ChartCover I s) (F : M → E → G)
    (ν : Measure E) (α : M) (hint : IntegrableOn (F α) (extChartAt I α).target ν)
    (hzero_s : ∀ x ∈ (extChartAt I α).source, x ∉ s → F α (extChartAt I α x) = 0)
    (hzero_compl : ∀ y ∉ (extChartAt I α).target, F α y = 0)
    (hα : ∀ i, ∀ᵐ y ∂ν, y ∉ (extChartAt I (c.center i)) ''
      ((extChartAt I (c.center i)).source ∩ (extChartAt I α).source) → F (c.center i) y = 0)
    (hchange : ∀ i,
      (∫ y in (extChartAt I (c.center i)) '' (c.piece i ∩ (extChartAt I α).source),
          F (c.center i) y ∂ν) =
        ∫ y in (extChartAt I α) '' (c.piece i ∩ (extChartAt I α).source), F α y ∂ν) :
    c.integral F ν = ∫ y, F α y ∂ν := by
  let e := extChartAt I α; rw [integral]
  trans ∑ i, ∫ y in e '' (c.piece i ∩ e.source), F α y ∂ν
  · refine Finset.sum_congr rfl fun i _ ↦ (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := ν)
      (c.measurableSet_image_piece i).nullMeasurableSet (image_mono inter_subset_left) ?_).trans
      (hchange i)
    filter_upwards [hα i] with y hy h; obtain ⟨⟨x, hx, rfl⟩, hns⟩ := h
    exact hy fun ⟨z, hz, he⟩ ↦ hns (mem_image_of_mem _
      ⟨hx, ((extChartAt I (c.center i)).injOn (c.piece_subset i hx) hz.1 he.symm) ▸ hz.2⟩)
  · have he := c.setIntegral_eq_sum_inter_piece F ν α (isOpen_extChartAt_source α).isChartMeasurable
      Subset.rfl (by simpa only [e, (extChartAt I α).image_source_eq_target] using hint) hzero_s
    have he' : (∑ i, ∫ y in e '' (c.piece i ∩ e.source), F α y ∂ν) =
        ∫ y in e '' e.source, F α y ∂ν := by simpa only [inter_comm] using he.symm
    rw [he', e.image_source_eq_target]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero_compl

end Integral

end ChartCover

/-- Global integrability of `F α` from local integrability on an open cover of a compact support
bound `K` and overlap transfer of integrability. -/
theorem integrable_of_open_cover_extChartAt [MeasurableSpace E] {G : Type*} [NormedAddCommGroup G]
    {J : Type*} {K : Set M} (hK : IsCompact K) (F : M → E → G) (ν : Measure E)
    (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i)) (hcover : K ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (F (β i)) ((extChartAt I (β i)) '' u i) ν) (α : M)
    (hsupp : Function.support (F α) ⊆ (extChartAt I α) '' ((extChartAt I α).source ∩ K))
    (hchange : ∀ i,
      IntegrableOn (F (β i)) ((extChartAt I (β i)) '' ((extChartAt I α).source ∩ u i)) ν →
      IntegrableOn (F α) ((extChartAt I α) '' ((extChartAt I α).source ∩ u i)) ν) :
    Integrable (F α) ν := by
  classical obtain ⟨t, ht⟩ := hK.elim_finite_subcover u hu hcover
  refine (integrableOn_iff_integrable_of_support_subset fun y hy ↦ ?_).mp
    (integrableOn_finite_iUnion.mpr fun i : t ↦
      hchange i ((hlocal i).mono_set (image_mono inter_subset_right)))
  obtain ⟨x, ⟨hxα, hxK⟩, rfl⟩ := hsupp hy; obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hxK)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, mem_image_of_mem _ ⟨hxα, hxi⟩⟩

/-- On a measurable chart-overlap subset `s`, if `fα` and `fβ` satisfy the absolute Jacobian
change-of-variables law on `s`, then their Haar set integrals and integrability on the coordinate
images of `s` agree. -/
theorem extChartAt_coordChange_setIntegral_and_integrableOn {E H M G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (α β : M) {s : Set M} (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s)) (fα fβ : E → G)
    (hcoef : ∀ x ∈ s,
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
        (extChartAt I α x)).toLinearMap.det| • fβ (extChartAt I β x) = fα (extChartAt I α x))
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    ((∫ y in (extChartAt I α) '' s, fα y ∂ν) = ∫ y in (extChartAt I β) '' s, fβ y ∂ν) ∧
      (IntegrableOn fα ((extChartAt I α) '' s) ν ↔ IntegrableOn fβ ((extChartAt I β) '' s) ν) := by
  have himage := extChartAt_coordChange_image α β hsub
  have hinj := injOn_extChartAt_coordChange α β hsub
  have hderiv := hasFDerivWithinAt_extChartAt_coordChange α β hsub
  have hcoef' : ∀ y ∈ (extChartAt I α) '' s,
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I) y).toLinearMap.det| •
        fβ (((extChartAt I α).symm ≫ extChartAt I β) y) = fα y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [PartialEquiv.trans_apply, (extChartAt I α).left_inv (hsub hx).1]
    exact hcoef x hx
  exact ⟨by rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul ν hs hderiv hinj]
            exact setIntegral_congr_fun hs fun y hy ↦ (hcoef' y hy).symm,
    by rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul ν hs hderiv hinj]
       exact (integrableOn_congr_fun hcoef' hs).symm⟩

end TauCeti
