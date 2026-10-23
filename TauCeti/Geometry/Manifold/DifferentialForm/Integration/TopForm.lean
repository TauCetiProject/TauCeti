/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basis
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Linear
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OrientationLift
import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Disjointed

/-!
# Integration of compactly supported top forms

A finite open chart cover is disjointed into Borel coordinate pieces. Integration over these
pieces requires no Hausdorff assumption or measurable structure on the manifold. Integrability
is expressed in every chart and every model basis, independently of a cover or an orientation.

For the mathematical construction of integration on oriented manifolds, see J. M. Lee,
*Introduction to Smooth Manifolds*, Chapter 16. Here finite disjoint Borel chart pieces provide
the localization, and their common refinement proves independence of the chosen cover.
-/

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {k : ℕ}

/-- A compactly supported top form is integrable when its unsigned coefficients are integrable
in every preferred chart and every model basis. The model uses its Borel measurable structure. -/
public def IntegrableTopForm (φ : RoughForm I M ℝ k) : Prop := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ∧
    Nonempty (Module.Basis (Fin k) ℝ E) ∧
    ∀ (b : Module.Basis (Fin k) ℝ E) (α : M),
      Integrable (φ.signedInChartAt b α (fun _ ↦ 1)) b.addHaar

private structure ChartCover (s : Set M) where
  n : ℕ
  center : Fin n → M
  domain : Fin n → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  domain_subset : ∀ i, domain i ⊆ (extChartAt I (center i)).source
  covers : s ⊆ ⋃ i, domain i

private def chooseChartCover [ProperSpace E] (s : Set M) (hc : IsCompact s) :
    ChartCover (I := I) s := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let h := exists_finite_precompact_chart_cover (I := I) hc
  let n := h.choose
  let α := h.choose_spec.choose
  let u := h.choose_spec.choose_spec.choose
  have hp := h.choose_spec.choose_spec.choose_spec.choose_spec
  exact ⟨n, α, u, fun i ↦ (hp.1 i).1, fun i ↦ (hp.1 i).2.1, hp.2⟩

private def ChartCover.piece {s : Set M} (c : ChartCover (I := I) s) (i : Fin c.n) : Set M :=
  disjointed c.domain i

private theorem ChartCover.piece_subset {s : Set M} (c : ChartCover (I := I) s)
    (i : Fin c.n) : c.piece i ⊆ (extChartAt I (c.center i)).source :=
  (disjointed_subset c.domain i).trans (c.domain_subset i)

private theorem ChartCover.piece_covers {s : Set M} (c : ChartCover (I := I) s) :
    s ⊆ ⋃ i, c.piece i := by
  simpa only [ChartCover.piece, iUnion_disjointed] using c.covers

private theorem ChartCover.pairwise_disjoint {s : Set M} (c : ChartCover (I := I) s) :
    Pairwise (fun i j ↦ Disjoint (c.piece i) (c.piece j)) := disjoint_disjointed c.domain

section WithMeasure

variable [MeasurableSpace E] [BorelSpace E]

private theorem ChartCover.measurableSet_image_piece {s : Set M} (c : ChartCover (I := I) s)
    (i : Fin c.n) : MeasurableSet ((extChartAt I (c.center i)) '' c.piece i) := by
  rw [ChartCover.piece, disjointed_apply]
  have ho : IsOpen ((Finset.Iio i).sup c.domain) := by
    rw [Finset.sup_set_eq_biUnion]
    exact isOpen_biUnion fun j _ ↦ c.isOpen_domain j
  exact ((c.isOpen_domain i).isChartMeasurable.diff ho.isChartMeasurable).image_extChartAt
    (c.center i) (Set.sdiff_subset.trans (c.domain_subset i))

private theorem ChartCover.isChartMeasurable_piece {s : Set M} (c : ChartCover (I := I) s)
    (i : Fin c.n) : IsChartMeasurable I (c.piece i) := by
  rw [ChartCover.piece, disjointed_apply]
  have ho : IsOpen ((Finset.Iio i).sup c.domain) := by
    rw [Finset.sup_set_eq_biUnion]
    exact isOpen_biUnion fun j _ ↦ c.isOpen_domain j
  exact (c.isOpen_domain i).isChartMeasurable.diff ho.isChartMeasurable

/-- The coordinate characterization of integrability, with any Borel measurable structure on
the model. Neither a chart cover nor an orientation occurs in this condition. -/
public theorem integrableTopForm_iff (φ : RoughForm I M ℝ k) :
    IntegrableTopForm φ ↔ IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ∧
    Nonempty (Module.Basis (Fin k) ℝ E) ∧
      ∀ (b : Module.Basis (Fin k) ℝ E) (α : M),
        Integrable (φ.signedInChartAt b α (fun _ ↦ 1)) b.addHaar := by
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  rfl

section RoughIntegrability

variable [FiniteDimensional ℝ E] [IsManifold I 1 M] {φ : RoughForm I M ℝ k}

/-- Integrability on an open chart cover introduces the intrinsic predicate for rough
forms. One model basis suffices, and neither form continuity nor an orientation is required. -/
public theorem RoughForm.integrableTopForm_of_open_cover {J : Type*}
    (φ : RoughForm I M ℝ k) (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (b : Module.Basis (Fin k) ℝ E)
    (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i))
    (hsource : ∀ i, u i ⊆ (chartAt H (β i)).source)
    (hcover : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (φ.signedInChartAt b (β i) (fun _ ↦ 1))
      ((extChartAt I (β i)) '' u i) b.addHaar) : IntegrableTopForm φ := by
  classical
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover u hu hcover
  have hcover' : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ ⋃ i : t, u i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hcoef (α : M) : Integrable (φ.signedInChartAt b α (fun _ ↦ 1)) b.addHaar := by
    let s : t → Set M := fun i ↦ (extChartAt I α).source ∩ u i
    let A : t → Set E := fun i ↦ (extChartAt I α) '' s i
    have hA : ∀ i, MeasurableSet (A i) := fun i ↦
      (hu i).measurableSet_image_extChartAt_source_inter α
    have hpiece : ∀ i, IntegrableOn (φ.signedInChartAt b α (fun _ ↦ 1)) (A i) b.addHaar := by
      intro i
      have hsub : s i ⊆ (extChartAt I α).source ∩ (extChartAt I (β i)).source := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        simpa only [extChartAt_source] using hsource i hx.2
      apply (φ.integrableOn_signedInChartAt_one_changeChart b α (β i) hsub (hA i) b.addHaar).mpr
      exact (hlocal i).mono_set (image_mono inter_subset_right)
    have htotal : IntegrableOn (φ.signedInChartAt b α (fun _ ↦ 1)) (⋃ i, A i) b.addHaar :=
      integrableOn_finite_iUnion.mpr hpiece
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp htotal
    intro y hy
    have hn := Function.mem_support.mp hy
    by_cases ht : y ∈ (extChartAt I α).target
    · have hne : φ ((extChartAt I α).symm y) ≠ 0 := by
        intro hz
        apply hn
        rw [RoughForm.signedInChartAt_apply, dite_eq_left ht,
          RoughForm.inChartAt_apply, hz]
        simp only [Units.val_one, Int.cast_one, one_mul]
        rfl
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover'
        (_root_.subset_tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ hne))
      exact mem_iUnion.mpr ⟨i, ⟨(extChartAt I α).symm y,
        ⟨(extChartAt I α).map_target ht, hi⟩, (extChartAt I α).right_inv ht⟩⟩
    · exact False.elim (hn (by rw [RoughForm.signedInChartAt_apply, dite_eq_right ht]))
  rw [integrableTopForm_iff]
  exact ⟨hc, ⟨b⟩, fun b' α ↦
    (φ.integrable_signedInChartAt_basis_iff b b' α (fun _ ↦ 1)).mpr (hcoef α)⟩

/-- A compact rough form supported in a preferred chart is intrinsically integrable exactly
when its single coefficient in one model basis is integrable. -/
public theorem RoughForm.integrableTopForm_iff_of_tsupport_subset_chart
    (b : Module.Basis (Fin k) ℝ E)
    (α : M) (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (chartAt H α).source) :
    IntegrableTopForm φ ↔ Integrable (φ.signedInChartAt b α (fun _ ↦ 1)) b.addHaar := by
  refine ⟨fun h ↦ ((integrableTopForm_iff φ).mp h).2.2 b α, fun hi ↦ ?_⟩
  apply φ.integrableTopForm_of_open_cover hc b
    (fun _ : Unit ↦ α) (fun _ ↦ (chartAt H α).source)
    (fun _ ↦ (chartAt H α).open_source) (fun _ ↦ Subset.rfl)
  · intro x hx
    exact mem_iUnion.mpr ⟨(), hs hx⟩
  · exact fun _ ↦ hi.integrableOn

end RoughIntegrability

private def coverIntegral [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (c : ChartCover (I := I) s) : ℝ :=
  (Orientation.signBasis l.modelOrientation b : ℝ) * ∑ i,
    ∫ y in (extChartAt I (c.center i)) '' c.piece i,
      φ.signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x.val) y ∂b.addHaar

private theorem coverIntegral_eq_sum_chartIntegral [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (c : ChartCover (I := I) s) :
    coverIntegral l b φ c = ∑ i, l.chartIntegral
      (fun x ↦ (c.piece i).indicator (fun _ ↦ (1 : ℝ)) x • φ x) (c.center i) := by
  classical
  unfold coverIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [l.chartIntegral_eq_integral _ b (c.center i)]
  congr 1
  have heq : RoughForm.signedInChartAt (I := I)
      (fun x ↦ (c.piece i).indicator (fun _ ↦ (1 : ℝ)) x • φ x) b (c.center i)
        (fun x ↦ l.signAt (c.center i) x) =
      ((extChartAt I (c.center i)) '' c.piece i).indicator
        (φ.signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x)) := by
    funext y
    rw [RoughForm.signedInChartAt_indicator,
      ← (extChartAt I (c.center i)).image_eq_target_inter_inv_preimage (c.piece_subset i)]
  rw [heq, integral_indicator (c.measurableSet_image_piece i)]

private theorem coverIntegral_basis_eq [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b b' : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (c : ChartCover (I := I) s) :
    coverIntegral l b φ c = coverIntegral l b' φ c := by
  rw [coverIntegral_eq_sum_chartIntegral, coverIntegral_eq_sum_chartIntegral]

private theorem coverIntegral_flip [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (c : ChartCover (I := I) s) :
    coverIntegral l.flip b φ c = coverIntegral l b φ c := by
  rw [coverIntegral_eq_sum_chartIntegral, coverIntegral_eq_sum_chartIntegral]
  simp_rw [Manifold.OrientationLift.chartIntegral_flip]

private theorem coverIntegral_neg [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (c : ChartCover (I := I) s) :
    coverIntegral (-l) b φ c = -coverIntegral l b φ c := by
  rw [coverIntegral_eq_sum_chartIntegral, coverIntegral_eq_sum_chartIntegral]
  simp_rw [Manifold.OrientationLift.chartIntegral_neg, Finset.sum_neg_distrib]

private theorem coverIntegral_zero [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (c : ChartCover (I := I) s) : coverIntegral l b (0 : RoughForm I M ℝ k) c = 0 := by
  unfold coverIntegral
  simp only [RoughForm.signedInChartAt_zero, integral_zero, Finset.sum_const_zero, mul_zero]

private theorem coverIntegral_smul [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (c : ℝ) (φ : RoughForm I M ℝ k) (p : ChartCover (I := I) s) :
    coverIntegral l b (c • φ) p = c * coverIntegral l b φ p := by
  unfold coverIntegral
  simp_rw [RoughForm.signedInChartAt_smul]
  simp_rw [integral_const_mul]
  rw [← Finset.mul_sum]
  ring

private theorem coverIntegral_choose_eq [FiniteDimensional ℝ E]
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) {s t : Set M} (hs : IsCompact s) (ht : IsCompact t)
    (hst : s = t) :
    coverIntegral l b φ (chooseChartCover (I := I) s hs) =
      coverIntegral l b φ (chooseChartCover (I := I) t ht) := by
  subst t
  rfl

private theorem signed_coefficient_integrable [FiniteDimensional ℝ E]
    (l : Manifold.OrientationLift I M (Fin k)) {φ : RoughForm I M ℝ k}
    (hi : IntegrableTopForm φ) (b : Module.Basis (Fin k) ℝ E) (α : M) :
    Integrable (φ.signedInChartAt b α (fun x ↦ l.signAt α x)) b.addHaar := by
  apply (φ.integrable_signedInChartAt_iff_unsigned b α (fun x ↦ l.signAt α x) ?_ b.addHaar).mpr
    (((integrableTopForm_iff φ).mp hi).2.2 b α)
  apply continuousOn_iff_continuous_domRestrict.mp
  simpa only [extChartAt_source] using l.continuousOn_signAt α

private theorem coverIntegral_add [FiniteDimensional ℝ E] {s : Set M}
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ ψ : RoughForm I M ℝ k) (hφ : IntegrableTopForm φ) (hψ : IntegrableTopForm ψ)
    (c : ChartCover (I := I) s) :
    coverIntegral l b (φ + ψ) c = coverIntegral l b φ c + coverIntegral l b ψ c := by
  have heq (i : Fin c.n) :
      (∫ y in (extChartAt I (c.center i)) '' c.piece i,
        (φ + ψ).signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x) y ∂b.addHaar) =
      (∫ y in (extChartAt I (c.center i)) '' c.piece i,
        φ.signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x) y ∂b.addHaar) +
      ∫ y in (extChartAt I (c.center i)) '' c.piece i,
        ψ.signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x) y ∂b.addHaar := by
    simp_rw [RoughForm.signedInChartAt_add]
    exact integral_add (signed_coefficient_integrable l hφ b (c.center i)).integrableOn
      (signed_coefficient_integrable l hψ b (c.center i)).integrableOn
  unfold coverIntegral
  simp_rw [heq]
  rw [Finset.sum_add_distrib, mul_add]

private theorem signed_changeChart [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : IsChartMeasurable I s) :
    (∫ y in (extChartAt I α) '' s, φ.signedInChartAt b α (fun x ↦ l.signAt α x) y ∂b.addHaar) =
      ∫ y in (extChartAt I β) '' s, φ.signedInChartAt b β (fun x ↦ l.signAt β x) y ∂b.addHaar := by
  apply (φ.signedInChartAt_changeChart b α β (fun x ↦ l.signAt α x)
    (fun x ↦ l.signAt β x) hsub (hs.image_extChartAt α (hsub.trans inter_subset_left))
    ?_ b.addHaar).1
  intro x hx
  have hα : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using (hsub hx).1
  have hβ : x ∈ (chartAt H β).source := by simpa only [extChartAt_source] using (hsub hx).2
  simpa only [Manifold.OrientationLift.signAt_of_mem _ hα,
    Manifold.OrientationLift.signAt_of_mem _ hβ] using l.sign_mul_det α β x hα hβ

private theorem integral_chart_piece_refine [FiniteDimensional ℝ E]
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (hi : IntegrableTopForm φ) (b : Module.Basis (Fin k) ℝ E) (α : M)
    {s : Set M} (c : ChartCover (I := I) s) (hc : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ s)
    {u : Set M} (hu : IsChartMeasurable I u) (hus : u ⊆ (extChartAt I α).source) :
    (∫ y in (extChartAt I α) '' u, φ.signedInChartAt b α (fun x ↦ l.signAt α x) y ∂b.addHaar) =
      ∑ i, ∫ y in (extChartAt I α) '' (u ∩ c.piece i),
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y ∂b.addHaar := by
  let e := extChartAt I α
  let f := φ.signedInChartAt b α (fun x ↦ l.signAt α x)
  let v : Fin c.n → Set E := fun i ↦ e '' (u ∩ c.piece i)
  have hv (i : Fin c.n) : MeasurableSet (v i) :=
    (hu.inter (c.isChartMeasurable_piece i)).image_extChartAt α (inter_subset_left.trans hus)
  have hvs : (⋃ i, v i) ⊆ e '' u := iUnion_subset fun _ ↦ image_mono inter_subset_left
  have hdisj : Pairwise (fun i j ↦ Disjoint (v i) (v j)) := by
    intro i j hij
    exact ((c.pairwise_disjoint hij).mono inter_subset_right inter_subset_right).image e.injOn
      (inter_subset_left.trans hus) (inter_subset_left.trans hus)
  have hf : Integrable f b.addHaar := signed_coefficient_integrable l hi b α
  have hz : ∀ y ∈ e '' u \ ⋃ i, v i, f y = 0 := by
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    have hx0 : x ∉ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) := by
      intro ht
      obtain ⟨i, hi⟩ := mem_iUnion.mp (c.piece_covers (hc ht))
      exact hn (mem_iUnion.mpr ⟨i, mem_image_of_mem e ⟨hx, hi⟩⟩)
    have hφ : φ x = 0 :=
      _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) hx0
    dsimp only [f, e]
    rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ (hus hx),
      RoughForm.inChartAt_apply, e.left_inv (hus hx), hφ]
    simp
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hu.image_extChartAt α hus) hvs hz).trans
    (integral_iUnion_fintype hv hdisj (fun _ ↦ hf.integrableOn))

private theorem coverIntegral_eq [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (hi : IntegrableTopForm φ) (b : Module.Basis (Fin k) ℝ E) {s t : Set M}
    (c : ChartCover (I := I) s) (d : ChartCover (I := I) t)
    (hc : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ s)
    (hd : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ t) :
    coverIntegral l b φ c = coverIntegral l b φ d := by
  unfold coverIntegral
  apply congrArg (fun r : ℝ ↦ (Orientation.signBasis l.modelOrientation b : ℝ) * r)
  simp_rw [integral_chart_piece_refine l φ hi b _ d hd
    (c.isChartMeasurable_piece _) (c.piece_subset _),
    integral_chart_piece_refine l φ hi b _ c hc
    (d.isChartMeasurable_piece _) (d.piece_subset _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h := signed_changeChart l φ b (c.center i) (d.center j)
    (s := c.piece i ∩ d.piece j)
    (fun x hx ↦ ⟨c.piece_subset i hx.1, d.piece_subset j hx.2⟩)
    ((c.isChartMeasurable_piece i).inter (d.isChartMeasurable_piece j))
  simpa only [inter_comm] using h

private theorem coverIntegral_eq_chartIntegral_of_ae_support
    [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E)
    (c : ChartCover (I := I) (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ))
    (hi : IntegrableTopForm φ) (α : M)
    (hα : ∀ β : M, ∀ᵐ y ∂b.addHaar,
      y ∉ (extChartAt I β) '' ((extChartAt I β).source ∩ (extChartAt I α).source) →
        φ.signedInChartAt b β (fun _ ↦ 1) y = 0) :
    coverIntegral l b φ c = l.chartIntegral φ α := by
  let e := extChartAt I α
  let f := φ.signedInChartAt b α (fun x ↦ l.signAt α x)
  let s : Fin c.n → Set M := fun i ↦ c.piece i ∩ e.source
  have hs (i : Fin c.n) : IsChartMeasurable I (s i) :=
    (c.isChartMeasurable_piece i).inter
      (by dsimp only [e]; simpa only [extChartAt_source] using
        (chartAt H α).open_source.isChartMeasurable (I := I))
  rw [l.chartIntegral_eq_integral φ b α, coverIntegral]
  apply congrArg (fun r : ℝ ↦ (Orientation.signBasis l.modelOrientation b : ℝ) * r)
  calc
    (∑ i, ∫ y in (extChartAt I (c.center i)) '' c.piece i,
      φ.signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x) y ∂b.addHaar) =
        ∑ i, ∫ y in e '' s i, f y ∂b.addHaar := by
      apply Finset.sum_congr rfl
      intro i _
      have hzero : ∀ᵐ y ∂b.addHaar,
          y ∈ (extChartAt I (c.center i)) '' c.piece i \
            (extChartAt I (c.center i)) '' s i →
            φ.signedInChartAt b (c.center i) (fun x ↦ l.signAt (c.center i) x) y = 0 := by
        filter_upwards [hα (c.center i)] with y hy hys
        obtain ⟨x, hx, rfl⟩ := hys.1
        have hn : extChartAt I (c.center i) x ∉ (extChartAt I (c.center i)) ''
            ((extChartAt I (c.center i)).source ∩ e.source) := by
          rintro ⟨z, hz, he⟩
          have hxz : x = z := (extChartAt I (c.center i)).injOn (c.piece_subset i hx) hz.1 he.symm
          exact hys.2 (mem_image_of_mem _ ⟨hx, hxz ▸ hz.2⟩)
        have hz := hy hn
        rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ (c.piece_subset i hx)] at hz ⊢
        simp only [Units.val_one, Int.cast_one, one_mul] at hz
        rw [hz, mul_zero]
      have hspiece : s i ⊆ c.piece i := inter_subset_left
      have heq := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := b.addHaar)
        (c.measurableSet_image_piece i).nullMeasurableSet
        (image_mono hspiece) hzero
      exact heq.trans (signed_changeChart l φ b (c.center i) α
        (fun _ hx ↦ ⟨c.piece_subset i hx.1, hx.2⟩) (hs i))
    _ = ∫ y, f y ∂b.addHaar := by
      have he := integral_chart_piece_refine l φ hi b α c Subset.rfl
        (by simpa only [extChartAt_source] using
          (chartAt H α).open_source.isChartMeasurable (I := I)) Subset.rfl
      -- Unfold the local chart e and coefficient f in the refinement identity; the
      -- original statement names extChartAt and signedInChartAt explicitly.
      change (∫ y in e '' e.source, f y ∂b.addHaar) =
        ∑ i, ∫ y in e '' (e.source ∩ c.piece i), f y ∂b.addHaar at he
      have he' : (∑ i, ∫ y in e '' s i, f y ∂b.addHaar) =
          ∫ y in e '' e.source, f y ∂b.addHaar := by
        simpa only [s, inter_comm] using he.symm
      rw [he', e.image_source_eq_target]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
        Function.notMem_support.mp (fun hn ↦
          hy (φ.support_signedInChartAt_subset_target b α (fun x ↦ l.signAt α x) hn))

end WithMeasure

/-- Integrable top forms have compact topological support. -/
public theorem IntegrableTopForm.isCompact {φ : RoughForm I M ℝ k}
    (hi : IntegrableTopForm φ) : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact ((integrableTopForm_iff φ).mp hi).1

/-- Multiplication by a nonzero scalar preserves top-form integrability. -/
public theorem integrableTopForm_smul_iff (c : ℝ) (φ : RoughForm I M ℝ k) (hc : c ≠ 0) :
    IntegrableTopForm (c • φ) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableTopForm_iff, integrableTopForm_iff, RoughForm.tsupport_smul c φ hc]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall_congr'
  intro b
  apply forall_congr'
  intro α
  have heq : (c • φ).signedInChartAt b α (fun _ ↦ 1) =
      fun y ↦ c * φ.signedInChartAt b α (fun _ ↦ 1) y := by
    funext y
    exact RoughForm.signedInChartAt_fun_smul (fun _ ↦ c) φ b α (fun _ ↦ 1) y
  rw [heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _

/-- The sum of two integrable top forms is integrable. -/
public theorem IntegrableTopForm.add {φ ψ : RoughForm I M ℝ k}
    (hφ : IntegrableTopForm φ) (hψ : IntegrableTopForm ψ) : IntegrableTopForm (φ + ψ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableTopForm_iff] at hφ hψ ⊢
  refine ⟨RoughForm.isCompact_tsupport_add hφ.1 hψ.1, hφ.2.1, ?_⟩
  intro b α
  have heq : (φ + ψ).signedInChartAt b α (fun _ ↦ 1) =
      fun y ↦ φ.signedInChartAt b α (fun _ ↦ 1) y + ψ.signedInChartAt b α (fun _ ↦ 1) y :=
    funext (RoughForm.signedInChartAt_add φ ψ b α (fun _ ↦ 1))
  rw [heq]
  exact (hφ.2.2 b α).add (hψ.2.2 b α)

/-- The zero form is integrable in top degree. An explicit model basis also covers an empty
manifold, where no nonzero form can certify the degree. -/
public theorem IntegrableTopForm.zero (b : Module.Basis (Fin k) ℝ E) :
    IntegrableTopForm (0 : RoughForm I M ℝ k) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableTopForm_iff]
  refine ⟨RoughForm.isCompact_tsupport_zero, ⟨b⟩, ?_⟩
  intro b α
  have heq : (0 : RoughForm I M ℝ k).signedInChartAt b α (fun _ ↦ 1) = 0 :=
    funext (RoughForm.signedInChartAt_zero b α (fun _ ↦ 1))
  rw [heq]
  exact integrable_zero E ℝ b.addHaar

/-- Multiplication by any constant scalar preserves top-form integrability. -/
public theorem IntegrableTopForm.smul {φ : RoughForm I M ℝ k}
    (hφ : IntegrableTopForm φ) (c : ℝ) : IntegrableTopForm (c • φ) := by
  classical
  by_cases hc : c = 0
  · subst c
    let : MeasurableSpace E := borel E
    let : BorelSpace E := ⟨rfl⟩
    obtain ⟨b⟩ := ((integrableTopForm_iff φ).mp hφ).2.1
    simpa only [zero_smul] using IntegrableTopForm.zero (I := I) (M := M) b
  · exact (integrableTopForm_smul_iff c φ hc).mpr hφ

/-- Negation preserves top-form integrability. -/
public theorem IntegrableTopForm.neg {φ : RoughForm I M ℝ k}
    (hφ : IntegrableTopForm φ) : IntegrableTopForm (-φ) := by
  simpa only [neg_one_smul] using hφ.smul (-1)

/-- Finite sums of integrable top forms are integrable. -/
public theorem IntegrableTopForm.sum {ι : Type*} (b : Module.Basis (Fin k) ℝ E)
    (φ : ι → RoughForm I M ℝ k) (s : Finset ι) (hφ : ∀ i ∈ s, IntegrableTopForm (φ i)) :
    IntegrableTopForm (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntegrableTopForm.zero (I := I) (M := M) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hφ i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj)))

variable [FiniteDimensional ℝ E]

/-- The total integral of a rough top form against a manifold orientation. It is zero unless
the form is compactly supported and integrable. A disjoint Borel chart cover defines the sum;
the manifold needs no Hausdorff or measurable-space structure. -/
public def integralTopForm (o : Manifold.Orientation I M (Fin k))
    (φ : RoughForm I M ℝ k) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact if hi : IntegrableTopForm φ then
    let l := Classical.choose o.exists_lift
    let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    coverIntegral l b φ (chooseChartCover (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) hi.1)
  else 0

/-- A nonintegrable top form has zero total integral. -/
public theorem integralTopForm_eq_zero_of_not_integrable
    (o : Manifold.Orientation I M (Fin k)) (φ : RoughForm I M ℝ k)
    (hi : ¬IntegrableTopForm φ) : integralTopForm o φ = 0 := by
  rw [integralTopForm, dite_eq_right hi]

/-- A form without compact support has zero total integral. -/
public theorem integralTopForm_eq_zero_of_not_isCompact
    (o : Manifold.Orientation I M (Fin k)) (φ : RoughForm I M ℝ k)
    (hc : ¬IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) : integralTopForm o φ = 0 :=
  integralTopForm_eq_zero_of_not_integrable o φ (fun hi ↦ hc hi.isCompact)

private theorem integralTopForm_mk [MeasurableSpace E] [BorelSpace E]
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (hi : IntegrableTopForm φ) (b : Module.Basis (Fin k) ℝ E) :
    integralTopForm (Manifold.Orientation.mk l) φ =
      coverIntegral l b φ (chooseChartCover
        (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) hi.isCompact) := by
  classical
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  let r := Classical.choose (Manifold.Orientation.mk l).exists_lift
  have hr : Manifold.Orientation.mk r = Manifold.Orientation.mk l :=
    Classical.choose_spec (Manifold.Orientation.mk l).exists_lift
  rw [integralTopForm, dite_eq_left hi]
  dsimp only
  rw [coverIntegral_basis_eq _ _ b]
  rcases (Manifold.Orientation.mk_eq_mk_iff r l).mp hr with h | h
  -- Lift uniqueness is phrased for the local abbreviation r, whereas unfolding the
  -- integral exposes Classical.choose; give rw the explicit chosen-lift equality.
  · rw [show Classical.choose (Manifold.Orientation.mk l).exists_lift = l from h]
  · rw [show Classical.choose (Manifold.Orientation.mk l).exists_lift = l.flip from h,
      coverIntegral_flip]

private theorem integralTopForm_eq_coverIntegral [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] (l : Manifold.OrientationLift I M (Fin k))
    (φ : RoughForm I M ℝ k) (hi : IntegrableTopForm φ)
    (b : Module.Basis (Fin k) ℝ E) {s : Set M} (c : ChartCover (I := I) s)
    (hc : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ s) :
    integralTopForm (Manifold.Orientation.mk l) φ = coverIntegral l b φ c := by
  rw [integralTopForm_mk l φ hi b]
  exact coverIntegral_eq l φ hi b _ c Subset.rfl hc

/-- Any finite open chart cover computes the canonical integral through its disjoint Borel
pieces. The formula is independent of the cover and model basis and permits overlapping charts. -/
public theorem integralTopForm_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (l : Manifold.OrientationLift I M (Fin k))
    (φ : RoughForm I M ℝ k) (hi : IntegrableTopForm φ) (b : Module.Basis (Fin k) ℝ E)
    {m : ℕ} (α : Fin m → M) (u : Fin m → Set M) (hu : ∀ i, IsOpen (u i))
    (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ ⋃ i, u i) :
    integralTopForm (Manifold.Orientation.mk l) φ =
      (Orientation.signBasis l.modelOrientation b : ℝ) * ∑ i,
        ∫ y in (extChartAt I (α i)) '' disjointed u i,
          φ.signedInChartAt b (α i) (fun x ↦ l.signAt (α i) x) y ∂b.addHaar := by
  let c : ChartCover (I := I) (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) := ⟨m, α, u, hu, hs, hc⟩
  exact integralTopForm_eq_coverIntegral l φ hi b c Subset.rfl

/-- A compact manifold admits a finite disjoint chartwise Borel partition computing every
integrable top-form integral. No measurable structure on the manifold is installed. -/
public theorem exists_chart_partition_integralTopForm [IsManifold I 1 M] [CompactSpace M]
    [MeasurableSpace E] [BorelSpace E] (l : Manifold.OrientationLift I M (Fin k))
    (b : Module.Basis (Fin k) ℝ E) :
    ∃ m : ℕ, ∃ α : Fin m → M, ∃ s : Fin m → Set M,
      (∀ i, IsChartMeasurable I (s i)) ∧
      (∀ i, s i ⊆ (extChartAt I (α i)).source) ∧
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ ∧
      ∀ φ : RoughForm I M ℝ k, IntegrableTopForm φ →
        integralTopForm (Manifold.Orientation.mk l) φ =
          (Orientation.signBasis l.modelOrientation b : ℝ) * ∑ i,
            ∫ y in (extChartAt I (α i)) '' s i,
              φ.signedInChartAt b (α i) (fun x ↦ l.signAt (α i) x) y ∂b.addHaar := by
  let c := chooseChartCover (I := I) (univ : Set M) isCompact_univ
  refine ⟨c.n, c.center, c.piece, c.isChartMeasurable_piece, c.piece_subset,
    c.pairwise_disjoint, Subset.antisymm (subset_univ _) c.piece_covers, ?_⟩
  intro φ hi
  exact integralTopForm_eq_coverIntegral l φ hi b c (subset_univ _)

/-- The top-form integral is additive on integrable rough forms. -/
public theorem integralTopForm_add_of_integrable [IsManifold I 1 M]
    (o : Manifold.Orientation I M (Fin k)) {φ ψ : RoughForm I M ℝ k}
    (hφ : IntegrableTopForm φ) (hψ : IntegrableTopForm ψ) :
    integralTopForm o (φ + ψ) = integralTopForm o φ + integralTopForm o ψ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  let c := chooseChartCover (I := I) ((_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ∪
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) ψ)) (hφ.isCompact.union hψ.isCompact)
  -- tsupport_add is a fixed-codomain function lemma; identify the tangent fibres
  -- with the model space to select that function argument.
  rw [integralTopForm_eq_coverIntegral l _ (hφ.add hψ) b c (_root_.tsupport_add
    (show M → E [⋀^Fin k]→L[ℝ] ℝ from φ) ψ),
    integralTopForm_eq_coverIntegral l _ hφ b c subset_union_left,
    integralTopForm_eq_coverIntegral l _ hψ b c subset_union_right,
    coverIntegral_add l b φ ψ hφ hψ c]

/-- Reversing the manifold orientation reverses the total integral, including its value on
nonintegrable rough forms. -/
public theorem integralTopForm_neg (o : Manifold.Orientation I M (Fin k))
    (φ : RoughForm I M ℝ k) : integralTopForm (-o) φ = -integralTopForm o φ := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  by_cases hi : IntegrableTopForm φ
  · let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    rw [Manifold.Orientation.neg_mk, integralTopForm_mk (-l) φ hi b,
      integralTopForm_mk l φ hi b, coverIntegral_neg]
  · rw [integralTopForm_eq_zero_of_not_integrable _ _ hi,
      integralTopForm_eq_zero_of_not_integrable _ _ hi, neg_zero]

/-- The zero top form has zero integral. -/
@[simp]
public theorem integralTopForm_zero (o : Manifold.Orientation I M (Fin k)) :
    integralTopForm o (0 : RoughForm I M ℝ k) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  by_cases hi : IntegrableTopForm (0 : RoughForm I M ℝ k)
  · let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    rw [integralTopForm_mk l _ hi b, coverIntegral_zero]
  · exact integralTopForm_eq_zero_of_not_integrable _ _ hi

/-- Integration commutes with finite sums of integrable top forms. -/
public theorem integralTopForm_sum [IsManifold I 1 M] {ι : Type*}
    (o : Manifold.Orientation I M (Fin k)) (φ : ι → RoughForm I M ℝ k) (s : Finset ι)
    (hφ : ∀ i ∈ s, IntegrableTopForm (φ i)) :
    integralTopForm o (∑ i ∈ s, φ i) = ∑ i ∈ s, integralTopForm o (φ i) := by
  classical
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integralTopForm_add_of_integrable o (hφ i (Finset.mem_insert_self i s))
        (IntegrableTopForm.sum b φ s (fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj))]

/-- Constant scalar multiplication commutes with the total top-form integral, even for
nonintegrable rough forms. -/
public theorem integralTopForm_smul (o : Manifold.Orientation I M (Fin k))
    (c : ℝ) (φ : RoughForm I M ℝ k) : integralTopForm o (c • φ) = c * integralTopForm o φ := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  by_cases hi : IntegrableTopForm φ
  · have hi' := (integrableTopForm_smul_iff c φ hc).mpr hi
    let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    rw [integralTopForm_mk l _ hi' b, integralTopForm_mk l _ hi b]
    rw [coverIntegral_smul]
    apply congrArg (fun r : ℝ ↦ c * r)
    exact coverIntegral_choose_eq l b φ hi'.isCompact hi.isCompact (RoughForm.tsupport_smul c φ hc)
  · have hi' : ¬IntegrableTopForm (c • φ) := fun h ↦ hi ((integrableTopForm_smul_iff c φ hc).mp h)
    rw [integralTopForm_eq_zero_of_not_integrable _ _ hi',
      integralTopForm_eq_zero_of_not_integrable _ _ hi, mul_zero]

/-- A preferred chart computes the whole integral when the form vanishes outside that
chart up to a chartwise null set. The premise uses the actual nonzero values, rather than
their closure, so null faces or endpoints may be omitted from the chart. -/
public theorem integralTopForm_eq_chartIntegral_of_ae_support [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (l : Manifold.OrientationLift I M (Fin k))
    (φ : RoughForm I M ℝ k) (hi : IntegrableTopForm φ) (α : M)
    (hs : IsNullSet I ({x | φ x ≠ 0} \ (extChartAt I α).source)) :
    integralTopForm (Manifold.Orientation.mk l) φ = l.chartIntegral φ α := by
  classical
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  rw [integralTopForm_mk l φ hi b]
  apply coverIntegral_eq_chartIntegral_of_ae_support l φ b _ hi α
  intro β
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hs.chartwise β b.addHaar)] with y hy ho
  by_cases ht : y ∈ (extChartAt I β).target
  · have hz : φ ((extChartAt I β).symm y) = 0 := by
      by_contra hn
      apply hy
      refine ⟨(extChartAt I β).symm y, ⟨⟨hn, ?_⟩,
        (extChartAt I β).map_target ht⟩, (extChartAt I β).right_inv ht⟩
      intro ha
      exact ho ⟨(extChartAt I β).symm y,
        ⟨(extChartAt I β).map_target ht, ha⟩, (extChartAt I β).right_inv ht⟩
    rw [RoughForm.signedInChartAt_apply, dite_eq_left ht, RoughForm.inChartAt_apply, hz]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rfl
  · rw [RoughForm.signedInChartAt_apply, dite_eq_right ht]

/-- An integrable form supported in a preferred chart has that chart's integral. This applies
to rough forms, including discontinuous coefficients, and to any representing orientation lift. -/
public theorem integralTopForm_eq_chartIntegral [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (l : Manifold.OrientationLift I M (Fin k))
    (φ : RoughForm I M ℝ k) (hi : IntegrableTopForm φ) (α : M)
    (hs : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source) :
    integralTopForm (Manifold.Orientation.mk l) φ = l.chartIntegral φ α := by
  apply integralTopForm_eq_chartIntegral_of_ae_support l φ hi α
  apply (isNullSet_boundary (I := I)).mono
  intro x hx
  exact False.elim (hx.2 (hs (_root_.subset_tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ hx.1)))

end TauCeti
