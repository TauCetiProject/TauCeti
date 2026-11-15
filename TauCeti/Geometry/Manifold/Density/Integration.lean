/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Chart
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.MeasureTheory.Integral.Bochner.Density
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Order.Disjointed
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Orientation-free integration of rough densities on manifolds

A rough density `μ : RoughDensity I M k` is integrable (`TauCeti.IntegrableDensity`) when its
topological support is compact, the model space `E` has dimension `k`, and in every preferred
extended chart and every model basis `b` the coordinate coefficient `y ↦ μ.inChartAt α y b` is
integrable on `(extChartAt I α).target` against `b.addHaar`.

To integrate an integrable rough density (`TauCeti.integralDensity`), a finite open chart cover of
`tsupport μ` is disjointed into Borel coordinate pieces and summed against `b.addHaar`. Because
density coordinates transform by the absolute Jacobian determinant (`|det|`) rather than the signed
determinant, each piece integral is independent of the model basis
(`Module.Basis.setIntegral_density_apply_eq`) and common refinement proves independence of the
chart cover (`TauCeti.RoughDensity.setIntegral_inChartAt_changeChart`). Neither an orientation of
`M`, nor a Riemannian metric, nor a Hausdorff or measurable-space structure on `M` is required, and
manifolds with boundary or corners are included.

## Main definitions and results

* `TauCeti.IntegrableDensity`: intrinsic coordinate integrability of a rough density.
* `TauCeti.integralDensity`: orientation-free total integral of a rough density on a manifold,
  returning `0` when `μ` is not integrable.
* `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals`: computation on any finite open chart
  cover via disjointed Borel pieces.
* `TauCeti.integralDensity_eq_setIntegral_of_ae_support` and
  `TauCeti.integralDensity_eq_setIntegral_of_tsupport_subset`: single-chart formulas when `μ`
  vanishes outside one chart up to a null set or has topological support inside one chart.
* `TauCeti.IntegrableDensity.integralDensity_model_eq_integral` and
  `TauCeti.IntegrableDensity.integralDensity_real_eq_integral`: model-space and real-line formulas.
* `TauCeti.integralDensity_nonneg`, `TauCeti.integralDensity_mono_of_integrable`,
  `TauCeti.abs_integralDensity_le_of_integrable`, and `TauCeti.integralDensity_pos`: nonnegativity,
  monotonicity, triangle inequality, and strict positivity in every dimension (including zero).
* `TauCeti.RoughDensity.integrableDensity_of_continuous_section` and
  `TauCeti.RoughDensity.integrableDensity_of_contMDiff_section`: compactly supported continuous or
  smooth sections of `TauCeti.DensityBundle` are integrable.

The disjointed-chart-cover construction parallels the oriented top-form integration architecture in
`TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm`, `Positivity`, and `Regularity`,
without orientation lifts or sign cocycles.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities
  (especially Theorem 16.38 and Proposition 16.40).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {k : ℕ}

/-! ### Intrinsic integrability of rough densities -/

/-- Disjointing a family of open subsets along a locally finite order with bottom produces
chart-measurable pieces. -/
theorem isChartMeasurable_disjointed [MeasurableSpace E] [OpensMeasurableSpace E]
    {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] {u : ι → Set M}
    (hu : ∀ i, IsOpen (u i)) (i : ι) :
    IsChartMeasurable I (disjointed u i) := by
  rw [disjointed_apply]
  have ho : IsOpen ((Finset.Iio i).sup u) := by
    rw [Finset.sup_set_eq_biUnion]
    exact isOpen_biUnion fun j _ ↦ hu j
  exact (hu i).isChartMeasurable.diff ho.isChartMeasurable

/-- A rough density is integrable when it has compact topological support, `E` admits a basis of
cardinality `k`, and its coordinate expression on `(extChartAt I α).target` is integrable in every
preferred chart and every model basis against the normalized additive Haar measure. -/
def IntegrableDensity (μ : RoughDensity I M k) : Prop := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact IsCompact (_root_.tsupport (α := Density E k) μ) ∧
    Nonempty (Module.Basis (Fin k) ℝ E) ∧
    ∀ (b : Module.Basis (Fin k) ℝ E) (α : M),
      IntegrableOn (fun y ↦ μ.inChartAt α y b) (extChartAt I α).target b.addHaar

private structure DensityChartCover (s : Set M) where
  n : ℕ
  center : Fin n → M
  domain : Fin n → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  domain_subset : ∀ i, domain i ⊆ (extChartAt I (center i)).source
  covers : s ⊆ ⋃ i, domain i

private def chooseDensityChartCover [ProperSpace E] (s : Set M) (hc : IsCompact s) :
    DensityChartCover (I := I) s := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let h := exists_finite_precompact_chart_cover (I := I) hc
  let n := h.choose
  let α := h.choose_spec.choose
  let u := h.choose_spec.choose_spec.choose
  have hp := h.choose_spec.choose_spec.choose_spec.choose_spec
  exact ⟨n, α, u, fun i ↦ (hp.1 i).1, fun i ↦ (hp.1 i).2.1, hp.2⟩

private def DensityChartCover.piece {s : Set M} (c : DensityChartCover (I := I) s)
    (i : Fin c.n) : Set M :=
  disjointed c.domain i

private theorem DensityChartCover.piece_subset {s : Set M} (c : DensityChartCover (I := I) s)
    (i : Fin c.n) : c.piece i ⊆ (extChartAt I (c.center i)).source :=
  (disjointed_subset c.domain i).trans (c.domain_subset i)

private theorem DensityChartCover.piece_covers {s : Set M} (c : DensityChartCover (I := I) s) :
    s ⊆ ⋃ i, c.piece i := by
  simpa only [DensityChartCover.piece, iUnion_disjointed] using c.covers

private theorem DensityChartCover.pairwise_disjoint {s : Set M}
    (c : DensityChartCover (I := I) s) :
    Pairwise (fun i j ↦ Disjoint (c.piece i) (c.piece j)) :=
  disjoint_disjointed c.domain

section WithMeasure

variable [MeasurableSpace E] [BorelSpace E]

private theorem DensityChartCover.isChartMeasurable_piece {s : Set M}
    (c : DensityChartCover (I := I) s) (i : Fin c.n) : IsChartMeasurable I (c.piece i) :=
  isChartMeasurable_disjointed c.isOpen_domain i

private theorem DensityChartCover.measurableSet_image_piece {s : Set M}
    (c : DensityChartCover (I := I) s) (i : Fin c.n) :
    MeasurableSet ((extChartAt I (c.center i)) '' c.piece i) :=
  (c.isChartMeasurable_piece i).image_extChartAt (c.center i) (c.piece_subset i)

/-- Coordinate characterization of `IntegrableDensity` under any Borel measurable structure on the
model space `E`. -/
theorem integrableDensity_iff (μ : RoughDensity I M k) :
    IntegrableDensity μ ↔ IsCompact (_root_.tsupport (α := Density E k) μ) ∧
      Nonempty (Module.Basis (Fin k) ℝ E) ∧
      ∀ (b : Module.Basis (Fin k) ℝ E) (α : M),
        IntegrableOn (fun y ↦ μ.inChartAt α y b) (extChartAt I α).target b.addHaar := by
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  rfl

/-- Integrability of a compactly supported rough density can be checked on any open chart cover in
a single model basis. -/
theorem RoughDensity.integrableDensity_of_open_cover [IsManifold I 1 M] {J : Type*}
    (μ : RoughDensity I M k) (hc : IsCompact (_root_.tsupport (α := Density E k) μ))
    (b : Module.Basis (Fin k) ℝ E)
    (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i))
    (hsource : ∀ i, u i ⊆ (chartAt H (β i)).source)
    (hcover : _root_.tsupport (α := Density E k) μ ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (fun y ↦ μ.inChartAt (β i) y b)
      ((extChartAt I (β i)) '' u i) b.addHaar) : IntegrableDensity μ := by
  classical
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover u hu hcover
  have hcover' : _root_.tsupport (α := Density E k) μ ⊆ ⋃ i : t, u i := fun x hx ↦ by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hchart (α : M) :
      IntegrableOn (fun y ↦ μ.inChartAt α y b) (extChartAt I α).target b.addHaar := by
    let s : t → Set M := fun i ↦ (extChartAt I α).source ∩ u i
    let A : t → Set E := fun i ↦ (extChartAt I α) '' s i
    have hA : ∀ i, MeasurableSet (A i) := fun i ↦
      (hu i).measurableSet_image_extChartAt_source_inter α
    have hpiece : ∀ i, IntegrableOn (fun y ↦ μ.inChartAt α y b) (A i) b.addHaar := fun i ↦ by
      have hsub : s i ⊆ (extChartAt I α).source ∩ (extChartAt I (β i)).source := fun x hx ↦
        ⟨hx.1, by simpa only [extChartAt_source] using hsource i hx.2⟩
      exact (μ.integrableOn_inChartAt_changeChart b α (β i) hsub (hA i) b.addHaar).mpr
        ((hlocal i).mono_set (image_mono inter_subset_right))
    have hsub_target : (⋃ i, A i) ⊆ (extChartAt I α).target :=
      iUnion_subset fun i ↦ (image_mono inter_subset_left).trans
        (extChartAt I α).image_source_eq_target.subset
    let g : E → ℝ := (extChartAt I α).target.indicator fun y ↦ μ.inChartAt α y b
    have hgtotal : IntegrableOn g (⋃ i, A i) b.addHaar :=
      integrableOn_finite_iUnion.mpr fun i ↦ (hpiece i).congr_fun
        (fun y hy ↦ (Set.indicator_of_mem (hsub_target (mem_iUnion.mpr ⟨i, hy⟩))
          (fun z ↦ μ.inChartAt α z b)).symm) (hA i)
    have hg : Integrable g b.addHaar :=
      (integrableOn_iff_integrable_of_support_subset
        (μ.support_target_indicator_inChartAt_subset α b hcover')).mp hgtotal
    exact (integrable_indicator_iff (measurableSet_extChartAt_target α)).mp hg
  rw [integrableDensity_iff]
  exact ⟨hc, ⟨b⟩, fun b' α ↦
    (b.integrableOn_density_apply_basis_iff b' (μ.inChartAt α) _).mpr (hchart α)⟩

/-- A compactly supported rough density supported inside a single preferred chart is integrable
precisely when its coordinate coefficient on that chart's target is integrable in one basis. -/
theorem RoughDensity.integrableDensity_iff_of_tsupport_subset_chart [IsManifold I 1 M]
    {μ : RoughDensity I M k} (b : Module.Basis (Fin k) ℝ E) (α : M)
    (hc : IsCompact (_root_.tsupport (α := Density E k) μ))
    (hs : _root_.tsupport (α := Density E k) μ ⊆ (chartAt H α).source) :
    IntegrableDensity μ ↔
      IntegrableOn (fun y ↦ μ.inChartAt α y b) (extChartAt I α).target b.addHaar := by
  refine ⟨fun h ↦ ((integrableDensity_iff μ).mp h).2.2 b α, fun hi ↦ ?_⟩
  refine μ.integrableDensity_of_open_cover hc b (fun _ : Unit ↦ α)
    (fun _ ↦ (chartAt H α).source) (fun _ ↦ (chartAt H α).open_source) (fun _ ↦ Subset.rfl)
    (fun x hx ↦ mem_iUnion.mpr ⟨(), hs hx⟩) fun _ ↦ ?_
  have himg : (extChartAt I α) '' (chartAt H α).source = (extChartAt I α).target := by
    rw [← extChartAt_source I α, (extChartAt I α).image_source_eq_target]
  rwa [himg]

end WithMeasure

/-- A compactly supported rough density whose coordinate expression is continuous on every
preferred chart target is integrable. -/
theorem RoughDensity.integrableDensity_of_continuousOn_inChartAt [IsManifold I 1 M]
    {μ : RoughDensity I M k} (hc : IsCompact (_root_.tsupport (α := Density E k) μ))
    (b : Module.Basis (Fin k) ℝ E)
    (hcont : ∀ α : M, ContinuousOn (μ.inChartAt α) (extChartAt I α).target) :
    IntegrableDensity μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨m, β, u, B, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  refine μ.integrableDensity_of_open_cover hc b β u (fun i ↦ (hu i).1)
    (fun i ↦ by simpa only [extChartAt_source] using (hu i).2.1) hcover fun i ↦ ?_
  have hcb : ContinuousOn (fun y ↦ μ.inChartAt (β i) y b) (B i) :=
    ((Density.continuous_eval b).comp_continuousOn (hcont (β i))).mono (hu i).2.2.2.1
  exact (hcb.integrableOn_compact (hu i).2.2.1).mono_set (hu i).2.2.2.2

/-- Integrable rough densities have compact topological support. -/
theorem IntegrableDensity.isCompact {μ : RoughDensity I M k} (hi : IntegrableDensity μ) :
    IsCompact (_root_.tsupport (α := Density E k) μ) :=
  hi.1

/-- Multiplication by a nonzero constant preserves density integrability. -/
theorem integrableDensity_smul_iff (c : ℝ) (μ : RoughDensity I M k) (hc : c ≠ 0) :
    IntegrableDensity (c • μ) ↔ IntegrableDensity μ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff, integrableDensity_iff, RoughDensity.tsupport_smul c μ hc]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall_congr' fun b ↦ forall_congr' fun α ↦ ?_)
  simp only [RoughDensity.inChartAt_smul, Pi.smul_apply, Density.smul_apply, smul_eq_mul]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _

/-- The zero rough density is integrable when `E` admits a basis of cardinality `k`. -/
theorem IntegrableDensity.zero (b : Module.Basis (Fin k) ℝ E) :
    IntegrableDensity (0 : RoughDensity I M k) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff]
  refine ⟨RoughDensity.isCompact_tsupport_zero, ⟨b⟩, fun b' α ↦ ?_⟩
  simp only [RoughDensity.inChartAt_zero, Pi.zero_apply, Density.zero_apply]
  exact integrableOn_zero

/-- The sum of two integrable rough densities is integrable. -/
theorem IntegrableDensity.add {μ ν : RoughDensity I M k}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) : IntegrableDensity (μ + ν) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ hν ⊢
  refine ⟨RoughDensity.isCompact_tsupport_add hμ.1 hν.1, hμ.2.1, fun b α ↦ ?_⟩
  simp only [RoughDensity.inChartAt_add, Pi.add_apply, Density.add_apply]
  exact (hμ.2.2 b α).add (hν.2.2 b α)

/-- Constant scalar multiplication preserves density integrability. -/
theorem IntegrableDensity.smul {μ : RoughDensity I M k} (hμ : IntegrableDensity μ) (c : ℝ) :
    IntegrableDensity (c • μ) := by
  by_cases hc : c = 0
  · subst c
    obtain ⟨b⟩ := hμ.2.1
    simpa only [zero_smul] using IntegrableDensity.zero (I := I) (M := M) b
  · exact (integrableDensity_smul_iff c μ hc).mpr hμ

/-- Negation preserves density integrability. -/
theorem IntegrableDensity.neg {μ : RoughDensity I M k} (hμ : IntegrableDensity μ) :
    IntegrableDensity (-μ) := by
  simpa only [neg_one_smul] using hμ.smul (-1)

/-- Subtraction preserves density integrability. -/
theorem IntegrableDensity.sub {μ ν : RoughDensity I M k}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) : IntegrableDensity (μ - ν) := by
  rw [sub_eq_add_neg]
  exact hμ.add hν.neg

/-- Finite sums of integrable rough densities are integrable. -/
theorem IntegrableDensity.sum {ι : Type*} (b : Module.Basis (Fin k) ℝ E)
    (μ : ι → RoughDensity I M k) (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    IntegrableDensity (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntegrableDensity.zero (I := I) (M := M) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hμ i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj))

/-! ### Cover integrals and basis/refinement invariance -/

section CoverIntegral

variable [MeasurableSpace E] [BorelSpace E]

private def densityCoverIntegral {s : Set M} (b : Module.Basis (Fin k) ℝ E)
    (μ : RoughDensity I M k) (c : DensityChartCover (I := I) s) : ℝ :=
  ∑ i, ∫ y in (extChartAt I (c.center i)) '' c.piece i,
    μ.inChartAt (c.center i) y b ∂b.addHaar

private theorem densityCoverIntegral_basis_eq {s : Set M}
    (b b' : Module.Basis (Fin k) ℝ E) (μ : RoughDensity I M k)
    (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b μ c = densityCoverIntegral b' μ c :=
  Finset.sum_congr rfl fun i _ ↦
    (b.setIntegral_density_apply_eq b' (μ.inChartAt (c.center i)) _).symm

private theorem densityCoverIntegral_zero {s : Set M} (b : Module.Basis (Fin k) ℝ E)
    (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b (0 : RoughDensity I M k) c = 0 := by
  simp [densityCoverIntegral]

private theorem densityCoverIntegral_smul {s : Set M} (b : Module.Basis (Fin k) ℝ E)
    (r : ℝ) (μ : RoughDensity I M k) (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b (r • μ) c = r * densityCoverIntegral b μ c := by
  unfold densityCoverIntegral
  simp only [RoughDensity.inChartAt_smul, Pi.smul_apply, Density.smul_apply, smul_eq_mul,
    integral_const_mul, ← Finset.mul_sum]

private theorem densityCoverIntegral_add {s : Set M} (b : Module.Basis (Fin k) ℝ E)
    (μ ν : RoughDensity I M k) (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b (μ + ν) c =
      densityCoverIntegral b μ c + densityCoverIntegral b ν c := by
  have hiμ := (integrableDensity_iff μ).mp hμ
  have hiν := (integrableDensity_iff ν).mp hν
  have heq (i : Fin c.n) :
      (∫ y in (extChartAt I (c.center i)) '' c.piece i,
        (μ + ν).inChartAt (c.center i) y b ∂b.addHaar) =
      (∫ y in (extChartAt I (c.center i)) '' c.piece i,
        μ.inChartAt (c.center i) y b ∂b.addHaar) +
      ∫ y in (extChartAt I (c.center i)) '' c.piece i,
        ν.inChartAt (c.center i) y b ∂b.addHaar := by
    have hsub : (extChartAt I (c.center i)) '' c.piece i ⊆ (extChartAt I (c.center i)).target :=
      (image_mono (c.piece_subset i)).trans
        (extChartAt I (c.center i)).image_source_eq_target.subset
    simp only [RoughDensity.inChartAt_add, Pi.add_apply, Density.add_apply]
    exact integral_add ((hiμ.2.2 b (c.center i)).mono_set hsub)
      ((hiν.2.2 b (c.center i)).mono_set hsub)
  simp only [densityCoverIntegral, heq, Finset.sum_add_distrib]

private theorem densityCoverIntegral_choose_eq [ProperSpace E] (b : Module.Basis (Fin k) ℝ E)
    (μ : RoughDensity I M k) {s t : Set M} (hs : IsCompact s) (ht : IsCompact t) (hst : s = t) :
    densityCoverIntegral b μ (chooseDensityChartCover (I := I) s hs) =
      densityCoverIntegral b μ (chooseDensityChartCover (I := I) t ht) := by
  subst t
  rfl

private theorem integral_density_piece_refine (μ : RoughDensity I M k) (hi : IntegrableDensity μ)
    (b : Module.Basis (Fin k) ℝ E) (α : M) {s : Set M} (c : DensityChartCover (I := I) s)
    (hc : _root_.tsupport (α := Density E k) μ ⊆ s)
    {u : Set M} (hu : IsChartMeasurable I u) (hus : u ⊆ (extChartAt I α).source) :
    (∫ y in (extChartAt I α) '' u, μ.inChartAt α y b ∂b.addHaar) =
      ∑ i, ∫ y in (extChartAt I α) '' (u ∩ c.piece i), μ.inChartAt α y b ∂b.addHaar := by
  let e := extChartAt I α
  let f : E → ℝ := fun y ↦ μ.inChartAt α y b
  let v : Fin c.n → Set E := fun i ↦ e '' (u ∩ c.piece i)
  have hv (i : Fin c.n) : MeasurableSet (v i) :=
    (hu.inter (c.isChartMeasurable_piece i)).image_extChartAt α (inter_subset_left.trans hus)
  have hvs : (⋃ i, v i) ⊆ e '' u := iUnion_subset fun _ ↦ image_mono inter_subset_left
  have hdisj : Pairwise (fun i j ↦ Disjoint (v i) (v j)) := fun i j hij ↦
    ((c.pairwise_disjoint hij).mono inter_subset_right inter_subset_right).image e.injOn
      (inter_subset_left.trans hus) (inter_subset_left.trans hus)
  have hfu : IntegrableOn f (e '' u) b.addHaar :=
    (((integrableDensity_iff μ).mp hi).2.2 b α).mono_set
      ((image_mono hus).trans e.image_source_eq_target.subset)
  have hz : ∀ y ∈ e '' u \ ⋃ i, v i, f y = 0 := by
    rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
    have hx0 : x ∉ _root_.tsupport (α := Density E k) μ := fun ht ↦ by
      obtain ⟨i, hi'⟩ := mem_iUnion.mp (c.piece_covers (hc ht))
      exact hn (mem_iUnion.mpr ⟨i, mem_image_of_mem e ⟨hx, hi'⟩⟩)
    have hμ0 : μ x = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E k) hx0
    dsimp only [f, e]
    rw [RoughDensity.inChartAt_apply, (extChartAt I α).left_inv (hus hx), hμ0]
    rfl
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hu.image_extChartAt α hus) hvs hz).trans
    (integral_iUnion_fintype hv hdisj fun i ↦ hfu.mono_set (Subset.trans (subset_iUnion v i) hvs))

private theorem densityCoverIntegral_eq [IsManifold I 1 M] (μ : RoughDensity I M k)
    (hi : IntegrableDensity μ) (b : Module.Basis (Fin k) ℝ E) {s t : Set M}
    (c : DensityChartCover (I := I) s) (d : DensityChartCover (I := I) t)
    (hc : _root_.tsupport (α := Density E k) μ ⊆ s)
    (hd : _root_.tsupport (α := Density E k) μ ⊆ t) :
    densityCoverIntegral b μ c = densityCoverIntegral b μ d := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  unfold densityCoverIntegral
  simp_rw [integral_density_piece_refine μ hi b _ d hd
      (c.isChartMeasurable_piece _) (c.piece_subset _),
    integral_density_piece_refine μ hi b _ c hc
      (d.isChartMeasurable_piece _) (d.piece_subset _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have h := μ.setIntegral_inChartAt_changeChart b (c.center i) (d.center j)
    (s := c.piece i ∩ d.piece j) (fun x hx ↦ ⟨c.piece_subset i hx.1, d.piece_subset j hx.2⟩)
    (((c.isChartMeasurable_piece i).inter (d.isChartMeasurable_piece j)).image_extChartAt
      (c.center i) (inter_subset_left.trans (c.piece_subset i))) b.addHaar
  simpa only [inter_comm] using h

private theorem densityCoverIntegral_eq_setIntegral_of_ae_support [IsManifold I 1 M]
    (μ : RoughDensity I M k) (b : Module.Basis (Fin k) ℝ E)
    (c : DensityChartCover (I := I) (_root_.tsupport (α := Density E k) μ))
    (hi : IntegrableDensity μ) (α : M)
    (hα : ∀ β : M, ∀ᵐ y ∂b.addHaar, y ∈ (extChartAt I β).target →
      y ∉ (extChartAt I β) '' ((extChartAt I β).source ∩ (extChartAt I α).source) →
        μ.inChartAt β y b = 0) :
    densityCoverIntegral b μ c =
      ∫ y in (extChartAt I α).target, μ.inChartAt α y b ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let e := extChartAt I α
  let s : Fin c.n → Set M := fun i ↦ c.piece i ∩ e.source
  have hs (i : Fin c.n) : IsChartMeasurable I (s i) :=
    (c.isChartMeasurable_piece i).inter
      (by simpa only [e, extChartAt_source] using
        (chartAt H α).open_source.isChartMeasurable (I := I))
  calc
    densityCoverIntegral b μ c =
        ∑ i, ∫ y in e '' s i, μ.inChartAt α y b ∂b.addHaar := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hzero : ∀ᵐ y ∂b.addHaar,
          y ∈ (extChartAt I (c.center i)) '' c.piece i \
            (extChartAt I (c.center i)) '' s i →
            μ.inChartAt (c.center i) y b = 0 := by
        filter_upwards [hα (c.center i)] with y hy hys
        obtain ⟨x, hx, rfl⟩ := hys.1
        have ht : extChartAt I (c.center i) x ∈ (extChartAt I (c.center i)).target :=
          (extChartAt I (c.center i)).map_source (c.piece_subset i hx)
        refine hy ht ?_
        rintro ⟨z, hz, heq⟩
        have hxz : x = z :=
          (extChartAt I (c.center i)).injOn (c.piece_subset i hx) hz.1 heq.symm
        exact hys.2 (mem_image_of_mem _ ⟨hx, hxz ▸ hz.2⟩)
      have heq := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := b.addHaar)
        (c.measurableSet_image_piece i).nullMeasurableSet
        (image_mono inter_subset_left) hzero
      exact heq.trans (μ.setIntegral_inChartAt_changeChart b (c.center i) α
        (s := s i) (fun _ hx ↦ ⟨c.piece_subset i hx.1, hx.2⟩)
        ((hs i).image_extChartAt (c.center i) (inter_subset_left.trans (c.piece_subset i)))
        b.addHaar)
    _ = ∫ y in e.target, μ.inChartAt α y b ∂b.addHaar := by
      have he := integral_density_piece_refine μ hi b α c Subset.rfl
        (by simpa only [extChartAt_source] using
          (chartAt H α).open_source.isChartMeasurable (I := I)) Subset.rfl
      have he' : (∑ i, ∫ y in e '' s i, μ.inChartAt α y b ∂b.addHaar) =
          ∫ y in e '' e.source, μ.inChartAt α y b ∂b.addHaar := by
        simpa only [e, s, inter_comm] using he.symm
      rw [he', e.image_source_eq_target]

end CoverIntegral

/-! ### Total orientation-free integral of a rough density -/

/-- The orientation-free total integral of a rough density on a manifold. It equals `0` unless `μ`
is integrable (`IntegrableDensity μ`). A finite open chart cover of `tsupport μ` is disjointed into
Borel coordinate pieces; no orientation, metric, Hausdorffness, or manifold measurable structure is
needed. -/
def integralDensity (μ : RoughDensity I M k) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact if hi : IntegrableDensity μ then
    let b := Classical.choice hi.2.1
    haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
    densityCoverIntegral b μ
      (chooseDensityChartCover (_root_.tsupport (α := Density E k) μ) hi.1)
  else 0

/-- A nonintegrable rough density has total integral `0`. -/
theorem integralDensity_eq_zero_of_not_integrable (μ : RoughDensity I M k)
    (hi : ¬IntegrableDensity μ) : integralDensity μ = 0 := by
  rw [integralDensity, dite_eq_right hi]

/-- A rough density without compact topological support has total integral `0`. -/
theorem integralDensity_eq_zero_of_not_isCompact (μ : RoughDensity I M k)
    (hc : ¬IsCompact (_root_.tsupport (α := Density E k) μ)) : integralDensity μ = 0 :=
  integralDensity_eq_zero_of_not_integrable μ fun hi ↦ hc hi.isCompact

private theorem integralDensity_eq_chooseCover [MeasurableSpace E] [BorelSpace E]
    (μ : RoughDensity I M k) (hi : IntegrableDensity μ) (b : Module.Basis (Fin k) ℝ E) :
    letI : FiniteDimensional ℝ E := Module.Finite.of_basis b
    integralDensity μ =
      densityCoverIntegral b μ
        (chooseDensityChartCover (_root_.tsupport (α := Density E k) μ) hi.isCompact) := by
  classical
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  rw [integralDensity, dite_eq_left hi]
  exact densityCoverIntegral_basis_eq (Classical.choice hi.2.1) b μ _

private theorem integralDensity_eq_coverIntegral [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] (μ : RoughDensity I M k) (hi : IntegrableDensity μ)
    (b : Module.Basis (Fin k) ℝ E) {s : Set M} (c : DensityChartCover (I := I) s)
    (hc : _root_.tsupport (α := Density E k) μ ⊆ s) :
    integralDensity μ = densityCoverIntegral b μ c := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  rw [integralDensity_eq_chooseCover μ hi b]
  exact densityCoverIntegral_eq μ hi b _ c Subset.rfl hc

/-- Any finite open chart cover of `tsupport μ` computes `integralDensity μ` as the sum of set
integrals over its disjointed Borel pieces, in any model basis `b`. -/
theorem integralDensity_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M k) (hi : IntegrableDensity μ)
    (b : Module.Basis (Fin k) ℝ E) {m : ℕ} (α : Fin m → M) (u : Fin m → Set M)
    (hu : ∀ i, IsOpen (u i)) (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : _root_.tsupport (α := Density E k) μ ⊆ ⋃ i, u i) :
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i,
        μ.inChartAt (α i) y b ∂b.addHaar :=
  integralDensity_eq_coverIntegral μ hi b ⟨m, α, u, hu, hs, hc⟩ Subset.rfl

/-- A compact manifold admits a finite disjoint chartwise Borel partition computing every
integrable rough density's integral, with no orientation or manifold measurable structure. -/
theorem exists_chart_partition_integralDensity [IsManifold I 1 M] [CompactSpace M]
    [MeasurableSpace E] [BorelSpace E] (b : Module.Basis (Fin k) ℝ E) :
    ∃ m : ℕ, ∃ α : Fin m → M, ∃ s : Fin m → Set M,
      (∀ i, IsChartMeasurable I (s i)) ∧
      (∀ i, s i ⊆ (extChartAt I (α i)).source) ∧
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ ∧
      ∀ μ : RoughDensity I M k, IntegrableDensity μ →
        integralDensity μ =
          ∑ i, ∫ y in (extChartAt I (α i)) '' s i, μ.inChartAt (α i) y b ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let c := chooseDensityChartCover (I := I) (univ : Set M) isCompact_univ
  refine ⟨c.n, c.center, c.piece, c.isChartMeasurable_piece, c.piece_subset,
    c.pairwise_disjoint, Subset.antisymm (subset_univ _) c.piece_covers, fun μ hi ↦ ?_⟩
  exact integralDensity_eq_coverIntegral μ hi b c (subset_univ _)

/-! ### Single-chart and model-space formulas -/

/-- A single preferred chart computes `integralDensity μ` whenever `μ` vanishes outside that chart's
source up to a chartwise null set. -/
theorem integralDensity_eq_setIntegral_of_ae_support [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M k) (hi : IntegrableDensity μ)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (hs : IsNullSet I ({x | μ x ≠ 0} \ (extChartAt I α).source)) :
    integralDensity μ =
      ∫ y in (extChartAt I α).target, μ.inChartAt α y b ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  rw [integralDensity_eq_chooseCover μ hi b]
  refine densityCoverIntegral_eq_setIntegral_of_ae_support μ b _ hi α fun β ↦ ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hs.chartwise β b.addHaar)] with y hy ht ho
  have hz : μ ((extChartAt I β).symm y) = 0 := by
    by_contra hn
    refine hy ⟨(extChartAt I β).symm y, ⟨⟨hn, fun ha ↦ ?_⟩,
      (extChartAt I β).map_target ht⟩, (extChartAt I β).right_inv ht⟩
    exact ho ⟨(extChartAt I β).symm y,
      ⟨(extChartAt I β).map_target ht, ha⟩, (extChartAt I β).right_inv ht⟩
  rw [RoughDensity.inChartAt_apply, hz]
  rfl

/-- An integrable rough density whose topological support lies inside a preferred chart has total
integral equal to its coordinate set integral over that chart's target. -/
theorem integralDensity_eq_setIntegral_of_tsupport_subset [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M k) (hi : IntegrableDensity μ)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (hs : _root_.tsupport (α := Density E k) μ ⊆ (extChartAt I α).source) :
    integralDensity μ =
      ∫ y in (extChartAt I α).target, μ.inChartAt α y b ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  refine integralDensity_eq_setIntegral_of_ae_support μ hi b α
    ((isNullSet_boundary (I := I)).mono fun x hx ↦ ?_)
  exact False.elim (hx.2 (hs (_root_.subset_tsupport (α := Density E k) μ hx.1)))

/-- Over a normed model space `𝓘(ℝ, E)`, the orientation-free integral of any integrable rough
density equals the Bochner integral of its evaluation on any basis `b` against `b.addHaar`. -/
theorem IntegrableDensity.integralDensity_model_eq_integral [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity 𝓘(ℝ, E) E k} (hi : IntegrableDensity μ)
    (b : Module.Basis (Fin k) ℝ E) :
    integralDensity μ = ∫ x, μ x b ∂b.addHaar := by
  rw [integralDensity_eq_setIntegral_of_tsupport_subset μ hi b 0 (by simp)]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target, Measure.restrict_univ,
    RoughDensity.inChartAt_model]
  rfl

/-- On `ℝ` with model `𝓘(ℝ, ℝ)`, the orientation-free integral of an integrable `1`-density is the
Lebesgue integral of its evaluation on the unit vector `fun _ ↦ 1`. -/
theorem IntegrableDensity.integralDensity_real_eq_integral {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1}
    (hi : IntegrableDensity μ) :
    integralDensity μ = ∫ t, μ t fun _ ↦ 1 := by
  rw [hi.integralDensity_model_eq_integral (Module.Basis.singleton (Fin 1) ℝ),
    Module.Basis.addHaar_singleton, Module.Basis.coe_singleton]
  rfl

/-! ### Linearity of `integralDensity` -/

/-- The zero rough density has integral `0`. -/
@[simp]
theorem integralDensity_zero : integralDensity (0 : RoughDensity I M k) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity (0 : RoughDensity I M k)
  · obtain ⟨b⟩ := hi.2.1
    have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    rw [integralDensity_eq_chooseCover _ hi b, densityCoverIntegral_zero]
  · exact integralDensity_eq_zero_of_not_integrable _ hi

/-- Constant scalar multiplication commutes with `integralDensity` unconditionally (including for
nonintegrable rough densities). -/
theorem integralDensity_smul (c : ℝ) (μ : RoughDensity I M k) :
    integralDensity (c • μ) = c * integralDensity μ := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity μ
  · have hi' : IntegrableDensity (c • μ) := (integrableDensity_smul_iff c μ hc).mpr hi
    obtain ⟨b⟩ := hi.2.1
    have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    rw [integralDensity_eq_chooseCover _ hi' b, integralDensity_eq_chooseCover _ hi b,
      densityCoverIntegral_smul]
    exact congrArg (c * ·)
      (densityCoverIntegral_choose_eq b μ hi'.isCompact hi.isCompact
        (RoughDensity.tsupport_smul c μ hc))
  · have hi' : ¬IntegrableDensity (c • μ) :=
      fun h ↦ hi ((integrableDensity_smul_iff c μ hc).mp h)
    rw [integralDensity_eq_zero_of_not_integrable _ hi',
      integralDensity_eq_zero_of_not_integrable _ hi, mul_zero]

/-- Negating a rough density negates its integral unconditionally. -/
@[simp]
theorem integralDensity_neg (μ : RoughDensity I M k) :
    integralDensity (-μ) = -integralDensity μ := by
  rw [← neg_one_smul ℝ μ, integralDensity_smul, neg_one_mul]

/-- `integralDensity` is additive on integrable rough densities. -/
theorem integralDensity_add_of_integrable [IsManifold I 1 M] {μ ν : RoughDensity I M k}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ + ν) = integralDensity μ + integralDensity ν := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hμ.2.1
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let c := chooseDensityChartCover (I := I)
    (_root_.tsupport (α := Density E k) μ ∪ _root_.tsupport (α := Density E k) ν)
    (hμ.isCompact.union hν.isCompact)
  -- Identify tangent fibres with `E` so fixed-codomain `tsupport_add` applies.
  rw [integralDensity_eq_coverIntegral _ (hμ.add hν) b c
      (_root_.tsupport_add (show M → Density E k from μ) ν),
    integralDensity_eq_coverIntegral _ hμ b c subset_union_left,
    integralDensity_eq_coverIntegral _ hν b c subset_union_right,
    densityCoverIntegral_add b μ ν hμ hν c]

/-- `integralDensity` respects subtraction of integrable rough densities. -/
theorem integralDensity_sub_of_integrable [IsManifold I 1 M] {μ ν : RoughDensity I M k}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ - ν) = integralDensity μ - integralDensity ν := by
  rw [sub_eq_add_neg, integralDensity_add_of_integrable hμ hν.neg, integralDensity_neg,
    sub_eq_add_neg]

/-- `integralDensity` commutes with finite sums of integrable rough densities. -/
theorem integralDensity_sum [IsManifold I 1 M] {ι : Type*}
    (μ : ι → RoughDensity I M k) (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    integralDensity (∑ i ∈ s, μ i) = ∑ i ∈ s, integralDensity (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨b⟩ := (hμ i (Finset.mem_insert_self i s)).2.1
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integralDensity_add_of_integrable (hμ i (Finset.mem_insert_self i s))
        (IntegrableDensity.sum b μ s fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)]

/-! ### Nonnegativity, monotonicity, and strict positivity -/

private theorem nonneg_inChartAt {μ : RoughDensity I M k}
    (hμ : ∀ x (v : Fin k → TangentSpace I x), 0 ≤ μ x v) (α : M) (y : E) (v : Fin k → E) :
    0 ≤ μ.inChartAt α y v := by
  rw [RoughDensity.inChartAt_apply]
  exact hμ _ _

/-- Pointwise nonnegative rough densities have nonnegative integral in every dimension (including
`k = 0`) and without regularity or integrability hypotheses. -/
theorem integralDensity_nonneg {μ : RoughDensity I M k}
    (hμ : ∀ x (v : Fin k → TangentSpace I x), 0 ≤ μ x v) :
    0 ≤ integralDensity μ := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity μ
  · obtain ⟨b⟩ := hi.2.1
    have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    rw [integralDensity_eq_chooseCover μ hi b]
    exact Finset.sum_nonneg fun i _ ↦ integral_nonneg fun y ↦ nonneg_inChartAt hμ _ y b
  · rw [integralDensity_eq_zero_of_not_integrable μ hi]

/-- `integralDensity` is monotone on integrable rough densities. -/
theorem integralDensity_mono_of_integrable [IsManifold I 1 M] {μ ν : RoughDensity I M k}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (h : ∀ x (v : Fin k → TangentSpace I x), μ x v ≤ ν x v) :
    integralDensity μ ≤ integralDensity ν := by
  rw [← sub_nonneg, ← integralDensity_sub_of_integrable hν hμ]
  exact integralDensity_nonneg fun x v ↦ sub_nonneg.mpr (h x v)

/-- Triangle-inequality bound for `integralDensity` on integrable rough densities. -/
theorem abs_integralDensity_le_of_integrable [IsManifold I 1 M] {μ ν : RoughDensity I M k}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (h : ∀ x (v : Fin k → TangentSpace I x), |μ x v| ≤ ν x v) :
    |integralDensity μ| ≤ integralDensity ν := by
  refine abs_le.mpr ⟨?_, integralDensity_mono_of_integrable hμ hν fun x v ↦ (abs_le.mp (h x v)).2⟩
  rw [← integralDensity_neg]
  exact integralDensity_mono_of_integrable hν.neg hμ fun x v ↦ (abs_le.mp (h x v)).1

/-- **Positivity of density integration** (Lee, Proposition 16.40): a compactly supported rough
density with continuous coordinate expressions on chart targets, everywhere nonnegative and strictly
positive on at least one tangent tuple, has strictly positive integral. Applies in every dimension
(including `k = 0`) and on manifolds with boundary or corners. -/
theorem integralDensity_pos [IsManifold I 1 M] {μ : RoughDensity I M k}
    (hc : IsCompact (_root_.tsupport (α := Density E k) μ))
    (b : Module.Basis (Fin k) ℝ E)
    (hcont : ∀ α : M, ContinuousOn (μ.inChartAt α) (extChartAt I α).target)
    (hnn : ∀ x (v : Fin k → TangentSpace I x), 0 ≤ μ x v)
    (hpos : ∃ x, ∃ v : Fin k → TangentSpace I x, 0 < μ x v) :
    0 < integralDensity μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  have hi : IntegrableDensity μ := μ.integrableDensity_of_continuousOn_inChartAt hc b hcont
  obtain ⟨x₀, v₀, hμ₀⟩ := hpos
  obtain ⟨m, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  let α' : Fin (m + 1) → M := Fin.cons x₀ α
  let u' : Fin (m + 1) → Set M := Fin.cons (extChartAt I x₀).source u
  have hu' : ∀ i, IsOpen (u' i) ∧ u' i ⊆ (extChartAt I (α' i)).source :=
    Fin.cases (by simpa [α', u'] using isOpen_extChartAt_source (I := I) x₀)
      fun i ↦ by simpa [α', u'] using And.intro (hu i).1 (hu i).2.1
  have hcover' : _root_.tsupport (α := Density E k) μ ⊆ ⋃ i, u' i :=
    hcover.trans (iUnion_subset fun i ↦ by simpa [u'] using subset_iUnion u' i.succ)
  rw [integralDensity_eq_sum_disjointed_chart_integrals μ hi b α' u' (fun i ↦ (hu' i).1)
    (fun i ↦ (hu' i).2) hcover', Fin.sum_univ_succ]
  refine add_pos_of_pos_of_nonneg ?_
    (Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun y ↦ nonneg_inChartAt hnn _ y b)
  have hpiece : (extChartAt I (α' 0)) '' disjointed u' 0 = (extChartAt I x₀).target := by
    rw [← bot_eq_zero, disjointed_bot, bot_eq_zero]
    simp only [α', u', Fin.cons_zero]
    exact (extChartAt I x₀).image_source_eq_target
  rw [hpiece]
  have hb₀ : 0 < μ x₀ b := by
    -- Expand `μ x₀ v₀` in the basis `b` of `TangentSpace I x₀ = E` to isolate `0 < μ x₀ b`.
    have hdet := (μ x₀).apply_eq_abs_det_mul b v₀
    rw [hdet] at hμ₀
    by_contra! hle
    exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hle) hμ₀
  have hy₀ : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (mem_extChartAt_source x₀)
  have hg₀ : 0 < μ.inChartAt x₀ (extChartAt I x₀ x₀) b := by
    rwa [RoughDensity.inChartAt_extChartAt_self]
  exact setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target (μ := b.addHaar) x₀
    (fun y ↦ nonneg_inChartAt hnn x₀ y b) (((integrableDensity_iff μ).mp hi).2.2 b x₀)
    ((Density.continuous_eval b).comp_continuousOn (hcont x₀)) hy₀ hg₀

/-! ### Continuous and smooth sections of `DensityBundle` -/

section DensityBundle

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- A continuous section of `DensityBundle I M` has continuous coordinate expressions on all
preferred chart targets. -/
theorem RoughDensity.continuousOn_inChartAt_of_continuous_section
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ Bundle.TotalSpace.mk' ℝ x (μ x)) (α : M) :
    ContinuousOn (RoughDensity.inChartAt (I := I) μ α) (extChartAt I α).target := by
  let b := Module.finBasis ℝ E
  let e := (trivializationAt E (TangentSpace I) α).density
  let s : M → Bundle.TotalSpace ℝ (DensityBundle I M) := fun x ↦ Bundle.TotalSpace.mk' ℝ x (μ x)
  have hebase : e.baseSet = (extChartAt I α).source := by
    dsimp only [e]
    rw [Bundle.Trivialization.density_baseSet, extChartAt_source]
    exact TangentBundle.trivializationAt_baseSet α
  have htriv : ContinuousOn (fun x ↦ (e (s x)).2) (extChartAt I α).source := by
    rw [← hebase]
    exact continuous_snd.comp_continuousOn
      (e.continuousOn_toFun.comp hμ.continuousOn fun x hx ↦ e.mem_source.mpr hx)
  have hcomp : ContinuousOn (fun y ↦ (e (s ((extChartAt I α).symm y))).2)
      (extChartAt I α).target :=
    htriv.comp (continuousOn_extChartAt_symm (I := I) α) fun y hy ↦
      (extChartAt I α).map_target hy
  have hcoeff : ContinuousOn (fun y ↦ RoughDensity.inChartAt (I := I) μ α y b)
      (extChartAt I α).target := by
    refine hcomp.congr fun y hy ↦ ?_
    dsimp only
    have hx : (extChartAt I α).symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    have hd := congrArg Prod.snd (Bundle.Trivialization.density_apply
      (trivializationAt E (TangentSpace I) α) (s ((extChartAt I α).symm y)))
    dsimp only [s] at hd
    rw [hd, ← RoughDensity.inChartAt_trivializationAt_apply (I := I) μ α hx b,
      (extChartAt I α).right_inv hy]
  refine (b.densityContinuousLinearEquiv.symm.continuous.comp_continuousOn hcoeff).congr
    fun y _ ↦ ?_
  dsimp only [Function.comp_def]
  rw [← b.densityContinuousLinearEquiv_apply]
  exact (b.densityContinuousLinearEquiv.symm_apply_apply
    (RoughDensity.inChartAt (I := I) μ α y)).symm

/-- Every compactly supported continuous section of `DensityBundle I M` is integrable. -/
theorem RoughDensity.integrableDensity_of_continuous_section
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ Bundle.TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (Module.finrank ℝ E)) μ)) :
    IntegrableDensity (I := I) μ :=
  RoughDensity.integrableDensity_of_continuousOn_inChartAt hc (Module.finBasis ℝ E)
    (RoughDensity.continuousOn_inChartAt_of_continuous_section hμ)

/-- Every compactly supported `C^n` section of `DensityBundle I M` is integrable. -/
theorem RoughDensity.integrableDensity_of_contMDiff_section {n : ℕ∞ω}
    {μ : (x : M) → DensityBundle I M x}
    (hμ : ContMDiff I (I.prod 𝓘(ℝ)) n fun x ↦ Bundle.TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (Module.finrank ℝ E)) μ)) :
    IntegrableDensity (I := I) μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ.continuous hc

/-- A compactly supported continuous section of `DensityBundle I M` that is everywhere nonnegative
and positive at one tangent tuple has strictly positive integral. -/
theorem integralDensity_pos_of_continuous_section
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ Bundle.TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (Module.finrank ℝ E)) μ))
    (hnn : ∀ x (v : Fin (Module.finrank ℝ E) → TangentSpace I x), 0 ≤ μ x v)
    (hpos : ∃ x, ∃ v : Fin (Module.finrank ℝ E) → TangentSpace I x, 0 < μ x v) :
    0 < integralDensity (I := I) μ :=
  integralDensity_pos hc (Module.finBasis ℝ E)
    (RoughDensity.continuousOn_inChartAt_of_continuous_section hμ) hnn hpos

end DensityBundle

end TauCeti
