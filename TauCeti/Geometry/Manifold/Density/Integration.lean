/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Order.Disjointed

/-!
# Orientation-free integration of densities on manifolds

A rough density `μ` on a manifold `M` is integrable (`TauCeti.IntegrableDensity`) when it has
compact topological support, the model space `E` admits a basis of cardinality `m`, and in every
preferred chart and model basis the zero-extended scalar coefficient `μ.coeffInChartAt b α` is
integrable against `b.addHaar`. No orientation, metric, Hausdorff hypothesis, or measurable-space
structure on `M` is assumed, and manifolds with boundary and corners are included.

Its total integral `TauCeti.integralDensity μ` is defined by summing the normalized Haar set
integrals of `μ.coeffInChartAt` over the disjointed Borel coordinate pieces of a finite open chart
cover of the support, returning `0` when `μ` is not integrable. Common refinement and the chart
Jacobian theorem make the sum independent of both the cover and the model basis. In particular:

* Any finite open chart cover computes `integralDensity` via its disjointed coordinate pieces
  (`TauCeti.integralDensity_eq_sum_disjointed_chart_integrals`), and any partition of unity
  decomposes `integralDensity μ` into the finite sum
  `∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x)`
  (`TauCeti.integralDensity_eq_finsum_partitionOfUnity`).
* On an oriented manifold, oriented top-form integration reduces unconditionally to density
  integration (`TauCeti.integralTopForm_eq_integralDensity`):
  `integralTopForm o φ = integralDensity (φ.toDensity o)`.
* Unlike top-form positivity, nonnegativity and strict positivity of `integralDensity` hold in
  every dimension `m : ℕ`, including dimension zero (`TauCeti.integralDensity_nonneg`,
  `TauCeti.integralDensity_pos`).

## Main definitions

* `TauCeti.IntegrableDensity`: intrinsic integrability predicate for rough densities.
* `TauCeti.integralDensity`: orientation-free total integral of a rough density on a manifold.

## Main results

* `TauCeti.RoughDensity.integrableDensity_of_open_cover`: open-cover criterion for integrability.
* `TauCeti.RoughDensity.integrableDensity_of_continuous_section`: every compactly supported
  continuous section of `TauCeti.DensityBundle` is integrable.
* `TauCeti.IntegrableDensity.fun_smul`: multiplication by a continuous scalar function preserves
  integrability without a Hausdorff assumption.
* `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals`,
  `TauCeti.integralDensity_eq_chartIntegral`,
  `TauCeti.integralDensity_eq_finsum_partitionOfUnity`: chart-cover, single-chart, and
  partition-of-unity formulas.
* `TauCeti.RoughForm.integrableDensity_toDensity_iff`,
  `TauCeti.integralTopForm_eq_integralDensity`: equivalence of integrability and equality of
  integrals for `φ.toDensity o`.
* `TauCeti.integralDensity_nonneg`, `TauCeti.integralDensity_pos`: nonnegativity and strict
  positivity of density integration in all dimensions.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Theorem 16.41
  and Proposition 16.42.
* The disjointed-chart-cover construction of `TauCeti.integralDensity` parallels the oriented
  construction of `TauCeti.integralTopForm` in
  `TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm`.
-/

noncomputable section

open Bundle MeasureTheory Set Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section Integrability

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {m : ℕ}

/-- A rough density is integrable when it has compact topological support and its zero-extended
chart coefficients are Haar-integrable in every preferred chart and model basis. -/
public def IntegrableDensity (μ : RoughDensity I M m) : Prop := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact IsCompact (_root_.tsupport (α := Density E m) μ) ∧
    Nonempty (Basis (Fin m) ℝ E) ∧
    ∀ (b : Basis (Fin m) ℝ E) (α : M),
      Integrable (μ.coeffInChartAt b α) b.addHaar

/-- Coordinate characterization of `IntegrableDensity` for any Borel measurable structure on the
model space. -/
public theorem integrableDensity_iff [MeasurableSpace E] [BorelSpace E]
    (μ : RoughDensity I M m) :
    IntegrableDensity μ ↔ IsCompact (_root_.tsupport (α := Density E m) μ) ∧
      Nonempty (Basis (Fin m) ℝ E) ∧
      ∀ (b : Basis (Fin m) ℝ E) (α : M),
        Integrable (μ.coeffInChartAt b α) b.addHaar := by
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  rfl

/-- Integrable rough densities have compact topological support. -/
public theorem IntegrableDensity.isCompact {μ : RoughDensity I M m}
    (hi : IntegrableDensity μ) : IsCompact (_root_.tsupport (α := Density E m) μ) :=
  hi.1

/-- An integrable rough density witnesses that the model space has a basis of cardinality `m`. -/
public theorem IntegrableDensity.nonempty_basis {μ : RoughDensity I M m}
    (hi : IntegrableDensity μ) : Nonempty (Basis (Fin m) ℝ E) :=
  hi.2.1

/-- Every chart coefficient of an integrable rough density is Haar-integrable. -/
public theorem IntegrableDensity.integrable_coeffInChartAt [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) (α : M) :
    Integrable (μ.coeffInChartAt b α) b.addHaar :=
  ((integrableDensity_iff μ).mp hi).2.2 b α

/-- Integrability on an open chart cover implies `IntegrableDensity`, using a single model basis
and assuming neither continuity nor orientability. -/
public theorem RoughDensity.integrableDensity_of_open_cover [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] {J : Type*} (μ : RoughDensity I M m)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (b : Basis (Fin m) ℝ E) (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i))
    (hsource : ∀ i, u i ⊆ (chartAt H (β i)).source)
    (hcover : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (μ.coeffInChartAt b (β i))
      ((extChartAt I (β i)) '' u i) b.addHaar) :
    IntegrableDensity μ := by
  classical
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover u hu hcover
  have hcover' : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i : t, u i := fun x hx ↦ by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hcoef (α : M) : Integrable (μ.coeffInChartAt b α) b.addHaar := by
    let s : t → Set M := fun i ↦ (extChartAt I α).source ∩ u i
    let A : t → Set E := fun i ↦ (extChartAt I α) '' s i
    have hA (i : t) : MeasurableSet (A i) :=
      (hu i).measurableSet_image_extChartAt_source_inter α
    have hpiece (i : t) : IntegrableOn (μ.coeffInChartAt b α) (A i) b.addHaar := by
      have hsub : s i ⊆ (extChartAt I α).source ∩ (extChartAt I (β i)).source := fun x hx ↦
        ⟨hx.1, by simpa only [extChartAt_source] using hsource i hx.2⟩
      exact (μ.coeffInChartAt_changeChart b α (β i) hsub (hA i) b.addHaar).2.mpr
        ((hlocal i).mono_set (image_mono inter_subset_right))
    have htotal : IntegrableOn (μ.coeffInChartAt b α) (⋃ i, A i) b.addHaar :=
      integrableOn_finite_iUnion.mpr hpiece
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp htotal
    intro y hy
    have ht' : y ∈ (extChartAt I α).target := μ.support_coeffInChartAt_subset_target b α hy
    have hne : μ ((extChartAt I α).symm y) ≠ 0 := by
      intro hz
      apply Function.mem_support.mp hy
      rw [μ.coeffInChartAt_apply_of_mem_target b α ht', RoughDensity.inChartAt_apply, hz]
      rfl
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      (hcover' (_root_.subset_tsupport (α := Density E m) μ hne))
    exact mem_iUnion.mpr ⟨i, ⟨(extChartAt I α).symm y,
      ⟨(extChartAt I α).map_target ht', hi⟩, (extChartAt I α).right_inv ht'⟩⟩
  rw [integrableDensity_iff]
  exact ⟨hc, ⟨b⟩, fun b' α ↦
    (μ.integrable_coeffInChartAt_basis_iff b b' α).mpr (hcoef α)⟩

/-- A compactly supported rough density supported inside one preferred chart is integrable if and
only if its coefficient in that chart and one model basis is Haar-integrable. -/
public theorem RoughDensity.integrableDensity_iff_of_tsupport_subset_chart
    [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M]
    {μ : RoughDensity I M m} (b : Basis (Fin m) ℝ E) (α : M)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (chartAt H α).source) :
    IntegrableDensity μ ↔ Integrable (μ.coeffInChartAt b α) b.addHaar := by
  refine ⟨fun h ↦ h.integrable_coeffInChartAt b α, fun hi ↦ ?_⟩
  exact μ.integrableDensity_of_open_cover hc b (fun _ : Unit ↦ α)
    (fun _ ↦ (chartAt H α).source) (fun _ ↦ (chartAt H α).open_source) (fun _ ↦ Subset.rfl)
    (fun x hx ↦ mem_iUnion.mpr ⟨(), hs hx⟩) (fun _ ↦ hi.integrableOn)

/-- Multiplication by a nonzero constant preserves `IntegrableDensity`. -/
public theorem integrableDensity_smul_iff (c : ℝ) (μ : RoughDensity I M m) (hc : c ≠ 0) :
    IntegrableDensity (c • μ) ↔ IntegrableDensity μ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff, integrableDensity_iff, RoughDensity.tsupport_smul c μ hc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun b ↦ forall_congr' fun α ↦ ?_))
  simp_rw [funext (RoughDensity.coeffInChartAt_smul c μ b α)]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _

/-- The sum of two integrable rough densities is integrable. -/
public theorem IntegrableDensity.add {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    IntegrableDensity (μ + ν) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ hν ⊢
  refine ⟨RoughDensity.isCompact_tsupport_add hμ.1 hν.1, hμ.2.1, fun b α ↦ ?_⟩
  rw [funext (RoughDensity.coeffInChartAt_add μ ν b α)]
  exact (hμ.2.2 b α).add (hν.2.2 b α)

/-- The zero density is integrable whenever the model space admits a basis of cardinality `m`. -/
public theorem IntegrableDensity.zero (b : Basis (Fin m) ℝ E) :
    IntegrableDensity (0 : RoughDensity I M m) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff]
  refine ⟨RoughDensity.isCompact_tsupport_zero, ⟨b⟩, fun b' α ↦ ?_⟩
  rw [RoughDensity.coeffInChartAt_zero]
  exact integrable_zero E ℝ b'.addHaar

/-- Constant scalar multiplication preserves `IntegrableDensity`. -/
public theorem IntegrableDensity.smul {μ : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (c : ℝ) : IntegrableDensity (c • μ) := by
  by_cases hc : c = 0
  · subst c
    obtain ⟨b⟩ := hμ.nonempty_basis
    simpa only [zero_smul] using IntegrableDensity.zero (I := I) (M := M) b
  · exact (integrableDensity_smul_iff c μ hc).mpr hμ

/-- Negation preserves `IntegrableDensity`. -/
public theorem IntegrableDensity.neg {μ : RoughDensity I M m}
    (hμ : IntegrableDensity μ) : IntegrableDensity (-μ) := by
  simpa only [neg_one_smul] using hμ.smul (-1)

/-- Subtraction preserves `IntegrableDensity`. -/
public theorem IntegrableDensity.sub {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    IntegrableDensity (μ - ν) := by
  rw [sub_eq_add_neg]
  exact hμ.add hν.neg

/-- Finite sums of integrable rough densities are integrable. -/
public theorem IntegrableDensity.sum {ι : Type*} (b : Basis (Fin m) ℝ E)
    (μ : ι → RoughDensity I M m) (s : Finset ι)
    (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    IntegrableDensity (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntegrableDensity.zero (I := I) (M := M) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hμ i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj))

/-- Pointwise multiplication by a continuous scalar function preserves `IntegrableDensity`, with no
Hausdorff assumption on the manifold: clamping the scalar function to its compact-support bound
produces a globally bounded continuous multiplier agreeing with `f` on `tsupport μ`. -/
public theorem IntegrableDensity.fun_smul {μ : RoughDensity I M m}
    (hμ : IntegrableDensity μ) {f : M → ℝ} (hf : Continuous f) :
    IntegrableDensity (fun x ↦ f x • μ x) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let K := _root_.tsupport (α := Density E m) μ
  obtain ⟨B, hB⟩ := hμ.isCompact.exists_bound_of_continuousOn hf.continuousOn
  let C : ℝ := max B 0
  have hC0 : 0 ≤ C := le_max_right B 0
  let g : M → ℝ := fun x ↦ max (-C) (min C (f x))
  have hg_cont : Continuous g := continuous_const.max (continuous_const.min hf)
  have hg_bound (x : M) : ‖g x‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (neg_le_self hC0) (min_le_left _ _)⟩
  have hgf : (fun x ↦ g x • μ x : RoughDensity I M m) = fun x ↦ f x • μ x := by
    funext x
    by_cases hx : x ∈ K
    · have hfx : |f x| ≤ C := by
        simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_max_left B 0)
      obtain ⟨hlow, hhigh⟩ := abs_le.mp hfx
      have hgx : g x = f x := by
        simp only [g, min_eq_right hhigh, max_eq_right hlow]
      rw [hgx]
    · have hz : μ x = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hx
      simp [hz]
  rw [← hgf, integrableDensity_iff]
  refine ⟨hμ.isCompact.of_isClosed_subset (_root_.isClosed_tsupport _)
    (RoughDensity.tsupport_fun_smul_subset g μ), hμ.nonempty_basis, fun b α ↦ ?_⟩
  let S := (extChartAt I α).target
  have hm : MeasurableSet S := measurableSet_extChartAt_target α
  have hmeas : AEStronglyMeasurable (fun y ↦ g ((extChartAt I α).symm y))
      (b.addHaar.restrict S) :=
    (hg_cont.comp_continuousOn (continuousOn_extChartAt_symm α)).aestronglyMeasurable hm
  have hbd : ∀ᵐ y ∂b.addHaar.restrict S, ‖g ((extChartAt I α).symm y)‖ ≤ C :=
    Filter.Eventually.of_forall fun y ↦ hg_bound _
  refine (integrableOn_iff_integrable_of_support_subset
    (RoughDensity.support_coeffInChartAt_subset_target _ b α)).mp ?_
  exact IntegrableOn.congr_fun
    ((hμ.integrable_coeffInChartAt b α).integrableOn.bdd_mul hmeas hbd)
    (fun y _ ↦ (RoughDensity.coeffInChartAt_fun_smul g μ b α y).symm) hm

/-- A compactly supported rough density whose coordinate expression is continuous on every
preferred chart target is integrable. -/
public theorem RoughDensity.integrableDensity_of_continuousOn_inChartAt [IsManifold I 1 M]
    {μ : RoughDensity I M m}
    (hμ : ∀ α, ContinuousOn (μ.inChartAt α) (extChartAt I α).target)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (b : Basis (Fin m) ℝ E) :
    IntegrableDensity μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨k, β, u, B, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  refine μ.integrableDensity_of_open_cover hc b β u (fun i ↦ (hu i).1)
    (fun i ↦ by simpa only [extChartAt_source] using (hu i).2.1) hcover fun i ↦ ?_
  exact (((μ.continuousOn_coeffInChartAt b (β i) (hμ (β i))).mono
    (hu i).2.2.2.1).integrableOn_compact (hu i).2.2.1 (μ := b.addHaar)).mono_set (hu i).2.2.2.2

/-- Every compactly supported continuous section of `TauCeti.DensityBundle` is integrable. -/
public theorem RoughDensity.integrableDensity_of_continuous_section
    [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ)) :
    IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuousOn_inChartAt
    (RoughDensity.continuousOn_inChartAt_of_continuous_section hμ) hc (finBasis ℝ E)

/-- On a compact manifold, every continuous section of `TauCeti.DensityBundle` is integrable. -/
public theorem RoughDensity.integrableDensity_of_continuous_section_of_compactSpace
    [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompactSpace M]
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x)) :
    IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ (_root_.isClosed_tsupport _).isCompact

/-- Every compactly supported `C^n` section of `TauCeti.DensityBundle` is integrable. -/
public theorem RoughDensity.integrableDensity_of_contMDiff_section
    [FiniteDimensional ℝ E] [IsManifold I 1 M] {n : ℕ∞ω}
    {μ : (x : M) → DensityBundle I M x}
    (hμ : ContMDiff I (I.prod 𝓘(ℝ)) n fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ)) :
    IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ.continuous hc

end Integrability

section CoverConstruction

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {m : ℕ}

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
    Pairwise fun i j ↦ Disjoint (c.piece i) (c.piece j) :=
  disjoint_disjointed c.domain

section WithMeasure

variable [MeasurableSpace E] [BorelSpace E]

private theorem DensityChartCover.isChartMeasurable_piece {s : Set M}
    (c : DensityChartCover (I := I) s) (i : Fin c.n) :
    IsChartMeasurable I (c.piece i) := by
  rw [DensityChartCover.piece, disjointed_apply]
  have ho : IsOpen ((Finset.Iio i).sup c.domain) := by
    rw [Finset.sup_set_eq_biUnion]
    exact isOpen_biUnion fun j _ ↦ c.isOpen_domain j
  exact (c.isOpen_domain i).isChartMeasurable.diff ho.isChartMeasurable

private theorem DensityChartCover.measurableSet_image_piece {s : Set M}
    (c : DensityChartCover (I := I) s) (i : Fin c.n) :
    MeasurableSet ((extChartAt I (c.center i)) '' c.piece i) :=
  (c.isChartMeasurable_piece i).image_extChartAt (c.center i) (c.piece_subset i)

private def densityCoverIntegral {s : Set M} (b : Basis (Fin m) ℝ E)
    (μ : RoughDensity I M m) (c : DensityChartCover (I := I) s) : ℝ :=
  ∑ i, ∫ y in (extChartAt I (c.center i)) '' c.piece i,
    μ.coeffInChartAt b (c.center i) y ∂b.addHaar

private theorem densityCoverIntegral_basis_eq {s : Set M} (b b' : Basis (Fin m) ℝ E)
    (μ : RoughDensity I M m) (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b μ c = densityCoverIntegral b' μ c :=
  Finset.sum_congr rfl fun i _ ↦ μ.setIntegral_coeffInChartAt_basis_eq b b' (c.center i) _

private theorem densityCoverIntegral_zero {s : Set M} (b : Basis (Fin m) ℝ E)
    (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b (0 : RoughDensity I M m) c = 0 := by
  simp [densityCoverIntegral]

private theorem densityCoverIntegral_smul {s : Set M} (b : Basis (Fin m) ℝ E)
    (r : ℝ) (μ : RoughDensity I M m) (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b (r • μ) c = r * densityCoverIntegral b μ c := by
  unfold densityCoverIntegral
  simp_rw [RoughDensity.coeffInChartAt_smul, integral_const_mul, ← Finset.mul_sum]

private theorem densityCoverIntegral_choose_eq [ProperSpace E]
    (b : Basis (Fin m) ℝ E) (μ : RoughDensity I M m) {s t : Set M}
    (hs : IsCompact s) (ht : IsCompact t) (hst : s = t) :
    densityCoverIntegral b μ (chooseDensityChartCover (I := I) s hs) =
      densityCoverIntegral b μ (chooseDensityChartCover (I := I) t ht) := by
  subst t
  rfl

private theorem densityCoverIntegral_add {s : Set M} (b : Basis (Fin m) ℝ E)
    (μ ν : RoughDensity I M m) (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (c : DensityChartCover (I := I) s) :
    densityCoverIntegral b (μ + ν) c =
      densityCoverIntegral b μ c + densityCoverIntegral b ν c := by
  unfold densityCoverIntegral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp_rw [RoughDensity.coeffInChartAt_add]
  exact integral_add (hμ.integrable_coeffInChartAt b (c.center i)).integrableOn
    (hν.integrable_coeffInChartAt b (c.center i)).integrableOn

private theorem integral_density_piece_refine (μ : RoughDensity I M m)
    (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) (α : M) {s : Set M}
    (c : DensityChartCover (I := I) s) (hc : _root_.tsupport (α := Density E m) μ ⊆ s)
    {u : Set M} (hu : IsChartMeasurable I u) (hus : u ⊆ (extChartAt I α).source) :
    (∫ y in (extChartAt I α) '' u, μ.coeffInChartAt b α y ∂b.addHaar) =
      ∑ i, ∫ y in (extChartAt I α) '' (u ∩ c.piece i),
        μ.coeffInChartAt b α y ∂b.addHaar := by
  let e := extChartAt I α
  let f := μ.coeffInChartAt b α
  let v : Fin c.n → Set E := fun i ↦ e '' (u ∩ c.piece i)
  have hv (i : Fin c.n) : MeasurableSet (v i) :=
    (hu.inter (c.isChartMeasurable_piece i)).image_extChartAt α (inter_subset_left.trans hus)
  have hvs : (⋃ i, v i) ⊆ e '' u := iUnion_subset fun _ ↦ image_mono inter_subset_left
  have hdisj : Pairwise fun i j ↦ Disjoint (v i) (v j) := fun i j hij ↦
    ((c.pairwise_disjoint hij).mono inter_subset_right inter_subset_right).image e.injOn
      (inter_subset_left.trans hus) (inter_subset_left.trans hus)
  have hf : Integrable f b.addHaar := hi.integrable_coeffInChartAt b α
  have hz : ∀ y ∈ e '' u \ ⋃ i, v i, f y = 0 := by
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    have hx0 : x ∉ _root_.tsupport (α := Density E m) μ := fun ht ↦ by
      obtain ⟨i, hi'⟩ := mem_iUnion.mp (c.piece_covers (hc ht))
      exact hn (mem_iUnion.mpr ⟨i, mem_image_of_mem e ⟨hx, hi'⟩⟩)
    have hμ : μ x = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hx0
    dsimp only [f, e]
    rw [μ.coeffInChartAt_apply_of_mem_source b α (hus hx), RoughDensity.inChartAt_apply,
      e.left_inv (hus hx), hμ]
    rfl
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hu.image_extChartAt α hus) hvs hz).trans
    (integral_iUnion_fintype hv hdisj fun _ ↦ hf.integrableOn)

private theorem densityCoverIntegral_eq [IsManifold I 1 M] (μ : RoughDensity I M m)
    (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) {s t : Set M}
    (c : DensityChartCover (I := I) s) (d : DensityChartCover (I := I) t)
    (hc : _root_.tsupport (α := Density E m) μ ⊆ s)
    (hd : _root_.tsupport (α := Density E m) μ ⊆ t) :
    densityCoverIntegral b μ c = densityCoverIntegral b μ d := by
  unfold densityCoverIntegral
  simp_rw [integral_density_piece_refine μ hi b _ d hd
      (c.isChartMeasurable_piece _) (c.piece_subset _),
    integral_density_piece_refine μ hi b _ c hc
      (d.isChartMeasurable_piece _) (d.piece_subset _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have h := (μ.coeffInChartAt_changeChart b (c.center i) (d.center j)
    (s := c.piece i ∩ d.piece j)
    (fun x hx ↦ ⟨c.piece_subset i hx.1, d.piece_subset j hx.2⟩)
    (((c.isChartMeasurable_piece i).inter (d.isChartMeasurable_piece j)).image_extChartAt
      (c.center i) (inter_subset_left.trans (c.piece_subset i))) b.addHaar).1
  simpa only [inter_comm] using h

private theorem densityCoverIntegral_eq_chartIntegral_of_ae_support [IsManifold I 1 M]
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (c : DensityChartCover (I := I) (_root_.tsupport (α := Density E m) μ))
    (hi : IntegrableDensity μ) (α : M)
    (hα : ∀ β : M, ∀ᵐ y ∂b.addHaar,
      y ∉ (extChartAt I β) '' ((extChartAt I β).source ∩ (extChartAt I α).source) →
        μ.coeffInChartAt b β y = 0) :
    densityCoverIntegral b μ c = ∫ y, μ.coeffInChartAt b α y ∂b.addHaar := by
  let e := extChartAt I α
  let f := μ.coeffInChartAt b α
  have he_meas : IsChartMeasurable I e.source := by
    dsimp only [e]
    simpa only [extChartAt_source] using (chartAt H α).open_source.isChartMeasurable (I := I)
  let s : Fin c.n → Set M := fun i ↦ c.piece i ∩ e.source
  have hs (i : Fin c.n) : IsChartMeasurable I (s i) :=
    (c.isChartMeasurable_piece i).inter he_meas
  rw [densityCoverIntegral]
  calc
    (∑ i, ∫ y in (extChartAt I (c.center i)) '' c.piece i,
        μ.coeffInChartAt b (c.center i) y ∂b.addHaar) =
      ∑ i, ∫ y in e '' s i, f y ∂b.addHaar := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hzero : ∀ᵐ y ∂b.addHaar,
          y ∈ (extChartAt I (c.center i)) '' c.piece i \
            (extChartAt I (c.center i)) '' s i →
            μ.coeffInChartAt b (c.center i) y = 0 := by
        filter_upwards [hα (c.center i)] with y hy hys
        obtain ⟨x, hx, rfl⟩ := hys.1
        apply hy
        rintro ⟨z, hz, he⟩
        have hxz : x = z := (extChartAt I (c.center i)).injOn (c.piece_subset i hx) hz.1 he.symm
        exact hys.2 (mem_image_of_mem _ ⟨hx, hxz ▸ hz.2⟩)
      have heq := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := b.addHaar)
        (c.measurableSet_image_piece i).nullMeasurableSet
        (image_mono inter_subset_left) hzero
      exact heq.trans ((μ.coeffInChartAt_changeChart b (c.center i) α (s := s i)
        (fun _ hx ↦ ⟨c.piece_subset i hx.1, hx.2⟩)
        ((hs i).image_extChartAt (c.center i) (inter_subset_left.trans (c.piece_subset i)))
        b.addHaar).1)
    _ = ∫ y, f y ∂b.addHaar := by
      have he : (∫ y in e '' e.source, f y ∂b.addHaar) =
          ∑ i, ∫ y in e '' (e.source ∩ c.piece i), f y ∂b.addHaar :=
        integral_density_piece_refine μ hi b α c Subset.rfl he_meas Subset.rfl
      have he' : (∑ i, ∫ y in e '' s i, f y ∂b.addHaar) =
          ∫ y in e '' e.source, f y ∂b.addHaar := by
        simpa only [s, inter_comm] using he.symm
      rw [he', e.image_source_eq_target]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
        Function.notMem_support.mp fun hn ↦
          hy (μ.support_coeffInChartAt_subset_target b α hn)

end WithMeasure

/-- The orientation-free total integral of a rough density `μ` on a manifold `M`. It is `0` unless
`μ` is compactly supported and integrable; when `IntegrableDensity μ` holds, a model basis from
`hi` supplies finite-dimensionality and normalized Haar measure on the disjointed Borel pieces of a
finite chart cover. Neither orientation, Hausdorffness, nor a measurable structure on `M` is
needed. -/
public def integralDensity (μ : RoughDensity I M m) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact if hi : IntegrableDensity μ then
    let b : Basis (Fin m) ℝ E := hi.nonempty_basis.some
    haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
    densityCoverIntegral b μ
      (chooseDensityChartCover (_root_.tsupport (α := Density E m) μ) hi.isCompact)
  else 0

/-- A nonintegrable rough density has zero total integral. -/
public theorem integralDensity_eq_zero_of_not_integrable (μ : RoughDensity I M m)
    (hi : ¬IntegrableDensity μ) : integralDensity μ = 0 := by
  rw [integralDensity, dite_eq_right hi]

/-- A rough density without compact support has zero total integral. -/
public theorem integralDensity_eq_zero_of_not_isCompact (μ : RoughDensity I M m)
    (hc : ¬IsCompact (_root_.tsupport (α := Density E m) μ)) :
    integralDensity μ = 0 :=
  integralDensity_eq_zero_of_not_integrable μ fun hi ↦ hc hi.isCompact

private theorem integralDensity_eq_choose [MeasurableSpace E] [BorelSpace E]
    (μ : RoughDensity I M m) (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) :
    integralDensity μ =
      (haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b;
        densityCoverIntegral b μ
          (chooseDensityChartCover (_root_.tsupport (α := Density E m) μ) hi.isCompact)) := by
  classical
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  rw [integralDensity, dite_eq_left hi]
  dsimp only
  let b₀ : Basis (Fin m) ℝ E := hi.nonempty_basis.some
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b₀
  exact densityCoverIntegral_basis_eq b₀ b μ _

private theorem integralDensity_eq_coverIntegral [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) {s : Set M} (c : DensityChartCover (I := I) s)
    (hc : _root_.tsupport (α := Density E m) μ ⊆ s) :
    integralDensity μ = densityCoverIntegral b μ c := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  rw [integralDensity_eq_choose μ hi b]
  exact densityCoverIntegral_eq μ hi b _ c Subset.rfl hc

/-- Any finite open chart cover computes `integralDensity` through its disjointed Borel coordinate
pieces, in any model basis and with no orientation data. -/
public theorem integralDensity_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) {k : ℕ} (α : Fin k → M) (u : Fin k → Set M)
    (hu : ∀ i, IsOpen (u i)) (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i) :
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i,
        μ.coeffInChartAt b (α i) y ∂b.addHaar := by
  let c : DensityChartCover (I := I) (_root_.tsupport (α := Density E m) μ) :=
    ⟨k, α, u, hu, hs, hc⟩
  exact integralDensity_eq_coverIntegral μ hi b c Subset.rfl

/-- A compact manifold admits a finite disjoint chartwise Borel partition computing every
integrable density integral, without installing a measurable structure or orientation on `M`. -/
public theorem exists_chart_partition_integralDensity [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [CompactSpace M] [MeasurableSpace E] [BorelSpace E] (b : Basis (Fin m) ℝ E) :
    ∃ k : ℕ, ∃ α : Fin k → M, ∃ s : Fin k → Set M,
      (∀ i, IsChartMeasurable I (s i)) ∧
      (∀ i, s i ⊆ (extChartAt I (α i)).source) ∧
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ ∧
      ∀ μ : RoughDensity I M m, IntegrableDensity μ →
        integralDensity μ =
          ∑ i, ∫ y in (extChartAt I (α i)) '' s i,
            μ.coeffInChartAt b (α i) y ∂b.addHaar := by
  let c := chooseDensityChartCover (I := I) (univ : Set M) isCompact_univ
  refine ⟨c.n, c.center, c.piece, c.isChartMeasurable_piece, c.piece_subset,
    c.pairwise_disjoint, Subset.antisymm (subset_univ _) c.piece_covers, fun μ hi ↦ ?_⟩
  exact integralDensity_eq_coverIntegral μ hi b c (subset_univ _)

/-- The zero density has zero integral. -/
@[simp]
public theorem integralDensity_zero : integralDensity (0 : RoughDensity I M m) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity (0 : RoughDensity I M m)
  · obtain ⟨b⟩ := hi.nonempty_basis
    rw [integralDensity_eq_choose _ hi b]
    have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    exact densityCoverIntegral_zero b _
  · exact integralDensity_eq_zero_of_not_integrable _ hi

/-- Constant scalar multiplication commutes with `integralDensity`, even for nonintegrable rough
densities. -/
public theorem integralDensity_smul (c : ℝ) (μ : RoughDensity I M m) :
    integralDensity (c • μ) = c * integralDensity μ := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity μ
  · have hi' := (integrableDensity_smul_iff c μ hc).mpr hi
    obtain ⟨b⟩ := hi.nonempty_basis
    have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    rw [integralDensity_eq_choose _ hi' b, integralDensity_eq_choose _ hi b,
      densityCoverIntegral_smul]
    exact congrArg (c * ·)
      (densityCoverIntegral_choose_eq b μ hi'.isCompact hi.isCompact
        (RoughDensity.tsupport_smul c μ hc))
  · have hi' : ¬IntegrableDensity (c • μ) :=
      fun h ↦ hi ((integrableDensity_smul_iff c μ hc).mp h)
    rw [integralDensity_eq_zero_of_not_integrable _ hi',
      integralDensity_eq_zero_of_not_integrable _ hi, mul_zero]

/-- Negation negates `integralDensity`, including for nonintegrable rough densities. -/
@[simp]
public theorem integralDensity_neg (μ : RoughDensity I M m) :
    integralDensity (-μ) = -integralDensity μ := by
  rw [← neg_one_smul ℝ μ, integralDensity_smul, neg_one_mul]

/-- `integralDensity` is additive on integrable rough densities. -/
public theorem integralDensity_add_of_integrable [IsManifold I 1 M]
    {μ ν : RoughDensity I M m} (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ + ν) = integralDensity μ + integralDensity ν := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hμ.nonempty_basis
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let c := chooseDensityChartCover (I := I)
    (_root_.tsupport (α := Density E m) μ ∪ _root_.tsupport (α := Density E m) ν)
    (hμ.isCompact.union hν.isCompact)
  -- Identify tangent fibres with `E` so `tsupport_add` applies at fixed codomain `Density E m`.
  rw [integralDensity_eq_coverIntegral _ (hμ.add hν) b c
      (_root_.tsupport_add (show M → Density E m from μ) ν),
    integralDensity_eq_coverIntegral _ hμ b c subset_union_left,
    integralDensity_eq_coverIntegral _ hν b c subset_union_right,
    densityCoverIntegral_add b μ ν hμ hν c]

/-- `integralDensity` respects subtraction of integrable rough densities. -/
public theorem integralDensity_sub_of_integrable [IsManifold I 1 M]
    {μ ν : RoughDensity I M m} (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ - ν) = integralDensity μ - integralDensity ν := by
  rw [sub_eq_add_neg, integralDensity_add_of_integrable hμ hν.neg, integralDensity_neg,
    sub_eq_add_neg]

/-- `integralDensity` commutes with finite sums of integrable rough densities. -/
public theorem integralDensity_sum [IsManifold I 1 M] {ι : Type*}
    (μ : ι → RoughDensity I M m) (s : Finset ι)
    (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    integralDensity (∑ i ∈ s, μ i) = ∑ i ∈ s, integralDensity (μ i) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  obtain ⟨b⟩ := (hμ i₀ hi₀).nonempty_basis
  clear i₀ hi₀
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integralDensity_add_of_integrable (hμ i (Finset.mem_insert_self i s))
        (IntegrableDensity.sum b μ s fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)]

/-- A partition of unity decomposes `integralDensity μ` into a finite sum of localized integrals,
with all terms outside the finite set vanishing. -/
public theorem integralDensity_eq_sum_partitionOfUnity [IsManifold I 1 M] {ι : Type*}
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (ρ : PartitionOfUnity ι M univ) :
    ∃ s : Finset ι,
      integralDensity μ = ∑ i ∈ s, integralDensity (fun x ↦ ρ i x • μ x) ∧
        ∀ i ∉ s, integralDensity (fun x ↦ ρ i x • μ x) = 0 := by
  obtain ⟨s, hsum, hzero⟩ := μ.exists_finset_partition_eq hi.isCompact ρ
  refine ⟨s, ?_, fun i his ↦ by rw [hzero i his, integralDensity_zero]⟩
  have hsum' : μ = ∑ i ∈ s, (fun x ↦ ρ i x • μ x : RoughDensity I M m) :=
    hsum.trans (by funext x; simp)
  conv_lhs => rw [hsum']
  exact integralDensity_sum _ s fun i _ ↦ hi.fun_smul (ρ i).continuous

/-- For any partition of unity `ρ`, `integralDensity μ` equals the finitely supported sum
`∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x)`. -/
public theorem integralDensity_eq_finsum_partitionOfUnity [IsManifold I 1 M] {ι : Type*}
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (ρ : PartitionOfUnity ι M univ) :
    integralDensity μ = ∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x) := by
  classical
  obtain ⟨s, hsum, hzero⟩ := integralDensity_eq_sum_partitionOfUnity hi ρ
  rw [hsum, finsum_eq_sum_of_support_subset]
  intro i hi'
  by_contra his
  exact Function.mem_support.mp hi' (hzero i his)

/-- A single preferred chart computes `integralDensity` whenever the density vanishes outside that
chart up to a chartwise null set. -/
public theorem integralDensity_eq_chartIntegral_of_ae_support [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M)
    (hs : IsNullSet I ({x | μ x ≠ 0} \ (extChartAt I α).source)) :
    integralDensity μ = ∫ y, μ.coeffInChartAt b α y ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  rw [integralDensity_eq_choose μ hi b]
  refine densityCoverIntegral_eq_chartIntegral_of_ae_support μ b _ hi α fun β ↦ ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hs.chartwise β b.addHaar)] with y hy ho
  by_cases ht : y ∈ (extChartAt I β).target
  · have hz : μ ((extChartAt I β).symm y) = 0 := by
      by_contra hn
      refine hy ⟨(extChartAt I β).symm y, ⟨⟨hn, fun ha ↦ ho ⟨(extChartAt I β).symm y,
        ⟨(extChartAt I β).map_target ht, ha⟩, (extChartAt I β).right_inv ht⟩⟩,
        (extChartAt I β).map_target ht⟩, (extChartAt I β).right_inv ht⟩
    rw [μ.coeffInChartAt_apply_of_mem_target b β ht, RoughDensity.inChartAt_apply, hz]
    rfl
  · exact μ.coeffInChartAt_apply_of_notMem_target b β ht

/-- An integrable rough density supported in a preferred chart integrates to its normalized Haar
integral in that chart, in any model basis. -/
public theorem integralDensity_eq_chartIntegral [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M)
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (extChartAt I α).source) :
    integralDensity μ = ∫ y, μ.coeffInChartAt b α y ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  refine integralDensity_eq_chartIntegral_of_ae_support μ hi b α
    ((isNullSet_boundary (I := I)).mono fun x hx ↦ ?_)
  exact False.elim (hx.2 (hs (_root_.subset_tsupport (α := Density E m) μ hx.1)))

/-- On a model normed space `E`, `integralDensity μ` of any integrable rough density equals the
Bochner integral `∫ x, μ x b ∂b.addHaar` in any basis `b`. -/
public theorem integralDensity_model_eq_integral [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity 𝓘(ℝ, E) E m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) :
    integralDensity μ = ∫ x, μ x b ∂b.addHaar := by
  rw [integralDensity_eq_chartIntegral μ hi b 0 (by simp)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have hx : x ∈ (extChartAt 𝓘(ℝ, E) (0 : E)).target := by simp
  -- `simp` cannot rewrite the identity chart under the dependently typed `mfderiv`, so `rw` does.
  rw [μ.coeffInChartAt_apply_of_mem_target b 0 hx, RoughDensity.inChartAt_apply,
    extChartAt_model_space_eq_id]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, modelWithCornersSelf_coe, range_id,
    mfderivWithin_univ, mfderiv_id]
  rfl

/-- On `ℝ`, the integral of an integrable rough `1`-density is the Lebesgue integral of its value
on the unit tangent vector `1`. -/
public theorem integralDensity_real_eq_integral {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1}
    (hi : IntegrableDensity μ) :
    integralDensity μ = ∫ t, μ t (fun _ ↦ 1) := by
  rw [integralDensity_model_eq_integral hi (Basis.singleton (Fin 1) ℝ),
    Basis.addHaar_singleton, Basis.coe_singleton]
  rfl

/-- On a zero-dimensional manifold, any rough density supported in `{x}` is integrable. -/
public theorem integrableDensity_zeroDim_singleton [Subsingleton E] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] (b : Basis (Fin 0) ℝ E)
    (μ : RoughDensity 𝓘(ℝ, E) M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) :
    IntegrableDensity μ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hc : IsCompact (_root_.tsupport (α := Density E 0) μ) :=
    isCompact_singleton.of_isClosed_subset (_root_.isClosed_tsupport _) hs
  rw [μ.integrableDensity_iff_of_tsupport_subset_chart b x hc
    (by simpa only [← extChartAt_source (I := 𝓘(ℝ, E)), extChartAt_source_zeroDim] using hs),
    Basis.addHaar_eq_dirac]
  exact integrable_dirac (by simp)

/-- On a zero-dimensional manifold, a rough density supported in `{x}` integrates to its value at
`x` on the empty tuple, with no orientation sign. -/
public theorem integralDensity_zeroDim_singleton [Subsingleton E] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] (b : Basis (Fin 0) ℝ E)
    (μ : RoughDensity 𝓘(ℝ, E) M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) :
    integralDensity μ = μ x 0 := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hi : IntegrableDensity μ := integrableDensity_zeroDim_singleton b μ x hs
  rw [integralDensity_eq_chartIntegral μ hi b x
      (by simpa only [extChartAt_source_zeroDim] using hs),
    Basis.addHaar_eq_dirac, integral_dirac,
    Subsingleton.elim (0 : E) (extChartAt 𝓘(ℝ, E) x x),
    μ.coeffInChartAt_apply_of_mem_source b x (mem_extChartAt_source x),
    RoughDensity.inChartAt_apply, extChartAt_to_inv]
  exact congrArg (μ x) (Subsingleton.elim _ 0)

/-- On a finite zero-dimensional manifold, `integralDensity μ` is the unsigned finite sum of the
point values `μ x 0`, with no orientation signs. -/
public theorem integralDensity_finite_zeroDim [Subsingleton E] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [Fintype M] (b : Basis (Fin 0) ℝ E)
    (μ : RoughDensity 𝓘(ℝ, E) M 0) :
    integralDensity μ = ∑ x : M, μ x 0 := by
  classical
  have : T1Space M := ChartedSpace.t1Space E M
  let δ : M → RoughDensity 𝓘(ℝ, E) M 0 := fun x y ↦ if y = x then μ y else 0
  have hs (x : M) : _root_.tsupport (α := Density E 0) (δ x) ⊆ {x} := by
    refine closure_minimal ?_ isClosed_singleton
    intro y hy
    by_contra hn
    have hne : y ≠ x := by simpa only [mem_singleton_iff] using hn
    exact hy (ite_eq_right hne)
  have hsum : μ = ∑ x : M, δ x := by
    funext y
    simp [δ]
  conv_lhs => rw [hsum]
  rw [integralDensity_sum δ Finset.univ
    (fun x _ ↦ integrableDensity_zeroDim_singleton b (δ x) x (hs x))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simpa only [δ, ite_true] using integralDensity_zeroDim_singleton b (δ x) x (hs x)

end CoverConstruction

section TopFormComparison

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {m : ℕ}

/-- On an oriented manifold, the density of a rough top form is integrable if and only if the top
form itself is integrable, including in dimension zero. -/
public theorem RoughForm.integrableDensity_toDensity_iff
    (o : Manifold.Orientation I M (Fin m)) (φ : RoughForm I M ℝ m) :
    IntegrableDensity (φ.toDensity o) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  rw [integrableDensity_iff, integrableTopForm_iff, φ.tsupport_toDensity]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun b ↦ forall_congr' fun α ↦ ?_))
  have hunit : IsUnit (Orientation.signBasis l.modelOrientation b : ℝ) := by
    rcases Int.units_eq_one_or (Orientation.signBasis l.modelOrientation b) with h | h <;>
      simp [h]
  have hσ : Continuous fun x : {x : M // x ∈ (extChartAt I α).source} ↦ l.signAt α x := by
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α
  rw [funext (φ.coeffInChartAt_toDensity l b α), integrable_const_mul_iff hunit,
    φ.integrable_signedInChartAt_iff_unsigned b α (fun x ↦ l.signAt α x) hσ b.addHaar]

/-- **Oriented top-form integration equals density integration** [Lee, Prop. 16.42]. On an oriented
manifold (possibly with boundary or corners, and including dimension zero), the integral of any
rough top form `φ` against `o` equals the orientation-free integral of its density
`φ.toDensity o`. Both sides vanish together when `φ` is not integrable. -/
public theorem integralTopForm_eq_integralDensity
    (o : Manifold.Orientation I M (Fin m)) (φ : RoughForm I M ℝ m) :
    integralTopForm o φ = integralDensity (φ.toDensity o) := by
  by_cases hi : IntegrableTopForm φ
  swap
  · have hid : ¬IntegrableDensity (φ.toDensity o) :=
      mt (φ.integrableDensity_toDensity_iff o).mp hi
    rw [integralTopForm_eq_zero_of_not_integrable o φ hi,
      integralDensity_eq_zero_of_not_integrable _ hid]
  have hid : IntegrableDensity (φ.toDensity o) :=
    (φ.integrableDensity_toDensity_iff o).mpr hi
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  obtain ⟨k, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hu i).1)
      (fun i ↦ (hu i).2.1) hcover,
    integralDensity_eq_sum_disjointed_chart_integrals (φ.toDensity (Manifold.Orientation.mk l))
      hid b α u (fun i ↦ (hu i).1) (fun i ↦ (hu i).2.1) (by rwa [φ.tsupport_toDensity]),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_const_mul]
  exact setIntegral_congr_fun
    (((hu i).1.isChartMeasurable.diff (by
      rw [Finset.sup_set_eq_biUnion]
      exact (isOpen_biUnion fun j _ ↦ (hu j).1).isChartMeasurable)).image_extChartAt (α i)
      ((disjointed_subset u i).trans (hu i).2.1))
    fun y _ ↦ (φ.coeffInChartAt_toDensity l b (α i) y).symm

end TopFormComparison

section Positivity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {m : ℕ}

private theorem coeffInChartAt_nonneg_of_basis_nonneg {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    0 ≤ μ.coeffInChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · obtain ⟨b', hb'⟩ := μ.inChartAt_apply_eq_eval_tangentBasis b α hy
    rw [μ.coeffInChartAt_apply_of_mem_target b α hy, hb']
    exact hμ _ b'
  · rw [μ.coeffInChartAt_apply_of_notMem_target b α hy]

/-- **Nonnegativity of density integration.** A rough density that is nonnegative on every tangent
basis has nonnegative integral, in every dimension `m : ℕ` (including dimension zero) and with no
regularity, support, or orientability hypothesis. -/
public theorem integralDensity_nonneg {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c) :
    0 ≤ integralDensity μ := by
  by_cases hi : IntegrableDensity μ
  swap
  · rw [integralDensity_eq_zero_of_not_integrable μ hi]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hi.nonempty_basis
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨k, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  rw [integralDensity_eq_sum_disjointed_chart_integrals μ hi b α u (fun i ↦ (hu i).1)
    (fun i ↦ (hu i).2.1) hcover]
  exact Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun y ↦ coeffInChartAt_nonneg_of_basis_nonneg hμ b (α i) y

/-- Pointwise dominance on tangent bases implies monotonicity of `integralDensity` for integrable
rough densities, in every dimension `m : ℕ`. -/
public theorem integralDensity_mono {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (hle : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), μ x c ≤ ν x c) :
    integralDensity μ ≤ integralDensity ν := by
  rw [← sub_nonneg, ← integralDensity_sub_of_integrable hν hμ]
  exact integralDensity_nonneg fun x c ↦ sub_nonneg.mpr (hle x c)

/-- **Strict positivity of density integration.** If an integrable rough density `μ` is nonnegative
on every tangent basis, positive on some tangent basis at `x₀`, and has continuous coordinate
expression on the target of the preferred chart at `x₀`, then `0 < integralDensity μ`. Unlike
`integralTopForm_pos`, this holds in dimension zero as well as positive dimensions. -/
public theorem integralDensity_pos_of_continuousOn_inChartAt {μ : RoughDensity I M m}
    (hi : IntegrableDensity μ)
    (hnn : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    {x₀ : M} (hcont : ContinuousOn (μ.inChartAt x₀) (extChartAt I x₀).target)
    {c₀ : Basis (Fin m) ℝ (TangentSpace I x₀)} (hpos : 0 < μ x₀ c₀) :
    0 < integralDensity μ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hi.nonempty_basis
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨k, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  let α' : Fin (k + 1) → M := Fin.cons x₀ α
  let u' : Fin (k + 1) → Set M := Fin.cons (extChartAt I x₀).source u
  have hu' : ∀ i, IsOpen (u' i) ∧ u' i ⊆ (extChartAt I (α' i)).source :=
    Fin.cases (by simpa [α', u'] using isOpen_extChartAt_source (I := I) x₀)
      fun i ↦ by simpa [α', u'] using And.intro (hu i).1 (hu i).2.1
  have hcover' : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u' i :=
    hcover.trans (iUnion_subset fun i ↦ by simpa [u'] using subset_iUnion u' i.succ)
  rw [integralDensity_eq_sum_disjointed_chart_integrals μ hi b α' u' (fun i ↦ (hu' i).1)
    (fun i ↦ (hu' i).2) hcover', Fin.sum_univ_succ]
  refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun y ↦ coeffInChartAt_nonneg_of_basis_nonneg hnn b (α' i.succ) y)
  have hpiece : (extChartAt I (α' 0)) '' disjointed u' 0 = (extChartAt I x₀).target := by
    rw [← bot_eq_zero, disjointed_bot, bot_eq_zero]
    simp only [α', u', Fin.cons_zero]
    exact (extChartAt I x₀).image_source_eq_target
  simp only [α', Fin.cons_zero] at hpiece ⊢
  rw [hpiece]
  have hy₀ : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target := mem_extChartAt_target x₀
  let b' : Basis (Fin m) ℝ (TangentSpace I x₀) :=
    b.map (tangentSpaceCastModel I x₀).symm.toLinearEquiv
  have hg₀ : 0 < μ.coeffInChartAt b x₀ (extChartAt I x₀ x₀) := by
    rw [μ.coeffInChartAt_apply_of_mem_source b x₀ (mem_extChartAt_source x₀),
      μ.inChartAt_chart_apply x₀ (mem_extChartAt_source x₀)]
    simp only [tangentCoordChange_self (mem_extChartAt_source x₀)]
    have hb' : μ x₀ (fun i ↦ b i) = μ x₀ b' := rfl
    rw [hb', (μ x₀).apply_eq_abs_det_mul c₀ b']
    exact mul_pos (abs_pos.mpr (c₀.isUnit_det b').ne_zero) hpos
  exact setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target (μ := b.addHaar) x₀
    (coeffInChartAt_nonneg_of_basis_nonneg hnn b x₀)
    (hi.integrable_coeffInChartAt b x₀).integrableOn
    (μ.continuousOn_coeffInChartAt b x₀ hcont) hy₀ hg₀

/-- **Strict positivity for continuous density sections** [Lee, Prop. 16.42(b)]. A compactly
supported continuous section of `TauCeti.DensityBundle` that is nonnegative everywhere and strictly
positive on one tangent basis at one point has strictly positive integral, in every dimension
including dimension zero. -/
public theorem integralDensity_pos [FiniteDimensional ℝ E]
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ))
    (hnn : ∀ x (c : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (hpos : ∃ x, ∃ c : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x), 0 < μ x c) :
    0 < integralDensity μ := by
  obtain ⟨x₀, c₀, hc₀⟩ := hpos
  exact integralDensity_pos_of_continuousOn_inChartAt
    (RoughDensity.integrableDensity_of_continuous_section hμ hc) hnn
    (RoughDensity.continuousOn_inChartAt_of_continuous_section hμ x₀) hc₀

end Positivity

end TauCeti
