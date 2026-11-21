/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.ExtChartAt.Cover
import TauCeti.Topology.PartitionOfUnity.Basic

/-!
# Orientation-free integration of densities on manifolds

Defines `TauCeti.IntegrableDensity` and `TauCeti.integralDensity` with no orientation, metric,
Hausdorff, or manifold measurable structure (including manifolds with boundary and corners), proves
open-cover/continuous integrability, chart-cover and partition-of-unity formulas, zero-dimensional
integration (`integralDensity_zeroDim`), `integralTopForm_eq_integralDensity`, and positivity.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Theorem 16.41
  and Proposition 16.42.
-/

noncomputable section

open Bundle MeasureTheory Set Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section Integrability

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- A rough density is integrable when it has compact topological support, `E` admits a basis of
cardinality `m`, and `μ.coeffInChartAt b α` is Haar-integrable against `b.addHaar` for every basis
`b` and preferred chart `α`. -/
public def IntegrableDensity (μ : RoughDensity I M m) : Prop := by
  letI : MeasurableSpace E := borel E; letI : BorelSpace E := ⟨rfl⟩
  exact IsCompact (_root_.tsupport (α := Density E m) μ) ∧ Nonempty (Basis (Fin m) ℝ E) ∧
    ∀ (b : Basis (Fin m) ℝ E) (α : M), Integrable (μ.coeffInChartAt b α) b.addHaar

/-- Coordinate characterization of `IntegrableDensity` for any Borel measurable structure on `E`. -/
public theorem integrableDensity_iff [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) :
    IntegrableDensity μ ↔ IsCompact (_root_.tsupport (α := Density E m) μ) ∧
      Nonempty (Basis (Fin m) ℝ E) ∧
      ∀ (b : Basis (Fin m) ℝ E) (α : M), Integrable (μ.coeffInChartAt b α) b.addHaar := by
  cases (BorelSpace.measurable_eq : ‹MeasurableSpace E› = borel E); rfl

/-- Integrable rough densities have compact topological support. -/
public theorem IntegrableDensity.isCompact {μ : RoughDensity I M m} (hi : IntegrableDensity μ) :
    IsCompact (_root_.tsupport (α := Density E m) μ) := hi.1

/-- An integrable rough density witnesses that `E` has a basis of cardinality `m`. -/
public theorem IntegrableDensity.nonempty_basis {μ : RoughDensity I M m}
    (hi : IntegrableDensity μ) : Nonempty (Basis (Fin m) ℝ E) := hi.2.1

/-- Every chart coefficient of an integrable rough density is Haar-integrable. -/
public theorem IntegrableDensity.integrable_coeffInChartAt [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) (α : M) :
    Integrable (μ.coeffInChartAt b α) b.addHaar := ((integrableDensity_iff μ).mp hi).2.2 b α

/-- For a compactly supported rough density, integrability on an open chart cover implies
`IntegrableDensity`, using a single model basis and neither continuity nor orientability. -/
public theorem RoughDensity.integrableDensity_of_open_cover [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] {J : Type*} (μ : RoughDensity I M m)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (b : Basis (Fin m) ℝ E) (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i))
    (hsource : ∀ i, u i ⊆ (chartAt H (β i)).source)
    (hcover : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (μ.coeffInChartAt b (β i))
      ((extChartAt I (β i)) '' u i) b.addHaar) : IntegrableDensity μ :=
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  (integrableDensity_iff μ).mpr ⟨hc, ⟨b⟩, fun b' α ↦
    (μ.integrable_coeffInChartAt_basis_iff b b' α).mpr <|
      integrable_of_open_cover_extChartAt hc (μ.coeffInChartAt b) b.addHaar β u hu hcover hlocal α
        (μ.support_coeffInChartAt_subset b α) fun i ↦
        (μ.coeffInChartAt_changeChart b α (β i) (s := (extChartAt I α).source ∩ u i)
          (fun _ hx ↦ ⟨hx.1, by simpa only [extChartAt_source] using hsource i hx.2⟩)
          ((hu i).measurableSet_image_extChartAt_source_inter α) b.addHaar).2.mpr⟩

/-- A compactly supported rough density supported in one preferred chart is integrable iff its
coefficient in that chart and one model basis is Haar-integrable. -/
public theorem RoughDensity.integrableDensity_iff_of_tsupport_subset_chart
    [MeasurableSpace E] [BorelSpace E] [IsManifold I 1 M] {μ : RoughDensity I M m}
    (b : Basis (Fin m) ℝ E) (α : M) (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (chartAt H α).source) :
    IntegrableDensity μ ↔ Integrable (μ.coeffInChartAt b α) b.addHaar :=
  ⟨fun h ↦ h.integrable_coeffInChartAt b α, fun hi ↦
    μ.integrableDensity_of_open_cover hc b (fun _ : Unit ↦ α) (fun _ ↦ (chartAt H α).source)
      (fun _ ↦ (chartAt H α).open_source) (fun _ ↦ Subset.rfl)
      (fun _ hx ↦ mem_iUnion.mpr ⟨(), hs hx⟩) (fun _ ↦ hi.integrableOn)⟩

/-- Multiplication by a nonzero constant preserves `IntegrableDensity`. -/
public theorem integrableDensity_smul_iff (c : ℝ) (μ : RoughDensity I M m) (hc : c ≠ 0) :
    IntegrableDensity (c • μ) ↔ IntegrableDensity μ := by
  let : MeasurableSpace E := borel E; let : BorelSpace E := ⟨rfl⟩
  have hts : _root_.tsupport (α := Density E m) (c • μ) = _root_.tsupport (α := Density E m) μ :=
    congrArg closure
      (Function.support_const_smul_of_ne_zero c (show M → Density E m from μ) hc)
  rw [integrableDensity_iff, integrableDensity_iff, hts]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun b ↦ forall_congr' fun α ↦ ?_))
  rw [funext (RoughDensity.coeffInChartAt_smul c μ b α)]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _

/-- The sum of two integrable rough densities is integrable. -/
public theorem IntegrableDensity.add {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) : IntegrableDensity (μ + ν) := by
  let : MeasurableSpace E := borel E; let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ hν ⊢
  exact ⟨HasCompactSupport.add (f := (show M → Density E m from μ)) hμ.1 hν.1, hμ.2.1,
    fun b α ↦ by
      rw [funext (RoughDensity.coeffInChartAt_add μ ν b α)]; exact (hμ.2.2 b α).add (hν.2.2 b α)⟩

/-- The zero density is integrable whenever `E` admits a basis of cardinality `m`. -/
public theorem IntegrableDensity.zero (b : Basis (Fin m) ℝ E) :
    IntegrableDensity (0 : RoughDensity I M m) := by
  let : MeasurableSpace E := borel E; let : BorelSpace E := ⟨rfl⟩
  exact (integrableDensity_iff _).mpr
    ⟨HasCompactSupport.zero (α := M) (β := Density E m), ⟨b⟩, fun b' α ↦ by
      simpa only [RoughDensity.coeffInChartAt_zero] using integrable_zero E ℝ b'.addHaar⟩

/-- Constant scalar multiplication preserves `IntegrableDensity`. -/
public theorem IntegrableDensity.smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) (c : ℝ) :
    IntegrableDensity (c • μ) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa only [zero_smul] using IntegrableDensity.zero (I := I) (M := M) hμ.nonempty_basis.some
  · exact (integrableDensity_smul_iff c μ hc).mpr hμ

/-- Negation preserves `IntegrableDensity`. -/
public theorem IntegrableDensity.neg {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) :
    IntegrableDensity (-μ) := by simpa only [neg_one_smul] using hμ.smul (-1)

/-- Subtraction preserves `IntegrableDensity`. -/
public theorem IntegrableDensity.sub {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) : IntegrableDensity (μ - ν) :=
  sub_eq_add_neg μ ν ▸ hμ.add hν.neg

/-- Finite sums of integrable rough densities are integrable. -/
public theorem IntegrableDensity.sum {ι : Type*} (b : Basis (Fin m) ℝ E)
    (μ : ι → RoughDensity I M m) (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    IntegrableDensity (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntegrableDensity.zero (I := I) (M := M) b
  | @insert i s hi ih => rw [Finset.sum_insert hi]; exact
      (hμ i (Finset.mem_insert_self i s)).add (ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj))

/-- Pointwise multiplication by a continuous scalar function preserves `IntegrableDensity`, with no
Hausdorff assumption on the manifold. -/
public theorem IntegrableDensity.fun_smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ)
    {f : M → ℝ} (hf : Continuous f) : IntegrableDensity (fun x ↦ f x • μ x) := by
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  -- Clamp `f` to its compact-support bound to obtain a globally bounded continuous multiplier.
  obtain ⟨B, hB⟩ := hμ.isCompact.exists_bound_of_continuousOn hf.continuousOn
  let C := max B 0; let g : M → ℝ := fun x ↦ max (-C) (min C (f x))
  have hgf : (fun x ↦ g x • μ x : RoughDensity I M m) = fun x ↦ f x • μ x := by
    funext x; by_cases hx : x ∈ _root_.tsupport (α := Density E m) μ
    · obtain ⟨hl, hh⟩ := abs_le.mp
        (by simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_max_left B 0))
      simp only [g, C, min_eq_right hh, max_eq_right hl]
    · have hz : μ x = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hx; simp [hz]
  rw [← hgf, integrableDensity_iff]
  refine ⟨hμ.isCompact.of_isClosed_subset (_root_.isClosed_tsupport _)
    (_root_.tsupport_smul_subset_right g (show M → Density E m from μ)),
    hμ.nonempty_basis, fun b α ↦ ?_⟩
  have hm := measurableSet_extChartAt_target (I := I) α
  exact (integrableOn_iff_integrable_of_support_subset
    (RoughDensity.support_coeffInChartAt_subset_target _ b α)).mp <| IntegrableOn.congr_fun
    ((hμ.integrable_coeffInChartAt b α).integrableOn.bdd_mul (((continuous_const.max
      (continuous_const.min hf)).comp_continuousOn (continuousOn_extChartAt_symm α)
      ).aestronglyMeasurable hm (μ := b.addHaar)) (Filter.Eventually.of_forall fun _ ↦
      (Real.norm_eq_abs _).trans_le <| abs_le.mpr
        ⟨le_max_left _ _, max_le (neg_le_self (le_max_right B 0)) (min_le_left _ _)⟩))
    (fun y _ ↦ (RoughDensity.coeffInChartAt_fun_smul g μ b α y).symm) hm

/-- A compactly supported rough density whose coordinate expression is continuous on every
preferred chart target is integrable whenever `E` admits a basis of cardinality `m`. -/
public theorem RoughDensity.integrableDensity_of_continuousOn_inChartAt [IsManifold I 1 M]
    {μ : RoughDensity I M m} (hμ : ∀ α, ContinuousOn (μ.inChartAt α) (extChartAt I α).target)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) (b : Basis (Fin m) ℝ E) :
    IntegrableDensity μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨_, β, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  exact μ.integrableDensity_of_open_cover hc b β u (fun i ↦ (hu i).1)
    (fun i ↦ by simpa only [extChartAt_source] using (hu i).2.1) hcover fun i ↦
    (((μ.continuousOn_coeffInChartAt b (β i) (hμ (β i))).mono
      (hu i).2.2.2.1).integrableOn_compact (hu i).2.2.1 (μ := b.addHaar)).mono_set (hu i).2.2.2.2

/-- Every compactly supported continuous section of `TauCeti.DensityBundle` is integrable. -/
public theorem RoughDensity.integrableDensity_of_continuous_section
    [FiniteDimensional ℝ E] [IsManifold I 1 M] {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ)) : IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuousOn_inChartAt
    (fun _ ↦ RoughDensity.continuousOn_inChartAt_of_continuousOn_section hμ.continuousOn)
    hc (finBasis ℝ E)

/-- On a compact manifold, every continuous section of `TauCeti.DensityBundle` is integrable. -/
public theorem RoughDensity.integrableDensity_of_continuous_section_of_compactSpace
    [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompactSpace M] {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x)) : IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ (_root_.isClosed_tsupport _).isCompact

/-- Every compactly supported `C^n` section of `TauCeti.DensityBundle` is integrable. -/
public theorem RoughDensity.integrableDensity_of_contMDiff_section
    [FiniteDimensional ℝ E] [IsManifold I 1 M] {n : ℕ∞ω} {μ : (x : M) → DensityBundle I M x}
    (hμ : ContMDiff I (I.prod 𝓘(ℝ)) n fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ)) : IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ.continuous hc

end Integrability

section CoverConstruction

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

private theorem coeffInChartAt_eq_zero_of_notMem_tsupport (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {x : M} (hx : x ∈ (extChartAt I α).source)
    (hn : x ∉ _root_.tsupport (α := Density E m) μ) :
    μ.coeffInChartAt b α (extChartAt I α x) = 0 :=
  RoughDensity.coeffInChartAt_eq_zero_of_apply_eq_zero b α <| by
    rw [(extChartAt I α).left_inv hx]
    exact _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hn

section WithMeasure

variable [MeasurableSpace E] [BorelSpace E]

private theorem densityCoverIntegral_basis_eq {s : Set M} (b b' : Basis (Fin m) ℝ E)
    (μ : RoughDensity I M m) (c : ChartCover I s) :
    c.integral (μ.coeffInChartAt b) b.addHaar = c.integral (μ.coeffInChartAt b') b'.addHaar := by
  rw [ChartCover.integral_eq_sum, ChartCover.integral_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ μ.setIntegral_coeffInChartAt_basis_eq b b' (c.center i) _

private theorem densityCoverIntegral_eq [IsManifold I 1 M] (μ : RoughDensity I M m)
    (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) {s t : Set M} (c : ChartCover I s)
    (d : ChartCover I t) (hc : _root_.tsupport (α := Density E m) μ ⊆ s)
    (hd : _root_.tsupport (α := Density E m) μ ⊆ t) :
    c.integral (μ.coeffInChartAt b) b.addHaar = d.integral (μ.coeffInChartAt b) b.addHaar :=
  c.integral_eq d (μ.coeffInChartAt b) b.addHaar
    (fun i ↦ (hi.integrable_coeffInChartAt b (c.center i)).integrableOn)
    (fun j ↦ (hi.integrable_coeffInChartAt b (d.center j)).integrableOn)
    (fun i _ hx hxt ↦ coeffInChartAt_eq_zero_of_notMem_tsupport μ b (c.center i)
      (c.piece_subset i hx) (mt (fun h ↦ hd h) hxt))
    (fun j _ hx hxs ↦ coeffInChartAt_eq_zero_of_notMem_tsupport μ b (d.center j)
      (d.piece_subset j hx) (mt (fun h ↦ hc h) hxs))
    fun i j ↦ (μ.coeffInChartAt_changeChart b (c.center i) (d.center j)
      (s := c.piece i ∩ d.piece j) (fun _ hx ↦ ⟨c.piece_subset i hx.1, d.piece_subset j hx.2⟩)
      (((c.isChartMeasurable_piece i).inter (d.isChartMeasurable_piece j)).image_extChartAt
        (c.center i) (inter_subset_left.trans (c.piece_subset i))) b.addHaar).1

end WithMeasure

/-- Orientation-free total integral of `μ` on `M`: `0` unless `IntegrableDensity μ`, otherwise the
sum of normalized Haar set integrals of `μ.coeffInChartAt` over the disjointed Borel pieces of a
finite open chart cover of the support (no orientation, Hausdorffness, or manifold measure). -/
public def integralDensity (μ : RoughDensity I M m) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E; letI : BorelSpace E := ⟨rfl⟩
  exact if hi : IntegrableDensity μ then
    let b := hi.nonempty_basis.some; haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
    letI : LocallyCompactSpace H := I.locallyCompactSpace
    (ChartCover.choose I hi.isCompact).integral (μ.coeffInChartAt b) b.addHaar
  else 0

/-- A nonintegrable rough density has zero total integral. -/
public theorem integralDensity_eq_zero_of_not_integrable (μ : RoughDensity I M m)
    (hi : ¬IntegrableDensity μ) : integralDensity μ = 0 := by rw [integralDensity, dite_eq_right hi]

/-- A rough density without compact support has zero total integral. -/
public theorem integralDensity_eq_zero_of_not_isCompact (μ : RoughDensity I M m)
    (hc : ¬IsCompact (_root_.tsupport (α := Density E m) μ)) : integralDensity μ = 0 :=
  integralDensity_eq_zero_of_not_integrable μ fun hi ↦ hc hi.isCompact

private theorem integralDensity_eq_choose [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace H] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) : integralDensity μ =
      (ChartCover.choose I hi.isCompact).integral (μ.coeffInChartAt b) b.addHaar := by
  classical
  cases (BorelSpace.measurable_eq : ‹MeasurableSpace E› = borel E)
  let : MeasurableSpace E := borel E; rw [integralDensity, dite_eq_left hi]; dsimp only
  exact densityCoverIntegral_basis_eq hi.nonempty_basis.some b μ _

private theorem integralDensity_eq_coverIntegral [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] (μ : RoughDensity I M m) (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E)
    {s : Set M} (c : ChartCover I s) (hc : _root_.tsupport (α := Density E m) μ ⊆ s) :
    integralDensity μ = c.integral (μ.coeffInChartAt b) b.addHaar :=
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  (integralDensity_eq_choose μ hi b).trans (densityCoverIntegral_eq μ hi b _ c Subset.rfl hc)

/-- Any finite open chart cover computes `integralDensity` through its disjointed Borel coordinate
pieces, in any model basis and with no orientation data. -/
public theorem integralDensity_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) {k : ℕ} (α : Fin k → M) (u : Fin k → Set M) (hu : ∀ i, IsOpen (u i))
    (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i) :
    integralDensity μ = ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i,
      μ.coeffInChartAt b (α i) y ∂b.addHaar := by
  let c : ChartCover I (_root_.tsupport (α := Density E m) μ) := ⟨k, α, u, hu, hs, hc⟩
  rw [integralDensity_eq_coverIntegral μ hi b c Subset.rfl, ChartCover.integral_eq_sum]
  simp only [ChartCover.piece_eq_disjointed, c]

/-- A compact manifold admits a finite disjoint chartwise Borel partition computing every
integrable density integral, without a measurable structure or orientation on `M`. -/
public theorem exists_chart_partition_integralDensity [IsManifold I 1 M] [CompactSpace M]
    [MeasurableSpace E] [BorelSpace E] (b : Basis (Fin m) ℝ E) :
    ∃ k : ℕ, ∃ α : Fin k → M, ∃ s : Fin k → Set M,
      (∀ i, IsChartMeasurable I (s i)) ∧ (∀ i, s i ⊆ (extChartAt I (α i)).source) ∧
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ ∧
      ∀ μ : RoughDensity I M m, IntegrableDensity μ → integralDensity μ =
        ∑ i, ∫ y in (extChartAt I (α i)) '' s i, μ.coeffInChartAt b (α i) y ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let c := ChartCover.choose I (isCompact_univ : IsCompact (univ : Set M))
  exact ⟨c.n, c.center, c.piece, c.isChartMeasurable_piece, c.piece_subset, c.pairwise_disjoint,
    Subset.antisymm (subset_univ _) c.piece_covers, fun μ hi ↦ by
      rw [integralDensity_eq_coverIntegral μ hi b c (subset_univ _), ChartCover.integral_eq_sum]⟩

/-- The zero density has zero integral. -/
@[simp] public theorem integralDensity_zero : integralDensity (0 : RoughDensity I M m) = 0 := by
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity (0 : RoughDensity I M m)
  · obtain ⟨b⟩ := hi.nonempty_basis; have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    let : LocallyCompactSpace H := I.locallyCompactSpace
    rw [integralDensity_eq_choose _ hi b, ChartCover.integral_eq_sum]
    simp [RoughDensity.coeffInChartAt_zero]
  · exact integralDensity_eq_zero_of_not_integrable _ hi

/-- Constant scalar multiplication commutes with `integralDensity`, even when nonintegrable. -/
@[simp] public theorem integralDensity_smul (c : ℝ) (μ : RoughDensity I M m) :
    integralDensity (c • μ) = c * integralDensity μ := by
  rcases eq_or_ne c 0 with rfl | hc; · simp
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  by_cases hi : IntegrableDensity μ
  · have hi' := (integrableDensity_smul_iff c μ hc).mpr hi
    obtain ⟨b⟩ := hi.nonempty_basis; have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    let : LocallyCompactSpace H := I.locallyCompactSpace
    have hs : (c • μ).coeffInChartAt b = fun α y ↦ c • μ.coeffInChartAt b α y :=
      funext fun α ↦ funext (RoughDensity.coeffInChartAt_smul c μ b α)
    rw [integralDensity_eq_choose _ hi' b, integralDensity_eq_choose _ hi b, hs,
      ChartCover.integral_smul, smul_eq_mul]
    exact congrArg (c * ·) (ChartCover.integral_choose_congr hi'.isCompact hi.isCompact
      (congrArg closure (Function.support_const_smul_of_ne_zero c (show M → Density E m from μ) hc))
      (μ.coeffInChartAt b) b.addHaar)
  · rw [integralDensity_eq_zero_of_not_integrable _ (mt (integrableDensity_smul_iff c μ hc).mp hi),
      integralDensity_eq_zero_of_not_integrable _ hi, mul_zero]

/-- Negation negates `integralDensity`, including for nonintegrable rough densities. -/
@[simp] public theorem integralDensity_neg (μ : RoughDensity I M m) :
    integralDensity (-μ) = -integralDensity μ := by
  rw [← neg_one_smul ℝ μ, integralDensity_smul, neg_one_mul]

/-- `integralDensity` is additive on integrable rough densities. -/
public theorem integralDensity_add_of_integrable [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ + ν) = integralDensity μ + integralDensity ν := by
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hμ.nonempty_basis; have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let c := ChartCover.choose I (hμ.isCompact.union hν.isCompact)
  have ha : (μ + ν).coeffInChartAt b = fun α y ↦ μ.coeffInChartAt b α y + ν.coeffInChartAt b α y :=
    funext fun α ↦ funext (RoughDensity.coeffInChartAt_add μ ν b α)
  rw [integralDensity_eq_coverIntegral _ (hμ.add hν) b c
      (_root_.tsupport_add (show M → Density E m from μ) (show M → Density E m from ν)),
    integralDensity_eq_coverIntegral _ hμ b c subset_union_left,
    integralDensity_eq_coverIntegral _ hν b c subset_union_right, ha]
  exact c.integral_add b.addHaar
    (fun i ↦ (hμ.integrable_coeffInChartAt b (c.center i)).integrableOn)
    (fun i ↦ (hν.integrable_coeffInChartAt b (c.center i)).integrableOn)

/-- `integralDensity` respects subtraction of integrable rough densities. -/
public theorem integralDensity_sub_of_integrable [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ - ν) = integralDensity μ - integralDensity ν := by
  rw [sub_eq_add_neg, integralDensity_add_of_integrable hμ hν.neg, integralDensity_neg,
    sub_eq_add_neg]

/-- `integralDensity` commutes with finite sums of integrable rough densities. -/
public theorem integralDensity_sum [IsManifold I 1 M] {ι : Type*} (μ : ι → RoughDensity I M m)
    (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    integralDensity (∑ i ∈ s, μ i) = ∑ i ∈ s, integralDensity (μ i) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩; · simp
  obtain ⟨b⟩ := (hμ i₀ hi₀).nonempty_basis; clear i₀ hi₀
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integralDensity_add_of_integrable (hμ i (Finset.mem_insert_self i s))
        (IntegrableDensity.sum b μ s fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)]

/-- A partition of unity covering `tsupport μ` decomposes `integralDensity μ` into a finite sum of
localized integrals, with all remaining terms vanishing. -/
public theorem exists_finset_integralDensity_eq_sum_partitionOfUnity [IsManifold I 1 M] {ι : Type*}
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) {t : Set M} (ρ : PartitionOfUnity ι M t)
    (ht : _root_.tsupport (α := Density E m) μ ⊆ t) :
    ∃ s : Finset ι, integralDensity μ = ∑ i ∈ s, integralDensity (fun x ↦ ρ i x • μ x) ∧
      ∀ i ∉ s, integralDensity (fun x ↦ ρ i x • μ x) = 0 := by
  have hpart : ∃ s : Finset ι, μ = (fun x ↦ ∑ i ∈ s, ρ i x • μ x) ∧
      ∀ i ∉ s, (fun x ↦ ρ i x • μ x : RoughDensity I M m) = 0 :=
    ρ.exists_finset_eq_sum_smul (show M → Density E m from μ) hi.isCompact ht
  obtain ⟨s, hsum, hzero⟩ := hpart
  exact ⟨s, (congrArg integralDensity (hsum.trans (by funext x; simp))).trans
    (integralDensity_sum _ s fun i _ ↦ hi.fun_smul (ρ i).continuous),
    fun i his ↦ by rw [hzero i his, integralDensity_zero]⟩

/-- For any partition of unity `ρ` covering `tsupport μ`, `integralDensity μ` equals
`∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x)`. -/
public theorem integralDensity_eq_finsum_partitionOfUnity [IsManifold I 1 M] {ι : Type*}
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) {t : Set M} (ρ : PartitionOfUnity ι M t)
    (ht : _root_.tsupport (α := Density E m) μ ⊆ t) :
    integralDensity μ = ∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x) := by
  classical
  obtain ⟨s, hsum, hzero⟩ := exists_finset_integralDensity_eq_sum_partitionOfUnity hi ρ ht
  rw [hsum, finsum_eq_sum_of_support_subset]
  exact fun i hi' ↦ by_contra fun his ↦ Function.mem_support.mp hi' (hzero i his)

/-- A single preferred chart computes `integralDensity` whenever `μ` vanishes outside that chart up
to a chartwise null set. -/
public theorem integralDensity_eq_chartIntegral_of_ae_support [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M) (hs : IsNullSet I ({x | μ x ≠ 0} \ (extChartAt I α).source)) :
    integralDensity μ = ∫ y, μ.coeffInChartAt b α y ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let c := ChartCover.choose I hi.isCompact; rw [integralDensity_eq_choose μ hi b]
  refine c.integral_eq_integral_of_ae_support (μ.coeffInChartAt b) b.addHaar α
    (hi.integrable_coeffInChartAt b α).integrableOn
    (fun _ hx hxs ↦ coeffInChartAt_eq_zero_of_notMem_tsupport μ b α hx hxs)
    (fun _ hy ↦ μ.coeffInChartAt_apply_of_notMem_target b α hy) (fun i ↦ ?_) fun i ↦
    (μ.coeffInChartAt_changeChart b (c.center i) α (s := c.piece i ∩ (extChartAt I α).source)
      (fun _ hx ↦ ⟨c.piece_subset i hx.1, hx.2⟩)
      (((c.isChartMeasurable_piece i).inter
        (isOpen_extChartAt_source α).isChartMeasurable).image_extChartAt (c.center i)
          (inter_subset_left.trans (c.piece_subset i))) b.addHaar).1
  filter_upwards [hs.ae_extChartAt_symm_notMem_of_sdiff_source (c.center i) b.addHaar] with y hy ho
  by_cases ht : y ∈ (extChartAt I (c.center i)).target
  · exact RoughDensity.coeffInChartAt_eq_zero_of_apply_eq_zero b _ (not_not.mp (hy ho ht))
  · exact μ.coeffInChartAt_apply_of_notMem_target b (c.center i) ht

/-- An integrable rough density supported in one preferred chart integrates to its normalized Haar
integral in that chart, in any model basis. -/
public theorem integralDensity_eq_chartIntegral [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M)
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (extChartAt I α).source) :
    integralDensity μ = ∫ y, μ.coeffInChartAt b α y ∂b.addHaar :=
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  integralDensity_eq_chartIntegral_of_ae_support μ hi b α ((isNullSet_boundary (I := I)).mono
    fun _ hx ↦ False.elim (hx.2 (hs (_root_.subset_tsupport (α := Density E m) μ hx.1))))

/-- On a model normed space `E`, `integralDensity μ` equals `∫ x, μ x b ∂b.addHaar` in any basis. -/
public theorem integralDensity_model_eq_integral [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity 𝓘(ℝ, E) E m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) :
    integralDensity μ = ∫ x, μ x b ∂b.addHaar := by
  rw [integralDensity_eq_chartIntegral μ hi b 0 (by simp)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  rw [μ.coeffInChartAt_apply_of_mem_target b 0 (by simp), RoughDensity.inChartAt_apply,
    extChartAt_model_space_eq_id]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, modelWithCornersSelf_coe, range_id,
    mfderivWithin_univ, mfderiv_id]; rfl

/-- On `ℝ`, the integral of an integrable `1`-density is `∫ t, μ t (fun _ ↦ 1)`. -/
public theorem integralDensity_real_eq_integral {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1}
    (hi : IntegrableDensity μ) : integralDensity μ = ∫ t, μ t (fun _ ↦ (1 : ℝ)) := by
  rw [integralDensity_model_eq_integral hi (Basis.singleton (Fin 1) ℝ),
    Basis.addHaar_singleton, Basis.coe_singleton]; rfl

section ZeroDim

variable [Subsingleton E]

private theorem tsupport_zeroDim_eq_support (μ : RoughDensity I M 0) :
    _root_.tsupport (α := Density E 0) μ = {x | μ x ≠ 0} :=
  have : DiscreteTopology M := I.discreteTopology M
  ((isClosed_discrete _).closure_eq).trans
    (Set.ext fun _ ↦ Function.mem_support (f := (show M → Density E 0 from μ)))

/-- On a zero-dimensional manifold, a rough density is integrable iff its support is finite. -/
public theorem integrableDensity_zeroDim_iff (μ : RoughDensity I M 0) :
    IntegrableDensity μ ↔ {x | μ x ≠ 0}.Finite := by
  have : DiscreteTopology M := I.discreteTopology M
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff, tsupport_zeroDim_eq_support μ, isCompact_iff_finite]
  exact ⟨fun h ↦ h.1, fun hfin ↦ ⟨hfin, ⟨Basis.empty E⟩, fun _ _ ↦ by
    rw [Basis.addHaar_eq_dirac]; exact integrable_dirac (by simp)⟩⟩

/-- On a zero-dimensional charted manifold, `integralDensity μ = ∑ᶠ x : M, μ x 0` unconditionally,
with no orientation signs or smoothness hypothesis. -/
public theorem integralDensity_zeroDim (μ : RoughDensity I M 0) :
    integralDensity μ = ∑ᶠ x : M, μ x 0 := by
  classical
  have hsupp_eq : Function.support (fun x : M ↦ μ x 0) = {x | μ x ≠ 0} := Set.ext fun x ↦
    not_congr ⟨fun h ↦ by dsimp only at h; ext v; rw [Subsingleton.elim v 0, h, Density.zero_apply],
      fun h ↦ by dsimp only; rw [h, Density.zero_apply]⟩
  by_cases hfin : {x | μ x ≠ 0}.Finite
  swap; · rw [integralDensity_eq_zero_of_not_integrable μ (mt (integrableDensity_zeroDim_iff μ).mp
      hfin), finsum_of_infinite_support (by rwa [hsupp_eq])]
  have : IsManifold I 1 M := isManifold_of_contDiffOn I 1 M fun _ _ _ _ ↦
    contDiffOn_const (c := (0 : E)).congr fun _ _ ↦ Subsingleton.elim _ _
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  let b : Basis (Fin 0) ℝ E := Basis.empty E
  let s := hfin.toFinset; let e := s.equivFin; let α (i : Fin s.card) : M := e.symm i
  have hdisj : Pairwise fun i j ↦ Disjoint ({α i} : Set M) {α j} := fun _ _ hij ↦
    disjoint_singleton.mpr fun h ↦ hij (e.symm.injective (Subtype.ext h))
  rw [integralDensity_eq_sum_disjointed_chart_integrals μ
    ((integrableDensity_zeroDim_iff μ).mpr hfin) b α (fun i ↦ {α i})
    (fun i ↦ extChartAt_source_zeroDim (I := I) (α i) ▸ isOpen_extChartAt_source (α i))
    (fun i ↦ (extChartAt_source_zeroDim (I := I) (α i)).ge)
    (by rw [tsupport_zeroDim_eq_support]; exact fun x hx ↦
      mem_iUnion.mpr ⟨e ⟨x, hfin.mem_toFinset.mpr hx⟩, by simp [α]⟩)]
  have hterm (i : Fin s.card) : (∫ y in (extChartAt I (α i)) '' disjointed (fun j ↦ {α j}) i,
      μ.coeffInChartAt b (α i) y ∂b.addHaar) = μ (α i) 0 := by
    rw [disjointed_eq_self fun j hj ↦ hdisj hj.ne, image_singleton,
      eq_univ_of_forall (s := {extChartAt I (α i) (α i)}) fun y ↦ Subsingleton.elim y _,
      Measure.restrict_univ, Basis.addHaar_eq_dirac, integral_dirac,
      Subsingleton.elim (0 : E) (extChartAt I (α i) (α i)),
      μ.coeffInChartAt_apply_of_mem_source b (α i) (mem_extChartAt_source (α i)),
      μ.inChartAt_extChartAt_self (α i)]
    exact congrArg (μ (α i)) (Subsingleton.elim _ 0)
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (f := fun x : M ↦ μ x 0) (s := s)
    (hsupp_eq ▸ hfin.coe_toFinset.ge)]
  exact (Fintype.sum_equiv e.symm (fun i ↦ μ (α i) 0) (fun x : s ↦ μ x.val 0) fun _ ↦ rfl).trans
    (Finset.sum_attach s fun x ↦ μ x 0)

/-- On a zero-dimensional charted manifold, any rough density supported in `{x}` is integrable. -/
public theorem integrableDensity_zeroDim_singleton (μ : RoughDensity I M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) : IntegrableDensity μ :=
  (integrableDensity_zeroDim_iff μ).mpr
    ((finite_singleton x).subset fun _ hy ↦ hs (_root_.subset_tsupport (α := Density E 0) μ hy))

/-- On a zero-dimensional manifold, a rough density supported in `{x}` integrates to `μ x 0`. -/
public theorem integralDensity_zeroDim_singleton (μ : RoughDensity I M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) : integralDensity μ = μ x 0 := by
  rw [integralDensity_zeroDim, finsum_eq_single _ x]; intro y hy
  have h0 : μ y = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E 0) fun h ↦ hy (hs h)
  rw [h0, Density.zero_apply]

/-- On a finite zero-dimensional charted manifold, `integralDensity μ = ∑ x : M, μ x 0`. -/
public theorem integralDensity_finite_zeroDim [Fintype M] (μ : RoughDensity I M 0) :
    integralDensity μ = ∑ x : M, μ x 0 := by rw [integralDensity_zeroDim, finsum_eq_sum_of_fintype]

end ZeroDim

end CoverConstruction

section TopFormComparison

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {m : ℕ}

/-- On an oriented manifold, `φ.toDensity o` is integrable iff `φ` is integrable (all dims). -/
public theorem RoughForm.integrableDensity_toDensity_iff
    (o : Manifold.Orientation I M (Fin m)) (φ : RoughForm I M ℝ m) :
    IntegrableDensity (φ.toDensity o) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  rw [integrableDensity_iff, integrableTopForm_iff, φ.tsupport_toDensity]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun b ↦ forall_congr' fun α ↦ ?_))
  have hunit : IsUnit (Orientation.signBasis l.modelOrientation b : ℝ) := by
    rcases Int.units_eq_one_or (Orientation.signBasis l.modelOrientation b) with h | h <;> simp [h]
  have hσ : Continuous fun x : {x : M // x ∈ (extChartAt I α).source} ↦ l.signAt α x :=
    continuousOn_iff_continuous_domRestrict.mp
      (by simpa only [extChartAt_source] using l.continuousOn_signAt α)
  rw [funext (φ.coeffInChartAt_toDensity l b α), integrable_const_mul_iff hunit,
    φ.integrable_signedInChartAt_iff_unsigned b α (fun x ↦ l.signAt α x) hσ b.addHaar]

/-- **Oriented top-form integration equals density integration** [Lee, Prop. 16.42]:
`integralTopForm o φ = integralDensity (φ.toDensity o)` in all dimensions (incl. boundary/zero). -/
public theorem integralTopForm_eq_integralDensity (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) : integralTopForm o φ = integralDensity (φ.toDensity o) := by
  by_cases hi : IntegrableTopForm φ
  swap; · rw [integralTopForm_eq_zero_of_not_integrable o φ hi,
    integralDensity_eq_zero_of_not_integrable _ (mt (φ.integrableDensity_toDensity_iff o).mp hi)]
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace; obtain ⟨l, rfl⟩ := o.exists_lift
  let b := finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  let c := ChartCover.choose I hi.isCompact
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b c.center c.domain
      c.isOpen_domain c.domain_subset c.covers,
    integralDensity_eq_sum_disjointed_chart_integrals (φ.toDensity (Manifold.Orientation.mk l))
      ((φ.integrableDensity_toDensity_iff _).mpr hi) b c.center c.domain c.isOpen_domain
      c.domain_subset (by rw [φ.tsupport_toDensity]; exact c.covers), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [← integral_const_mul]; simp_rw [← φ.coeffInChartAt_toDensity l b (c.center i)]

end TopFormComparison

section Positivity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

private theorem coeffInChartAt_nonneg_of_basis_nonneg {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (b : Basis (Fin m) ℝ E) (α : M) (y : E) : 0 ≤ μ.coeffInChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [μ.coeffInChartAt_apply_of_mem_target b α hy, RoughDensity.inChartAt_apply]
    let c := b.map (tangentSpaceCastModel I ((extChartAt I α).symm y)).symm.toLinearEquiv
    rw [(μ ((extChartAt I α).symm y)).apply_eq_abs_det_mul c]
    exact mul_nonneg (abs_nonneg _) (hμ _ c)
  · rw [μ.coeffInChartAt_apply_of_notMem_target b α hy]

/-- **Nonnegativity of density integration.** A rough density nonnegative on every tangent basis
has nonnegative integral, in every dimension `m : ℕ` (no regularity, support, or orientation). -/
public theorem integralDensity_nonneg {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c) : 0 ≤ integralDensity μ := by
  by_cases hi : IntegrableDensity μ
  swap; · rw [integralDensity_eq_zero_of_not_integrable μ hi]
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hi.nonempty_basis; have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  rw [integralDensity_eq_choose μ hi b, ChartCover.integral_eq_sum]
  exact Finset.sum_nonneg fun _ _ ↦
    integral_nonneg fun y ↦ coeffInChartAt_nonneg_of_basis_nonneg hμ b _ y

/-- Pointwise dominance on tangent bases implies monotonicity of `integralDensity` in all dims. -/
public theorem integralDensity_mono [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (hle : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), μ x c ≤ ν x c) :
    integralDensity μ ≤ integralDensity ν := by
  rw [← sub_nonneg, ← integralDensity_sub_of_integrable hν hμ]
  exact integralDensity_nonneg fun x c ↦ sub_nonneg.mpr (hle x c)

/-- **Strict positivity of density integration.** An integrable rough density nonnegative on every
tangent basis, positive on one at `x₀`, and continuous on `(extChartAt I x₀).target` satisfies
`0 < integralDensity μ`. -/
public theorem integralDensity_pos_of_continuousOn_inChartAt [IsManifold I 1 M]
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (hnn : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    {x₀ : M} (hcont : ContinuousOn (μ.inChartAt x₀) (extChartAt I x₀).target)
    {c₀ : Basis (Fin m) ℝ (TangentSpace I x₀)} (hpos : 0 < μ x₀ c₀) : 0 < integralDensity μ := by
  let : MeasurableSpace E := borel E; have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hi.nonempty_basis; have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace; let c := ChartCover.choose I hi.isCompact
  rw [integralDensity_eq_coverIntegral μ hi b (c.cons x₀) Subset.rfl, c.integral_cons x₀]
  refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun y ↦ coeffInChartAt_nonneg_of_basis_nonneg hnn b (c.center i) y)
  have hg₀ : 0 < μ.coeffInChartAt b x₀ (extChartAt I x₀ x₀) := by
    obtain ⟨b', hb'⟩ := μ.exists_basis_inChartAt_chart_apply_eq b x₀ (mem_extChartAt_source x₀)
    rw [μ.coeffInChartAt_apply_of_mem_source b x₀ (mem_extChartAt_source x₀), hb',
      (μ x₀).apply_eq_abs_det_mul c₀ b']
    exact mul_pos (abs_pos.mpr (c₀.isUnit_det b').ne_zero) hpos
  exact setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target (μ := b.addHaar) x₀
    (coeffInChartAt_nonneg_of_basis_nonneg hnn b x₀)
    (hi.integrable_coeffInChartAt b x₀).integrableOn
    (μ.continuousOn_coeffInChartAt b x₀ hcont) (mem_extChartAt_target x₀) hg₀

/-- **Strict positivity for continuous density sections** [Lee, Prop. 16.42(b)]: a compactly
supported continuous section nonnegative everywhere and positive at some point satisfies
`0 < integralDensity μ`. -/
public theorem integralDensity_pos [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {μ : (x : M) → DensityBundle I M x} (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ))
    (hnn : ∀ x (c : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (hpos : ∃ x, ∃ c : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x), 0 < μ x c) :
    0 < integralDensity μ :=
  let ⟨_, _, hc₀⟩ := hpos
  integralDensity_pos_of_continuousOn_inChartAt
    (RoughDensity.integrableDensity_of_continuous_section hμ hc) hnn
    (RoughDensity.continuousOn_inChartAt_of_continuousOn_section hμ.continuousOn) hc₀

end Positivity

end TauCeti
