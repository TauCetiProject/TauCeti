/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Chart
public import TauCeti.Geometry.Manifold.ExtChartAt.Integral
public import TauCeti.Geometry.Manifold.Measure
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Disjointed

/-!
# Integration of densities on manifolds

A rough density `μ` of degree `m` is read in a preferred chart through a model basis `b` via
`TauCeti.RoughDensity.inChartAt`. On a chart overlap two coefficients differ by the absolute
determinant of the transition derivative, and two bases change the coefficient by their absolute
change-of-basis determinant. The absolute Jacobian change-of-variables formula therefore makes the
chartwise integrals independent of chart, basis and cover, with no orientation.

`TauCeti.integralDensity μ` is the integral of a compactly supported integrable rough density:
the sum of its chart integrals over the disjointed pieces of a finite open chart cover of its
support. `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals` computes it with any
finite chart-measurable chart cover of the points where the density is nonzero, and any model
basis.

As for top forms, the manifold needs no Hausdorff assumption or measurable structure, and may
have boundary or corners: only the model carries its Borel measurable structure.

## Main definitions

* `TauCeti.IntegrableDensity`: compact support and integrable coefficients in every chart.
* `TauCeti.integralDensity`: the integral of a rough density.

## Main results

* `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals`: independence of chart, basis and
  cover.
* `TauCeti.integralDensity_modelSpace`: on the model space the integral is the Lebesgue integral
  of the value on a model basis.
* `TauCeti.integralDensity_eq_sum_chooseChartCover`,
  `TauCeti.integralDensity_eq_integral_inChartAt_of_ae_support`: chosen-cover and almost-everywhere
  single-chart formulas.
* `TauCeti.integralDensity_real_eq_integral`: real-line specialization.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

namespace RoughDensity

variable [MeasurableSpace E] [BorelSpace E]

/-- Chart integrals of a density, and their integrability, agree on an actual chart overlap,
by the absolute Jacobian change-of-variables formula. No orientation or sign data enter. -/
theorem setIntegral_inChartAt_changeChart [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s)) (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ y in (extChartAt I α) '' s, μ.inChartAt b α y ∂ν) =
        (∫ y in (extChartAt I β) '' s, μ.inChartAt b β y ∂ν) ∧
      (IntegrableOn (μ.inChartAt b α) ((extChartAt I α) '' s) ν ↔
        IntegrableOn (μ.inChartAt b β) ((extChartAt I β) '' s) ν) := by
  have := Module.Finite.of_basis b
  exact TauCeti.setIntegral_image_extChartAt_changeChart α β hsub hs
    (fun x hx ↦ by
      rw [smul_eq_mul]
      exact (inChartAt_changeChart μ b (hsub hx).1 (hsub hx).2).symm) ν

/-- Chart integrals of a density over a set do not depend on the model basis, each basis
carrying its normalized Haar measure. -/
theorem setIntegral_inChartAt_basis_eq (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) (s : Set E) :
    (∫ y in s, μ.inChartAt b' α y ∂b'.addHaar) = ∫ y in s, μ.inChartAt b α y ∂b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [b.addHaar_eq_smul_of_basis b', Measure.restrict_smul, integral_smul_measure]
  simp_rw [inChartAt_basis_change μ b b']
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hd), one_mul]

/-- Integrability of the chart coefficients of a density does not depend on the model basis. -/
theorem integrable_inChartAt_basis_iff (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) :
    Integrable (μ.inChartAt b' α) b'.addHaar ↔ Integrable (μ.inChartAt b α) b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [b.addHaar_eq_smul_of_basis b', integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  have heq : μ.inChartAt b' α = fun y ↦ |b.det b'| * μ.inChartAt b α y :=
    funext (inChartAt_basis_change μ b b' α)
  rw [heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hd)) _

end RoughDensity

/-- A rough density is integrable when it has compact support and its coefficients are
integrable in every preferred chart and every model basis. The model uses its Borel measurable
structure. In degrees other than the dimension of the model there is no model basis, and no
density is integrable. -/
def IntegrableDensity (μ : RoughDensity I M m) : Prop := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact IsCompact (_root_.tsupport (α := Density E m) μ) ∧ Nonempty (Basis (Fin m) ℝ E) ∧
    ∀ (b : Basis (Fin m) ℝ E) (α : M), Integrable (μ.inChartAt b α) b.addHaar

section WithMeasure

variable [MeasurableSpace E] [BorelSpace E]

/-- The coordinate characterization of integrability, with any Borel measurable structure on
the model. -/
theorem integrableDensity_iff (μ : RoughDensity I M m) :
    IntegrableDensity μ ↔ IsCompact (_root_.tsupport (α := Density E m) μ) ∧
      Nonempty (Basis (Fin m) ℝ E) ∧
      ∀ (b : Basis (Fin m) ℝ E) (α : M), Integrable (μ.inChartAt b α) b.addHaar := by
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  rfl

/-- One model basis suffices to check integrability of a compactly supported density. -/
theorem integrableDensity_of_basis {μ : RoughDensity I M m}
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) (b : Basis (Fin m) ℝ E)
    (hi : ∀ α : M, Integrable (μ.inChartAt b α) b.addHaar) : IntegrableDensity μ :=
  (integrableDensity_iff μ).mpr ⟨hc, ⟨b⟩, fun b' α ↦
    (μ.integrable_inChartAt_basis_iff b b' α).mpr (hi α)⟩

section OpenCover

variable [IsManifold I 1 M]

/-- Integrability on an open chart cover of the support introduces integrability of a compactly
supported density. One model basis suffices. -/
theorem RoughDensity.integrableDensity_of_open_cover {J : Type*} (μ : RoughDensity I M m)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) (b : Basis (Fin m) ℝ E)
    (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i))
    (hsource : ∀ i, u i ⊆ (chartAt H (β i)).source)
    (hcover : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (μ.inChartAt b (β i)) ((extChartAt I (β i)) '' u i) b.addHaar) :
    IntegrableDensity μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  refine integrableDensity_of_basis hc b fun α ↦
    integrable_of_isCompact_of_open_cover_extChartAt (I := I) α hc u hu hcover (fun i ↦ ?_)
      fun y hy ↦ ?_
  · have hsub : (extChartAt I α).source ∩ u i ⊆
        (extChartAt I α).source ∩ (extChartAt I (β i)).source := fun x hx ↦
      ⟨hx.1, by simpa only [extChartAt_source] using hsource i hx.2⟩
    apply (μ.setIntegral_inChartAt_changeChart b α (β i) hsub
      ((hu i).measurableSet_image_extChartAt_source_inter α) b.addHaar).2.mpr
    exact (hlocal i).mono_set (image_mono inter_subset_right)
  · by_cases hyt : y ∈ (extChartAt I α).target
    · have hne : μ ((extChartAt I α).symm y) ≠ 0 := fun hz ↦ hy (by
        rw [RoughDensity.inChartAt_of_mem_target μ b α hyt, hz, Density.zero_apply])
      exact ⟨hyt, subset_tsupport (α := Density E m) μ hne⟩
    · exact absurd (RoughDensity.inChartAt_of_notMem_target μ b α hyt) hy

/-- A compactly supported density whose support lies in a preferred chart is integrable exactly
when its coefficient in that chart, in one model basis, is integrable. -/
theorem RoughDensity.integrableDensity_iff_of_tsupport_subset_chart {μ : RoughDensity I M m}
    (b : Basis (Fin m) ℝ E) (α : M) (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (chartAt H α).source) :
    IntegrableDensity μ ↔ Integrable (μ.inChartAt b α) b.addHaar := by
  refine ⟨fun h ↦ ((integrableDensity_iff μ).mp h).2.2 b α, fun hi ↦ ?_⟩
  exact μ.integrableDensity_of_open_cover hc b (fun _ : Unit ↦ α) (fun _ ↦ (chartAt H α).source)
    (fun _ ↦ (chartAt H α).open_source) (fun _ ↦ Subset.rfl)
    (fun x hx ↦ mem_iUnion.mpr ⟨(), hs hx⟩) fun _ ↦ hi.integrableOn

end OpenCover

end WithMeasure

/-- Integrable densities have compact topological support. -/
theorem IntegrableDensity.isCompact {μ : RoughDensity I M m} (hi : IntegrableDensity μ) :
    IsCompact (_root_.tsupport (α := Density E m) μ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact ((integrableDensity_iff μ).mp hi).1

/-- An integrable density has a model basis of the size of its degree. -/
theorem IntegrableDensity.nonempty_basis {μ : RoughDensity I M m} (hi : IntegrableDensity μ) :
    Nonempty (Basis (Fin m) ℝ E) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact ((integrableDensity_iff μ).mp hi).2.1

/-- The coefficients of an integrable density are integrable in every preferred chart and every
model basis. -/
theorem IntegrableDensity.integrable_inChartAt [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) (α : M) :
    Integrable (μ.inChartAt b α) b.addHaar :=
  ((integrableDensity_iff μ).mp hi).2.2 b α

/-- The sum of two integrable densities is integrable. -/
theorem IntegrableDensity.add {μ ν : RoughDensity I M m} (hμ : IntegrableDensity μ)
    (hν : IntegrableDensity ν) : IntegrableDensity (μ + ν) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ hν ⊢
  refine ⟨(hμ.1.union hν.1).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_add (α := Density E m) μ ν), hμ.2.1, fun b α ↦ ?_⟩
  rw [RoughDensity.inChartAt_add]
  exact (hμ.2.2 b α).add (hν.2.2 b α)

/-- A constant multiple of an integrable density is integrable. -/
theorem IntegrableDensity.smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) (c : ℝ) :
    IntegrableDensity (c • μ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ ⊢
  refine ⟨hμ.1.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_right (α := Density E m) (fun _ ↦ c) μ),
    hμ.2.1, fun b α ↦ ?_⟩
  rw [RoughDensity.inChartAt_smul]
  exact (hμ.2.2 b α).smul c

/-- Multiplication by a nonzero scalar preserves density integrability. -/
theorem integrableDensity_smul_iff {c : ℝ} (hc : c ≠ 0) (μ : RoughDensity I M m) :
    IntegrableDensity (c • μ) ↔ IntegrableDensity μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul c⟩
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h.smul c⁻¹

/-- In top degree, witnessed by a model basis `b` of the degree's size, the zero density is
integrable. -/
theorem IntegrableDensity.zero (b : Basis (Fin m) ℝ E) :
    IntegrableDensity (0 : RoughDensity I M m) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff]
  refine ⟨?_, ⟨b⟩, fun b α ↦ ?_⟩
  · exact isCompact_empty.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_zero (X := M) (α := Density E m)).le
  · rw [RoughDensity.inChartAt_zero]
    exact integrable_zero E ℝ b.addHaar

/-- Negation preserves density integrability. -/
theorem IntegrableDensity.neg {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) :
    IntegrableDensity (-μ) := by
  simpa only [neg_one_smul] using hμ.smul (-1)

/-- The difference of two integrable densities is integrable. -/
theorem IntegrableDensity.sub {μ ν : RoughDensity I M m} (hμ : IntegrableDensity μ)
    (hν : IntegrableDensity ν) : IntegrableDensity (μ - ν) := by
  simpa only [sub_eq_add_neg] using hμ.add hν.neg

/-- In top degree, witnessed by a model basis `b` of the degree's size, finite sums of integrable
densities are integrable. The basis is needed for the empty sum. -/
theorem IntegrableDensity.sum {ι : Type*} (b : Basis (Fin m) ℝ E)
    (μ : ι → RoughDensity I M m) (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    IntegrableDensity (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IntegrableDensity.zero (I := I) (M := M) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hμ i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj))

/-- The sum of the chart integrals of a density over the disjointed pieces of a finite chart
cover. -/
private def coverSum [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E)
    {n : ℕ} (α : Fin n → M) (u : Fin n → Set M) : ℝ :=
  ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i, μ.inChartAt b (α i) y ∂b.addHaar

/-- `coverSum` for the chosen finite open chart cover of a compact set `K`. -/
private def chosenCoverSum [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (K : Set M) (hK : IsCompact K) : ℝ :=
  let c := chooseChartCover (I := I) K hK
  coverSum μ b c.center c.domain

private theorem chosenCoverSum_congr [MeasurableSpace E] [BorelSpace E]
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) {K K' : Set M} (hK : IsCompact K)
    (hK' : IsCompact K') (h : K = K') : chosenCoverSum μ b K hK = chosenCoverSum μ b K' hK' := by
  subst h
  rfl

private theorem chosenCoverSum_smul [MeasurableSpace E] [BorelSpace E] (c : ℝ)
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (K : Set M) (hK : IsCompact K) :
    chosenCoverSum (c • μ) b K hK = c * chosenCoverSum μ b K hK := by
  simp only [chosenCoverSum, coverSum, RoughDensity.inChartAt_smul, Pi.smul_apply, smul_eq_mul,
    integral_const_mul, Finset.mul_sum]

/-- The integral of a rough density. It is zero unless the density is integrable, in particular
unless its degree is the dimension of the model. The sum of chart integrals over the disjointed
pieces of a chosen finite open chart cover of the support defines it; by
`integralDensity_eq_sum_disjointed_chart_integrals` it does not depend on that cover or on the
model basis. -/
def integralDensity (μ : RoughDensity I M m) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact if hi : IntegrableDensity μ then
    chosenCoverSum μ (Classical.choice ((integrableDensity_iff μ).mp hi).2.1)
      (_root_.tsupport (α := Density E m) μ) hi.isCompact
  else 0

/-- A nonintegrable density has zero integral. -/
theorem integralDensity_eq_zero_of_not_integrable {μ : RoughDensity I M m}
    (hi : ¬IntegrableDensity μ) : integralDensity μ = 0 := by
  rw [integralDensity, dite_eq_right hi]

/-- The integral of an integrable density is the sum of its chart integrals over the disjointed
pieces of any finite chart-measurable chart cover of the points where it is nonzero, in any model
basis. -/
theorem integralDensity_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) {n : ℕ} (α : Fin n → M) (u : Fin n → Set M)
    (hu : ∀ i, IsChartMeasurable I (u i)) (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : {x | μ x ≠ 0} ⊆ ⋃ i, u i) :
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i, μ.inChartAt b (α i) y ∂b.addHaar := by
  classical
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  rw [integralDensity, dite_eq_left hi]
  unfold chosenCoverSum coverSum
  let c := chooseChartCover (I := I) _ hi.isCompact
  simp_rw [μ.setIntegral_inChartAt_basis_eq b]
  have hint (β : M) (t : Set E) : IntegrableOn (μ.inChartAt b β) t b.addHaar :=
    (hi.integrable_inChartAt b β).integrableOn
  -- The coefficient of a density vanishes at the coordinates of the points where it vanishes.
  have hz (β : M) (x : M) (hx : x ∈ (extChartAt I β).source) (hx0 : x ∉ {x | μ x ≠ 0}) :
      μ.inChartAt b β (extChartAt I β x) = 0 := by
    have hμ : μ ((extChartAt I β).symm (extChartAt I β x)) = 0 := by
      rw [(extChartAt I β).left_inv hx]
      exact of_not_not hx0
    rw [RoughDensity.inChartAt_of_mem_target μ b β ((extChartAt I β).map_source hx), hμ,
      Density.zero_apply]
  exact sum_setIntegral_image_extChartAt_disjointed_eq hz
    (fun β γ _ hsub hm ↦ (μ.setIntegral_inChartAt_changeChart b β γ hsub
      (hm.image_extChartAt β (hsub.trans inter_subset_left)) b.addHaar).1)
    c.center c.domain (fun i ↦ (c.isOpen_domain i).isChartMeasurable) c.domain_subset
    (fun x hx ↦ c.covers (subset_closure hx)) (fun _ ↦ hint _ _)
    α u hu hs hc (fun _ ↦ hint _ _)

/-- An integrable density that vanishes outside a preferred chart has that chart's integral. -/
theorem integralDensity_eq_integral_inChartAt [IsManifold I 1 M] [MeasurableSpace E]
    [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E)
    (α : M) (hs : {x | μ x ≠ 0} ⊆ (extChartAt I α).source) :
    integralDensity μ = ∫ y, μ.inChartAt b α y ∂b.addHaar := by
  rw [integralDensity_eq_sum_disjointed_chart_integrals hi b (fun _ : Fin 1 ↦ α)
    (fun _ ↦ (extChartAt I α).source) (fun _ ↦ (isOpen_extChartAt_source α).isChartMeasurable)
    (fun _ ↦ Subset.rfl) (hs.trans (subset_iUnion_of_subset 0 Subset.rfl))]
  rw [Fin.sum_univ_one, disjointed_of_isMin _ (fun j _ ↦ le_of_eq (Subsingleton.elim _ _)),
    (extChartAt I α).image_source_eq_target]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
  exact μ.inChartAt_of_notMem_target b α hy

/-- The integral of an integrable density is the sum of its chart integrals over the disjointed
pieces of `chooseChartCover` for its support. -/
theorem integralDensity_eq_sum_chooseChartCover [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) :
    let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (c.center i)) '' disjointed c.domain i,
        μ.inChartAt b (c.center i) y ∂b.addHaar := by
  let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
  exact integralDensity_eq_sum_disjointed_chart_integrals hi b c.center c.domain
    (fun i ↦ (c.isOpen_domain i).isChartMeasurable) c.domain_subset
    fun x hx ↦ c.covers (subset_closure hx)

/-- A single preferred chart computes `integralDensity` whenever `μ` vanishes outside that chart up
to a chartwise null set. -/
theorem integralDensity_eq_integral_inChartAt_of_ae_support [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M) (hs : IsNullSet I ({x | μ x ≠ 0} \ (extChartAt I α).source)) :
    integralDensity μ = ∫ y, μ.inChartAt b α y ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
  rw [integralDensity_eq_sum_chooseChartCover hi b]
  simp_rw [← ChartCover.piece_def]
  refine sum_setIntegral_image_extChartAt_piece_eq_integral c α (hi.integrable_inChartAt b α)
    (μ.support_inChartAt_subset_target b α)
    (fun _ hx hn ↦ μ.inChartAt_eq_zero_of_notMem_tsupport b α hx hn)
    (fun i s hsub hsm ↦ (μ.setIntegral_inChartAt_changeChart b (c.center i) α hsub
      (hsm.image_extChartAt (c.center i) (hsub.trans inter_subset_left)) b.addHaar).1)
    fun i ↦ ?_
  filter_upwards [hs.ae_extChartAt_symm_notMem_of_sdiff_source (c.center i) b.addHaar] with y hy
  intro hxo ⟨x, hx, hxy⟩
  exact μ.inChartAt_eq_zero_of_apply_eq_zero b (c.center i)
    (not_not.mp (hy hxo (hxy ▸ (extChartAt I (c.center i)).map_source (c.piece_subset i hx))))

/-- On the model space, the integral of an integrable density is the Lebesgue integral of its
value on a model basis, for the Haar measure of that basis. -/
theorem integralDensity_modelSpace [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity 𝓘(ℝ, E) E m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) :
    integralDensity μ = ∫ y, μ y b ∂b.addHaar := by
  rw [integralDensity_eq_integral_inChartAt hi b 0 (by simp),
    RoughDensity.inChartAt_modelSpace]

/-- On a model normed space `E`, `μ` is integrable iff `tsupport μ` is compact and `x ↦ μ x b` is
Haar-integrable against `b.addHaar` in any model basis `b`. -/
theorem integrableDensity_modelSpace_iff [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity 𝓘(ℝ, E) E m} (b : Basis (Fin m) ℝ E) :
    IntegrableDensity μ ↔
      IsCompact (_root_.tsupport (α := Density E m) μ) ∧ Integrable (fun x ↦ μ x b) b.addHaar := by
  refine ⟨fun hi ↦ ⟨hi.isCompact, ?_⟩, fun ⟨hc, hint⟩ ↦ ?_⟩
  · rw [← μ.inChartAt_modelSpace b 0]
    exact hi.integrable_inChartAt b 0
  · refine (μ.integrableDensity_iff_of_tsupport_subset_chart b 0 hc (by simp)).mpr ?_
    rwa [μ.inChartAt_modelSpace b 0]

/-- Evaluating a `1`-density on `ℝ` at `Basis.singleton (Fin 1) ℝ` agrees with evaluating it on the
constant tuple `fun _ ↦ 1`. -/
private theorem apply_basis_singleton (μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1) (t : ℝ) :
    μ t (Basis.singleton (Fin 1) ℝ) = μ t (fun _ ↦ (1 : ℝ)) :=
  congrArg (μ t) (by rw [Basis.coe_singleton, Pi.one_def])

/-- On `ℝ`, a `1`-density `μ` is integrable iff `tsupport μ` is compact and
`t ↦ μ t (fun _ ↦ 1)` is Lebesgue-integrable. -/
theorem integrableDensity_real_iff {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1} :
    IntegrableDensity μ ↔
      IsCompact (_root_.tsupport (α := Density ℝ 1) μ) ∧
        Integrable (fun t ↦ μ t (fun _ ↦ (1 : ℝ))) := by
  simp only [integrableDensity_modelSpace_iff (Basis.singleton (Fin 1) ℝ),
    Basis.addHaar_singleton, apply_basis_singleton]

/-- On `ℝ`, the integral of an integrable `1`-density is `∫ t, μ t (fun _ ↦ 1)`. -/
theorem integralDensity_real_eq_integral {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1}
    (hi : IntegrableDensity μ) : integralDensity μ = ∫ t, μ t (fun _ ↦ (1 : ℝ)) := by
  simp only [integralDensity_modelSpace hi (Basis.singleton (Fin 1) ℝ),
    Basis.addHaar_singleton, apply_basis_singleton]

/-- The zero density has zero integral. -/
@[simp]
theorem integralDensity_zero : integralDensity (0 : RoughDensity I M m) = 0 := by
  classical
  by_cases hi : IntegrableDensity (0 : RoughDensity I M m)
  · let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    rw [integralDensity, dite_eq_left hi]
    simp [chosenCoverSum, coverSum]
  · exact integralDensity_eq_zero_of_not_integrable hi

/-- The integral of densities is additive on integrable densities. -/
theorem integralDensity_add [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ + ν) = integralDensity μ + integralDensity ν := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hμ.nonempty_basis
  let c := chooseChartCover (I := I) _ (hμ.isCompact.union hν.isCompact)
  have hu (i : Fin c.n) : IsChartMeasurable I (c.domain i) :=
    (c.isOpen_domain i).isChartMeasurable
  rw [integralDensity_eq_sum_disjointed_chart_integrals (hμ.add hν) b c.center c.domain hu
      c.domain_subset fun x hx ↦ c.covers (tsupport_add (α := Density E m) μ ν (subset_closure hx)),
    integralDensity_eq_sum_disjointed_chart_integrals hμ b c.center c.domain hu c.domain_subset
      fun x hx ↦ c.covers (Or.inl (subset_closure hx)),
    integralDensity_eq_sum_disjointed_chart_integrals hν b c.center c.domain hu c.domain_subset
      fun x hx ↦ c.covers (Or.inr (subset_closure hx)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RoughDensity.inChartAt_add]
  exact integral_add (hμ.integrable_inChartAt b (c.center i)).integrableOn
    (hν.integrable_inChartAt b (c.center i)).integrableOn

/-- Integration of densities commutes with finite sums of integrable densities. -/
theorem integralDensity_sum [IsManifold I 1 M] {ι : Type*} (μ : ι → RoughDensity I M m)
    (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    integralDensity (∑ i ∈ s, μ i) = ∑ i ∈ s, integralDensity (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hμi := hμ i (Finset.mem_insert_self i s)
    let : MeasurableSpace E := borel E
    let : BorelSpace E := ⟨rfl⟩
    obtain ⟨b⟩ := hμi.nonempty_basis
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integralDensity_add hμi (IntegrableDensity.sum b μ s fun j hj ↦
        hμ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)]

/-- Constant scalar multiplication commutes with the integral of densities, including
nonintegrable ones. -/
theorem integralDensity_smul (c : ℝ) (μ : RoughDensity I M m) :
    integralDensity (c • μ) = c * integralDensity μ := by
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul, zero_mul, integralDensity_zero]
  by_cases hμ : IntegrableDensity μ
  swap
  · rw [integralDensity_eq_zero_of_not_integrable hμ, integralDensity_eq_zero_of_not_integrable
      (mt (integrableDensity_smul_iff hc0 μ).mp hμ), mul_zero]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hsupp : tsupport (α := Density E m) (c • μ) = tsupport (α := Density E m) μ :=
    congrArg closure (Function.support_const_smul_of_ne_zero (M := Density E m) c μ hc0)
  rw [integralDensity, dite_eq_left (hμ.smul c), integralDensity, dite_eq_left hμ,
    chosenCoverSum_congr _ _ _ hμ.isCompact hsupp, chosenCoverSum_smul]

/-- The integral of the negative of a density is the negative of its integral. -/
@[simp]
theorem integralDensity_neg (μ : RoughDensity I M m) :
    integralDensity (-μ) = -integralDensity μ := by
  simpa only [neg_one_smul, neg_one_mul] using integralDensity_smul (-1) μ

/-- The integral of densities is subtractive on integrable densities. -/
theorem integralDensity_sub [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ - ν) = integralDensity μ - integralDensity ν := by
  rw [sub_eq_add_neg, integralDensity_add hμ hν.neg, integralDensity_neg, ← sub_eq_add_neg]

end TauCeti
