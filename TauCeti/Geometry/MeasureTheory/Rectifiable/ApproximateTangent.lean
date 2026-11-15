/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
public import TauCeti.Geometry.MeasureTheory.Rectifiable.MeasurableTangent
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Existence, uniqueness, and measurability of approximate tangent planes

An **approximate tangent `k`-plane** to a set `E` in a real normed space `V` at a point `x` is a
finite-dimensional subspace `P : Submodule ℝ V` of dimension `k` such that `E` has strictly
positive upper `k`-dimensional Euclidean Hausdorff density at `x` and the portion of `E` outside
every cone `{v | infDist v P ≤ ε * ‖v‖}` around `P` at `x` has `k`-dimensional density zero
(`TauCeti.IsApproxTangentPlane`). Requiring `FiniteDimensional ℝ P` alongside
`Module.finrank ℝ P = k` excludes infinite-dimensional subspaces when `k = 0` and `V` is
infinite-dimensional. When such a `k`-plane exists uniquely, `TauCeti.approxTangentPlane k E x`
denotes it, defaulting to `⊥` otherwise; it always carries a `FiniteDimensional ℝ` instance.

Unlike the pointwise tangent cone, an approximate tangent plane ignores subsets of `k`-density
zero (`TauCeti.isApproxTangentPlane_congr_of_tendsto_symmDiff_div`), so modifying `E` by a
`μHE[k]`-null set leaves `IsApproxTangentPlane k E P x` and `approxTangentPlane k E x` unchanged at
every point (`TauCeti.isApproxTangentPlane_congr_ae`, `TauCeti.approxTangentPlane_congr_ae`).

At any Lebesgue density-one parameter point of a differentiable inverse-Lipschitz map `f` into `E`,
directional lower Hausdorff density forces every approximate tangent plane to `E` at `f x₀` to
equal `range A`, where `A` is the derivative of `f`
(`HasFDerivWithinAt.eq_range_of_isApproxTangentPlane`).
Combining this deterministic uniqueness with the density-one theorem (`Rectifiable.Density`),
bi-Lipschitz decompositions (`Rectifiable.Bilipschitz`), and measurable projection extensions
(`Rectifiable.MeasurableTangent`) yields:

* **almost everywhere existence and uniqueness** of approximate tangent `k`-planes on every
  null-measurable, countably `k`-rectifiable set `E` with locally finite `μHE[k]` measure
  (`TauCeti.CountablyRectifiable.ae_existsUnique_isApproxTangentPlane`);
* **chart identification** `approxTangentPlane k E (f x) = (fderiv ℝ f x).range` almost everywhere
  along any bi-Lipschitz patch `f '' s ⊆ E`
  (`LipschitzWith.ae_existsUnique_isApproxTangentPlane_image`);
* **measurability** of the canonical orthogonal projection field
  `x ↦ (approxTangentPlane k E x).starProjection` with respect to `μHE[k].restrict E`
  (`TauCeti.CountablyRectifiable.aemeasurable_starProjection_approxTangentPlane`).

All statements include `k = 0`.

## Main definitions

* `TauCeti.IsApproxTangentPlane k E P x`: predicate that `P` is an approximate tangent `k`-plane
  to `E` at `x`.
* `TauCeti.approxTangentPlane k E x`: the unique approximate tangent `k`-plane to `E` at `x`, or
  `⊥` when existence or uniqueness fails.

## Main results

* `TauCeti.isApproxTangentPlane_congr_of_tendsto_symmDiff_div`,
  `TauCeti.approxTangentPlane_congr_ae`: invariance under `k`-density-zero symmetric difference
  and `μHE[k]`-null modifications.
* `HasFDerivWithinAt.eq_range_of_isApproxTangentPlane`,
  `HasFDerivWithinAt.existsUnique_isApproxTangentPlane_of_tendsto_diff`: deterministic uniqueness
  and derivative-range identification at parameter density-one points.
* `TauCeti.CountablyRectifiable.ae_existsUnique_isApproxTangentPlane`: almost everywhere existence
  and uniqueness on countably `k`-rectifiable sets with locally finite `μHE[k]` measure.
* `TauCeti.CountablyRectifiable.aemeasurable_starProjection_approxTangentPlane`: almost everywhere
  measurability of the canonical orthogonal projection field.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (Theorem 11.6).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapters 15–16 (Theorem 15.19).
* H. Federer, *Geometric Measure Theory*, 3.2.19.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal symmDiff Topology

namespace TauCeti

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `IsApproxTangentPlane k E P x` states that `P : Submodule ℝ V` is an approximate tangent
`k`-plane to `E` at `x`: `P` is finite-dimensional of dimension `k`, `E` has strictly positive
upper `k`-dimensional Euclidean Hausdorff density at `x`, and the portion of `E` outside every
cone around `P` at `x` has `k`-dimensional density zero. -/
structure IsApproxTangentPlane (k : ℕ) (E : Set V) (P : Submodule ℝ V) (x : V) : Prop where
  /-- `P` is finite-dimensional, ruling out infinite-dimensional subspaces when `k = 0`. -/
  finiteDimensional : FiniteDimensional ℝ P
  /-- `P` has dimension `k`. -/
  finrank_eq : Module.finrank ℝ P = k
  /-- `E` has strictly positive upper `k`-dimensional Hausdorff density at `x`. -/
  limsup_pos : 0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
    volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0)
  /-- Outside every cone around `P` at `x`, `E` has `k`-dimensional Hausdorff density zero. -/
  tendsto_outside_cone_div : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

/-- Characteristic equivalence for `IsApproxTangentPlane`. -/
theorem isApproxTangentPlane_iff {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V} :
    IsApproxTangentPlane k E P x ↔
      FiniteDimensional ℝ P ∧ Module.finrank ℝ P = k ∧
        0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ∧
        ∀ ε > (0 : ℝ), Tendsto (fun r =>
          μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
            volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

namespace IsApproxTangentPlane

/-- Construct `IsApproxTangentPlane` when `FiniteDimensional ℝ P` is available as an instance. -/
theorem of_finrank_eq {k : ℕ} {E : Set V} {P : Submodule ℝ V} [FiniteDimensional ℝ P] {x : V}
    (hdim : Module.finrank ℝ P = k)
    (hpos : 0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E P x :=
  ⟨inferInstance, hdim, hpos, hcone⟩

/-- Construct `IsApproxTangentPlane` at a point where `E` has `k`-dimensional density one. -/
theorem of_tendsto_inter_closedBall_div {k : ℕ} {E : Set V} {P : Submodule ℝ V}
    [FiniteDimensional ℝ P] {x : V} (hdim : Module.finrank ℝ P = k)
    (hdens : Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E P x := by
  refine of_finrank_eq hdim ?_ hcone
  rw [hdens.limsup_eq]
  exact zero_lt_one

/-- Every approximate tangent plane is a closed subspace of the ambient normed space. -/
theorem isClosed {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E P x) : IsClosed (P : Set V) := by
  have := h.finiteDimensional
  exact P.isClosed_of_finiteDimensional

/-- Any point admitting an approximate tangent plane to `E` lies in `closure E`. -/
theorem mem_closure {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E P x) : x ∈ closure E := by
  by_contra hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
  have hzero : Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
    have hempty : E ∩ closedBall x r = ∅ := by
      refine eq_empty_of_forall_notMem fun z ⟨hzE, hzr⟩ => ?_
      have hzb : z ∈ ball x δ := mem_ball.2 ((mem_closedBall.1 hzr).trans_lt hr)
      exact hball hzb (subset_closure hzE)
    rw [hempty, measure_empty, ENNReal.zero_div]
  exact h.limsup_pos.ne' hzero.limsup_eq

/-- A `0`-dimensional approximate tangent plane is necessarily `⊥`. -/
theorem eq_bot_of_zero {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane 0 E P x) : P = ⊥ := by
  have := h.finiteDimensional
  exact Submodule.finrank_eq_zero.1 h.finrank_eq

/-- Approximate tangency is preserved when both `E₁ \ E₂` and `E₂ \ E₁` have `k`-dimensional
density zero at `x`. -/
theorem of_tendsto_diff {k : ℕ} {E₁ E₂ : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E₁ P x)
    (h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
    (h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E₂ P x where
  finiteDimensional := h.finiteDimensional
  finrank_eq := h.finrank_eq
  limsup_pos := by
    refine h.limsup_pos.trans_le ((limsup_measure_inter_div_le_of_tendsto_diff h12).trans ?_)
    refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
    gcongr
    exact inter_subset_right
  tendsto_outside_cone_div ε hε := by
    have hsum : Tendsto (fun r =>
        μHE[k] {z ∈ E₁ ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
        μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using (h.tendsto_outside_cone_div ε hε).add h21
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ((measure_mono ?_).trans (measure_union_le _ _)) _
    intro z ⟨⟨hzE₂, hzr⟩, hzcone⟩
    by_cases hzE₁ : z ∈ E₁
    · exact Or.inl ⟨⟨hzE₁, hzr⟩, hzcone⟩
    · exact Or.inr ⟨⟨hzE₂, hzE₁⟩, hzr⟩

end IsApproxTangentPlane

/-- The empty set has no approximate tangent plane at any point. -/
@[simp]
theorem not_isApproxTangentPlane_empty (k : ℕ) (P : Submodule ℝ V) (x : V) :
    ¬ IsApproxTangentPlane k (∅ : Set V) P x := by
  intro h
  have h0 := h.limsup_pos
  simp only [empty_inter, measure_empty, ENNReal.zero_div, limsup_const, lt_self_iff_false] at h0

/-- The canonical approximate tangent `k`-plane to `E` at `x`: the unique `P` satisfying
`IsApproxTangentPlane k E P x` if one exists uniquely, and `⊥` otherwise. -/
noncomputable def approxTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V :=
  open Classical in
  if h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x then h.choose else ⊥

/-- `approxTangentPlane k E x` is always finite-dimensional, even without finite-dimensionality of
the ambient space or existence of an approximate tangent plane. -/
instance instFiniteDimensionalApproxTangentPlane (k : ℕ) (E : Set V) (x : V) :
    FiniteDimensional ℝ (approxTangentPlane k E x) := by
  by_cases h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x
  · have heq : approxTangentPlane k E x = h.choose := by
      simp only [approxTangentPlane, h, ↓reduceDIte]
    exact heq ▸ h.choose_spec.1.finiteDimensional
  · have heq : approxTangentPlane k E x = ⊥ := by
      simp only [approxTangentPlane, h, ↓reduceDIte]
    exact heq ▸ inferInstance

/-- When `E` has a unique approximate tangent `k`-plane at `x`, `approxTangentPlane k E x`
satisfies `IsApproxTangentPlane`. -/
theorem isApproxTangentPlane_approxTangentPlane {k : ℕ} {E : Set V} {x : V}
    (h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x) :
    IsApproxTangentPlane k E (approxTangentPlane k E x) x := by
  simp only [approxTangentPlane, h, ↓reduceDIte]
  exact h.choose_spec.1

/-- When `E` has a unique approximate tangent `k`-plane at `x`, `approxTangentPlane k E x` equals
any `P` satisfying `IsApproxTangentPlane k E P x`. -/
theorem approxTangentPlane_eq_of_existsUnique {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hP : IsApproxTangentPlane k E P x) :
    approxTangentPlane k E x = P :=
  h.unique (isApproxTangentPlane_approxTangentPlane h) hP

/-- Outside the locus of unique existence, `approxTangentPlane` takes the junk value `⊥`. -/
theorem approxTangentPlane_of_not_existsUnique {k : ℕ} {E : Set V} {x : V}
    (h : ¬ ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x) :
    approxTangentPlane k E x = ⊥ := by
  simp only [approxTangentPlane, h, ↓reduceDIte]

/-- At any point of unique existence, `approxTangentPlane k E x` has dimension `k`. -/
theorem finrank_approxTangentPlane {k : ℕ} {E : Set V} {x : V}
    (h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x) :
    Module.finrank ℝ (approxTangentPlane k E x) = k :=
  (isApproxTangentPlane_approxTangentPlane h).finrank_eq

@[simp]
theorem approxTangentPlane_empty (k : ℕ) (x : V) : approxTangentPlane k (∅ : Set V) x = ⊥ :=
  approxTangentPlane_of_not_existsUnique fun ⟨P, hP, _⟩ => not_isApproxTangentPlane_empty k P x hP

@[simp]
theorem approxTangentPlane_zero (E : Set V) (x : V) : approxTangentPlane 0 E x = ⊥ := by
  by_cases h : ∃! P : Submodule ℝ V, IsApproxTangentPlane 0 E P x
  · exact (isApproxTangentPlane_approxTangentPlane h).eq_bot_of_zero
  · exact approxTangentPlane_of_not_existsUnique h

/-- Approximate tangency at `x` depends on `E` only up to symmetric differences of `k`-dimensional
density zero at `x`. -/
theorem isApproxTangentPlane_congr_of_tendsto_symmDiff_div {k : ℕ} {E₁ E₂ : Set V}
    {P : Submodule ℝ V} {x : V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x := by
  have h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsym
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun r => by gcongr; exact subset_union_left)
  have h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsym
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun r => by gcongr; exact subset_union_right)
  exact ⟨fun h => h.of_tendsto_diff h12 h21, fun h => h.of_tendsto_diff h21 h12⟩

/-- `approxTangentPlane k E x` depends on `E` only up to symmetric differences of `k`-dimensional
density zero at `x`. -/
theorem approxTangentPlane_congr_of_tendsto_symmDiff_div {k : ℕ} {E₁ E₂ : Set V} {x : V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x := by
  have hiff (P : Submodule ℝ V) : IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x :=
    isApproxTangentPlane_congr_of_tendsto_symmDiff_div hsym
  by_cases h1 : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E₁ P x
  · have h2 : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E₂ P x := by
      simpa only [← hiff] using h1
    exact (approxTangentPlane_eq_of_existsUnique h1
      ((hiff _).2 (isApproxTangentPlane_approxTangentPlane h2)))
  · have h2 : ¬ ∃! P : Submodule ℝ V, IsApproxTangentPlane k E₂ P x := by
      simpa only [← hiff] using h1
    rw [approxTangentPlane_of_not_existsUnique h1, approxTangentPlane_of_not_existsUnique h2]

/-- Modifying `E` by a `μHE[k]`-null set preserves `IsApproxTangentPlane` at **every** point `x`,
with no measurability or local finiteness assumption. -/
theorem isApproxTangentPlane_congr_ae {k : ℕ} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂)
    (P : Submodule ℝ V) (x : V) :
    IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_union_null (ae_eq_set.1 h).1 (ae_eq_set.1 h).2
  refine isApproxTangentPlane_congr_of_tendsto_symmDiff_div (tendsto_const_nhds.congr fun r => ?_)
  rw [measure_mono_null inter_subset_left hnull, ENNReal.zero_div]

/-- Modifying `E` by a `μHE[k]`-null set preserves `approxTangentPlane` at **every** point `x`. -/
theorem approxTangentPlane_congr_ae {k : ℕ} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_union_null (ae_eq_set.1 h).1 (ae_eq_set.1 h).2
  refine approxTangentPlane_congr_of_tendsto_symmDiff_div (tendsto_const_nhds.congr fun r => ?_)
  rw [measure_mono_null inter_subset_left hnull, ENNReal.zero_div]

omit [NormedSpace ℝ V] in
private lemma tendsto_symmDiff_div_of_eventuallyEq_nhds {k : ℕ} {E₁ E₂ : Set V} {x : V}
    (h : E₁ =ᶠ[𝓝 x] E₂) :
    Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨U, hU, hUU⟩ := eventually_iff_exists_mem.1 h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hempty : (E₁ ∆ E₂) ∩ closedBall x r = ∅ := by
    refine eq_empty_of_forall_notMem fun z ⟨hz, hzr⟩ => ?_
    have hzU : z ∈ U := hball (mem_ball.2 ((mem_closedBall.1 hzr).trans_lt hr))
    have heq : z ∈ E₁ ↔ z ∈ E₂ := hUU z hzU
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (heq.1 h1)
    · exact h2 (heq.2 h1)
  rw [hempty, measure_empty, ENNReal.zero_div]

/-- Approximate tangency at `x` is local: if `E₁` and `E₂` agree on a neighborhood of `x`, they
have the same approximate tangent planes at `x`. -/
theorem isApproxTangentPlane_congr_nhds {k : ℕ} {E₁ E₂ : Set V} {P : Submodule ℝ V} {x : V}
    (h : E₁ =ᶠ[𝓝 x] E₂) :
    IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x :=
  isApproxTangentPlane_congr_of_tendsto_symmDiff_div (tendsto_symmDiff_div_of_eventuallyEq_nhds h)

/-- `approxTangentPlane k E x` depends only on the germ of `E` at `x`. -/
theorem approxTangentPlane_congr_nhds {k : ℕ} {E₁ E₂ : Set V} {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x :=
  approxTangentPlane_congr_of_tendsto_symmDiff_div (tendsto_symmDiff_div_of_eventuallyEq_nhds h)

end Normed

end TauCeti

namespace LinearIsometryEquiv

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W]

/-- Linear isometric equivalences transport approximate tangent planes. -/
theorem isApproxTangentPlane_image_iff (e : V ≃ₗᵢ[ℝ] W) {k : ℕ} {E : Set V} {P : Submodule ℝ V}
    {x : V} :
    TauCeti.IsApproxTangentPlane k (e '' E) (P.map e.toLinearMap) (e x) ↔
      TauCeti.IsApproxTangentPlane k E P x := by
  have hinter (r : ℝ) : e '' E ∩ closedBall (e x) r = e '' (E ∩ closedBall x r) := by
    ext w
    constructor
    · rintro ⟨⟨z, hzE, rfl⟩, hwr⟩
      exact ⟨z, ⟨hzE, by simpa only [mem_closedBall, e.dist_map] using hwr⟩, rfl⟩
    · rintro ⟨z, ⟨hzE, hzr⟩, rfl⟩
      exact ⟨mem_image_of_mem e hzE, by simpa only [mem_closedBall, e.dist_map] using hzr⟩
  have hinf (z : V) :
      infDist (e z - e x) (P.map e.toLinearMap : Set W) = infDist (z - x) (P : Set V) := by
    rw [← map_sub, Submodule.map_coe]
    exact infDist_image e.isometry
  have hcone_set (ε r : ℝ) :
      {w ∈ e '' E ∩ closedBall (e x) r |
        ε * dist w (e x) < infDist (w - e x) (P.map e.toLinearMap : Set W)} =
      e '' {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} := by
    ext w
    constructor
    · rintro ⟨⟨⟨z, hzE, rfl⟩, hwr⟩, hw⟩
      refine ⟨z, ⟨⟨hzE, by simpa only [mem_closedBall, e.dist_map] using hwr⟩, ?_⟩, rfl⟩
      simpa only [e.dist_map, hinf] using hw
    · rintro ⟨z, ⟨⟨hzE, hzr⟩, hz⟩, rfl⟩
      refine ⟨⟨mem_image_of_mem e hzE, by simpa only [mem_closedBall, e.dist_map] using hzr⟩, ?_⟩
      simpa only [e.dist_map, hinf] using hz
  rw [TauCeti.isApproxTangentPlane_iff, TauCeti.isApproxTangentPlane_iff]
  have hfd : FiniteDimensional ℝ (P.map e.toLinearMap) ↔ FiniteDimensional ℝ P :=
    ⟨fun _ => (e.toLinearEquiv.submoduleMap P).symm.finiteDimensional,
      fun _ => Module.Finite.map P e.toLinearMap⟩
  have hfr : Module.finrank ℝ (P.map e.toLinearMap) = Module.finrank ℝ P :=
    (e.toLinearEquiv.submoduleMap P).finrank_eq.symm
  simp_rw [hcone_set]
  simp only [hfd, hfr, hinter, e.isometry.euclideanHausdorffMeasure_image]

/-- Linear isometric equivalences commute with `approxTangentPlane`. -/
theorem approxTangentPlane_image (e : V ≃ₗᵢ[ℝ] W) (k : ℕ) (E : Set V) (x : V) :
    TauCeti.approxTangentPlane k (e '' E) (e x) =
      (TauCeti.approxTangentPlane k E x).map e.toLinearMap := by
  have hmap_symm (Q : Submodule ℝ W) : (Q.map e.symm.toLinearMap).map e.toLinearMap = Q := by
    ext w; simp
  have hsymm_map (P : Submodule ℝ V) : (P.map e.toLinearMap).map e.symm.toLinearMap = P := by
    ext v; simp
  by_cases h : ∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane k E P x
  · have himg : ∃! Q : Submodule ℝ W, TauCeti.IsApproxTangentPlane k (e '' E) Q (e x) := by
      obtain ⟨P, hP, huniq⟩ := h
      refine ⟨P.map e.toLinearMap, (e.isApproxTangentPlane_image_iff).2 hP, fun Q hQ => ?_⟩
      have hQ' : TauCeti.IsApproxTangentPlane k E (Q.map e.symm.toLinearMap) x :=
        (e.isApproxTangentPlane_image_iff).1 ((hmap_symm Q).symm ▸ hQ)
      rw [← huniq _ hQ', hmap_symm]
    exact TauCeti.approxTangentPlane_eq_of_existsUnique himg
      ((e.isApproxTangentPlane_image_iff).2 (TauCeti.isApproxTangentPlane_approxTangentPlane h))
  · have himg : ¬ ∃! Q : Submodule ℝ W, TauCeti.IsApproxTangentPlane k (e '' E) Q (e x) := by
      rintro ⟨Q, hQ, huniq⟩
      refine h ⟨Q.map e.symm.toLinearMap,
        (e.isApproxTangentPlane_image_iff).1 ((hmap_symm Q).symm ▸ hQ), fun P hP => ?_⟩
      rw [← huniq _ ((e.isApproxTangentPlane_image_iff).2 hP), hsymm_map]
    rw [TauCeti.approxTangentPlane_of_not_existsUnique h,
      TauCeti.approxTangentPlane_of_not_existsUnique himg, Submodule.map_bot]

end LinearIsometryEquiv

namespace HasFDerivWithinAt

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {E : Set V} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

/-- **Deterministic uniqueness along a parametrization.** At a Lebesgue density-one point `x₀ ∈ s`
of an inverse-Lipschitz differentiable map `f` with `f '' s ⊆ E`, every approximate tangent
`(finrank ℝ U)`-plane to `E` at `f x₀` must equal `range A`. -/
theorem eq_range_of_isApproxTangentPlane
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {P : Submodule ℝ V}
    (hP : TauCeti.IsApproxTangentPlane (finrank ℝ U) E P (f x₀)) :
    P = LinearMap.range A.toLinearMap := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hle : LinearMap.range A.toLinearMap ≤ P :=
    hf.range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div hi hs hfs hP.isClosed
      hP.tendsto_outside_cone_div
  have := hP.finiteDimensional
  exact (Submodule.eq_of_le_of_finrank_eq hle
    ((LinearMap.finrank_range_of_inj hinj).trans hP.finrank_eq.symm)).symm

/-- At a Lebesgue density-one point `x₀ ∈ s` of an inverse-Lipschitz differentiable map `f`, the
derivative range `range A` is an approximate tangent `(finrank ℝ U)`-plane to `f '' s` at `f x₀`. -/
theorem isApproxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    TauCeti.IsApproxTangentPlane (finrank ℝ U) (f '' s) (LinearMap.range A.toLinearMap) (f x₀) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  refine ⟨Module.Finite.range A.toLinearMap, LinearMap.finrank_range_of_inj hinj,
    hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hs Subset.rfl, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hcone⟩ := hf.exists_pos_forall_infDist_range_le hx₀ hi hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hempty : {z ∈ f '' s ∩ closedBall (f x₀) r |
      ε * dist z (f x₀) < infDist (z - f x₀) (LinearMap.range A.toLinearMap : Set V)} = ∅ := by
    refine eq_empty_of_forall_notMem fun z ⟨⟨hzs, hzr⟩, hz⟩ => ?_
    exact (not_lt_of_ge (hcone z hzs ((mem_closedBall.1 hzr).trans_lt hr))) hz
  rw [hempty, measure_empty, ENNReal.zero_div]

/-- At a Lebesgue density-one point `x₀ ∈ s` of an inverse-Lipschitz differentiable map `f` with
`f '' s ⊆ E`, if `E \ f '' s` has `(finrank ℝ U)`-dimensional Hausdorff density zero at `f x₀`,
then `range A` is the **unique** approximate tangent `(finrank ℝ U)`-plane to `E` at `f x₀`. -/
theorem existsUnique_isApproxTangentPlane_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    ∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane (finrank ℝ U) E P (f x₀) := by
  have hsym : Tendsto (fun r =>
      μHE[finrank ℝ U] (((f '' s) ∆ E) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0) := by
    have heq : (f '' s) ∆ E = E \ f '' s := by
      rw [symmDiff_def, sdiff_eq_empty.2 hfs, empty_union]
    simpa only [heq] using hdiff
  refine ⟨LinearMap.range A.toLinearMap,
    (TauCeti.isApproxTangentPlane_congr_of_tendsto_symmDiff_div hsym).1
      (hf.isApproxTangentPlane_image hx₀ hi hs),
    fun P hP => hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs hP⟩

/-- Under the hypotheses of `existsUnique_isApproxTangentPlane_of_tendsto_diff`, the canonical
approximate tangent plane `approxTangentPlane (finrank ℝ U) E (f x₀)` equals `range A`. -/
theorem approxTangentPlane_eq_range_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀) = LinearMap.range A.toLinearMap :=
  hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs
    (TauCeti.isApproxTangentPlane_approxTangentPlane
      (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff))

/-- On the patch `f '' s` itself, `range A` is the unique approximate tangent `(finrank ℝ U)`-plane
at `f x₀`. -/
theorem existsUnique_isApproxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    ∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane (finrank ℝ U) (f '' s) P (f x₀) :=
  hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs Subset.rfl (by
    simp only [sdiff_self, empty_inter, measure_empty, ENNReal.zero_div, tendsto_const_nhds])

/-- On the patch `f '' s` itself, `approxTangentPlane (finrank ℝ U) (f '' s) (f x₀)` equals
`range A`. -/
theorem approxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    TauCeti.approxTangentPlane (finrank ℝ U) (f '' s) (f x₀) = LinearMap.range A.toLinearMap :=
  hf.approxTangentPlane_eq_range_of_tendsto_diff hx₀ hi hs Subset.rfl (by
    simp only [sdiff_self, empty_inter, measure_empty, ENNReal.zero_div, tendsto_const_nhds])

end HasFDerivWithinAt

/-- **Chart identification of approximate tangent planes.** Let `f : U → V` be globally Lipschitz
between finite-dimensional real inner product spaces and `L`-antilipschitz on a Borel set `s` with
`f '' s ⊆ E`, where `E` is `μHE[finrank ℝ U]`-null-measurable with locally finite restricted
measure. Then at `μHE[finrank ℝ U]`-almost every `y ∈ f '' s`, `f` is differentiable with injective
derivative at the unique parameter `x ∈ s` with `f x = y`, `E` has a unique approximate tangent
plane at `y`, and `approxTangentPlane (finrank ℝ U) E y = (fderiv ℝ f x).range`. -/
theorem LipschitzWith.ae_existsUnique_isApproxTangentPlane_image
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {E : Set V} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hs : MeasurableSet s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hfs : f '' s ⊆ E) (hEm : NullMeasurableSet E μHE[finrank ℝ U])
    [IsLocallyFiniteMeasure (μHE[finrank ℝ U].restrict E)] :
    ∀ᵐ y ∂μHE[finrank ℝ U], y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ DifferentiableAt ℝ f x ∧ Injective (fderiv ℝ f x) ∧
        (∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane (finrank ℝ U) E P y) ∧
        TauCeti.approxTangentPlane (finrank ℝ U) E y = (fderiv ℝ f x).range := by
  set k := finrank ℝ U
  -- Parameter-space bad set: points of `s` failing differentiability of `f` or density one of `s`.
  have hparam : ∀ᵐ x ∂(volume : Measure U), x ∈ s → DifferentiableAt ℝ f x ∧
      Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
        (𝓝[>] 0) (𝓝 1) := by
    filter_upwards [hf.ae_differentiableAt,
      (ae_restrict_iff' hs).1 (Besicovitch.ae_tendsto_measure_inter_div volume s)]
      with x hdiff hdens hxs
    exact ⟨hdiff, hdens hxs⟩
  set N : Set U := {x ∈ s | ¬ (DifferentiableAt ℝ f x ∧
    Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1))}
  have hN_vol : volume N = 0 := by
    rw [ae_iff] at hparam
    refine measure_mono_null (fun x hx => ?_) hparam
    exact fun h => hx.2 (h hx.1)
  have hN_img : μHE[k] (f '' N) = 0 := by
    have hN_haus : μHE[k] N = 0 := by
      rwa [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    refine nonpos_iff_eq_zero.1 ?_
    exact (hf.lipschitzOnWith.euclideanHausdorffMeasure_image_le k).trans_eq
      (by rw [hN_haus, mul_zero])
  -- Target-space bad set: points of `f '' s` where `E \ f '' s` does not have density zero.
  have hf_meas : MeasurableSet (f '' s) :=
    hs.image_of_continuousOn_injOn hf.continuous.continuousOn (injOn_iff_injective.2 hi.injective)
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ f '' s)) := by
    rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict hf_meas.compl]
    infer_instance
  have hdiff_zero :=
    TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure k
      (hEm.diff hf_meas.nullMeasurableSet)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN_img, hdiff_zero] with y hyN hzero hyfs
  obtain ⟨x, hxs, rfl⟩ := hyfs
  have hx_good : DifferentiableAt ℝ f x ∧
      Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
    by_contra hx_bad
    exact hyN ⟨x, ⟨hxs, hx_bad⟩, rfl⟩
  have hfdw := hx_good.1.hasFDerivAt.hasFDerivWithinAt (s := s)
  have hz : Tendsto (fun r =>
      μHE[k] ((E \ f '' s) ∩ closedBall (f x) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
    hzero fun h => h.2 (mem_image_of_mem f hxs)
  refine ⟨x, hxs, rfl, hx_good.1,
    hfdw.injective_of_tendsto_inter_closedBall_div volume hxs hi hx_good.2,
    hfdw.existsUnique_isApproxTangentPlane_of_tendsto_diff hxs hi hx_good.2 hfs hz,
    hfdw.approxTangentPlane_eq_range_of_tendsto_diff hxs hi hx_good.2 hfs hz⟩

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

/-- **Existence of approximate tangent planes.** At almost every point of a null-measurable,
countably `k`-rectifiable set with locally finite `μHE[k]` measure, there is a `k`-plane such
that the part of the set outside every cone about that plane has `k`-dimensional density
zero. The density-one theorem supplies the nonzero density required for an approximate
tangent plane. -/
theorem CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Q, _, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  filter_upwards [hQ] with x hx hxE
  obtain ⟨P, hdim, _, hP⟩ := hx hxE
  exact ⟨P, hdim, hP⟩

/-- **Existence and uniqueness of approximate tangent `k`-planes.** At `μHE[k]`-almost every point
of a null-measurable, countably `k`-rectifiable set `E` with locally finite `μHE[k]` measure,
there exists a **unique** approximate tangent `k`-plane `P : Submodule ℝ V`. -/
theorem CountablyRectifiable.ae_existsUnique_isApproxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x := by
  -- Pass to a Borel subset `E₀ ⊆ E` with `E₀ =ᵐ[μHE[k]] E` so each chart piece can be intersected
  -- with `E₀` while remaining Borel measurable.
  obtain ⟨E₀, hE₀E, hE₀m, hE₀ae⟩ := hEm.exists_measurable_subset_ae_eq
  obtain ⟨A, f, hAm, hbi, hcover⟩ := (hE.congr hE₀ae.symm).exists_bilipschitz_cover
  choose K L hLip hAnti using hbi
  let A' (n : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := A n ∩ f n ⁻¹' E₀
  have hA'm (n : ℕ) : MeasurableSet (A' n) :=
    (hAm n).inter (hE₀m.preimage (hLip n).continuous.measurable)
  have hA'anti (n : ℕ) : AntilipschitzWith (L n) ((A' n).domRestrict (f n)) :=
    fun x y => hAnti n ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
  have hA'sub (n : ℕ) : f n '' A' n ⊆ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hE₀E hx.2
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [finrank_euclideanSpace_fin] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  have hpatch (n : ℕ) : ∀ᵐ y ∂μHE[k], y ∈ f n '' A' n →
      ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P y := by
    have h := (hLip n).ae_existsUnique_isApproxTangentPlane_image (hA'm n) (hA'anti n)
      (by simpa only [finrank_euclideanSpace_fin] using hA'sub n)
      (by simpa only [finrank_euclideanSpace_fin] using hEm)
    simpa only [finrank_euclideanSpace_fin] using
      h.mono fun y hy hyfs => (hy hyfs).choose_spec.2.2.2.2.1
  have hcov : μHE[k] (E \ ⋃ n, f n '' A' n) = 0 := by
    have h1 : μHE[k] (E \ E₀) = 0 := (ae_eq_set.1 hE₀ae.symm).1
    refine measure_mono_null (fun y ⟨hyE, hyU⟩ => ?_) (measure_union_null h1 hcover)
    by_cases hyE₀ : y ∈ E₀
    · refine Or.inr ⟨hyE₀, fun hyA => hyU ?_⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 hyA
      obtain ⟨x, hx, rfl⟩ := hn
      exact mem_iUnion.2 ⟨n, x, ⟨hx, hyE₀⟩, rfl⟩
    · exact Or.inl ⟨hyE, hyE₀⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 hpatch] with x hcovx hpx hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.1 (not_not.1 fun h => hcovx ⟨hxE, h⟩)
  exact hpx n hxn

/-- At `μHE[k]`-almost every point of a null-measurable, countably `k`-rectifiable set `E` with
locally finite `μHE[k]` measure, `approxTangentPlane k E x` is an approximate tangent `k`-plane to
`E` at `x`. -/
theorem CountablyRectifiable.ae_isApproxTangentPlane_approxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → IsApproxTangentPlane k E (approxTangentPlane k E x) x := by
  filter_upwards [hE.ae_existsUnique_isApproxTangentPlane hEm] with x hx hxE
  exact isApproxTangentPlane_approxTangentPlane (hx hxE)

/-- At `μHE[k]`-almost every point of a null-measurable, countably `k`-rectifiable set `E` with
locally finite `μHE[k]` measure, `approxTangentPlane k E x` has dimension `k`. -/
theorem CountablyRectifiable.ae_finrank_approxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → Module.finrank ℝ (approxTangentPlane k E x) = k := by
  filter_upwards [hE.ae_existsUnique_isApproxTangentPlane hEm] with x hx hxE
  exact finrank_approxTangentPlane (hx hxE)

/-- **Measurability of the canonical approximate tangent projection field.** For a null-measurable,
countably `k`-rectifiable set `E` with locally finite `μHE[k]` measure, the orthogonal projection
field `x ↦ (approxTangentPlane k E x).starProjection` is `(μHE[k].restrict E)`-almost everywhere
measurable. -/
theorem CountablyRectifiable.aemeasurable_starProjection_approxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (fun x => (approxTangentPlane k E x).starProjection) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr ((ae_restrict_iff'₀ hEm).2 ?_)
  filter_upwards [hQ, hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm,
    hE.ae_existsUnique_isApproxTangentPlane hEm] with x hxQ hdens huniq hxE
  obtain ⟨P, hdim, hQP, hcone⟩ := hxQ hxE
  have hP : IsApproxTangentPlane k E P x :=
    IsApproxTangentPlane.of_tendsto_inter_closedBall_div hdim (hdens hxE) hcone
  have heq : P = approxTangentPlane k E x :=
    (approxTangentPlane_eq_of_existsUnique (huniq hxE) hP).symm
  subst heq
  exact hQP

end TauCeti
