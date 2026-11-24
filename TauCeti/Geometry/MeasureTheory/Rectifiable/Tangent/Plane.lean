/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Approximate
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Uniqueness
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.Calculus.TangentCone.Haar
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.MeasureTheory.OuterMeasure.DensityQuotient

/-!
# Bundled approximate tangent planes and the canonical plane field

An **approximate tangent `k`-plane** to `E ⊆ V` at `x` (`TauCeti.IsApproxTangentPlane`) bundles
finite-dimensionality, `Module.finrank ℝ P = k`, positive upper `k`-dimensional Hausdorff density of
`E` at `x`, and `TauCeti.DensityZeroOutsideCones k E x P`, with canonical choice
`TauCeti.approxTangentPlane k E x` (`⊥` if not unique). Approximate tangent planes ignore
`k`-density-zero symmetric differences
(`TauCeti.isApproxTangentPlane_congr_of_tendsto_symmDiff_div`) and `μHE[k]`-null modifications
(`TauCeti.approxTangentPlane_congr_ae`), equal `range A` at Haar density-one parameter points of
inverse-Lipschitz differentiable charts (`HasFDerivWithinAt.eq_range_of_isApproxTangentPlane`), and
exist uniquely `μHE[k]`-a.e. with `(μHE[k].restrict E)`-a.e. measurable `starProjection` on
`μHE[k]`-null-measurable countably `k`-rectifiable sets with locally finite `μHE[k].restrict E`
measure (`TauCeti.CountablyRectifiable.ae_existsUnique_isApproxTangentPlane`,
`TauCeti.CountablyRectifiable.aemeasurable_starProjection_approxTangentPlane`).

## References
* L. Simon, *Lectures on Geometric Measure Theory*, §11; P. Mattila, *Geometry of Sets and
  Measures in Euclidean Spaces*, Theorem 15.19.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal symmDiff Topology

namespace TauCeti
section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- `IsApproxTangentPlane k E P x` states that `P : Submodule ℝ V` is a finite-dimensional `k`-plane
with positive upper `k`-density of `E` at `x` and `DensityZeroOutsideCones k E x P`. -/
structure IsApproxTangentPlane (k : ℕ) (E : Set V) (P : Submodule ℝ V) (x : V) : Prop where
  /-- `P` is finite-dimensional, ruling out infinite-dimensional subspaces when `k = 0`. -/
  finiteDimensional : FiniteDimensional ℝ P
  /-- `P` has dimension `k`. -/
  finrank_eq : Module.finrank ℝ P = k
  /-- `E` has strictly positive upper `k`-dimensional Hausdorff density at `x`. -/
  limsup_pos : 0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
    volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0)
  /-- Outside every cone around `P` at `x`, `E` has `k`-dimensional Hausdorff density zero. -/
  densityZeroOutsideCones : DensityZeroOutsideCones k E x P

/-- Characteristic equivalence for `IsApproxTangentPlane`. -/
theorem isApproxTangentPlane_iff {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V} :
    IsApproxTangentPlane k E P x ↔ FiniteDimensional ℝ P ∧ Module.finrank ℝ P = k ∧
      0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ∧
      DensityZeroOutsideCones k E x P :=
  ⟨fun h => ⟨h.finiteDimensional, h.finrank_eq, h.limsup_pos, h.densityZeroOutsideCones⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

namespace IsApproxTangentPlane

/-- Construct `IsApproxTangentPlane` when `FiniteDimensional ℝ P` is available as an instance. -/
theorem of_finrank_eq {k : ℕ} {E : Set V} {P : Submodule ℝ V} [FiniteDimensional ℝ P] {x : V}
    (hdim : Module.finrank ℝ P = k)
    (hpos : 0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0))
    (hcone : DensityZeroOutsideCones k E x P) : IsApproxTangentPlane k E P x :=
  ⟨inferInstance, hdim, hpos, hcone⟩

/-- Construct `IsApproxTangentPlane` at a point where `E` has `k`-dimensional density one. -/
theorem of_tendsto_inter_closedBall_div {k : ℕ} {E : Set V} {P : Submodule ℝ V}
    [FiniteDimensional ℝ P] {x : V} (hdim : Module.finrank ℝ P = k)
    (hdens : Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1))
    (hcone : DensityZeroOutsideCones k E x P) : IsApproxTangentPlane k E P x :=
  of_finrank_eq hdim (by rw [hdens.limsup_eq]; exact zero_lt_one) hcone

/-- Every approximate tangent plane is a closed subspace of the ambient normed space. -/
theorem isClosed {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E P x) : IsClosed (P : Set V) :=
  have := h.finiteDimensional; P.isClosed_of_finiteDimensional

/-- Any point admitting an approximate tangent plane to `E` lies in `closure E`. -/
theorem mem_closure {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E P x) : x ∈ closure E := by
  by_contra hx
  have h0 : ∀ᶠ z in 𝓝 x, z ∉ E := Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hx)
    fun _ hz hE => hz (subset_closure hE)
  exact h.limsup_pos.ne' (tendsto_measure_inter_div_of_eventually_notMem h0
    ((tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds) _).limsup_eq

/-- A `0`-dimensional approximate tangent plane is necessarily `⊥`. -/
theorem eq_bot_of_zero {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane 0 E P x) : P = ⊥ :=
  have := h.finiteDimensional; Submodule.finrank_eq_zero.1 h.finrank_eq

/-- Approximate tangency is preserved under `k`-density-zero set differences at `x`. -/
theorem of_tendsto_diff {k : ℕ} {E₁ E₂ : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E₁ P x)
    (h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
    (h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E₂ P x where
  finiteDimensional := h.finiteDimensional
  finrank_eq := h.finrank_eq
  limsup_pos := h.limsup_pos.trans_le <| (limsup_measure_inter_div_le_of_tendsto_diff h12).trans
    (limsup_le_limsup (Eventually.of_forall fun _ => by gcongr; exact inter_subset_right))
  densityZeroOutsideCones := densityZeroOutsideCones_iff.2 fun ε hε => by
    classical
    exact tendsto_measure_div_of_subset_union
      (densityZeroOutsideCones_iff.1 h.densityZeroOutsideCones ε hε) h21
      fun _ z ⟨⟨hzE₂, hzr⟩, hzc⟩ =>
        if hzE₁ : z ∈ E₁ then Or.inl ⟨⟨hzE₁, hzr⟩, hzc⟩ else Or.inr ⟨⟨hzE₂, hzE₁⟩, hzr⟩

end IsApproxTangentPlane

/-- The empty set has no approximate tangent plane at any point. -/
@[simp] theorem not_isApproxTangentPlane_empty (k : ℕ) (P : Submodule ℝ V) (x : V) :
    ¬ IsApproxTangentPlane k (∅ : Set V) P x := fun h => by
  have h0 := h.limsup_pos; simp at h0

/-- The canonical approximate tangent `k`-plane to `E` at `x` (`⊥` if not unique). -/
noncomputable def approxTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V :=
  open Classical in
  if h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x then h.choose else ⊥

instance instFiniteDimensionalApproxTangentPlane (k : ℕ) (E : Set V) (x : V) :
    FiniteDimensional ℝ (approxTangentPlane k E x) := by
  by_cases h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x
  · exact (by simp [approxTangentPlane, h] : approxTangentPlane k E x = h.choose) ▸
      h.choose_spec.1.finiteDimensional
  · exact (by simp [approxTangentPlane, h] : approxTangentPlane k E x = ⊥) ▸ inferInstance

/-- When `E` has a unique approximate tangent `k`-plane at `x`, `approxTangentPlane k E x`
satisfies `IsApproxTangentPlane`. -/
theorem isApproxTangentPlane_approxTangentPlane {k : ℕ} {E : Set V} {x : V}
    (h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x) :
    IsApproxTangentPlane k E (approxTangentPlane k E x) x := by
  simpa only [approxTangentPlane, h, ↓reduceDIte] using h.choose_spec.1

/-- When `E` has a unique approximate tangent `k`-plane at `x`, `approxTangentPlane` equals any
witness `P`. -/
theorem approxTangentPlane_eq_of_existsUnique {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hP : IsApproxTangentPlane k E P x) : approxTangentPlane k E x = P :=
  h.unique (isApproxTangentPlane_approxTangentPlane h) hP

/-- Outside the locus of unique existence, `approxTangentPlane` takes the junk value `⊥`. -/
theorem approxTangentPlane_of_not_existsUnique {k : ℕ} {E : Set V} {x : V}
    (h : ¬ ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x) : approxTangentPlane k E x = ⊥ := by
  simp [approxTangentPlane, h]

/-- At any point of unique existence, `approxTangentPlane k E x` has dimension `k`. -/
theorem finrank_approxTangentPlane {k : ℕ} {E : Set V} {x : V}
    (h : ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x) :
    Module.finrank ℝ (approxTangentPlane k E x) = k :=
  (isApproxTangentPlane_approxTangentPlane h).finrank_eq

@[simp] theorem approxTangentPlane_empty (k : ℕ) (x : V) : approxTangentPlane k (∅ : Set V) x = ⊥ :=
  approxTangentPlane_of_not_existsUnique fun ⟨P, hP, _⟩ => not_isApproxTangentPlane_empty k P x hP

@[simp] theorem approxTangentPlane_zero (E : Set V) (x : V) : approxTangentPlane 0 E x = ⊥ := by
  by_cases h : ∃! P : Submodule ℝ V, IsApproxTangentPlane 0 E P x
  · exact (isApproxTangentPlane_approxTangentPlane h).eq_bot_of_zero
  · exact approxTangentPlane_of_not_existsUnique h

/-- If `E₁` and `E₂` admit the same approximate tangent `k`-planes at `x`, `approxTangentPlane`
agrees at `x`. -/
theorem approxTangentPlane_congr_of_iff {k : ℕ} {E₁ E₂ : Set V} {x : V}
    (h : ∀ P, IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x := by
  have hex := existsUnique_congr h
  by_cases h₁ : ∃! P, IsApproxTangentPlane k E₁ P x
  · exact (approxTangentPlane_eq_of_existsUnique (hex.1 h₁)
      ((h _).1 (isApproxTangentPlane_approxTangentPlane h₁))).symm
  · rw [approxTangentPlane_of_not_existsUnique h₁,
      approxTangentPlane_of_not_existsUnique (mt hex.2 h₁)]

/-- Approximate tangency depends on `E` only up to `k`-density-zero symmetric differences at `x`. -/
theorem isApproxTangentPlane_congr_of_tendsto_symmDiff_div {k : ℕ} {E₁ E₂ : Set V}
    {P : Submodule ℝ V} {x : V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x := by
  have hle {A : Set V} (hA : A ⊆ E₁ ∆ E₂) :
      Tendsto (fun r => μHE[k] (A ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_measure_div_of_subset hsym fun _ => inter_subset_inter_left _ hA
  exact ⟨fun h => h.of_tendsto_diff (hle subset_union_left) (hle subset_union_right),
    fun h => h.of_tendsto_diff (hle subset_union_right) (hle subset_union_left)⟩

/-- `approxTangentPlane` depends on `E` only up to `k`-density-zero symmetric differences at `x`. -/
theorem approxTangentPlane_congr_of_tendsto_symmDiff_div {k : ℕ} {E₁ E₂ : Set V} {x : V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x :=
  approxTangentPlane_congr_of_iff fun _ => isApproxTangentPlane_congr_of_tendsto_symmDiff_div hsym

/-- Modifying `E` by a `μHE[k]`-null set preserves `IsApproxTangentPlane` at **every** point `x`. -/
theorem isApproxTangentPlane_congr_ae {k : ℕ} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂)
    (P : Submodule ℝ V) (x : V) : IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x :=
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_union_null (ae_eq_set.1 h).1 (ae_eq_set.1 h).2
  isApproxTangentPlane_congr_of_tendsto_symmDiff_div
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl hnull _ _ _)

/-- Modifying `E` by a `μHE[k]`-null set preserves `approxTangentPlane` at **every** point `x`. -/
theorem approxTangentPlane_congr_ae {k : ℕ} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x :=
  approxTangentPlane_congr_of_iff fun P => isApproxTangentPlane_congr_ae h P x

/-- Approximate tangency at `x` is local: if `E₁ =ᶠ[𝓝 x] E₂`, they share approximate tangents. -/
theorem isApproxTangentPlane_congr_nhds {k : ℕ} {E₁ E₂ : Set V} {P : Submodule ℝ V} {x : V}
    (h : E₁ =ᶠ[𝓝 x] E₂) : IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x :=
  isApproxTangentPlane_congr_of_tendsto_symmDiff_div
    (tendsto_measure_symmDiff_inter_div_of_eventuallyEq h
      ((tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds) _)

/-- `approxTangentPlane k E x` depends only on the germ of `E` at `x`. -/
theorem approxTangentPlane_congr_nhds {k : ℕ} {E₁ E₂ : Set V} {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x :=
  approxTangentPlane_congr_of_iff fun _ => isApproxTangentPlane_congr_nhds h

end Normed
end TauCeti

namespace HasFDerivWithinAt

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {E : Set V} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

/-- **Deterministic uniqueness along a parametrization**: every approximate tangent
`(finrank ℝ U)`-plane to `E` at `f x₀` equals `range A`, without requiring `f` to be Lipschitz. -/
theorem eq_range_of_isApproxTangentPlane
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {P : Submodule ℝ V}
    (hP : TauCeti.IsApproxTangentPlane (finrank ℝ U) E P (f x₀)) :
    P = LinearMap.range A.toLinearMap := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have := hP.finiteDimensional
  exact (Submodule.eq_of_le_of_finrank_eq
    (hf.range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div hi hs hfs hP.isClosed
      (TauCeti.densityZeroOutsideCones_iff.1 hP.densityZeroOutsideCones))
    ((LinearMap.finrank_range_of_inj hinj).trans hP.finrank_eq.symm)).symm

/-- `range A` is an approximate tangent `(finrank ℝ U)`-plane to `f '' s` at `f x₀`. -/
theorem isApproxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    TauCeti.IsApproxTangentPlane (finrank ℝ U) (f '' s) (LinearMap.range A.toLinearMap) (f x₀) := by
  refine ⟨Module.Finite.range A.toLinearMap, LinearMap.finrank_range_of_inj
    (hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs),
    hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hs Subset.rfl,
    TauCeti.densityZeroOutsideCones_iff.2 fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hcone⟩ := hf.exists_pos_forall_infDist_range_le hx₀ hi hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hemp : {z ∈ f '' s ∩ closedBall (f x₀) r |
      ε * dist z (f x₀) < infDist (z - f x₀) (LinearMap.range A.toLinearMap : Set V)} = ∅ :=
    eq_empty_of_forall_notMem fun z ⟨⟨hzs, hzr⟩, hz⟩ =>
      (not_lt_of_ge (hcone z hzs ((mem_closedBall.1 hzr).trans_lt hr))) hz
  rw [hemp, measure_empty, ENNReal.zero_div]

/-- If `E \ f '' s` has `(finrank ℝ U)`-density zero at `f x₀`, `range A` is the **unique**
approximate tangent `(finrank ℝ U)`-plane to `E` at `f x₀`. -/
theorem existsUnique_isApproxTangentPlane_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    ∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane (finrank ℝ U) E P (f x₀) := by
  have heq : (f '' s) ∆ E = E \ f '' s := by rw [symmDiff_def, sdiff_eq_empty.2 hfs, empty_union]
  exact ⟨LinearMap.range A.toLinearMap,
    (TauCeti.isApproxTangentPlane_congr_of_tendsto_symmDiff_div (by rwa [heq])).1
      (hf.isApproxTangentPlane_image hx₀ hi hs),
    fun _ hP => hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs hP⟩

/-- Under `existsUnique_isApproxTangentPlane_of_tendsto_diff`,
`approxTangentPlane (finrank ℝ U) E (f x₀) = range A`. -/
theorem approxTangentPlane_eq_range_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀) = LinearMap.range A.toLinearMap :=
  hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs
    (TauCeti.isApproxTangentPlane_approxTangentPlane
      (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff))

/-- On `f '' s` itself, `range A` is the unique approximate tangent `(finrank ℝ U)`-plane. -/
theorem existsUnique_isApproxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    ∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane (finrank ℝ U) (f '' s) P (f x₀) :=
  hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs Subset.rfl (by simp)

/-- On `f '' s` itself, `approxTangentPlane (finrank ℝ U) (f '' s) (f x₀) = range A`. -/
theorem approxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    TauCeti.approxTangentPlane (finrank ℝ U) (f '' s) (f x₀) = LinearMap.range A.toLinearMap :=
  hf.approxTangentPlane_eq_range_of_tendsto_diff hx₀ hi hs Subset.rfl (by simp)

end HasFDerivWithinAt

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

/-- **Existence and uniqueness of approximate tangent `k`-planes** at `μHE[k]`-a.e. `x ∈ E`. -/
theorem CountablyRectifiable.ae_existsUnique_isApproxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x := by
  filter_upwards [hE.ae_exists_submodule_densityZeroOutsideCones hEm,
    hE.ae_eq_of_densityZeroOutsideCones hEm,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm]
    with x hex huniq hone hxE
  obtain ⟨P, hPdim, hPcone⟩ := hex hxE
  exact ⟨P, .of_tendsto_inter_closedBall_div hPdim (hone hxE) hPcone,
    fun Q hQ => huniq hxE Q P hQ.finrank_eq hPdim hQ.densityZeroOutsideCones hPcone⟩

/-- **Measurability of `(approxTangentPlane k E x).starProjection`** on `μHE[k].restrict E`. -/
theorem CountablyRectifiable.aemeasurable_starProjection_approxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (fun x => (approxTangentPlane k E x).starProjection) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr ((ae_restrict_iff'₀ hEm).2 ?_)
  filter_upwards [hQ, hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm,
    hE.ae_existsUnique_isApproxTangentPlane hEm] with x hxQ hdens huniq hxE
  obtain ⟨P, hdim, hQP, hcone⟩ := hxQ hxE
  have heq : P = approxTangentPlane k E x := (approxTangentPlane_eq_of_existsUnique (huniq hxE)
    (.of_tendsto_inter_closedBall_div hdim (hdens hxE) hcone)).symm
  subst heq; exact hQP

end TauCeti
