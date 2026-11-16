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
import TauCeti.Analysis.Calculus.TangentCone.Haar
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Existence, uniqueness, and measurability of approximate tangent planes

An **approximate tangent `k`-plane** to `E ⊆ V` at `x` is a finite-dimensional `k`-plane
`P : Submodule ℝ V` such that `E` has positive upper `k`-dimensional Hausdorff density at `x` and
`k`-dimensional density zero outside every cone around `P` (`TauCeti.IsApproxTangentPlane`,
`TauCeti.approxTangentPlane`). Approximate tangent planes ignore `k`-density-zero subsets
(`TauCeti.isApproxTangentPlane_congr_of_tendsto_symmDiff_div`) and `μHE[k]`-null modifications
(`TauCeti.approxTangentPlane_congr_ae`), are forced to equal `range A` along antilipschitz
differentiable charts (`HasFDerivWithinAt.eq_range_of_isApproxTangentPlane`), and exist uniquely
`μHE[k]`-a.e. with `(μHE[k].restrict E)`-measurable `starProjection` on countably `k`-rectifiable
sets (`TauCeti.CountablyRectifiable.ae_existsUnique_isApproxTangentPlane`,
`TauCeti.CountablyRectifiable.aemeasurable_starProjection_approxTangentPlane`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (Theorem 11.6).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 15.19.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal symmDiff Topology

namespace TauCeti

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- `IsApproxTangentPlane k E P x` states that `P : Submodule ℝ V` is a `k`-dimensional subspace
such that `E` has positive upper `k`-dimensional Hausdorff density at `x` and `k`-density zero
outside every cone around `P` at `x`. -/
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
    IsApproxTangentPlane k E P x := ⟨inferInstance, hdim, hpos, hcone⟩

/-- Construct `IsApproxTangentPlane` at a point where `E` has `k`-dimensional density one. -/
theorem of_tendsto_inter_closedBall_div {k : ℕ} {E : Set V} {P : Submodule ℝ V}
    [FiniteDimensional ℝ P] {x : V} (hdim : Module.finrank ℝ P = k)
    (hdens : Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproxTangentPlane k E P x :=
  of_finrank_eq hdim (by rw [hdens.limsup_eq]; exact zero_lt_one) hcone

/-- Every approximate tangent plane is a closed subspace of the ambient normed space. -/
theorem isClosed {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E P x) : IsClosed (P : Set V) :=
  have := h.finiteDimensional; P.isClosed_of_finiteDimensional

/-- Any point admitting an approximate tangent plane to `E` lies in `closure E`. -/
theorem mem_closure {k : ℕ} {E : Set V} {P : Submodule ℝ V} {x : V}
    (h : IsApproxTangentPlane k E P x) : x ∈ closure E := by
  by_contra hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
  refine h.limsup_pos.ne' (Tendsto.limsup_eq (tendsto_const_nhds.congr' ?_))
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hemp : E ∩ closedBall x r = ∅ := eq_empty_of_forall_notMem fun z ⟨hzE, hzr⟩ =>
    hball (mem_ball.2 ((mem_closedBall.1 hzr).trans_lt hr)) (subset_closure hzE)
  simp [hemp]

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
  tendsto_outside_cone_div ε hε := by
    classical
    exact tendsto_measure_div_of_subset_union (h.tendsto_outside_cone_div ε hε) h21
      fun _ z ⟨⟨hzE₂, hzr⟩, hzc⟩ =>
        if hzE₁ : z ∈ E₁ then Or.inl ⟨⟨hzE₁, hzr⟩, hzc⟩ else Or.inr ⟨⟨hzE₂, hzE₁⟩, hzr⟩

end IsApproxTangentPlane

/-- The empty set has no approximate tangent plane at any point. -/
@[simp]
theorem not_isApproxTangentPlane_empty (k : ℕ) (P : Submodule ℝ V) (x : V) :
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

@[simp]
theorem approxTangentPlane_empty (k : ℕ) (x : V) : approxTangentPlane k (∅ : Set V) x = ⊥ :=
  approxTangentPlane_of_not_existsUnique fun ⟨P, hP, _⟩ => not_isApproxTangentPlane_empty k P x hP

@[simp]
theorem approxTangentPlane_zero (E : Set V) (x : V) : approxTangentPlane 0 E x = ⊥ := by
  by_cases h : ∃! P : Submodule ℝ V, IsApproxTangentPlane 0 E P x
  · exact (isApproxTangentPlane_approxTangentPlane h).eq_bot_of_zero
  · exact approxTangentPlane_of_not_existsUnique h

/-- If `E₁` and `E₂` admit the same approximate tangent `k`-planes at `x`, their canonical
`approxTangentPlane` agrees at `x`. -/
theorem approxTangentPlane_congr_of_iff {k : ℕ} {E₁ E₂ : Set V} {x : V}
    (h : ∀ P, IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x := by
  have hex : (∃! P, IsApproxTangentPlane k E₁ P x) ↔ ∃! P, IsApproxTangentPlane k E₂ P x :=
    existsUnique_congr h
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
    (P : Submodule ℝ V) (x : V) :
    IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_union_null (ae_eq_set.1 h).1 (ae_eq_set.1 h).2
  exact isApproxTangentPlane_congr_of_tendsto_symmDiff_div
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl hnull _ _ _)

/-- Modifying `E` by a `μHE[k]`-null set preserves `approxTangentPlane` at **every** point `x`. -/
theorem approxTangentPlane_congr_ae {k : ℕ} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x :=
  approxTangentPlane_congr_of_iff fun P => isApproxTangentPlane_congr_ae h P x

omit [NormedSpace ℝ V] in
private lemma tendsto_symmDiff_div_of_eventuallyEq_nhds {k : ℕ} {E₁ E₂ : Set V} {x : V}
    (h : E₁ =ᶠ[𝓝 x] E₂) :
    Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨U, hU, hUU⟩ := eventually_iff_exists_mem.1 h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hemp : (E₁ ∆ E₂) ∩ closedBall x r = ∅ := eq_empty_of_forall_notMem fun z ⟨hz, hzr⟩ => by
    have heq : z ∈ E₁ ↔ z ∈ E₂ := hUU z (hball (mem_ball.2 ((mem_closedBall.1 hzr).trans_lt hr)))
    exact hz.elim (fun ⟨h1, h2⟩ => h2 (heq.1 h1)) (fun ⟨h1, h2⟩ => h2 (heq.2 h1))
  simp [hemp]

/-- Approximate tangency at `x` is local: if `E₁ =ᶠ[𝓝 x] E₂`, they share approximate tangents. -/
theorem isApproxTangentPlane_congr_nhds {k : ℕ} {E₁ E₂ : Set V} {P : Submodule ℝ V} {x : V}
    (h : E₁ =ᶠ[𝓝 x] E₂) : IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x :=
  isApproxTangentPlane_congr_of_tendsto_symmDiff_div (tendsto_symmDiff_div_of_eventuallyEq_nhds h)

/-- `approxTangentPlane k E x` depends only on the germ of `E` at `x`. -/
theorem approxTangentPlane_congr_nhds {k : ℕ} {E₁ E₂ : Set V} {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approxTangentPlane k E₁ x = approxTangentPlane k E₂ x :=
  approxTangentPlane_congr_of_iff fun _ => isApproxTangentPlane_congr_nhds h

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
    ext y; constructor
    · rintro ⟨⟨z, hz, rfl⟩, hr⟩; exact ⟨z, ⟨hz, by simpa [mem_closedBall] using hr⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hr⟩, rfl⟩; exact ⟨mem_image_of_mem e hz, by simpa [mem_closedBall] using hr⟩
  have hinf (z : V) : infDist (e z - e x) (P.map e.toLinearMap : Set W) = infDist (z - x) P := by
    rw [← map_sub, Submodule.map_coe]; exact infDist_image e.isometry
  have hcone_set (ε r : ℝ) :
      {w ∈ e '' E ∩ closedBall (e x) r |
        ε * dist w (e x) < infDist (w - e x) (P.map e.toLinearMap : Set W)} =
      e '' {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} := by
    ext y; simp only [hinter, mem_sep_iff, mem_image]; constructor
    · rintro ⟨⟨z, hz, rfl⟩, hw⟩; exact ⟨z, ⟨hz, by simpa only [e.dist_map, hinf] using hw⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hz'⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, by simpa only [e.dist_map, hinf] using hz'⟩
  rw [TauCeti.isApproxTangentPlane_iff, TauCeti.isApproxTangentPlane_iff]
  have hfd : FiniteDimensional ℝ (P.map e.toLinearMap) ↔ FiniteDimensional ℝ P :=
    ⟨fun _ => (e.toLinearEquiv.submoduleMap P).symm.finiteDimensional,
      fun _ => Module.Finite.map P e.toLinearMap⟩
  simp_rw [hcone_set]
  simp only [hfd, (e.toLinearEquiv.submoduleMap P).finrank_eq.symm, hinter,
    e.isometry.euclideanHausdorffMeasure_image]

/-- Linear isometric equivalences commute with `approxTangentPlane`. -/
theorem approxTangentPlane_image (e : V ≃ₗᵢ[ℝ] W) (k : ℕ) (E : Set V) (x : V) :
    TauCeti.approxTangentPlane k (e '' E) (e x) =
      (TauCeti.approxTangentPlane k E x).map e.toLinearMap := by
  have hms (Q : Submodule ℝ W) : (Q.map e.symm.toLinearMap).map e.toLinearMap = Q := by ext; simp
  have hsm (P : Submodule ℝ V) : (P.map e.toLinearMap).map e.symm.toLinearMap = P := by ext; simp
  by_cases h : ∃! P : Submodule ℝ V, TauCeti.IsApproxTangentPlane k E P x
  · obtain ⟨P, hP, huniq⟩ := h
    have himg : ∃! Q : Submodule ℝ W, TauCeti.IsApproxTangentPlane k (e '' E) Q (e x) :=
      ⟨P.map e.toLinearMap, e.isApproxTangentPlane_image_iff.2 hP, fun Q hQ => by
        rw [← huniq _ (e.isApproxTangentPlane_image_iff.1 (by rwa [hms Q])), hms]⟩
    exact TauCeti.approxTangentPlane_eq_of_existsUnique himg (e.isApproxTangentPlane_image_iff.2
      (TauCeti.isApproxTangentPlane_approxTangentPlane ⟨P, hP, huniq⟩))
  · have himg : ¬ ∃! Q : Submodule ℝ W, TauCeti.IsApproxTangentPlane k (e '' E) Q (e x) :=
      fun ⟨Q, hQ, huniq⟩ => h ⟨Q.map e.symm.toLinearMap,
        e.isApproxTangentPlane_image_iff.1 (by rwa [hms Q]), fun P hP => by
          rw [← huniq _ (e.isApproxTangentPlane_image_iff.2 hP), hsm]⟩
    rw [TauCeti.approxTangentPlane_of_not_existsUnique h,
      TauCeti.approxTangentPlane_of_not_existsUnique himg, Submodule.map_bot]

end LinearIsometryEquiv

namespace HasFDerivWithinAt

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {E : Set V} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

/-- **Deterministic uniqueness along a parametrization**: every approximate tangent
`(finrank ℝ U)`-plane to `E` at `f x₀` equals `range A`. -/
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
      hP.tendsto_outside_cone_div)
    ((LinearMap.finrank_range_of_inj hinj).trans hP.finrank_eq.symm)).symm

/-- `range A` is an approximate tangent `(finrank ℝ U)`-plane to `f '' s` at `f x₀`. -/
theorem isApproxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    TauCeti.IsApproxTangentPlane (finrank ℝ U) (f '' s) (LinearMap.range A.toLinearMap) (f x₀) := by
  refine ⟨Module.Finite.range A.toLinearMap, LinearMap.finrank_range_of_inj
    (hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs),
    hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hs Subset.rfl, fun ε hε => ?_⟩
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
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
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
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
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
  hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs Subset.rfl
    (TauCeti.tendsto_measure_sdiff_inter_div_of_subset Subset.rfl _ _ _)

/-- On `f '' s` itself, `approxTangentPlane (finrank ℝ U) (f '' s) (f x₀) = range A`. -/
theorem approxTangentPlane_image
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) :
    TauCeti.approxTangentPlane (finrank ℝ U) (f '' s) (f x₀) = LinearMap.range A.toLinearMap :=
  hf.approxTangentPlane_eq_range_of_tendsto_diff hx₀ hi hs Subset.rfl
    (TauCeti.tendsto_measure_sdiff_inter_div_of_subset Subset.rfl _ _ _)

end HasFDerivWithinAt

/-- Pushing volume-a.e. parameter conditions on `s` forward along a bi-Lipschitz patch `f '' s`. -/
theorem LipschitzWith.ae_image_of_ae_volume
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {E : Set V} {K L : ℝ≥0} {p : U → Prop}
    (hf : LipschitzWith K f) (hs : MeasurableSet s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hEm : NullMeasurableSet E μHE[finrank ℝ U])
    [IsLocallyFiniteMeasure (μHE[finrank ℝ U].restrict E)]
    (hp : ∀ᵐ x ∂(volume : Measure U), x ∈ s → p x) :
    ∀ᵐ y ∂μHE[finrank ℝ U], y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ p x ∧ DifferentiableAt ℝ f x ∧
        Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) ∧
        Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x) r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0) := by
  set k := finrank ℝ U
  have hparam : ∀ᵐ x ∂(volume : Measure U), x ∈ s → p x ∧ DifferentiableAt ℝ f x ∧
      Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
    filter_upwards [hp, hf.ae_differentiableAt,
      (ae_restrict_iff' hs).1 (Besicovitch.ae_tendsto_measure_inter_div volume s)]
      with x hpx hdiff hdens hxs using ⟨hpx hxs, hdiff, hdens hxs⟩
  set N : Set U := {x ∈ s | ¬ (p x ∧ DifferentiableAt ℝ f x ∧
    Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1))}
  have hN_haus : μHE[k] N = 0 := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, measure_eq_zero_iff_ae_notMem]
    exact hparam.mono fun x hx hN => hN.2 (hx hN.1)
  have hN_img : μHE[k] (f '' N) = 0 := nonpos_iff_eq_zero.1 <|
    (hf.lipschitzOnWith.euclideanHausdorffMeasure_image_le k).trans_eq (by rw [hN_haus, mul_zero])
  have hf_meas : MeasurableSet (f '' s) :=
    hs.image_of_continuousOn_injOn hf.continuous.continuousOn (injOn_iff_injective.2 hi.injective)
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ f '' s)) := by
    rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict hf_meas.compl]; infer_instance
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN_img,
    TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure k
      (hEm.diff hf_meas.nullMeasurableSet)] with y hyN hzero
  rintro ⟨x, hxs, rfl⟩
  obtain ⟨hpx, hdf, hdens⟩ : p x ∧ DifferentiableAt ℝ f x ∧
      Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) :=
    by_contra fun hbad => hyN ⟨x, ⟨hxs, hbad⟩, rfl⟩
  exact ⟨x, hxs, rfl, hpx, hdf, hdens, hzero fun h => h.2 (mem_image_of_mem f hxs)⟩

/-- **Chart identification of approximate tangent planes** along a bi-Lipschitz Borel patch. -/
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
  filter_upwards [hf.ae_image_of_ae_volume hs hi hEm
    (Eventually.of_forall fun _ _ => True.intro)] with y hy hyfs
  obtain ⟨x, hxs, rfl, -, hdf, hdens, hz⟩ := hy hyfs
  have hfdw := hdf.hasFDerivAt.hasFDerivWithinAt (s := s)
  exact ⟨x, hxs, rfl, hdf, hfdw.injective_of_tendsto_inter_closedBall_div volume hxs hi hdens,
    hfdw.existsUnique_isApproxTangentPlane_of_tendsto_diff hxs hi hdens hfs hz,
    hfdw.approxTangentPlane_eq_range_of_tendsto_diff hxs hi hdens hfs hz⟩

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

/-- **Existence of approximate tangent planes** (without uniqueness) on a null-measurable,
countably `k`-rectifiable set with locally finite `μHE[k]` measure. -/
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

/-- **Existence and uniqueness of approximate tangent `k`-planes** at `μHE[k]`-a.e. `x ∈ E`. -/
theorem CountablyRectifiable.ae_existsUnique_isApproxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P x := by
  obtain ⟨A, f, hAm, hAsub, hbi, hcov⟩ := hE.exists_bilipschitz_subset_cover hEm
  choose K L hLip hAnti using hbi
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [finrank_euclideanSpace_fin] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  have hpatch (n : ℕ) : ∀ᵐ y ∂μHE[k], y ∈ f n '' A n →
      ∃! P : Submodule ℝ V, IsApproxTangentPlane k E P y := by
    have hae := (hLip n).ae_existsUnique_isApproxTangentPlane_image (hAm n) (hAnti n) (hAsub n)
      (by simpa only [finrank_euclideanSpace_fin] using hEm)
    rw [finrank_euclideanSpace_fin] at hae
    refine hae.mono fun _ hy hyfs => ?_
    obtain ⟨_, _, _, _, _, hex, -⟩ := hy hyfs
    exact hex
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 hpatch] with x hcovx hpx hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.1 (not_not.1 fun h => hcovx ⟨hxE, h⟩)
  exact hpx n hxn

/-- At `μHE[k]`-almost every `x ∈ E`, `approxTangentPlane k E x` is an approximate tangent plane. -/
theorem CountablyRectifiable.ae_isApproxTangentPlane_approxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → IsApproxTangentPlane k E (approxTangentPlane k E x) x :=
  (hE.ae_existsUnique_isApproxTangentPlane hEm).mono fun _ hx hxE =>
    isApproxTangentPlane_approxTangentPlane (hx hxE)

/-- At `μHE[k]`-almost every `x ∈ E`, `approxTangentPlane k E x` has dimension `k`. -/
theorem CountablyRectifiable.ae_finrank_approxTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → Module.finrank ℝ (approxTangentPlane k E x) = k :=
  (hE.ae_existsUnique_isApproxTangentPlane hEm).mono fun _ hx hxE =>
    finrank_approxTangentPlane (hx hxE)

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
    (IsApproxTangentPlane.of_tendsto_inter_closedBall_div hdim (hdens hxE) hcone)).symm
  subst heq; convert hQP

end TauCeti
