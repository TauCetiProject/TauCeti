/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Density
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Approximate
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Uniqueness
public import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Calculus.TangentCone.Haar
import TauCeti.MeasureTheory.OuterMeasure.DensityQuotient

/-!
# Canonical approximate tangent planes and projections

A countably `k`-rectifiable set with locally finite normalized Euclidean Hausdorff measure has,
almost everywhere, a unique approximate tangent `k`-plane: a `k`-plane with positive upper
`k`-dimensional density and `TauCeti.DensityZeroOutsideCones` (`IsApproximateTangentPlane`,
Mattila 15.17). Combining existence (`Rectifiable.Tangent.Approximate`), uniqueness
(`Rectifiable.Tangent.Uniqueness`), and the density-one theorem (`Rectifiable.Density`) yields
almost-everywhere existence and uniqueness
(`CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane`) and defines the canonical plane
`approximateTangentPlane` (defaulting to `⊥` where none exists) and its orthogonal projection
`approximateTangentProjection` (defaulting to `0`), which is `μHE[k].restrict E`-a.e. measurable.

Approximate tangent planes place the basepoint in `closure E`
(`IsApproximateTangentPlane.mem_closure`) and depend on `E` only up to `k`-density-zero symmetric
differences at `x` (`IsApproximateTangentPlane.congr_of_tendsto_symmDiff_div`,
`approximateTangentPlane_congr_of_tendsto_symmDiff_div`), subsuming both `μHE[k]`-null and germ
modifications.

For inverse-Lipschitz parametrizations `f : U → V` differentiable within `s` at a Lebesgue
density-one point `x₀ ∈ s` (without assuming `f` is Lipschitz on `s` or separately assuming
`Injective A`, since `HasFDerivWithinAt.injective_of_tendsto_inter_closedBall_div_zero` deduces
injectivity automatically), any closed subspace with cone-density zero contains `range A`
(`HasFDerivWithinAt.range_le_of_densityZeroOutsideCones`), identifying `approximateTangentPlane`
on both general patches and differentiable normal graphs. The canonical plane and projection
provide the linear domain for tangential derivatives and Jacobians in
`Rectifiable.TangentialFDeriv`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangents).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Def. 15.17 and Thm. 15.19.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff
local notation "ω[" d "](" r ")" => volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)
local notation "𝓝₊" => 𝓝[>] (0 : ℝ)
local notation "cb" => Metric.closedBall

namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {x₀ : U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V}

/-- Patchwise lower bound `range A ≤ Q` on any cone-density-zero subspace `Q ≤ V`, without
requiring `f` to be Lipschitz on `s`. -/
theorem range_le_of_densityZeroOutsideCones (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hQ : DensityZeroOutsideCones (finrank ℝ U) E (f x₀) Q) :
    LinearMap.range A.toLinearMap ≤ Q :=
  hf.range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div hi hdens hsub
    Q.isClosed_of_finiteDimensional (densityZeroOutsideCones_iff.mp hQ)

/-- Patchwise uniqueness `Q = range A` when `A` is injective and `finrank ℝ Q ≤ finrank ℝ U`. -/
theorem eq_range_of_densityZeroOutsideCones (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
    (hQdim : finrank ℝ Q ≤ finrank ℝ U) (hQ : DensityZeroOutsideCones (finrank ℝ U) E (f x₀) Q) :
    Q = LinearMap.range A.toLinearMap :=
  (Submodule.eq_of_le_of_finrank_le (hf.range_le_of_densityZeroOutsideCones hi hsub hdens hQ)
    (hQdim.trans_eq (LinearMap.finrank_range_of_inj hinj).symm)).symm

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] in
/-- Zero `(dim U)`-density outside every cone around `range A` on an inverse-Lipschitz patch. -/
theorem densityZeroOutsideCones_range (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f x₀) r) /
      ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) :
    DensityZeroOutsideCones (finrank ℝ U) E (f x₀) (LinearMap.range A.toLinearMap) := by
  rw [densityZeroOutsideCones_iff]; intro ε hε
  obtain ⟨r₀, hr₀, hcone⟩ := hf.exists_pos_forall_infDist_range_le hx₀ hi hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨_, hrr₀⟩
  gcongr; rintro z ⟨⟨hzE, hzr⟩, hzcone⟩
  exact ⟨⟨hzE, fun hzs => hzcone.not_ge (hcone z hzs ((mem_closedBall.mp hzr).trans_lt hrr₀))⟩,
    hzr⟩

end HasFDerivWithinAt

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E E₁ E₂ : Set V}

/-- `P` is an approximate tangent `k`-plane to `E` at `x` (Mattila, Definition 15.17). -/
structure IsApproximateTangentPlane (k : ℕ) (E : Set V) (x : V) (P : Submodule ℝ V) : Prop where
  /-- `P` has dimension `k`. -/
  finrank_eq : finrank ℝ P = k
  /-- `E` has positive upper `k`-dimensional density at `x`. -/
  limsup_pos : 0 < limsup (fun r => μHE[k] (E ∩ cb x r) / ω[k](r)) 𝓝₊
  /-- Outside every cone around `P`, `E` has `k`-dimensional density zero at `x`. -/
  densityZeroOutsideCones : DensityZeroOutsideCones k E x P

omit [FiniteDimensional ℝ V] in
/-- The empty set has no approximate tangent plane at any point. -/
@[simp] theorem not_isApproximateTangentPlane_empty (k : ℕ) (x : V) (P : Submodule ℝ V) :
    ¬ IsApproximateTangentPlane k (∅ : Set V) x P := fun h => by
  have h0 := h.limsup_pos; simp at h0

namespace IsApproximateTangentPlane

/-- In dimension zero, any approximate tangent plane is `⊥`. -/
theorem eq_bot {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane 0 E x P) : P = ⊥ := by
  have := finrank_zero_iff.mp h.finrank_eq; exact Submodule.eq_bot_of_subsingleton

omit [FiniteDimensional ℝ V] in
/-- Any point admitting an approximate tangent plane to `E` lies in `closure E`. -/
theorem mem_closure {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane k E x P) :
    x ∈ closure E := by
  by_contra hx
  have h0 : ∀ᶠ z in 𝓝 x, z ∉ E :=
    Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hx) fun _ hz hE =>
      hz (subset_closure hE)
  exact h.limsup_pos.ne' (tendsto_measure_inter_div_of_eventually_notMem h0
    ((tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds) _).limsup_eq

omit [FiniteDimensional ℝ V] in
/-- Approximate tangency is preserved under `k`-density-zero set differences at `x`. -/
theorem of_tendsto_diff {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane k E₁ x P)
    (h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0))
    (h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    IsApproximateTangentPlane k E₂ x P where
  finrank_eq := h.finrank_eq
  limsup_pos := h.limsup_pos.trans_le <| (limsup_measure_inter_div_le_of_tendsto_diff h12).trans
    (limsup_le_limsup (Eventually.of_forall fun _ => by gcongr; exact inter_subset_right))
  densityZeroOutsideCones := densityZeroOutsideCones_iff.mpr fun ε hε =>
    tendsto_measure_sep_inter_div_of_sdiff
      (densityZeroOutsideCones_iff.mp h.densityZeroOutsideCones ε hε) h21

omit [FiniteDimensional ℝ V] in
/-- Approximate tangency depends on `E` only up to `k`-density-zero symmetric differences at `x`. -/
theorem congr_of_tendsto_symmDiff_div {x : V} {P : Submodule ℝ V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P :=
  let ⟨h12, h21⟩ := tendsto_measure_symmDiff_inter_div_iff.mp hsym
  ⟨fun h => h.of_tendsto_diff h12 h21, fun h => h.of_tendsto_diff h21 h12⟩

omit [FiniteDimensional ℝ V] in
/-- Modifying `E` by a `μHE[k]`-null set preserves approximate tangent planes at `x`. -/
theorem congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} {P : Submodule ℝ V} :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P :=
  congr_of_tendsto_symmDiff_div
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl
      (measure_symmDiff_eq_zero_iff.2 h) _ _ _)

omit [FiniteDimensional ℝ V] in
/-- Approximate tangent planes depend only on the germ of `E` at `x`. -/
theorem congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) {P : Submodule ℝ V} :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P :=
  congr_of_tendsto_symmDiff_div
    (tendsto_measure_symmDiff_inter_div_of_eventuallyEq h
      ((tendsto_closedBall_smallSets x).mono_left nhdsWithin_le_nhds) _)

end IsApproximateTangentPlane

open Classical in
/-- Canonical approximate tangent `k`-plane to `E` at `x` (`⊥` if none exists). -/
noncomputable def approximateTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V :=
  if h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P then h.choose else ⊥

/-- Orthogonal projection onto `TauCeti.approximateTangentPlane k E x`. -/
noncomputable def approximateTangentProjection (k : ℕ) (E : Set V) (x : V) : V →L[ℝ] V :=
  (approximateTangentPlane k E x).starProjection

/-- Unfolding lemma for `approximateTangentProjection k E x`. -/
theorem approximateTangentProjection_eq (k : ℕ) (E : Set V) (x : V) :
    approximateTangentProjection k E x = (approximateTangentPlane k E x).starProjection := by rfl

omit [FiniteDimensional ℝ V] in
/-- Uniqueness identifies `approximateTangentPlane k E x` with `P`. -/
theorem IsApproximateTangentPlane.approximateTangentPlane_eq {x : V} {P : Submodule ℝ V}
    (hP : IsApproximateTangentPlane k E x P)
    (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentPlane k E x = P := by
  have hex : ∃ Q, IsApproximateTangentPlane k E x Q := ⟨P, hP⟩
  simp only [approximateTangentPlane, hex, ↓reduceDIte]; exact huniq _ hex.choose_spec

/-- Uniqueness identifies `approximateTangentProjection k E x` with `P.starProjection`. -/
theorem IsApproximateTangentPlane.approximateTangentProjection_eq {x : V} {P : Submodule ℝ V}
    (hP : IsApproximateTangentPlane k E x P)
    (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentProjection k E x = P.starProjection := by
  simp only [approximateTangentProjection, hP.approximateTangentPlane_eq huniq]

omit [FiniteDimensional ℝ V] in
/-- Specification of `approximateTangentPlane k E x` when a plane exists. -/
theorem isApproximateTangentPlane_approximateTangentPlane {x : V}
    (h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    IsApproximateTangentPlane k E x (approximateTangentPlane k E x) := by
  simp only [approximateTangentPlane, h, ↓reduceDIte]; exact h.choose_spec

omit [FiniteDimensional ℝ V] in
/-- When no approximate tangent `k`-plane exists at `x`, `approximateTangentPlane k E x = ⊥`. -/
@[simp] theorem approximateTangentPlane_eq_bot_of_not_exists {x : V}
    (h : ¬ ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    approximateTangentPlane k E x = ⊥ := by simp [approximateTangentPlane, h]

/-- If no approximate tangent `k`-plane exists at `x`, `approximateTangentProjection k E x = 0`. -/
@[simp] theorem approximateTangentProjection_eq_zero_of_not_exists {x : V}
    (h : ¬ ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    approximateTangentProjection k E x = 0 := by simp [approximateTangentProjection, h]

omit [FiniteDimensional ℝ V] in
/-- On the empty set, `approximateTangentPlane` takes the fallback value `⊥`. -/
theorem approximateTangentPlane_empty (k : ℕ) (x : V) :
    approximateTangentPlane k (∅ : Set V) x = ⊥ := by simp

/-- On the empty set, `approximateTangentProjection` vanishes. -/
theorem approximateTangentProjection_empty (k : ℕ) (x : V) :
    approximateTangentProjection k (∅ : Set V) x = 0 := by simp

/-- In dimension zero, `approximateTangentPlane 0 E x = ⊥`. -/
@[simp] theorem approximateTangentPlane_zero (E : Set V) (x : V) :
    approximateTangentPlane 0 E x = ⊥ := by
  by_cases h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane 0 E x P
  exacts [(isApproximateTangentPlane_approximateTangentPlane h).eq_bot, by simp [h]]

/-- In dimension zero, `approximateTangentProjection 0 E x = 0`. -/
@[simp] theorem approximateTangentProjection_zero (E : Set V) (x : V) :
    approximateTangentProjection 0 E x = 0 := by simp [approximateTangentProjection]

omit [FiniteDimensional ℝ V] in
private lemma approximateTangentPlane_eq_of_iff {x : V}
    (hiff : ∀ P, IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x := by
  unfold approximateTangentPlane
  rw [funext fun P => propext (hiff P)]

omit [FiniteDimensional ℝ V] in
/-- Symmetric-difference `k`-density-zero invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_of_tendsto_symmDiff_div {x : V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  approximateTangentPlane_eq_of_iff fun _ =>
    IsApproximateTangentPlane.congr_of_tendsto_symmDiff_div hsym

/-- Symmetric-difference `k`-density-zero invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_of_tendsto_symmDiff_div {x : V}
    (hsym : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ cb x r) / ω[k](r)) 𝓝₊ (𝓝 0)) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection,
    approximateTangentPlane_congr_of_tendsto_symmDiff_div hsym]

omit [FiniteDimensional ℝ V] in
/-- Null-set invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  approximateTangentPlane_eq_of_iff fun _ => IsApproximateTangentPlane.congr_ae h

/-- Null-set invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_ae h]

omit [FiniteDimensional ℝ V] in
/-- Germ invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  approximateTangentPlane_eq_of_iff fun _ => IsApproximateTangentPlane.congr_nhds h

/-- Germ invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_nhds h]

section Rectifiable
variable (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
  [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hE hEm

/-- Almost-everywhere existence and uniqueness of approximate tangent `k`-planes. -/
theorem CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P := by
  filter_upwards [hE.ae_exists_submodule_densityZeroOutsideCones hEm,
    hE.ae_eq_of_densityZeroOutsideCones hEm,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm] with x hex huniq hdens hxE
  obtain ⟨P, hPdim, hPcone⟩ := hex hxE
  exact ⟨P, ⟨hPdim, by rw [(hdens hxE).limsup_eq]; exact zero_lt_one, hPcone⟩,
    fun Q hQ => huniq hxE Q P hQ.finrank_eq hPdim hQ.densityZeroOutsideCones hPcone⟩

/-- Almost everywhere on `E`, `approximateTangentPlane k E x` is an approximate tangent plane. -/
theorem CountablyRectifiable.ae_isApproximateTangentPlane_approximateTangentPlane :
    ∀ᵐ x ∂μHE[k], x ∈ E → IsApproximateTangentPlane k E x (approximateTangentPlane k E x) :=
  (hE.ae_existsUnique_isApproximateTangentPlane hEm).mono fun _ hx hxE =>
    isApproximateTangentPlane_approximateTangentPlane (hx hxE).exists

/-- `μHE[k].restrict E`-a.e. measurability of `approximateTangentProjection k E`. -/
theorem CountablyRectifiable.aemeasurable_approximateTangentProjection :
    AEMeasurable (approximateTangentProjection k E) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr <| (ae_restrict_iff'₀ hEm).mpr ?_
  filter_upwards [hQ, hE.ae_existsUnique_isApproximateTangentPlane hEm] with x hxQ huniq hxE
  obtain ⟨P, hPdim, hQP, hPcone⟩ := hxQ hxE; obtain ⟨P₀, hP₀, hP₀uniq⟩ := huniq hxE
  rw [hP₀.approximateTangentProjection_eq hP₀uniq,
    ← hP₀uniq P ⟨hPdim, hP₀.limsup_pos, hPcone⟩, hQP]

end Rectifiable
end TauCeti

namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {x₀ : U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V}
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
include hf hi hx₀

section WithSub
variable (hsub : f '' s ⊆ E)
  (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
  (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f x₀) r) /
    ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hsub hdens hdiff

/-- Characterization `IsApproximateTangentPlane (dim U) E (f x₀) Q ↔ Q = range A` on a patch,
without separately assuming `Injective A`. -/
theorem isApproximateTangentPlane_iff :
    IsApproximateTangentPlane (finrank ℝ U) E (f x₀) Q ↔ Q = LinearMap.range A.toLinearMap := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div_zero volume hx₀ hi hdens
  exact ⟨fun hQ => hf.eq_range_of_densityZeroOutsideCones hinj hi hsub hdens hQ.finrank_eq.le
      hQ.densityZeroOutsideCones,
    fun h => h ▸ ⟨LinearMap.finrank_range_of_inj hinj,
      hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hsub hdens,
      hf.densityZeroOutsideCones_range hi hx₀ hdiff⟩⟩

/-- Formula `approximateTangentPlane (dim U) E (f x₀) = range A` on an inverse-Lipschitz patch. -/
theorem approximateTangentPlane_eq_range :
    approximateTangentPlane (finrank ℝ U) E (f x₀) = LinearMap.range A.toLinearMap := by
  have hiff := fun Q => hf.isApproximateTangentPlane_iff hi hx₀ hsub hdens hdiff (Q := Q)
  exact ((hiff _).mpr rfl).approximateTangentPlane_eq fun Q hQ => (hiff Q).mp hQ

end WithSub

section ImageOnly
variable (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
include hdens

/-- Characterization of approximate tangent planes to `f '' s` at `f x₀`. -/
theorem isApproximateTangentPlane_image_iff :
    IsApproximateTangentPlane (finrank ℝ U) (f '' s) (f x₀) Q ↔
      Q = LinearMap.range A.toLinearMap :=
  hf.isApproximateTangentPlane_iff hi hx₀ Subset.rfl hdens (by simp)

/-- Formula `approximateTangentPlane (dim U) (f '' s) (f x₀) = range A`. -/
theorem approximateTangentPlane_image_eq_range :
    approximateTangentPlane (finrank ℝ U) (f '' s) (f x₀) = LinearMap.range A.toLinearMap :=
  hf.approximateTangentPlane_eq_range hi hx₀ Subset.rfl hdens (by simp)

end ImageOnly
end HasFDerivWithinAt
