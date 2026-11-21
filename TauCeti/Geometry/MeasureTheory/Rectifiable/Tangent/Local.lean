/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Approximate
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Uniqueness

/-!
# Approximate tangent planes in an open set

The cone-density condition of an approximate tangent plane (`TauCeti.DensityZeroOutsideCones`)
says that the part of a set `S` outside every cone about the affine subspace `x + P` has
`k`-dimensional density zero at `x`. It passes to subsets, depends only on the set near `x`, and
holds trivially for the whole space `P = ⊤`.

Existence and almost-everywhere uniqueness of approximate tangent planes
(`Tangent/Approximate.lean`, `Tangent/Uniqueness.lean`) are stated for sets of locally finite
measure in the whole space. This file localizes them to a countably rectifiable set whose
intersections with the compact subsets of an open set `Ω` have finite measure, by covering `Ω` with
countably many balls compactly contained in `Ω`
(`TauCeti.CountablyRectifiable.ae_existsUnique_densityZeroOutsideCones`). As a consequence, at
almost every common point of two such sets the planes of the two sets agree, and are planes of the
union (`TauCeti.CountablyRectifiable.ae_densityZeroOutsideCones_union`).

## Main declarations

* `TauCeti.DensityZeroOutsideCones`: the cone-density condition of an approximate tangent plane.
* `TauCeti.CountablyRectifiable.ae_existsUnique_densityZeroOutsideCones`: approximate tangent
  planes exist and are unique almost everywhere on a countably rectifiable set of locally finite
  measure in an open set.
* `TauCeti.CountablyRectifiable.ae_densityZeroOutsideCones_union`: the planes of two such sets
  agree almost everywhere where the sets meet.

## References

* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 3, §1 (approximate tangent planes).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace MeasureTheory Module
open scoped ENNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ}

/-- The **cone-density condition** of an approximate tangent plane: the part of `S` outside every
cone about the affine subspace `x + P` has `k`-dimensional density zero at `x`. Here `P` is an
arbitrary subspace, and the condition holds trivially for `P = ⊤`
(`TauCeti.densityZeroOutsideCones_top`). For a `k`-dimensional `P`, together with positive density,
which holds almost everywhere on a countably `k`-rectifiable set of locally finite measure, it says
that `P` is an approximate tangent plane of `S` at `x`. -/
def DensityZeroOutsideCones (k : ℕ) (S : Set V) (x : V) (P : Submodule ℝ V) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto (fun r ↦
    μHE[k] {z ∈ S ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

omit [FiniteDimensional ℝ V] in
/-- Unfolding the cone-density condition. -/
theorem densityZeroOutsideCones_iff {S : Set V} {x : V} {P : Submodule ℝ V} :
    DensityZeroOutsideCones k S x P ↔ ∀ ε > (0 : ℝ), Tendsto (fun r ↦
      μHE[k] {z ∈ S ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

omit [FiniteDimensional ℝ V] in
/-- Every set satisfies the cone-density condition for the whole space: no point lies outside a
cone about it. -/
theorem densityZeroOutsideCones_top (S : Set V) (x : V) :
    DensityZeroOutsideCones k S x ⊤ := fun ε hε ↦ by
  refine tendsto_const_nhds.congr fun r ↦ ?_
  have hempty : {z ∈ S ∩ closedBall x r |
      ε * dist z x < infDist (z - x) ((⊤ : Submodule ℝ V) : Set V)} = ∅ := by
    ext z
    simp only [Submodule.top_coe, infDist_zero_of_mem (mem_univ _), mem_sep_iff,
      mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun _ ↦ mul_nonneg hε.le dist_nonneg
  rw [hempty, measure_empty, ENNReal.zero_div]

omit [FiniteDimensional ℝ V] in
/-- The cone-density condition passes to subsets. -/
theorem DensityZeroOutsideCones.mono {S T : Set V} {x : V} {P : Submodule ℝ V}
    (h : DensityZeroOutsideCones k T x P) (hST : S ⊆ T) : DensityZeroOutsideCones k S x P :=
  fun ε hε ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ zero_le) fun _ ↦ ENNReal.div_le_div_right (measure_mono fun _ hz ↦ by
      exact ⟨⟨hST hz.1.1, hz.1.2⟩, hz.2⟩) _

omit [FiniteDimensional ℝ V] in
/-- The cone-density condition at `x` only depends on the set near `x`. -/
theorem densityZeroOutsideCones_inter_iff {S B : Set V} {x : V} {P : Submodule ℝ V} {δ : ℝ}
    (hδ : 0 < δ) (hB : closedBall x δ ⊆ B) :
    DensityZeroOutsideCones k (S ∩ B) x P ↔ DensityZeroOutsideCones k S x P := by
  refine forall₂_congr fun ε _ ↦ tendsto_congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  congr 3
  ext z
  simp only [mem_inter_iff, and_congr_left_iff]
  intro _ hz
  exact and_iff_left (hB (closedBall_subset_closedBall hr.le hz))

/-- **Approximate tangent planes in an open set.** Let `S` be a null-measurable, countably
`k`-rectifiable set whose intersections with the compact subsets of an open set `Ω` have finite
`μHE[k]` measure. At almost every point of `S` in `Ω` there is a unique `k`-plane outside every
cone about which `S` has density zero. -/
theorem CountablyRectifiable.ae_existsUnique_densityZeroOutsideCones {Ω S : Set V} (hΩ : IsOpen Ω)
    (hS : CountablyRectifiable k S) (hSm : NullMeasurableSet S μHE[k])
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] (S ∩ K) ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∈ Ω → x ∈ S → ∃ P : Submodule ℝ V, finrank ℝ P = k ∧
      DensityZeroOutsideCones k S x P ∧
        ∀ Q : Submodule ℝ V, finrank ℝ Q = k → DensityZeroOutsideCones k S x Q → Q = P := by
  -- Cover `Ω` by countably many balls whose closures lie in `Ω`.
  have hr (x : Ω) : ∃ r > 0, closedBall (x : V) r ⊆ Ω := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x x.property
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose r hr0 hrΩ using hr
  obtain ⟨T, hTc, hTU⟩ :=
    isOpen_iUnion_countable (fun x : Ω ↦ ball (x : V) (r x)) fun _ ↦ isOpen_ball
  -- On each closed ball the set has finite measure, where the existence and uniqueness theorems
  -- apply; inside the open ball the cone-density condition is that of `S`.
  have hpiece (c : Ω) : ∀ᵐ x ∂μHE[k], x ∈ ball (c : V) (r c) → x ∈ S →
      ∃ P : Submodule ℝ V, finrank ℝ P = k ∧ DensityZeroOutsideCones k S x P ∧
        ∀ Q : Submodule ℝ V, finrank ℝ Q = k → DensityZeroOutsideCones k S x Q → Q = P := by
    set Sc := S ∩ closedBall (c : V) (r c)
    have hfc : μHE[k] Sc ≠ ∞ := hfin _ (isCompact_closedBall _ _) (hrΩ c)
    have : IsFiniteMeasure (μHE[k].restrict Sc) := isFiniteMeasure_restrict.2 hfc
    have hSc : CountablyRectifiable k Sc := hS.mono inter_subset_left
    have hScm : NullMeasurableSet Sc μHE[k] :=
      hSm.inter isClosed_closedBall.measurableSet.nullMeasurableSet
    filter_upwards [hSc.ae_exists_submodule_tendsto_measure_outside_cone_div hScm,
      hSc.ae_eq_of_tendsto_measure_outside_cone_div hScm] with x hex huniq hxb hxS
    have hxSc : x ∈ Sc := ⟨hxS, ball_subset_closedBall hxb⟩
    have hδ : 0 < r c - dist x c := sub_pos.2 hxb
    have hiff (P : Submodule ℝ V) :
        DensityZeroOutsideCones k Sc x P ↔ DensityZeroOutsideCones k S x P :=
      densityZeroOutsideCones_inter_iff hδ (closedBall_subset_closedBall' (by linarith))
    obtain ⟨P, hP, hPc⟩ := hex hxSc
    exact ⟨P, hP, (hiff P).1 hPc, fun Q hQ hQc ↦ huniq hxSc Q P hQ hP ((hiff Q).2 hQc) hPc⟩
  have : Countable T := hTc.to_subtype
  filter_upwards [ae_all_iff.2 fun c : T ↦ hpiece c] with x hx hxΩ hxS
  have hxT : x ∈ ⋃ i ∈ T, ball (i : V) (r i) :=
    hTU ▸ mem_iUnion.2 ⟨⟨x, hxΩ⟩, mem_ball_self (hr0 _)⟩
  obtain ⟨c, hcT, hxc⟩ := mem_iUnion₂.1 hxT
  exact hx ⟨c, hcT⟩ hxc hxS

/-- At almost every point of the union of two such sets in `Ω`, the plane outside whose cones
either set has density zero is one for the union. In particular, where the two sets meet, their
planes agree. -/
theorem CountablyRectifiable.ae_densityZeroOutsideCones_union {Ω S₁ S₂ : Set V} (hΩ : IsOpen Ω)
    (hS₁ : CountablyRectifiable k S₁) (hS₁m : NullMeasurableSet S₁ μHE[k])
    (hfin₁ : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] (S₁ ∩ K) ≠ ∞)
    (hS₂ : CountablyRectifiable k S₂) (hS₂m : NullMeasurableSet S₂ μHE[k])
    (hfin₂ : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] (S₂ ∩ K) ≠ ∞)
    {P₁ P₂ : V → Submodule ℝ V} (hP₁ : ∀ x ∈ S₁, finrank ℝ (P₁ x) = k)
    (hP₂ : ∀ x ∈ S₂, finrank ℝ (P₂ x) = k)
    (hP₁c : ∀ᵐ x ∂μHE[k], x ∈ Ω → x ∈ S₁ → DensityZeroOutsideCones k S₁ x (P₁ x))
    (hP₂c : ∀ᵐ x ∂μHE[k], x ∈ Ω → x ∈ S₂ → DensityZeroOutsideCones k S₂ x (P₂ x)) :
    ∀ᵐ x ∂μHE[k], x ∈ Ω →
      (x ∈ S₁ → DensityZeroOutsideCones k (S₁ ∪ S₂) x (P₁ x)) ∧
      (x ∈ S₂ → DensityZeroOutsideCones k (S₁ ∪ S₂) x (P₂ x)) ∧
      (x ∈ S₁ → x ∈ S₂ → P₁ x = P₂ x) := by
  have hfin : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] ((S₁ ∪ S₂) ∩ K) ≠ ∞ := fun K hK hKΩ ↦ by
    rw [union_inter_distrib_right]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin₁ K hK hKΩ, hfin₂ K hK hKΩ⟩)
      (measure_union_le _ _)
  filter_upwards [(hS₁.union hS₂).ae_existsUnique_densityZeroOutsideCones hΩ (hS₁m.union hS₂m)
      hfin, hS₁.ae_existsUnique_densityZeroOutsideCones hΩ hS₁m hfin₁,
      hS₂.ae_existsUnique_densityZeroOutsideCones hΩ hS₂m hfin₂, hP₁c, hP₂c]
    with x hU h₁ h₂ hc₁ hc₂ hxΩ
  -- The plane `Q` of the union is a plane of each set, so it is the unique plane of each.
  have key (hx : x ∈ S₁ ∪ S₂) : ∃ Q : Submodule ℝ V, DensityZeroOutsideCones k (S₁ ∪ S₂) x Q ∧
      (x ∈ S₁ → P₁ x = Q) ∧ (x ∈ S₂ → P₂ x = Q) := by
    obtain ⟨Q, hQ, hQc, -⟩ := hU hxΩ hx
    refine ⟨Q, hQc, fun hx₁ ↦ ?_, fun hx₂ ↦ ?_⟩
    · obtain ⟨P, -, -, hPu⟩ := h₁ hxΩ hx₁
      exact (hPu (P₁ x) (hP₁ x hx₁) (hc₁ hxΩ hx₁)).trans
        (hPu Q hQ (hQc.mono subset_union_left)).symm
    · obtain ⟨P, -, -, hPu⟩ := h₂ hxΩ hx₂
      exact (hPu (P₂ x) (hP₂ x hx₂) (hc₂ hxΩ hx₂)).trans
        (hPu Q hQ (hQc.mono subset_union_right)).symm
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_, fun hx₁ hx₂ ↦ ?_⟩
  · obtain ⟨Q, hQc, h, -⟩ := key (Or.inl hx)
    rwa [h hx]
  · obtain ⟨Q, hQc, -, h⟩ := key (Or.inr hx)
    rwa [h hx]
  · obtain ⟨Q, -, h, h'⟩ := key (Or.inl hx₁)
    rw [h hx₁, h' hx₂]

end TauCeti
