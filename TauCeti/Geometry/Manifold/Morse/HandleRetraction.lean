/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.Analysis.Calculus.Morse.HandleRetraction.Basic
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Milnor's handle retraction in Morse charts

Passing a critical level `c` of a Morse function `f` attaches one cell at each critical point on
the level. In a normalized Morse chart `ψ` of index `λ` around such a point,

`f = c - Σ_{j < λ} yⱼ² + Σ_{j ≥ λ} yⱼ²`,

and the cell is the disc `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ λ}` of the negative coordinates. Milnor
(*Morse Theory*, Theorem 3.2) retracts the sublevel `{F ≤ c - ε}` of a function `F` lowered near
the critical points onto `{f ≤ c - ε}` with these cells attached, by a deformation which in each
chart only shrinks the positive coordinates. The quadratic model of this deformation is
`TauCeti.quadraticHandleDeformation`; this file reads it in finitely many charts with disjoint
sources and glues it to the identity outside them (`TauCeti.exists_inter_deformation_of_charts`).

The result, `TauCeti.exists_inter_sublevel_union_cells_deformation`, applies to any set `X ⊆ M`
whose points outside the balls `‖ψ x‖ ≤ ρ` of the charts lie in `{f ≤ c - ε}`, and which is
preserved inside these balls by scaling the positive coordinates by factors in `[0, 1]`. For such
`X`, the intersection of `X` with `{f ≤ c - ε}` and the cells is a strong deformation retract of
`X`. The charts and width supplied by `TauCeti.IsMorse.exists_admissible_morseCharts` satisfy the
hypotheses on the charts with `ρ = √(2ε)`.

The positive and negative coordinates of a chart are separated by
`EuclideanSpace.sumComplEquivProd`, which turns the chart into one with values in the product
`Eᵤ × Eₛ` on which `TauCeti.quadraticHandleDeformation` is defined. The deformation moves no point
outside the compact preimages of the balls, which makes the gluing continuous.

## Main results

* `TauCeti.exists_inter_sublevel_union_cells_deformation`: Milnor's retraction of `X` onto its
  intersection with the lower sublevel and the cells of disjoint Morse charts.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

noncomputable section

open Function Set unitInterval

namespace TauCeti

section MorseCharts

variable {M ι : Type*} [TopologicalSpace M] {n : ℕ}

/-- In a Morse chart `ψ` of index `k`, read in the coordinates `(u, v)` of
`EuclideanSpace.sumComplEquivProd`, a point lies in the model set `quadraticSublevelUnionCell ε`
iff it lies in the sublevel `{f ≤ c - ε}` or in the cell of the chart. -/
private theorem sumComplEquivProd_mem_quadraticSublevelUnionCell_iff
    {ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {k : ℕ} {f : M → ℝ} {c ε : ℝ}
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    {x : M} (hx : x ∈ ψ.source) :
    EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) (ψ x) ∈
        quadraticSublevelUnionCell ε ↔
      f x ≤ c - ε ∨ x ∈ ψ.source ∩ ψ ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k ≤ j.val → y j = 0} := by
  have hfx : f x = c + (-‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)
      (ψ x)).1‖ ^ 2 + ‖(EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)
      (ψ x)).2‖ ^ 2) := by
    rw [hf x hx, EuclideanSpace.sum_ite_neg_one_mul_sq_eq]
  rw [mem_quadraticSublevelUnionCell, hfx,
    EuclideanSpace.norm_fst_sumComplEquivProd_sq_le_and_snd_eq_zero_iff]
  exact or_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩ (by simp [hx])

/-- In a Morse chart `ψ` of index `k`, scaling the coordinates `v` of a point of `X` in the ball of
radius `ρ` by `s ∈ [0, 1]` stays in the image of the ball under the coordinate change and in `X`,
when `X` is preserved by this scaling. -/
private theorem sumComplEquivProd_scale_mem_image_closedBall_and_mem
    {ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {k : ℕ} {ρ : ℝ} {X : Set M}
    (hXscale : ∀ x ∈ X ∩ ψ.source, ‖ψ x‖ ≤ ρ → ∀ s ∈ Icc (0 : ℝ) 1,
      ψ.symm (WithLp.toLp 2 fun j ↦ if j.val < k then ψ x j else s * ψ x j) ∈ X)
    {x : M} (hx : x ∈ X ∩ ψ.source) (hρx : ‖ψ x‖ ≤ ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) (ψ x)).1,
        s • (EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) (ψ x)).2) ∈
      EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) '' Metric.closedBall 0 ρ ∧
    ψ.symm ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).symm
      ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) (ψ x)).1,
        s • (EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) (ψ x)).2)) ∈ X := by
  refine ⟨⟨_, ?_, ContinuousLinearEquiv.apply_symm_apply _ _⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (EuclideanSpace.norm_sumComplEquivProd_symm_smul_snd_le (ψ x)
      ((Real.norm_of_nonneg hs.1).trans_le hs.2)).trans hρx
  · simpa only [EuclideanSpace.sumComplEquivProd_symm_smul_snd] using hXscale x hx hρx s hs

/-- **Milnor's handle retraction in Morse charts.** Let `ψ i` be charts of `M` with pairwise
disjoint sources, each containing the closed ball of radius `ρ` about `0` in its target, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. The cell of the chart `ψ i` is the disc
`{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k i}` of the first `k i` coordinates, read in `M`. Let `X ⊆ M` be a
set such that

* every point of `X` outside the balls `‖ψ i x‖ ≤ ρ` lies in the sublevel `{f ≤ c - ε}`;
* inside these balls, `X` is preserved by scaling the coordinates `yⱼ`, `j ≥ k i`, by factors in
  `[0, 1]`.

Then `X ∩ ({f ≤ c - ε} ∪ ⋃ cells)` is a strong deformation retract of `X`: there is a retraction
of `X` onto it, and a homotopy in `X` from this retraction to the identity which fixes it
pointwise. In Milnor's proof of cell attachment, `X` is the sublevel `{F ≤ c - ε}` of the function
`F` obtained by lowering `f` near the critical points, and the conclusion retracts it onto
`{f ≤ c - ε}` with one cell attached at each critical point. -/
theorem exists_inter_sublevel_union_cells_deformation [T2Space M] [Finite ι]
    (ψ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ) {f : M → ℝ} {c ε ρ : ℝ}
    (hρ : ∀ i, Metric.closedBall 0 ρ ⊆ (ψ i).target)
    (hf : ∀ i, ∀ y ∈ (ψ i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
    {X : Set M} (hXout : ∀ x ∈ X, (∀ i, x ∈ (ψ i).source → ρ < ‖ψ i x‖) → f x ≤ c - ε)
    (hXscale : ∀ i, ∀ x ∈ X ∩ (ψ i).source, ‖ψ i x‖ ≤ ρ → ∀ s ∈ Icc (0 : ℝ) 1,
      (ψ i).symm (WithLp.toLp 2 fun j ↦ if j.val < k i then ψ i x j else s * ψ i x j) ∈ X) :
    ∃ r : C(X, ↥(X ∩ ({x | f x ≤ c - ε} ∪
        ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id X) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
          ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}}) := by
  -- Read each chart in the coordinates `(u, v)`, `u` the first `k i` coordinates.
  set e : ∀ i, EuclideanSpace ℝ (Fin n) ≃L[ℝ] _ := fun i ↦
    EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k i
  set φ := fun i ↦ (ψ i).transHomeomorph (e i).toHomeomorph
  have hφ_source (i : ι) : (φ i).source = (ψ i).source := by simp [φ]
  have hφ_apply (i : ι) (x : M) : φ i x = e i (ψ i x) := by simp [φ]
  have hφ_symm (i : ι) (z) : (φ i).symm z = (ψ i).symm ((e i).symm z) := by simp [φ]
  set S := {x | f x ≤ c - ε} ∪
    ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}
  -- Membership of a chart point in the model set `quadraticSublevelUnionCell ε`.
  have hQ (i : ι) {x : M} (hx : x ∈ (ψ i).source) :
      φ i x ∈ quadraticSublevelUnionCell ε ↔ f x ≤ c - ε ∨
        x ∈ (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0} := by
    rw [hφ_apply]
    exact sumComplEquivProd_mem_quadraticSublevelUnionCell_iff (hf i) hx
  have hS (x : M) (hxX : x ∈ X) :
      x ∈ S ↔ ∀ i, x ∈ (φ i).source → φ i x ∈ quadraticSublevelUnionCell ε := by
    simp only [hφ_source]
    refine ⟨fun hxS i hi ↦ (hQ i hi).2 ?_, fun h ↦ ?_⟩
    · rcases hxS with h | h
      · exact .inl h
      · obtain ⟨j, hj⟩ := mem_iUnion.1 h
        obtain rfl : j = i := hψ.eq (not_disjoint_iff.2 ⟨x, hj.1, hi⟩)
        exact .inr hj
    · by_cases hx : ∃ i, x ∈ (ψ i).source
      · obtain ⟨i, hi⟩ := hx
        rcases (hQ i hi).1 (h i hi) with h' | h'
        · exact .inl h'
        · exact .inr (mem_iUnion.2 ⟨i, h'⟩)
      · exact .inl (hXout x hxX fun i hi ↦ absurd hi (not_exists.1 hx i))
  -- The compact regions: the images of the closed balls of radius `ρ`.
  set C := fun i ↦ e i '' Metric.closedBall 0 ρ
  have hC (i : ι) : IsCompact (C i) := (isCompact_closedBall 0 ρ).image (e i).continuous
  have hCφ (i : ι) : C i ⊆ (φ i).target := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [φ] using hρ i hy
  -- Outside the model set, chart points lie in the balls, which the scaling preserves.
  -- The model deformation only scales the second component by factors in `[0, 1]`.
  have hX (i : ι) (x : M) (hx : x ∈ X ∩ (φ i).source)
      (hxQ : φ i x ∉ quadraticSublevelUnionCell ε) (t : I) :
      quadraticHandleDeformation ε (t, φ i x) ∈ C i ∧
        (φ i).symm (quadraticHandleDeformation ε (t, φ i x)) ∈ X := by
    rw [hφ_source] at hx
    obtain ⟨hxX, hx⟩ := hx
    have hρx : ‖ψ i x‖ ≤ ρ := by
      by_contra hlt
      refine hxQ ((hQ i hx).2 (.inl (hXout x hxX fun j hj ↦ ?_)))
      obtain rfl : j = i := hψ.eq (not_disjoint_iff.2 ⟨x, hj, hx⟩)
      exact lt_of_not_ge hlt
    obtain ⟨s, hs, hst⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t (φ i x)
    rw [hst, hφ_symm, hφ_apply]
    exact sumComplEquivProd_scale_mem_image_closedBall_and_mem (hXscale i) ⟨hxX, hx⟩ hρx hs
  exact exists_inter_deformation_of_charts (φ := φ) (G := fun _ ↦ quadraticHandleDeformation ε)
    (by simpa only [hφ_source] using hψ) hCφ hX hC (fun _ ↦ quadraticHandleRetraction_mem ε) hS

end MorseCharts

end TauCeti
