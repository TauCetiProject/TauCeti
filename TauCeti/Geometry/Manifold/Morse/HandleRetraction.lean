/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.Analysis.Calculus.Morse.HandleRetraction
public import TauCeti.Analysis.InnerProductSpace.PiL2

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
sources and glues it to the identity outside them.

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

section Gluing

variable {M ι : Type*} [TopologicalSpace M] {Eᵤ Eₛ : ι → Type*}
  [∀ i, NormedAddCommGroup (Eᵤ i)] [∀ i, NormedAddCommGroup (Eₛ i)] [∀ i, NormedSpace ℝ (Eₛ i)]
  {φ : ∀ i, OpenPartialHomeomorph M (Eᵤ i × Eₛ i)} {ε : ℝ} {t : I} {x : M} {i : ι}

/-- Milnor's deformation `TauCeti.quadraticHandleDeformation ε` read in each of the charts `φ i`,
and extended by the identity outside their sources. -/
private def chartHandleDeformation (φ : ∀ i, OpenPartialHomeomorph M (Eᵤ i × Eₛ i)) (ε : ℝ)
    (t : I) (x : M) : M := by
  classical
  exact if h : ∃ i, x ∈ (φ i).source then
    (φ h.choose).symm (quadraticHandleDeformation ε (t, φ h.choose x)) else x

private theorem chartHandleDeformation_of_mem (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source))
    (hx : x ∈ (φ i).source) :
    chartHandleDeformation φ ε t x = (φ i).symm (quadraticHandleDeformation ε (t, φ i x)) := by
  have h : ∃ j, x ∈ (φ j).source := ⟨i, hx⟩
  have hi : h.choose = i := hφ.eq (not_disjoint_iff.2 ⟨x, h.choose_spec, hx⟩)
  rw [chartHandleDeformation, dite_eq_left h]
  generalize h.choose = j at hi ⊢
  subst hi
  rfl

private theorem chartHandleDeformation_of_forall_notMem (hx : ∀ i, x ∉ (φ i).source) :
    chartHandleDeformation φ ε t x = x := by
  rw [chartHandleDeformation, dite_eq_right (not_exists.2 hx)]

section Hypotheses

variable {C : ∀ i, Set (Eᵤ i × Eₛ i)} {X : Set M}
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (hCφ : ∀ i, C i ⊆ (φ i).target)
  (hX : ∀ i, ∀ x ∈ X ∩ (φ i).source, φ i x ∉ quadraticSublevelUnionCell ε →
    ∀ s ∈ Icc (0 : ℝ) 1, ((φ i x).1, s • (φ i x).2) ∈ C i ∧
      (φ i).symm ((φ i x).1, s • (φ i x).2) ∈ X)
include hX

include hCφ in
/-- In a chart, the model deformation of a point of `X` stays in the chart target, and returns to
`X`. -/
private theorem quadraticHandleDeformation_mem_target_and_mem (hxX : x ∈ X) (hx : x ∈ (φ i).source)
    (t : I) :
    quadraticHandleDeformation ε (t, φ i x) ∈ (φ i).target ∧
      (φ i).symm (quadraticHandleDeformation ε (t, φ i x)) ∈ X := by
  by_cases hQ : φ i x ∈ quadraticSublevelUnionCell ε
  · rw [(quadraticHandleDeformation ε).eq_snd t hQ, ContinuousMap.id_apply, (φ i).left_inv hx]
    exact ⟨(φ i).map_source hx, hxX⟩
  · obtain ⟨s, hs, hst⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t (φ i x)
    obtain ⟨hsC, hsX⟩ := hX i x ⟨hxX, hx⟩ hQ s hs
    rw [hst]
    exact ⟨hCφ i hsC, hsX⟩

include hφ hCφ in
private theorem chartHandleDeformation_mem (hx : x ∈ X) (t : I) :
    chartHandleDeformation φ ε t x ∈ X := by
  by_cases h : ∃ i, x ∈ (φ i).source
  · obtain ⟨i, hi⟩ := h
    rw [chartHandleDeformation_of_mem hφ hi]
    exact (quadraticHandleDeformation_mem_target_and_mem hCφ hX hx hi t).2
  · rwa [chartHandleDeformation_of_forall_notMem (not_exists.1 h)]

include hφ in
/-- A point of `X` in a chart whose image lies outside `C i` is not moved. -/
private theorem chartHandleDeformation_eq_self_of_notMem (hxX : x ∈ X) (hx : x ∈ (φ i).source)
    (hxC : φ i x ∉ C i) (t : I) : chartHandleDeformation φ ε t x = x := by
  have hQ : φ i x ∈ quadraticSublevelUnionCell ε := by
    by_contra hQ
    exact hxC (by simpa using (hX i x ⟨hxX, hx⟩ hQ 1 ⟨zero_le_one, le_rfl⟩).1)
  rw [chartHandleDeformation_of_mem hφ hx, (quadraticHandleDeformation ε).eq_snd t hQ,
    ContinuousMap.id_apply, (φ i).left_inv hx]

include hφ hCφ in
/-- The glued deformation is continuous on `X`: near a point of a chart source it is the model
deformation read in that chart, and away from the compact sets `(φ i).symm '' C i` it is the
identity. -/
private theorem continuous_chartHandleDeformation [T2Space M] [Finite ι]
    (hC : ∀ i, IsCompact (C i)) :
    Continuous fun p : I × X ↦ chartHandleDeformation φ ε p.1 p.2 := by
  have hval : Continuous fun q : I × X ↦ (q.2 : M) := continuous_subtype_val.comp continuous_snd
  set K := ⋃ i, (φ i).symm '' C i
  have hK : IsClosed K := (isCompact_iUnion fun i ↦ (hC i).image_of_continuousOn
    ((φ i).continuousOn_symm.mono (hCφ i))).isClosed
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  by_cases h : ∃ i, (p.2 : M) ∈ (φ i).source
  · obtain ⟨i, hi⟩ := h
    have hU : IsOpen {q : I × X | (q.2 : M) ∈ (φ i).source} := (φ i).open_source.preimage hval
    have hcU : ContinuousOn
        (fun q : I × X ↦ (φ i).symm (quadraticHandleDeformation ε (q.1, φ i q.2)))
        {q : I × X | (q.2 : M) ∈ (φ i).source} :=
      (φ i).continuousOn_symm.comp ((quadraticHandleDeformation ε).continuous.comp_continuousOn
        (continuousOn_fst.prodMk ((φ i).continuousOn.comp hval.continuousOn fun _ hq ↦ hq)))
        fun q hq ↦ (quadraticHandleDeformation_mem_target_and_mem hCφ hX q.2.2 hq q.1).1
    exact (hcU.continuousAt (hU.mem_nhds hi)).congr
      (Filter.eventually_of_mem (hU.mem_nhds hi) fun q hq ↦
        (chartHandleDeformation_of_mem hφ hq).symm)
  · have hpK : (p.2 : M) ∉ K := by
      simp only [K, mem_iUnion, not_exists]
      rintro i ⟨z, hz, hzp⟩
      exact not_exists.1 h i (hzp ▸ (φ i).map_target (hCφ i hz))
    refine hval.continuousAt.congr (Filter.eventually_of_mem
      ((hK.isOpen_compl.preimage hval).mem_nhds hpK) fun q hq ↦ ?_)
    by_cases hq' : ∃ i, (q.2 : M) ∈ (φ i).source
    · obtain ⟨i, hi⟩ := hq'
      refine (chartHandleDeformation_eq_self_of_notMem hφ hX q.2.2 hi
        (fun hqC ↦ hq (mem_iUnion.2 ⟨i, φ i q.2, hqC, ?_⟩)) q.1).symm
      exact (φ i).left_inv hi
    · exact (chartHandleDeformation_of_forall_notMem (not_exists.1 hq')).symm

include hφ hCφ in
/-- Milnor's handle retractions in charts `φ i` with disjoint sources glue to a strong deformation
retraction of `X` onto `X ∩ S`, where `S` consists, among the points of `X`, of those whose image
in every chart containing them lies in `TauCeti.quadraticSublevelUnionCell ε`. The hypotheses ask
that the points of `X` moved by the model deformation lie in compact sets `C i` inside the chart
targets, which are preserved, together with `X`, by scaling the second component. -/
private theorem exists_deformation_of_charts [T2Space M] [Finite ι] (hC : ∀ i, IsCompact (C i))
    {S : Set M}
    (hS : ∀ x ∈ X, x ∈ S ↔ ∀ i, x ∈ (φ i).source → φ i x ∈ quadraticSublevelUnionCell ε) :
    ∃ r : C(X, ↥(X ∩ S)),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id X) {x | (x : M) ∈ S}) := by
  -- Points of `S` are not moved, at any time.
  have hfixS {x : M} (hxX : x ∈ X) (hxS : x ∈ S) (t : I) : chartHandleDeformation φ ε t x = x := by
    by_cases h : ∃ i, x ∈ (φ i).source
    · obtain ⟨i, hi⟩ := h
      rw [chartHandleDeformation_of_mem hφ hi,
        (quadraticHandleDeformation ε).eq_snd t ((hS x hxX).1 hxS i hi), ContinuousMap.id_apply,
        (φ i).left_inv hi]
    · exact chartHandleDeformation_of_forall_notMem (not_exists.1 h)
  -- At time `1` the deformation is the identity.
  have hG1 (x : M) : chartHandleDeformation φ ε 1 x = x := by
    by_cases h : ∃ i, x ∈ (φ i).source
    · obtain ⟨i, hi⟩ := h
      rw [chartHandleDeformation_of_mem hφ hi, (quadraticHandleDeformation ε).apply_one,
        ContinuousMap.id_apply, (φ i).left_inv hi]
    · exact chartHandleDeformation_of_forall_notMem (not_exists.1 h)
  -- At time `0` it lands in `S`, since the model retraction lands in the model set.
  have hG0S {x : M} (hxX : x ∈ X) : chartHandleDeformation φ ε 0 x ∈ S := by
    refine (hS _ (chartHandleDeformation_mem hφ hCφ hX hxX 0)).2 fun j hj ↦ ?_
    by_cases h : ∃ i, x ∈ (φ i).source
    · obtain ⟨i, hi⟩ := h
      have hmem := (quadraticHandleDeformation_mem_target_and_mem hCφ hX hxX hi 0).1
      rw [chartHandleDeformation_of_mem hφ hi] at hj ⊢
      obtain rfl : j = i := hφ.eq (not_disjoint_iff.2 ⟨_, hj, (φ i).map_target hmem⟩)
      rw [(φ j).right_inv hmem, (quadraticHandleDeformation ε).apply_zero]
      exact quadraticHandleRetraction_mem ε _
    · rw [chartHandleDeformation_of_forall_notMem (not_exists.1 h)] at hj
      exact absurd hj (not_exists.1 h j)
  have hcont := continuous_chartHandleDeformation hφ hCφ hX hC
  refine ⟨⟨fun x ↦ ⟨chartHandleDeformation φ ε 0 x, chartHandleDeformation_mem hφ hCφ hX x.2 0,
      hG0S x.2⟩, (hcont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩,
    fun x ↦ Subtype.ext (hfixS x.2.1 x.2.2 0), ⟨?_⟩⟩
  exact
    { toFun p :=
        ⟨chartHandleDeformation φ ε p.1 p.2, chartHandleDeformation_mem hφ hCφ hX p.2.2 p.1⟩
      continuous_toFun := hcont.subtype_mk _
      map_zero_left x := rfl
      map_one_left x := Subtype.ext (hG1 x)
      prop' t x hx := Subtype.ext ((hfixS x.2 hx t).trans (hfixS x.2 hx 0).symm) }

end Hypotheses

end Gluing

section MorseCharts

variable {M ι : Type*} [TopologicalSpace M] {n : ℕ}

/-- In the splitting of the coordinates along `j < k`, scaling the second component by `s` scales
the coordinates `j ≥ k`. -/
private theorem sumComplEquivProd_symm_smul_snd (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    (EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).symm
        (((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) y).1,
          s • ((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) y).2) =
      WithLp.toLp 2 fun j ↦ if j.val < k then y j else s * y j := by
  ext j
  by_cases h : j.val < k <;> simp [EuclideanSpace.sumComplEquivProd_symm_apply, h]

/-- Scaling the coordinates `j ≥ k` by a factor in `[0, 1]` does not increase the norm. -/
private theorem norm_sumComplEquivProd_symm_smul_snd_le (k : ℕ) (y : EuclideanSpace ℝ (Fin n))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).symm
        (((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) y).1,
          s • ((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) y).2)‖ ≤ ‖y‖ := by
  set e := EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  have hnorm (z : EuclideanSpace ℝ (Fin n)) : ‖(e z).1‖ ^ 2 + ‖(e z).2‖ ^ 2 = ‖z‖ ^ 2 :=
    EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq z
  rw [← hnorm, ← hnorm y, e.apply_symm_apply,
    norm_smul, mul_pow, Real.norm_of_nonneg hs.1]
  have : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
  nlinarith [sq_nonneg ‖(e y).2‖]

/-- In the splitting of the coordinates along `j < k`, the cell condition `‖u‖² ≤ ε`, `v = 0`
says that `‖y‖² ≤ ε` and that the coordinates `j ≥ k` vanish. -/
private theorem fst_norm_sq_le_and_snd_eq_zero_iff {k : ℕ} {y : EuclideanSpace ℝ (Fin n)}
    {ε : ℝ} :
    (‖((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) y).1‖ ^ 2 ≤ ε ∧
        ((EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k) y).2 = 0) ↔
      ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k ≤ j.val → y j = 0 := by
  set e := EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k
  have hv : (e y).2 = 0 ↔ ∀ j : Fin n, k ≤ j.val → y j = 0 := by
    refine ⟨fun h j hj ↦ ?_, fun h ↦ ?_⟩
    · simpa [e] using congr($h ⟨j, not_lt.2 hj⟩)
    · ext j
      simpa [e] using h j (not_lt.1 j.2)
  have hnorm : ‖(e y).1‖ ^ 2 + ‖(e y).2‖ ^ 2 = ‖y‖ ^ 2 :=
    EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq y
  rw [← hv, ← hnorm]
  refine and_congr_left fun h ↦ ?_
  rw [h, norm_zero]
  simp

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
  -- The quadratic form in the coordinates `(u, v)`.
  have hfφ (i : ι) {x : M} (hx : x ∈ (ψ i).source) :
      f x = c + (-‖(φ i x).1‖ ^ 2 + ‖(φ i x).2‖ ^ 2) := by
    rw [hf i x hx, hφ_apply, EuclideanSpace.sum_ite_neg_one_mul_sq_eq]
  set S := {x | f x ≤ c - ε} ∪
    ⋃ i, (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}
  -- Membership of a chart point in the model set `quadraticSublevelUnionCell ε`.
  have hQ (i : ι) {x : M} (hx : x ∈ (ψ i).source) :
      φ i x ∈ quadraticSublevelUnionCell ε ↔ f x ≤ c - ε ∨
        x ∈ (ψ i).source ∩ ψ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0} := by
    rw [mem_quadraticSublevelUnionCell, hfφ i hx, hφ_apply, fst_norm_sq_le_and_snd_eq_zero_iff]
    exact or_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩ (by simp [hx])
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
  have hX (i : ι) (x : M) (hx : x ∈ X ∩ (φ i).source)
      (hxQ : φ i x ∉ quadraticSublevelUnionCell ε) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ((φ i x).1, s • (φ i x).2) ∈ C i ∧ (φ i).symm ((φ i x).1, s • (φ i x).2) ∈ X := by
    rw [hφ_source] at hx
    obtain ⟨hxX, hx⟩ := hx
    have hρx : ‖ψ i x‖ ≤ ρ := by
      by_contra hlt
      refine hxQ ((hQ i hx).2 (.inl (hXout x hxX fun j hj ↦ ?_)))
      obtain rfl : j = i := hψ.eq (not_disjoint_iff.2 ⟨x, hj, hx⟩)
      exact lt_of_not_ge hlt
    set w := (e i).symm ((φ i x).1, s • (φ i x).2)
    refine ⟨⟨w, ?_, (e i).apply_symm_apply _⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_sumComplEquivProd_symm_smul_snd_le (k i) (ψ i x) hs).trans hρx
    · rw [hφ_symm, hφ_apply]
      simpa only [e, sumComplEquivProd_symm_smul_snd] using hXscale i x ⟨hxX, hx⟩ hρx s hs
  exact exists_deformation_of_charts (φ := φ) (by simpa only [hφ_source] using hψ) hCφ hX hC hS

end MorseCharts

end TauCeti
