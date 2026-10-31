/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CellAttachment
public import TauCeti.Topology.CWComplex.Classical.Skeleton.CellMap

/-!
# The cells of a critical level form a relative CW complex

Milnor's cell attachment theorem (`TauCeti.IsMorse.exists_sublevel_union_cells_deformation`) says
that, for small `ε > 0`, the sublevel `M_{c+ε} = {f ≤ c + ε}` of a Morse function strong
deformation retracts onto the lower sublevel `M_{c-ε} = {f ≤ c - ε}` together with one disc at
each critical point of the level `c`: in a normalized Morse chart `φ` of index `λ`, in which
`f = c - Σ_{j < λ} yⱼ² + Σ_{j ≥ λ} yⱼ²`, the disc is `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ λ}`. This file
shows that these discs are the cells of a relative CW complex over `M_{c-ε}`, so that `M_{c+ε}` has
the homotopy type of `M_{c-ε}` with one `λ`-cell attached at each critical point of index `λ`.

The characteristic map of the cell of a chart `φ` is `TauCeti.morseCell`: on the Euclidean unit
disc of `ℝ^λ` it sends `w` to the point of chart coordinates `(√ε • w, 0)`, with `w` in the first
`λ` coordinates. On the boundary sphere `f = c - ε`, so the attaching map lands in `M_{c-ε}`,
while `f > c - ε` on the open disc, which is therefore disjoint from `M_{c-ε}`. Mathlib's
classical `Topology.RelCWComplex` takes characteristic maps on the closed unit ball of the sup
norm, which is carried onto the Euclidean disc by the radial homeomorphism
`ContinuousLinearEquiv.unitBallHomeomorph`; read back on the Euclidean disc `𝔻 λ` through
`TauCeti.cellDiskHom`, the characteristic map is again `TauCeti.morseCell`
(`TauCeti.coe_cellDiskHom_morseRelCWComplex`).

The construction is purely topological: it uses only charts `φ i` that are open partial
homeomorphisms to `ℝⁿ` with pairwise disjoint sources, the normal form of a continuous `f` in
them, and the containment of the closed ball of radius `√ε` in their targets.

## Main definitions

* `TauCeti.morseCell`: the characteristic map of the negative disc of a Morse chart.
* `TauCeti.morseRelCWComplex`: the finite relative CW complex `M_{c-ε} ∪ ⋃ cells` over
  `M_{c-ε}`, with one `k i`-cell for each chart `φ i`.

## Main results

* `TauCeti.image_morseCell_closedBall`: the image of the closed unit disc under `morseCell` is
  the disc `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ λ}` of the chart.
* `TauCeti.apply_morseCell`: the value of `f` on the cell is `c - ε‖w‖²`.
* `TauCeti.finite_morseRelCWComplex`: the relative CW complex `TauCeti.morseRelCWComplex` is
  finite.
* `TauCeti.IsMorse.exists_relCWComplex_sublevel_deformation`: **Milnor's cell attachment theorem
  in CW form.** Across a value `c` of a Morse function with a compact band around it, the
  sublevel `M_{c+ε}` strong deformation retracts onto a finite CW complex relative to `M_{c-ε}`
  whose `m`-cells correspond to the critical points of index `m` on the level `c`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Filter Topology Metric Topology.RelCWComplex
open scoped Manifold ContDiff

namespace TauCeti

universe u

section MorseCell

variable {M : Type u} [TopologicalSpace M] {n m : ℕ}
  {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {ε : ℝ}

variable (φ ε) in
/-- The **characteristic map of the negative disc of a Morse chart** `φ`: for `m ≤ n`, the point
of `M` whose chart coordinates are `(√ε • w, 0)`, with `w : ℝᵐ` in the first `m` coordinates.
When `f = c - Σ_{j < m} yⱼ² + Σ_{j ≥ m} yⱼ²` in the chart, it carries the closed unit disc onto the
cell `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ m}` (`TauCeti.image_morseCell_closedBall`), on which
`f = c - ε‖w‖²` (`TauCeti.apply_morseCell`). -/
def morseCell (hm : m ≤ n) (w : EuclideanSpace ℝ (Fin m)) : M :=
  φ.symm (√ε • LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hm) w)

theorem morseCell_apply (hm : m ≤ n) (w : EuclideanSpace ℝ (Fin m)) :
    morseCell φ ε hm w =
      φ.symm (√ε • LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hm) w) :=
  (rfl)

/-- The radial homeomorphism from the sup norm to the Euclidean norm keeps the closed unit ball. -/
private theorem norm_unitBallHomeomorph_symm_le_one {x : Fin m → ℝ} (hx : x ∈ closedBall 0 1) :
    ‖(EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x‖ ≤ 1 :=
  (EuclideanSpace.equiv (Fin m) ℝ).norm_unitBallHomeomorph_symm_le_one_iff.2
    (mem_closedBall_zero_iff.1 hx)

/-- The radial homeomorphism from the sup norm to the Euclidean norm keeps the open unit ball. -/
private theorem norm_unitBallHomeomorph_symm_lt_one {x : Fin m → ℝ} (hx : x ∈ ball 0 1) :
    ‖(EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x‖ < 1 :=
  (EuclideanSpace.equiv (Fin m) ℝ).norm_unitBallHomeomorph_symm_lt_one_iff.2
    (mem_ball_zero_iff.1 hx)

/-- The radial homeomorphism from the sup norm to the Euclidean norm keeps the unit sphere. -/
private theorem norm_unitBallHomeomorph_symm_eq_one {x : Fin m → ℝ} (hx : x ∈ sphere 0 1) :
    ‖(EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x‖ = 1 :=
  (EuclideanSpace.equiv (Fin m) ℝ).norm_unitBallHomeomorph_symm_eq_one_iff.2
    (mem_sphere_zero_iff_norm.1 hx)

variable (hball : closedBall 0 √ε ⊆ φ.target)
include hball

private theorem smul_extendByZero_mem_target (hm : m ≤ n) {w : EuclideanSpace ℝ (Fin m)}
    (hw : ‖w‖ ≤ 1) :
    √ε • LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hm) w ∈ φ.target := by
  refine hball (mem_closedBall_zero_iff.2 ?_)
  rw [norm_smul, LinearIsometry.norm_map, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hw

/-- The chart coordinates of the point of the cell of disc coordinate `w` are `(√ε • w, 0)`. -/
theorem apply_morseCell_eq (hm : m ≤ n) {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ ≤ 1) :
    φ (morseCell φ ε hm w) = √ε • LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hm) w :=
  φ.right_inv (smul_extendByZero_mem_target hball hm hw)

/-- The cell of a Morse chart lies in the source of the chart. -/
theorem morseCell_mem_source (hm : m ≤ n) {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ ≤ 1) :
    morseCell φ ε hm w ∈ φ.source :=
  φ.map_target (smul_extendByZero_mem_target hball hm hw)

/-- The chart coordinates of a point of the cell vanish beyond the first `m`. -/
theorem apply_morseCell_apply_eq_zero (hm : m ≤ n) {w : EuclideanSpace ℝ (Fin m)}
    (hw : ‖w‖ ≤ 1) {j : Fin n} (hj : m ≤ j.val) : φ (morseCell φ ε hm w) j = 0 := by
  rw [apply_morseCell_eq hball hm hw, PiLp.smul_apply,
    EuclideanSpace.piLpExtendByZero_castLEEmb_apply_of_le hm w hj, smul_zero]

/-- The squared norm of the chart coordinates of the point of the cell of disc coordinate `w` is
`ε‖w‖²`. -/
theorem norm_apply_morseCell_sq (hε : 0 ≤ ε) (hm : m ≤ n) {w : EuclideanSpace ℝ (Fin m)}
    (hw : ‖w‖ ≤ 1) : ‖φ (morseCell φ ε hm w)‖ ^ 2 = ε * ‖w‖ ^ 2 := by
  rw [apply_morseCell_eq hball hm hw, norm_smul, LinearIsometry.norm_map,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hε]

/-- Undoing the scaling and the zero extension recovers the disc coordinate of a cell point. -/
private theorem inv_smul_take_apply_morseCell (hε : 0 < ε) (hm : m ≤ n)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ ≤ 1) :
    (√ε)⁻¹ • EuclideanSpace.take hm (φ (morseCell φ ε hm w)) = w := by
  rw [apply_morseCell_eq hball hm hw, ← map_smul (LinearIsometry.piLpExtendByZero 2 ℝ ℝ _),
    EuclideanSpace.take_piLpExtendByZero_castLEEmb, inv_smul_smul₀ (Real.sqrt_pos.2 hε).ne']

/-- The characteristic map of a Morse cell is continuous on the closed unit disc. -/
theorem continuousOn_morseCell (hm : m ≤ n) : ContinuousOn (morseCell φ ε hm) (closedBall 0 1) :=
  φ.continuousOn_symm.comp (((LinearIsometry.piLpExtendByZero 2 ℝ ℝ
    (Fin.castLEEmb hm)).continuous.const_smul √ε).continuousOn) fun _ hw ↦
      smul_extendByZero_mem_target hball hm (mem_closedBall_zero_iff.1 hw)

/-- **The cell of a Morse chart.** The closed unit disc of `ℝᵐ` is carried by `morseCell` onto
the points of the chart whose coordinates satisfy `‖y‖² ≤ ε` and `yⱼ = 0` for `j ≥ m`. -/
theorem image_morseCell_closedBall (hε : 0 < ε) (hm : m ≤ n) :
    morseCell φ ε hm '' closedBall 0 1 =
      φ.source ∩ φ ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, m ≤ j.val → y j = 0} := by
  ext x
  refine ⟨?_, fun ⟨hx, hxε, hx0⟩ ↦ ?_⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff] at hw
    refine ⟨morseCell_mem_source hball hm hw, ?_, fun j hj ↦
      apply_morseCell_apply_eq_zero hball hm hw hj⟩
    rw [norm_apply_morseCell_sq hball hε.le hm hw]
    exact mul_le_of_le_one_right hε.le (pow_le_one₀ (norm_nonneg _) hw)
  · have hsq := Real.sqrt_pos.2 hε
    have hz : ‖φ x‖ ≤ √ε := (abs_of_nonneg (norm_nonneg _)).symm.trans_le (Real.abs_le_sqrt hxε)
    refine ⟨(√ε)⁻¹ • EuclideanSpace.take hm (φ x), mem_closedBall_zero_iff.2 ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq.le), ← LinearIsometry.norm_map
        (LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hm)),
        EuclideanSpace.piLpExtendByZero_castLEEmb_take hm hx0]
      exact (inv_mul_le_one₀ hsq).2 hz
    · rw [morseCell_apply, map_smul, smul_inv_smul₀ hsq.ne',
        EuclideanSpace.piLpExtendByZero_castLEEmb_take hm hx0, φ.left_inv hx]

variable {c : ℝ} {f : M → ℝ}

/-- The value of `f` on the cell of a Morse chart in which `f` has the normal form
`c - Σ_{j < m} yⱼ² + Σ_{j ≥ m} yⱼ²`: at the point of disc coordinate `w` it is `c - ε‖w‖²`. -/
theorem apply_morseCell (hε : 0 ≤ ε) (hm : m ≤ n)
    (hf : ∀ y ∈ φ.source, f y = c + ∑ j, (if j.val < m then -1 else 1) * φ y j ^ 2)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ ≤ 1) : f (morseCell φ ε hm w) = c - ε * ‖w‖ ^ 2 := by
  set p : Fin n → Prop := fun j ↦ j.val < m
  have h2 : (EuclideanSpace.sumComplEquivProd ℝ p (φ (morseCell φ ε hm w))).2 = 0 :=
    EuclideanSpace.snd_sumComplEquivProd_eq_zero_iff.2 fun j hj ↦
      apply_morseCell_apply_eq_zero hball hm hw (not_lt.1 hj)
  have h1 := EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq (p := p)
    (φ (morseCell φ ε hm w))
  rw [h2, norm_zero, norm_apply_morseCell_sq hball hε hm hw] at h1
  rw [hf _ (morseCell_mem_source hball hm hw), EuclideanSpace.sum_ite_neg_one_mul_sq_eq (p := p),
    h2, norm_zero]
  linarith

/-- The disc coordinate of a cell point, read back through the sup-norm ball. -/
private theorem unitBallHomeomorph_inv_smul_take_apply_morseCell (hε : 0 < ε) (hm : m ≤ n)
    {x : Fin m → ℝ} (hx : x ∈ closedBall 0 1) :
    (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph ((√ε)⁻¹ • EuclideanSpace.take hm
      (φ (morseCell φ ε hm ((EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x)))) = x := by
  rw [inv_smul_take_apply_morseCell hball hε hm (norm_unitBallHomeomorph_symm_le_one hx),
    Homeomorph.apply_symm_apply]

variable (φ) in
/-- The characteristic map of the cell of `φ` on the closed unit ball of the sup norm on `ℝᵐ`, the
domain of characteristic maps of a classical CW complex: `TauCeti.morseCell` precomposed with the
radial homeomorphism onto the Euclidean disc. -/
private def morseCellMap (hε : 0 < ε) (hm : m ≤ n) : PartialEquiv (Fin m → ℝ) M where
  toFun x := morseCell φ ε hm ((EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x)
  invFun y :=
    (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph ((√ε)⁻¹ • EuclideanSpace.take hm (φ y))
  source := ball 0 1
  target := (fun x ↦ morseCell φ ε hm ((EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x))
    '' ball 0 1
  map_source' _ hx := mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [unitBallHomeomorph_inv_smul_take_apply_morseCell hball hε hm
      (ball_subset_closedBall hx)]
  left_inv' x hx :=
    unitBallHomeomorph_inv_smul_take_apply_morseCell hball hε hm (ball_subset_closedBall hx)
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [unitBallHomeomorph_inv_smul_take_apply_morseCell hball hε hm
      (ball_subset_closedBall hx)]

private theorem coe_morseCellMap (hε : 0 < ε) (hm : m ≤ n) :
    ⇑(morseCellMap φ hball hε hm) =
      morseCell φ ε hm ∘ (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm :=
  rfl

private theorem continuousOn_morseCellMap (hε : 0 < ε) (hm : m ≤ n) :
    ContinuousOn (morseCellMap φ hball hε hm) (closedBall 0 1) := by
  rw [coe_morseCellMap]
  exact (continuousOn_morseCell hball hm).comp (Homeomorph.continuous _).continuousOn
    fun _ hx ↦ mem_closedBall_zero_iff.2 (norm_unitBallHomeomorph_symm_le_one hx)

private theorem continuousOn_morseCellMap_symm (hε : 0 < ε) (hm : m ≤ n) :
    ContinuousOn (morseCellMap φ hball hε hm).symm (morseCellMap φ hball hε hm).target := by
  refine ((Homeomorph.continuous _).comp_continuousOn
    (((EuclideanSpace.continuous_take hm).comp_continuousOn φ.continuousOn).const_smul
      (√ε)⁻¹)).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact morseCell_mem_source hball hm
    (norm_unitBallHomeomorph_symm_le_one (ball_subset_closedBall hx))

private theorem image_morseCellMap_closedBall (hε : 0 < ε) (hm : m ≤ n) :
    morseCellMap φ hball hε hm '' closedBall 0 1 =
      φ.source ∩ φ ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, m ≤ j.val → y j = 0} := by
  rw [coe_morseCellMap, image_comp, Homeomorph.image_symm,
    ← image_morseCell_closedBall hball hε hm]
  congr 1
  ext x
  simp

private theorem image_morseCellMap_ball_subset_source (hε : 0 < ε) (hm : m ≤ n) :
    morseCellMap φ hball hε hm '' ball 0 1 ⊆ φ.source :=
  ((image_mono ball_subset_closedBall).trans
    (image_morseCellMap_closedBall hball hε hm).subset).trans inter_subset_left

end MorseCell

section RelCWComplex

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} [Finite ι] {f : M → ℝ} {c ε : ℝ}

/-- **The cells of a critical level form a relative CW complex.** Let `φ i` be charts of `M` into
`ℝⁿ` with pairwise disjoint sources, each containing the closed ball of radius `√ε` in its target,
in which a continuous `f` has the normal form `c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. Then the
lower sublevel `{f ≤ c - ε}` with the discs `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k i}` of the charts
attached is a finite CW complex relative to `{f ≤ c - ε}`, with one `k i`-cell for each `i`
(`TauCeti.morseRelCWComplexCellEquiv`), whose characteristic map is `TauCeti.morseCell`
(`TauCeti.coe_map_morseRelCWComplex`). -/
@[instance_reducible]
def morseRelCWComplex (hfc : Continuous f)
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2) :
    RelCWComplex ({x | f x ≤ c - ε} ∪
      ⋃ i, (φ i).source ∩ φ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0})
      {x | f x ≤ c - ε} :=
  RelCWComplex.mkFinite _ _ (fun m ↦ {i // k i = m})
    (fun _ i ↦ morseCellMap (φ i) (hball i) hε (i.2 ▸ hk i))
    (eventually_atTop.2 ⟨n + 1, fun m hm ↦ ⟨fun i ↦ by have := hk i; have := i.2; omega⟩⟩)
    (fun _ ↦ inferInstance) (fun _ _ ↦ rfl)
    (fun _ i ↦ continuousOn_morseCellMap (hball i) hε _)
    (fun _ i ↦ continuousOn_morseCellMap_symm (hball i) hε _)
    (by
      rintro ⟨m, i, hi⟩ - ⟨m', i', hi'⟩ - hne
      obtain rfl | hii' := eq_or_ne i i'
      · subst hi hi'
        exact absurd rfl hne
      exact (hφ hii').mono (image_morseCellMap_ball_subset_source _ _ _)
        (image_morseCellMap_ball_subset_source _ _ _))
    (by
      rintro _ ⟨i, rfl⟩
      refine disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩ hxD
      have hw := norm_unitBallHomeomorph_symm_lt_one hx
      rw [mem_ofPred_eq, coe_morseCellMap, comp_apply,
        apply_morseCell (hball i) hε.le _ (hf i) hw.le] at hxD
      have := mul_lt_mul_of_pos_left (pow_lt_one₀ (norm_nonneg _) hw two_ne_zero) hε
      linarith)
    (by
      rintro _ ⟨i, rfl⟩ x hx
      refine Or.inl ?_
      rw [mem_ofPred_eq, coe_morseCellMap, comp_apply, apply_morseCell (hball i) hε.le _ (hf i)
        (norm_unitBallHomeomorph_symm_eq_one hx).le, norm_unitBallHomeomorph_symm_eq_one hx]
      linarith)
    (isClosed_le hfc continuous_const)
    (by
      congr 1
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, hx⟩
        exact ⟨i, image_morseCellMap_closedBall (hball i) hε _ ▸ hx⟩
      · rintro ⟨i, hx⟩
        exact ⟨k i, ⟨i, rfl⟩, (image_morseCellMap_closedBall (hball i) hε _).symm ▸ hx⟩)

variable (hfc : Continuous f) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
  (hε : 0 < ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
  (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)

/-- The `m`-cells of `TauCeti.morseRelCWComplex` are the charts `φ i` with `k i = m`. -/
def morseRelCWComplexCellEquiv (m : ℕ) :
    @cell M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m ≃ {i // k i = m} :=
  Equiv.refl _

/-- `TauCeti.morseRelCWComplex` is a finite relative CW complex: its cells have dimension at most
`n` and there are finitely many charts. -/
instance finite_morseRelCWComplex :
    @RelCWComplex.Finite M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) :=
  let := morseRelCWComplex hfc φ hφ k hk hε hball hf
  { eventually_isEmpty_cell :=
      eventually_atTop.2 ⟨n + 1, fun m hm ↦
        ⟨fun i : {i // k i = m} ↦ by have := hk i.1; have := i.2; omega⟩⟩
    finite_cell := fun m ↦ inferInstanceAs (Finite {i // k i = m}) }

/-- The characteristic map of the `m`-cell of `TauCeti.morseRelCWComplex` at the chart `φ i` is
`TauCeti.morseCell` precomposed with the radial homeomorphism from the closed unit ball of the sup
norm onto the Euclidean disc. -/
@[simp]
theorem coe_map_morseRelCWComplex (m : ℕ)
    (j : @cell M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m) :
    ⇑(@map M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m j) =
      morseCell (φ (morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).1) ε
          ((morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).2 ▸ hk _) ∘
        (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm :=
  (rfl)

/-- Read on the Euclidean disc `𝔻 m` through `TauCeti.cellDiskHom`, the characteristic map of the
`m`-cell of `TauCeti.morseRelCWComplex` at the chart `φ i` is `TauCeti.morseCell`: it sends `w` to
the point of chart coordinates `(√ε • w, 0)`. -/
theorem coe_cellDiskHom_morseRelCWComplex [T2Space M] (m : ℕ)
    (j : @cell M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m) (z : TopCat.disk.{u} m) :
    (@cellDiskHom M _ _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m j z : M) =
      morseCell (φ (morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).1) ε
        ((morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).2 ▸ hk _)
        (z : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).down := by
  let := morseRelCWComplex hfc φ hφ k hk hε hball hf
  rw [coe_cellDiskHom_apply, coe_map_morseRelCWComplex, comp_apply,
    coe_diskHomeomorphClosedBall_apply, Homeomorph.symm_apply_apply]

end RelCWComplex

section IsMorse

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {c δ : ℝ}

/-- **Milnor's cell attachment theorem in CW form.** Let `f` be a Morse function and `c` a value
with a compact band `f⁻¹[c - δ, c + δ]`. Then for some `0 < ε ≤ δ` the sublevel `{f ≤ c + ε}`
strong deformation retracts onto a finite CW complex `C ⊆ {f ≤ c + ε}` relative to the lower
sublevel `{f ≤ c - ε}`, whose `m`-cells correspond to the critical points of index `m` on the level
`c`. The complex is `TauCeti.morseRelCWComplex` built from normalized Morse charts at these
critical points. -/
theorem IsMorse.exists_relCWComplex_sublevel_deformation (hf : IsMorse I f) (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ ∃ (C : Set M) (_ : RelCWComplex C {x | f x ≤ c - ε})
      (_ : RelCWComplex.Finite C) (hC : C ⊆ {x | f x ≤ c + ε}),
      (∀ m, Nonempty (cell C m ≃
        {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = m})) ∧
      ∃ r : C({x | f x ≤ c + ε}, C), (∀ x, r (ContinuousMap.inclusion hC x) = x) ∧
        Nonempty (((ContinuousMap.inclusion hC).comp r).HomotopyRel (ContinuousMap.id _)
          {x | (x : M) ∈ C}) := by
  obtain ⟨ε, hε, hεδ, ψ, hψ, hψp, r, hr, ⟨G⟩⟩ :=
    hf.exists_sublevel_union_cells_deformation hδ hcompact
  have hk : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}),
      manifoldMorseIndex I f p ≤ Module.finrank ℝ E := fun _ ↦ manifoldMorseIndex_le_finrank
  have hball : ∀ p, closedBall 0 √ε ⊆ (ψ p).target := fun p ↦
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith))).trans (hψp p).2.2.1
  have : Finite ↥(criticalPoints I f ∩ f ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  -- The lower sublevel and the cells lie in `{f ≤ c}`.
  have hS : {x | f x ≤ c - ε} ∪ ⋃ p, (ψ p).source ∩ ψ p ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧
      ∀ i : Fin (Module.finrank ℝ E), manifoldMorseIndex I f p ≤ i.val → y i = 0} ⊆
      {x | f x ≤ c + ε} := by
    rintro x (hx | hx)
    · rw [mem_ofPred_eq] at hx ⊢
      linarith
    obtain ⟨p, hx⟩ := mem_iUnion.1 hx
    have hx' : x ∈ morseCell (ψ p).toOpenPartialHomeomorph ε (hk p) '' closedBall 0 1 := by
      rw [image_morseCell_closedBall (hball p) hε (hk p)]
      exact hx
    obtain ⟨w, hw, rfl⟩ := hx'
    rw [mem_ofPred_eq, apply_morseCell (f := f) (hball p) hε.le (hk p) (hψp p).2.2.2
      (mem_closedBall_zero_iff.1 hw)]
    nlinarith [sq_nonneg ‖w‖]
  refine ⟨ε, hε, hεδ, _, morseRelCWComplex hf.contMDiff.continuous
    (fun p ↦ (ψ p).toOpenPartialHomeomorph) hψ (manifoldMorseIndex I f ·) hk hε hball
    (fun p ↦ (hψp p).2.2.2), finite_morseRelCWComplex _ _ _ _ _ _ _ _, hS,
    fun m ↦ ⟨morseRelCWComplexCellEquiv _ _ _ _ _ _ _ _ m⟩,
    (ContinuousMap.inclusion inter_subset_right).comp r, fun x ↦ ?_,
    ⟨G.cast (by ext; rfl) rfl⟩⟩
  exact congrArg (ContinuousMap.inclusion inter_subset_right) (hr ⟨x, hS x.2, x.2⟩)

end IsMorse

end TauCeti
