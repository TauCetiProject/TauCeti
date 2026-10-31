/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.Cell.Attachment
public import TauCeti.Geometry.Manifold.Morse.Cell.Map
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

The characteristic map of the cell of a chart `φ` is `OpenPartialHomeomorph.morseCellMap`: on the
Euclidean unit disc of `ℝ^λ` it sends `w` to the point of chart coordinates `(√ε • w, 0)`, with `w`
in the first `λ` coordinates. On the boundary sphere `f = c - ε`, so the attaching map lands in
`M_{c-ε}`, while `f > c - ε` on the open disc, which is therefore disjoint from `M_{c-ε}`. Mathlib's
classical `Topology.RelCWComplex` takes characteristic maps on the closed unit ball of the sup
norm, which is carried onto the Euclidean disc by the radial homeomorphism
`ContinuousLinearEquiv.unitBallHomeomorph`; read back on the Euclidean disc `𝔻 λ` through
`TauCeti.cellDiskHom`, the characteristic map is again `OpenPartialHomeomorph.morseCellMap`
(`TauCeti.coe_cellDiskHom_morseRelCWComplex`).

The construction is purely topological: it uses only charts `φ i` that are open partial
homeomorphisms to `ℝⁿ` with pairwise disjoint sources, the normal form of a continuous `f` in
them, and the containment of the closed ball of radius `√ε` in their targets.

## Main definitions

* `TauCeti.morseRelCWComplex`: the finite relative CW complex `M_{c-ε} ∪ ⋃ cells` over
  `M_{c-ε}`, with one `k i`-cell for each chart `φ i`.

## Main results

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

/-- Undoing the scaling and the zero extension recovers the disc coordinate of a cell point. -/
private theorem inv_smul_take_apply_morseCellMap (hε : 0 < ε) (hm : m ≤ n)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ ≤ 1) :
    (√ε)⁻¹ • EuclideanSpace.take hm (φ (φ.morseCellMap hm ε w)) = w := by
  rw [OpenPartialHomeomorph.apply_morseCellMap hball hm hw,
    ← map_smul (LinearIsometry.piLpExtendByZero 2 ℝ ℝ _),
    EuclideanSpace.take_piLpExtendByZero_castLEEmb, inv_smul_smul₀ (Real.sqrt_pos.2 hε).ne']

/-- The disc coordinate of a cell point, read back through the sup-norm ball. -/
private theorem unitBallHomeomorph_inv_smul_take_apply_morseCellMap (hε : 0 < ε) (hm : m ≤ n)
    {x : Fin m → ℝ} (hx : x ∈ closedBall 0 1) :
    (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph ((√ε)⁻¹ • EuclideanSpace.take hm
      (φ (φ.morseCellMap hm ε ((EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x)))) =
      x := by
  rw [inv_smul_take_apply_morseCellMap hball hε hm (norm_unitBallHomeomorph_symm_le_one hx),
    Homeomorph.apply_symm_apply]

variable (φ) in
/-- The characteristic map of the cell of `φ` on the closed unit ball of the sup norm on `ℝᵐ`, the
domain of characteristic maps of a classical CW complex: `OpenPartialHomeomorph.morseCellMap`
precomposed with the radial homeomorphism onto the Euclidean disc. -/
private def morseCellPartialEquiv (hε : 0 < ε) (hm : m ≤ n) : PartialEquiv (Fin m → ℝ) M where
  toFun x := φ.morseCellMap hm ε ((EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x)
  invFun y :=
    (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph ((√ε)⁻¹ • EuclideanSpace.take hm (φ y))
  source := ball 0 1
  target :=
    (fun x ↦ φ.morseCellMap hm ε ((EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm x)) ''
      ball 0 1
  map_source' _ hx := mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [unitBallHomeomorph_inv_smul_take_apply_morseCellMap hball hε hm
      (ball_subset_closedBall hx)]
  left_inv' x hx :=
    unitBallHomeomorph_inv_smul_take_apply_morseCellMap hball hε hm (ball_subset_closedBall hx)
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [unitBallHomeomorph_inv_smul_take_apply_morseCellMap hball hε hm
      (ball_subset_closedBall hx)]

private theorem coe_morseCellPartialEquiv (hε : 0 < ε) (hm : m ≤ n) :
    ⇑(morseCellPartialEquiv φ hball hε hm) =
      φ.morseCellMap hm ε ∘ (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm :=
  rfl

private theorem continuousOn_morseCellPartialEquiv (hε : 0 < ε) (hm : m ≤ n) :
    ContinuousOn (morseCellPartialEquiv φ hball hε hm) (closedBall 0 1) := by
  rw [coe_morseCellPartialEquiv]
  exact (OpenPartialHomeomorph.continuousOn_morseCellMap hball hm).comp
    (Homeomorph.continuous _).continuousOn fun _ hx ↦
      mem_closedBall_zero_iff.2 (norm_unitBallHomeomorph_symm_le_one hx)

private theorem continuousOn_morseCellPartialEquiv_symm (hε : 0 < ε) (hm : m ≤ n) :
    ContinuousOn (morseCellPartialEquiv φ hball hε hm).symm
      (morseCellPartialEquiv φ hball hε hm).target := by
  refine ((Homeomorph.continuous _).comp_continuousOn
    (((EuclideanSpace.continuous_take hm).comp_continuousOn φ.continuousOn).const_smul
      (√ε)⁻¹)).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact OpenPartialHomeomorph.morseCellMap_mem_source hball hm
    (norm_unitBallHomeomorph_symm_le_one (ball_subset_closedBall hx))

private theorem image_morseCellPartialEquiv_closedBall (hε : 0 < ε) (hm : m ≤ n) :
    morseCellPartialEquiv φ hball hε hm '' closedBall 0 1 =
      φ.source ∩ φ ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, m ≤ j.val → y j = 0} := by
  rw [coe_morseCellPartialEquiv, image_comp, Homeomorph.image_symm,
    ← OpenPartialHomeomorph.morseCellMap_image_closedBall hball hm hε]
  congr 1
  ext x
  simp

private theorem image_morseCellPartialEquiv_ball_subset_source (hε : 0 < ε) (hm : m ≤ n) :
    morseCellPartialEquiv φ hball hε hm '' ball 0 1 ⊆ φ.source :=
  ((image_mono ball_subset_closedBall).trans
    (image_morseCellPartialEquiv_closedBall hball hε hm).subset).trans inter_subset_left

end MorseCell

section RelCWComplex

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} [Finite ι] {f : M → ℝ} {c ε : ℝ}

/-- **The cells of a critical level form a relative CW complex.** Let `φ i` be charts of `M` into
`ℝⁿ` with pairwise disjoint sources, each containing the closed ball of radius `√ε` in its target,
in which a continuous `f` has the normal form `c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. Then the
lower sublevel `{f ≤ c - ε}` with the discs `{‖y‖² ≤ ε, yⱼ = 0 for j ≥ k i}` of the charts
attached is a finite CW complex relative to `{f ≤ c - ε}`, with one `k i`-cell for each `i`
(`TauCeti.morseRelCWComplexCellEquiv`), whose characteristic map is
`OpenPartialHomeomorph.morseCellMap` (`TauCeti.coe_map_morseRelCWComplex`). -/
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
    (fun _ i ↦ morseCellPartialEquiv (φ i) (hball i) hε (i.2 ▸ hk i))
    (eventually_atTop.2 ⟨n + 1, fun m hm ↦ ⟨fun i ↦ by have := hk i; have := i.2; omega⟩⟩)
    (fun _ ↦ inferInstance) (fun _ _ ↦ rfl)
    (fun _ i ↦ continuousOn_morseCellPartialEquiv (hball i) hε _)
    (fun _ i ↦ continuousOn_morseCellPartialEquiv_symm (hball i) hε _)
    (by
      rintro ⟨m, i, hi⟩ - ⟨m', i', hi'⟩ - hne
      obtain rfl | hii' := eq_or_ne i i'
      · subst hi hi'
        exact absurd rfl hne
      exact (hφ hii').mono (image_morseCellPartialEquiv_ball_subset_source _ _ _)
        (image_morseCellPartialEquiv_ball_subset_source _ _ _))
    (by
      rintro _ ⟨i, rfl⟩
      refine disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩ hxD
      have hw := norm_unitBallHomeomorph_symm_lt_one hx
      rw [mem_ofPred_eq, coe_morseCellPartialEquiv, comp_apply,
        OpenPartialHomeomorph.apply_morseCellMap_eq_sub_mul_norm_sq (hball i) (hf i) _ hε.le
          hw.le] at hxD
      have := mul_lt_mul_of_pos_left (pow_lt_one₀ (norm_nonneg _) hw two_ne_zero) hε
      linarith)
    (by
      rintro _ ⟨i, rfl⟩ x hx
      refine Or.inl ?_
      rw [mem_ofPred_eq, coe_morseCellPartialEquiv, comp_apply,
        OpenPartialHomeomorph.apply_morseCellMap_eq_sub_mul_norm_sq (hball i) (hf i) _ hε.le
          (norm_unitBallHomeomorph_symm_eq_one hx).le, norm_unitBallHomeomorph_symm_eq_one hx]
      linarith)
    (isClosed_le hfc continuous_const)
    (by
      congr 1
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, hx⟩
        exact ⟨i, image_morseCellPartialEquiv_closedBall (hball i) hε _ ▸ hx⟩
      · rintro ⟨i, hx⟩
        exact ⟨k i, ⟨i, rfl⟩, (image_morseCellPartialEquiv_closedBall (hball i) hε _).symm ▸ hx⟩)

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
`OpenPartialHomeomorph.morseCellMap` precomposed with the radial homeomorphism from the closed
unit ball of the sup norm onto the Euclidean disc. -/
@[simp]
theorem coe_map_morseRelCWComplex (m : ℕ)
    (j : @cell M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m) :
    ⇑(@map M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m j) =
      OpenPartialHomeomorph.morseCellMap
          (φ (morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).1)
          ((morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).2 ▸ hk _) ε ∘
        (EuclideanSpace.equiv (Fin m) ℝ).unitBallHomeomorph.symm :=
  (rfl)

/-- Read on the Euclidean disc `𝔻 m` through `TauCeti.cellDiskHom`, the characteristic map of the
`m`-cell of `TauCeti.morseRelCWComplex` at the chart `φ i` is
`OpenPartialHomeomorph.morseCellMap`: it sends `w` to the point of chart coordinates
`(√ε • w, 0)`. -/
theorem coe_cellDiskHom_morseRelCWComplex [T2Space M] (m : ℕ)
    (j : @cell M _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m) (z : TopCat.disk.{u} m) :
    (@cellDiskHom M _ _ _ _ (morseRelCWComplex hfc φ hφ k hk hε hball hf) m j z : M) =
      OpenPartialHomeomorph.morseCellMap
        (φ (morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).1)
        ((morseRelCWComplexCellEquiv hfc φ hφ k hk hε hball hf m j).2 ▸ hk _) ε
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
    have hx' : x ∈ (ψ p).toOpenPartialHomeomorph.morseCellMap (hk p) ε '' closedBall 0 1 := by
      rw [OpenPartialHomeomorph.morseCellMap_image_closedBall (hball p) (hk p) hε]
      exact hx
    obtain ⟨w, hw, rfl⟩ := hx'
    rw [mem_ofPred_eq, OpenPartialHomeomorph.apply_morseCellMap_eq_sub_mul_norm_sq (f := f)
      (hball p) (hψp p).2.2.2 (hk p) hε.le (mem_closedBall_zero_iff.1 hw)]
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
