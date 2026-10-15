/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Topology.CWComplex.Classical.OpenCells
public import TauCeti.Topology.CWComplex.Classical.Quotient
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Deforming the top cells of a skeleton through their characteristic maps

Let `C` be a relative CW complex, `A` a set of `n`-cells, and `Ψ : I × Dⁿ → Dⁿ` a family of maps
of the closed unit ball which fix the unit sphere. Reading `Ψ` through the characteristic map of
every cell of `A`, and fixing every other point, gives a family of maps
`TauCeti.cellDeformation A Ψ` of the `n`-skeleton `skeletonLT C (n + 1)`, continuous in the time
and the point. Deformations of the closed unit ball fixing its boundary therefore become
deformations of the `n`-skeleton supported in the open cells of `A`.

## Main definitions

* `TauCeti.cellDeformation A Ψ`: `Ψ` read through the characteristic maps of the cells of `A`.

## Main results

* `TauCeti.cellDeformation_map`: through the characteristic map of a cell of `A`, the deformation
  is `Ψ`.
* `TauCeti.cellDeformation_of_notMem`: points outside the open cells of `A` are fixed.
* `TauCeti.cellDeformation_mem`: the deformation keeps the `n`-skeleton inside itself.
* `TauCeti.continuous_cellDeformation`: the deformation is continuous on `I × skeletonLT C (n + 1)`.
* `TauCeti.exists_homotopicRel_openCell`: a deformation of the closed unit ball fixing the unit
  sphere, read through the characteristic map of one `n`-cell `j`, deforms maps into the
  `n`-skeleton relative to the points not sent into the open cell `j`.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D] {n : ℕ}

/-- The family of maps `Ψ` of the closed unit ball read through the characteristic maps of a set
`A` of `n`-cells, at time `t`: a point of the open cell of some `j ∈ A` moves by `Ψ` read through
the characteristic map of `j`, and every other point is fixed. -/
def cellDeformation (A : Set (cell C n)) (Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)) (q : I × X) : X :=
  open Classical in
  if h : ∃ j ∈ A, q.2 ∈ openCell n j then
    map n h.choose (Ψ (q.1, (map n h.choose).symm q.2))
  else q.2

/-- A point outside the open cells of `A` is fixed. -/
lemma cellDeformation_of_notMem {A : Set (cell C n)} {Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)}
    {t : I} {x : X} (hx : ∀ j ∈ A, x ∉ openCell n j) : cellDeformation A Ψ (t, x) = x := by
  rw [cellDeformation, dite_eq_right fun ⟨j, hj, h⟩ ↦ hx j hj h]

/-- A point of the open cell of `j ∈ A` moves by `Ψ`, read through the characteristic map of
`j`. -/
lemma cellDeformation_of_mem {A : Set (cell C n)} {Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)} {t : I}
    {x : X} {j : cell C n} (hj : j ∈ A) (hx : x ∈ openCell n j) :
    cellDeformation A Ψ (t, x) = map n j (Ψ (t, (map n j).symm x)) := by
  have h : ∃ j ∈ A, x ∈ openCell n j := ⟨j, hj, hx⟩
  -- The open cells are disjoint, so the cell chosen in the definition is `j`.
  obtain rfl : h.choose = j := by
    by_contra hne
    exact (disjoint_openCell_of_ne (by simpa using hne)).notMem_of_mem_left h.choose_spec.2 hx
  rw [cellDeformation, dite_eq_left h]

variable [T2Space X]

/-- The `(n-1)`-skeleton misses every open `n`-cell, and is fixed. -/
lemma cellDeformation_of_mem_skeletonLT {A : Set (cell C n)}
    {Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)} {t : I} {x : X}
    (hx : x ∈ (skeletonLT C (n : ℕ∞) : Set X)) : cellDeformation A Ψ (t, x) = x :=
  cellDeformation_of_notMem fun _ _ ↦ (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left hx

/-- **Through the characteristic map of a cell of `A`, the deformation is `Ψ`**, provided `Ψ`
fixes the unit sphere. -/
lemma cellDeformation_map {A : Set (cell C n)} {Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)}
    (hΨ : ∀ t y, ‖y‖ = 1 → Ψ (t, y) = y) {j : cell C n} (hj : j ∈ A) (t : I)
    {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    cellDeformation A Ψ (t, map n j y) = map n j (Ψ (t, y)) := by
  rcases hy.lt_or_eq with hy | hy
  · have hmem : y ∈ (map n j).source := by rwa [source_eq, mem_ball_zero_iff]
    rw [cellDeformation_of_mem hj ⟨y, mem_ball_zero_iff.2 hy, rfl⟩, (map n j).left_inv hmem]
  · -- A point of the boundary sphere lands in the frontier of the cell, which is fixed.
    rw [hΨ t y hy, cellDeformation_of_mem_skeletonLT
      (cellFrontier_subset_skeletonLT n j ⟨y, mem_sphere_zero_iff_norm.2 hy, rfl⟩)]

/-- The deformation keeps the `n`-skeleton inside itself, provided `Ψ` keeps the closed unit ball
inside itself. -/
lemma cellDeformation_mem {A : Set (cell C n)} {Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)}
    (hΨb : ∀ t y, ‖y‖ ≤ 1 → ‖Ψ (t, y)‖ ≤ 1) (t : I) {x : X}
    (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    cellDeformation A Ψ (t, x) ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  by_cases hxA : ∃ j ∈ A, x ∈ openCell n j
  · obtain ⟨j, hj, hxj⟩ := hxA
    rw [cellDeformation_of_mem hj hxj]
    exact map_mem_skeletonLT_succ j (hΨb _ _ (mem_ball_zero_iff.1 (map_symm_mem_ball n hxj)).le)
  · push Not at hxA
    rwa [cellDeformation_of_notMem hxA]

/-- **The deformation is continuous on `I × skeletonLT C (n + 1)`**, provided `Ψ` fixes the unit
sphere and keeps the closed unit ball inside itself. -/
lemma continuous_cellDeformation (A : Set (cell C n)) {Ψ : C(I × (Fin n → ℝ), Fin n → ℝ)}
    (hΨ : ∀ t y, ‖y‖ = 1 → Ψ (t, y) = y) (hΨb : ∀ t y, ‖y‖ ≤ 1 → ‖Ψ (t, y)‖ ≤ 1) :
    Continuous fun q : I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ↦
      cellDeformation A Ψ (q.1, q.2) := by
  rw [continuous_prod_complex_iff]
  refine ⟨fun m ⟨i, hi⟩ ↦ ?_, ?_⟩
  · have hm : m ≤ n := Nat.lt_succ_iff.1 (by
      simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hi)
    by_cases hiA : ∃ j ∈ A, (⟨m, i⟩ : Σ n, cell C n) = ⟨n, j⟩
    · -- On a cell of `A` the deformation is `Ψ`, read through the characteristic map.
      obtain ⟨j, hj, hij⟩ := hiA
      obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.1 hij
      obtain rfl := eq_of_heq hij
      refine ((continuousOn m i).comp_continuous (Ψ.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
        fun q ↦ mem_closedBall_zero_iff.2 (hΨb _ _ (mem_closedBall_zero_iff.1 q.2.2))).congr
        fun q ↦ ?_
      exact (cellDeformation_map hΨ hj q.1 (mem_closedBall_zero_iff.1 q.2.2)).symm
    · -- Every other cell of the skeleton misses the open cells of `A`, and is fixed.
      push Not at hiA
      refine ((continuousOn m i).comp_continuous (continuous_subtype_val.comp continuous_snd)
        fun q ↦ q.2.2).congr fun q ↦ (cellDeformation_of_notMem fun j hj ↦ ?_).symm
      exact (disjoint_closedCell_openCell_of_ne n hm (hiA j hj)).notMem_of_mem_left
        ⟨q.2, q.2.2, rfl⟩
  · -- The base lies in the `(n-1)`-skeleton, which is fixed.
    exact (continuous_subtype_val.comp continuous_snd).congr fun q ↦
      (cellDeformation_of_mem_skeletonLT ((skeletonLT C n).base_subset q.2.2)).symm

/-- **A deformation of the closed unit ball fixing the unit sphere, read through the
characteristic map of an `n`-cell `j`, deforms maps into the `n`-skeleton relative to the points
not sent into the open cell `j`.** A point `z` sent into the open cell, at `map n j y`, ends at
`map n j (g y)`. -/
lemma exists_homotopicRel_openCell (j : cell C n) {g : C(Fin n → ℝ, Fin n → ℝ)}
    (Ψ : (ContinuousMap.id _).HomotopyRel g (frontier (closedBall 0 1)))
    (hΨb : ∀ t y, ‖y‖ ≤ 1 → ‖Ψ (t, y)‖ ≤ 1) {Z : Type*} [TopologicalSpace Z]
    (f : C(Z, (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))) {S : Set Z}
    (hS : ∀ z ∈ S, (f z : X) ∉ openCell n j) :
    ∃ f' : C(Z, (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)), f.HomotopicRel f' S ∧
      (∀ z, (f z : X) ∈ openCell n j → (f' z : X) = map n j (g ((map n j).symm (f z)))) ∧
      ∀ z, (f z : X) ∉ openCell n j → f' z = f z := by
  have hΨ (t : I) (y : Fin n → ℝ) (hy : ‖y‖ = 1) : Ψ (t, y) = y :=
    Ψ.eq_fst t (frontier_closedBall (0 : Fin n → ℝ) one_ne_zero ▸ mem_sphere_zero_iff_norm.2 hy)
  have hfix {t : I} {x : X} (hx : x ∉ openCell n j) :
      cellDeformation {j} Ψ.toContinuousMap (t, x) = x :=
    cellDeformation_of_notMem fun i hi ↦ by rwa [mem_singleton_iff.1 hi]
  let Q : C(I × Z, (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :=
    ⟨fun q ↦ ⟨cellDeformation {j} Ψ.toContinuousMap (q.1, f q.2),
        cellDeformation_mem hΨb q.1 (f q.2).2⟩,
      ((continuous_cellDeformation {j} hΨ hΨb).comp
        (continuous_fst.prodMk (f.continuous.comp continuous_snd))).subtype_mk _⟩
  have hQ (q : I × Z) : (Q q : X) = cellDeformation {j} Ψ.toContinuousMap (q.1, f q.2) := rfl
  have h0 (z : Z) : Q (0, z) = f z := by
    refine Subtype.ext ?_
    by_cases hz : (f z : X) ∈ openCell n j
    · -- At time `0` the deformation `Ψ` is the identity.
      rw [hQ, cellDeformation_of_mem (mem_singleton j) hz,
        ContinuousMap.HomotopyWith.coe_toContinuousMap, Ψ.apply_zero, ContinuousMap.id_apply,
        map_map_symm n hz]
    · exact hfix hz
  refine ⟨Q.curry 1, ⟨⟨⟨Q, h0, fun _ ↦ rfl⟩, fun t z hz ↦ Subtype.ext ?_⟩⟩, fun z hz ↦ ?_,
    fun z hz ↦ Subtype.ext ?_⟩
  · exact hfix (hS z hz)
  · rw [ContinuousMap.curry_apply, hQ, cellDeformation_of_mem (mem_singleton j) hz,
      ContinuousMap.HomotopyWith.coe_toContinuousMap, Ψ.apply_one]
  · exact hfix hz

end TauCeti
