/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Energy
public import TauCeti.MeasureTheory.Constructions.UnitInterval.CellPartition
import Mathlib.Tactic.Ring

/-!
# Step graphons induced by finite vertex partitions

Given a partition `P` of `Fin m` with `0 < m` and a symmetric `[0, 1]`-valued matrix `val` indexed
by `P.parts`, `stepGraphonOfFinpartition P val hsymm` is the step graphon on `(I, volume)` over the
lifted cell partition `P.cellPartition`. On the product of the cells of `A` and `B`, it takes the
prescribed value `val A B`.

Because `P.cellPartition` has non-null parts in bijection with `P.parts`, finite-partition step
graphons match general step graphons on `P.cellPartition` in both directions:
* `stepGraphonOfFinpartition_def` and `stepGraphon_cellPartition_eq_stepGraphonOfFinpartition`
  identify `stepGraphonOfFinpartition P` with `stepGraphon` on `P.cellPartition`;
* `stepGraphonOfFinpartition_eq_comap_ofMatrix` identifies it with the pullback along
  `cellFin m : I → Fin m` of the corresponding discrete weighted graph on `Fin m`;
* `stepGraphonAvg_stepGraphonOfFinpartition` and
  `blockAverage_cellPartition_stepGraphonOfFinpartition` show that it is its own block average over
  `P.cellPartition` and that block averaging recovers `val`;
* `rectIntegral_stepGraphonOfFinpartition_preimage` and `l2sq_stepGraphonOfFinpartition` express its
  cell-preimage rectangle integrals and squared `L²` norm as finite sums over `P.parts`.

## Main definitions

* `TauCeti.DenseGraphLimits.stepGraphonOfFinpartition`: the step graphon on `(I, volume)` associated
  to a partition of `Fin m` and a symmetric `[0, 1]`-valued matrix on its parts.

## Main results

* `TauCeti.DenseGraphLimits.stepGraphonOfFinpartition_apply` and
  `TauCeti.DenseGraphLimits.stepGraphonOfFinpartition_apply_part`: pointwise evaluation on cells.
* `TauCeti.DenseGraphLimits.stepGraphonOfFinpartition_inj`: injectivity in the block matrix.
* `TauCeti.DenseGraphLimits.stepGraphon_cellPartition_eq_stepGraphonOfFinpartition`: every step
  graphon on `P.cellPartition` is a `stepGraphonOfFinpartition P`.
* `TauCeti.DenseGraphLimits.stepGraphonOfFinpartition_eq_comap_ofMatrix`: pullback form from the
  uniform probability space on `Fin m`.
* `TauCeti.DenseGraphLimits.stepGraphonAvg_stepGraphonOfFinpartition` and
  `TauCeti.DenseGraphLimits.stepGraphonAvg_cellPartition_eq_stepGraphonOfFinpartition`:
  compatibility with `stepGraphonAvg` and `blockAverage`.
* `TauCeti.DenseGraphLimits.rectIntegral_stepGraphonOfFinpartition_preimage` and
  `TauCeti.DenseGraphLimits.l2sq_stepGraphonOfFinpartition`: rectangle integrals over cell preimages
  and squared `L²` norm.
-/

public section

noncomputable section

open Finset MeasureTheory ProbabilityTheory TauCeti.unitInterval
open scoped unitInterval

namespace TauCeti.DenseGraphLimits

variable {m : ℕ} [NeZero m]

/-- The step graphon on `(I, volume)` associated to a partition `P` of `Fin m` with `0 < m` and a
symmetric `[0, 1]`-valued matrix `val` indexed by `P.parts`. On the cells of `A` and `B`, it takes
the value `val A B`. -/
def stepGraphonOfFinpartition (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A) :
    Graphon I (volume : Measure I) :=
  stepGraphon (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
    (fun p q => val (P.partsCellPartitionEquiv.symm p) (P.partsCellPartitionEquiv.symm q))
    (fun _ _ => hsymm _ _)

/-- Unfolding lemma relating `stepGraphonOfFinpartition` to `stepGraphon` on `P.cellPartition`. -/
theorem stepGraphonOfFinpartition_def (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A) :
    stepGraphonOfFinpartition P val hsymm =
      stepGraphon (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
        (fun p q => val (P.partsCellPartitionEquiv.symm p) (P.partsCellPartitionEquiv.symm q))
        (fun _ _ => hsymm _ _) := by
  rw [stepGraphonOfFinpartition]

/-- On the cells of two parts `A` and `B` of `P`, `stepGraphonOfFinpartition` takes the value
`val A B`. -/
theorem stepGraphonOfFinpartition_apply (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A)
    {A B : P.parts} {x y : I} (hx : cellFin m x ∈ A.1) (hy : cellFin m y ∈ B.1) :
    stepGraphonOfFinpartition P val hsymm x y = (val A B : ℝ) := by
  have hx' : x ∈ (P.partsCellPartitionEquiv A : Set I) := by simpa using hx
  have hy' : y ∈ (P.partsCellPartitionEquiv B : Set I) := by simpa using hy
  rw [stepGraphonOfFinpartition_def, stepGraphon_apply _ _ _ _ hx' hy',
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- At an arbitrary pair `(x, y)`, `stepGraphonOfFinpartition` evaluates `val` on the parts of `P`
containing the cells of `x` and `y`. -/
@[simp]
theorem stepGraphonOfFinpartition_apply_part (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A) (x y : I) :
    stepGraphonOfFinpartition P val hsymm x y =
      (val ⟨P.part (cellFin m x), P.part_mem.2 (mem_univ _)⟩
        ⟨P.part (cellFin m y), P.part_mem.2 (mem_univ _)⟩ : ℝ) :=
  stepGraphonOfFinpartition_apply P val hsymm (P.mem_part (mem_univ _)) (P.mem_part (mem_univ _))

/-- Two finite-partition step graphons on a fixed partition `P` are equal if and only if their block
matrices agree. -/
@[simp]
theorem stepGraphonOfFinpartition_inj (P : Finpartition (univ : Finset (Fin m)))
    (val val' : P.parts → P.parts → Set.Icc (0 : ℝ) 1)
    (hsymm : ∀ A B, val A B = val B A) (hsymm' : ∀ A B, val' A B = val' B A) :
    stepGraphonOfFinpartition P val hsymm = stepGraphonOfFinpartition P val' hsymm' ↔
      val = val' := by
  rw [stepGraphonOfFinpartition_def, stepGraphonOfFinpartition_def, stepGraphon_inj]
  constructor
  · intro h
    funext A B
    simpa only [Equiv.symm_apply_apply] using
      congr_fun₂ h (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B)
  · rintro rfl
    rfl

/-- A finite-partition step graphon with constant block matrix is the constant graphon. -/
@[simp]
theorem stepGraphonOfFinpartition_const (P : Finpartition (univ : Finset (Fin m)))
    (c : Set.Icc (0 : ℝ) 1) :
    stepGraphonOfFinpartition P (fun _ _ => c) (fun _ _ => rfl) = Graphon.const volume c := by
  rw [stepGraphonOfFinpartition_def, stepGraphon_const]

/-- Every step graphon on `P.cellPartition` is a `stepGraphonOfFinpartition` on `P`, obtained by
reading its block matrix along `P.partsCellPartitionEquiv`. -/
theorem stepGraphon_cellPartition_eq_stepGraphonOfFinpartition
    (P : Finpartition (univ : Finset (Fin m)))
    (hP : ∀ p ∈ P.cellPartition.parts, MeasurableSet p)
    (val : P.cellPartition.parts → P.cellPartition.parts → Set.Icc (0 : ℝ) 1)
    (hsymm : ∀ p q, val p q = val q p) :
    stepGraphon (μ := volume) P.cellPartition hP val hsymm =
      stepGraphonOfFinpartition P
        (fun A B => val (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B))
        (fun _ _ => hsymm _ _) := by
  ext x y
  have hx := P.cellPartition.indexedPartition.mem_index x
  have hy := P.cellPartition.indexedPartition.mem_index y
  rw [stepGraphon_apply P.cellPartition hP val hsymm hx hy, stepGraphonOfFinpartition_def,
    stepGraphon_apply _ _ _ _ hx hy, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Pullback compatibility.** `stepGraphonOfFinpartition` is the pullback along `cellFin m` of the
weighted graph on `(Fin m, uniformOn Set.univ)` assigning `val (P.part i) (P.part j)` to `(i, j)`.
-/
theorem stepGraphonOfFinpartition_eq_comap_ofMatrix (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A) :
    stepGraphonOfFinpartition P val hsymm =
      (Graphon.ofMatrix (uniformOn Set.univ)
        (fun i j => val ⟨P.part i, P.part_mem.2 (mem_univ i)⟩
          ⟨P.part j, P.part_mem.2 (mem_univ j)⟩)
        (fun _ _ => hsymm _ _)).comap (cellFin m) measurable_cellFin volume := by
  ext x y
  simp

/-- **A finite-partition step graphon is its own block average** over `P.cellPartition`, since every
part of `P.cellPartition` has positive volume. -/
@[simp]
theorem stepGraphonAvg_stepGraphonOfFinpartition (P : Finpartition (univ : Finset (Fin m)))
    (hP : ∀ p ∈ P.cellPartition.parts, MeasurableSet p)
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A) :
    stepGraphonAvg (μ := volume) P.cellPartition hP (stepGraphonOfFinpartition P val hsymm) =
      stepGraphonOfFinpartition P val hsymm := by
  obtain rfl : hP = P.measurableSet_of_mem_cellPartition := Subsingleton.elim _ _
  rw [stepGraphonOfFinpartition_def]
  exact stepGraphonAvg_stepGraphon _ _ _ _ fun _ hp => P.volume_ne_zero_of_mem_cellPartition hp

/-- Block averaging `stepGraphonOfFinpartition P val hsymm` over the lifted parts corresponding to
`A` and `B` recovers `val A B`. -/
@[simp]
theorem blockAverage_cellPartition_stepGraphonOfFinpartition
    (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A)
    (A B : P.parts) :
    blockAverage P.cellPartition (stepGraphonOfFinpartition P val hsymm)
        (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B) = val A B := by
  have h := stepGraphonAvg_stepGraphonOfFinpartition P P.measurableSet_of_mem_cellPartition
    val hsymm
  conv_rhs at h => rw [stepGraphonOfFinpartition_def]
  rw [stepGraphonAvg_def, stepGraphon_inj] at h
  simpa only [Equiv.symm_apply_apply] using
    congr_fun₂ h (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B)

/-- For any graphon `W` on `(I, volume)`, its block-average step graphon over `P.cellPartition` is
the `stepGraphonOfFinpartition` of its rectangle averages pulled back to `P.parts`. -/
theorem stepGraphonAvg_cellPartition_eq_stepGraphonOfFinpartition
    (P : Finpartition (univ : Finset (Fin m)))
    (hP : ∀ p ∈ P.cellPartition.parts, MeasurableSet p) (W : Graphon I (volume : Measure I)) :
    stepGraphonAvg (μ := volume) P.cellPartition hP W =
      stepGraphonOfFinpartition P
        (fun A B => blockAverage P.cellPartition W
          (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B))
        (fun _ _ => blockAverage_comm _ _ _ _) := by
  rw [stepGraphonAvg_def, stepGraphon_cellPartition_eq_stepGraphonOfFinpartition]

omit [NeZero m] in
/-- Grouping a sum over `X ⊆ Fin m` by the subtype of parts of `P`. -/
private theorem sum_apply_part_subtype (P : Finpartition (univ : Finset (Fin m)))
    (X : Finset (Fin m)) (g : P.parts → ℝ) :
    ∑ i ∈ X, g ⟨P.part i, P.part_mem.2 (mem_univ i)⟩ =
      ∑ A : P.parts, (#(X ∩ A.1) : ℝ) * g A := by
  classical
  rw [← Finset.sum_fiberwise X (fun i => (⟨P.part i, P.part_mem.2 (mem_univ i)⟩ : P.parts))]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
    nsmul_eq_mul]
  congr 3
  ext i
  simp [Subtype.ext_iff, P.part_eq_iff_mem A.2]

/-- **Rectangle integral over cell preimages.** Over the cells of two vertex sets `S` and `T`,
`stepGraphonOfFinpartition` integrates to the trace-weighted block sum divided by `m²`. -/
theorem rectIntegral_stepGraphonOfFinpartition_preimage (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A)
    (S T : Finset (Fin m)) :
    (stepGraphonOfFinpartition P val hsymm).toSymmKernel.rectIntegral volume
        (cellFin m ⁻¹' (S : Set (Fin m))) (cellFin m ⁻¹' (T : Set (Fin m))) =
      (∑ A : P.parts, ∑ B : P.parts, (val A B : ℝ) * #(S ∩ A.1) * #(T ∩ B.1)) / (m : ℝ) ^ 2 := by
  rw [stepGraphonOfFinpartition_eq_comap_ofMatrix, Graphon.toSymmKernel_comap,
    SymmKernel.rectIntegral_comap_preimage _ measurePreserving_cellFin _
      S.measurableSet T.measurableSet,
    SymmKernel.rectIntegral_uniformOn_univ, Fintype.card_fin]
  congr 1
  simp only [Graphon.coe_toSymmKernel, Graphon.ofMatrix_apply]
  have hT (A : P.parts) :
      ∑ j ∈ T, (val A ⟨P.part j, P.part_mem.2 (mem_univ j)⟩ : ℝ) =
        ∑ B : P.parts, (#(T ∩ B.1) : ℝ) * val A B :=
    sum_apply_part_subtype P T fun B => (val A B : ℝ)
  simp_rw [sum_congr rfl fun i _ => hT ⟨P.part i, P.part_mem.2 (mem_univ i)⟩]
  rw [sum_apply_part_subtype P S fun A => ∑ B : P.parts, (#(T ∩ B.1) : ℝ) * val A B]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun B _ => by ring

/-- **Squared `L²` norm of `stepGraphonOfFinpartition`.** Each pair of parts `(A, B)` contributes
`(|A||B| / m²) * (val A B)²`. -/
theorem l2sq_stepGraphonOfFinpartition (P : Finpartition (univ : Finset (Fin m)))
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ A B, val A B = val B A) :
    l2sq volume (stepGraphonOfFinpartition P val hsymm).toSymmKernel =
      ∑ A : P.parts, ∑ B : P.parts, (#A.1 * #B.1 / (m : ℝ) ^ 2) * (val A B : ℝ) ^ 2 := by
  let W := stepGraphonOfFinpartition P val hsymm
  have havg := stepGraphonAvg_stepGraphonOfFinpartition P P.measurableSet_of_mem_cellPartition
    val hsymm
  calc l2sq volume W.toSymmKernel
      = graphonPartitionEnergy volume P.cellPartition P.measurableSet_of_mem_cellPartition W := by
        rw [graphonPartitionEnergy_eq, havg]
    _ = ∑ pq : P.cellPartition.parts × P.cellPartition.parts,
          W.toSymmKernel.rectIntegral volume (pq.1 : Set I) (pq.2 : Set I) *
            (blockAverage P.cellPartition W pq.1 pq.2 : ℝ) := by
        simp_rw [graphonPartitionEnergy_eq_sum, coe_blockAverage]
    _ = ∑ A : P.parts, ∑ B : P.parts,
          W.toSymmKernel.rectIntegral volume
              (P.partsCellPartitionEquiv A : Set I) (P.partsCellPartitionEquiv B : Set I) *
            (blockAverage P.cellPartition W
              (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B) : ℝ) := by
        rw [Fintype.sum_prod_type, ← P.partsCellPartitionEquiv.sum_comp]
        exact Finset.sum_congr rfl fun A _ => (P.partsCellPartitionEquiv.sum_comp _).symm
    _ = ∑ A : P.parts, ∑ B : P.parts, (#A.1 * #B.1 / (m : ℝ) ^ 2) * (val A B : ℝ) ^ 2 := by
        have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
        have hvolA : (#A.1 : ℝ) / m ≠ 0 :=
          div_ne_zero (Nat.cast_ne_zero.2 (P.nonempty_of_mem_parts A.2).card_pos.ne') hm
        have hvolB : (#B.1 : ℝ) / m ≠ 0 :=
          div_ne_zero (Nat.cast_ne_zero.2 (P.nonempty_of_mem_parts B.2).card_pos.ne') hm
        have hrect : W.toSymmKernel.rectIntegral volume
            (P.partsCellPartitionEquiv A : Set I) (P.partsCellPartitionEquiv B : Set I) =
            (#A.1 / m) * (#B.1 / m) * (val A B : ℝ) := by
          have h := coe_blockAverage_eq_inv_mul_rectIntegral P.cellPartition W
            (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B)
          rw [blockAverage_cellPartition_stepGraphonOfFinpartition P val hsymm A B,
            P.volume_real_partsCellPartitionEquiv, P.volume_real_partsCellPartitionEquiv] at h
          exact ((eq_inv_mul_iff_mul_eq₀ (mul_ne_zero hvolA hvolB)).1 h).symm
        rw [hrect, blockAverage_cellPartition_stepGraphonOfFinpartition P val hsymm A B]
        ring

end TauCeti.DenseGraphLimits
