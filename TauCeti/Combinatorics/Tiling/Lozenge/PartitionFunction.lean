/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Tiling
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Partition functions and Boltzmann measures of lozenge tilings

Let `w : TriEdge → ℝ` be an edge weight. A tiling `M` of a region `R` has the weight
`∏_{e ∈ M} w(e)`, and the partition function `Z_R(w)` of `R` is the sum of the weights of its
tilings. A finite region has finitely many tilings, each a finite set of edges, so these are finite
sums and products; they are written with `finsum` and `finprod` so that `partitionFunction` is
defined for every region. The Boltzmann measure of a finite region is the measure on configurations
`TriEdge → Bool` giving each tiling, read as its indicator configuration, the mass
`ENNReal.ofReal (∏_{e ∈ M} w(e) / Z_R(w))`. When `w` is nonnegative and `Z_R(w)` is positive, this
mass is `∏_{e ∈ M} w(e) / Z_R(w)` and the Boltzmann measure is a probability measure. With unit
weights it is the uniform measure on the tilings of `R`.

The Kasteleyn matrix of `TauCeti.Combinatorics.Tiling.Lozenge.Kasteleyn` computes `Z_R(w)`.

## Main definitions

* `TauCeti.partitionFunction`: the partition function `Z_R(w) = Σ_{M tiling of R} ∏_{e ∈ M} w(e)`.
* `TauCeti.boltzmannMeasure`: the Boltzmann measure of a finite region on `TriEdge → Bool`.

## Main statements

* `TauCeti.finite_setOf_isTiling`: a finite region has finitely many tilings.
* `TauCeti.partitionFunction_pos`: for a positive weight, a finite tileable region has positive
  partition function.
* `TauCeti.partitionFunction_vadd`, `TauCeti.partitionFunction_rot`: translations and the rotation
  `ρ` preserve the partition function, with translated or rotated weights.
* `TauCeti.boltzmannMeasure_singleton`, `TauCeti.boltzmannMeasure_setOf_not_isTiling`: the
  Boltzmann measure gives a tiling the mass `ENNReal.ofReal (∏_{e ∈ M} w(e) / Z_R(w))` and is
  carried by tilings.
* `TauCeti.isProbabilityMeasure_boltzmannMeasure`: for a nonnegative weight with positive partition
  function, it is a probability measure.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 3.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Sections 3.1 and 3.4.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace TauCeti

/-! ### The partition function -/

/-- The partition function `Z_R(w)` of a region `R` for an edge weight `w`: the sum, over the
tilings `M` of `R`, of the weights `∏_{e ∈ M} w(e)`. For a finite region these are finite sums of
finite products (`TauCeti.finite_setOf_isTiling`, `TauCeti.IsTiling.finite`). -/
def partitionFunction (R : Set TriFace) (w : TriEdge → ℝ) : ℝ :=
  ∑ᶠ M ∈ {M | IsTiling R M}, ∏ᶠ e ∈ M, w e

theorem partitionFunction_def (R : Set TriFace) (w : TriEdge → ℝ) :
    partitionFunction R w = ∑ᶠ M ∈ {M | IsTiling R M}, ∏ᶠ e ∈ M, w e :=
  (rfl)

/-- A finite region has finitely many tilings: they are sets of edges of the region. -/
theorem finite_setOf_isTiling (R : Finset TriFace) : {M | IsTiling (R : Set TriFace) M}.Finite :=
  (finite_regionEdges R).finite_subsets.subset fun _ hM => hM.isFreeTiling.subset_regionEdges

/-- The empty region has exactly one tiling, the empty one, of weight `1`. -/
@[simp] theorem partitionFunction_empty (w : TriEdge → ℝ) : partitionFunction ∅ w = 1 := by
  have h : {M : Set TriEdge | IsTiling ∅ M} = {∅} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, isTiling_def, Set.mem_empty_iff_false,
      false_imp_iff, implies_true, and_true, Set.eq_empty_iff_forall_notMem]
    exact ⟨fun h e he => h e he _ e.mem_whiteFace_edges, fun h e he => (h e he).elim⟩
  rw [partitionFunction_def, h, finsum_mem_singleton, finprod_mem_empty]

/-- A region without tilings has partition function `0`. -/
theorem partitionFunction_eq_zero (R : Set TriFace) (w : TriEdge → ℝ)
    (h : ∀ M, ¬IsTiling R M) : partitionFunction R w = 0 := by
  rw [partitionFunction_def, finsum_mem_eq_zero_of_forall_eq_zero]
  exact fun M hM => (h M hM).elim

theorem partitionFunction_nonneg (R : Set TriFace) {w : TriEdge → ℝ} (hw : ∀ e, 0 ≤ w e) :
    0 ≤ partitionFunction R w :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => finprod_nonneg fun _ => finprod_nonneg fun _ =>
    hw _

/-- For a positive weight, a finite tileable region has positive partition function. -/
theorem partitionFunction_pos (R : Finset TriFace) {w : TriEdge → ℝ} (hw : ∀ e, 0 < w e)
    {M : Set TriEdge} (hM : IsTiling (R : Set TriFace) M) : 0 < partitionFunction R w := by
  rw [partitionFunction_def, finsum_mem_eq_finite_toFinset_sum _ (finite_setOf_isTiling R)]
  refine Finset.sum_pos (fun M' _ => ?_) ⟨M, (finite_setOf_isTiling R).mem_toFinset.2 hM⟩
  exact finprod_mem_induction (0 < ·) one_pos (fun _ _ => mul_pos) fun _ _ => hw _

/-! ### Symmetries -/

/-- Transport of the partition function along a permutation `ψ` of the edges mapping the tilings
of `R` exactly onto those of `R'`. -/
private theorem partitionFunction_image (ψ : Equiv.Perm TriEdge) {R R' : Set TriFace}
    (h : ∀ M, IsTiling R' (ψ '' M) ↔ IsTiling R M) (w : TriEdge → ℝ) :
    partitionFunction R' w = partitionFunction R (fun e => w (ψ e)) := by
  refine (finsum_mem_eq_of_bijOn (fun M => ψ '' M) ⟨fun M hM => (h M).2 hM,
    (Set.image_injective.2 ψ.injective).injOn, fun M' hM' => ⟨ψ.symm '' M', ?_, ?_⟩⟩
    fun M _ => (finprod_mem_image ψ.injective.injOn).symm).symm
  · rw [Set.mem_ofPred_eq, ← h, ψ.image_symm_image]
    exact hM'
  · exact ψ.image_symm_image M'

/-- Translating a region and the weight together preserves the partition function. -/
theorem partitionFunction_vadd (u : ℤ × ℤ) (R : Set TriFace) (w : TriEdge → ℝ) :
    partitionFunction (u +ᵥ R) w = partitionFunction R (fun e => w (u +ᵥ e)) :=
  partitionFunction_image (AddAction.toPerm u) (fun _ => isTiling_vadd_iff u) w

/-- Rotating a region by `ρ` and the weight together preserves the partition function. -/
theorem partitionFunction_rot (R : Set TriFace) (w : TriEdge → ℝ) :
    partitionFunction (TriFace.rot '' R) w = partitionFunction R (fun e => w (TriEdge.rot e)) :=
  partitionFunction_image TriEdge.rot (fun _ => isTiling_rot_iff) w

/-! ### The Boltzmann measure -/

/-- The configurations `ω : TriEdge → Bool` whose edge sets `{e | ω e = true}` tile a finite
region form a finite set. -/
theorem finite_setOf_isTiling_setOf_eq_true (R : Finset TriFace) :
    {ω : TriEdge → Bool | IsTiling (R : Set TriFace) {e | ω e = true}}.Finite :=
  (finite_setOf_isTiling R).preimage fun ω _ ω' _ h => funext fun e => by
    simpa using Set.ext_iff.1 h e

/-- The Boltzmann measure of a finite region `R` for an edge weight `w`: the measure on
configurations giving the indicator configuration of each tiling `M` of `R` the mass
`ENNReal.ofReal (∏_{e ∈ M} w(e) / Z_R(w))`, which truncates a negative ratio to `0`. When `w` is
nonnegative and `Z_R(w) > 0`, this mass is `∏_{e ∈ M} w(e) / Z_R(w)` and the measure is a
probability measure (`TauCeti.isProbabilityMeasure_boltzmannMeasure`); for `w ≡ 1` it is the uniform
measure on the tilings of `R`. -/
def boltzmannMeasure (R : Finset TriFace) (w : TriEdge → ℝ) : Measure (TriEdge → Bool) :=
  ∑ ω ∈ (finite_setOf_isTiling_setOf_eq_true R).toFinset,
    ENNReal.ofReal ((∏ᶠ e ∈ {e | ω e = true}, w e) / partitionFunction R w) • Measure.dirac ω

theorem boltzmannMeasure_def (R : Finset TriFace) (w : TriEdge → ℝ) :
    boltzmannMeasure R w = ∑ ω ∈ (finite_setOf_isTiling_setOf_eq_true R).toFinset,
      ENNReal.ofReal ((∏ᶠ e ∈ {e | ω e = true}, w e) / partitionFunction R w) •
        Measure.dirac ω :=
  (rfl)

/-- The mass of a set `A` of configurations under the Boltzmann measure is the sum, over the
tilings `M` in `A`, of `ENNReal.ofReal (∏_{e ∈ M} w(e) / Z_R(w))`. -/
theorem boltzmannMeasure_apply (R : Finset TriFace) (w : TriEdge → ℝ) (A : Set (TriEdge → Bool)) :
    boltzmannMeasure R w A = ∑ ω ∈ (finite_setOf_isTiling_setOf_eq_true R).toFinset,
      A.indicator (fun ω =>
        ENNReal.ofReal ((∏ᶠ e ∈ {e | ω e = true}, w e) / partitionFunction R w)) ω := by
  rw [boltzmannMeasure_def, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hω : ω ∈ A <;> simp [hω]

/-- The Boltzmann measure gives a tiling `M` of `R`, read as the configuration `ω` with
`{e | ω e = true} = M`, the mass `ENNReal.ofReal (∏_{e ∈ M} w(e) / Z_R(w))`. -/
theorem boltzmannMeasure_singleton (R : Finset TriFace) (w : TriEdge → ℝ) {ω : TriEdge → Bool}
    (hω : IsTiling (R : Set TriFace) {e | ω e = true}) :
    boltzmannMeasure R w {ω} =
      ENNReal.ofReal ((∏ᶠ e ∈ {e | ω e = true}, w e) / partitionFunction R w) := by
  rw [boltzmannMeasure_apply, Finset.sum_eq_single_of_mem ω
    ((finite_setOf_isTiling_setOf_eq_true R).mem_toFinset.2 hω)
    fun ω' _ hne => Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hne) _]
  exact Set.indicator_of_mem rfl _

/-- The Boltzmann measure is carried by the tilings of `R`. -/
theorem boltzmannMeasure_setOf_not_isTiling (R : Finset TriFace) (w : TriEdge → ℝ) :
    boltzmannMeasure R w {ω | ¬IsTiling (R : Set TriFace) {e | ω e = true}} = 0 := by
  rw [boltzmannMeasure_apply]
  refine Finset.sum_eq_zero fun ω hω => Set.indicator_of_notMem ?_ _
  exact not_not.2 ((finite_setOf_isTiling_setOf_eq_true R).mem_toFinset.1 hω)

/-- The partition function of a finite region, as a sum over the configurations of its
tilings. -/
private theorem partitionFunction_eq_sum_setOf_eq_true (R : Finset TriFace) (w : TriEdge → ℝ) :
    partitionFunction R w = ∑ ω ∈ (finite_setOf_isTiling_setOf_eq_true R).toFinset,
      ∏ᶠ e ∈ {e | ω e = true}, w e := by
  classical
  rw [← finsum_mem_eq_finite_toFinset_sum, partitionFunction_def]
  refine (finsum_mem_eq_of_bijOn (fun ω : TriEdge → Bool => {e | ω e = true})
    ⟨fun ω hω => hω, fun ω _ ω' _ h => funext fun e => by simpa using Set.ext_iff.1 h e,
      fun M hM => ⟨fun e => decide (e ∈ M), ?_, ?_⟩⟩ fun _ _ => rfl).symm
  · simpa only [Set.mem_ofPred_eq, decide_eq_true_eq, Set.ofPred_mem_eq] using hM
  · simp only [decide_eq_true_eq, Set.ofPred_mem_eq]

/-- For a nonnegative weight with positive partition function, the Boltzmann measure is a
probability measure. -/
theorem isProbabilityMeasure_boltzmannMeasure (R : Finset TriFace) {w : TriEdge → ℝ}
    (hw : ∀ e, 0 ≤ w e) (hZ : 0 < partitionFunction R w) :
    IsProbabilityMeasure (boltzmannMeasure R w) := by
  refine ⟨?_⟩
  simp only [boltzmannMeasure_apply, Set.indicator_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ =>
      div_nonneg (finprod_nonneg fun _ => finprod_nonneg fun _ => hw _) hZ.le,
    ← Finset.sum_div, ← partitionFunction_eq_sum_setOf_eq_true, div_self hZ.ne',
    ENNReal.ofReal_one]

end TauCeti
