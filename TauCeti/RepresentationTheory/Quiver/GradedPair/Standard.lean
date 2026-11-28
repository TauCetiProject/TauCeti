/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.GradedPair.Basic
public import TauCeti.RepresentationTheory.Quiver.Multisegment.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Standard interval pairs of a multisegment

For a multisegment `m`, the standard graded space `m.standardSpace` has one basis vector for
every *valid label* `(i, a) : m.StandardIndex`: an occurrence label `i : Fin m.card` together
with an integer degree `a` in the interval `m.occurrenceInterval i`. The basis vector of `(i, a)`
lies in degree `a`. Repeated intervals of `m` have different occurrence labels and hence
different basis vectors.

The standard raising operator moves each basis vector one step up inside its interval block and
kills the last vector of the block; the standard lowering operator moves one step down and kills
the first vector. Together with the grading these give the standard pairs
`m.standardPair StepDirection.up` and `m.standardPair StepDirection.down`, the direct sums of the
interval blocks of `m`. They are the explicit models in which commuting operators of opposite
degree are written in block coordinates.

To state the formulas uniformly, `m.standardVector i a` is the basis vector of `(i, a)` when `a`
lies in the `i`-th interval and `0` otherwise.

## Main definitions

* `TauCeti.Multisegment.standardSpace`: the graded coordinate space spanned by these labels.
* `TauCeti.Multisegment.standardBasis`: its basis indexed by the valid labels.
* `TauCeti.Multisegment.standardVector`: the basis vector of a label, or `0` for an invalid one.
* `TauCeti.Multisegment.standardGradeBasis`: the basis of the degree-`a` piece indexed by the
  occurrences containing `a`.
* `TauCeti.Multisegment.standardPair`: the standard raising or lowering pair of `m`.

## Main results

* `TauCeti.Multisegment.n_standardSpace`: the total dimension is `totalLength m`.
* `TauCeti.Multisegment.finrank_grade_standardSpace`: the degree-`a` dimension is
  `degreeDimension m a`.
* `TauCeti.Multisegment.grade_standardSpace`: the degree-`a` piece is spanned by the degree-`a`
  standard vectors.
* `TauCeti.Multisegment.standardVector_eq_zero_iff`: a standard vector vanishes exactly when its
  degree lies outside its interval.
* `TauCeti.Multisegment.standardVector_inj`: distinct valid labels give distinct vectors.
* `TauCeti.Multisegment.mem_grade_standardSpace_iff`: grade membership in the coordinates of
  `standardBasis m`.
* `TauCeti.Multisegment.standardPair_operator_standardVector`: on a valid label the operator in
  direction `d` sends the vector of degree `a` to that of degree `a + d.step`.
* `TauCeti.Multisegment.standardPair_operator_pow_standardVector`: its `k`-th power moves `k`
  steps, giving zero once the block is left.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1.
* C. Mœglin, J.-L. Waldspurger, *Sur l'involution de Zelevinski*, J. reine angew. Math. 372
  (1986), 136–177, §II.1.
-/

public section

open Module

namespace TauCeti

namespace Multisegment

variable (m : Multisegment)

/-! ### The standard space -/

/-- The standard graded space of `m`: one coordinate for each valid label `(i, a)`, placed in
degree `a`. -/
noncomputable def standardSpace : GradedCoordSpace where
  n := Fintype.card (StandardIndex m)
  degree k := ((Fintype.equivFin (StandardIndex m)).symm k).2

/-- The enumeration of the valid labels of `m` by the coordinates of `m.standardSpace`. -/
noncomputable def standardIndexEquiv : StandardIndex m ≃ Fin (standardSpace m).n :=
  Fintype.equivFin (StandardIndex m)

/-- The total dimension of the standard space is the total length of `m`. -/
@[simp]
theorem n_standardSpace : (standardSpace m).n = totalLength m :=
  card_standardIndex m

/-- The coordinate of a valid label has the label's degree. -/
@[simp]
theorem degree_standardSpace_standardIndexEquiv (x : StandardIndex m) :
    (standardSpace m).degree (standardIndexEquiv m x) = x.2 := by
  simp only [standardSpace, standardIndexEquiv]
  exact congrArg (fun y : StandardIndex m ↦ (y.2 : ℤ)) ((Fintype.equivFin _).symm_apply_apply x)

/-- The basis of the standard space indexed by the valid labels of `m`. -/
noncomputable def standardBasis : Basis (StandardIndex m) ℂ (standardSpace m).Carrier :=
  (Pi.basisFun ℂ (Fin (standardSpace m).n)).reindex (standardIndexEquiv m).symm

/-- The basis vector of a valid label is the coordinate vector of its coordinate. -/
theorem standardBasis_apply (x : StandardIndex m) :
    standardBasis m x = Pi.single (standardIndexEquiv m x) 1 := by
  simp [standardBasis]

/-- The coefficient of a vector at a valid label in `standardBasis m` is its coordinate at the
label's coordinate. -/
@[simp]
theorem standardBasis_repr_apply (v : (standardSpace m).Carrier) (x : StandardIndex m) :
    (standardBasis m).repr v x = v (standardIndexEquiv m x) := by
  simp [standardBasis]

/-- The basis vector of a valid label lies in the grade of the label's degree. -/
@[simp]
theorem standardBasis_mem_grade (x : StandardIndex m) :
    standardBasis m x ∈ (standardSpace m).grade x.2 := by
  rw [standardBasis_apply, ← degree_standardSpace_standardIndexEquiv]
  exact (standardSpace m).single_mem_grade _ 1

/-! ### Standard vectors -/

open Classical in
/-- The standard vector of the label `(i, a)`: the basis vector of `(i, a)` when `a` lies in the
`i`-th interval of `m`, and `0` otherwise. -/
noncomputable def standardVector (i : Fin m.card) (a : ℤ) : (standardSpace m).Carrier :=
  if h : a ∈ occurrenceInterval m i then
    standardBasis m (StandardIndex.mk i a h)
  else 0

variable {m}

/-- On a valid label the standard vector is the corresponding basis vector. -/
theorem standardVector_of_mem {i : Fin m.card} {a : ℤ} (h : a ∈ occurrenceInterval m i) :
    standardVector m i a = standardBasis m (StandardIndex.mk i a h) := by
  simp [standardVector, h]

/-- On an invalid label the standard vector is zero. -/
@[simp]
theorem standardVector_of_notMem {i : Fin m.card} {a : ℤ} (h : a ∉ occurrenceInterval m i) :
    standardVector m i a = 0 := by
  simp [standardVector, h]

/-- Each basis vector of the standard space is a standard vector. -/
theorem standardBasis_eq_standardVector (x : StandardIndex m) :
    standardBasis m x = standardVector m x.1 x.2 := by
  rw [standardVector_of_mem x.mem_occurrenceInterval, StandardIndex.mk_fst_snd]

/-- A standard vector vanishes exactly when its degree lies outside its interval. -/
@[simp]
theorem standardVector_eq_zero_iff {i : Fin m.card} {a : ℤ} :
    standardVector m i a = 0 ↔ a ∉ occurrenceInterval m i := by
  refine ⟨fun h0 h ↦ ?_, standardVector_of_notMem⟩
  rw [standardVector_of_mem h] at h0
  exact (standardBasis m).ne_zero _ h0

/-- A standard vector lies in the grade of its degree, also when it is zero. -/
@[simp]
theorem standardVector_mem_grade (i : Fin m.card) (a : ℤ) :
    standardVector m i a ∈ (standardSpace m).grade a := by
  by_cases h : a ∈ occurrenceInterval m i
  · rw [standardVector_of_mem h]
    simpa only [StandardIndex.coe_snd_mk] using standardBasis_mem_grade m (StandardIndex.mk i a h)
  · rw [standardVector_of_notMem h]
    exact zero_mem _

/-- Distinct labels give distinct standard vectors, provided one of them is valid. -/
theorem standardVector_inj {i j : Fin m.card} {a b : ℤ} (ha : a ∈ occurrenceInterval m i) :
    standardVector m i a = standardVector m j b ↔ i = j ∧ a = b := by
  refine ⟨fun h ↦ ?_, fun ⟨hi, hab⟩ ↦ hi ▸ hab ▸ rfl⟩
  -- The left side is nonzero, so the label `(j, b)` is valid as well.
  have hb : b ∈ occurrenceInterval m j := by
    by_contra hb
    rw [standardVector_of_notMem hb, standardVector_eq_zero_iff] at h
    exact h ha
  rw [standardVector_of_mem ha, standardVector_of_mem hb] at h
  simpa only [Sigma.subtype_ext_iff, StandardIndex.fst_mk, StandardIndex.coe_snd_mk] using
    (standardBasis m).injective h

/-- The standard vectors of the valid labels are linearly independent. -/
theorem linearIndependent_standardVector :
    LinearIndependent ℂ fun x : StandardIndex m ↦ standardVector m x.1 x.2 := by
  convert (standardBasis m).linearIndependent with x
  exact (standardBasis_eq_standardVector x).symm

/-- A vector lies in the degree-`a` piece of the standard space exactly when its coordinates in
`standardBasis m` vanish at every label of degree different from `a`. -/
theorem mem_grade_standardSpace_iff {a : ℤ} {v : (standardSpace m).Carrier} :
    v ∈ (standardSpace m).grade a ↔
      ∀ x : StandardIndex m, (x.2 : ℤ) ≠ a → (standardBasis m).repr v x = 0 := by
  rw [GradedCoordSpace.mem_grade_iff, ← (standardIndexEquiv m).forall_congr_right]
  simp only [degree_standardSpace_standardIndexEquiv, standardBasis_repr_apply]

variable (m) in
/-- The degree-`a` piece of the standard space is spanned by the standard vectors of degree `a`.
-/
theorem grade_standardSpace (a : ℤ) :
    (standardSpace m).grade a =
      Submodule.span ℂ (Set.range fun i : Fin m.card ↦ standardVector m i a) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [GradedCoordSpace.grade_eq_span, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨x, rfl⟩ := (standardIndexEquiv m).surjective k
    rw [Set.mem_ofPred_eq, degree_standardSpace_standardIndexEquiv] at hk
    refine Submodule.subset_span ⟨x.1, ?_⟩
    dsimp only
    rw [← hk, ← standardBasis_eq_standardVector]
    simp only [standardBasis_apply, Pi.basisFun_apply]
  · rintro _ ⟨i, rfl⟩
    exact standardVector_mem_grade i a

/-- The degree-`a` piece of the standard space is spanned by the standard vectors of the
occurrences containing `a`. -/
private theorem grade_standardSpace_eq_span_mem (m : Multisegment) (a : ℤ) :
    (standardSpace m).grade a = Submodule.span ℂ (Set.range
      fun i : {i : Fin m.card // a ∈ occurrenceInterval m i} ↦ standardVector m i a) := by
  rw [grade_standardSpace]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨i, rfl⟩
    by_cases h : a ∈ occurrenceInterval m i
    · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
    · simp [standardVector_of_notMem h]
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩

/-- The standard vectors of the occurrences containing `a` are linearly independent. -/
private theorem linearIndependent_standardVector_mem (m : Multisegment) (a : ℤ) :
    LinearIndependent ℂ
      fun i : {i : Fin m.card // a ∈ occurrenceInterval m i} ↦ standardVector m i a := by
  have hinj : Function.Injective fun i : {i : Fin m.card // a ∈ occurrenceInterval m i} ↦
      StandardIndex.mk i.val a i.property :=
    fun i j h ↦ Subtype.ext (by
      simpa only [Sigma.subtype_ext_iff, StandardIndex.fst_mk, StandardIndex.coe_snd_mk,
        and_true] using h)
  convert linearIndependent_standardVector.comp _ hinj with i
  simp

variable (m) in
/-- The basis of the degree-`a` piece of the standard space given by the standard vectors of the
occurrences of `m` containing `a`. -/
noncomputable def standardGradeBasis (a : ℤ) :
    Basis {i : Fin m.card // a ∈ occurrenceInterval m i} ℂ ((standardSpace m).grade a) :=
  (Basis.span (linearIndependent_standardVector_mem m a)).map
    (LinearEquiv.ofEq _ _ (grade_standardSpace_eq_span_mem m a).symm)

/-- The basis vector of an occurrence `i` containing `a` in `standardGradeBasis m a` is the
standard vector of `(i, a)`. -/
@[simp]
theorem coe_standardGradeBasis_apply (a : ℤ)
    (i : {i : Fin m.card // a ∈ occurrenceInterval m i}) :
    (standardGradeBasis m a i : (standardSpace m).Carrier) = standardVector m i a := by
  simp [standardGradeBasis]

variable (m) in
/-- The degree-`a` dimension of the standard space is the number of occurrences of `m` containing
`a`. -/
@[simp]
theorem finrank_grade_standardSpace (a : ℤ) :
    finrank ℂ ((standardSpace m).grade a) = degreeDimension m a := by
  rw [finrank_eq_card_basis (standardGradeBasis m a), Fintype.card_subtype,
    card_filter_mem_occurrenceInterval]

/-! ### The standard pairs -/

/-- The linear map sending the basis vector of `(i, a)` to the standard vector of
`(i, a + d.step)`. -/
private noncomputable def standardOperator (m : Multisegment) (d : StepDirection) :
    Module.End ℂ (standardSpace m).Carrier :=
  (standardBasis m).constr ℂ fun x ↦ standardVector m x.1 (x.2 + d.step)

private theorem standardOperator_standardBasis (m : Multisegment) (d : StepDirection)
    (x : StandardIndex m) :
    standardOperator m d (standardBasis m x) = standardVector m x.1 (x.2 + d.step) :=
  (standardBasis m).constr_basis ℂ _ x

private theorem isHomogeneous_standardOperator (m : Multisegment) (d : StepDirection) :
    LinearMap.IsHomogeneous (standardOperator m d) (standardSpace m).grade
      (standardSpace m).grade d.step := by
  rw [LinearMap.isHomogeneous_def]
  intro a v hv
  rw [grade_standardSpace] at hv
  refine (Submodule.image_span_subset _ _ _).2 ?_ ⟨v, hv, rfl⟩
  rintro _ ⟨i, rfl⟩
  dsimp only
  by_cases h : a ∈ occurrenceInterval m i
  · rw [standardVector_of_mem h, standardOperator_standardBasis,
      StandardIndex.coe_snd_mk, StandardIndex.fst_mk]
    exact standardVector_mem_grade i _
  · rw [standardVector_of_notMem h, map_zero]
    exact zero_mem _

variable (m) in
/-- The standard pair of `m` in direction `d`: on each interval block of `m` the operator moves
each basis vector one step in direction `d`, and kills the last vector of the block when
`d = up` and the first vector when `d = down`. -/
noncomputable def standardPair (d : StepDirection) : GradedPair (standardSpace m) d where
  operator := standardOperator m d
  isHomogeneous := isHomogeneous_standardOperator m d

/-- The standard operator in direction `d` sends the basis vector of a valid label `(i, a)` to the
standard vector of `(i, a + d.step)`, which is zero when this step leaves the interval. -/
@[simp]
theorem standardPair_operator_standardBasis (d : StepDirection) (x : StandardIndex m) :
    (standardPair m d).operator (standardBasis m x) = standardVector m x.1 (x.2 + d.step) :=
  standardOperator_standardBasis m d x

/-- On a valid label the standard operator in direction `d` moves the standard vector one step in
direction `d`; the result is zero when this step leaves the interval. -/
@[simp]
theorem standardPair_operator_standardVector (d : StepDirection) {i : Fin m.card} {a : ℤ}
    (h : a ∈ occurrenceInterval m i) :
    (standardPair m d).operator (standardVector m i a) = standardVector m i (a + d.step) := by
  rw [standardVector_of_mem h, standardPair_operator_standardBasis,
    StandardIndex.coe_snd_mk, StandardIndex.fst_mk]

/-- The standard raising operator kills the last vector of each interval block. -/
@[simp]
theorem standardPair_up_operator_standardVector_snd (i : Fin m.card) :
    (standardPair m .up).operator (standardVector m i (occurrenceInterval m i).snd) = 0 := by
  rw [standardPair_operator_standardVector .up
    (NonemptyInterval.mem_def.2 ⟨(occurrenceInterval m i).fst_le_snd, le_rfl⟩),
    StepDirection.step_up, standardVector_eq_zero_iff, NonemptyInterval.mem_def]
  omega

/-- The standard lowering operator kills the first vector of each interval block. -/
@[simp]
theorem standardPair_down_operator_standardVector_fst (i : Fin m.card) :
    (standardPair m .down).operator (standardVector m i (occurrenceInterval m i).fst) = 0 := by
  rw [standardPair_operator_standardVector .down
    (NonemptyInterval.mem_def.2 ⟨le_rfl, (occurrenceInterval m i).fst_le_snd⟩),
    StepDirection.step_down, standardVector_eq_zero_iff, NonemptyInterval.mem_def]
  omega

/-- On a valid label the `k`-th power of the standard operator in direction `d` moves the
standard vector `k` steps in direction `d`. Since intervals are convex, the result is zero
exactly when the endpoint `a + k * d.step` lies outside the interval. -/
@[simp]
theorem standardPair_operator_pow_standardVector (d : StepDirection) {i : Fin m.card} {a : ℤ}
    (h : a ∈ occurrenceInterval m i) (k : ℕ) :
    ((standardPair m d).operator ^ k) (standardVector m i a) =
      standardVector m i (a + k * d.step) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih]
    by_cases hk : a + k * d.step ∈ occurrenceInterval m i
    · rw [standardPair_operator_standardVector d hk]
      congr 1
      push_cast
      ring
    · -- Once the block is left, the next step also lies outside it.
      rw [standardVector_of_notMem hk, map_zero, eq_comm, standardVector_eq_zero_iff]
      rw [NonemptyInterval.mem_def] at h hk ⊢
      cases d <;> simp only [StepDirection.step_up, StepDirection.step_down] at hk ⊢ <;>
        push_cast <;> omega

/-- The `k`-th power of the standard operator in direction `d` sends the basis vector of a valid
label `(i, a)` to the standard vector of `(i, a + k * d.step)`, which is zero once the block is
left. -/
@[simp]
theorem standardPair_operator_pow_standardBasis (d : StepDirection) (x : StandardIndex m)
    (k : ℕ) :
    ((standardPair m d).operator ^ k) (standardBasis m x) =
      standardVector m x.1 (x.2 + k * d.step) := by
  rw [standardBasis_eq_standardVector,
    standardPair_operator_pow_standardVector d x.mem_occurrenceInterval]

end Multisegment

end TauCeti
