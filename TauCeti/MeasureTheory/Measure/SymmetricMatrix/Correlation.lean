/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Correlation coordinates and their Lebesgue measure

A correlation matrix is a positive-semidefinite symmetric matrix with unit diagonal. A
symmetric matrix with unit diagonal is determined by its strictly lower-triangular entries, which
serve as coordinates. `TauCeti.correlationCoordinates p` reconstructs the
`p × p` symmetric matrix with unit diagonal from these entries; it is an affine map and a
homeomorphism onto the unit-diagonal symmetric matrices.

`TauCeti.correlationLebesgue p` is the pushforward of product Lebesgue measure on the
strict-lower coordinates. This is the reference measure for densities of random correlation
matrices, such as the LKJ laws. It is concentrated on the unit-diagonal symmetric matrices, and
it is invariant under simultaneous permutation of rows and columns and under conjugation by
diagonal sign matrices.

In these coordinates, the positive-definite correlation matrices form an open, bounded region
of positive finite volume: every off-diagonal entry of a positive-definite correlation matrix
lies in `(-1, 1)`, and the identity matrix is an interior point. The closure of the region is
the positive-semidefinite correlation region, and its boundary is contained in the
determinant-zero locus, which is Lebesgue-null.

## Main declarations

* `TauCeti.strictLowerTriangle` — the index type of strictly lower-triangular positions.
* `TauCeti.correlationCoordinates` — the affine reconstruction of a unit-diagonal symmetric
  matrix from its strict-lower entries.
* `TauCeti.correlationCoordinatesHomeomorph` — the homeomorphism onto the unit-diagonal
  symmetric matrices, and `TauCeti.measurableEmbedding_correlationCoordinates`.
* `TauCeti.correlationLebesgue` — Lebesgue measure on unit-diagonal symmetric matrices.
* `TauCeti.ae_correlationLebesgue_apply_self_eq_one` — it is concentrated on the unit-diagonal
  symmetric matrices.
* `TauCeti.correlationLebesgue_of_le_one` — for `p ≤ 1` it is the Dirac measure at the identity.
* `TauCeti.map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue`,
  `TauCeti.map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue` — invariance under
  congruence by permutation matrices and by diagonal sign matrices.
* `TauCeti.abs_lt_one_of_posDef_correlationCoordinates` — the off-diagonal entries of a
  positive-definite correlation matrix lie in `(-1, 1)`.
* `TauCeti.isOpen_setOfPred_posDef_correlationCoordinates`,
  `TauCeti.isBounded_setOfPred_posDef_correlationCoordinates` — the positive-definite
  coordinate region is open and bounded.
* `TauCeti.closure_setOfPred_posDef_correlationCoordinates` — its closure is the
  positive-semidefinite coordinate region.
* `TauCeti.correlationLebesgue_setOf_posDef_pos`,
  `TauCeti.correlationLebesgue_setOf_posDef_lt_top` — the positive-definite correlation
  matrices have positive finite `correlationLebesgue` measure.
* `TauCeti.correlationLebesgue_setOf_det_eq_zero`,
  `TauCeti.volume_frontier_setOfPred_posDef_correlationCoordinates` — the singular
  unit-diagonal symmetric matrices, and hence the boundary of the positive-definite region, are
  null.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped Matrix ENNReal

namespace TauCeti

/-- The index type for the strictly lower-triangular positions of a `p × p` matrix. A symmetric
matrix with unit diagonal is determined by these entries. -/
abbrev strictLowerTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.2 < ij.1}

section coordinates

variable (p : ℕ)

/-- The symmetric matrix with zero diagonal whose strictly lower-triangular entries are `x`; the
linear part of `TauCeti.correlationCoordinates`. Each coordinate is placed at the mirrored
strictly upper-triangular position, the diagonal coordinates are zero, and
`TauCeti.symmetricCoordinates` reconstructs the matrix. -/
private def offDiagonalSymmetric :
    (strictLowerTriangle p → ℝ) →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  (symmetricCoordinates p).symm.toLinearMap ∘ₗ
    LinearMap.pi fun ij : upperTriangle p =>
      if h : ij.1.1 < ij.1.2 then LinearMap.proj ⟨ij.1.swap, h⟩ else 0

/-- The correlation-coordinate map: the symmetric matrix with unit diagonal whose strictly
lower-triangular entries are `x`, reflected across the diagonal. It is affine, with linear part
the zero-diagonal reflection, and it is a homeomorphism onto the unit-diagonal symmetric matrices
(`TauCeti.correlationCoordinatesHomeomorph`). -/
def correlationCoordinates :
    (strictLowerTriangle p → ℝ) →ᴬ[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  (LinearMap.toContinuousLinearMap (offDiagonalSymmetric p)).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ _ ⟨1, IsSelfAdjoint.one _⟩

/-- The entries of `correlationCoordinates p x`: the coordinate below the diagonal, its reflection
above it, and `1` on it. -/
theorem coe_correlationCoordinates_apply (x : strictLowerTriangle p → ℝ) (i j : Fin p) :
    (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ) i j =
      if h : j < i then x ⟨(i, j), h⟩ else if h : i < j then x ⟨(j, i), h⟩ else 1 := by
  simp only [correlationCoordinates, ContinuousAffineMap.coe_add, Pi.add_apply,
    ContinuousLinearMap.coe_toContinuousAffineMap, LinearMap.coe_toContinuousLinearMap',
    ContinuousAffineMap.coe_const, Function.const_apply, Submodule.coe_add, Matrix.add_apply,
    offDiagonalSymmetric, LinearMap.coe_comp, Function.comp_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [coe_symmetricCoordinates_symm_apply_of_le p _ h.le, h, h.ne, not_lt.2 h.le]
  · simp
  · simp [coe_symmetricCoordinates_symm_apply_of_ge p _ h.le, h, h.ne']

@[simp]
theorem coe_correlationCoordinates_apply_of_lt (x : strictLowerTriangle p → ℝ) {i j : Fin p}
    (h : j < i) :
    (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(i, j), h⟩ := by
  rw [coe_correlationCoordinates_apply, dite_eq_left h]

@[simp]
theorem coe_correlationCoordinates_apply_of_gt (x : strictLowerTriangle p → ℝ) {i j : Fin p}
    (h : i < j) :
    (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(j, i), h⟩ := by
  rw [coe_correlationCoordinates_apply, dite_eq_right (not_lt.2 h.le), dite_eq_left h]

@[simp]
theorem coe_correlationCoordinates_apply_self (x : strictLowerTriangle p → ℝ) (i : Fin p) :
    (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ) i i = 1 := by
  simp [coe_correlationCoordinates_apply]

/-- The zero coordinate vector gives the identity matrix. -/
@[simp]
theorem coe_correlationCoordinates_zero :
    (correlationCoordinates p 0 : Matrix (Fin p) (Fin p) ℝ) = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h, h.ne']

/-- Shrinking the coordinates by `t` interpolates linearly between the identity matrix and the
unit-diagonal symmetric matrix `R x`: `R (t • x) = t • R x + (1 - t) • 1`. -/
theorem coe_correlationCoordinates_smul (t : ℝ) (x : strictLowerTriangle p → ℝ) :
    (correlationCoordinates p (t • x) : Matrix (Fin p) (Fin p) ℝ) =
      t • (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ) + (1 - t) • 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h, h.ne']

/-- The correlation-coordinate map is injective: the coordinates are entries of the matrix. -/
theorem correlationCoordinates_injective :
    Function.Injective (correlationCoordinates p) := fun x y hxy => by
  funext ij
  obtain ⟨⟨i, j⟩, h⟩ := ij
  have := congrArg (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
    (A : Matrix (Fin p) (Fin p) ℝ) i j) hxy
  simpa [h] using this

/-- A unit-diagonal symmetric matrix is reconstructed from its strictly lower-triangular
entries. -/
theorem correlationCoordinates_strictLowerEntries
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1) :
    correlationCoordinates p (fun ij => (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2) = A := by
  refine Subtype.ext ?_
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simpa [h] using selfAdjoint.coe_apply_comm A j i
  · simpa using (hA i).symm
  · simp [h]

/-- The range of the correlation-coordinate map is the set of unit-diagonal symmetric
matrices. -/
theorem range_correlationCoordinates :
    range (correlationCoordinates p) =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1} :=
  Subset.antisymm (range_subset_iff.2 fun x i => by simp) fun _ hA =>
    ⟨_, correlationCoordinates_strictLowerEntries p hA⟩

/-- The correlation-coordinate map as a homeomorphism onto the unit-diagonal symmetric matrices.
Its inverse reads off the strictly lower-triangular entries. -/
def correlationCoordinatesHomeomorph :
    (strictLowerTriangle p → ℝ) ≃ₜ
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) //
        ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1} where
  toFun x := ⟨correlationCoordinates p x, fun i => by simp⟩
  invFun A ij := (A.1 : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2
  left_inv x := by
    funext ij
    obtain ⟨⟨i, j⟩, h⟩ := ij
    simp [h]
  right_inv A := Subtype.ext (correlationCoordinates_strictLowerEntries p A.2)
  continuous_toFun := (correlationCoordinates p).continuous.subtype_mk _
  continuous_invFun := continuous_pi fun ij =>
    (selfAdjoint.continuous_coe_apply ij.1.1 ij.1.2).comp continuous_subtype_val

@[simp]
theorem coe_correlationCoordinatesHomeomorph_apply (x : strictLowerTriangle p → ℝ) :
    (correlationCoordinatesHomeomorph p x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) =
      correlationCoordinates p x := by
  simp [correlationCoordinatesHomeomorph]

@[simp]
theorem correlationCoordinatesHomeomorph_symm_apply
    (A : {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) //
      ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1}) (ij : strictLowerTriangle p) :
    (correlationCoordinatesHomeomorph p).symm A ij =
      (A.1 : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 := by
  simp [correlationCoordinatesHomeomorph]

/-- The correlation-coordinate map is a closed embedding: the unit-diagonal symmetric matrices
form a closed set. -/
theorem isClosedEmbedding_correlationCoordinates :
    Topology.IsClosedEmbedding (correlationCoordinates p) := by
  have hclosed : IsClosed {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1} := by
    rw [ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_eq (selfAdjoint.continuous_coe_apply i i) continuous_const
  exact (hclosed.isClosedEmbedding_subtypeVal).comp
    (correlationCoordinatesHomeomorph p).isClosedEmbedding

theorem measurableEmbedding_correlationCoordinates :
    MeasurableEmbedding (correlationCoordinates p) :=
  (isClosedEmbedding_correlationCoordinates p).measurableEmbedding

end coordinates

/-! ### Lebesgue measure on unit-diagonal symmetric matrices -/

/-- Lebesgue measure on the unit-diagonal symmetric matrices: the pushforward of product Lebesgue
measure on the strictly lower-triangular coordinates along `TauCeti.correlationCoordinates`. The
coordinate unit cube has measure one. -/
def correlationLebesgue (p : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (volume : Measure (strictLowerTriangle p → ℝ)).map (correlationCoordinates p)

/-- The correlation-coordinate map carries product Lebesgue measure to
`correlationLebesgue`. -/
theorem measurePreserving_correlationCoordinates (p : ℕ) :
    MeasurePreserving (correlationCoordinates p) volume (correlationLebesgue p) :=
  ⟨(correlationCoordinates p).continuous.measurable, rfl⟩

/-- The `correlationLebesgue` measure of any set is the Lebesgue measure of its preimage in
correlation coordinates. -/
theorem correlationLebesgue_apply (p : ℕ)
    (s : Set (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) :
    correlationLebesgue p s = volume (correlationCoordinates p ⁻¹' s) :=
  (measurableEmbedding_correlationCoordinates p).map_apply _ s

/-- `correlationLebesgue`-almost every symmetric matrix has unit diagonal. -/
theorem ae_correlationLebesgue_apply_self_eq_one (p : ℕ) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂correlationLebesgue p,
      ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1 :=
  (measurableEmbedding_correlationCoordinates p).ae_map_iff.2
    (Filter.Eventually.of_forall fun x i => coe_correlationCoordinates_apply_self p x i)

/-- `correlationLebesgue` is σ-finite, being the pushforward of Lebesgue measure along a
measurable embedding. -/
instance (p : ℕ) : SigmaFinite (correlationLebesgue p) :=
  (measurableEmbedding_correlationCoordinates p).sigmaFinite_map

/-- In dimensions zero and one there are no off-diagonal entries, and `correlationLebesgue` is
the Dirac measure at the identity matrix `correlationCoordinates p 0`
(`TauCeti.coe_correlationCoordinates_zero`). -/
theorem correlationLebesgue_of_le_one {p : ℕ} (hp : p ≤ 1) :
    correlationLebesgue p = Measure.dirac (correlationCoordinates p 0) := by
  have : IsEmpty (strictLowerTriangle p) :=
    ⟨fun ij => (ne_of_gt ij.2) (Fin.ext (by omega))⟩
  rw [correlationLebesgue, volume_pi, Measure.pi_of_empty _ 0]
  exact Measure.map_dirac' (correlationCoordinates p).continuous.measurable 0

/-! ### The positive-definite region -/

section posDef

variable {p : ℕ}

/-- The off-diagonal entries of a positive-definite correlation matrix lie in `(-1, 1)`. -/
theorem abs_lt_one_of_posDef_correlationCoordinates {x : strictLowerTriangle p → ℝ}
    (hx : (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).PosDef)
    (ij : strictLowerTriangle p) : |x ij| < 1 := by
  obtain ⟨⟨i, j⟩, h⟩ := ij
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [h.ne, h.ne']
  have hdet := (hx.submatrix hinj).det_pos
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, coe_correlationCoordinates_apply_self,
    coe_correlationCoordinates_apply_of_lt p x h,
    coe_correlationCoordinates_apply_of_gt p x h, one_mul] at hdet
  rw [abs_lt]
  constructor <;> nlinarith

variable (p)

/-- The positive-definite correlation matrices form an open region in correlation
coordinates. -/
theorem isOpen_setOfPred_posDef_correlationCoordinates :
    IsOpen {x : strictLowerTriangle p → ℝ |
      (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).PosDef} :=
  (isOpen_setOfPred_posDefMatrix p).preimage (correlationCoordinates p).continuous

/-- The positive-definite correlation matrices form a bounded region in correlation
coordinates. -/
theorem isBounded_setOfPred_posDef_correlationCoordinates :
    Bornology.IsBounded {x : strictLowerTriangle p → ℝ |
      (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  exact fun ij => (Real.norm_eq_abs _ ▸ abs_lt_one_of_posDef_correlationCoordinates hx ij).le

/-- The closure of the positive-definite region in correlation coordinates is the
positive-semidefinite region. -/
theorem closure_setOfPred_posDef_correlationCoordinates :
    closure {x : strictLowerTriangle p → ℝ |
        (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).PosDef} =
      {x | (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).PosSemidef} := by
  -- If `R x` is positive semidefinite, then `R (t • x) = t • R x + (1 - t) • 1` is positive
  -- definite for `0 < t < 1`, and `t • x → x` as `t → 1`.
  refine Subset.antisymm (closure_minimal (fun x hx => Matrix.PosDef.posSemidef hx)
    (Matrix.posSemidef_is_closed.preimage
      (continuous_subtype_val.comp (correlationCoordinates p).continuous))) fun x hx => ?_
  have hlim : Filter.Tendsto (fun t : ℝ => t • x) (nhdsWithin 1 (Iio 1)) (nhds x) := by
    have hc : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
  rw [coe_correlationCoordinates_smul]
  exact Matrix.PosDef.posSemidef_add (Matrix.PosSemidef.smul hx ht.1.le)
    (Matrix.PosDef.one.smul (sub_pos.2 ht.2))

/-- The determinant of the unit-diagonal symmetric matrix with given strictly lower-triangular
coordinates, as a polynomial in those coordinates. -/
private def correlationDetPolynomial : MvPolynomial (strictLowerTriangle p) ℝ :=
  (Matrix.of fun i j : Fin p =>
    if h : j < i then MvPolynomial.X ⟨(i, j), h⟩
    else if h : i < j then MvPolynomial.X ⟨(j, i), h⟩ else 1).det

private theorem eval_correlationDetPolynomial (x : strictLowerTriangle p → ℝ) :
    MvPolynomial.eval x (correlationDetPolynomial p) =
      (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).det := by
  rw [correlationDetPolynomial, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    coe_correlationCoordinates_apply]
  split_ifs <;> simp

/-- The singular unit-diagonal symmetric matrices form a null set in correlation
coordinates. -/
theorem volume_setOfPred_det_correlationCoordinates_eq_zero :
    volume {x : strictLowerTriangle p → ℝ |
      (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).det = 0} = 0 := by
  have hne : correlationDetPolynomial p ≠ 0 := fun h => by
    simpa [h] using eval_correlationDetPolynomial p 0
  simpa only [eval_correlationDetPolynomial] using
    (correlationDetPolynomial p).volume_setOfPred_eval_eq_zero hne

/-- The boundary of the positive-definite region in correlation coordinates is Lebesgue-null. -/
theorem volume_frontier_setOfPred_posDef_correlationCoordinates :
    volume (frontier {x : strictLowerTriangle p → ℝ |
      (correlationCoordinates p x : Matrix (Fin p) (Fin p) ℝ).PosDef}) = 0 := by
  refine measure_mono_null (fun x hx => ?_)
    (volume_setOfPred_det_correlationCoordinates_eq_zero p)
  rw [frontier, closure_setOfPred_posDef_correlationCoordinates,
    (isOpen_setOfPred_posDef_correlationCoordinates p).interior_eq] at hx
  exact not_not.1 fun h => hx.2 (hx.1.posDef_iff_det_ne_zero.2 h)

/-- The singular symmetric matrices are `correlationLebesgue`-null. -/
theorem correlationLebesgue_setOf_det_eq_zero :
    correlationLebesgue p {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).det = 0} = 0 := by
  rw [correlationLebesgue_apply]
  exact volume_setOfPred_det_correlationCoordinates_eq_zero p

/-- The positive-definite correlation matrices have positive `correlationLebesgue` measure. -/
theorem correlationLebesgue_setOf_posDef_pos :
    0 < correlationLebesgue p {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  rw [correlationLebesgue_apply]
  exact (isOpen_setOfPred_posDef_correlationCoordinates p).measure_pos volume
    ⟨0, by simpa using Matrix.PosDef.one⟩

/-- The positive-definite correlation matrices have finite `correlationLebesgue` measure. -/
theorem correlationLebesgue_setOf_posDef_lt_top :
    correlationLebesgue p {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} < ∞ := by
  rw [correlationLebesgue_apply]
  exact (isBounded_setOfPred_posDef_correlationCoordinates p).measure_lt_top

end posDef

/-! ### Permutation and sign invariance

Simultaneously permuting the rows and columns of a unit-diagonal symmetric matrix, or
conjugating it by a diagonal sign matrix, permutes or changes the signs of its strict-lower
coordinates. Both coordinate changes preserve Lebesgue measure, so `correlationLebesgue` is
invariant. -/

section invariance

variable {p : ℕ}

/-- A map of symmetric matrices that acts on correlation coordinates by a Lebesgue-measure
preserving map leaves `correlationLebesgue` invariant. -/
private theorem map_correlationLebesgue_of_comp_eq
    {T : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} (hT : Measurable T)
    {f : (strictLowerTriangle p → ℝ) → strictLowerTriangle p → ℝ}
    (hf : MeasurePreserving f volume volume)
    (h : ∀ x, T (correlationCoordinates p x) = correlationCoordinates p (f x)) :
    (correlationLebesgue p).map T = correlationLebesgue p := by
  have hR := (correlationCoordinates p).continuous.measurable
  have hcomp : T ∘ correlationCoordinates p = correlationCoordinates p ∘ f := funext h
  rw [correlationLebesgue, Measure.map_map hT hR, hcomp, ← Measure.map_map hR hf.measurable,
    hf.map_eq]

/-- A strictly lower-triangular position is determined by its unordered pair of indices. -/
private theorem injective_sym2_strictLowerTriangle :
    Function.Injective fun ij : strictLowerTriangle p => s(ij.1.1, ij.1.2) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd (hij.trans hkl) (lt_irrefl _)

/-- A permutation of the indices acts on strictly lower-triangular positions by moving both
indices and reordering them. -/
private def permStrictLowerTriangle (σ : Equiv.Perm (Fin p)) (ij : strictLowerTriangle p) :
    strictLowerTriangle p :=
  if h : σ ij.1.2 < σ ij.1.1 then ⟨(σ ij.1.1, σ ij.1.2), h⟩
  else ⟨(σ ij.1.2, σ ij.1.1), lt_of_le_of_ne (not_lt.1 h) (σ.injective.ne ij.2.ne')⟩

private theorem sym2_permStrictLowerTriangle (σ : Equiv.Perm (Fin p))
    (ij : strictLowerTriangle p) :
    s((permStrictLowerTriangle σ ij).1.1, (permStrictLowerTriangle σ ij).1.2) =
      s(σ ij.1.1, σ ij.1.2) := by
  unfold permStrictLowerTriangle
  split_ifs
  · rfl
  · exact Sym2.eq_swap

private theorem bijective_permStrictLowerTriangle (σ : Equiv.Perm (Fin p)) :
    Function.Bijective (permStrictLowerTriangle σ) := by
  refine Finite.injective_iff_bijective.1 fun ij kl h => injective_sym2_strictLowerTriangle ?_
  have h' := congrArg (fun ij : strictLowerTriangle p => s(ij.1.1, ij.1.2)) h
  simp only [sym2_permStrictLowerTriangle] at h'
  exact Sym2.map.injective σ.injective (by simpa using h')

/-- `correlationLebesgue` is invariant under simultaneous permutation of rows and columns,
that is, under congruence by a permutation matrix. -/
theorem map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue
    (σ : Equiv.Perm (Fin p)) :
    (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap (Equiv.Perm.permMatrix ℝ σ)) =
      correlationLebesgue p := by
  set e := Equiv.ofBijective _ (bijective_permStrictLowerTriangle σ)
  have hf : MeasurePreserving (fun x : strictLowerTriangle p → ℝ => x ∘ e) volume volume := by
    convert volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id volume) using 1
    funext x ij
    simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']
  refine map_correlationLebesgue_of_comp_eq
    (LinearMap.continuous_of_finiteDimensional _).measurable hf fun x => Subtype.ext ?_
  ext i j
  rw [Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply, Matrix.submatrix_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have hne : σ i ≠ σ j := σ.injective.ne h.ne
    rw [coe_correlationCoordinates_apply_of_gt p _ h, Function.comp_apply,
      Equiv.ofBijective_apply, coe_correlationCoordinates_apply]
    unfold permStrictLowerTriangle
    by_cases h' : σ i < σ j
    · simp [h', not_lt.2 h'.le]
    · simp [h', lt_of_le_of_ne (not_lt.1 h') hne.symm]
  · simp
  · have hne : σ j ≠ σ i := σ.injective.ne h.ne
    rw [coe_correlationCoordinates_apply_of_lt p _ h, Function.comp_apply,
      Equiv.ofBijective_apply, coe_correlationCoordinates_apply]
    unfold permStrictLowerTriangle
    by_cases h' : σ j < σ i
    · simp [h']
    · simp [h', lt_of_le_of_ne (not_lt.1 h') hne.symm]

/-- `correlationLebesgue` is invariant under conjugation by a diagonal sign matrix. -/
theorem map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue {s : Fin p → ℝ}
    (hs : ∀ i, |s i| = 1) :
    (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s)) =
      correlationLebesgue p := by
  -- Multiplying a real coordinate by a factor of absolute value one preserves Lebesgue measure.
  have hmul {c : ℝ} (hc : |c| = 1) : MeasurePreserving (fun y : ℝ => c * y) volume volume := by
    have hc0 : c ≠ 0 := fun h => by simp [h] at hc
    exact ⟨measurable_const_mul c, by
      rw [Real.map_volume_mul_left hc0, abs_inv, hc, inv_one, ENNReal.ofReal_one, one_smul]⟩
  have hf : MeasurePreserving
      (fun (x : strictLowerTriangle p → ℝ) (ij : strictLowerTriangle p) =>
        s ij.1.1 * s ij.1.2 * x ij) volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume) fun ij =>
      hmul (by rw [abs_mul, hs, hs, one_mul])
  refine map_correlationLebesgue_of_comp_eq
    (LinearMap.continuous_of_finiteDimensional _).measurable hf fun x => Subtype.ext ?_
  ext i j
  rw [Matrix.coe_symmetricCongruenceLinearMap_diagonal_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [coe_correlationCoordinates_apply_of_gt p _ h]
    ring
  · rw [coe_correlationCoordinates_apply_self, coe_correlationCoordinates_apply_self, mul_one,
      ← abs_mul_abs_self, hs, one_mul]
  · simp only [coe_correlationCoordinates_apply_of_lt p _ h]
    ring

end invariance

end TauCeti
