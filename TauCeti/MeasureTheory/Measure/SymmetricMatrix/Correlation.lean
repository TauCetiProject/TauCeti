/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.Analysis.Matrix.PartialCorrelation
public import TauCeti.LinearAlgebra.Matrix.Cholesky.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineMap
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Topology.Constructions.Pi
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Order.Prod.Lex.Basic

/-!
# Correlation coordinates and the reference Lebesgue measure for correlation matrices

A correlation matrix is a positive-semidefinite symmetric matrix with unit diagonal. The
correlation matrices form a subset of the affine space of unit-diagonal symmetric matrices, and
a unit-diagonal symmetric matrix is determined by its strictly lower entries `R i j`, `j < i`,
which may be chosen freely: `TauCeti.correlationMatrix p x` reconstructs the unit-diagonal
symmetric matrix with coordinates `x : TauCeti.strictLowerTriangle p → ℝ` by symmetry and ones
on the diagonal. It is a correlation matrix exactly when it is positive semidefinite. This is a
continuous affine closed embedding of the coordinate space into the symmetric matrices whose
range is exactly the unit-diagonal matrices; the continuous linear map
`TauCeti.correlationCoordinates p` reading off the strictly lower entries inverts it there.

Pushing coordinate Lebesgue measure forward along this embedding gives
`TauCeti.correlationLebesgue p`, the reference measure for laws of random correlation matrices
such as the LKJ distributions. It measures the whole affine space of unit-diagonal symmetric
matrices, not only the positive-semidefinite ones: positivity is imposed separately, for instance
by the support of a density. It is concentrated on the unit-diagonal matrices, it is invariant
under simultaneous permutation of rows and columns and under sign changes of the coordinate axes,
and in dimensions zero and one it is the Dirac measure at the identity.

The positive-definite correlation matrices correspond to the coordinate region
`TauCeti.posDefCorrelationRegion p`. It is open, convex and contains the origin (the identity
matrix), and all its coordinates lie in `(-1, 1)`, so it has positive finite volume. Its closure
is the region of positive-semidefinite correlation matrices, and its frontier, the
positive-semidefinite correlation matrices with zero determinant, is Lebesgue-null.

Partial correlations parametrize this region: the forward map
`TauCeti.correlationCoordinatesOfPartialCorrelation` is a bijection from the open cube
`(-1, 1) ^ J` onto `TauCeti.posDefCorrelationRegion p`, and its inverse takes the Cholesky factor
of a positive-definite correlation matrix and reads off its partial correlations with
`Matrix.partialCorrelationOfCholesky` (`TauCeti.partialCorrelationOfCorrelationCoordinates`).

## Main declarations

* `TauCeti.correlationMatrix` — the unit-diagonal symmetric matrix with prescribed strictly lower
  entries, as a continuous affine map.
* `TauCeti.correlationCoordinates` — the strictly lower entries of a symmetric matrix.
* `TauCeti.range_correlationMatrix` — the range is the unit-diagonal symmetric matrices.
* `TauCeti.isClosedEmbedding_correlationMatrix`, `TauCeti.measurableEmbedding_correlationMatrix`.
* `TauCeti.correlationLebesgue` — Lebesgue measure on the unit-diagonal symmetric matrices, the
  reference measure for random correlation matrices.
* `TauCeti.correlationLebesgue_of_le_one` — in dimension at most one it is the Dirac measure at
  the identity.
* `TauCeti.map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue`,
  `TauCeti.map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue` — invariance under
  permutation and sign-change conjugation.
* `TauCeti.posDefCorrelationRegion` — the coordinates of positive-definite correlation matrices.
* `TauCeti.correlationCoordinatesOfPartialCorrelation` — the continuous partial-correlation
  forward map, smooth and injective on the open cube, with values in the positive-definite region.
* `TauCeti.abs_det_fderiv_correlationCoordinatesOfPartialCorrelation` — the exact Jacobian of
  the partial-correlation forward map on the open cube.
* `TauCeti.coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation` — reconstruction of
  partial-correlation Gram matrices from their correlation coordinates on the closed cube.
* `TauCeti.bijOn_correlationCoordinatesOfPartialCorrelation`,
  `TauCeti.image_correlationCoordinatesOfPartialCorrelation` — the forward map is a bijection from
  the open cube onto the positive-definite region.
* `TauCeti.partialCorrelationOfCorrelationCoordinates`,
  `TauCeti.invOn_partialCorrelationOfCorrelationCoordinates` — its inverse, which reads the partial
  correlations off the Cholesky factor and maps the region into the open cube.
* `TauCeti.volume_posDefCorrelationRegion_pos`, `TauCeti.volume_posDefCorrelationRegion_lt_top`.
* `TauCeti.closure_posDefCorrelationRegion` — the closure is the positive-semidefinite region.
* `TauCeti.frontier_posDefCorrelationRegion`, `TauCeti.volume_frontier_posDefCorrelationRegion` —
  the frontier is the singular positive-semidefinite region, and it is null.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory Topology Filter Set
open scoped ContDiff

namespace TauCeti

variable (p : ℕ)

/-- The unit-diagonal symmetric matrix with strictly lower entries `x`: its entry at `(i, j)`,
`j < i`, and at `(j, i)` is `x (i, j)`. It is an affine map of the coordinates, and its value is a
correlation matrix exactly when it is positive semidefinite. -/
def correlationMatrix :
    (strictLowerTriangle p → ℝ) →ᴬ[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) where
  toFun x := (symmetricCoordinates p).symm fun ij =>
    if h : ij.1.1 < ij.1.2 then x ⟨(ij.1.2, ij.1.1), h⟩ else 1
  linear := (symmetricCoordinates p).symm.toLinearMap ∘ₗ
    { toFun x ij := if h : ij.1.1 < ij.1.2 then x ⟨(ij.1.2, ij.1.1), h⟩ else 0
      map_add' x y := by
        funext ij
        by_cases h : ij.1.1 < ij.1.2 <;> simp [h]
      map_smul' c x := by
        funext ij
        by_cases h : ij.1.1 < ij.1.2 <;> simp [h] }
  map_vadd' x v := by
    simp only [vadd_eq_add, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [← map_add]
    congr 1
    funext ij
    by_cases h : ij.1.1 < ij.1.2 <;> simp [h]
  cont := (symmetricCoordinates p).symm.continuous.comp <| continuous_pi fun ij => by
    by_cases h : ij.1.1 < ij.1.2
    · simpa [h] using continuous_apply _
    · simpa [h] using continuous_const

variable {p}

/-- The matrix `TauCeti.correlationMatrix p x` has ones on the diagonal. -/
@[simp]
theorem coe_correlationMatrix_apply_self (x : strictLowerTriangle p → ℝ) (i : Fin p) :
    (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ) i i = 1 := by
  simp [correlationMatrix]

/-- A strictly lower entry of `TauCeti.correlationMatrix p x` is its coordinate. -/
@[simp]
theorem coe_correlationMatrix_apply_of_gt (x : strictLowerTriangle p → ℝ) {i j : Fin p}
    (h : j < i) :
    (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(i, j), h⟩ := by
  simp [correlationMatrix, coe_symmetricCoordinates_symm_apply_of_ge p _ h.le, h]

/-- A strictly upper entry of `TauCeti.correlationMatrix p x` is the coordinate at the reflected
position. -/
@[simp]
theorem coe_correlationMatrix_apply_of_lt (x : strictLowerTriangle p → ℝ) {i j : Fin p}
    (h : i < j) :
    (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(j, i), h⟩ := by
  simp [correlationMatrix, coe_symmetricCoordinates_symm_apply_of_le p _ h.le, h]

/-- An off-diagonal entry of `TauCeti.correlationMatrix p x` is the coordinate at the sorted
position. -/
theorem coe_correlationMatrix_apply_of_ne (x : strictLowerTriangle p → ℝ) {i j : Fin p}
    (h : i ≠ j) :
    (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ) i j =
      x ⟨(max i j, min i j), min_lt_max.2 h⟩ := by
  rcases h.lt_or_gt with h | h
  · simp [h, h.le]
  · simp [h, h.le]

/-- The origin of the coordinates is the identity matrix. -/
@[simp]
theorem coe_correlationMatrix_zero :
    (correlationMatrix p 0 : Matrix (Fin p) (Fin p) ℝ) = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h, h.ne']

/-- Scaling the coordinates by `c` moves `TauCeti.correlationMatrix p x` towards the identity:
`R (c • x) = c • R x + (1 - c) • 1`. -/
theorem coe_correlationMatrix_smul (c : ℝ) (x : strictLowerTriangle p → ℝ) :
    (correlationMatrix p (c • x) : Matrix (Fin p) (Fin p) ℝ) =
      c • (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ) + (1 - c) • 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h, h.ne']

variable (p) in
/-- The strictly lower entries of a symmetric matrix, as a continuous linear map. On the
unit-diagonal matrices it inverts `TauCeti.correlationMatrix`. -/
def correlationCoordinates :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →L[ℝ] (strictLowerTriangle p → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun A ij := (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

@[simp]
theorem correlationCoordinates_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (ij : strictLowerTriangle p) :
    correlationCoordinates p A ij = (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 :=
  (rfl)

@[simp]
theorem correlationCoordinates_correlationMatrix (x : strictLowerTriangle p → ℝ) :
    correlationCoordinates p (correlationMatrix p x) = x := by
  funext ij
  simp [ij.2]

variable (p) in
theorem leftInverse_correlationCoordinates_correlationMatrix :
    Function.LeftInverse (correlationCoordinates p) (correlationMatrix p) :=
  correlationCoordinates_correlationMatrix

variable (p) in
theorem correlationMatrix_injective : Function.Injective (correlationMatrix p) :=
  (leftInverse_correlationCoordinates_correlationMatrix p).injective

/-- A unit-diagonal symmetric matrix is the value of `TauCeti.correlationMatrix` at its strictly
lower entries. -/
theorem correlationMatrix_correlationCoordinates
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1) :
    correlationMatrix p (correlationCoordinates p A) = A := by
  refine Subtype.ext ?_
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, selfAdjoint.coe_apply_comm A i j]
  · simp [hA]
  · simp [h]

variable (p) in
/-- The range of `TauCeti.correlationMatrix p` is exactly the set of unit-diagonal symmetric
matrices. -/
theorem range_correlationMatrix :
    range (correlationMatrix p) = {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1} := by
  ext A
  refine ⟨?_, fun hA => ⟨_, correlationMatrix_correlationCoordinates hA⟩⟩
  rintro ⟨x, rfl⟩ i
  simp

variable (p) in
/-- The map `TauCeti.correlationMatrix p` is a closed embedding: an affine homeomorphism onto the
closed set of unit-diagonal symmetric matrices. -/
theorem isClosedEmbedding_correlationMatrix : IsClosedEmbedding (correlationMatrix p) :=
  (leftInverse_correlationCoordinates_correlationMatrix p).isClosedEmbedding
    (correlationCoordinates p).continuous (correlationMatrix p).continuous

variable (p) in
/-- The map `TauCeti.correlationMatrix p` is a measurable embedding of the coordinate space into the
symmetric matrices. -/
theorem measurableEmbedding_correlationMatrix : MeasurableEmbedding (correlationMatrix p) :=
  (isClosedEmbedding_correlationMatrix p).measurableEmbedding

/-! ### Lebesgue measure on unit-diagonal symmetric matrices -/

variable (p) in
/-- Lebesgue measure on the affine space of unit-diagonal symmetric matrices: the pushforward of
Lebesgue measure on the strictly lower coordinates along `TauCeti.correlationMatrix p`. It does not
impose positive semidefiniteness; it is the reference measure against which laws of random
correlation matrices are described, with positivity imposed separately. -/
def correlationLebesgue : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (volume : Measure (strictLowerTriangle p → ℝ)).map (correlationMatrix p)

variable (p) in
theorem measurePreserving_correlationMatrix :
    MeasurePreserving (correlationMatrix p) volume (correlationLebesgue p) :=
  ⟨(correlationMatrix p).continuous.measurable, rfl⟩

/-- The measure of a set `s` of symmetric matrices is the volume of the coordinates `x` with
`TauCeti.correlationMatrix p x ∈ s`, that is, of the unit-diagonal matrices in `s`. -/
theorem correlationLebesgue_apply (s : Set (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) :
    correlationLebesgue p s = volume (correlationMatrix p ⁻¹' s) :=
  (measurableEmbedding_correlationMatrix p).map_apply _ _

variable (p) in
/-- `TauCeti.correlationLebesgue p`-almost every symmetric matrix has unit diagonal. -/
theorem ae_correlationLebesgue_diag_eq_one :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂correlationLebesgue p,
      ∀ i, (A : Matrix (Fin p) (Fin p) ℝ) i i = 1 := by
  rw [correlationLebesgue, (measurableEmbedding_correlationMatrix p).ae_map_iff]
  exact ae_of_all _ fun x i => coe_correlationMatrix_apply_self x i

instance correlationLebesgueSigmaFinite : SigmaFinite (correlationLebesgue p) :=
  (measurableEmbedding_correlationMatrix p).sigmaFinite_map

/-- In dimension at most one there are no strictly lower coordinates, and
`TauCeti.correlationLebesgue p` is the Dirac measure at the identity. -/
theorem correlationLebesgue_of_le_one (hp : p ≤ 1) :
    correlationLebesgue p = Measure.dirac ⟨1, IsSelfAdjoint.one _⟩ := by
  have : IsEmpty (strictLowerTriangle p) :=
    ⟨fun ij => by have := ij.2; have := ij.1.1.2; omega⟩
  have h0 : correlationMatrix p 0 = ⟨1, IsSelfAdjoint.one _⟩ :=
    Subtype.ext coe_correlationMatrix_zero
  rw [correlationLebesgue, volume_pi, Measure.pi_of_empty _ 0,
    Measure.map_dirac' (correlationMatrix p).continuous.measurable, h0]

/-! ### The positive-definite region -/

variable (p) in
/-- The coordinates of the positive-definite correlation matrices. -/
def posDefCorrelationRegion : Set (strictLowerTriangle p → ℝ) :=
  {x | (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).PosDef}

@[simp]
theorem mem_posDefCorrelationRegion {x : strictLowerTriangle p → ℝ} :
    x ∈ posDefCorrelationRegion p ↔ (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).PosDef :=
  Iff.rfl

variable (p) in
theorem isOpen_posDefCorrelationRegion : IsOpen (posDefCorrelationRegion p) :=
  (isOpen_setOfPred_posDefMatrix p).preimage (correlationMatrix p).continuous

variable (p) in
theorem measurableSet_posDefCorrelationRegion : MeasurableSet (posDefCorrelationRegion p) :=
  (isOpen_posDefCorrelationRegion p).measurableSet

variable (p) in
theorem convex_posDefCorrelationRegion : Convex ℝ (posDefCorrelationRegion p) :=
  (convex_setOfPred_posDef.affine_preimage
    ((selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype.toAffineMap)).affine_preimage
    (correlationMatrix p).toAffineMap

variable (p) in
/-- The origin, the coordinates of the identity matrix, is a positive-definite correlation
matrix. -/
theorem zero_mem_posDefCorrelationRegion : (0 : strictLowerTriangle p → ℝ) ∈
    posDefCorrelationRegion p := by
  simpa using Matrix.PosDef.one

/-- The strictly lower coordinates of the Gram matrix constructed from partial correlations.
On the open cube this maps into the positive-definite correlation region. Outside the cube,
it retains the square-root totalization of `TauCeti.partialCorrelationGram`. -/
def correlationCoordinatesOfPartialCorrelation (z : strictLowerTriangle p → ℝ) :
    strictLowerTriangle p → ℝ :=
  correlationCoordinates p
    ⟨partialCorrelationGram z,
      Matrix.isHermitian_iff_isSelfAdjoint.1 (posSemidef_partialCorrelationGram z).isHermitian⟩

/-- A coordinate of the forward map is the corresponding strictly lower Gram entry. -/
@[simp]
theorem correlationCoordinatesOfPartialCorrelation_apply (z : strictLowerTriangle p → ℝ)
    (ij : strictLowerTriangle p) :
    correlationCoordinatesOfPartialCorrelation z ij =
      partialCorrelationGram z ij.1.1 ij.1.2 := (rfl)

/-- On the closed partial-correlation cube, reconstruction from correlation coordinates
returns the original Gram matrix. -/
@[simp]
theorem coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| ≤ 1) :
    (correlationMatrix p (correlationCoordinatesOfPartialCorrelation z) :
      Matrix (Fin p) (Fin p) ℝ) =
      partialCorrelationGram z := by
  exact congrArg Subtype.val
    (correlationMatrix_correlationCoordinates (partialCorrelationGram_apply_self hz))

/-- The partial-correlation forward map sends the open cube into the positive-definite
correlation region. -/
theorem mapsTo_correlationCoordinatesOfPartialCorrelation :
    MapsTo (correlationCoordinatesOfPartialCorrelation (p := p)) {z | ∀ ij, |z ij| < 1}
      (posDefCorrelationRegion p) := by
  intro z hz
  rw [mem_posDefCorrelationRegion,
    coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation (fun ij ↦ (hz ij).le)]
  exact posDef_partialCorrelationGram hz

/-- The partial-correlation forward map is injective on the open cube. -/
theorem injOn_correlationCoordinatesOfPartialCorrelation :
    InjOn (correlationCoordinatesOfPartialCorrelation (p := p)) {z | ∀ ij, |z ij| < 1} := by
  intro z hz w hw heq
  apply injOn_partialCorrelationGram hz hw
  have h := congrArg (fun x ↦ (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ)) heq
  rwa [coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation (fun ij ↦ (hz ij).le),
    coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation (fun ij ↦ (hw ij).le)] at h

/-- The partial-correlation forward map is continuous on the entire coordinate space. -/
@[fun_prop]
theorem continuous_correlationCoordinatesOfPartialCorrelation :
    Continuous (correlationCoordinatesOfPartialCorrelation (p := p)) := by
  apply continuous_pi
  intro ij
  simp only [correlationCoordinatesOfPartialCorrelation_apply]
  exact (continuous_apply ij.1.2).comp
    ((continuous_apply ij.1.1).comp continuous_partialCorrelationGram)

/-- The partial-correlation forward map is smooth on the open cube. -/
theorem contDiffOn_correlationCoordinatesOfPartialCorrelation :
    ContDiffOn ℝ ∞ (correlationCoordinatesOfPartialCorrelation (p := p))
      {z | ∀ ij, |z ij| < 1} := by
  apply contDiffOn_pi.2
  intro ij
  simp only [correlationCoordinatesOfPartialCorrelation_apply]
  exact contDiffOn_pi.1 (contDiffOn_pi.1 contDiffOn_partialCorrelationGram ij.1.1) ij.1.2

/-! ### The partial-correlation Jacobian -/

private def partialCorrelationPrefix (z : strictLowerTriangle p → ℝ) (i j : Fin p) : ℝ :=
  ∏ kl : strictLowerTriangle p with kl.1.1 = i ∧ kl.1.2 < j,
    Real.sqrt (1 - z kl ^ 2)

private abbrev partialCorrelationJacobianOccurrence (p : ℕ) :=
  Σ ij : strictLowerTriangle p,
    {kl : strictLowerTriangle p // kl.1.1 = ij.1.1 ∧ kl.1.2 < ij.1.2} ⊕
      {kl : strictLowerTriangle p // kl.1.1 = ij.1.2 ∧ kl.1.2 < ij.1.2}

private abbrev partialCorrelationJacobianMultiplicity (p : ℕ) :=
  Σ kl : strictLowerTriangle p, {k : Fin p // kl.1.2 < k ∧ k ≠ kl.1.1}

private def partialCorrelationJacobianOccurrenceEquiv :
    partialCorrelationJacobianOccurrence p ≃ partialCorrelationJacobianMultiplicity p where
  toFun q := match q with
    | ⟨ij, Sum.inl kl⟩ => ⟨kl, ⟨ij.1.2, kl.2.2, fun h ↦ ij.2.ne (h.trans kl.2.1)⟩⟩
    | ⟨ij, Sum.inr kl⟩ => ⟨kl, ⟨ij.1.1, kl.2.2.trans ij.2,
        fun h ↦ ij.2.ne' (h.trans kl.2.1)⟩⟩
  invFun q := if h : q.2.1 < q.1.1.1 then
      ⟨⟨(q.1.1.1, q.2.1), h⟩, Sum.inl ⟨q.1, rfl, q.2.2.1⟩⟩
    else
      ⟨⟨(q.2.1, q.1.1.1), lt_of_le_of_ne (not_lt.1 h) q.2.2.2.symm⟩,
        Sum.inr ⟨q.1, rfl, q.1.2⟩⟩
  left_inv q := by
    rcases q with ⟨⟨⟨i, j⟩, hij⟩, kl | kl⟩
    · rcases kl with ⟨⟨⟨a, b⟩, hab⟩, hrow, hcol⟩
      obtain rfl : a = i := hrow
      simp [hij]
    · rcases kl with ⟨⟨⟨a, b⟩, hab⟩, hrow, hcol⟩
      obtain rfl : a = j := hrow
      simp [not_lt_of_ge hij.le]
  right_inv q := by
    rcases q with ⟨kl, k⟩
    by_cases h : k.1 < kl.1.1
    · simp [h]
    · simp [h]

@[simp]
private theorem partialCorrelationJacobianOccurrenceEquiv_fst_inl
    (ij : strictLowerTriangle p)
    (kl : {kl : strictLowerTriangle p // kl.1.1 = ij.1.1 ∧ kl.1.2 < ij.1.2}) :
    (partialCorrelationJacobianOccurrenceEquiv ⟨ij, Sum.inl kl⟩).1 = kl := rfl

@[simp]
private theorem partialCorrelationJacobianOccurrenceEquiv_fst_inr
    (ij : strictLowerTriangle p)
    (kl : {kl : strictLowerTriangle p // kl.1.1 = ij.1.2 ∧ kl.1.2 < ij.1.2}) :
    (partialCorrelationJacobianOccurrenceEquiv ⟨ij, Sum.inr kl⟩).1 = kl := rfl

private theorem partialCorrelationPrefix_eq_prod_subtype
    (z : strictLowerTriangle p → ℝ) (i j : Fin p) :
    partialCorrelationPrefix z i j =
      ∏ kl : {kl : strictLowerTriangle p // kl.1.1 = i ∧ kl.1.2 < j},
        Real.sqrt (1 - z kl ^ 2) := by
  unfold partialCorrelationPrefix
  exact Finset.prod_subtype _ (by simp) _

private def partialCorrelationJacobianOccurrenceCoordinate :
    partialCorrelationJacobianOccurrence p → strictLowerTriangle p
  | ⟨_, Sum.inl kl⟩ => kl
  | ⟨_, Sum.inr kl⟩ => kl

private theorem prod_partialCorrelationPrefix_eq_prod_multiplicity
    (z : strictLowerTriangle p → ℝ) :
    (∏ ij : strictLowerTriangle p,
        partialCorrelationPrefix z ij.1.1 ij.1.2 *
          partialCorrelationPrefix z ij.1.2 ij.1.2) =
      ∏ q : partialCorrelationJacobianMultiplicity p, Real.sqrt (1 - z q.1 ^ 2) := by
  calc
    _ = ∏ q : partialCorrelationJacobianOccurrence p,
        Real.sqrt (1 - z (partialCorrelationJacobianOccurrenceCoordinate q) ^ 2) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro ij _
      rw [Fintype.prod_sum_type,
        partialCorrelationPrefix_eq_prod_subtype,
        partialCorrelationPrefix_eq_prod_subtype]
      simp only [partialCorrelationJacobianOccurrenceCoordinate]
    _ = _ := Fintype.prod_equiv partialCorrelationJacobianOccurrenceEquiv _ _ fun q ↦ by
      rcases q with ⟨ij, kl | kl⟩ <;>
        simp only [partialCorrelationJacobianOccurrenceCoordinate,
          partialCorrelationJacobianOccurrenceEquiv_fst_inl,
          partialCorrelationJacobianOccurrenceEquiv_fst_inr]

private theorem card_partialCorrelationJacobianMultiplicity
    (kl : strictLowerTriangle p) :
    Fintype.card {k : Fin p // kl.1.2 < k ∧ k ≠ kl.1.1} = p - kl.1.2.1 - 2 := by
  let A := {k : Fin p // kl.1.2 < k}
  calc
    Fintype.card {k : Fin p // kl.1.2 < k ∧ k ≠ kl.1.1} =
        Fintype.card {k : A // k.1 ≠ kl.1.1} :=
      Fintype.card_congr
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun k : Fin p ↦ kl.1.2 < k)
          (fun k ↦ k ≠ kl.1.1)).symm
    _ = Fintype.card A - Fintype.card {k : A // k.1 = kl.1.1} := by
      simpa only [not_not] using
        Fintype.card_subtype_compl (fun k : A ↦ k.1 = kl.1.1)
    _ = p - kl.1.2.1 - 2 := by
      have hcardA : Fintype.card A = p - 1 - kl.1.2.1 := by
        calc
          Fintype.card A = Fintype.card (Finset.Ioi kl.1.2) :=
            Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
          _ = (Finset.Ioi kl.1.2).card := Fintype.card_coe _
          _ = p - 1 - kl.1.2.1 := Fin.card_Ioi kl.1.2
      have hcardEq : Fintype.card {k : A // k.1 = kl.1.1} = 1 := by
        refine Fintype.card_eq_one_iff.mpr ⟨⟨⟨kl.1.1, kl.2⟩, rfl⟩, ?_⟩
        rintro ⟨k, hk⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hk
      rw [hcardA, hcardEq]
      omega

private theorem prod_partialCorrelationJacobianMultiplicity
    (z : strictLowerTriangle p → ℝ) :
    (∏ q : partialCorrelationJacobianMultiplicity p, Real.sqrt (1 - z q.1 ^ 2)) =
      ∏ kl : strictLowerTriangle p,
        Real.sqrt (1 - z kl ^ 2) ^ (p - kl.1.2.1 - 2) := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro kl _
  simp only [Finset.prod_const, Finset.card_univ,
    card_partialCorrelationJacobianMultiplicity]

private theorem partialCorrelationCholesky_apply_self_eq_prefix
    (z : strictLowerTriangle p → ℝ) (i : Fin p) :
    partialCorrelationCholesky z i i = partialCorrelationPrefix z i i := by
  rw [partialCorrelationCholesky_apply_self]
  unfold partialCorrelationPrefix
  apply Finset.prod_congr
  · ext kl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hkl ↦ ⟨hkl, hkl ▸ kl.2⟩, And.left⟩
  · simp

private theorem correlationCoordinatesOfPartialCorrelation_apply_eq
    (z : strictLowerTriangle p → ℝ) (ij : strictLowerTriangle p) :
    correlationCoordinatesOfPartialCorrelation z ij =
      (∑ k ∈ Finset.Iio ij.1.2,
        partialCorrelationCholesky z ij.1.1 k *
          partialCorrelationCholesky z ij.1.2 k) +
      z ij * partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2 := by
  simp only [correlationCoordinatesOfPartialCorrelation_apply]
  rw [partialCorrelationGram_def, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have hsum :
      (∑ k : Fin p, partialCorrelationCholesky z ij.1.1 k *
          partialCorrelationCholesky z ij.1.2 k) =
        ∑ k ∈ Finset.Iic ij.1.2, partialCorrelationCholesky z ij.1.1 k *
          partialCorrelationCholesky z ij.1.2 k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_Iic, not_le] at hk
    rw [partialCorrelationCholesky_apply_of_lt z hk, mul_zero]
  rw [hsum, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  rw [partialCorrelationCholesky_apply_of_gt z ij.2]
  rw [partialCorrelationCholesky_apply_self_eq_prefix]
  -- The entry lemma expands the prefix product; restore its named form before rearranging.
  change
    z ij * partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2 + _ = _
  ring

private def partialCorrelationLine (z : strictLowerTriangle p → ℝ)
    (kl : strictLowerTriangle p) (t : ℝ) : strictLowerTriangle p → ℝ :=
  z + t • (Pi.single kl 1 : strictLowerTriangle p → ℝ)

private theorem partialCorrelationPrefix_add_single_of_not_mem
    (z : strictLowerTriangle p → ℝ) (kl : strictLowerTriangle p) (t : ℝ) (i j : Fin p)
    (hkl : ¬ (kl.1.1 = i ∧ kl.1.2 < j)) :
    partialCorrelationPrefix (partialCorrelationLine z kl t) i j =
      partialCorrelationPrefix z i j := by
  unfold partialCorrelationPrefix
  apply Finset.prod_congr rfl
  intro ab hab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
  have hne : ab ≠ kl := by
    intro h
    exact hkl (h ▸ hab)
  simp [partialCorrelationLine, hne]

private theorem add_single_apply_of_ne (z : strictLowerTriangle p → ℝ)
    (kl ab : strictLowerTriangle p) (t : ℝ) (h : ab ≠ kl) :
    partialCorrelationLine z kl t ab = z ab := by
  simp [partialCorrelationLine, h]

private theorem add_single_apply_self (z : strictLowerTriangle p → ℝ)
    (kl : strictLowerTriangle p) (t : ℝ) :
    partialCorrelationLine z kl t kl = z kl + t := by
  simp [partialCorrelationLine]

private theorem partialCorrelationCholesky_line_of_lt_col
    (z : strictLowerTriangle p → ℝ) (kl : strictLowerTriangle p) (t : ℝ)
    {i k : Fin p} (hki : k < i) (hk : k < kl.1.2) :
    partialCorrelationCholesky (partialCorrelationLine z kl t) i k =
      partialCorrelationCholesky z i k := by
  rw [partialCorrelationCholesky_apply_of_gt _ hki,
    partialCorrelationCholesky_apply_of_gt _ hki]
  have hne : (⟨(i, k), hki⟩ : strictLowerTriangle p) ≠ kl := by
    intro h
    have hcol := congrArg (fun ab : strictLowerTriangle p ↦ ab.1.2) h
    exact hk.ne hcol
  rw [add_single_apply_of_ne z kl _ t hne]
  apply congrArg (z ⟨(i, k), hki⟩ * ·)
  exact partialCorrelationPrefix_add_single_of_not_mem z kl t _ _
    (fun h ↦ (not_lt_of_ge hk.le) h.2)

private theorem sum_partialCorrelationCholesky_line_of_le_col
    (z : strictLowerTriangle p → ℝ) (kl : strictLowerTriangle p) (t : ℝ)
    {i j : Fin p} (hji : j < i) (hjle : j ≤ kl.1.2) :
    (∑ k ∈ Finset.Iio j,
      partialCorrelationCholesky (partialCorrelationLine z kl t) i k *
        partialCorrelationCholesky (partialCorrelationLine z kl t) j k) =
      ∑ k ∈ Finset.Iio j,
        partialCorrelationCholesky z i k * partialCorrelationCholesky z j k := by
  apply Finset.sum_congr rfl
  intro k hk
  have hkj := Finset.mem_Iio.1 hk
  have hkkl : k < kl.1.2 := hkj.trans_le hjle
  rw [partialCorrelationCholesky_line_of_lt_col z kl t (hkj.trans hji) hkkl,
    partialCorrelationCholesky_line_of_lt_col z kl t hkj hkkl]

private theorem correlationCoordinatesOfPartialCorrelation_add_single_self
    (z : strictLowerTriangle p → ℝ) (ij : strictLowerTriangle p) (t : ℝ) :
    correlationCoordinatesOfPartialCorrelation (partialCorrelationLine z ij t) ij =
      correlationCoordinatesOfPartialCorrelation z ij +
        t * (partialCorrelationPrefix z ij.1.1 ij.1.2 *
          partialCorrelationPrefix z ij.1.2 ij.1.2) := by
  rw [correlationCoordinatesOfPartialCorrelation_apply_eq,
    correlationCoordinatesOfPartialCorrelation_apply_eq]
  rw [sum_partialCorrelationCholesky_line_of_le_col z ij t ij.2 le_rfl,
    add_single_apply_self,
    partialCorrelationPrefix_add_single_of_not_mem z ij t ij.1.1 ij.1.2
      (fun h ↦ (lt_irrefl _) h.2),
    partialCorrelationPrefix_add_single_of_not_mem z ij t ij.1.2 ij.1.2
      (fun h ↦ ij.2.ne h.1.symm)]
  ring

private def strictLowerTriangleKey (ij : strictLowerTriangle p) : Fin p ×ₗ Fin p :=
  toLex (ij.1.2, ij.1.1)

private theorem strictLowerTriangleKey_injective :
    Function.Injective (strictLowerTriangleKey (p := p)) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  simp only [strictLowerTriangleKey, toLex_inj, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.2 h.1)

private theorem differentiableAt_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    DifferentiableAt ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z :=
  ((contDiffOn_correlationCoordinatesOfPartialCorrelation.differentiableOn
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) z hz).differentiableAt
    (isOpen_setOf_forall_abs_lt_one.mem_nhds hz))

private theorem hasDerivAt_correlationCoordinatesOfPartialCorrelation_partialCorrelationLine
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    (ij kl : strictLowerTriangle p) :
    HasDerivAt
      (fun t : ℝ ↦ correlationCoordinatesOfPartialCorrelation (partialCorrelationLine z kl t) ij)
      (LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
        (Pi.basisFun ℝ (strictLowerTriangle p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z) ij kl) 0 := by
  let e : strictLowerTriangle p → ℝ := Pi.single kl 1
  have hline : HasDerivAt (partialCorrelationLine z kl) e 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) z).add
      ((hasDerivAt_id (x := (0 : ℝ))).smul_const e) using 1 <;>
      ext ab <;> simp [partialCorrelationLine, e]
  have hcomp :=
    (differentiableAt_correlationCoordinatesOfPartialCorrelation hz).hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hline (by simp [partialCorrelationLine])
  convert hasDerivAt_pi.1 hcomp ij using 1 <;>
    simp only [Function.comp_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      Pi.basisFun_apply, e, ContinuousLinearMap.coe_coe]

private theorem toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_diag
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    (ij : strictLowerTriangle p) :
    LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
        (Pi.basisFun ℝ (strictLowerTriangle p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z) ij ij =
      partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2 := by
  have hactual :=
    hasDerivAt_correlationCoordinatesOfPartialCorrelation_partialCorrelationLine hz ij ij
  have hformula : (fun t : ℝ ↦
      correlationCoordinatesOfPartialCorrelation (partialCorrelationLine z ij t) ij) =
      fun t ↦ correlationCoordinatesOfPartialCorrelation z ij +
        t * (partialCorrelationPrefix z ij.1.1 ij.1.2 *
          partialCorrelationPrefix z ij.1.2 ij.1.2) := by
    funext t
    exact correlationCoordinatesOfPartialCorrelation_add_single_self z ij t
  rw [hformula] at hactual
  have hexpected : HasDerivAt (fun t : ℝ ↦ correlationCoordinatesOfPartialCorrelation z ij +
      t * (partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2))
      (partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2) 0 := by
    exact (hasDerivAt_mul_const (partialCorrelationPrefix z ij.1.1 ij.1.2 *
      partialCorrelationPrefix z ij.1.2 ij.1.2)).const_add
        (correlationCoordinatesOfPartialCorrelation z ij)
  exact hactual.unique hexpected

private theorem correlationCoordinatesOfPartialCorrelation_add_single_of_key_lt
    (z : strictLowerTriangle p → ℝ) (ij kl : strictLowerTriangle p) (t : ℝ)
    (hkey : strictLowerTriangleKey ij < strictLowerTriangleKey kl) :
    correlationCoordinatesOfPartialCorrelation (partialCorrelationLine z kl t) ij =
      correlationCoordinatesOfPartialCorrelation z ij := by
  have hne : ij ≠ kl := by
    intro h
    subst kl
    exact (lt_irrefl _ hkey)
  rw [strictLowerTriangleKey, strictLowerTriangleKey, Prod.Lex.toLex_lt_toLex] at hkey
  have hjle : ij.1.2 ≤ kl.1.2 := hkey.elim (fun h ↦ h.le) (fun h ↦ h.1.le)
  rw [correlationCoordinatesOfPartialCorrelation_apply_eq,
    correlationCoordinatesOfPartialCorrelation_apply_eq]
  rw [sum_partialCorrelationCholesky_line_of_le_col z kl t ij.2 hjle,
    add_single_apply_of_ne z kl ij t hne,
    partialCorrelationPrefix_add_single_of_not_mem z kl t ij.1.1 ij.1.2
      (fun h ↦ (not_lt_of_ge hjle) h.2),
    partialCorrelationPrefix_add_single_of_not_mem z kl t ij.1.2 ij.1.2
      (fun h ↦ (not_lt_of_ge hjle) h.2)]

private theorem toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_of_key_lt
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    {ij kl : strictLowerTriangle p}
    (hkey : strictLowerTriangleKey ij < strictLowerTriangleKey kl) :
    LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
        (Pi.basisFun ℝ (strictLowerTriangle p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z) ij kl = 0 := by
  have hactual :=
    hasDerivAt_correlationCoordinatesOfPartialCorrelation_partialCorrelationLine hz ij kl
  have hconstant : (fun t : ℝ ↦
      correlationCoordinatesOfPartialCorrelation (partialCorrelationLine z kl t) ij) =
      fun _ ↦ correlationCoordinatesOfPartialCorrelation z ij := by
    funext t
    exact correlationCoordinatesOfPartialCorrelation_add_single_of_key_lt z ij kl t hkey
  rw [hconstant] at hactual
  exact hactual.unique (hasDerivAt_const (x := (0 : ℝ)) _)

private theorem blockTriangular_toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    (LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
      (Pi.basisFun ℝ (strictLowerTriangle p))
      (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z)).BlockTriangular
      (OrderDual.toDual ∘ strictLowerTriangleKey) := by
  intro ij kl h
  simp only [Function.comp_apply, OrderDual.toDual_lt_toDual] at h
  exact toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_of_key_lt hz h

private theorem abs_det_fderiv_correlationCoordinatesOfPartialCorrelation_eq_prefix
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det| =
      ∏ ij : strictLowerTriangle p,
        partialCorrelationPrefix z ij.1.1 ij.1.2 *
          partialCorrelationPrefix z ij.1.2 ij.1.2 := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ (strictLowerTriangle p)),
    (blockTriangular_toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation hz).det_eq_prod_diag
      (OrderDual.toDual.injective.comp strictLowerTriangleKey_injective),
    Finset.prod_congr rfl fun ij (_ : ij ∈ Finset.univ) ↦
      toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_diag hz ij,
    abs_of_pos]
  exact Finset.prod_pos fun ij _ ↦ mul_pos
    (Finset.prod_pos fun kl hkl ↦ Real.sqrt_pos.2 <| sub_pos.2 <|
      (sq_lt_one_iff_abs_lt_one _).2 (hz kl))
    (Finset.prod_pos fun kl hkl ↦ Real.sqrt_pos.2 <| sub_pos.2 <|
      (sq_lt_one_iff_abs_lt_one _).2 (hz kl))

/-- **Jacobian of the partial-correlation map.** For zero-based column `j`, each partial
correlation contributes the factor `√(1 - z²)` with exponent `p - j - 2`. -/
theorem abs_det_fderiv_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det| =
      ∏ ij : strictLowerTriangle p,
        Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2) := by
  rw [abs_det_fderiv_correlationCoordinatesOfPartialCorrelation_eq_prefix hz,
    prod_partialCorrelationPrefix_eq_prod_multiplicity,
    prod_partialCorrelationJacobianMultiplicity]
/-- The Cholesky factor of a positive-definite correlation matrix has unit-length rows. -/
private theorem sum_sq_cholesky_correlationMatrix {x : strictLowerTriangle p → ℝ}
    (hx : x ∈ posDefCorrelationRegion p) (i : Fin p) :
    ∑ j, (cholesky ⟨correlationMatrix p x, mem_posDefCorrelationRegion.1 hx⟩).1 i j ^ 2 = 1 := by
  have h := congrFun (congrFun
    (cholesky_mul_transpose ⟨correlationMatrix p x, mem_posDefCorrelationRegion.1 hx⟩) i) i
  simpa [Matrix.mul_apply, sq] using h

/-- The partial correlations of the Cholesky factor of a positive-definite correlation matrix
lie in the open cube. -/
theorem abs_partialCorrelationOfCholesky_cholesky_lt_one {x : strictLowerTriangle p → ℝ}
    (hx : x ∈ posDefCorrelationRegion p) (ij : strictLowerTriangle p) :
    |Matrix.partialCorrelationOfCholesky
      (cholesky ⟨correlationMatrix p x, mem_posDefCorrelationRegion.1 hx⟩).1 ij| < 1 :=
  abs_partialCorrelationOfCholesky_lt_one (fun i ↦ ((cholesky _).2.2 i).ne')
    (sum_sq_cholesky_correlationMatrix hx) ij

/-- The partial correlations of the Cholesky factor of a positive-definite correlation matrix
are sent back to that matrix by the partial-correlation forward map. -/
@[simp]
theorem correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCholesky_cholesky
    {x : strictLowerTriangle p → ℝ} (hx : x ∈ posDefCorrelationRegion p) :
    correlationCoordinatesOfPartialCorrelation
      (Matrix.partialCorrelationOfCholesky
        (cholesky ⟨correlationMatrix p x, mem_posDefCorrelationRegion.1 hx⟩).1) = x := by
  funext ⟨⟨i, j⟩, hji⟩
  rw [correlationCoordinatesOfPartialCorrelation_apply, partialCorrelationGram_def,
    partialCorrelationCholesky_partialCorrelationOfCholesky (cholesky _).2.1 (cholesky _).2.2
      (sum_sq_cholesky_correlationMatrix hx), cholesky_mul_transpose]
  exact coe_correlationMatrix_apply_of_gt x hji

open scoped Classical in
/-- The inverse of the partial-correlation forward map: the partial correlations read off the
Cholesky factor of the correlation matrix with coordinates `x`. Outside the positive-definite
correlation region, where there is no Cholesky factor, it is `0`. -/
def partialCorrelationOfCorrelationCoordinates (x : strictLowerTriangle p → ℝ) :
    strictLowerTriangle p → ℝ :=
  if hx : x ∈ posDefCorrelationRegion p then
    Matrix.partialCorrelationOfCholesky
      (cholesky ⟨correlationMatrix p x, mem_posDefCorrelationRegion.1 hx⟩).1
  else 0

/-- On the positive-definite correlation region, the inverse map reads the partial correlations
off the Cholesky factor. -/
theorem partialCorrelationOfCorrelationCoordinates_of_mem {x : strictLowerTriangle p → ℝ}
    (hx : x ∈ posDefCorrelationRegion p) :
    partialCorrelationOfCorrelationCoordinates x =
      Matrix.partialCorrelationOfCholesky
        (cholesky ⟨correlationMatrix p x, mem_posDefCorrelationRegion.1 hx⟩).1 := by
  simp only [partialCorrelationOfCorrelationCoordinates, hx, ↓reduceDIte]

/-- Outside the positive-definite correlation region, the inverse map is `0`. -/
@[simp]
theorem partialCorrelationOfCorrelationCoordinates_of_notMem {x : strictLowerTriangle p → ℝ}
    (hx : x ∉ posDefCorrelationRegion p) : partialCorrelationOfCorrelationCoordinates x = 0 := by
  simp only [partialCorrelationOfCorrelationCoordinates, hx, ↓reduceDIte]

/-- The inverse map sends the positive-definite correlation region into the open cube. -/
theorem mapsTo_partialCorrelationOfCorrelationCoordinates :
    MapsTo (partialCorrelationOfCorrelationCoordinates (p := p)) (posDefCorrelationRegion p)
      {z | ∀ ij, |z ij| < 1} := fun _ hx ij ↦ by
  rw [partialCorrelationOfCorrelationCoordinates_of_mem hx]
  exact abs_partialCorrelationOfCholesky_cholesky_lt_one hx ij

/-- On the positive-definite correlation region, the forward map undoes the inverse map. -/
@[simp]
theorem correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCorrelationCoordinates
    {x : strictLowerTriangle p → ℝ} (hx : x ∈ posDefCorrelationRegion p) :
    correlationCoordinatesOfPartialCorrelation (partialCorrelationOfCorrelationCoordinates x) =
      x := by
  rw [partialCorrelationOfCorrelationCoordinates_of_mem hx]
  exact correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCholesky_cholesky hx

/-- On the open cube, the inverse map undoes the forward map. -/
@[simp]
theorem partialCorrelationOfCorrelationCoordinates_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    partialCorrelationOfCorrelationCoordinates (correlationCoordinatesOfPartialCorrelation z) =
      z := by
  have hx := mapsTo_correlationCoordinatesOfPartialCorrelation hz
  exact injOn_correlationCoordinatesOfPartialCorrelation
    (mapsTo_partialCorrelationOfCorrelationCoordinates hx) hz
    (correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCorrelationCoordinates hx)

/-- The Cholesky partial-correlation map inverts the partial-correlation forward map between
the open cube and the positive-definite correlation region. -/
theorem invOn_partialCorrelationOfCorrelationCoordinates :
    InvOn (partialCorrelationOfCorrelationCoordinates (p := p))
      correlationCoordinatesOfPartialCorrelation {z | ∀ ij, |z ij| < 1}
      (posDefCorrelationRegion p) :=
  ⟨fun _ hz ↦
      partialCorrelationOfCorrelationCoordinates_correlationCoordinatesOfPartialCorrelation hz,
    fun _ hx ↦
      correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCorrelationCoordinates hx⟩

/-- The partial-correlation forward map is a bijection from the open cube onto the
positive-definite correlation region. -/
theorem bijOn_correlationCoordinatesOfPartialCorrelation :
    BijOn (correlationCoordinatesOfPartialCorrelation (p := p)) {z | ∀ ij, |z ij| < 1}
      (posDefCorrelationRegion p) :=
  ⟨mapsTo_correlationCoordinatesOfPartialCorrelation,
    injOn_correlationCoordinatesOfPartialCorrelation, fun _ hx ↦
      ⟨_, abs_partialCorrelationOfCholesky_cholesky_lt_one hx,
        correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCholesky_cholesky hx⟩⟩

/-- The image of the open cube under the partial-correlation forward map is the
positive-definite correlation region. -/
theorem image_correlationCoordinatesOfPartialCorrelation :
    correlationCoordinatesOfPartialCorrelation ''
        {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} = posDefCorrelationRegion p :=
  bijOn_correlationCoordinatesOfPartialCorrelation.image_eq
/-- Every off-diagonal entry of a positive-definite correlation matrix lies in `(-1, 1)`: its
`2 × 2` principal minor `1 - x (i, j) ^ 2` is positive. -/
theorem abs_lt_one_of_mem_posDefCorrelationRegion {x : strictLowerTriangle p → ℝ}
    (hx : x ∈ posDefCorrelationRegion p) (ij : strictLowerTriangle p) : |x ij| < 1 := by
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hij.ne, hij.ne']
  have hdet := (hx.submatrix hinj).det_pos
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    coe_correlationMatrix_apply_self, coe_correlationMatrix_apply_of_gt x hij,
    coe_correlationMatrix_apply_of_lt x hij] at hdet
  rw [abs_lt]
  constructor <;> nlinarith

variable (p) in
/-- The positive-definite region lies in the open cube `(-1, 1) ^ J`. -/
theorem posDefCorrelationRegion_subset_pi :
    posDefCorrelationRegion p ⊆ univ.pi fun _ => Ioo (-1) 1 :=
  fun _ hx ij _ => abs_lt.1 (abs_lt_one_of_mem_posDefCorrelationRegion hx ij)

variable (p) in
theorem isBounded_posDefCorrelationRegion : Bornology.IsBounded (posDefCorrelationRegion p) :=
  (Metric.isBounded_Icc (-1 : strictLowerTriangle p → ℝ) 1).subset fun x hx => by
    have h := posDefCorrelationRegion_subset_pi p hx
    exact ⟨fun ij => (h ij trivial).1.le, fun ij => (h ij trivial).2.le⟩

variable (p) in
/-- The positive-definite region has positive volume: it is open and contains the origin. -/
theorem volume_posDefCorrelationRegion_pos : 0 < volume (posDefCorrelationRegion p) :=
  (isOpen_posDefCorrelationRegion p).measure_pos _ ⟨0, zero_mem_posDefCorrelationRegion p⟩

variable (p) in
/-- The positive-definite region has finite volume: it is bounded. -/
theorem volume_posDefCorrelationRegion_lt_top : volume (posDefCorrelationRegion p) < ⊤ :=
  (isBounded_posDefCorrelationRegion p).measure_lt_top

variable (p) in
/-- The positive-definite correlation matrices have `TauCeti.correlationLebesgue` measure equal
to the volume of their coordinate region. -/
theorem correlationLebesgue_setOf_posDef :
    correlationLebesgue p {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef} =
      volume (posDefCorrelationRegion p) :=
  correlationLebesgue_apply _

variable (p) in
/-- The closure of the positive-definite region is the region of positive-semidefinite
correlation matrices: shrinking the coordinates of a positive-semidefinite correlation matrix
towards the origin mixes in a positive multiple of the identity. -/
theorem closure_posDefCorrelationRegion :
    closure (posDefCorrelationRegion p) =
      {x | (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).PosSemidef} := by
  refine Subset.antisymm ?_ fun x hx => ?_
  · refine closure_minimal (fun x hx => hx.posSemidef) ?_
    exact isClosed_setOfPred_posSemidef.preimage
      (continuous_subtype_val.comp (correlationMatrix p).continuous)
  · have hmem : ∀ᶠ t in 𝓝[<] (1 : ℝ), t • x ∈ posDefCorrelationRegion p := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
      rw [mem_posDefCorrelationRegion, coe_correlationMatrix_smul, add_comm]
      exact (Matrix.PosDef.one.smul (sub_pos.2 ht.2)).add_posSemidef (hx.smul ht.1.le)
    have hcont : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
    have htends : Tendsto (fun t : ℝ => t • x) (𝓝[<] 1) (𝓝 x) :=
      (hcont.tendsto' 1 x (one_smul ℝ x)).mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto htends hmem

variable (p) in
/-- The frontier of the positive-definite region consists of the coordinates of the singular
positive-semidefinite correlation matrices. -/
theorem frontier_posDefCorrelationRegion :
    frontier (posDefCorrelationRegion p) =
      {x | (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
        (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det = 0} := by
  rw [frontier, closure_posDefCorrelationRegion, (isOpen_posDefCorrelationRegion p).interior_eq]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_posDefCorrelationRegion]
  exact and_congr_right fun hx => by rw [hx.posDef_iff_det_ne_zero, not_not]

variable (p) in
/-- The frontier of the positive-definite region is Lebesgue-null, being the frontier of a convex
set. -/
theorem volume_frontier_posDefCorrelationRegion :
    volume (frontier (posDefCorrelationRegion p)) = 0 :=
  (convex_posDefCorrelationRegion p).addHaar_frontier _

/-! ### Invariance under permutations and sign changes

Conjugating a unit-diagonal symmetric matrix by a permutation matrix or by a diagonal sign matrix
gives a unit-diagonal symmetric matrix whose coordinates are those of the original, permuted and
multiplied by signs.
Such signed permutations of the coordinates preserve Lebesgue measure. -/

/-- A measurable self-map of the symmetric matrices that acts on the values of
`TauCeti.correlationMatrix` through a permutation and sign change of the coordinates preserves
`TauCeti.correlationLebesgue`. -/
private theorem map_correlationLebesgue_of_signedPerm
    {f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hf : Measurable f) (e : strictLowerTriangle p ≃ strictLowerTriangle p)
    (c : strictLowerTriangle p → ℝ) (hc : ∀ ij, |c ij| = 1)
    (h : ∀ x, f (correlationMatrix p x) = correlationMatrix p fun ij => c ij * x (e ij)) :
    (correlationLebesgue p).map f = correlationLebesgue p := by
  have hR := (correlationMatrix p).continuous.measurable
  have hg := volume_preserving_signedPerm e c hc
  have hcomp : f ∘ correlationMatrix p =
      correlationMatrix p ∘ fun (x : strictLowerTriangle p → ℝ) ij => c ij * x (e ij) :=
    funext h
  rw [correlationLebesgue, Measure.map_map hf hR, hcomp, ← Measure.map_map hR hg.measurable,
    hg.map_eq]

/-- The action of a permutation of the indices on the strictly lower positions: `(i, j)` goes to
the sorted pair `(max (σ i) (σ j), min (σ i) (σ j))`. -/
private def permStrictLower (σ : Equiv.Perm (Fin p)) (ij : strictLowerTriangle p) :
    strictLowerTriangle p :=
  ⟨(max (σ ij.1.1) (σ ij.1.2), min (σ ij.1.1) (σ ij.1.2)),
    min_lt_max.2 (σ.injective.ne ij.2.ne')⟩

private theorem permStrictLower_inv (σ : Equiv.Perm (Fin p)) (ij : strictLowerTriangle p) :
    permStrictLower σ⁻¹ (permStrictLower σ ij) = ij := by
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  refine Subtype.ext ?_
  dsimp only at hij
  rcases (σ.injective.ne hij.ne').lt_or_gt with h | h
  · simp [permStrictLower, max_eq_right h.le, min_eq_left h.le, max_eq_right hij.le,
      min_eq_left hij.le]
  · simp [permStrictLower, max_eq_left h.le, min_eq_right h.le, max_eq_left hij.le,
      min_eq_right hij.le]

/-- `TauCeti.permStrictLower` as a permutation of the strictly lower positions. -/
private def permStrictLowerEquiv (σ : Equiv.Perm (Fin p)) :
    strictLowerTriangle p ≃ strictLowerTriangle p where
  toFun := permStrictLower σ
  invFun := permStrictLower σ⁻¹
  left_inv := permStrictLower_inv σ
  right_inv ij := by simpa using permStrictLower_inv σ⁻¹ ij

variable (p) in
/-- `TauCeti.correlationLebesgue` is invariant under simultaneous permutation of rows and columns:
conjugation by a permutation matrix preserves it. -/
theorem map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue
    (σ : Equiv.Perm (Fin p)) :
    (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ)) =
      correlationLebesgue p := by
  refine map_correlationLebesgue_of_signedPerm
    (LinearMap.continuous_of_finiteDimensional _).measurable
    (permStrictLowerEquiv σ) 1 (fun _ => by simp) fun x => ?_
  rw [← correlationMatrix_correlationCoordinates (A := Matrix.symmetricCongruenceLinearMap _ _)
    fun i => by simp [-Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply]]
  congr 1
  funext ij
  simp [-Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply,
    coe_correlationMatrix_apply_of_ne x (σ.injective.ne ij.2.ne'),
    permStrictLowerEquiv, permStrictLower]

variable (p) in
/-- `TauCeti.correlationLebesgue` is invariant under sign changes of the coordinate axes:
conjugation by a diagonal matrix with entries `±1` preserves it. -/
theorem map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue {s : Fin p → ℝ}
    (hs : ∀ i, |s i| = 1) :
    (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s)) =
      correlationLebesgue p := by
  have hcoe : ∀ (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (i j : Fin p),
      (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s) A : Matrix (Fin p) (Fin p) ℝ) i j =
        s i * (A : Matrix (Fin p) (Fin p) ℝ) i j * s j := fun A i j => by
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine map_correlationLebesgue_of_signedPerm
    (LinearMap.continuous_of_finiteDimensional _).measurable
    (Equiv.refl _) (fun ij => s ij.1.1 * s ij.1.2) (fun ij => by simp [abs_mul, hs])
    fun x => ?_
  have hsq : ∀ i, s i * s i = 1 := fun i => by rw [← abs_mul_abs_self, hs, one_mul]
  rw [← correlationMatrix_correlationCoordinates (A := Matrix.symmetricCongruenceLinearMap _ _)
    fun i => by simp [hcoe, hsq]]
  congr 1
  funext ij
  simp [hcoe, ij.2]
  ring

end TauCeti
