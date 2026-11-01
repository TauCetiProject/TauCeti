/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.Analysis.Matrix.PartialCorrelation
public import Mathlib.Topology.Algebra.ContinuousAffineMap
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Matrix.Order

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
* `TauCeti.coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation` — reconstruction of
  partial-correlation Gram matrices from their correlation coordinates on the closed cube.
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
  (convex_setOf_posDef.affine_preimage
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
    exact Matrix.posSemidef_is_closed.preimage
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
