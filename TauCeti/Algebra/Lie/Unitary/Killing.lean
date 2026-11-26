/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Unitary
import Mathlib.Data.Matrix.Basis
import TauCeti.Algebra.Lie.IndefiniteUnitary
import TauCeti.Algebra.Lie.CartanInvolution.Matrix
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# The Killing form, centre and derived algebra of `𝔲(n)`

Let `𝔲(n) = TauCeti.unitaryLieAlgebra ι` be the real Lie algebra of skew-Hermitian `n × n` complex
matrices, `n = card ι`, the Lie algebra of the unitary group `U(n)`. This file computes the
Lie-algebra data that the decomposition of a compact connected Lie group into a torus and a
compact semisimple factor reads off, for `G = U(n)`:

* the centre of `𝔲(n)` is the line `iℝ · 1` of imaginary scalar matrices
  (`TauCeti.mem_center_unitaryLieAlgebra_iff`);
* the derived algebra `[𝔲(n), 𝔲(n)]` is `𝔰𝔲(n)`, the trace-free skew-Hermitian matrices
  (`TauCeti.mem_derivedSeries_one_unitaryLieAlgebra_iff`), and `𝔲(n)` is the direct sum of the two
  (`TauCeti.isCompl_center_derivedSeries_one_unitaryLieAlgebra`);
* the Killing form is `κ(X, Y) = Re (2 n tr(X Y) - 2 tr X tr Y)`
  (`TauCeti.killingForm_unitaryLieAlgebra_apply`);
* it is negative semidefinite (`TauCeti.killingForm_unitaryLieAlgebra_self_nonpos`), with kernel
  exactly the centre (`TauCeti.killingForm_unitaryLieAlgebra_self_eq_zero_iff`): it vanishes at
  `X = i · 1`, where `2 n tr(X²) - 2 (tr X)² = -2 n² + 2 n² = 0`, and is negative at every
  noncentral `X` (`TauCeti.killingForm_unitaryLieAlgebra_self_neg`).

Reindexing along `ι ≃ ι ⊕ ∅` identifies `𝔲(n)` with the indefinite unitary Lie algebra `𝔲(n, 0)`,
whose Killing form is `TauCeti.killingForm_indefiniteUnitaryLieAlgebra_apply`. Its trace-free part
`𝔰𝔲(n, 0)` has nondegenerate Killing form, hence is perfect
(`TauCeti.derivedSeries_one_eq_top_of_isKilling`), which gives `𝔰𝔲(n) ⊆ [𝔲(n), 𝔲(n)]`; the
reverse inclusion holds because commutators are trace-free.

The sign of the Killing form comes from the positive-definite invariant form `Re tr(X Yᴴ)`
(`TauCeti.reTraceForm`) on `𝔲(n)`: for such a form, `ad X` is skew-adjoint, so `tr((ad X)²) ≤ 0`
with equality exactly when `ad X = 0`
(`LinearMap.BilinForm.killingForm_self_nonpos_of_posDef`,
`LinearMap.BilinForm.killingForm_self_eq_zero_iff_of_posDef`). The centre is computed directly: a
matrix commuting with every skew-Hermitian matrix commutes with every matrix, since every matrix is
`-i (i ℜ M) + i ℑ M` with `i ℜ M` and `i ℑ M` skew-Hermitian, so it is scalar
(`Matrix.mem_range_scalar_of_commute_single`), and a skew-Hermitian scalar is imaginary.

Compactness of `U(n)` is what makes the Killing form semidefinite: on the Lie algebra `𝔰𝔩(2, ℝ)` of
the noncompact `SL(2, ℝ)`, the Killing form is positive at `diag(1, -1)`.

## Main results

* `TauCeti.killingForm_unitaryLieAlgebra_apply`: the Killing form of `𝔲(n)`.
* `TauCeti.mem_center_unitaryLieAlgebra_iff`: the centre of `𝔲(n)` is `iℝ · 1`.
* `TauCeti.mem_derivedSeries_one_unitaryLieAlgebra_iff`: the derived algebra of `𝔲(n)` is `𝔰𝔲(n)`.
* `TauCeti.isCompl_center_derivedSeries_one_unitaryLieAlgebra`: `𝔲(n) = iℝ · 1 ⊕ 𝔰𝔲(n)`.
* `TauCeti.killingForm_unitaryLieAlgebra_self_nonpos`,
  `TauCeti.killingForm_unitaryLieAlgebra_self_eq_zero_iff`,
  `TauCeti.killingForm_unitaryLieAlgebra_self_neg`: the Killing form of `𝔲(n)` is negative
  semidefinite with kernel the centre.

## References

* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, Proposition 8.33.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter I.
-/

public section

noncomputable section

open LieAlgebra LieAlgebra.Orthogonal Matrix Complex
open scoped ComplexStarModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing along `ι ≃ ι ⊕ Empty`, as an isomorphism of real algebras. -/
private def reindexSumEmpty : Matrix ι ι ℂ ≃ₐ[ℝ] Matrix (ι ⊕ Empty) (ι ⊕ Empty) ℂ :=
  reindexAlgEquiv ℝ ℂ (Equiv.sumEmpty ι Empty).symm

omit [Fintype ι] in
private theorem indefiniteDiagonal_empty : indefiniteDiagonal ι Empty ℂ = 1 := by
  rw [indefiniteDiagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i
  · rfl
  · exact i.elim

private theorem map_unitaryLieAlgebra :
    (unitaryLieAlgebra ι).map (reindexSumEmpty (ι := ι)).toLieEquiv.toLieHom =
      indefiniteUnitaryLieAlgebra ι Empty := by
  ext Y
  simp only [LieSubalgebra.mem_map, mem_indefiniteUnitaryLieAlgebra_iff, indefiniteDiagonal_empty,
    Matrix.mul_one, Matrix.one_mul]
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [mem_unitaryLieAlgebra_iff] at hX
    simp [reindexSumEmpty, hX, submatrix_neg]
  · intro hY
    refine ⟨reindexSumEmpty.symm Y, ?_, by simp⟩
    rw [mem_unitaryLieAlgebra_iff]
    simp [reindexSumEmpty, hY, submatrix_neg]

/-- `𝔲(n)` is `𝔲(n, 0)`. -/
private def unitaryLieAlgebraEquivIndefinite :
    unitaryLieAlgebra ι ≃ₗ⁅ℝ⁆ indefiniteUnitaryLieAlgebra ι Empty :=
  (reindexSumEmpty (ι := ι)).toLieEquiv.ofSubalgebras _ _ map_unitaryLieAlgebra

private theorem trace_reindexSumEmpty (X : Matrix ι ι ℂ) :
    (reindexSumEmpty X).trace = X.trace := by
  simp [reindexSumEmpty, Matrix.trace, Fintype.sum_sum_type]

/-- **The Killing form of `𝔲(n)`** is the real part of that of `𝔤𝔩_n(ℂ)`:
`κ(X, Y) = Re (2 n tr(X Y) - 2 tr X tr Y)` for `n = card ι`. -/
theorem killingForm_unitaryLieAlgebra_apply (X Y : unitaryLieAlgebra ι) :
    killingForm ℝ (unitaryLieAlgebra ι) X Y =
      (2 * Fintype.card ι * ((X : Matrix ι ι ℂ) * Y).trace -
        2 * (X : Matrix ι ι ℂ).trace * (Y : Matrix ι ι ℂ).trace).re := by
  rw [← killingForm_of_equiv_apply unitaryLieAlgebraEquivIndefinite,
    killingForm_indefiniteUnitaryLieAlgebra_apply]
  simp only [unitaryLieAlgebraEquivIndefinite, LieEquiv.ofSubalgebras_apply,
    AlgEquiv.toLieEquiv_apply, ← map_mul, trace_reindexSumEmpty, Fintype.card_sum,
    Fintype.card_empty, add_zero]

/-! ### The centre -/

omit [DecidableEq ι] in
/-- A matrix commuting with every skew-Hermitian matrix commutes with every matrix: for the
Hermitian real and imaginary parts `ℜ M` and `ℑ M` of `M`, the matrices `i ℜ M` and `i ℑ M` are
skew-Hermitian, and `M = -i (i ℜ M) + i ℑ M`. -/
private theorem commute_of_forall_conjTranspose_eq_neg {X : Matrix ι ι ℂ}
    (h : ∀ Y : Matrix ι ι ℂ, Yᴴ = -Y → Commute Y X) (M : Matrix ι ι ℂ) : Commute M X := by
  have hskew (H : selfAdjoint (Matrix ι ι ℂ)) : (I • (H : Matrix ι ι ℂ))ᴴ = -(I • H) := by
    rw [conjTranspose_smul, ← star_eq_conjTranspose, H.property.star_eq, Complex.star_def,
      conj_I, neg_smul]
  have hM : M = (-I) • (I • (ℜ M : Matrix ι ι ℂ)) + I • (ℑ M : Matrix ι ι ℂ) := by
    rw [smul_smul, neg_mul, I_mul_I, neg_neg, one_smul, realPart_add_I_smul_imaginaryPart]
  rw [hM]
  exact ((h _ (hskew _)).smul_left _).add_left (h _ (hskew _))

/-- A scalar matrix of `𝔲(n)` is central. -/
private theorem mem_center_of_coe_eq_smul_one {X : unitaryLieAlgebra ι} {c : ℂ}
    (h : (X : Matrix ι ι ℂ) = c • 1) : X ∈ center ℝ (unitaryLieAlgebra ι) := by
  rw [LieModule.mem_maxTrivSubmodule]
  intro Y
  ext1
  simp [LieSubalgebra.coe_bracket, Ring.lie_def, h]

/-- **The centre of `𝔲(n)`** is the line `iℝ · 1` of imaginary scalar matrices. -/
theorem mem_center_unitaryLieAlgebra_iff {X : unitaryLieAlgebra ι} :
    X ∈ center ℝ (unitaryLieAlgebra ι) ↔ ∃ t : ℝ, (X : Matrix ι ι ℂ) = (t * I) • 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ mem_center_of_coe_eq_smul_one ht⟩
  rw [LieModule.mem_maxTrivSubmodule] at h
  have hc (Y : Matrix ι ι ℂ) (hY : Yᴴ = -Y) : Commute Y X := by
    have := congrArg Subtype.val (h ⟨Y, mem_unitaryLieAlgebra_iff.2 hY⟩)
    exact (by simpa [LieSubalgebra.coe_bracket, Ring.lie_def, sub_eq_zero] using this :
      Y * X = X * Y)
  obtain ⟨c, hcX⟩ := mem_range_scalar_of_commute_single fun _ _ _ ↦
    commute_of_forall_conjTranspose_eq_neg hc _
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hX := congrFun (congrFun (mem_unitaryLieAlgebra_iff.1 X.property) i) i
  rw [← hcX] at hX
  simp only [conjTranspose_apply, scalar_apply, diagonal_apply_eq] at hX
  refine ⟨c.im, ?_⟩
  rw [← hcX, scalar_apply, ← smul_one_eq_diagonal]
  congr 1
  apply Complex.ext <;> simp [Complex.ext_iff] at hX ⊢
  linarith

/-! ### The derived algebra -/

/-- **The derived algebra of `𝔲(n)`** is `𝔰𝔲(n)`, the trace-free matrices of `𝔲(n)`. -/
theorem mem_derivedSeries_one_unitaryLieAlgebra_iff {X : unitaryLieAlgebra ι} :
    X ∈ derivedSeries ℝ (unitaryLieAlgebra ι) 1 ↔ (X : Matrix ι ι ℂ).trace = 0 := by
  constructor
  · intro hX
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero] at hX
    have hX' : X ∈ (⁅(⊤ : LieIdeal ℝ (unitaryLieAlgebra ι)), ⊤⁆ :
      LieIdeal ℝ (unitaryLieAlgebra ι)).toSubmodule := hX
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hX'
    clear hX
    induction hX' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      rw [LieSubalgebra.coe_bracket]
      exact matrix_trace_commutator_zero _ _ _ _
    | zero => simp
    | add x y _ _ hx hy => simp [trace_add, hx, hy]
    | smul r x _ hx => simp [trace_smul, hx]
  · intro h
    let f : specialIndefiniteUnitaryLieAlgebra ι Empty →ₗ⁅ℝ⁆ unitaryLieAlgebra ι :=
      unitaryLieAlgebraEquivIndefinite.symm.toLieHom.comp
        (LieSubalgebra.inclusion (specialIndefiniteUnitaryLieAlgebra_le (p := ι) (q := Empty)))
    let Y : specialIndefiniteUnitaryLieAlgebra ι Empty :=
      ⟨unitaryLieAlgebraEquivIndefinite X, mem_specialIndefiniteUnitaryLieAlgebra_iff.2
        ⟨(unitaryLieAlgebraEquivIndefinite X).property, by
          simpa [unitaryLieAlgebraEquivIndefinite, trace_reindexSumEmpty] using h⟩⟩
    have hY : Y ∈ derivedSeries ℝ (specialIndefiniteUnitaryLieAlgebra ι Empty) 1 := by
      rw [derivedSeries_one_eq_top_of_isKilling]
      exact LieSubmodule.mem_top _
    have hfY : f Y = X :=
      unitaryLieAlgebraEquivIndefinite.symm_apply_apply X
    exact hfY ▸ LieIdeal.derivedSeries_map_le (f := f) 1 (LieIdeal.mem_map hY)

/-! ### The sign of the Killing form -/

/-- The real trace form `(X, Y) ↦ Re tr(X Yᴴ)` restricted to `𝔲(n)`. -/
private def unitaryReTraceForm : LinearMap.BilinForm ℝ (unitaryLieAlgebra ι) :=
  (reTraceForm ℂ ι ι).compl₁₂ (unitaryLieAlgebra ι).incl.toLinearMap
    (unitaryLieAlgebra ι).incl.toLinearMap

private theorem isSymm_unitaryReTraceForm : (unitaryReTraceForm (ι := ι)).IsSymm :=
  ⟨fun X Y ↦ (isSymm_reTraceForm ℂ ι ι).eq (X : Matrix ι ι ℂ) Y⟩

private theorem posDef_unitaryReTraceForm : (unitaryReTraceForm (ι := ι)).toQuadraticMap.PosDef :=
  fun X hX ↦ posDef_reTraceForm ℂ ι ι (X : Matrix ι ι ℂ) (by simpa using hX)

/-- `Re tr(X Yᴴ)` is invariant on `𝔲(n)`, since `ad X` has adjoint `ad Xᴴ = -ad X`. -/
private theorem lieInvariant_unitaryReTraceForm :
    (unitaryReTraceForm (ι := ι)).lieInvariant (unitaryLieAlgebra ι) := by
  intro X Y Z
  simp only [unitaryReTraceForm, LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap,
    LieSubalgebra.coe_incl, LieSubalgebra.coe_bracket]
  rw [reTraceForm_lie_apply, mem_unitaryLieAlgebra_iff.1 X.property, neg_lie, map_neg]

/-- **The Killing form of `𝔲(n)` is negative semidefinite.** -/
theorem killingForm_unitaryLieAlgebra_self_nonpos (X : unitaryLieAlgebra ι) :
    killingForm ℝ (unitaryLieAlgebra ι) X X ≤ 0 :=
  unitaryReTraceForm.killingForm_self_nonpos_of_posDef isSymm_unitaryReTraceForm
    posDef_unitaryReTraceForm lieInvariant_unitaryReTraceForm X

/-- **The kernel of the Killing form of `𝔲(n)` is its centre**: `κ(X, X) = 0` exactly when `X`
lies in the centre `iℝ · 1` (`TauCeti.mem_center_unitaryLieAlgebra_iff`). -/
@[simp]
theorem killingForm_unitaryLieAlgebra_self_eq_zero_iff {X : unitaryLieAlgebra ι} :
    killingForm ℝ (unitaryLieAlgebra ι) X X = 0 ↔ X ∈ center ℝ (unitaryLieAlgebra ι) :=
  unitaryReTraceForm.killingForm_self_eq_zero_iff_of_posDef isSymm_unitaryReTraceForm
    posDef_unitaryReTraceForm lieInvariant_unitaryReTraceForm X

/-- The Killing form of `𝔲(n)` is strictly negative off the centre. -/
theorem killingForm_unitaryLieAlgebra_self_neg {X : unitaryLieAlgebra ι}
    (hX : X ∉ center ℝ (unitaryLieAlgebra ι)) : killingForm ℝ (unitaryLieAlgebra ι) X X < 0 :=
  unitaryReTraceForm.killingForm_self_neg_of_posDef_of_notMem_center isSymm_unitaryReTraceForm
    posDef_unitaryReTraceForm lieInvariant_unitaryReTraceForm X hX

/-- **`𝔲(n) = 𝔷 ⊕ [𝔲(n), 𝔲(n)]`**: the centre `iℝ · 1` and the derived algebra `𝔰𝔲(n)` of `𝔲(n)`
are complementary. -/
theorem isCompl_center_derivedSeries_one_unitaryLieAlgebra :
    IsCompl (center ℝ (unitaryLieAlgebra ι)) (derivedSeries ℝ (unitaryLieAlgebra ι) 1) :=
  unitaryReTraceForm.isCompl_center_derivedSeries_one_of_anisotropic
    isSymm_unitaryReTraceForm.isRefl posDef_unitaryReTraceForm.anisotropic
    lieInvariant_unitaryReTraceForm

end TauCeti
