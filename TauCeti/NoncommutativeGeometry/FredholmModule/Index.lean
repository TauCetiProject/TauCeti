/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.Compression
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.NoncommutativeGeometry.FredholmModule.Normalization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Analytic index pairings of Fredholm modules

Every even Fredholm module `(H, π, F, γ)` over a complex `*`-algebra `A` pairs with idempotents
`e² = e` in `A` (without requiring `e` to be self-adjoint), and every odd Fredholm module
`(H, π, F)` over a unital complex `*`-algebra `A` pairs with invertible elements `u ∈ Aˣ`:

* **Even index pairing (`EvenFredholmModule.evenIndex`).** Let `γ₊ = (1 + γ) / 2` and
  `γ₋ = (1 - γ) / 2` be the grading projections onto the `±1`-eigenspaces of `γ`. Because `γ`
  commutes with `π(e)`, the operators `P₊ = π(e) γ₊` and `P₋ = π(e) γ₋` are bounded idempotents
  with closed ranges `π(e) H₊` and `π(e) H₋` whenever `e² = e`. Compressing `F` gives
  `evenCompression M e : range P₊ →L[ℂ] range P₋` with parametrix
  `evenParametrix M e : range P₋ →L[ℂ] range P₊` modulo compact operators, because
  `P₊ F P₋ F P₊ - P₊ = (π(e) ((F² - 1) π(e)) - π(e) F [F, π(e)] π(e)) γ₊`. Equivalently,
  `evenIndex M e` is the compression index of the off-diagonal block `gradePosToNeg : H₊ →L[ℂ] H₋`
  between the restricted actions `repPos e` and `repNeg e`
  (`evenIndex_eq_compressionIndex_gradePosToNeg`).
* **Odd index pairing (`FredholmModule.oddIndex`).** Let `P = (1 + F) / 2`. For any `a ∈ A`, the
  Toeplitz-type operator `oddToeplitzElem M a = 1 + P π(a - 1) P` on `H` is well-defined without
  requiring `π` to be unital or `F² = 1`, and satisfies `oddToeplitzElem a * oddToeplitzElem b -
  oddToeplitzElem (a * b) ∈ K(H)` for all `a, b ∈ A`. In particular, for `u ∈ Aˣ` the operator
  `oddToeplitz M u` is Fredholm and `u ↦ index (oddToeplitz M u)` is a group homomorphism
  `Aˣ → ℤ` (`oddIndex_mul`). When `F² = 1`, splitting `H ≃ range P × ker P` identifies
  `oddToeplitz M u` with `oddCompression M u ⊕ id`, recovering the compressed Toeplitz operator
  `P (1 + π(u - 1)) P : range P → range P` (equal to `P π(u) P` whenever `π(1) = 1`).

Both pairings vanish on degenerate modules, add under orthogonal direct sums `prod`, and are
invariant under unitary conjugation `conj`, relatively compact perturbations `perturb`, spectral
contraction `sinContraction`, contraction doubling `double`, and two-step normalization
`normalize`. In addition, the even pairing changes sign under `flipGrading` and is invariant under
forced unitization `unitize`.

## Main definitions

* `TauCeti.EvenFredholmModule.gradingPos`, `TauCeti.EvenFredholmModule.gradingNeg`,
  `TauCeti.EvenFredholmModule.gradePosToNeg`, `TauCeti.EvenFredholmModule.gradePosToNegEquiv`,
  `TauCeti.EvenFredholmModule.evenProjPos`, `TauCeti.EvenFredholmModule.evenProjNeg`:
  grading projections, off-diagonal operator block `H₊ →L[ℂ] H₋`, and idempotent range projections
  of an even Fredholm module.
* `TauCeti.EvenFredholmModule.evenCompression`, `TauCeti.EvenFredholmModule.evenParametrix`,
  `TauCeti.EvenFredholmModule.evenIndex`: Fredholm compression, parametrix, and integer index
  pairing with idempotents `e ∈ A`.
* `TauCeti.EvenFredholmModule.pointCycle`, `TauCeti.EvenFredholmModule.matrixPointCycle`:
  finite-dimensional point cycles (`F = 0`, `γ = 1`), whose even index computes
  `finrank ℂ (π e).range` and matrix rank.
* `TauCeti.FredholmModule.posProj`, `TauCeti.FredholmModule.oddToeplitzElem`,
  `TauCeti.FredholmModule.oddToeplitz`, `TauCeti.FredholmModule.oddCompression`,
  `TauCeti.FredholmModule.oddIndex`, `TauCeti.FredholmModule.oddIndexHom`: odd Toeplitz operators,
  normalized compression on `range ((1 + F) / 2)`, and integer `K₁`-index homomorphism.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1, Proposition 3.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.1–8.3.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Even index pairing with idempotents -/

namespace EvenFredholmModule

section EvenPairing

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H H' H₁ H₂ : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

variable (M : EvenFredholmModule A H)

/-- Positive grading projection `(1 + γ) / 2` onto the `+1`-eigenspace of `M.grading`. -/
def gradingPos : H →L[ℂ] H :=
  (2 : ℂ)⁻¹ • (1 + M.grading)

theorem gradingPos_def : M.gradingPos = (2 : ℂ)⁻¹ • (1 + M.grading) :=
  (rfl)

/-- Negative grading projection `(1 - γ) / 2` onto the `-1`-eigenspace of `M.grading`. -/
def gradingNeg : H →L[ℂ] H :=
  (2 : ℂ)⁻¹ • (1 - M.grading)

theorem gradingNeg_def : M.gradingNeg = (2 : ℂ)⁻¹ • (1 - M.grading) :=
  (rfl)

@[simp]
theorem flipGrading_gradingPos : M.flipGrading.gradingPos = M.gradingNeg := by
  simp [gradingPos, gradingNeg, sub_eq_add_neg]

@[simp]
theorem flipGrading_gradingNeg : M.flipGrading.gradingNeg = M.gradingPos := by
  simp [gradingPos, gradingNeg]

theorem gradingPos_add_gradingNeg : M.gradingPos + M.gradingNeg = 1 := by
  ext x
  simp only [gradingPos, gradingNeg, add_apply, smul_apply, sub_apply, one_apply_eq_self]
  rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ x, smul_smul]
  norm_num

theorem grading_mul_gradingPos : M.grading * M.gradingPos = M.gradingPos := by
  rw [gradingPos, mul_smul_comm, mul_add, mul_one, M.grading_mul_grading, add_comm]

theorem isIdempotentElem_gradingPos : IsIdempotentElem M.gradingPos := by
  ext x
  have hgg : M.grading (M.grading x) = x := congr($M.grading_mul_grading x)
  simp only [gradingPos, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    smul_apply, add_apply, one_apply_eq_self, map_smul, map_add, hgg]
  rw [add_comm (M.grading x) x, ← two_smul ℂ, smul_smul, smul_smul]
  congr 1
  norm_num

theorem isIdempotentElem_gradingNeg : IsIdempotentElem M.gradingNeg := by
  rw [← M.flipGrading_gradingPos]
  exact M.flipGrading.isIdempotentElem_gradingPos

theorem gradingNeg_mul_operator : M.gradingNeg * M.operator = M.operator * M.gradingPos := by
  rw [gradingNeg, gradingPos, smul_mul_assoc, mul_smul_comm, sub_mul, one_mul,
    M.grading_mul_operator, sub_neg_eq_add, mul_add, mul_one]

theorem gradingPos_mul_operator : M.gradingPos * M.operator = M.operator * M.gradingNeg := by
  simpa using M.flipGrading.gradingNeg_mul_operator

theorem commute_gradingPos_rep (a : A) : Commute M.gradingPos (M.rep a) :=
  ((Commute.one_left (M.rep a)).add_left (M.commute_grading_rep a)).smul_left (2 : ℂ)⁻¹

theorem commute_gradingNeg_rep (a : A) : Commute M.gradingNeg (M.rep a) :=
  ((Commute.one_left (M.rep a)).sub_left (M.commute_grading_rep a)).smul_left (2 : ℂ)⁻¹

theorem range_gradingPos :
    M.gradingPos.range = Module.End.eigenspace (M.grading : Module.End ℂ H) 1 := by
  ext x
  rw [Module.End.mem_eigenspace_iff, one_smul]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have hfix : M.gradingPos x = x :=
      ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingPos ⟨x, hx⟩
    calc
      M.grading x = M.grading (M.gradingPos x) := by rw [hfix]
      _ = (M.grading * M.gradingPos) x := rfl
      _ = M.gradingPos x := by rw [M.grading_mul_gradingPos]
      _ = x := hfix
  · have hx' : M.grading x = x := hx
    refine ⟨x, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, gradingPos_def, smul_apply, add_apply,
      one_apply_eq_self, hx', ← two_smul ℂ x, smul_smul]
    norm_num

theorem range_gradingNeg :
    M.gradingNeg.range = Module.End.eigenspace (M.grading : Module.End ℂ H) (-1) := by
  rw [← M.flipGrading_gradingPos, M.flipGrading.range_gradingPos]
  ext x
  simp [neg_eq_iff_eq_neg]

/-- Off-diagonal block `F₊ : H₊ →L[ℂ] H₋` of `M.operator` mapping the `+1`-grading subspace
`M.gradingPos.range` into the `-1`-grading subspace `M.gradingNeg.range`. -/
def gradePosToNeg : M.gradingPos.range →L[ℂ] M.gradingNeg.range :=
  M.gradingNeg.rangeRestrict ∘L M.operator ∘L M.gradingPos.range.subtypeL

theorem gradePosToNeg_def :
    M.gradePosToNeg = M.gradingNeg.rangeRestrict ∘L M.operator ∘L M.gradingPos.range.subtypeL :=
  (rfl)

@[simp]
theorem coe_gradePosToNeg_apply (w : M.gradingPos.range) :
    (M.gradePosToNeg w : H) = M.operator w := by
  have hw : M.gradingPos w = w :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingPos w
  have hcomm : M.gradingNeg (M.operator w) = M.operator (M.gradingPos w) :=
    congr($M.gradingNeg_mul_operator w)
  simpa [gradePosToNeg_def, hw] using hcomm

/-- When `M` is normalized (`F² = 1`), `M.gradePosToNeg` upgrades to a continuous linear
equivalence `H₊ ≃L[ℂ] H₋`, with inverse induced by `M.operator` from `H₋` to `H₊`. -/
def gradePosToNegEquiv (hM : M.IsNormalized) :
    M.gradingPos.range ≃L[ℂ] M.gradingNeg.range :=
  .equivOfInverse M.gradePosToNeg
    (M.gradingPos.rangeRestrict ∘L M.operator ∘L M.gradingNeg.range.subtypeL)
    (fun w ↦ Subtype.ext <| by
      have hw : M.gradingPos w = w :=
        ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingPos w
      have hFF : M.operator (M.operator w) = w := congr($hM.operator_mul_operator w)
      simpa [coe_gradePosToNeg_apply, hFF] using hw)
    (fun w ↦ Subtype.ext <| by
      have hw : M.gradingNeg w = w :=
        ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingNeg w
      have hpos : M.gradingPos (M.operator w) = M.operator w := by
        have hcomm : M.gradingPos (M.operator w) = M.operator (M.gradingNeg w) :=
          congr($M.gradingPos_mul_operator w)
        rwa [hw] at hcomm
      have hFF : M.operator (M.operator w) = w := congr($hM.operator_mul_operator w)
      have hval :
          (((M.gradingPos.rangeRestrict ∘L M.operator ∘L M.gradingNeg.range.subtypeL) w) : H) =
            M.gradingPos (M.operator w) := rfl
      rw [coe_gradePosToNeg_apply, hval, hpos, hFF])

@[simp]
theorem coe_gradePosToNegEquiv (hM : M.IsNormalized) :
    (M.gradePosToNegEquiv hM : M.gradingPos.range →L[ℂ] M.gradingNeg.range) = M.gradePosToNeg :=
  (rfl)

/-- For a normalized even Fredholm module (`F² = 1`), `M.gradePosToNeg : H₊ →L[ℂ] H₋` is
invertible and therefore has Fredholm index `0`. -/
@[simp]
theorem index_gradePosToNeg_of_isNormalized (hM : M.IsNormalized) :
    M.gradePosToNeg.index = 0 := by
  rw [← M.coe_gradePosToNegEquiv hM]
  exact ContinuousLinearMap.index_eq_zero_of_bijective _ (M.gradePosToNegEquiv hM).bijective

/-- Restriction `π₊(a) : H₊ →L[ℂ] H₊` of `M.rep a` to the `+1`-grading subspace. -/
def repPos (a : A) : M.gradingPos.range →L[ℂ] M.gradingPos.range :=
  M.gradingPos.rangeRestrict ∘L M.rep a ∘L M.gradingPos.range.subtypeL

theorem repPos_def (a : A) :
    M.repPos a = M.gradingPos.rangeRestrict ∘L M.rep a ∘L M.gradingPos.range.subtypeL :=
  (rfl)

@[simp]
theorem coe_repPos_apply (a : A) (w : M.gradingPos.range) :
    (M.repPos a w : H) = M.rep a w := by
  have hw : M.gradingPos w = w :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingPos w
  have hcomm : M.gradingPos (M.rep a w) = M.rep a (M.gradingPos w) :=
    DFunLike.congr_fun (M.commute_gradingPos_rep a).eq (w : H)
  simpa [repPos_def, hw] using hcomm

/-- Restriction `π₋(a) : H₋ →L[ℂ] H₋` of `M.rep a` to the `-1`-grading subspace. -/
def repNeg (a : A) : M.gradingNeg.range →L[ℂ] M.gradingNeg.range :=
  M.gradingNeg.rangeRestrict ∘L M.rep a ∘L M.gradingNeg.range.subtypeL

theorem repNeg_def (a : A) :
    M.repNeg a = M.gradingNeg.rangeRestrict ∘L M.rep a ∘L M.gradingNeg.range.subtypeL :=
  (rfl)

@[simp]
theorem coe_repNeg_apply (a : A) (w : M.gradingNeg.range) :
    (M.repNeg a w : H) = M.rep a w := by
  have hw : M.gradingNeg w = w :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingNeg w
  have hcomm : M.gradingNeg (M.rep a w) = M.rep a (M.gradingNeg w) :=
    DFunLike.congr_fun (M.commute_gradingNeg_rep a).eq (w : H)
  simpa [repNeg_def, hw] using hcomm

/-- Positive graded projection `π(e) (1 + γ) / 2` associated to an element `e : A`. -/
def evenProjPos (e : A) : H →L[ℂ] H :=
  M.rep e * M.gradingPos

theorem evenProjPos_def (e : A) : M.evenProjPos e = M.rep e * M.gradingPos :=
  (rfl)

/-- Negative graded projection `π(e) (1 - γ) / 2` associated to an element `e : A`. -/
def evenProjNeg (e : A) : H →L[ℂ] H :=
  M.rep e * M.gradingNeg

theorem evenProjNeg_def (e : A) : M.evenProjNeg e = M.rep e * M.gradingNeg :=
  (rfl)

@[simp]
theorem flipGrading_evenProjPos (e : A) : M.flipGrading.evenProjPos e = M.evenProjNeg e := by
  simp [evenProjPos, evenProjNeg]

@[simp]
theorem flipGrading_evenProjNeg (e : A) : M.flipGrading.evenProjNeg e = M.evenProjPos e := by
  simp [evenProjPos, evenProjNeg]

/-- For any idempotent `e² = e` in `A` (not necessarily self-adjoint), `M.evenProjPos e` is a
bounded idempotent on `H`. -/
theorem isIdempotentElem_evenProjPos {e : A} (he : IsIdempotentElem e) :
    IsIdempotentElem (M.evenProjPos e) := by
  have he_rep : M.rep e * M.rep e = M.rep e := by rw [← map_mul, he.eq]
  calc
    M.evenProjPos e * M.evenProjPos e
      = M.rep e * (M.gradingPos * M.rep e) * M.gradingPos := by
          simp only [evenProjPos, mul_assoc]
    _ = (M.rep e * M.rep e) * (M.gradingPos * M.gradingPos) := by
          rw [(M.commute_gradingPos_rep e).eq]
          simp only [mul_assoc]
    _ = M.evenProjPos e := by rw [he_rep, M.isIdempotentElem_gradingPos.eq, evenProjPos]

/-- For any idempotent `e² = e` in `A`, `M.evenProjNeg e` is a bounded idempotent on `H`. -/
theorem isIdempotentElem_evenProjNeg {e : A} (he : IsIdempotentElem e) :
    IsIdempotentElem (M.evenProjNeg e) := by
  rw [← M.flipGrading_evenProjPos]
  exact M.flipGrading.isIdempotentElem_evenProjPos he

/-- The range of `M.evenProjPos e` is the image under `π(e)` of the `+1`-eigenspace of `M.grading`.
-/
theorem range_evenProjPos_eq_map_eigenspace (e : A) :
    (M.evenProjPos e).range =
      (Module.End.eigenspace (M.grading : Module.End ℂ H) 1).map (M.rep e : H →ₗ[ℂ] H) := by
  rw [evenProjPos, ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, ← M.range_gradingPos]

/-- The range of `M.evenProjNeg e` is the image under `π(e)` of the `-1`-eigenspace of `M.grading`.
-/
theorem range_evenProjNeg_eq_map_eigenspace (e : A) :
    (M.evenProjNeg e).range =
      (Module.End.eigenspace (M.grading : Module.End ℂ H) (-1)).map (M.rep e : H →ₗ[ℂ] H) := by
  rw [evenProjNeg, ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, ← M.range_gradingNeg]

/-- **Even compression.** Restriction of `M.operator` from `(M.evenProjPos e).range` into
`(M.evenProjNeg e).range` via `P₋ F : range P₊ → range P₋`. -/
def evenCompression (e : A) : (M.evenProjPos e).range →L[ℂ] (M.evenProjNeg e).range :=
  (M.evenProjNeg e).rangeRestrict ∘L M.operator ∘L (M.evenProjPos e).range.subtypeL

theorem evenCompression_def (e : A) :
    M.evenCompression e =
      (M.evenProjNeg e).rangeRestrict ∘L M.operator ∘L (M.evenProjPos e).range.subtypeL :=
  (rfl)

/-- **Even parametrix.** Restriction of `M.operator` in the opposite direction
`P₊ F : range P₋ → range P₊`. -/
def evenParametrix (e : A) : (M.evenProjNeg e).range →L[ℂ] (M.evenProjPos e).range :=
  (M.evenProjPos e).rangeRestrict ∘L M.operator ∘L (M.evenProjNeg e).range.subtypeL

theorem evenParametrix_def (e : A) :
    M.evenParametrix e =
      (M.evenProjPos e).rangeRestrict ∘L M.operator ∘L (M.evenProjNeg e).range.subtypeL :=
  (rfl)

/-- **Even analytic index pairing** of an even Fredholm module `M` with an idempotent `e ∈ A`,
defined as the Fredholm index of `M.evenCompression e : range P₊ →L[ℂ] range P₋`. -/
def evenIndex (e : A) : ℤ :=
  (M.evenCompression e).index

theorem evenIndex_def (e : A) : M.evenIndex e = (M.evenCompression e).index :=
  (rfl)

private theorem evenIndex_eq_compressionIndex (e : A) :
    M.evenIndex e =
      ContinuousLinearMap.compressionIndex (M.evenProjPos e) (M.evenProjNeg e) M.operator := by
  rw [evenIndex_def, ContinuousLinearMap.compressionIndex_def, evenCompression_def,
    ContinuousLinearMap.rangeCompression_def]

private theorem index_evenParametrix_eq_compressionIndex (e : A) :
    (M.evenParametrix e).index =
      ContinuousLinearMap.compressionIndex (M.evenProjNeg e) (M.evenProjPos e) M.operator := by
  rw [ContinuousLinearMap.compressionIndex_def, evenParametrix_def,
    ContinuousLinearMap.rangeCompression_def]

/-- **Identification of `evenIndex` with `gradePosToNeg` on `H₊ → H₋`.** For every `e : A`,
`M.evenIndex e` equals the compression index of `M.gradePosToNeg : H₊ →L[ℂ] H₋` between the
restricted actions `M.repPos e : H₊ →L[ℂ] H₊` and `M.repNeg e : H₋ →L[ℂ] H₋`. -/
theorem evenIndex_eq_compressionIndex_gradePosToNeg (e : A) :
    M.evenIndex e =
      ContinuousLinearMap.compressionIndex (M.repPos e) (M.repNeg e) M.gradePosToNeg := by
  have hri_pos : M.gradingPos.rangeRestrict.comp M.gradingPos.range.subtypeL =
      .id ℂ M.gradingPos.range := by
    ext w
    simpa using ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingPos w
  have hri_neg : M.gradingNeg.rangeRestrict.comp M.gradingNeg.range.subtypeL =
      .id ℂ M.gradingNeg.range := by
    ext w
    simpa using ContinuousLinearMap.IsIdempotentElem.apply_coe_range M.isIdempotentElem_gradingNeg w
  have hp : M.gradingPos.range.subtypeL ∘L M.repPos e ∘L M.gradingPos.rangeRestrict =
      M.evenProjPos e := by
    have hmul : M.gradingPos * M.rep e * M.gradingPos = M.evenProjPos e := by
      rw [(M.commute_gradingPos_rep e).eq, mul_assoc, M.isIdempotentElem_gradingPos.eq,
        evenProjPos_def]
    ext x
    rw [← hmul]
    rfl
  have hq : M.gradingNeg.range.subtypeL ∘L M.repNeg e ∘L M.gradingNeg.rangeRestrict =
      M.evenProjNeg e := by
    have hmul : M.gradingNeg * M.rep e * M.gradingNeg = M.evenProjNeg e := by
      rw [(M.commute_gradingNeg_rep e).eq, mul_assoc, M.isIdempotentElem_gradingNeg.eq,
        evenProjNeg_def]
    ext x
    rw [← hmul]
    rfl
  rw [M.evenIndex_eq_compressionIndex, ← hp, ← hq,
    ContinuousLinearMap.compressionIndex_retract hri_pos hri_neg, ← M.gradePosToNeg_def]

/-- When `π(1) = 1`, the even index at `1` equals the Fredholm index of
`M.gradePosToNeg : H₊ →L[ℂ] H₋`. -/
theorem evenIndex_one_eq_index_gradePosToNeg [One A] (h1 : M.rep 1 = 1) :
    M.evenIndex 1 = M.gradePosToNeg.index := by
  have hpos : M.evenProjPos 1 = M.gradingPos := by rw [evenProjPos_def, h1, one_mul]
  have hneg : M.evenProjNeg 1 = M.gradingNeg := by rw [evenProjNeg_def, h1, one_mul]
  rw [M.evenIndex_eq_compressionIndex, hpos, hneg, ContinuousLinearMap.compressionIndex_def,
    ContinuousLinearMap.rangeCompression_def, M.gradePosToNeg_def]

/-- For a normalized even Fredholm module (`F² = 1`) with unital representation (`π(1) = 1`), the
even index at `1` vanishes. -/
theorem evenIndex_one_eq_zero_of_isNormalized [One A] (hM : M.IsNormalized) (h1 : M.rep 1 = 1) :
    M.evenIndex 1 = 0 := by
  rw [M.evenIndex_one_eq_index_gradePosToNeg h1, M.index_gradePosToNeg_of_isNormalized hM]

/-- Ambient algebraic defect formula for the composite `P₊ F P₋ F P₊ - P₊` on `H`. -/
theorem evenProjPos_mul_operator_defect {e : A} (he : IsIdempotentElem e) :
    M.evenProjPos e * M.operator * M.evenProjNeg e * M.operator * M.evenProjPos e -
      M.evenProjPos e =
      (M.rep e * ((M.operator * M.operator - 1) * M.rep e) -
        M.rep e * M.operator * (M.operator * M.rep e - M.rep e * M.operator) * M.rep e) *
        M.gradingPos := by
  have he_rep : M.rep e * M.rep e = M.rep e := by rw [← map_mul, he.eq]
  have hfive :
      M.evenProjPos e * M.operator * M.evenProjNeg e * M.operator * M.evenProjPos e =
        M.rep e * M.operator * M.rep e * M.operator * M.rep e * M.gradingPos := by
    calc
      M.evenProjPos e * M.operator * M.evenProjNeg e * M.operator * M.evenProjPos e
        = M.rep e * (M.gradingPos * M.operator) * (M.rep e * M.gradingNeg) * M.operator *
            (M.rep e * M.gradingPos) := by
              simp only [evenProjPos, evenProjNeg, mul_assoc]
      _ = M.rep e * M.operator * (M.gradingNeg * M.rep e) * M.gradingNeg * M.operator *
            (M.rep e * M.gradingPos) := by
              rw [M.gradingPos_mul_operator]
              simp only [mul_assoc]
      _ = M.rep e * M.operator * M.rep e * (M.gradingNeg * M.gradingNeg) * M.operator *
            (M.rep e * M.gradingPos) := by
              rw [(M.commute_gradingNeg_rep e).eq]
              simp only [mul_assoc]
      _ = M.rep e * M.operator * M.rep e * (M.gradingNeg * M.operator) *
            (M.rep e * M.gradingPos) := by
              rw [M.isIdempotentElem_gradingNeg.eq]
              simp only [mul_assoc]
      _ = M.rep e * M.operator * M.rep e * M.operator * (M.gradingPos * M.rep e) *
            M.gradingPos := by
              rw [M.gradingNeg_mul_operator]
              simp only [mul_assoc]
      _ = M.rep e * M.operator * M.rep e * M.operator * M.rep e *
            (M.gradingPos * M.gradingPos) := by
              rw [(M.commute_gradingPos_rep e).eq]
              simp only [mul_assoc]
      _ = M.rep e * M.operator * M.rep e * M.operator * M.rep e * M.gradingPos := by
              rw [M.isIdempotentElem_gradingPos.eq]
  have hinner :
      M.rep e * ((M.operator * M.operator - 1) * M.rep e) -
          M.rep e * M.operator * (M.operator * M.rep e - M.rep e * M.operator) * M.rep e =
        M.rep e * M.operator * M.rep e * M.operator * M.rep e - M.rep e := by
    calc
      M.rep e * ((M.operator * M.operator - 1) * M.rep e) -
          M.rep e * M.operator * (M.operator * M.rep e - M.rep e * M.operator) * M.rep e
        = M.rep e * ((M.operator * M.operator - 1) * (M.rep e * M.rep e)) -
            M.rep e * M.operator * (M.operator * M.rep e - M.rep e * M.operator) * M.rep e := by
            conv_lhs => enter [1, 2, 2]; rw [← he_rep]
      _ = M.rep e * M.operator * M.rep e * M.operator * M.rep e -
            M.rep e * (M.rep e * M.rep e) := by noncomm_ring
      _ = M.rep e * M.operator * M.rep e * M.operator * M.rep e - M.rep e := by
            rw [he_rep, he_rep]
  rw [hfive, hinner, sub_mul, ← evenProjPos]

theorem isCompactOperator_evenProjPos_mul_operator_defect {e : A} (he : IsIdempotentElem e) :
    IsCompactOperator
      ⇑(M.evenProjPos e * M.operator * M.evenProjNeg e * M.operator * M.evenProjPos e -
        M.evenProjPos e) := by
  rw [M.evenProjPos_mul_operator_defect he]
  have h₁ : IsCompactOperator ⇑(M.rep e * ((M.operator * M.operator - 1) * M.rep e)) :=
    (M.isCompactOperator_mul_self_sub_one_mul e).mul_left (M.rep e)
  have h₂ : IsCompactOperator
      ⇑(M.rep e * M.operator * (M.operator * M.rep e - M.rep e * M.operator) * M.rep e) :=
    ((M.isCompactOperator_commutator e).mul_left (M.rep e * M.operator)).mul_right (M.rep e)
  exact (h₁.sub h₂).mul_right M.gradingPos

theorem evenParametrix_comp_evenCompression_sub_one {e : A} (he : IsIdempotentElem e) :
    (M.evenParametrix e).comp (M.evenCompression e) - 1 =
      (M.evenProjPos e).rangeRestrict ∘L
        (M.evenProjPos e * M.operator * M.evenProjNeg e * M.operator * M.evenProjPos e -
          M.evenProjPos e) ∘L (M.evenProjPos e).range.subtypeL := by
  have hp := M.isIdempotentElem_evenProjPos he
  have hrr_pos (z : H) : ((M.evenProjPos e).rangeRestrict z : H) = M.evenProjPos e z := rfl
  have hrr_neg (z : H) : ((M.evenProjNeg e).rangeRestrict z : H) = M.evenProjNeg e z := rfl
  ext w
  have hw : M.evenProjPos e w = w := ContinuousLinearMap.IsIdempotentElem.apply_coe_range hp w
  have hpp (z : H) : M.evenProjPos e (M.evenProjPos e z) = M.evenProjPos e z := congr($hp.eq z)
  simp only [evenParametrix, evenCompression, sub_apply, Submodule.coe_sub, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hrr_pos, hrr_neg,
    ContinuousLinearMap.mul_def, map_sub, hw, hpp]

theorem evenCompression_comp_evenParametrix_sub_one {e : A} (he : IsIdempotentElem e) :
    (M.evenCompression e).comp (M.evenParametrix e) - 1 =
      (M.evenProjNeg e).rangeRestrict ∘L
        (M.evenProjNeg e * M.operator * M.evenProjPos e * M.operator * M.evenProjNeg e -
          M.evenProjNeg e) ∘L (M.evenProjNeg e).range.subtypeL := by
  have hq := M.isIdempotentElem_evenProjNeg he
  have hrr_pos (z : H) : ((M.evenProjPos e).rangeRestrict z : H) = M.evenProjPos e z := rfl
  have hrr_neg (z : H) : ((M.evenProjNeg e).rangeRestrict z : H) = M.evenProjNeg e z := rfl
  ext w
  have hw : M.evenProjNeg e w = w := ContinuousLinearMap.IsIdempotentElem.apply_coe_range hq w
  have hqq (z : H) : M.evenProjNeg e (M.evenProjNeg e z) = M.evenProjNeg e z := congr($hq.eq z)
  simp only [evenParametrix, evenCompression, sub_apply, Submodule.coe_sub, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hrr_pos, hrr_neg,
    ContinuousLinearMap.mul_def, map_sub, hw, hqq]

theorem isCompactOperator_evenParametrix_comp_evenCompression_sub_one {e : A}
    (he : IsIdempotentElem e) :
    IsCompactOperator ⇑((M.evenParametrix e).comp (M.evenCompression e) - 1) := by
  rw [M.evenParametrix_comp_evenCompression_sub_one he]
  exact ((M.isCompactOperator_evenProjPos_mul_operator_defect he).comp_clm
    (M.evenProjPos e).range.subtypeL).clm_comp (M.evenProjPos e).rangeRestrict

theorem isCompactOperator_evenCompression_comp_evenParametrix_sub_one {e : A}
    (he : IsIdempotentElem e) :
    IsCompactOperator ⇑((M.evenCompression e).comp (M.evenParametrix e) - 1) := by
  have hdefect :
      IsCompactOperator
        ⇑(M.evenProjNeg e * M.operator * M.evenProjPos e * M.operator * M.evenProjNeg e -
          M.evenProjNeg e) := by
    simpa only [flipGrading_evenProjPos, flipGrading_evenProjNeg, flipGrading_toFredholmModule]
      using M.flipGrading.isCompactOperator_evenProjPos_mul_operator_defect he
  rw [M.evenCompression_comp_evenParametrix_sub_one he]
  exact (hdefect.comp_clm (M.evenProjNeg e).range.subtypeL).clm_comp
    (M.evenProjNeg e).rangeRestrict

/-- **Fredholmness of the even compression.** For every idempotent `e² = e` in `A`, the compressed
operator `M.evenCompression e : range P₊ →L[ℂ] range P₋` is Fredholm. -/
theorem isFredholm_evenCompression {e : A} (he : IsIdempotentElem e) :
    (M.evenCompression e).IsFredholm := by
  have := ContinuousLinearMap.IsIdempotentElem.completeSpace_range
    (M.isIdempotentElem_evenProjPos he)
  have := ContinuousLinearMap.IsIdempotentElem.completeSpace_range
    (M.isIdempotentElem_evenProjNeg he)
  exact .of_isCompactOperator_comp_sub_one
    (M.isCompactOperator_evenParametrix_comp_evenCompression_sub_one he)
    (M.isCompactOperator_evenCompression_comp_evenParametrix_sub_one he)

/-- Reversing the grading `γ ↦ -γ` negates the even index pairing. -/
@[simp]
theorem evenIndex_flipGrading {e : A} (he : IsIdempotentElem e) :
    M.flipGrading.evenIndex e = -M.evenIndex e := by
  have := ContinuousLinearMap.IsIdempotentElem.completeSpace_range
    (M.isIdempotentElem_evenProjPos he)
  have := ContinuousLinearMap.IsIdempotentElem.completeSpace_range
    (M.isIdempotentElem_evenProjNeg he)
  have hop : M.flipGrading.operator = M.operator := by simp
  have hflip : M.flipGrading.evenIndex e = (M.evenParametrix e).index := by
    rw [evenIndex_eq_compressionIndex, M.flipGrading_evenProjPos, M.flipGrading_evenProjNeg, hop,
      M.index_evenParametrix_eq_compressionIndex]
  rw [hflip, evenIndex]
  exact ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one
    (M.isCompactOperator_evenParametrix_comp_evenCompression_sub_one he)
    (M.isCompactOperator_evenCompression_comp_evenParametrix_sub_one he)

/-- Degenerate even Fredholm modules have vanishing even index on every idempotent. -/
theorem evenIndex_eq_zero_of_isDegenerate (hdeg : M.IsDegenerate) {e : A}
    (he : IsIdempotentElem e) : M.evenIndex e = 0 := by
  have hzero_pos :
      M.evenProjPos e * M.operator * M.evenProjNeg e * M.operator * M.evenProjPos e -
        M.evenProjPos e = 0 := by
    rw [M.evenProjPos_mul_operator_defect he, hdeg.mul_self_sub_one_mul_eq_zero e,
      hdeg.commutator_eq_zero e]
    simp
  have hdeg_flip : M.flipGrading.IsDegenerate := by simpa [IsDegenerate] using hdeg
  have hzero_neg :
      M.evenProjNeg e * M.operator * M.evenProjPos e * M.operator * M.evenProjNeg e -
        M.evenProjNeg e = 0 := by
    have h := M.flipGrading.evenProjPos_mul_operator_defect he
    rw [hdeg_flip.mul_self_sub_one_mul_eq_zero e, hdeg_flip.commutator_eq_zero e] at h
    simpa only [flipGrading_evenProjPos, flipGrading_evenProjNeg, flipGrading_toFredholmModule,
      mul_zero, sub_zero, zero_mul] using h
  have hleft : (M.evenParametrix e).comp (M.evenCompression e) = 1 :=
    sub_eq_zero.mp (by rw [M.evenParametrix_comp_evenCompression_sub_one he, hzero_pos]; simp)
  have hright : (M.evenCompression e).comp (M.evenParametrix e) = 1 :=
    sub_eq_zero.mp (by rw [M.evenCompression_comp_evenParametrix_sub_one he, hzero_neg]; simp)
  have hlinv : Function.LeftInverse (M.evenParametrix e) (M.evenCompression e) := fun x ↦ by
    simpa using congr($hleft x)
  have hrinv : Function.RightInverse (M.evenParametrix e) (M.evenCompression e) := fun y ↦ by
    simpa using congr($hright y)
  exact ContinuousLinearMap.index_eq_zero_of_bijective _ ⟨hlinv.injective, hrinv.surjective⟩

/-- Two even Fredholm modules with the same representation at `e`, the same grading, and operator
difference compact relative to `π(e)` have the same even index at `e`. -/
theorem evenIndex_eq_of_isCompactOperator_sub_mul_rep {M' : EvenFredholmModule A H} {e : A}
    (he : IsIdempotentElem e) (hrep : M'.rep e = M.rep e) (hγ : M'.grading = M.grading)
    (hK : IsCompactOperator ⇑((M'.operator - M.operator) * M.rep e)) :
    M'.evenIndex e = M.evenIndex e := by
  have := ContinuousLinearMap.IsIdempotentElem.completeSpace_range
    (M.isIdempotentElem_evenProjPos he)
  have := ContinuousLinearMap.IsIdempotentElem.completeSpace_range
    (M.isIdempotentElem_evenProjNeg he)
  have hpos : M'.evenProjPos e = M.evenProjPos e := by
    simp [evenProjPos, gradingPos, hrep, hγ]
  have hneg : M'.evenProjNeg e = M.evenProjNeg e := by
    simp [evenProjNeg, gradingNeg, hrep, hγ]
  let C : (M.evenProjPos e).range →L[ℂ] (M.evenProjNeg e).range :=
    (M.evenProjNeg e).rangeRestrict ∘L ((M'.operator - M.operator) * M.rep e) ∘L M.gradingPos ∘L
      (M.evenProjPos e).range.subtypeL
  have hC : IsCompactOperator C :=
    ((hK.comp_clm (M.gradingPos ∘L (M.evenProjPos e).range.subtypeL)).clm_comp
      (M.evenProjNeg e).rangeRestrict)
  have hrw :
      (M.evenProjNeg e).rangeRestrict ∘L M'.operator ∘L (M.evenProjPos e).range.subtypeL =
        M.evenCompression e + C := by
    have hp := M.isIdempotentElem_evenProjPos he
    have hrr (z : H) : ((M.evenProjNeg e).rangeRestrict z : H) = M.evenProjNeg e z := rfl
    ext w
    have hw : M.rep e (M.gradingPos w) = w :=
      ContinuousLinearMap.IsIdempotentElem.apply_coe_range hp w
    simp only [evenCompression, C, add_apply, Submodule.coe_add, Submodule.coe_sub,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hrr, ContinuousLinearMap.mul_def,
      sub_apply, hw, map_sub]
    exact (add_sub_cancel _ _).symm
  rw [M'.evenIndex_eq_compressionIndex, hpos, hneg, ContinuousLinearMap.compressionIndex_def,
    ContinuousLinearMap.rangeCompression_def, M.evenIndex_def, hrw]
  exact ContinuousLinearMap.index_add_of_isCompactOperator (M.isFredholm_evenCompression he) hC

/-- Relatively compact perturbations leave the even index unchanged. -/
@[simp]
theorem evenIndex_perturb (K : H →L[ℂ] H) (hK : IsSelfAdjoint K)
    (hKc : ∀ a, IsCompactOperator ⇑(K * M.rep a)) (hγK : M.grading * K = -(K * M.grading))
    {e : A} (he : IsIdempotentElem e) :
    (M.perturb K hK hKc hγK).evenIndex e = M.evenIndex e :=
  M.evenIndex_eq_of_isCompactOperator_sub_mul_rep he (by simp) (by simp) (by simpa using hKc e)

/-- Unitary equivalence leaves the even index unchanged. -/
@[simp]
theorem evenIndex_conj (U : H ≃ₗᵢ[ℂ] H') (e : A) :
    (M.conj U).evenIndex e = M.evenIndex e := by
  let eU : H ≃L[ℂ] H' := U.toContinuousLinearEquiv
  have hconj (T : H →L[ℂ] H) :
      U.conjStarAlgEquiv T = (eU : H →L[ℂ] H') ∘L T ∘L (eU.symm : H' →L[ℂ] H) := by
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ← LinearIsometryEquiv.toContinuousLinearEquiv_symm]
  have hpos : (M.conj U).evenProjPos e =
      (eU : H →L[ℂ] H') ∘L M.evenProjPos e ∘L (eU.symm : H' →L[ℂ] H) := by
    rw [← hconj]
    simp [evenProjPos, gradingPos, map_mul, map_smul, map_add, map_one]
  have hneg : (M.conj U).evenProjNeg e =
      (eU : H →L[ℂ] H') ∘L M.evenProjNeg e ∘L (eU.symm : H' →L[ℂ] H) := by
    rw [← hconj]
    simp [evenProjNeg, gradingNeg, map_mul, map_smul, map_sub, map_one]
  rw [(M.conj U).evenIndex_eq_compressionIndex, M.evenIndex_eq_compressionIndex, hpos, hneg,
    show (M.conj U).operator = (eU : H →L[ℂ] H') ∘L M.operator ∘L (eU.symm : H' →L[ℂ] H) by
      simp [hconj]]
  exact ContinuousLinearMap.compressionIndex_conj eU eU (M.evenProjPos e) (M.evenProjNeg e)
    M.operator

/-- Orthogonal direct sums add even indices. -/
@[simp]
theorem evenIndex_prod (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) {e : A}
    (he : IsIdempotentElem e) :
    (M₁.prod M₂).evenIndex e = M₁.evenIndex e + M₂.evenIndex e := by
  have hgpos : (M₁.prod M₂).gradingPos = M₁.gradingPos.withLpProdMap 2 M₂.gradingPos := by
    rw [gradingPos, gradingPos, gradingPos, prod_grading, ← ContinuousLinearMap.withLpProdMap_one,
      ← ContinuousLinearMap.withLpProdMap_add, ContinuousLinearMap.withLpProdMap_smul]
  have hgneg : (M₁.prod M₂).gradingNeg = M₁.gradingNeg.withLpProdMap 2 M₂.gradingNeg := by
    rw [gradingNeg, gradingNeg, gradingNeg, prod_grading, ← ContinuousLinearMap.withLpProdMap_one,
      ← ContinuousLinearMap.withLpProdMap_sub, ContinuousLinearMap.withLpProdMap_smul]
  have hpos : (M₁.prod M₂).evenProjPos e =
      (M₁.evenProjPos e).withLpProdMap 2 (M₂.evenProjPos e) := by
    rw [evenProjPos, evenProjPos, evenProjPos, hgpos, prod_toFredholmModule,
      FredholmModule.prod_rep_apply, ContinuousLinearMap.withLpProdMap_mul]
  have hneg : (M₁.prod M₂).evenProjNeg e =
      (M₁.evenProjNeg e).withLpProdMap 2 (M₂.evenProjNeg e) := by
    rw [evenProjNeg, evenProjNeg, evenProjNeg, hgneg, prod_toFredholmModule,
      FredholmModule.prod_rep_apply, ContinuousLinearMap.withLpProdMap_mul]
  have hop : (M₁.prod M₂).operator = M₁.operator.withLpProdMap 2 M₂.operator := by
    simp
  rw [(M₁.prod M₂).evenIndex_eq_compressionIndex, M₁.evenIndex_eq_compressionIndex,
    M₂.evenIndex_eq_compressionIndex, hpos, hneg, hop]
  exact ContinuousLinearMap.compressionIndex_withLpProdMap _ _ _ _ _ _
    (by rw [ContinuousLinearMap.rangeCompression_def, ← evenCompression_def]
        exact M₁.isFredholm_evenCompression he)
    (by rw [ContinuousLinearMap.rangeCompression_def, ← evenCompression_def]
        exact M₂.isFredholm_evenCompression he)

/-- The linear operator homotopy to `sin(π F / 2)` preserves the even index at every idempotent. -/
@[simp]
theorem evenIndex_sinContractionHomotopy (t : ℝ) {e : A} (he : IsIdempotentElem e) :
    (M.sinContractionHomotopy t).evenIndex e = M.evenIndex e := by
  refine M.evenIndex_eq_of_isCompactOperator_sub_mul_rep he (by simp) (by simp) ?_
  have hsub : (M.sinContractionHomotopy t).operator - M.operator =
      (t : ℂ) • M.toFredholmModule.sinPerturbation := by
    simp
  rw [hsub, smul_mul_assoc, FunLike.coe_smul]
  exact (M.toFredholmModule.isCompactOperator_sinPerturbation_mul_rep e).smul (t : ℂ)

/-- Spectral contraction `sin(π F / 2)` preserves the even index at every idempotent. -/
@[simp]
theorem evenIndex_sinContraction {e : A} (he : IsIdempotentElem e) :
    M.sinContraction.evenIndex e = M.evenIndex e := by
  rw [← M.sinContractionHomotopy_one, M.evenIndex_sinContractionHomotopy 1 he]

/-- The doubling operator homotopy preserves the even index at every idempotent. -/
@[simp]
theorem evenIndex_doubleHomotopy (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) {e : A}
    (he : IsIdempotentElem e) :
    (M.doubleHomotopy hF t).evenIndex e = M.evenIndex e := by
  let M₀ := M.prod M.negZeroRep
  have hhom : (M.doubleHomotopy hF t).evenIndex e = M₀.evenIndex e := by
    refine M₀.evenIndex_eq_of_isCompactOperator_sub_mul_rep he
      (by simp [M₀]) (by simp [M₀]) ?_
    have hsub :
        (M.doubleHomotopy hF t).operator - M₀.operator =
          (t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation := by
      simp [M₀]
    have hrep0 : M₀.rep e = (M.rep e).withLpProdMap 2 0 := by simp [M₀]
    rw [hsub, hrep0, smul_mul_assoc, FunLike.coe_smul]
    exact ((ContinuousLinearMap.isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
      _ _).mpr (M.toFredholmModule.isCompactOperator_sqrt_one_sub_mul_rep hF e)).smul (t : ℂ)
  rw [hhom, EvenFredholmModule.evenIndex_prod _ _ he,
    EvenFredholmModule.evenIndex_eq_zero_of_isDegenerate _ M.isDegenerate_negZeroRep he, add_zero]

/-- Contraction doubling preserves the even index at every idempotent. -/
@[simp]
theorem evenIndex_double (hF : 0 ≤ 1 - M.operator * M.operator) {e : A}
    (he : IsIdempotentElem e) :
    (M.double hF).evenIndex e = M.evenIndex e := by
  rw [← M.doubleHomotopy_one hF, M.evenIndex_doubleHomotopy hF 1 he]

/-- **Normalization preserves the even index.** Passing from an arbitrary even Fredholm module `M`
to its normalized (`F² = 1`) module `M.normalize` leaves the index pairing with every idempotent
`e ∈ A` unchanged. -/
@[simp]
theorem evenIndex_normalize {e : A} (he : IsIdempotentElem e) :
    M.normalize.evenIndex e = M.evenIndex e := by
  rw [M.normalize_def, M.sinContraction.evenIndex_double _ he, M.evenIndex_sinContraction he]

end EvenPairing

section EvenUnitizationInvariance

variable {A : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : EvenFredholmModule A H)

/-- Forced unitization onto `Unitization ℂ A` preserves the even index on idempotents from `A`. -/
@[simp]
theorem evenIndex_unitize (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) {e : A} :
    (M.unitize hK).evenIndex (Unitization.inr e) = M.evenIndex e := by
  have hpos : (M.unitize hK).evenProjPos (Unitization.inr e) = M.evenProjPos e := by
    rw [evenProjPos_def, evenProjPos_def, unitize_toFredholmModule,
      FredholmModule.unitize_rep_inr, gradingPos_def, gradingPos_def, unitize_grading]
  have hneg : (M.unitize hK).evenProjNeg (Unitization.inr e) = M.evenProjNeg e := by
    rw [evenProjNeg_def, evenProjNeg_def, unitize_toFredholmModule,
      FredholmModule.unitize_rep_inr, gradingNeg_def, gradingNeg_def, unitize_grading]
  have hop : (M.unitize hK).operator = M.operator := by simp
  rw [(M.unitize hK).evenIndex_eq_compressionIndex, M.evenIndex_eq_compressionIndex,
    hpos, hneg, hop]

end EvenUnitizationInvariance

/-! ### Finite-dimensional point cycles and `M₂(ℂ)` idempotent check -/

section PointCycle

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Point cycle** on a finite-dimensional Hilbert space `H`: the even Fredholm module with
representation `π`, operator `F = 0`, and grading `γ = 1`. -/
def pointCycle [FiniteDimensional ℂ H] (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) : EvenFredholmModule A H :=
  ofFiniteDimensional π 0 (IsSelfAdjoint.zero _) 1 (IsSelfAdjoint.one _) (one_mul 1)
    (fun a ↦ Commute.one_left (π a)) (by simp)

theorem pointCycle_def [FiniteDimensional ℂ H] (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) :
    pointCycle π =
      ofFiniteDimensional π 0 (IsSelfAdjoint.zero _) 1 (IsSelfAdjoint.one _) (one_mul 1)
        (fun a ↦ Commute.one_left (π a)) (by simp) :=
  (rfl)

/-- The even index of a finite-dimensional point cycle `(H, π, F = 0, γ = 1)` at `e` is the complex
dimension of `range π(e)`. -/
@[simp]
theorem evenIndex_pointCycle [FiniteDimensional ℂ H] (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (e : A) :
    (pointCycle π).evenIndex e = (Module.finrank ℂ (π e).range : ℤ) := by
  have hpos : (pointCycle π).evenProjPos e = π e := by
    ext x
    simp only [pointCycle, evenProjPos, gradingPos, ofFiniteDimensional_toFredholmModule,
      FredholmModule.ofFiniteDimensional_rep, ofFiniteDimensional_grading,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, smul_apply,
      add_apply, one_apply_eq_self, ← two_smul ℂ x, smul_smul]
    norm_num
  have hneg : (pointCycle π).evenProjNeg e = 0 := by
    ext x
    simp [pointCycle, evenProjNeg, gradingNeg]
  rw [(pointCycle π).evenIndex_eq_compressionIndex, hpos, hneg,
    ContinuousLinearMap.compressionIndex_def, ContinuousLinearMap.index_eq_of_finiteDimensional]
  simp

/-- Canonical point cycle of `Matrix ι ι ℂ` acting on `EuclideanSpace ℂ ι`. -/
def matrixPointCycle (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EvenFredholmModule (Matrix ι ι ℂ) (EuclideanSpace ℂ ι) :=
  pointCycle (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom

theorem matrixPointCycle_def (ι : Type*) [Fintype ι] [DecidableEq ι] :
    matrixPointCycle ι =
      pointCycle (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom :=
  (rfl)

/-- The even index of `matrixPointCycle ι` on any matrix `E` equals `(E.rank : ℤ)`. -/
@[simp]
theorem evenIndex_matrixPointCycle (ι : Type*) [Fintype ι] [DecidableEq ι] (E : Matrix ι ι ℂ) :
    (matrixPointCycle ι).evenIndex E = (E.rank : ℤ) := by
  rw [matrixPointCycle, evenIndex_pointCycle, Matrix.rank_eq_finrank_range_toEuclideanLin]
  rfl

private def matIdem (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, a; 0, 0]

private theorem isIdempotentElem_matIdem (a : ℂ) : IsIdempotentElem (matIdem a) := by
  rw [IsIdempotentElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matIdem, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matIdem_ne_star_of_ne_zero {a : ℂ} (ha : a ≠ 0) : matIdem a ≠ star (matIdem a) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [matIdem, Matrix.star_apply, ha] at h01

private theorem rank_matIdem (a : ℂ) : (matIdem a).rank = 1 := by
  rw [Matrix.rank_eq_finrank_range_toEuclideanLin]
  let e₀ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1
  have he₀ : e₀ ≠ 0 := by
    intro h
    have h0 : e₀ 0 = 0 := congrFun (congrArg WithLp.ofLp h) 0
    simp [e₀] at h0
  have hrange : LinearMap.range (Matrix.toEuclideanLin (matIdem a)) = Submodule.span ℂ {e₀} := by
    ext y
    rw [LinearMap.mem_range, Submodule.mem_span_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      refine ⟨x 0 + a * x 1, ?_⟩
      ext i
      fin_cases i <;> simp [e₀, matIdem, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]
    · rintro ⟨c, rfl⟩
      refine ⟨c • e₀, ?_⟩
      ext i
      fin_cases i <;> simp [e₀, matIdem, Matrix.toLpLin_apply]
  rw [hrange, finrank_span_singleton he₀]

private theorem evenIndex_matrixPointCycle_matIdem (a : ℂ) :
    (matrixPointCycle (Fin 2)).evenIndex (matIdem a) = 1 := by
  rw [evenIndex_matrixPointCycle, rank_matIdem]
  rfl

private theorem evenIndex_normalize_matrixPointCycle_matIdem (a : ℂ) :
    (matrixPointCycle (Fin 2)).normalize.evenIndex (matIdem a) = 1 := by
  rw [evenIndex_normalize _ (isIdempotentElem_matIdem a), evenIndex_matrixPointCycle_matIdem]

private theorem evenIndex_flipGrading_matrixPointCycle_matIdem (a : ℂ) :
    (matrixPointCycle (Fin 2)).flipGrading.evenIndex (matIdem a) = -1 := by
  rw [evenIndex_flipGrading _ (isIdempotentElem_matIdem a), evenIndex_matrixPointCycle_matIdem]

end PointCycle

end EvenFredholmModule

/-! ### Odd index pairing with invertible elements -/

namespace FredholmModule

section PosProj

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : FredholmModule A H)

/-- Approximate positive spectral projection `P = (1 + F) / 2` of an odd Fredholm module. -/
def posProj : H →L[ℂ] H :=
  (2 : ℂ)⁻¹ • (1 + M.operator)

theorem posProj_def : M.posProj = (2 : ℂ)⁻¹ • (1 + M.operator) :=
  (rfl)

theorem isSelfAdjoint_posProj : IsSelfAdjoint M.posProj :=
  isSelfAdjoint_iff.mpr <| by
    rw [posProj, star_smul, star_inv₀, Complex.star_def, map_ofNat, star_add, star_one,
      M.star_operator]

theorem posProj_mul_posProj_sub_posProj :
    M.posProj * M.posProj - M.posProj = (4 : ℂ)⁻¹ • (M.operator * M.operator - 1) := by
  ext x
  simp only [posProj, sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, one_apply_eq_self, map_add, map_smul]
  calc
    (2 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • (x + M.operator x) + (2 : ℂ)⁻¹ • (M.operator x +
          M.operator (M.operator x))) - (2 : ℂ)⁻¹ • (x + M.operator x)
      = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ - (2 : ℂ)⁻¹) • (x + M.operator x) +
          ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • (M.operator (M.operator x) - x) := by
            simp only [smul_add, smul_sub, add_smul, sub_smul, mul_smul]
            abel
    _ = (4 : ℂ)⁻¹ • (M.operator (M.operator x) - x) := by
          have h0 : (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ - (2 : ℂ)⁻¹ = 0 := by norm_num
          have h4 : (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ = (4 : ℂ)⁻¹ := by norm_num
          rw [h0, h4, zero_smul, zero_add]

theorem isIdempotentElem_posProj (hM : M.IsNormalized) : IsIdempotentElem M.posProj := by
  rw [IsIdempotentElem, ← sub_eq_zero, M.posProj_mul_posProj_sub_posProj,
    hM.operator_mul_operator, sub_self, smul_zero]

theorem posProj_commutator (a : A) :
    M.posProj * M.rep a - M.rep a * M.posProj =
      (2 : ℂ)⁻¹ • (M.operator * M.rep a - M.rep a * M.operator) := by
  rw [posProj, smul_mul_assoc, mul_smul_comm, ← smul_sub, add_mul, mul_add, one_mul, mul_one,
    add_sub_add_left_eq_sub]

theorem isCompactOperator_posProj_commutator (a : A) :
    IsCompactOperator ⇑(M.posProj * M.rep a - M.rep a * M.posProj) := by
  rw [M.posProj_commutator a, FunLike.coe_smul]
  exact (M.isCompactOperator_commutator a).smul (2 : ℂ)⁻¹

theorem isCompactOperator_rep_mul_posProj_sq_sub (a : A) :
    IsCompactOperator ⇑(M.rep a * (M.posProj * M.posProj - M.posProj)) := by
  rw [M.posProj_mul_posProj_sub_posProj, mul_smul_comm, FunLike.coe_smul]
  exact (M.isCompactOperator_rep_mul_mul_self_sub_one a).smul (4 : ℂ)⁻¹

theorem posProj_sub_posProj (M' : FredholmModule A H) :
    M'.posProj - M.posProj = (2 : ℂ)⁻¹ • (M'.operator - M.operator) := by
  rw [posProj, posProj, ← smul_sub, add_sub_add_left_eq_sub]

theorem isCompactOperator_posProj_sub_mul_rep (M' : FredholmModule A H)
    (hKc : ∀ a, IsCompactOperator ⇑((M'.operator - M.operator) * M.rep a)) (a : A) :
    IsCompactOperator ⇑((M'.posProj - M.posProj) * M.rep a) := by
  rw [M.posProj_sub_posProj M', smul_mul_assoc]
  exact (hKc a).smul (2 : ℂ)⁻¹

theorem isCompactOperator_rep_mul_posProj_sub (M' : FredholmModule A H)
    (hKc : ∀ a, IsCompactOperator ⇑((M'.operator - M.operator) * M.rep a)) (a : A) :
    IsCompactOperator ⇑(M.rep a * (M'.posProj - M.posProj)) := by
  have hK_sa : IsSelfAdjoint (M'.operator - M.operator) :=
    M'.isSelfAdjoint_operator.sub M.isSelfAdjoint_operator
  have hKright : IsCompactOperator ⇑(M.rep a * (M'.operator - M.operator)) := by
    simpa only [star_mul, map_star, star_star, hK_sa.star_eq] using (hKc (star a)).star
  rw [M.posProj_sub_posProj M', mul_smul_comm]
  exact hKright.smul (2 : ℂ)⁻¹

end PosProj

section OddPairing

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
variable {H H' H₁ H₂ : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

variable (M : FredholmModule A H)

/-- **Odd Toeplitz operator** `1 + P π(a - 1) P` on `H`, well-defined without assuming `π(1) = 1`
or `F² = 1`. When `π(1) = 1` and `F² = 1`, this equals `(1 - P) + P π(a) P`. -/
def oddToeplitzElem (a : A) : H →L[ℂ] H :=
  1 + M.posProj * M.rep (a - 1) * M.posProj

theorem oddToeplitzElem_def (a : A) :
    M.oddToeplitzElem a = 1 + M.posProj * M.rep (a - 1) * M.posProj :=
  (rfl)

/-- **Odd Toeplitz operator** associated to an invertible element `u ∈ Aˣ`. -/
def oddToeplitz (u : Aˣ) : H →L[ℂ] H :=
  M.oddToeplitzElem u

theorem oddToeplitz_def (u : Aˣ) : M.oddToeplitz u = M.oddToeplitzElem u :=
  (rfl)

/-- **Odd analytic index pairing** of an odd Fredholm module `M` with an invertible element
`u ∈ Aˣ`, defined as the Fredholm index of `M.oddToeplitz u`. -/
def oddIndex (u : Aˣ) : ℤ :=
  (M.oddToeplitz u).index

theorem oddIndex_def (u : Aˣ) : M.oddIndex u = (M.oddToeplitz u).index :=
  (rfl)

/-- **Compressed odd Toeplitz operator** `P (1 + π(u - 1)) P : range P →L[ℂ] range P` on the
positive spectral subspace `range ((1 + F) / 2)`. When `F² = 1`, `oddToeplitz M u` splits as
`oddCompression M u ⊕ id` along `H ≃ range P × ker P`. -/
def oddCompression (u : Aˣ) : M.posProj.range →L[ℂ] M.posProj.range :=
  M.posProj.rangeRestrict ∘L (1 + M.rep (↑u - 1)) ∘L M.posProj.range.subtypeL

theorem oddCompression_def (u : Aˣ) :
    M.oddCompression u =
      M.posProj.rangeRestrict ∘L (1 + M.rep (↑u - 1)) ∘L M.posProj.range.subtypeL :=
  (rfl)

@[simp]
theorem oddToeplitzElem_one : M.oddToeplitzElem 1 = 1 := by
  simp [oddToeplitzElem]

@[simp]
theorem oddToeplitz_one : M.oddToeplitz 1 = 1 := by
  simp [oddToeplitz]

@[simp]
theorem oddIndex_one : M.oddIndex 1 = 0 := by
  rw [oddIndex, M.oddToeplitz_one]
  exact ContinuousLinearMap.index_id

/-- When `M` is normalized (`F² = 1`) and `π` is unital (`π(1) = 1`), `M.oddToeplitzElem a` is
`(1 - P) + P π(a) P`. -/
theorem oddToeplitzElem_eq_of_isNormalized_of_rep_one (hM : M.IsNormalized) (h1 : M.rep 1 = 1)
    (a : A) :
    M.oddToeplitzElem a = (1 - M.posProj) + M.posProj * M.rep a * M.posProj := by
  have hP : M.posProj * M.posProj = M.posProj := (M.isIdempotentElem_posProj hM).eq
  rw [oddToeplitzElem, map_sub, h1]
  calc
    1 + M.posProj * (M.rep a - 1) * M.posProj
      = 1 - M.posProj * M.posProj + M.posProj * M.rep a * M.posProj := by noncomm_ring
    _ = (1 - M.posProj) + M.posProj * M.rep a * M.posProj := by rw [hP]

/-- When `π(1) = 1`, `M.oddCompression u` is the classical Toeplitz compression
`P π(u) : range P →L[ℂ] range P`. -/
theorem oddCompression_eq_of_rep_one (h1 : M.rep 1 = 1) (u : Aˣ) :
    M.oddCompression u =
      M.posProj.rangeRestrict ∘L M.rep ↑u ∘L M.posProj.range.subtypeL := by
  rw [oddCompression, map_sub, h1, add_sub_cancel]

/-- Exact multiplicative defect identity for `oddToeplitzElem` on `H`. -/
theorem oddToeplitzElem_mul_sub (a b : A) :
    M.oddToeplitzElem a * M.oddToeplitzElem b - M.oddToeplitzElem (a * b) =
      M.posProj * (M.rep (a - 1) * (M.posProj * M.posProj - M.posProj)) * M.rep (b - 1) *
          M.posProj +
        M.posProj * M.rep (a - 1) *
          (M.posProj * M.rep (b - 1) - M.rep (b - 1) * M.posProj) * M.posProj +
        M.posProj * M.rep (a - 1) *
          (M.rep (b - 1) * (M.posProj * M.posProj - M.posProj)) := by
  have hab : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  have hrep : M.rep (a * b - 1) =
      M.rep (a - 1) + M.rep (b - 1) + M.rep (a - 1) * M.rep (b - 1) := by
    rw [hab, map_add, map_add, map_mul]
  rw [oddToeplitzElem, oddToeplitzElem, oddToeplitzElem, hrep]
  noncomm_ring

theorem isCompactOperator_oddToeplitzElem_mul_sub (a b : A) :
    IsCompactOperator ⇑(M.oddToeplitzElem a * M.oddToeplitzElem b - M.oddToeplitzElem (a * b)) := by
  rw [M.oddToeplitzElem_mul_sub a b]
  have h₁ : IsCompactOperator
      ⇑(M.posProj * (M.rep (a - 1) * (M.posProj * M.posProj - M.posProj)) * M.rep (b - 1) *
        M.posProj) :=
    (((M.isCompactOperator_rep_mul_posProj_sq_sub (a - 1)).mul_left M.posProj).mul_right
      (M.rep (b - 1))).mul_right M.posProj
  have h₂ : IsCompactOperator
      ⇑(M.posProj * M.rep (a - 1) *
        (M.posProj * M.rep (b - 1) - M.rep (b - 1) * M.posProj) * M.posProj) :=
    ((M.isCompactOperator_posProj_commutator (b - 1)).mul_left
      (M.posProj * M.rep (a - 1))).mul_right M.posProj
  have h₃ : IsCompactOperator
      ⇑(M.posProj * M.rep (a - 1) * (M.rep (b - 1) * (M.posProj * M.posProj - M.posProj))) :=
    (M.isCompactOperator_rep_mul_posProj_sq_sub (b - 1)).mul_left (M.posProj * M.rep (a - 1))
  exact (h₁.add h₂).add h₃

/-- **Fredholmness of the odd Toeplitz operator.** For every `u ∈ Aˣ`, `M.oddToeplitz u` is
Fredholm, with parametrix `M.oddToeplitz u⁻¹` modulo compact operators. -/
theorem isFredholm_oddToeplitz (u : Aˣ) : (M.oddToeplitz u).IsFredholm := by
  refine .of_isCompactOperator_comp_sub_one (S := M.oddToeplitz u⁻¹) ?_ ?_
  · simpa [oddToeplitz, ← ContinuousLinearMap.mul_def] using
      M.isCompactOperator_oddToeplitzElem_mul_sub (↑u⁻¹) ↑u
  · simpa [oddToeplitz, ← ContinuousLinearMap.mul_def] using
      M.isCompactOperator_oddToeplitzElem_mul_sub ↑u (↑u⁻¹)

/-- **Logarithmic additivity of the odd index.** `M.oddIndex (u * v) = M.oddIndex u + M.oddIndex v`
for all `u, v ∈ Aˣ`. -/
@[simp]
theorem oddIndex_mul (u v : Aˣ) : M.oddIndex (u * v) = M.oddIndex u + M.oddIndex v := by
  have hu := M.isFredholm_oddToeplitz u
  have hv := M.isFredholm_oddToeplitz v
  have huv := M.isFredholm_oddToeplitz (u * v)
  let K := M.oddToeplitz u * M.oddToeplitz v - M.oddToeplitz (u * v)
  have hK : IsCompactOperator K := M.isCompactOperator_oddToeplitzElem_mul_sub ↑u ↑v
  have hrw : (M.oddToeplitz u).comp (M.oddToeplitz v) = M.oddToeplitz (u * v) + K := by
    dsimp only [K]
    rw [← ContinuousLinearMap.mul_def]
    exact (add_sub_cancel _ _).symm
  have hcomp := hu.index_comp hv
  rw [← ContinuousLinearMap.index_def, hrw,
    ContinuousLinearMap.index_add_of_isCompactOperator huv hK] at hcomp
  simpa only [oddIndex, ContinuousLinearMap.index_def] using hcomp

/-- Inversion in `Aˣ` negates the odd index pairing. -/
@[simp]
theorem oddIndex_inv (u : Aˣ) : M.oddIndex u⁻¹ = -M.oddIndex u := by
  have h := M.oddIndex_mul u⁻¹ u
  rw [inv_mul_cancel, M.oddIndex_one] at h
  omega

/-- The odd index bundled as an additive homomorphism `Additive Aˣ →+ ℤ`. -/
def oddIndexHom : Additive Aˣ →+ ℤ where
  toFun u := M.oddIndex (Additive.toMul u)
  map_zero' := M.oddIndex_one
  map_add' u v := M.oddIndex_mul (Additive.toMul u) (Additive.toMul v)

@[simp]
theorem oddIndexHom_ofMul (u : Aˣ) : M.oddIndexHom (Additive.ofMul u) = M.oddIndex u :=
  (rfl)

/-- Degenerate odd Fredholm modules have vanishing odd index on every `u ∈ Aˣ`. -/
theorem oddIndex_eq_zero_of_isDegenerate (hdeg : M.IsDegenerate) (u : Aˣ) :
    M.oddIndex u = 0 := by
  have hmul (a b : A) : M.oddToeplitzElem a * M.oddToeplitzElem b = M.oddToeplitzElem (a * b) := by
    refine sub_eq_zero.mp ?_
    rw [M.oddToeplitzElem_mul_sub a b]
    simp only [M.posProj_mul_posProj_sub_posProj, M.posProj_commutator, mul_smul_comm,
      hdeg.rep_mul_mul_self_sub_one_eq_zero, hdeg.commutator_eq_zero, smul_zero, mul_zero,
      zero_mul, add_zero]
  have hleft : M.oddToeplitz u⁻¹ * M.oddToeplitz u = 1 := by
    simpa [oddToeplitz] using hmul (↑u⁻¹) ↑u
  have hright : M.oddToeplitz u * M.oddToeplitz u⁻¹ = 1 := by
    simpa [oddToeplitz] using hmul ↑u (↑u⁻¹)
  have hlinv : Function.LeftInverse (M.oddToeplitz u⁻¹) (M.oddToeplitz u) := fun x ↦ by
    simpa [ContinuousLinearMap.mul_def] using congr($hleft x)
  have hrinv : Function.RightInverse (M.oddToeplitz u⁻¹) (M.oddToeplitz u) := fun y ↦ by
    simpa [ContinuousLinearMap.mul_def] using congr($hright y)
  exact ContinuousLinearMap.index_eq_zero_of_bijective _ ⟨hlinv.injective, hrinv.surjective⟩

/-- On a finite-dimensional Hilbert space, every odd Fredholm module has vanishing odd index. -/
theorem oddIndex_eq_zero_of_finiteDimensional [FiniteDimensional ℂ H] (u : Aˣ) :
    M.oddIndex u = 0 := by
  rw [oddIndex, ContinuousLinearMap.index_eq_of_finiteDimensional, sub_self]

/-- When `M` is normalized (`F² = 1`), the topological direct-sum equivalence
`range P × ker P ≃L[ℂ] H` intertwines `M.oddCompression u ⊕ id` with `M.oddToeplitz u`. -/
theorem oddToeplitz_comp_prodEquivOfIsTopCompl (hM : M.IsNormalized) (u : Aˣ) :
    (M.oddToeplitz u).comp
        ((M.posProj.range.prodEquivOfIsTopCompl M.posProj.ker
          (ContinuousLinearMap.IsIdempotentElem.isTopCompl (M.isIdempotentElem_posProj hM)) :
            (M.posProj.range × M.posProj.ker) →L[ℂ] H)) =
      ((M.posProj.range.prodEquivOfIsTopCompl M.posProj.ker
          (ContinuousLinearMap.IsIdempotentElem.isTopCompl (M.isIdempotentElem_posProj hM)) :
            (M.posProj.range × M.posProj.ker) →L[ℂ] H)).comp
        ((M.oddCompression u).prodMap (.id ℂ M.posProj.ker)) := by
  have hP := M.isIdempotentElem_posProj hM
  have hrr (z : H) : (M.posProj.rangeRestrict z : H) = M.posProj z := rfl
  have he {h} (z : M.posProj.range × M.posProj.ker) :
      M.posProj.range.prodEquivOfIsTopCompl M.posProj.ker h z = (z.1 : H) + z.2 := rfl
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ ↦ ?_
  have hx : M.posProj x = x := ContinuousLinearMap.IsIdempotentElem.apply_coe_range hP x
  have hy : M.posProj y = 0 := LinearMap.mem_ker.mp y.2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, he,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.id_apply, oddToeplitz,
    oddToeplitzElem, oddCompression, add_apply, one_apply_eq_self, ContinuousLinearMap.mul_def,
    Submodule.subtypeL_apply, Submodule.coe_add, hrr, map_add, map_zero, hx, hy, add_zero]

/-- When `M` is normalized (`F² = 1`), the compressed Toeplitz operator `M.oddCompression u` on
`range ((1 + F) / 2)` is Fredholm. -/
theorem isFredholm_oddCompression (hM : M.IsNormalized) (u : Aˣ) :
    (M.oddCompression u).IsFredholm := by
  let htop := ContinuousLinearMap.IsIdempotentElem.isTopCompl (M.isIdempotentElem_posProj hM)
  let e := M.posProj.range.prodEquivOfIsTopCompl M.posProj.ker htop
  have hconj := (M.oddToeplitz_comp_prodEquivOfIsTopCompl hM u).symm
  have hprod : ((M.oddCompression u).prodMap (.id ℂ M.posProj.ker)).IsFredholm :=
    (ContinuousLinearMap.isFredholm_iff_of_comp_eq e e hconj).mpr (M.isFredholm_oddToeplitz u)
  exact hprod.of_prodMap_left

/-- When `M` is normalized (`F² = 1`), the Fredholm index of `M.oddCompression u` agrees with
`M.oddIndex u`. -/
@[simp]
theorem index_oddCompression_eq_oddIndex (hM : M.IsNormalized) (u : Aˣ) :
    (M.oddCompression u).index = M.oddIndex u := by
  let htop := ContinuousLinearMap.IsIdempotentElem.isTopCompl (M.isIdempotentElem_posProj hM)
  let e := M.posProj.range.prodEquivOfIsTopCompl M.posProj.ker htop
  let eL : (M.posProj.range × M.posProj.ker) →L[ℂ] H := e
  have hcomp := M.isFredholm_oddCompression hM u
  have hid : (ContinuousLinearMap.id ℂ M.posProj.ker).IsFredholm := .id
  have := hcomp.finite_ker
  have := hid.finite_ker
  have := hcomp.finite_coker
  have := hid.finite_coker
  have hconj : (M.oddToeplitz u).comp eL =
      eL.comp ((M.oddCompression u).prodMap (.id ℂ M.posProj.ker)) :=
    M.oddToeplitz_comp_prodEquivOfIsTopCompl hM u
  rw [oddIndex]
  calc
    (M.oddCompression u).index
      = (M.oddCompression u).index + (ContinuousLinearMap.id ℂ M.posProj.ker).index := by simp
    _ = ((M.oddCompression u).prodMap (.id ℂ M.posProj.ker)).index :=
          ((M.oddCompression u).index_prodMap (.id ℂ M.posProj.ker)).symm
    _ = (eL.comp ((M.oddCompression u).prodMap (.id ℂ M.posProj.ker))).index :=
          (((M.oddCompression u).prodMap (.id ℂ M.posProj.ker)).index_equiv_comp e).symm
    _ = ((M.oddToeplitz u).comp eL).index := by rw [hconj]
    _ = (M.oddToeplitz u).index := (M.oddToeplitz u).index_comp_equiv e

/-- Two odd Fredholm modules with the same representation and operator difference compact relative
to `π` have the same odd index at `u`. -/
theorem oddIndex_eq_of_isCompactOperator_sub_mul_rep {M' : FredholmModule A H} (u : Aˣ)
    (hrep : ∀ a, M'.rep a = M.rep a)
    (hKc : ∀ a, IsCompactOperator ⇑((M'.operator - M.operator) * M.rep a)) :
    M'.oddIndex u = M.oddIndex u := by
  have hFred : (1 + M.posProj * M.rep (↑u - 1) * M.posProj).IsFredholm :=
    M.isFredholm_oddToeplitz u
  have h1 := isCompactOperator_posProj_sub_mul_rep M M' hKc (↑u - 1)
  have h2 := isCompactOperator_rep_mul_posProj_sub M M' hKc (↑u - 1)
  rw [oddIndex_def, oddIndex_def, oddToeplitz_def, oddToeplitz_def, oddToeplitzElem_def,
    oddToeplitzElem_def, hrep (↑u - 1)]
  exact ContinuousLinearMap.index_one_add_mul_eq _ _ _ hFred h1 h2

/-- Relatively compact perturbations leave the odd index unchanged. -/
@[simp]
theorem oddIndex_perturb (K : H →L[ℂ] H) (hK : IsSelfAdjoint K)
    (hKc : ∀ a, IsCompactOperator ⇑(K * M.rep a)) (u : Aˣ) :
    (M.perturb K hK hKc).oddIndex u = M.oddIndex u :=
  M.oddIndex_eq_of_isCompactOperator_sub_mul_rep u (by simp) (fun a ↦ by simpa using hKc a)

/-- Unitary equivalence leaves the odd index unchanged. -/
@[simp]
theorem oddIndex_conj (U : H ≃ₗᵢ[ℂ] H') (u : Aˣ) :
    (M.conj U).oddIndex u = M.oddIndex u := by
  let eU : H ≃L[ℂ] H' := U.toContinuousLinearEquiv
  have hconj (T : H →L[ℂ] H) :
      U.conjStarAlgEquiv T =
        ((eU : H →L[ℂ] H').comp T).comp (eU.symm : H' →L[ℂ] H) := by
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ← LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearMap.comp_assoc]
  have hT : (M.conj U).oddToeplitz u =
      ((eU : H →L[ℂ] H').comp (M.oddToeplitz u)).comp (eU.symm : H' →L[ℂ] H) := by
    rw [← hconj]
    simp [oddToeplitz_def, oddToeplitzElem_def, posProj_def, map_add, map_mul, map_smul, map_one]
  rw [oddIndex_def, oddIndex_def, hT, ContinuousLinearMap.index_comp_equiv,
    ContinuousLinearMap.index_equiv_comp]

/-- Orthogonal direct sums add odd indices. -/
@[simp]
theorem oddIndex_prod (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) (u : Aˣ) :
    (M₁.prod M₂).oddIndex u = M₁.oddIndex u + M₂.oddIndex u := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂
  let eSymm : (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := e.symm
  have hP : (M₁.prod M₂).posProj = M₁.posProj.withLpProdMap 2 M₂.posProj := by
    rw [posProj, posProj, posProj, prod_operator, ← ContinuousLinearMap.withLpProdMap_one,
      ← ContinuousLinearMap.withLpProdMap_add, ContinuousLinearMap.withLpProdMap_smul]
  have hprod : (M₁.prod M₂).oddToeplitz u =
      (M₁.oddToeplitz u).withLpProdMap 2 (M₂.oddToeplitz u) := by
    rw [oddToeplitz, oddToeplitz, oddToeplitz, oddToeplitzElem, oddToeplitzElem, oddToeplitzElem,
      hP, prod_rep_apply, ContinuousLinearMap.withLpProdMap_mul,
      ContinuousLinearMap.withLpProdMap_mul, ← ContinuousLinearMap.withLpProdMap_one,
      ← ContinuousLinearMap.withLpProdMap_add]
  have hconj :
      ((M₁.oddToeplitz u).withLpProdMap 2 (M₂.oddToeplitz u)).comp eSymm =
        eSymm.comp ((M₁.oddToeplitz u).prodMap (M₂.oddToeplitz u)) := by
    refine ContinuousLinearMap.ext fun ⟨x₁, x₂⟩ ↦ ?_
    apply e.injective
    ext <;> simp [eSymm, e]
  have h₁ := M₁.isFredholm_oddToeplitz u
  have h₂ := M₂.isFredholm_oddToeplitz u
  have := h₁.finite_ker
  have := h₂.finite_ker
  have := h₁.finite_coker
  have := h₂.finite_coker
  rw [oddIndex, oddIndex, oddIndex, hprod]
  calc
    ((M₁.oddToeplitz u).withLpProdMap 2 (M₂.oddToeplitz u)).index
      = (((M₁.oddToeplitz u).withLpProdMap 2 (M₂.oddToeplitz u)).comp eSymm).index :=
          (((M₁.oddToeplitz u).withLpProdMap 2 (M₂.oddToeplitz u)).index_comp_equiv e.symm).symm
    _ = (eSymm.comp ((M₁.oddToeplitz u).prodMap (M₂.oddToeplitz u))).index := by rw [hconj]
    _ = ((M₁.oddToeplitz u).prodMap (M₂.oddToeplitz u)).index :=
          ((M₁.oddToeplitz u).prodMap (M₂.oddToeplitz u)).index_equiv_comp e.symm
    _ = (M₁.oddToeplitz u).index + (M₂.oddToeplitz u).index :=
          (M₁.oddToeplitz u).index_prodMap (M₂.oddToeplitz u)

/-- The linear operator homotopy to `sin(π F / 2)` preserves the odd index at every `u ∈ Aˣ`. -/
@[simp]
theorem oddIndex_sinContractionHomotopy (t : ℝ) (u : Aˣ) :
    (M.sinContractionHomotopy t).oddIndex u = M.oddIndex u := by
  refine M.oddIndex_eq_of_isCompactOperator_sub_mul_rep u (by simp) fun a ↦ ?_
  have hsub : (M.sinContractionHomotopy t).operator - M.operator = (t : ℂ) • M.sinPerturbation := by
    simp
  rw [hsub, smul_mul_assoc, FunLike.coe_smul]
  exact (M.isCompactOperator_sinPerturbation_mul_rep a).smul (t : ℂ)

/-- Spectral contraction `sin(π F / 2)` preserves the odd index at every `u ∈ Aˣ`. -/
@[simp]
theorem oddIndex_sinContraction (u : Aˣ) :
    M.sinContraction.oddIndex u = M.oddIndex u := by
  rw [← M.sinContractionHomotopy_one, M.oddIndex_sinContractionHomotopy 1 u]

/-- The doubling operator homotopy preserves the odd index at every `u ∈ Aˣ`. -/
@[simp]
theorem oddIndex_doubleHomotopy (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) (u : Aˣ) :
    (M.doubleHomotopy hF t).oddIndex u = M.oddIndex u := by
  let M₀ := M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg)
  have hhom : (M.doubleHomotopy hF t).oddIndex u = M₀.oddIndex u := by
    refine M₀.oddIndex_eq_of_isCompactOperator_sub_mul_rep u (by simp [M₀]) fun a ↦ ?_
    have hsub :
        (M.doubleHomotopy hF t).operator - M₀.operator =
          (t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation := by
      simp [M₀]
    have hrep0 : M₀.rep a = (M.rep a).withLpProdMap 2 0 := by simp [M₀]
    rw [hsub, hrep0, smul_mul_assoc, FunLike.coe_smul]
    exact ((ContinuousLinearMap.isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
      _ _).mpr (M.isCompactOperator_sqrt_one_sub_mul_rep hF a)).smul (t : ℂ)
  rw [hhom, FredholmModule.oddIndex_prod,
    FredholmModule.oddIndex_eq_zero_of_isDegenerate _ (isDegenerate_zeroRep _ _) u, add_zero]

/-- Contraction doubling preserves the odd index at every `u ∈ Aˣ`. -/
@[simp]
theorem oddIndex_double (hF : 0 ≤ 1 - M.operator * M.operator) (u : Aˣ) :
    (M.double hF).oddIndex u = M.oddIndex u := by
  rw [← M.doubleHomotopy_one hF, M.oddIndex_doubleHomotopy hF 1 u]

/-- **Normalization preserves the odd index.** Passing from an arbitrary odd Fredholm module `M`
to its normalized (`F² = 1`) module `M.normalize` leaves the index pairing with every invertible
element `u ∈ Aˣ` unchanged. -/
@[simp]
theorem oddIndex_normalize (u : Aˣ) :
    M.normalize.oddIndex u = M.oddIndex u := by
  rw [M.normalize_def, M.sinContraction.oddIndex_double _ u, M.oddIndex_sinContraction u]

end OddPairing

end FredholmModule

end TauCeti
