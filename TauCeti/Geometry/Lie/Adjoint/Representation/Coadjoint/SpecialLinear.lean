/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.SpecialLinear
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.Stabilizer

/-!
# Coadjoint orbits of the real special linear group

Let `G = SL(n, ℝ)` with its native Lie group structure and tangent Lie algebra
`𝔤 = GroupLieAlgebra 𝓘(ℝ, Model n ℝ) G`. The differential at the identity of the matrix inclusion
identifies `𝔤` with the trace-zero matrices
(`Matrix.SpecialLinearGroup.range_mvfderiv_subtypeVal_one`) and carries the adjoint action to
conjugation (`Matrix.SpecialLinearGroup.mvfderiv_subtypeVal_adjointContinuousLinearMap`).

Pairing through the trace form, a matrix `Y` gives the covector `ν_Y(ξ) = tr(Y X_ξ)` on `𝔤`,
where `X_ξ` is the matrix of `ξ` (`Matrix.SpecialLinearGroup.tracePairing`). The trace form is
invariant, so the coadjoint action becomes conjugation as well, `Ad*_g ν_Y = ν_(g Y g⁻¹)`
(`Matrix.SpecialLinearGroup.coadjointRepresentation_tracePairing`), and the trace form is
nondegenerate on trace-zero matrices, since `tr(Y Yᵀ)` is the sum of the squares of the entries of
`Y`. So `Y ↦ ν_Y` identifies the trace-zero matrices with `𝔤*`
(`Matrix.SpecialLinearGroup.tracePairingEquiv`), and every coadjoint orbit is the image of an orbit
of conjugation (`Matrix.SpecialLinearGroup.range_orbitMap_coadjointRepresentation_tracePairing`).

For `SL(2, ℝ)` and the nilpotent matrix `E = [[0, 1], [0, 0]]` (`Matrix.single 0 1 1`), conjugation
by `g = [[a, b], [c, d]]` gives `g E g⁻¹ = [[-a c, a²], [-c², a c]]`. Hence the conjugation orbit of
`E` is one half of the punctured nilpotent cone `{Y | tr Y = 0, det Y = 0, Y ≠ 0}`, the half with
`Y₀₁ ≥ 0 ≥ Y₁₀` (`Matrix.SpecialLinearGroup.range_coe_mul_single_mul_coe_inv`), and the orbit of
`-E` is the other half. Accordingly the coadjoint orbits of `ν_E` and of `-ν_E` are disjoint and
their union is the image of the punctured nilpotent cone
(`Matrix.SpecialLinearGroup.range_orbitMap_coadjointRepresentation_tracePairing_single_union`,
`Matrix.SpecialLinearGroup.disjoint_range_orbitMap_coadjointRepresentation_tracePairing_single`).

The coadjoint orbit of `ν_E` is not closed. Conjugation by `diag(t, t⁻¹)` scales `E` by `t²`, so
`t² ν_E` lies on the orbit for every `t ≠ 0` and tends to `0` as `t → 0`, while `0` does not lie on
the orbit. Reading covectors in the continuous dual `StrongDual ℝ 𝔤`, the image of the orbit map
`ι_ν : G ⧸ G_ν → 𝔤*` of `ν = ν_E` has `0` in its closure and is not closed. So, for a noncompact
group, the injective orbit map `ι_ν` need not have closed image.

## Main definitions

All declarations are in the namespace `Matrix.SpecialLinearGroup`.

* `tracePairing`: the covector `ξ ↦ tr(Y X_ξ)` of a matrix `Y`.
* `tracePairingEquiv`: the trace form identifies the trace-zero matrices with `𝔤*`.

## Main results

* `coadjointRepresentation_tracePairing`: `Ad*_g ν_Y = ν_(g Y g⁻¹)`.
* `range_coe_mul_single_mul_coe_inv`: the conjugation orbit of `E` in `SL(2, ℝ)` is one half of
  the punctured nilpotent cone.
* `range_orbitMap_coadjointRepresentation_tracePairing_single`: the same for the coadjoint orbit
  of `ν_E`.
* `not_isClosed_range_orbitMap_coadjointRepresentation_tracePairing_single`: the coadjoint orbit
  of `ν_E` is not closed in `𝔤*`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

noncomputable section

open Filter Matrix Manifold Topology TauCeti TauCeti.Lie
open scoped Manifold ContDiff MatrixGroups Matrix.Norms.Operator

namespace Matrix.SpecialLinearGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-! ### The trace form -/

section TracePairing

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "𝔤" n => GroupLieAlgebra 𝓘(ℝ, Model n ℝ) (SpecialLinearGroup n ℝ)

variable (n) in
/-- The covector `ξ ↦ tr(Y X_ξ)` on the Lie algebra of `SL(n, ℝ)` given by a matrix `Y`, where
`X_ξ` is the matrix of `ξ` under the differential of the matrix inclusion at the identity. -/
def tracePairing : Matrix n n ℝ →ₗ[ℝ] Module.Dual ℝ (𝔤 n) :=
  ((LinearMap.mul ℝ (Matrix n n ℝ)).compr₂ (traceLinearMap n ℝ ℝ)).compl₂
    (mvfderiv 𝓘(ℝ, Model n ℝ) (fun A : SpecialLinearGroup n ℝ ↦ (A : Matrix n n ℝ)) 1 :
      (𝔤 n) →ₗ[ℝ] Matrix n n ℝ)

@[simp]
theorem tracePairing_apply (Y : Matrix n n ℝ) (ξ : 𝔤 n) :
    tracePairing n Y ξ = (Y * mvfderiv 𝓘(ℝ, Model n ℝ)
      (fun A : SpecialLinearGroup n ℝ ↦ (A : Matrix n n ℝ)) 1 ξ).trace :=
  (rfl)

/-- **The trace form is invariant**: the coadjoint action on `ν_Y` is conjugation of `Y`,
`Ad*_g ν_Y = ν_(g Y g⁻¹)`. -/
@[simp]
theorem coadjointRepresentation_tracePairing (g : SpecialLinearGroup n ℝ) (Y : Matrix n n ℝ) :
    coadjointRepresentation ℝ 𝓘(ℝ, Model n ℝ) (SpecialLinearGroup n ℝ) g (tracePairing n Y) =
      tracePairing n
        ((g : Matrix n n ℝ) * Y * ((g⁻¹ : SpecialLinearGroup n ℝ) : Matrix n n ℝ)) := by
  ext ξ
  rw [coadjointRepresentation_apply, tracePairing_apply, tracePairing_apply,
    mvfderiv_subtypeVal_adjointContinuousLinearMap, inv_inv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- The trace form is nondegenerate on trace-zero matrices: such a matrix `Y` gives the zero
covector only when `Y = 0`. -/
theorem tracePairing_eq_zero_iff {Y : Matrix n n ℝ} (hY : Y.trace = 0) :
    tracePairing n Y = 0 ↔ Y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  -- Pair `Y` with the matrix of a Lie algebra element whose matrix is `Yᵀ`.
  obtain ⟨ξ, hξ⟩ : Yᵀ ∈ (mvfderiv 𝓘(ℝ, Model n ℝ)
      (fun A : SpecialLinearGroup n ℝ ↦ (A : Matrix n n ℝ)) 1).range := by
    rw [range_mvfderiv_subtypeVal_one]
    simpa using hY
  have hYY := LinearMap.congr_fun h ξ
  rw [ContinuousLinearMap.coe_coe] at hξ
  rw [tracePairing_apply, hξ, LinearMap.zero_apply, ← conjTranspose_eq_transpose_of_trivial] at hYY
  exact trace_mul_conjTranspose_self_eq_zero_iff.mp hYY

/-- Distinct trace-zero matrices give distinct covectors. -/
theorem injOn_tracePairing : Set.InjOn (tracePairing n) {Y | Y.trace = 0} := by
  intro Y hY Y' hY' h
  rw [← sub_eq_zero, ← tracePairing_eq_zero_iff (by simp [trace_sub, hY.out, hY'.out]), map_sub, h,
    sub_self]

variable (n) in
/-- The trace form identifies the trace-zero matrices with the dual of the Lie algebra of
`SL(n, ℝ)`, by `Y ↦ (ξ ↦ tr(Y X_ξ))`. -/
def tracePairingEquiv : LinearMap.ker (traceLinearMap n ℝ ℝ) ≃ₗ[ℝ] Module.Dual ℝ (𝔤 n) :=
  LinearEquiv.ofBijective ((tracePairing n).domRestrict _) <| by
    have hinj : Function.Injective
        ((tracePairing n).domRestrict (LinearMap.ker (traceLinearMap n ℝ ℝ))) := fun Y Y' h ↦
      Subtype.ext (injOn_tracePairing (LinearMap.mem_ker.mp Y.property)
        (LinearMap.mem_ker.mp Y'.property) h)
    refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
    rw [Subspace.dual_finrank_eq, ← range_mvfderiv_subtypeVal_one,
      LinearMap.finrank_range_of_inj (injective_mvfderiv_subtypeVal 1)]

@[simp]
theorem tracePairingEquiv_apply (Y : LinearMap.ker (traceLinearMap n ℝ ℝ)) :
    tracePairingEquiv n Y = tracePairing n Y :=
  (rfl)

/-- The coadjoint orbit of `ν_(Y₀)` is the image of the conjugation orbit of `Y₀`. -/
theorem range_orbitMap_coadjointRepresentation_tracePairing (Y₀ : Matrix n n ℝ) :
    Set.range (Representation.orbitMap
        (coadjointRepresentation ℝ 𝓘(ℝ, Model n ℝ) (SpecialLinearGroup n ℝ)) (tracePairing n Y₀)) =
      tracePairing n '' Set.range (fun g : SpecialLinearGroup n ℝ ↦
        (g : Matrix n n ℝ) * Y₀ * ((g⁻¹ : SpecialLinearGroup n ℝ) : Matrix n n ℝ)) := by
  rw [Representation.range_orbitMap, ← Set.range_comp]
  exact congrArg Set.range (funext fun g ↦ coadjointRepresentation_tracePairing g Y₀)

end TracePairing

/-! ### The nilpotent orbits of `SL(2, ℝ)` -/

section Nilpotent

/-- Conjugating `E = [[0, 1], [0, 0]]` by `g = [[a, b], [c, d]]` in `SL(2, ℝ)` gives
`[[-a c, a²], [-c², a c]]`. -/
theorem coe_mul_single_mul_coe_inv (g : SL(2, ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) * single 0 1 1 * ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-(g 0 0 * g 1 0), g 0 0 ^ 2; -(g 1 0 ^ 2), g 0 0 * g 1 0] := by
  rw [SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, single_apply] <;> ring

/-- Every nonzero trace-zero matrix of determinant zero with `Y₀₁ ≥ 0 ≥ Y₁₀` is conjugate to
`E = [[0, 1], [0, 0]]` in `SL(2, ℝ)`, written with the formula of `coe_mul_single_mul_coe_inv`. -/
private theorem exists_eq_of_trace_eq_zero_of_det_eq_zero {Y : Matrix (Fin 2) (Fin 2) ℝ}
    (htr : Y.trace = 0) (hdet : Y.det = 0) (hne : Y ≠ 0) (hy : 0 ≤ Y 0 1) (hz : Y 1 0 ≤ 0) :
    ∃ g : SL(2, ℝ), !![-(g 0 0 * g 1 0), g 0 0 ^ 2; -(g 1 0 ^ 2), g 0 0 * g 1 0] = Y := by
  rw [trace_fin_two] at htr
  rw [det_fin_two] at hdet
  have h11 : Y 1 1 = -Y 0 0 := by linarith
  have hx : Y 0 0 ^ 2 = Y 0 1 * -Y 1 0 := by linear_combination Y 0 0 * htr - hdet
  have hpos : 0 < Y 0 1 - Y 1 0 := by
    by_contra! hle
    have h01 : Y 0 1 = 0 := by linarith
    have h10 : Y 1 0 = 0 := by linarith
    have h00 : Y 0 0 = 0 := by nlinarith
    refine hne ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  -- Solve `a² = Y₀₁`, `c² = -Y₁₀`, `a c = -Y₀₀`, then complete `(a, c)` to an element of
  -- `SL(2, ℝ)`.
  have habs : √(Y 0 1) * √(-Y 1 0) = |Y 0 0| := by
    rw [← Real.sqrt_mul hy, ← hx, Real.sqrt_sq_eq_abs]
  obtain ⟨c, hc, hac⟩ : ∃ c : ℝ, c ^ 2 = -Y 1 0 ∧ √(Y 0 1) * c = -Y 0 0 := by
    rcases le_or_gt (Y 0 0) 0 with h | h
    · exact ⟨√(-Y 1 0), Real.sq_sqrt (by linarith), by rw [habs, abs_of_nonpos h]⟩
    · exact ⟨-√(-Y 1 0), by rw [neg_sq, Real.sq_sqrt (by linarith)],
        by rw [mul_neg, habs, abs_of_pos h]⟩
  have ha : √(Y 0 1) ^ 2 = Y 0 1 := Real.sq_sqrt hy
  refine ⟨⟨!![√(Y 0 1), -c / (Y 0 1 - Y 1 0); c, √(Y 0 1) / (Y 0 1 - Y 1 0)], ?_⟩, ?_⟩
  · rw [det_fin_two_of]
    field_simp
    linear_combination ha + hc
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
        cons_val_one, Fin.zero_eta, Fin.mk_one]
    · linear_combination -hac
    · exact ha
    · linear_combination -hc
    · linear_combination hac - h11

/-- **The conjugation orbit of `E = [[0, 1], [0, 0]]` in `SL(2, ℝ)`** is one half of the punctured
nilpotent cone: the nonzero trace-zero matrices of determinant zero with `Y₀₁ ≥ 0 ≥ Y₁₀`. -/
theorem range_coe_mul_single_mul_coe_inv :
    Set.range (fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) * single 0 1 1 *
        ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) =
      {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ 0 ≤ Y 0 1 ∧ Y 1 0 ≤ 0} := by
  ext Y
  simp only [Set.mem_range, Set.mem_ofPred_eq, coe_mul_single_mul_coe_inv]
  constructor
  · rintro ⟨g, rfl⟩
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      rw [← det_fin_two]
      exact g.property
    refine ⟨by simp [trace_fin_two], by simp [det_fin_two]; ring, fun h ↦ ?_, by simp [sq_nonneg],
      by simp [sq_nonneg]⟩
    have h0 : g 0 0 = 0 := by simpa using congrFun (congrFun h 0) 1
    have h1 : g 1 0 = 0 := by simpa using congrFun (congrFun h 1) 0
    simp [h0, h1] at hdet
  · rintro ⟨htr, hdet, hne, hy, hz⟩
    exact exists_eq_of_trace_eq_zero_of_det_eq_zero htr hdet hne hy hz

/-- The conjugation orbit of `-E` in `SL(2, ℝ)` is the other half of the punctured nilpotent cone,
the matrices with `Y₀₁ ≤ 0 ≤ Y₁₀`. -/
theorem range_coe_mul_neg_single_mul_coe_inv :
    Set.range (fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) * -single 0 1 1 *
        ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) =
      {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ Y 0 1 ≤ 0 ∧ 0 ≤ Y 1 0} := by
  ext Y
  have h := Set.ext_iff.mp range_coe_mul_single_mul_coe_inv (-Y)
  simp only [Set.mem_range, Set.mem_ofPred_eq, trace_neg, det_neg, Matrix.neg_apply, neg_eq_zero,
    neg_ne_zero, neg_nonneg, neg_nonpos, Fintype.card_fin, even_two, Even.neg_one_pow, one_mul]
    at h ⊢
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_eq_iff_eq_neg]
  exact h

/-- The punctured nilpotent cone of `𝔰𝔩(2, ℝ)` is the union of its two halves. -/
private theorem setOf_trace_eq_zero_det_eq_zero_ne_zero_eq_union :
    {Y : Matrix (Fin 2) (Fin 2) ℝ | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0} =
      {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ 0 ≤ Y 0 1 ∧ Y 1 0 ≤ 0} ∪
        {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ Y 0 1 ≤ 0 ∧ 0 ≤ Y 1 0} := by
  ext Y
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨htr, hdet, hne⟩
    have hprod : Y 0 1 * Y 1 0 = -Y 0 0 ^ 2 := by
      rw [trace_fin_two] at htr
      rw [det_fin_two] at hdet
      linear_combination Y 0 0 * htr - hdet
    -- The off-diagonal entries have product `-Y₀₀² ≤ 0`, so they have opposite signs.
    rcases le_total 0 (Y 0 1) with h | h <;> rcases le_total 0 (Y 1 0) with h' | h'
    · rcases mul_eq_zero.mp (le_antisymm (hprod ▸ neg_nonpos.mpr (sq_nonneg _))
        (mul_nonneg h h')) with h0 | h0
      · exact .inr ⟨htr, hdet, hne, h0.le, h'⟩
      · exact .inl ⟨htr, hdet, hne, h, h0.le⟩
    · exact .inl ⟨htr, hdet, hne, h, h'⟩
    · exact .inr ⟨htr, hdet, hne, h, h'⟩
    · rcases mul_eq_zero.mp (le_antisymm (hprod ▸ neg_nonpos.mpr (sq_nonneg _))
        (mul_nonneg_of_nonpos_of_nonpos h h')) with h0 | h0
      · exact .inl ⟨htr, hdet, hne, h0.ge, h'⟩
      · exact .inr ⟨htr, hdet, hne, h, h0.ge⟩
  · rintro (⟨htr, hdet, hne, -⟩ | ⟨htr, hdet, hne, -⟩) <;> exact ⟨htr, hdet, hne⟩

/-- The two halves of the punctured nilpotent cone of `𝔰𝔩(2, ℝ)` are disjoint. -/
private theorem disjoint_setOf_nilpotent_halves :
    Disjoint
      {Y : Matrix (Fin 2) (Fin 2) ℝ | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ 0 ≤ Y 0 1 ∧ Y 1 0 ≤ 0}
      {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ Y 0 1 ≤ 0 ∧ 0 ≤ Y 1 0} := by
  rw [Set.disjoint_left]
  rintro Y ⟨htr, hdet, hne, hy, hz⟩ ⟨-, -, -, hy', hz'⟩
  rw [trace_fin_two] at htr
  rw [det_fin_two] at hdet
  have h01 : Y 0 1 = 0 := le_antisymm hy' hy
  have h10 : Y 1 0 = 0 := le_antisymm hz hz'
  have h00 : Y 0 0 = 0 := by nlinarith
  have h11 : Y 1 1 = 0 := by linarith
  exact hne (by ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11])

local notation "𝔰𝔩₂" => GroupLieAlgebra 𝓘(ℝ, Model (Fin 2) ℝ) SL(2, ℝ)
local notation "Ad*" => coadjointRepresentation ℝ 𝓘(ℝ, Model (Fin 2) ℝ) SL(2, ℝ)

/-- **The coadjoint orbit of `ν_E` in `SL(2, ℝ)`**, for `E = [[0, 1], [0, 0]]`, is the image of one
half of the punctured nilpotent cone under the trace form. -/
theorem range_orbitMap_coadjointRepresentation_tracePairing_single :
    Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) =
      tracePairing (Fin 2) '' {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ 0 ≤ Y 0 1 ∧ Y 1 0 ≤ 0} := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing, range_coe_mul_single_mul_coe_inv]

/-- The coadjoint orbit of `-ν_E` in `SL(2, ℝ)` is the image of the other half of the punctured
nilpotent cone. -/
theorem range_orbitMap_coadjointRepresentation_neg_tracePairing_single :
    Set.range (Representation.orbitMap Ad* (-tracePairing (Fin 2) (single 0 1 1))) =
      tracePairing (Fin 2) '' {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ Y 0 1 ≤ 0 ∧ 0 ≤ Y 1 0} := by
  rw [← map_neg, range_orbitMap_coadjointRepresentation_tracePairing,
    range_coe_mul_neg_single_mul_coe_inv]

/-- The coadjoint orbits of `ν_E` and `-ν_E` in `SL(2, ℝ)` together make up the image of the
punctured nilpotent cone under the trace form. -/
theorem range_orbitMap_coadjointRepresentation_tracePairing_single_union :
    Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) ∪
        Set.range (Representation.orbitMap Ad* (-tracePairing (Fin 2) (single 0 1 1))) =
      tracePairing (Fin 2) '' {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0} := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing_single,
    range_orbitMap_coadjointRepresentation_neg_tracePairing_single, ← Set.image_union,
    setOf_trace_eq_zero_det_eq_zero_ne_zero_eq_union]

/-- The coadjoint orbits of `ν_E` and `-ν_E` in `SL(2, ℝ)` are disjoint: each is one half of the
punctured nilpotent cone. -/
theorem disjoint_range_orbitMap_coadjointRepresentation_tracePairing_single :
    Disjoint (Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))))
      (Set.range (Representation.orbitMap Ad* (-tracePairing (Fin 2) (single 0 1 1)))) := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing_single,
    range_orbitMap_coadjointRepresentation_neg_tracePairing_single]
  exact disjoint_setOf_nilpotent_halves.image injOn_tracePairing (fun Y hY ↦ hY.1) fun Y hY ↦ hY.1

/-- The zero covector does not lie on the coadjoint orbit of `ν_E` in `SL(2, ℝ)`. -/
theorem zero_notMem_range_orbitMap_coadjointRepresentation_tracePairing_single :
    0 ∉ Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing_single]
  rintro ⟨Y, hY, h0⟩
  exact hY.2.2.1 ((tracePairing_eq_zero_iff hY.1).mp h0)

/-- The zero covector lies in the closure of the coadjoint orbit of `ν_E` in `SL(2, ℝ)`, read in
the continuous dual: the orbit contains `t² ν_E` for every `t ≠ 0`. -/
theorem zero_mem_closure_range_orbitMap_coadjointRepresentation_tracePairing_single :
    (0 : StrongDual ℝ 𝔰𝔩₂) ∈ closure (LinearMap.toContinuousLinearMap ''
      Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1)))) := by
  have hmem (t : ℝ) (ht : t ≠ 0) : t ^ 2 • tracePairing (Fin 2) (single 0 1 1) ∈
      Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) := by
    rw [range_orbitMap_coadjointRepresentation_tracePairing_single, ← map_smul]
    refine Set.mem_image_of_mem _ ⟨by simp, by simp [det_fin_two], ?_, by simp [sq_nonneg],
      by simp⟩
    exact fun h ↦ pow_ne_zero 2 ht (by simpa using congrFun (congrFun h 0) 1)
  refine mem_closure_of_tendsto (b := 𝓝[≠] (0 : ℝ))
    (f := fun t : ℝ ↦ t ^ 2 • LinearMap.toContinuousLinearMap (tracePairing (Fin 2) (single 0 1 1)))
    ?_ ?_
  · have hc : Continuous fun t : ℝ ↦
        t ^ 2 • LinearMap.toContinuousLinearMap (tracePairing (Fin 2) (single 0 1 1)) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨_, hmem t ht, map_smul _ _ _⟩

/-- **The coadjoint orbit of a nonzero nilpotent element of `SL(2, ℝ)` is not closed.** The image
of the orbit map `G ⧸ G_ν → 𝔤*` of `ν = ν_E`, read in the continuous dual, is not closed. -/
theorem not_isClosed_range_orbitMap_coadjointRepresentation_tracePairing_single :
    ¬ IsClosed (LinearMap.toContinuousLinearMap ''
      Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) :
        Set (StrongDual ℝ 𝔰𝔩₂)) := by
  intro h
  obtain ⟨ν, hν, h0⟩ := h.closure_eq ▸
    zero_mem_closure_range_orbitMap_coadjointRepresentation_tracePairing_single
  rw [LinearEquiv.map_eq_zero_iff] at h0
  exact zero_notMem_range_orbitMap_coadjointRepresentation_tracePairing_single (h0 ▸ hν)

end Nilpotent

end Matrix.SpecialLinearGroup
