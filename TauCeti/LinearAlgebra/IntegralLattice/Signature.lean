/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Signature and definiteness of integral lattices

This file defines the radical and signature `(n₊, n₀, n₋)` of an integral symmetric lattice and
the standard definiteness predicates. The indices of inertia are Mathlib's `sigPos`
and `sigNeg`; the null index is the dimension of the kernel of the bilinear form.

Positive- and negative-semidefiniteness are expressed using Mathlib's bilinear-form predicates.
The characteristic theorems relate every predicate both to the signature and to the usual
elementwise inequalities. In particular, an indefinite lattice has vectors of both signs, and a
degenerate lattice has a nonzero vector in its radical. The final section proves that an
integral-lattice isometry transports the radical and preserves all three inertia indices and every
definiteness predicate.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.

## Main definitions

* `TauCeti.IntegralLattice.radical`: the kernel of the rational bilinear form.
* `TauCeti.IntegralLattice.signature`: the positive, null, and negative indices.
* `TauCeti.IntegralLattice.IsPosSemidef` and related definiteness predicates.
* `TauCeti.IntegralLattice.isPosDef_ofGramMatrix_iff`: a lattice presented by a Gram matrix is
  positive definite exactly when the matrix is, read over `ℚ`.
* `TauCeti.IntegralLattice.determinant_eq_neg_one_pow_sigNeg_mul_discriminant`: the sign of the
  determinant is `(-1) ^ n₋`.
* `TauCeti.IntegralLattice.finrank_eq_of_signature_eq`: equal signatures force equal ranks, and
  `TauCeti.IntegralLattice.IsPosDef.signature_eq`: a positive definite lattice of rank `n` has
  signature `(n, 0, 0)`.
* `TauCeti.IntegralLattice.IsIndefinite.exists_carrier_pos_and_neg`: an indefinite lattice has
  lattice vectors of positive and of negative norm.
* `TauCeti.IntegralLattice.Isometry.map_radical` and the `Isometry.sigPos_eq`, `sigNull_eq`, and
  `sigNeg_eq` theorems: isometry invariance of the signature.
-/

public section

namespace TauCeti

open QuadraticMap

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

/-- The radical of an integral lattice is the kernel of its rational bilinear form. -/
def radical : Submodule ℚ V := L.form.ker

/-- A vector lies in the radical of an integral lattice if and only if it annihilates all
vectors under the rational bilinear form. -/
@[simp]
theorem mem_radical_iff (x : V) : x ∈ L.radical ↔ ∀ y : V, L.form x y = 0 := by
  simp only [radical, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]

/-- The radical of the quadratic form associated to a lattice is its bilinear radical. -/
@[simp]
theorem radical_toQuadraticMap : L.form.toQuadraticMap.radical = L.radical :=
  LinearMap.BilinForm.radical_toQuadraticMap L.form L.isSymm

/-- The positive index of inertia of an integral lattice. -/
noncomputable abbrev sigPos : ℕ := _root_.sigPos L.form.toQuadraticMap

/-- The dimension of the radical of an integral lattice. -/
noncomputable abbrev sigNull : ℕ := Module.finrank ℚ L.radical

/-- The negative index of inertia of an integral lattice. -/
noncomputable abbrev sigNeg : ℕ := _root_.sigNeg L.form.toQuadraticMap

/-- The signature `(n₊, n₀, n₋)` of an integral lattice. -/
noncomputable abbrev signature : ℕ × ℕ × ℕ := (L.sigPos, L.sigNull, L.sigNeg)

/-- The positive, null, and negative indices exhaust the rank of the lattice. -/
theorem signature_sum_eq_finrank :
    L.sigPos + L.sigNull + L.sigNeg = Module.finrank ℚ V := by
  have := L.finiteDimensional
  have h := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.form.toQuadraticMap)
  rw [L.radical_toQuadraticMap] at h
  simpa only [sigPos, sigNull, sigNeg, add_comm, add_left_comm, add_assoc] using h

/-- Integral lattices with equal signatures have equal ranks. -/
theorem finrank_eq_of_signature_eq {M : IntegralLattice W} (h : L.signature = M.signature) :
    Module.finrank ℤ L = Module.finrank ℤ M := by
  rw [L.finrank_carrier, M.finrank_carrier, ← L.signature_sum_eq_finrank,
    ← M.signature_sum_eq_finrank]
  exact congrArg (fun s : ℕ × ℕ × ℕ ↦ s.1 + s.2.1 + s.2.2) h

/-- **The sign of the determinant is `(-1) ^ n₋`.** The signed determinant of an integral lattice
is its discriminant times `(-1)` to the negative index of inertia: in an orthogonal rational basis
the Gram matrix is diagonal with exactly `n₋` negative entries, and a change of basis multiplies
the determinant by a positive square. A degenerate lattice has determinant and discriminant `0`. -/
theorem determinant_eq_neg_one_pow_sigNeg_mul_discriminant :
    L.determinant = (-1) ^ L.sigNeg * L.discriminant := by
  classical
  have := L.finiteDimensional
  by_cases hnd : L.form.Nondegenerate
  swap
  · have h0 : L.determinant = 0 := not_ne_iff.mp (mt L.determinant_ne_zero_iff.mp hnd)
    simp [discriminant_def, h0]
  -- Compare a lattice basis with an orthogonal basis `v` of the rational form.
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp L.isSymm)
  let e := (Module.Free.chooseBasis ℤ L).reindex (L.rationalBasis.indexEquiv v)
  let b := e.extendOfIsLattice ℚ
  set d : Fin (Module.finrank ℚ V) → ℚ := fun i ↦ L.form (v i) (v i)
  have hd : ∀ i, d i ≠ 0 := hv.not_isOrtho_basis_self_of_separatingLeft hnd.1
  have hdiag : LinearMap.BilinForm.toMatrix v L.form = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hv h
  -- Sylvester's law of inertia counts the negative diagonal entries.
  have hneg : L.sigNeg = (Finset.univ.filter fun i ↦ d i < 0).card := by
    have hQ : (QuadraticMap.associated (R := ℚ) L.form.toQuadraticMap).IsOrthoᵢ v := by
      rwa [QuadraticMap.associated_left_inverse ℚ fun x y ↦ L.isSymm.eq x y]
    rw [sigNeg, QuadraticForm.sigNeg_of_equiv_weightedSumSquares
      ⟨QuadraticForm.isometryEquivWeightedSumSquares _ v hQ⟩,
      Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    rfl
  have hdet : (L.determinant : ℚ) * (b.toMatrix v).det ^ 2 = ∏ i, d i := by
    rw [← Matrix.det_diagonal, ← hdiag, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, L.determinant_eq_gramDet e,
      intCast_gramDet]
    ring
  -- The sign of `∏ i, d i` is `(-1) ^ L.sigNeg`, and `(b.toMatrix v).det ^ 2` is positive.
  have habs : ∏ i, |d i| = (-1) ^ L.sigNeg * ∏ i, d i := by
    have hsign : (-1 : ℚ) ^ (Finset.univ.filter fun i ↦ d i < 0).card =
        ∏ i, if d i < 0 then -1 else 1 := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [hneg, hsign, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.mp h)]; ring
  have hpos : (0 : ℚ) < (-1) ^ L.sigNeg * L.determinant := by
    have h := Finset.prod_pos fun i (_ : i ∈ Finset.univ) ↦ abs_pos.mpr (hd i)
    rw [habs, ← hdet, ← mul_assoc] at h
    exact pos_of_mul_pos_left h (sq_nonneg _)
  have hpos' : 0 < (-1) ^ L.sigNeg * L.determinant := by exact_mod_cast hpos
  have h1 : |L.determinant| = (-1) ^ L.sigNeg * L.determinant := by
    rw [← abs_of_pos hpos', abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [discriminant_def, Int.natCast_natAbs, h1, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul]

/-- An integral lattice is positive-definite when its quadratic form is positive on every nonzero
vector. -/
abbrev IsPosDef : Prop := L.form.toQuadraticMap.PosDef

/-- An integral lattice is positive-semidefinite when its symmetric bilinear form is nonnegative. -/
abbrev IsPosSemidef : Prop := L.form.IsPosSemidef

/-- An integral lattice is negative-definite when the negative of its quadratic form is
positive-definite. -/
abbrev IsNegDef : Prop := (-L.form.toQuadraticMap).PosDef

/-- An integral lattice is negative-semidefinite when the negative of its symmetric bilinear form
is positive-semidefinite. -/
abbrev IsNegSemidef : Prop := (-L.form).IsPosSemidef

/-- An integral lattice is degenerate when its radical is nontrivial. -/
def IsDegenerate : Prop := L.radical ≠ ⊥

/-- An integral lattice is indefinite when both its positive and negative indices are nonzero. -/
def IsIndefinite : Prop := 0 < L.sigPos ∧ 0 < L.sigNeg

/-- The radical of an integral lattice is trivial if and only if its null index vanishes. -/
theorem radical_eq_bot_iff_sigNull_eq_zero : L.radical = ⊥ ↔ L.sigNull = 0 := by
  have := L.finiteDimensional
  exact Submodule.finrank_eq_zero.symm

/-- Positive-definiteness has its usual elementwise characterization. -/
@[grind =]
theorem isPosDef_iff :
    L.IsPosDef ↔ ∀ x : V, x ≠ 0 → 0 < L.form x x := by
  simp only [IsPosDef, QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply]

open Classical in
/-- **A lattice presented by a Gram matrix is positive definite exactly when the matrix is**,
read over `ℚ`. The form of `ofGramMatrix b G hG` is the bilinear form of `G` in the coordinates
of `b`, so this is Mathlib's comparison of a quadratic map with the matrix of its bilinear form
in a basis. -/
theorem isPosDef_ofGramMatrix_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ V)
    (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).IsPosDef ↔ (G.map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [IsPosDef,
    LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b _ (ofGramMatrix b G hG).isSymm,
    ofGramMatrix_form, LinearMap.BilinForm.toMatrix_toBilin]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]

/-- Positive-semidefiniteness has its usual elementwise characterization. -/
@[grind =]
theorem isPosSemidef_iff :
    L.IsPosSemidef ↔ ∀ x : V, 0 ≤ L.form x x :=
  LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg L.form L.isSymm

/-- Negative-definiteness has its usual elementwise characterization. -/
@[grind =]
theorem isNegDef_iff :
    L.IsNegDef ↔ ∀ x : V, x ≠ 0 → L.form x x < 0 := by
  simp only [IsNegDef, QuadraticMap.PosDef, neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, neg_pos]

/-- Negative-semidefiniteness has its usual elementwise characterization. -/
@[grind =]
theorem isNegSemidef_iff :
    L.IsNegSemidef ↔ ∀ x : V, L.form x x ≤ 0 := by
  rw [IsNegSemidef, LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg (-L.form) L.isSymm.neg]
  simp only [LinearMap.neg_apply, neg_nonneg]

/-- Positive-semidefiniteness is equivalent to the vanishing of the negative index. -/
@[grind =]
theorem isPosSemidef_iff_sigNeg_eq_zero :
    L.IsPosSemidef ↔ L.sigNeg = 0 := by
  have := L.finiteDimensional
  exact LinearMap.BilinForm.isPosSemidef_iff_sigNeg_eq_zero L.form L.isSymm

/-- Negative-semidefiniteness is equivalent to the vanishing of the positive index. -/
@[grind =]
theorem isNegSemidef_iff_sigPos_eq_zero :
    L.IsNegSemidef ↔ L.sigPos = 0 := by
  have := L.finiteDimensional
  rw [IsNegSemidef,
    LinearMap.BilinForm.isPosSemidef_iff_sigNeg_eq_zero (-L.form) L.isSymm.neg]
  simp only [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg, sigPos]

/-- Positive-definiteness is positive-semidefiniteness together with nondegeneracy. -/
@[grind =]
theorem isPosDef_iff_isPosSemidef_and_nondegenerate :
    L.IsPosDef ↔ L.IsPosSemidef ∧ L.form.Nondegenerate := by
  have := L.finiteDimensional
  exact LinearMap.BilinForm.posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate
    L.form L.isSymm

/-- A positive-definite lattice is positive-semidefinite. -/
theorem IsPosDef.isPosSemidef (hL : L.IsPosDef) : L.IsPosSemidef :=
  (L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).1

/-- Positive-definiteness is equivalent to zero null and negative indices. -/
@[grind =]
theorem isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero :
    L.IsPosDef ↔ L.sigNull = 0 ∧ L.sigNeg = 0 := by
  have := L.finiteDimensional
  exact LinearMap.BilinForm.posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    L.form L.isSymm

/-- A positive definite lattice has signature `(n, 0, 0)`, where `n` is its rank. -/
theorem IsPosDef.signature_eq (hLp : L.IsPosDef) : L.signature = (Module.finrank ℤ L, 0, 0) := by
  obtain ⟨h0, hneg⟩ := L.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero.mp hLp
  have hsum := L.signature_sum_eq_finrank
  rw [h0, hneg, add_zero, add_zero, ← L.finrank_carrier] at hsum
  simp only [signature, hsum, h0, hneg]

/-- Negative-definiteness is negative-semidefiniteness together with nondegeneracy. -/
@[grind =]
theorem isNegDef_iff_isNegSemidef_and_nondegenerate :
    L.IsNegDef ↔ L.IsNegSemidef ∧ L.form.Nondegenerate := by
  have := L.finiteDimensional
  rw [IsNegDef, IsNegSemidef, ← LinearMap.BilinMap.toQuadraticMap_neg]
  have h := LinearMap.BilinForm.posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate
    (-L.form) L.isSymm.neg
  rw [h, LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_neg]

/-- Negative-definiteness is equivalent to zero positive and null indices. -/
@[grind =]
theorem isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero :
    L.IsNegDef ↔ L.sigPos = 0 ∧ L.sigNull = 0 := by
  have := L.finiteDimensional
  have h := LinearMap.BilinForm.posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    (-L.form) L.isSymm.neg
  rw [LinearMap.ker_neg, LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg] at h
  rw [IsNegDef, h, and_comm, sigNull, radical]

/-- Degeneracy is equivalent to a positive null index. -/
@[grind =]
theorem isDegenerate_iff_sigNull_pos : L.IsDegenerate ↔ 0 < L.sigNull := by
  have := L.finiteDimensional
  simp only [IsDegenerate, ne_eq, L.radical_eq_bot_iff_sigNull_eq_zero]
  exact Nat.pos_iff_ne_zero.symm

/-- A lattice is degenerate exactly when its bilinear form is not nondegenerate. -/
@[grind =]
theorem isDegenerate_iff_not_nondegenerate : L.IsDegenerate ↔ ¬L.form.Nondegenerate := by
  have := L.finiteDimensional
  simp only [IsDegenerate, radical, LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]

/-- A lattice is degenerate exactly when its radical contains a nonzero vector. -/
@[grind =]
theorem isDegenerate_iff_exists_mem_radical_ne_zero :
    L.IsDegenerate ↔ ∃ x : V, x ∈ L.radical ∧ x ≠ 0 := by
  simp only [IsDegenerate]
  exact L.radical.ne_bot_iff

/-- Indefiniteness is equivalent to the failure of both semidefiniteness conditions. -/
@[grind =]
theorem isIndefinite_iff_not_semidef :
    L.IsIndefinite ↔ ¬L.IsPosSemidef ∧ ¬L.IsNegSemidef := by
  rw [IsIndefinite, L.isPosSemidef_iff_sigNeg_eq_zero,
    L.isNegSemidef_iff_sigPos_eq_zero]
  omega

/-- An indefinite lattice has, and is characterized by, vectors of both signs. -/
@[grind =]
theorem isIndefinite_iff_exists_pos_and_exists_neg :
    L.IsIndefinite ↔ (∃ x : V, 0 < L.form x x) ∧ (∃ x : V, L.form x x < 0) := by
  rw [L.isIndefinite_iff_not_semidef, L.isPosSemidef_iff,
    L.isNegSemidef_iff]
  simp only [not_forall, not_le]
  exact and_comm

variable {L} in
/-- An indefinite lattice has lattice vectors of positive and of negative norm. -/
theorem IsIndefinite.exists_carrier_pos_and_neg (hL : L.IsIndefinite) :
    ∃ x y : L, 0 < L.form x x ∧ L.form y y < 0 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := L.isIndefinite_iff_exists_pos_and_exists_neg.mp hL
  obtain ⟨s, hs, hsp⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier p
  obtain ⟨t, ht, htq⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ L.carrier q
  have hscale (r : ℤ) (z : V) : L.form (r • z) (r • z) = (r : ℚ) ^ 2 * L.form z z := by
    simp only [← Int.cast_smul_eq_zsmul ℚ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  refine ⟨⟨s • p, hsp⟩, ⟨t • q, htq⟩, ?_, ?_⟩
  · rw [hscale]
    exact mul_pos (by positivity) hp
  · rw [hscale]
    exact mul_neg_of_pos_of_neg (by positivity) hq

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- An integral-lattice isometry maps the source radical onto the target radical. -/
@[simp]
theorem map_radical (e : Isometry L M) :
    L.radical.map (e : V ≃ₗ[ℚ] W).toLinearMap = M.radical := by
  rw [← L.radical_toQuadraticMap, ← M.radical_toQuadraticMap,
    ← L.norm_def, ← M.norm_def]
  simpa only [e.normIsometryEquiv_toLinearEquiv] using e.normIsometryEquiv.map_radical

/-- Isometric integral lattices have the same positive index. -/
theorem sigPos_eq (e : Isometry L M) : L.sigPos = M.sigPos := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [sigPos, sigPos, ← L.norm_def, ← M.norm_def]
  exact QuadraticMap.Equivalent.sigPos_eq ⟨e.normIsometryEquiv⟩

/-- Isometric integral lattices have the same null index. -/
theorem sigNull_eq (e : Isometry L M) : L.sigNull = M.sigNull := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [sigNull, sigNull, ← e.map_radical]
  exact (LinearEquiv.finrank_map_eq (e : V ≃ₗ[ℚ] W) L.radical).symm

/-- Isometric integral lattices have the same negative index. -/
theorem sigNeg_eq (e : Isometry L M) : L.sigNeg = M.sigNeg := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [sigNeg, sigNeg, ← L.norm_def, ← M.norm_def]
  exact QuadraticMap.Equivalent.sigNeg_eq ⟨e.normIsometryEquiv⟩

/-- Isometric integral lattices have the same signature. -/
theorem signature_eq (e : Isometry L M) : L.signature = M.signature := by
  rw [signature, signature, e.sigPos_eq, e.sigNull_eq, e.sigNeg_eq]

/-- Nondegeneracy of the ambient form is invariant under integral-lattice isometry. -/
theorem form_nondegenerate_iff (e : Isometry L M) :
    L.form.Nondegenerate ↔ M.form.Nondegenerate := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  have hL : L.form.ker = L.radical :=
    (LinearMap.BilinForm.radical_toQuadraticMap L.form L.isSymm).symm.trans
      L.radical_toQuadraticMap
  have hM : M.form.ker = M.radical :=
    (LinearMap.BilinForm.radical_toQuadraticMap M.form M.isSymm).symm.trans
      M.radical_toQuadraticMap
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, hL, hM, ← e.map_radical]
  exact Submodule.map_eq_bot_iff.symm

/-- The nondegeneracy mixin is invariant under integral-lattice isometry. -/
theorem isNondegenerate_iff (e : Isometry L M) : L.IsNondegenerate ↔ M.IsNondegenerate := by
  constructor <;> rintro ⟨h⟩
  · exact ⟨e.form_nondegenerate_iff.mp h⟩
  · exact ⟨e.form_nondegenerate_iff.mpr h⟩

/-- Transport the nondegeneracy mixin along an integral-lattice isometry. -/
theorem isNondegenerate (e : Isometry L M) [L.IsNondegenerate] : M.IsNondegenerate :=
  e.isNondegenerate_iff.mp (by infer_instance)

/-- Positive-definiteness is invariant under integral-lattice isometry. -/
theorem isPosDef_iff (e : Isometry L M) : L.IsPosDef ↔ M.IsPosDef := by
  rw [M.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero,
    L.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero, ← e.sigNull_eq, ← e.sigNeg_eq]

/-- Positive-semidefiniteness is invariant under integral-lattice isometry. -/
theorem isPosSemidef_iff (e : Isometry L M) : L.IsPosSemidef ↔ M.IsPosSemidef := by
  rw [M.isPosSemidef_iff_sigNeg_eq_zero, L.isPosSemidef_iff_sigNeg_eq_zero, ← e.sigNeg_eq]

/-- Negative-definiteness is invariant under integral-lattice isometry. -/
theorem isNegDef_iff (e : Isometry L M) : L.IsNegDef ↔ M.IsNegDef := by
  rw [M.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero,
    L.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero, ← e.sigPos_eq, ← e.sigNull_eq]

/-- Negative-semidefiniteness is invariant under integral-lattice isometry. -/
theorem isNegSemidef_iff (e : Isometry L M) : L.IsNegSemidef ↔ M.IsNegSemidef := by
  rw [M.isNegSemidef_iff_sigPos_eq_zero, L.isNegSemidef_iff_sigPos_eq_zero, ← e.sigPos_eq]

/-- Degeneracy is invariant under integral-lattice isometry. -/
theorem isDegenerate_iff (e : Isometry L M) : L.IsDegenerate ↔ M.IsDegenerate := by
  rw [M.isDegenerate_iff_sigNull_pos, L.isDegenerate_iff_sigNull_pos, ← e.sigNull_eq]

/-- Indefiniteness is invariant under integral-lattice isometry. -/
theorem isIndefinite_iff (e : Isometry L M) : L.IsIndefinite ↔ M.IsIndefinite := by
  rw [IsIndefinite, IsIndefinite, ← e.sigPos_eq, ← e.sigNeg_eq]

end Isometry

end IntegralLattice

end TauCeti
