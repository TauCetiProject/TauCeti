/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import Mathlib.Tactic.LinearCombination

/-!
# Stabilized projection homotopy and Murray–von Neumann equivalence over C⋆-algebras

Over a (possibly non-unital) C⋆-algebra `A`, two square matrices `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` have Murray–von Neumann equivalent underlying matrices
(`Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q)`) if and only if their
block-diagonal stabilizations `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` (or, for equal index
types `m = n`, `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0`) are joined by a continuous path of
star projections. When `A` is unital, this is further equivalent to unitary conjugacy in the
identity path component of `unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. No separability or
projection cancellation is assumed.

## Main definitions

* `CStarMatrix.stabilizedRotationPath`: the explicit `2 × 2` rotation path in
  `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` rotating by
  angle `πt / 2`.

## Main results

* `CStarMatrix.isMurrayVonNeumannEquivalent_of_norm_sub_lt_one`: star projections
  `p, q : CStarMatrix n n A` with `‖p - q‖ < 1` have Murray–von Neumann equivalent underlying
  matrices.
* `CStarMatrix.isStarProjection_stabilizedRotationPath`: every point along
  `stabilizedRotationPath p q v` is a star projection when `v` is a rectangular partial isometry
  with initial projection `p` and final projection `q`.
* `CStarMatrix.isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks`,
  `CStarMatrix.isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks_zero`: equivalence between
  Murray–von Neumann equivalence and stabilized projection homotopy over possibly non-unital
  C⋆-algebras.
* `CStarMatrix.isMurrayVonNeumannEquivalent_iff_exists_joined_one_unitary_mul_fromBlocks_mul_star`
  and `isMurrayVonNeumannEquivalent_iff_exists_joined_one_unitary_mul_fromBlocks_zero_mul_star`
  (in `CStarMatrix`): equivalence between Murray–von Neumann equivalence and stabilized unitary
  conjugacy in the identity path component over unital C⋆-algebras.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Chapter III, §4.6 (Propositions 4.6.2–4.6.6).
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), §§2.1–2.2.
-/

public section

open scoped Matrix Real unitInterval

namespace CStarMatrix

variable {A m n : Type*} [Fintype m] [Fintype n]

/-- Two matrix star projections over a (possibly non-unital) C⋆-algebra at operator-norm distance
`< 1` have Murray–von Neumann equivalent underlying matrices. -/
theorem isMurrayVonNeumannEquivalent_of_norm_sub_lt_one [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  obtain ⟨v, hv₁, hv₂⟩ := hp.exists_star_mul_self_eq_of_norm_sub_lt_one hq h
  refine ⟨isStarProjection_ofMatrix_symm_iff.mpr hp, isStarProjection_ofMatrix_symm_iff.mpr hq,
    ofMatrix.symm v, ?_, ?_⟩
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star] using congrArg ofMatrix.symm hv₁
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star] using congrArg ofMatrix.symm hv₂

private theorem isMurrayVonNeumannEquivalent_of_path [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} (γ : Path p q) (hγ : ∀ t, IsStarProjection (γ t)) :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  have hc : Continuous fun t ↦ ofMatrix.symm (γ t) :=
    ofMatrixL.symm.continuous.comp γ.continuous
  simpa only [γ.source, γ.target] using
    hc.isMurrayVonNeumannEquivalent (fun t ↦ isStarProjection_ofMatrix_symm_iff.mpr (hγ t)) 0 1

omit [Fintype m] [Fintype n] in
/-- **Explicit `2 × 2` rotation path for Murray–von Neumann equivalent projections.** Given matrices
`p : CStarMatrix m m A`, `q : CStarMatrix n n A`, and `v : CStarMatrix n m A` over a (possibly
non-unital) C⋆-algebra `A`, this is the continuous path from `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q` given by rotating by angle `πt / 2`; every point is a star projection when `v`
is a rectangular partial isometry with initial projection `p` and final projection `q`. -/
noncomputable def stabilizedRotationPath [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) where
  toFun t :=
    fromBlocks (Real.cos (π / 2 * t) ^ 2 • p)
      ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v.conjTranspose)
      ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v)
      (Real.sin (π / 2 * t) ^ 2 • q)
  continuous_toFun := by
    conv =>
      enter [1, t]
      rw [← ofMatrix.apply_symm_apply (fromBlocks _ _ _ _), ofMatrix_symm_fromBlocks,
        ofMatrix_eq_ofMatrixL]
      simp only [ofMatrix_symm_smul]
    exact ofMatrixL.continuous.comp
      (Continuous.matrix_fromBlocks (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  source' := by simp
  target' := by simp

omit [Fintype m] [Fintype n] in
@[simp] theorem stabilizedRotationPath_apply [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) (t : I) :
    stabilizedRotationPath p q v t =
      fromBlocks (Real.cos (π / 2 * t) ^ 2 • p)
        ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v.conjTranspose)
        ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v)
        (Real.sin (π / 2 * t) ^ 2 • q) := (rfl)

/-- Every point along `stabilizedRotationPath p q v` is a star projection when `v` is a rectangular
partial isometry with initial projection `p` and final projection `q`. -/
theorem isStarProjection_stabilizedRotationPath [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hv : v * v.conjTranspose * v = v) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (t : I) :
    IsStarProjection (stabilizedRotationPath p q v t) := by
  open scoped ComplexStarModule in
  have hvM : ofMatrix.symm v * (ofMatrix.symm v)ᴴ * ofMatrix.symm v = ofMatrix.symm v := by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hv
  have heq := Matrix.isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq hvM
  have hp : IsStarProjection p := isStarProjection_ofMatrix_symm_iff.mp
    (by simpa only [← hv₁, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
      heq.isStarProjection_left)
  have hq : IsStarProjection q := isStarProjection_ofMatrix_symm_iff.mp
    (by simpa only [← hv₂, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
      heq.isStarProjection_right)
  have hvp : v * p = v := by rw [← hv₁, ← mul_assoc_rectangular, hv]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    simpa [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using congrArg conjTranspose hvp
  have hqv : q * v = v := by rw [← hv₂, hv]
  have hvq : v.conjTranspose * q = v.conjTranspose := by
    simpa [← star_eq_conjTranspose, hq.isSelfAdjoint.star_eq] using congrArg conjTranspose hqv
  set c : ℝ := Real.cos (π / 2 * t)
  set s : ℝ := Real.sin (π / 2 * t)
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq (π / 2 * t)
  rw [stabilizedRotationPath_apply]
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, fromBlocks_multiply]
    simp only [CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul, hp.isIdempotentElem.eq,
      hq.isIdempotentElem.eq, hv₁, hv₂, hvp, hpv, hqv, hvq, ← add_smul, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · congr 1; linear_combination c ^ 2 * hcs
    · congr 1; linear_combination c * s * hcs
    · congr 1; linear_combination c * s * hcs
    · congr 1; linear_combination s ^ 2 * hcs
  · rw [IsSelfAdjoint, fromBlocks_star]; simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

/-- Over a (possibly non-unital) C⋆-algebra, two matrix elements `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` have Murray–von Neumann equivalent underlying matrices if and only if
`fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are joined by a continuous path of star
projections. -/
theorem isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks
    [NonUnitalCStarAlgebra A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks (0 : CStarMatrix m m A) 0 0 q), ∀ t, IsStarProjection (γ t) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨v, hvp, hvq, hv⟩ := h.exists_mul_conjTranspose_mul_self_eq
    refine ⟨stabilizedRotationPath p q (ofMatrix v),
      isStarProjection_stabilizedRotationPath ?_ ?_ ?_⟩ <;>
      apply ofMatrix.symm.injective <;>
      simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply]
    exacts [hv, hvp, hvq]
  · have hp : IsStarProjection (ofMatrix.symm p) := isStarProjection_ofMatrix_symm_iff.mpr
      (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.mp (γ.source ▸ hγ 0)).1
    have hq : IsStarProjection (ofMatrix.symm q) := isStarProjection_ofMatrix_symm_iff.mpr
      (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.mp (γ.target ▸ hγ 1)).2
    have hpath := isMurrayVonNeumannEquivalent_of_path γ hγ
    simp only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] at hpath
    exact hp.isMurrayVonNeumannEquivalent_fromBlocks_zero.trans
      (hpath.trans hq.isMurrayVonNeumannEquivalent_zero_fromBlocks.symm)

/-- Over a unital C⋆-algebra, a star projection `p : CStarMatrix m m A` and `q : CStarMatrix n n A`
have Murray–von Neumann equivalent underlying matrices if and only if `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem isMurrayVonNeumannEquivalent_iff_exists_joined_one_unitary_mul_fromBlocks_mul_star
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsStarProjection p) :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) ↔
      ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 u ∧
        (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 0 0 0 q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.mpr ⟨hp, .zero _⟩
  rw [isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks,
    hp0.exists_path_iff_exists_joined_one_mul_mul_star_eq]

/-- Over a (possibly non-unital) C⋆-algebra, two matrix elements `p, q : CStarMatrix n n A` have
Murray–von Neumann equivalent underlying matrices if and only if `fromBlocks p 0 0 0` and
`fromBlocks q 0 0 0` are joined by a continuous path of star projections. -/
theorem isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks_zero [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks q 0 0 (0 : CStarMatrix n n A)), ∀ t, IsStarProjection (γ t) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨γ₁, hγ₁⟩ := isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks.mp h
    obtain ⟨γ₂, hγ₂⟩ :=
      isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks.mp (.refl h.isStarProjection_right)
    refine ⟨γ₁.trans γ₂.symm, fun t ↦ ?_⟩
    rw [Path.trans_apply]; split_ifs <;> simp [hγ₁, hγ₂]
  · have hq : IsStarProjection (ofMatrix.symm q) := isStarProjection_ofMatrix_symm_iff.mpr
      (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.mp (γ.target ▸ hγ 1)).1
    obtain ⟨γ₂, hγ₂⟩ := isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks.mp (.refl hq)
    refine isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks.mpr ⟨γ.trans γ₂, fun t ↦ ?_⟩
    rw [Path.trans_apply]; split_ifs <;> simp [hγ, hγ₂]

/-- Over a unital C⋆-algebra, a star projection `p : CStarMatrix n n A` and `q : CStarMatrix n n A`
have Murray–von Neumann equivalent underlying matrices if and only if `fromBlocks p 0 0 0` and
`fromBlocks q 0 0 0` are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
theorem isMurrayVonNeumannEquivalent_iff_exists_joined_one_unitary_mul_fromBlocks_zero_mul_star
    [DecidableEq n] [CStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) ↔
      ∃ u : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A), Joined 1 u ∧
        (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) = fromBlocks q 0 0 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.mpr ⟨hp, .zero _⟩
  rw [isMurrayVonNeumannEquivalent_iff_exists_path_fromBlocks_zero,
    hp0.exists_path_iff_exists_joined_one_mul_mul_star_eq]

end CStarMatrix
