/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Exponential
public import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence
import TauCeti.Algebra.Star.Projection.Basic
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann

/-!
# Stabilized unitary conjugacy and homotopy for Murray–von Neumann equivalence

Building on `CStarMatrix.MurrayVonNeumannEquiv`
(`TauCeti.Analysis.CStarAlgebra.Projection.Equivalence`) and the `2 × 2` block calculus
(`TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block`), this file develops stabilized unitary
conjugacy and the explicit exponential rotation path between Murray–von Neumann equivalent
projections in matrix C⋆-algebras:

* For unital `A`, the symmetry `stabilizedSymmetry p q v = fromBlocks (1 - p) v.conjTranspose v
  (1 - q)` conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` and equals
  `expUnitary (π • ⟨r, _⟩)` for the star projection
  `r = (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q`.
* For general (possibly non-unital) C⋆-algebras `A`, conjugating by
  `t ↦ expUnitary ((π * t) • ⟨r, _⟩)` in the unitization gives a norm-continuous path of star
  projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `inl p` to `inr q` (and hence also to `inl q`
  when `m = n`).

## Main declarations

* `CStarMatrix.stabilizedSymmetry`, `CStarMatrix.rotationProjection`,
  `CStarMatrix.rotationPath`,
  `CStarMatrix.MurrayVonNeumannEquiv.joined_inl_inr`,
  `CStarMatrix.MurrayVonNeumannEquiv.joined_inl_inl`: stabilized unitary conjugacy and
  projection homotopy.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Definition 4.6.1 and
  Propositions 4.6.2–4.6.6.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Chapter 2, §§2.2–2.3.
-/

public section

noncomputable section

namespace CStarMatrix

section StabilizedUnitaryAndRotationPath

section UnitalAlgebraic

open scoped Matrix

/-- The `2 × 2` block matrix `fromBlocks (1 - p) v.conjTranspose v (1 - q)` over a unital ring
with `0`, `1`, subtraction, and `star`. Whenever `v.conjTranspose * v = p`,
`v * v.conjTranspose = q`, and `v * p = v` (which holds automatically for idempotent `p` over a
star-ordered ring with `IsProperStar A`), it is a self-adjoint unitary
(`stabilizedSymmetry_mem_unitary`) conjugating `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`
(`stabilizedSymmetry_conj_inl`). -/
def stabilizedSymmetry {m n A : Type*} [DecidableEq m] [DecidableEq n]
    [Zero A] [One A] [Sub A] [Star A] (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks (1 - p) v.conjTranspose v (1 - q)

/-- Reading `stabilizedSymmetry p q v` as an ordinary `Matrix`. -/
@[simp] theorem ofMatrix_symm_stabilizedSymmetry {m n A : Type*} [DecidableEq m] [DecidableEq n]
    [Zero A] [One A] [Sub A] [Star A] (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    ofMatrix.symm (stabilizedSymmetry p q v) =
      Matrix.fromBlocks (1 - ofMatrix.symm p) (ofMatrix.symm v)ᴴ (ofMatrix.symm v)
        (1 - ofMatrix.symm q) := by
  rw [stabilizedSymmetry]
  simp

/-- `stabilizedSymmetry p q v` is self-adjoint whenever `vᴴ * v = p` and `v * vᴴ = q`. -/
theorem isSelfAdjoint_stabilizedSymmetry {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NonAssocRing A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsSelfAdjoint (stabilizedSymmetry p q v) := by
  rw [IsSelfAdjoint]
  apply ofMatrix.symm.injective
  simpa [← Matrix.star_eq_conjTranspose] using
    (Matrix.isSelfAdjoint_fromBlocks_one_sub (p := ofMatrix.symm p)
      (q := ofMatrix.symm q) (v := ofMatrix.symm v) hvp hvq).star_eq

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Ring A] [StarRing A]

/-- `stabilizedSymmetry p q v` is an involution whenever `vᴴ * v = p`, `v * vᴴ = q`, and
`v * p = v`. -/
theorem stabilizedSymmetry_mul_self {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p)
    (hvq : v * v.conjTranspose = q) (hv : v * p = v) :
    stabilizedSymmetry p q v * stabilizedSymmetry p q v = 1 := by
  apply ofMatrix.symm.injective
  simpa using Matrix.fromBlocks_one_sub_mul_self (p := ofMatrix.symm p)
    (q := ofMatrix.symm q) (v := ofMatrix.symm v) hvp hvq hv

/-- `stabilizedSymmetry p q v` is unitary whenever `vᴴ * v = p`, `v * vᴴ = q`, and
`v * p = v`. -/
theorem stabilizedSymmetry_mem_unitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p)
    (hvq : v * v.conjTranspose = q) (hv : v * p = v) :
    stabilizedSymmetry p q v ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  rw [Unitary.mem_iff, (isSelfAdjoint_stabilizedSymmetry hvp hvq).star_eq,
    stabilizedSymmetry_mul_self hvp hvq hv]
  exact ⟨rfl, rfl⟩

/-- `stabilizedSymmetry p q v` conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. -/
theorem stabilizedSymmetry_conj_inl {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p)
    (hvq : v * v.conjTranspose = q) (hv : v * p = v) :
    stabilizedSymmetry p q v * fromBlocks p 0 0 0 * star (stabilizedSymmetry p q v) =
      fromBlocks 0 0 0 q := by
  apply ofMatrix.symm.injective
  simpa [← Matrix.star_eq_conjTranspose] using
    Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_star (p := ofMatrix.symm p)
      (q := ofMatrix.symm q) (v := ofMatrix.symm v) hvp hvq hv

end UnitalAlgebraic

section RotationPath

/-- The `2 × 2` block matrix `(1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q` inside
`CStarMatrix (m ⊕ n) (m ⊕ n) A`, defined for arbitrary `p`, `q`, `v` without assuming `A` is
unital. Whenever `v.conjTranspose * v = p`, `v * v.conjTranspose = q`, and `v * p = v` (which
holds automatically for idempotent `p` over a star-ordered ring with proper star), this matrix is a
star projection (`isStarProjection_rotationProjection`). Over a (possibly non-unital) star-ordered
C⋆-algebra `A` when `p` is idempotent, `v.conjTranspose * v = p`, and `v * v.conjTranspose = q`,
conjugating `fromBlocks p 0 0 0` by the exponential unitary path
`t ↦ expUnitary ((π * t) • ⟨rotationProjection p q v, _⟩)` in
`Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)` sends `t = 0` to `fromBlocks p 0 0 0` and `t = 1`
to `fromBlocks 0 0 0 q` (see `rotationPath`). -/
def rotationProjection {m n A : Type*} [Neg A] [Star A] [SMul ℂ A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q

/-- Doubling `rotationProjection p q v` recovers `fromBlocks p (-v.conjTranspose) (-v) q`. -/
theorem two_smul_rotationProjection {m n A : Type*} [Neg A] [Star A] [MulAction ℂ A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    (2 : ℂ) • rotationProjection p q v = fromBlocks p (-v.conjTranspose) (-v) q := by
  rw [rotationProjection, smul_smul]; norm_num

/-- Over any unital ring `A` with a `ℂ`-module structure, `1 - 2 * rotationProjection p q v` equals
`stabilizedSymmetry p q v = fromBlocks (1 - p) v.conjTranspose v (1 - q)`. -/
theorem one_sub_two_mul_rotationProjection {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NonAssocRing A] [Star A] [Module ℂ A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    1 - 2 * rotationProjection p q v = stabilizedSymmetry p q v := by
  rw [two_mul, ← two_smul ℂ, two_smul_rotationProjection, ← fromBlocks_one, fromBlocks_sub,
    stabilizedSymmetry]
  simp

/-- When `v.conjTranspose * v = p`, `v * v.conjTranspose = q`, and `v * p = v`,
`rotationProjection p q v` is a star projection in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_rotationProjection {m n A : Type*} [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hv : v * p = v) :
    IsStarProjection (rotationProjection p q v) := by
  have hp_sa : IsSelfAdjoint p := by
    rw [← hvp]
    exact (Matrix.isHermitian_conjTranspose_mul_self (ofMatrix.symm v)).isSelfAdjoint
  have hq_sa : IsSelfAdjoint q := by
    rw [← hvq]
    exact (Matrix.isHermitian_mul_conjTranspose_self (ofMatrix.symm v)).isSelfAdjoint
  have hp_idem : p * p = p := calc
    p * p = v.conjTranspose * v * p := by rw [hvp]
    _ = v.conjTranspose * (v * p) := mul_assoc_rectangular _ _ _
    _ = p := by rw [hv, hvp]
  have hq_idem : q * q = q := (isIdempotentElem_of_mul_conjTranspose_eq hvp hvq hv).eq
  rw [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, rotationProjection]
  set B := fromBlocks p (-v.conjTranspose) (-v) q
  have hB_sa : IsSelfAdjoint B :=
    isSelfAdjoint_fromBlocks_iff.mpr ⟨hp_sa, by simp, hq_sa⟩
  have hB_sq : B * B = (2 : ℂ) • B := by
    simp only [B, fromBlocks_multiply, fromBlocks_add, hp_idem, hq_idem,
      CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hvp, hvq,
      mul_conjTranspose_eq_self_of_mul_eq hvp hv,
      conjTranspose_mul_eq_self_of_mul_eq hvp hvq hv,
      hv, mul_self_eq_self_of_mul_eq hvp hvq hv, two_smul]
  exact ⟨by rw [smul_mul_smul_comm, hB_sq, smul_smul]; norm_num,
    by rw [star_smul, hB_sa.star_eq]; norm_num⟩

/-- Proper-star version of `isStarProjection_rotationProjection`, deriving `v * p = v` from
`IsIdempotentElem p`. -/
theorem isStarProjection_rotationProjection_of_isIdempotentElem {m n A : Type*} [Fintype m]
    [Fintype n] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsStarProjection (rotationProjection p q v) :=
  isStarProjection_rotationProjection hvp hvq (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

section NonUnitalCStar

variable {m n A : Type*} [Fintype m] [Fintype n]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In the unitization of `CStarMatrix (m ⊕ n) (m ⊕ n) A`, conjugating `fromBlocks p 0 0 0` by
`1 - 2 * rotationProjection p q v` yields `fromBlocks 0 0 0 q` without requiring `A` to be
unital. -/
private theorem unitization_one_sub_two_mul_rotationProjection_conj
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hv : v * p = v) :
    ((1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) *
        (fromBlocks p 0 0 0 : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        (1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)))) =
      ((fromBlocks 0 0 0 q : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  set b : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks p (-v.conjTranspose) (-v) q
  set x : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks p 0 0 0
  have h2r : 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (b : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
    rw [two_mul, ← two_smul ℂ, ← Unitization.inr_smul, two_smul_rotationProjection]
  have hexpand :
      (1 - (b : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) *
          (x : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
          (1 - (b : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) =
        ((x - b * x - (x * b - b * x * b) : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
    simp only [sub_mul, one_mul, mul_sub, mul_one, ← Unitization.inr_mul, ← Unitization.inr_sub]
  rw [h2r, hexpand]
  congr 1
  apply ofMatrix.symm.injective
  simpa only [b, x, ofMatrix_symm_sub, ofMatrix_symm_mul, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_zero, ofMatrix_symm_neg] using
    Matrix.fromBlocks_sub_mul_sub_of_mul_eq (a := ofMatrix.symm v.conjTranspose)
      (b := ofMatrix.symm v) (e := ofMatrix.symm p) (f := ofMatrix.symm q)
      (ofMatrix_symm_mul_eq hvp) (ofMatrix_symm_mul_eq hvq) (ofMatrix_symm_mul_eq hv)

/-- Explicit norm-continuous path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from
`inl p` to `inr q` associated to a concrete rectangular matrix `v` implementing `p ∼ q`, over any
(possibly non-unital) C⋆-algebra `A`. -/
def rotationPath {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path
      (⟨inl (n := n) (R := ℂ) p, hp.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨inr (m := m) (R := ℂ) q, hq.map (inr (m := m) (R := ℂ))⟩ :=
  let hr := isStarProjection_rotationProjection_of_isIdempotentElem hp.isIdempotentElem hvp hvq
  let uPath := (hr.inr (R := ℂ)).expUnitaryPath
  let x : CStarMatrix (m ⊕ n) (m ⊕ n) A := inl (n := n) (R := ℂ) p
  have hx : IsStarProjection x := hp.map (inl (n := n) (R := ℂ))
  { toFun := fun t ↦
      ⟨((uPath t : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
          (x : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
          star (uPath t : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))).snd,
        Unitization.isStarProjection_snd_conj hx (SetLike.coe_mem (uPath t))⟩
    continuous_toFun := by
      have hu : Continuous fun t : unitInterval ↦
          (uPath t : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
        continuous_subtypeVal.comp uPath.continuous
      exact Continuous.subtype_mk (Unitization.continuous_snd.comp
        ((hu.mul continuous_const).mul (continuous_star.comp hu))) _
    source' := by
      refine Subtype.ext (Unitization.inr_injective (R := ℂ) ?_)
      rw [Unitization.inr_snd_conj _ x, uPath.source]
      simp [x]
    target' := by
      refine Subtype.ext (Unitization.inr_injective (R := ℂ) ?_)
      rw [Unitization.inr_snd_conj _ x]
      have hu1 : (uPath 1 : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
          1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
        congrArg Subtype.val uPath.target
      have hrU : IsStarProjection
          (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
        hr.inr
      rw [hu1, hrU.isSelfAdjoint_one_sub_two_mul.star_eq]
      simp only [x, inl_apply, inr_apply]
      exact unitization_one_sub_two_mul_rotationProjection_conj hvp hvq
        (mul_eq_self_of_conjTranspose_mul_eq v hp.isIdempotentElem hvp) }

/-- Evaluated inside `Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)`, `rotationPath` is conjugation
of `inl p` by `IsStarProjection.expUnitaryPath` applied to `rotationProjection p q v`. -/
theorem inr_coe_rotationPath_apply {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (t : unitInterval) :
    ((rotationPath hp hq hvp hvq t : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (((isStarProjection_rotationProjection_of_isIdempotentElem hp.isIdempotentElem hvp hvq).inr
          (R := ℂ)).expUnitaryPath t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (((isStarProjection_rotationProjection_of_isIdempotentElem
            hp.isIdempotentElem hvp hvq).inr
          (R := ℂ)).expUnitaryPath t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
  Unitization.inr_snd_conj _ _

namespace MurrayVonNeumannEquiv

/-- Murray–von Neumann equivalent projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A`
become path-connected inside the space of star projections of `CStarMatrix (m ⊕ n) (m ⊕ n) A` as
`inl p` and `inr q`. -/
theorem joined_inl_inr {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    Joined
      (⟨CStarMatrix.inl (n := n) (R := ℂ) p,
        h.isStarProjection_left.map (CStarMatrix.inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨CStarMatrix.inr (m := m) (R := ℂ) q,
        h.isStarProjection_right.map (CStarMatrix.inr (m := m) (R := ℂ))⟩ := by
  obtain ⟨v, hvp, hvq⟩ := h.exists_matrix
  exact ⟨rotationPath h.isStarProjection_left h.isStarProjection_right hvp hvq⟩

/-- Two Murray–von Neumann equivalent projections `p, q : CStarMatrix n n A` of the same matrix
size become path-connected after `2 × 2` stabilization `P ↦ fromBlocks P 0 0 0` inside the space
of star projections of `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem joined_inl_inl {p q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    Joined
      (⟨CStarMatrix.inl (n := n) (R := ℂ) p,
        h.isStarProjection_left.map (CStarMatrix.inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P})
      ⟨CStarMatrix.inl (n := n) (R := ℂ) q,
        h.isStarProjection_right.map (CStarMatrix.inl (n := n) (R := ℂ))⟩ :=
  h.joined_inl_inr.trans (MurrayVonNeumannEquiv.refl h.isStarProjection_right).joined_inl_inr.symm

end MurrayVonNeumannEquiv

end NonUnitalCStar

section UnitalCStar

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Over a unital C⋆-algebra `A`, `expUnitary (π • ⟨rotationProjection p q v, _⟩)` evaluates to
`stabilizedSymmetry p q v`. -/
theorem expUnitary_pi_smul_rotationProjection
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    selfAdjoint.expUnitary (Real.pi • ⟨rotationProjection p q v,
      (isStarProjection_rotationProjection_of_isIdempotentElem hp hvp hvq).isSelfAdjoint⟩) =
      ⟨stabilizedSymmetry p q v, stabilizedSymmetry_mem_unitary hvp hvq
        (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)⟩ :=
  ((isStarProjection_rotationProjection_of_isIdempotentElem hp hvp hvq).expUnitary_pi_smul).trans
    (Subtype.ext (one_sub_two_mul_rotationProjection p q v))

end UnitalCStar

end RotationPath

end StabilizedUnitaryAndRotationPath

end CStarMatrix
