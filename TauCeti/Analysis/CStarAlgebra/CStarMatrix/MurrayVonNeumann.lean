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
public import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Algebra.Star.Projection.Basic
import TauCeti.Analysis.CStarAlgebra.Exponential
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann

/-!
# Permanence, stabilized unitary conjugacy, and homotopy for Murray–von Neumann equivalence

Building on `CStarMatrix.MurrayVonNeumannEquiv`
(`TauCeti.Analysis.CStarAlgebra.Projection.Equivalence`) and the `2 × 2` block calculus
(`TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block`), this file develops structural permanence
properties, stabilized unitary conjugacy, and the explicit exponential rotation path between
Murray–von Neumann equivalent projections in matrix C⋆-algebras:

* Permanence under diagonal corner embeddings (`single`), block corner padding (`inr`), finite
  reindexing (`reindexₐ`), unitary conjugacy in `Unitization`, and orthogonal sums (`p₁ * p₂ = 0`,
  `q₁ * q₂ = 0`), together with `murrayVonNeumannSetoid` on
  `{p : CStarMatrix n n A // IsStarProjection p}`.
* Stabilized unitary conjugacy and the explicit exponential rotation path: for unital `A`, the
  symmetry `stabilizedSymmetry p q v = fromBlocks (1 - p) v.conjTranspose v (1 - q)` conjugates
  `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` and equals `expUnitary (π • ⟨r, _⟩)` for the star
  projection `r = (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q`. For general (possibly
  non-unital) C⋆-algebras `A`, conjugating by `t ↦ expUnitary ((π * t) • ⟨r, _⟩)` in the unitization
  gives a norm-continuous path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `inl p`
  to `inr q` (and hence also to `inl q` when `m = n`).

## Main declarations

* `IsStarProjection.murrayVonNeumannEquiv_single`,
  `IsStarProjection.murrayVonNeumannEquiv_inr`,
  `IsStarProjection.murrayVonNeumannEquiv_reindexₐ`,
  `CStarMatrix.murrayVonNeumannEquiv_of_unitization_unitary_conj`,
  `CStarMatrix.MurrayVonNeumannEquiv.add_of_mul_eq_zero`: permanence properties of
  `CStarMatrix.MurrayVonNeumannEquiv`.
* `CStarMatrix.murrayVonNeumannSetoid`: setoid of Murray–von Neumann equivalence on star projections
  of fixed finite size `n`.
* `CStarMatrix.stabilizedSymmetry`, `CStarMatrix.rotationProjection`,
  `CStarMatrix.rotationUnitary`, `CStarMatrix.rotationPath`,
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

section Permanence

variable {m n R A : Type*}

/-- Placing a star projection `p : A` in any two diagonal corners `(i, i)` and `(j, j)` of
matrix C⋆-algebras `CStarMatrix m m A` and `CStarMatrix n n A` yields Murray–von Neumann
equivalent projections, witnessed by `single j i p` without requiring `A` to be unital. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_single [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NonUnitalSemiring A] [StarRing A] {p : A}
    (hp : IsStarProjection p) (i : m) (j : n) :
    MurrayVonNeumannEquiv (single i i p) (single j j p) := by
  simpa only [← ofMatrix_symm_single, Equiv.apply_symm_apply] using
    murrayVonNeumannEquiv_ofMatrix (hp.isMurrayVonNeumannEquivalent_single i j)

/-- Padding a star projection `q` with zero blocks in the upper-left corner yields an equivalent
projection, without requiring `A` to have a unit. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_inr [Fintype m] [Fintype n]
    [Semiring R] [NonUnitalSemiring A] [Module R A] [StarRing A]
    {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv (inr (m := m) (R := R) q) q := by
  have h := (murrayVonNeumannEquiv_ofMatrix
    ((isStarProjection_ofMatrix_symm hq).isMurrayVonNeumannEquivalent_zero_fromBlocks
      (n := m))).symm
  simpa only [inr_apply, of_fromBlocks, of_zero, Equiv.apply_symm_apply] using h

/-- Reindexing a star projection along an equivalence `e : m ≃ n` yields a Murray–von Neumann
equivalent projection, without requiring `A` to have a unit. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindexₐ [Fintype m] [Fintype n]
    [Semiring R] [NonUnitalSemiring A] [Module R A] [StarRing A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) (e : m ≃ n) :
    MurrayVonNeumannEquiv (reindexₐ R A e p) p := by
  have h := (murrayVonNeumannEquiv_ofMatrix
    ((isStarProjection_ofMatrix_symm hp).isMurrayVonNeumannEquivalent_reindex e)).symm
  have hre : ofMatrix (Matrix.reindex e e (ofMatrix.symm p)) = reindexₐ R A e p := by
    rw [← reindexₗ_eq_reindexₐ (R := R), ← ofMatrix_symm_reindexₗ (R := R), Equiv.apply_symm_apply]
  simpa only [hre, Equiv.apply_symm_apply] using h

private theorem inr_snd_eq_of_fst_eq_zero {R A : Type*} [AddZeroClass R] [AddZeroClass A]
    {z : Unitization R A} (hz : z.fst = 0) : (z.snd : Unitization R A) = z := by
  simpa [hz] using Unitization.inl_fst_add_inr_snd_eq z

/-- If two matrix projections `p, q : CStarMatrix n n A` over a possibly non-unital `⋆`-algebra `A`
become unitarily conjugate inside the unitization `Unitization R (CStarMatrix n n A)`, then `p` and
`q` are Murray–von Neumann equivalent inside `CStarMatrix n n A`. -/
theorem murrayVonNeumannEquiv_of_unitization_unitary_conj [Fintype n]
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : Unitization R (CStarMatrix n n A)}
    (hu : u ∈ unitary (Unitization R (CStarMatrix n n A)))
    (hconj : u * (p : Unitization R (CStarMatrix n n A)) * star u =
      (q : Unitization R (CStarMatrix n n A))) :
    MurrayVonNeumannEquiv p q := by
  let M := CStarMatrix n n A
  let v : M := (u * (p : Unitization R M)).snd
  have hv_coe : (v : Unitization R M) = u * (p : Unitization R M) :=
    inr_snd_eq_of_fst_eq_zero (by simp [Unitization.fst_mul, Unitization.fst_inr])
  have hp_coe : IsStarProjection (p : Unitization R M) := hp.inr
  have hq_coe : IsStarProjection (q : Unitization R M) := by
    have h := hp_coe.map (Unitary.conjStarAlgAut R (Unitization R M) ⟨u, hu⟩)
    rw [Unitary.conjStarAlgAut_apply, hconj] at h
    exact h
  have hq : IsStarProjection q := hq_coe.of_inr
  refine (murrayVonNeumannEquiv_iff hp hq).mpr ⟨v, Unitization.inr_injective (R := R) ?_,
    Unitization.inr_injective (R := R) ?_⟩
  · rw [Unitization.inr_mul, ← star_eq_conjTranspose, Unitization.inr_star, hv_coe, star_mul,
      hp_coe.isSelfAdjoint.star_eq, mul_assoc (p : Unitization R M) (star u) (u * p),
      ← mul_assoc (star u) u (p : Unitization R M), Unitary.star_mul_self_of_mem hu, one_mul,
      hp_coe.isIdempotentElem.eq]
  · rw [Unitization.inr_mul, ← star_eq_conjTranspose, Unitization.inr_star, hv_coe, star_mul,
      hp_coe.isSelfAdjoint.star_eq, mul_assoc u (p : Unitization R M),
      ← mul_assoc (p : Unitization R M) (p : Unitization R M) (star u),
      hp_coe.isIdempotentElem.eq, ← mul_assoc, hconj]

/-- Setoid of Murray–von Neumann equivalence on star projections of fixed size `n`. -/
def murrayVonNeumannSetoid (n A : Type*) [Fintype n]
    [NonUnitalSemiring A] [StarRing A] :
    Setoid {p : CStarMatrix n n A // IsStarProjection p} where
  r p q := MurrayVonNeumannEquiv p.val q.val
  iseqv := ⟨fun p ↦ MurrayVonNeumannEquiv.refl p.property, fun h ↦ h.symm,
    fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- The relation of `murrayVonNeumannSetoid n A` is Murray–von Neumann equivalence on the underlying
projections. -/
@[simp] theorem murrayVonNeumannSetoid_r [Fintype n] [NonUnitalSemiring A] [StarRing A]
    (p q : {p : CStarMatrix n n A // IsStarProjection p}) :
    (murrayVonNeumannSetoid n A).r p q ↔ MurrayVonNeumannEquiv p.val q.val := (Iff.rfl)

namespace MurrayVonNeumannEquiv

/-- Orthogonal sums preserve Murray–von Neumann equivalence: if `p₁ * p₂ = 0` and `q₁ * q₂ = 0`,
then adding supported implementing matrices `v₁ + v₂` implements `(p₁ + p₂) ∼ (q₁ + q₂)`. -/
theorem add_of_mul_eq_zero [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : MurrayVonNeumannEquiv p₁ q₁) (h₂ : MurrayVonNeumannEquiv p₂ q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    MurrayVonNeumannEquiv (p₁ + p₂) (q₁ + q₂) := by
  have hp₁ := h₁.isStarProjection_left
  have hq₁ := h₁.isStarProjection_right
  have hp₂ := h₂.isStarProjection_left
  have hq₂ := h₂.isStarProjection_right
  obtain ⟨v₁, hv₁p, hv₁q, hv₁_mul⟩ := h₁.exists_matrix_mul_eq_self
  obtain ⟨v₂, hv₂p, hv₂q, hv₂_mul⟩ := h₂.exists_matrix_mul_eq_self
  have hq₁v₁ : q₁ * v₁ = v₁ := by rw [← hv₁q, mul_assoc_rectangular, hv₁p, hv₁_mul]
  have hq₂v₂ : q₂ * v₂ = v₂ := by rw [← hv₂q, mul_assoc_rectangular, hv₂p, hv₂_mul]
  have hp₂_sa : p₂.conjTranspose = p₂ := by rw [← star_eq_conjTranspose, hp₂.isSelfAdjoint.star_eq]
  have hq₁_sa : q₁.conjTranspose = q₁ := by rw [← star_eq_conjTranspose, hq₁.isSelfAdjoint.star_eq]
  have hp₂v₂ : p₂ * v₂.conjTranspose = v₂.conjTranspose := by
    simpa [hp₂_sa] using congrArg conjTranspose hv₂_mul
  have hv₁q₁ : v₁.conjTranspose * q₁ = v₁.conjTranspose := by
    simpa [hq₁_sa] using congrArg conjTranspose hq₁v₁
  have hv₁₂ : v₁.conjTranspose * v₂ = 0 := by
    calc v₁.conjTranspose * v₂
        = (v₁.conjTranspose * q₁) * (q₂ * v₂) := by rw [hv₁q₁, hq₂v₂]
      _ = v₁.conjTranspose * (q₁ * q₂) * v₂ := by simp only [mul_assoc_rectangular]
      _ = 0 := by rw [hq, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have hv₂₁ : v₂.conjTranspose * v₁ = 0 := by simpa using congrArg conjTranspose hv₁₂
  have hw₁₂ : v₁ * v₂.conjTranspose = 0 := by
    calc v₁ * v₂.conjTranspose
        = (v₁ * p₁) * (p₂ * v₂.conjTranspose) := by rw [hv₁_mul, hp₂v₂]
      _ = v₁ * (p₁ * p₂) * v₂.conjTranspose := by simp only [mul_assoc_rectangular]
      _ = 0 := by rw [hp, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have hw₂₁ : v₂ * v₁.conjTranspose = 0 := by simpa using congrArg conjTranspose hw₁₂
  refine (murrayVonNeumannEquiv_iff (hp₁.add hp₂ hp) (hq₁.add hq₂ hq)).mpr
    ⟨v₁ + v₂,
      by rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
        hv₁p, hv₂p, hv₁₂, hv₂₁, add_zero, zero_add],
      by rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
        hv₁q, hv₂q, hw₁₂, hw₂₁, add_zero, zero_add]⟩

end MurrayVonNeumannEquiv

end Permanence

section ProperStar

variable {m n A : Type*} [Fintype m] [Fintype n]
  [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

private theorem mul_conjTranspose_eq_self_of_conjTranspose_mul_self {p : CStarMatrix m m A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) :
    p * v.conjTranspose = v.conjTranspose := by
  have hp_sa : p.conjTranspose = p := by
    rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  simpa [hp_sa] using congrArg conjTranspose (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

private theorem mul_self_eq_self_of_self_mul_conjTranspose {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) : q * v = v := by
  rw [← hvq, mul_assoc_rectangular, hvp]
  exact mul_eq_self_of_conjTranspose_mul_eq v hp hvp

private theorem conjTranspose_mul_eq_self_of_self_mul_conjTranspose {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    v.conjTranspose * q = v.conjTranspose := by
  have hq_sa : q.conjTranspose = q := by
    rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  simpa [hq_sa] using congrArg conjTranspose
    (mul_self_eq_self_of_self_mul_conjTranspose hp hvp hvq)

end ProperStar

section StabilizedUnitaryAndRotationPath

section UnitalAlgebraic

/-- The `2 × 2` block matrix `fromBlocks (1 - p) v.conjTranspose v (1 - q)` over a unital ring
with `0`, `1`, subtraction, and `star`. Over a star-ordered ring with proper star
(`IsProperStar A`), whenever `p` is idempotent, `v.conjTranspose * v = p`, and
`v * v.conjTranspose = q`, it is a self-adjoint unitary (`stabilizedSymmetry_mem_unitary`)
conjugating `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` (`stabilizedSymmetry_conj_inl`). -/
def stabilizedSymmetry {m n A : Type*} [DecidableEq m] [DecidableEq n]
    [Zero A] [One A] [Sub A] [Star A] (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks (1 - p) v.conjTranspose v (1 - q)

/-- Defining block formula for `stabilizedSymmetry p q v`. -/
theorem stabilizedSymmetry_def {m n A : Type*} [DecidableEq m] [DecidableEq n]
    [Zero A] [One A] [Sub A] [Star A] (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedSymmetry p q v = fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)

/-- `stabilizedSymmetry p q v` is self-adjoint whenever `vᴴ * v = p` and `v * vᴴ = q`. -/
theorem isSelfAdjoint_stabilizedSymmetry {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NonAssocRing A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsSelfAdjoint (stabilizedSymmetry p q v) := by
  have hp : IsSelfAdjoint p := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, ← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hq : IsSelfAdjoint q := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, ← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  have h1m : IsSelfAdjoint (1 : CStarMatrix m m A) := conjTranspose_one
  have h1n : IsSelfAdjoint (1 : CStarMatrix n n A) := conjTranspose_one
  rw [stabilizedSymmetry, isSelfAdjoint_fromBlocks_iff]
  exact ⟨h1m.sub hp, conjTranspose_conjTranspose v, h1n.sub hq⟩

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- `stabilizedSymmetry p q v` is an involution whenever `p` is idempotent, `vᴴ * v = p`, and
`v * vᴴ = q`. -/
theorem stabilizedSymmetry_mul_self {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSymmetry p q v * stabilizedSymmetry p q v = 1 := by
  apply ofMatrix.symm.injective
  rw [stabilizedSymmetry, ofMatrix_symm_mul, ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq (a := ofMatrix.symm v.conjTranspose)
    (b := ofMatrix.symm v) (e := ofMatrix.symm p) (f := ofMatrix.symm q) hvp hvq
    (mul_conjTranspose_eq_self_of_conjTranspose_mul_self hp hvp)
    (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

/-- `stabilizedSymmetry p q v` is unitary whenever `p` is idempotent, `vᴴ * v = p`, and
`v * vᴴ = q`. -/
theorem stabilizedSymmetry_mem_unitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSymmetry p q v ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  rw [Unitary.mem_iff, (isSelfAdjoint_stabilizedSymmetry hvp hvq).star_eq,
    stabilizedSymmetry_mul_self hp hvp hvq]
  exact ⟨rfl, rfl⟩

/-- `stabilizedSymmetry p q v` conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. -/
theorem stabilizedSymmetry_conj_inl {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSymmetry p q v * fromBlocks p 0 0 0 * star (stabilizedSymmetry p q v) =
      fromBlocks 0 0 0 q := by
  rw [(isSelfAdjoint_stabilizedSymmetry hvp hvq).star_eq]
  apply ofMatrix.symm.injective
  rw [stabilizedSymmetry, ofMatrix_symm_mul, ofMatrix_symm_mul, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (a := ofMatrix.symm v.conjTranspose) (b := ofMatrix.symm v)
    (e := ofMatrix.symm p) (f := ofMatrix.symm q) hvp hvq
    (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

end UnitalAlgebraic

section RotationPath

/-- The `2 × 2` block matrix `(1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q` inside
`CStarMatrix (m ⊕ n) (m ⊕ n) A`, defined for arbitrary `p`, `q`, `v` without assuming `A` is
unital. Over a complex star-ordered ring with proper star, whenever `p` is idempotent,
`v.conjTranspose * v = p`, and `v * v.conjTranspose = q`, this matrix is a star projection
(`isStarProjection_rotationProjection`). Over a (possibly non-unital) star-ordered C⋆-algebra `A`
under the same hypotheses, conjugating `fromBlocks p 0 0 0` by the exponential unitary path
`t ↦ expUnitary ((π * t) • ⟨rotationProjection p q v, _⟩)` in
`Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)` sends `t = 0` to `fromBlocks p 0 0 0` and `t = 1`
to `fromBlocks 0 0 0 q` (see `rotationUnitary` and `rotationPath`). -/
def rotationProjection {m n A : Type*} [Neg A] [Star A] [SMul ℂ A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q

/-- Defining block formula for `rotationProjection p q v`. -/
theorem rotationProjection_def {m n A : Type*} [Neg A] [Star A] [SMul ℂ A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    rotationProjection p q v = (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)

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

/-- When `v` implements `p ∼ q` for an idempotent `p`, `rotationProjection p q v` is a star
projection in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_rotationProjection {m n A : Type*} [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsStarProjection (rotationProjection p q v) := by
  have hp_sa : IsSelfAdjoint p := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, ← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hq_sa : IsSelfAdjoint q := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, ← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  have hv_mul_p : v * p = v := mul_eq_self_of_conjTranspose_mul_eq v hp hvp
  have hq_idem : q * q = q := by
    rw [← hvq, mul_assoc_rectangular, ← mul_assoc_rectangular v.conjTranspose v v.conjTranspose,
      hvp, ← mul_assoc_rectangular, hv_mul_p]
  rw [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, rotationProjection]
  set B := fromBlocks p (-v.conjTranspose) (-v) q
  have hB_sa : IsSelfAdjoint B :=
    isSelfAdjoint_fromBlocks_iff.mpr ⟨hp_sa, by simp, hq_sa⟩
  have hB_sq : B * B = (2 : ℂ) • B := by
    simp only [B, fromBlocks_multiply, fromBlocks_add, hp.eq, hq_idem,
      CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hvp, hvq,
      mul_conjTranspose_eq_self_of_conjTranspose_mul_self hp hvp,
      conjTranspose_mul_eq_self_of_self_mul_conjTranspose hp hvp hvq,
      hv_mul_p,
      mul_self_eq_self_of_self_mul_conjTranspose hp hvp hvq, two_smul]
  exact ⟨by rw [smul_mul_smul_comm, hB_sq, smul_smul]; norm_num,
    by rw [star_smul, hB_sa.star_eq]; norm_num⟩

section NonUnitalCStar

variable {m n A : Type*} [Fintype m] [Fintype n]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In the unitization of `CStarMatrix (m ⊕ n) (m ⊕ n) A`, conjugating `fromBlocks p 0 0 0` by
`1 - 2 * rotationProjection p q v` yields `fromBlocks 0 0 0 q` without requiring `A` to be
unital. -/
private theorem unitization_one_sub_two_mul_rotationProjection_conj
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    ((1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) *
        (fromBlocks p 0 0 0 : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        (1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)))) =
      ((fromBlocks 0 0 0 q : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  have hvp_mul : v * p = v := mul_eq_self_of_conjTranspose_mul_eq v hp hvp
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
      (by simpa [ofMatrix_symm_mul] using congrArg ofMatrix.symm hvp)
      (by simpa [ofMatrix_symm_mul] using congrArg ofMatrix.symm hvq)
      (by simpa [ofMatrix_symm_mul] using congrArg ofMatrix.symm hvp_mul)

/-- The one-parameter family of unitaries `expUnitary ((π * t) • ⟨rotationProjection p q v, _⟩)` in
`Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)` whose conjugation rotates `inl p` to `inr q` on
`[0, 1]`. -/
def rotationUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (t : ℝ) : unitary (Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
  selfAdjoint.expUnitary ((Real.pi * t) •
    ⟨(rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
      selfAdjoint.mem_iff.mpr
        ((isStarProjection_rotationProjection hp hvp hvq).map
          (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint⟩)

/-- Defining exponential-unitary formula for `rotationUnitary` at an arbitrary real parameter
`t`. -/
theorem rotationUnitary_def {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (t : ℝ) :
    rotationUnitary hp hvp hvq t =
      selfAdjoint.expUnitary ((Real.pi * t) •
        ⟨(rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
          selfAdjoint.mem_iff.mpr
            ((isStarProjection_rotationProjection hp hvp hvq).map
              (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint⟩) := (rfl)

/-- At `t = 0`, `rotationUnitary` evaluates to the identity unitary `1`. -/
@[simp] theorem rotationUnitary_zero {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    rotationUnitary hp hvp hvq 0 = 1 := by
  rw [rotationUnitary, mul_zero, ← selfAdjoint.expUnitary_zero]
  exact congrArg _ (Subtype.ext (zero_smul ℝ _))

/-- At `t = 1`, `rotationUnitary` evaluates in the unitization to
`1 - 2 * rotationProjection p q v`. -/
theorem coe_rotationUnitary_one {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    (rotationUnitary hp hvp hvq 1 : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  rw [rotationUnitary, mul_one]
  exact ((isStarProjection_rotationProjection hp hvp hvq).map
    (Unitization.inrNonUnitalStarAlgHom ℂ _)).coe_expUnitary_pi_smul

/-- `rotationUnitary` varies continuously with `t : ℝ`. -/
theorem continuous_rotationUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Continuous (rotationUnitary hp hvp hvq) :=
  selfAdjoint.continuous_expUnitary.comp (by fun_prop)

private theorem rotationUnitary_conj_inl_snd_eq_and_isStarProjection
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (t : ℝ) :
    (((rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))).snd :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) ∧
    IsStarProjection
      ((rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))).snd := by
  set u := (rotationUnitary hp.isIdempotentElem hvp hvq t :
    Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))
  set x := ((inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
    Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))
  have hxU : IsStarProjection x :=
    (hp.map (inl (n := n) (R := ℂ))).map (Unitization.inrNonUnitalStarAlgHom ℂ _)
  have hcoe : ((u * x * star u).snd : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      u * x * star u :=
    inr_snd_eq_of_fst_eq_zero (by simp [x, Unitization.fst_mul, Unitization.fst_inr])
  have hprojU : IsStarProjection (u * x * star u) := by
    have h := hxU.map (Unitary.conjStarAlgAut ℂ
      (Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))
      (rotationUnitary hp.isIdempotentElem hvp hvq t))
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  rw [← hcoe] at hprojU
  exact ⟨hcoe, hprojU.of_inr⟩

/-- Explicit norm-continuous path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from
`inl p` to `inr q` associated to a concrete rectangular matrix `v` implementing `p ∼ q`, over any
(possibly non-unital) C⋆-algebra `A`. -/
def rotationPath {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path
      (⟨inl (n := n) (R := ℂ) p, hp.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨inr (m := m) (R := ℂ) q, hq.map (inr (m := m) (R := ℂ))⟩ where
  toFun t :=
    ⟨((rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))).snd,
      (rotationUnitary_conj_inl_snd_eq_and_isStarProjection hp hvp hvq t).2⟩
  continuous_toFun := by
    have hu : Continuous fun t : unitInterval ↦
        (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
      continuous_subtypeVal.comp
        ((continuous_rotationUnitary hp.isIdempotentElem hvp hvq).comp continuous_subtypeVal)
    exact Continuous.subtype_mk
      (Unitization.continuous_snd.comp ((hu.mul continuous_const).mul (continuous_star.comp hu))) _
  source' := by
    refine Subtype.ext (Unitization.inr_injective (R := ℂ) ?_)
    rw [(rotationUnitary_conj_inl_snd_eq_and_isStarProjection hp hvp hvq (0 : unitInterval)).1]
    simp
  target' := by
    have hrU : IsStarProjection
        (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
      (isStarProjection_rotationProjection hp.isIdempotentElem hvp hvq).map
        (Unitization.inrNonUnitalStarAlgHom ℂ _)
    refine Subtype.ext (Unitization.inr_injective (R := ℂ) ?_)
    rw [(rotationUnitary_conj_inl_snd_eq_and_isStarProjection hp hvp hvq (1 : unitInterval)).1]
    simp only [Set.Icc.coe_one, coe_rotationUnitary_one, hrU.isSelfAdjoint_one_sub_two_mul.star_eq,
      inl_apply, inr_apply]
    exact unitization_one_sub_two_mul_rotationProjection_conj hp.isIdempotentElem hvp hvq

/-- Evaluated inside `Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)`, `rotationPath` is conjugation
of `inl p` by `rotationUnitary`. -/
theorem inr_coe_rotationPath_apply {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (t : unitInterval) :
    ((rotationPath hp hq hvp hvq t : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
  (rotationUnitary_conj_inl_snd_eq_and_isStarProjection hp hvp hvq t).1

namespace MurrayVonNeumannEquiv

/-- Murray–von Neumann equivalent projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A`
become path-connected inside the space of star projections of `CStarMatrix (m ⊕ n) (m ⊕ n) A` as
`inl p` and `inr q`. -/
theorem joined_inl_inr {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    Joined
      (⟨inl (n := n) (R := ℂ) p, h.isStarProjection_left.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨inr (m := m) (R := ℂ) q, h.isStarProjection_right.map (inr (m := m) (R := ℂ))⟩ := by
  obtain ⟨v, hvp, hvq⟩ := h.exists_matrix
  exact ⟨rotationPath h.isStarProjection_left h.isStarProjection_right hvp hvq⟩

/-- Two Murray–von Neumann equivalent projections `p, q : CStarMatrix n n A` of the same matrix
size become path-connected after `2 × 2` stabilization `P ↦ fromBlocks P 0 0 0` inside the space
of star projections of `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem joined_inl_inl {p q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    Joined
      (⟨inl (n := n) (R := ℂ) p, h.isStarProjection_left.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P})
      ⟨inl (n := n) (R := ℂ) q, h.isStarProjection_right.map (inl (n := n) (R := ℂ))⟩ :=
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
      (isStarProjection_rotationProjection hp hvp hvq).isSelfAdjoint⟩) =
      ⟨stabilizedSymmetry p q v, stabilizedSymmetry_mem_unitary hp hvp hvq⟩ :=
  ((isStarProjection_rotationProjection hp hvp hvq).expUnitary_pi_smul).trans
    (Subtype.ext (one_sub_two_mul_rotationProjection p q v))

end UnitalCStar

end RotationPath

end StabilizedUnitaryAndRotationPath

end CStarMatrix
