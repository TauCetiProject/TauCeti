/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Matrix.Block

/-!
# Rectangular Murray–von Neumann equivalence and stabilized homotopy of matrix projections

Two projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` over a star semiring `A`, of
possibly different finite matrix sizes `m` and `n`, are *Murray–von Neumann equivalent*
(`CStarMatrix.MurrayVonNeumannEquiv p q`) when both are star projections and there exists a
rectangular matrix `v : CStarMatrix n m A` satisfying `v.conjTranspose * v = p` and
`v * v.conjTranspose = q`.

Using rectangular matrix multiplication directly — without casts between unequal matrix sizes — we
establish:

* **Equivalence-relation and monoid laws**: `MurrayVonNeumannEquiv` is reflexive on star
  projections, symmetric, and transitive (`(w * v).conjTranspose * (w * v) = p` and
  `(w * v) * (w * v).conjTranspose = s`), compatible with orthogonal block sums `fromBlocks`,
  preserved by entrywise `⋆`-algebra homomorphisms `mapₙₐ` and `mapₐ`, implied by unitary conjugacy,
  and invariant under zero-block padding, finite reindexing `reindexₐ`, block commutativity
  `Equiv.sumComm`, and block associativity `Equiv.sumAssoc`.
* **Square partial-isometry characterization**: when `m = n` and `A` is a C⋆-algebra (or whenever
  `CStarMatrix n n A` has a proper star), the implementing elements `v : CStarMatrix n n A` are
  precisely the partial isometries `TauCeti.IsPartialIsometry v`, with initial projection
  `star v * v` (`TauCeti.IsPartialIsometry.isStarProjection_star_mul_self`) and final projection
  `v * star v` (`TauCeti.IsPartialIsometry.isStarProjection_mul_star_self`).
* **Perturbation and homotopy → equivalence**: for any possibly non-unital C⋆-algebra `A`, nearby
  matrix projections (`‖p - q‖ < 1`) and endpoints of any norm-continuous path of projections in
  `CStarMatrix n n A` are Murray–von Neumann equivalent.
* **Equivalence → stabilized homotopy**: if `v.conjTranspose * v = p` and `v * v.conjTranspose = q`
  over a C⋆-algebra `A`, then `v * v.conjTranspose * v = v`. Over a unital algebra, the self-adjoint
  unitary `stabilizedSymmetry p q v = fromBlocks (1 - p) v.conjTranspose v (1 - q)` conjugates
  `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` (by
  `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq` and
  `Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`), and equals
  `1 - 2 • r = expUnitary (π • r)` for the star projection
  `r = stabilizedProjection p q v = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q`.
  Crucially, `r` and the resulting rotation path `stabilizedRotation p q v` from
  `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` lie entirely inside `CStarMatrix (m ⊕ n) (m ⊕ n) A`,
  even when `A` is non-unital.

## Main definitions

* `CStarMatrix.MurrayVonNeumannEquiv p q`: rectangular Murray–von Neumann equivalence of matrix
  projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A`.
* `CStarMatrix.stabilizedSymmetry p q v`: the block symmetry
  `fromBlocks (1 - p) v.conjTranspose v (1 - q)` over a unital coefficient ring.
* `CStarMatrix.stabilizedProjection p q v`: the star projection
  `(1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q` in `CStarMatrix (m ⊕ n) (m ⊕ n) A`.
* `CStarMatrix.stabilizedRotation p q v t`, `CStarMatrix.stabilizedPath`: the explicit rotation path
  of projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A` joining `fromBlocks p 0 0 0` to
  `fromBlocks 0 0 0 q`, passing at `t = 1 / 2` through
  `fromBlocks ((1 / 2 : ℝ) • p) ((I / 2) • v.conjTranspose) (-(I / 2) • v) ((1 / 2 : ℝ) • q)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Definition 4.6.1 and Propositions 4.6.2–4.6.6.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, London
  Mathematical Society Student Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

noncomputable section

open Matrix TauCeti
open scoped Real unitInterval

namespace CStarMatrix

section Algebraic

variable {l m n o R A B : Type*}

/-- Rectangular **Murray–von Neumann equivalence** of matrix projections: `p : CStarMatrix m m A`
and `q : CStarMatrix n n A` are star projections linked by a rectangular matrix
`v : CStarMatrix n m A` with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
def MurrayVonNeumannEquiv [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- Unfold `CStarMatrix.MurrayVonNeumannEquiv`. -/
theorem murrayVonNeumannEquiv_def [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    p.MurrayVonNeumannEquiv q ↔
      IsStarProjection p ∧ IsStarProjection q ∧
        ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  Iff.rfl

namespace MurrayVonNeumannEquiv

section Basic

variable [Fintype l] [Fintype m] [Fintype n] [Fintype o]

/-- The left matrix in a Murray–von Neumann equivalence is a star projection. -/
theorem isStarProjection_left [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection p :=
  h.1

/-- The right matrix in a Murray–von Neumann equivalence is a star projection. -/
theorem isStarProjection_right [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection q :=
  h.2.1

/-- Reflexivity of Murray–von Neumann equivalence on star projections (`v = p`). -/
theorem refl [Mul A] [AddCommMonoid A] [Star A] {p : CStarMatrix m m A}
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv p :=
  ⟨hp, hp, p, by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Symmetry of rectangular Murray–von Neumann equivalence (`v ↦ v.conjTranspose`). -/
@[symm]
theorem symm [AddCommMonoid A] [Mul A] [InvolutiveStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    q.MurrayVonNeumannEquiv p := by
  obtain ⟨hp, hq, v, hv₁, hv₂⟩ := h
  exact ⟨hq, hp, v.conjTranspose, by simpa using hv₂, by simpa using hv₁⟩

/-- Transitivity of rectangular Murray–von Neumann equivalence (`(w, v) ↦ w * v`). -/
@[trans]
theorem trans [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {s : CStarMatrix n n A}
    (h₁ : p.MurrayVonNeumannEquiv q) (h₂ : q.MurrayVonNeumannEquiv s) :
    p.MurrayVonNeumannEquiv s := by
  obtain ⟨hp, -, v, hv₁, hv₂⟩ := h₁
  obtain ⟨-, hs, w, hw₁, hw₂⟩ := h₂
  refine ⟨hp, hs, w * v, ?_, ?_⟩
  · calc (w * v).conjTranspose * (w * v)
        = v.conjTranspose * (w.conjTranspose * w) * v := by
          rw [conjTranspose_mul, ← hMul_assoc, hMul_assoc v.conjTranspose w.conjTranspose w]
      _ = v.conjTranspose * (v * v.conjTranspose) * v := by rw [hw₁, ← hv₂]
      _ = (v.conjTranspose * v) * (v.conjTranspose * v) := by
          rw [← hMul_assoc v.conjTranspose v v.conjTranspose, hMul_assoc]
      _ = p := by rw [hv₁, hp.isIdempotentElem.eq]
  · calc (w * v) * (w * v).conjTranspose
        = w * (v * v.conjTranspose) * w.conjTranspose := by
          rw [conjTranspose_mul, ← hMul_assoc, hMul_assoc w v v.conjTranspose]
      _ = w * (w.conjTranspose * w) * w.conjTranspose := by rw [hv₂, ← hw₁]
      _ = (w * w.conjTranspose) * (w * w.conjTranspose) := by
          rw [← hMul_assoc w w.conjTranspose w, hMul_assoc]
      _ = s := by rw [hw₂, hs.isIdempotentElem.eq]

/-- Zero projections of any two finite matrix sizes are Murray–von Neumann equivalent (`v = 0`). -/
theorem zero [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquiv (0 : CStarMatrix n n A) :=
  ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- On the subtype of square star projections of size `n`, `MurrayVonNeumannEquiv` is an equivalence
relation. -/
theorem equivalence [NonUnitalSemiring A] [StarRing A] :
    Equivalence (fun p q : {x : CStarMatrix n n A // IsStarProjection x} ↦
      p.1.MurrayVonNeumannEquiv q.1) :=
  ⟨fun p ↦ refl p.2, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Compatibility with orthogonal block sums `fromBlocks`. -/
theorem fromBlocks [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix l l A} {q₁ : CStarMatrix m m A}
    {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix o o A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.fromBlocks p₁ 0 0 p₂).MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks q₁ 0 0 q₂) := by
  obtain ⟨hp₁, hq₁, v₁, hv₁₁, hv₁₂⟩ := h₁
  obtain ⟨hp₂, hq₂, v₂, hv₂₁, hv₂₂⟩ := h₂
  refine ⟨isStarProjection_fromBlocks.mpr ⟨hp₁, hp₂⟩,
    isStarProjection_fromBlocks.mpr ⟨hq₁, hq₂⟩,
    CStarMatrix.fromBlocks v₁ 0 0 v₂, ?_, ?_⟩ <;>
    simp [hv₁₁, hv₁₂, hv₂₁, hv₂₂]

/-- Functoriality of rectangular Murray–von Neumann equivalence under entrywise non-unital
`⋆`-algebra homomorphisms. -/
theorem mapₙₐ [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (φ : A →⋆ₙₐ[R] B) :
    (CStarMatrix.mapₙₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ φ q) := by
  obtain ⟨hp, hq, v, hv₁, hv₂⟩ := h
  refine ⟨hp.map (CStarMatrix.mapₙₐ φ), hq.map (CStarMatrix.mapₙₐ φ),
    v.mapₗ (φ : A →ₗ[R] B), ?_, ?_⟩
  · rw [← mapₗ_conjTranspose φ, ← mapₗ_mul φ, hv₁]; rfl
  · rw [← mapₗ_conjTranspose φ, ← mapₗ_mul φ, hv₂]; rfl

/-- Functoriality under entrywise unital `⋆`-algebra homomorphisms. -/
theorem mapₐ [DecidableEq m] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (φ : A →⋆ₐ[R] B) :
    (CStarMatrix.mapₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ φ q) := by
  change ((CStarMatrix.mapₐ φ).toNonUnitalStarAlgHom p).MurrayVonNeumannEquiv
    ((CStarMatrix.mapₐ φ).toNonUnitalStarAlgHom q)
  rw [toNonUnitalStarAlgHom_mapₐ, toNonUnitalStarAlgHom_mapₐ]
  exact h.mapₙₐ φ.toNonUnitalStarAlgHom

/-- Unitary conjugacy in `CStarMatrix n n A` implies Murray–von Neumann equivalence. -/
theorem of_unitary_conj [DecidableEq n] [Semiring A] [StarRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (u : unitary (CStarMatrix n n A))
    (h : (u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A) = q) :
    p.MurrayVonNeumannEquiv q := by
  have hq : IsStarProjection q := by
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem, ← h]
      calc (u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A) *
              ((u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A))
          = (u : CStarMatrix n n A) * p *
              (star (u : CStarMatrix n n A) * (u : CStarMatrix n n A)) *
              p * star (u : CStarMatrix n n A) := by simp only [mul_assoc]
        _ = (u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A) := by
          rw [Unitary.star_mul_self_of_mem u.property, mul_one, mul_assoc (u : CStarMatrix n n A),
            hp.isIdempotentElem.eq]
    · rw [isSelfAdjoint_iff, ← h, star_mul, star_mul, star_star, hp.isSelfAdjoint.star_eq,
        mul_assoc]
  refine ⟨hp, hq, (u : CStarMatrix n n A) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc (star (u : CStarMatrix n n A)), Unitary.star_mul_self_of_mem u.property,
      one_mul, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc p, hp.isIdempotentElem.eq, ← mul_assoc, h]

end Basic

end MurrayVonNeumannEquiv

/-- A matrix equals itself up to `MurrayVonNeumannEquiv` iff it is a star projection. -/
@[simp]
theorem murrayVonNeumannEquiv_self_iff [Fintype m] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} : p.MurrayVonNeumannEquiv p ↔ IsStarProjection p :=
  ⟨MurrayVonNeumannEquiv.isStarProjection_left, MurrayVonNeumannEquiv.refl⟩

section PaddingAndReindex

variable [Fintype l] [Fintype m] [Fintype n] [Fintype o] [NonUnitalSemiring A] [StarRing A]

/-- Padding a star projection by zero blocks in the top-left corner preserves its
Murray–von Neumann equivalence class, without requiring unitality of `A`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_inlCorner {p : CStarMatrix m m A}
    (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (fromBlocks p (0 : CStarMatrix m n A) 0 0) := by
  refine ⟨hp, isStarProjection_fromBlocks.mpr ⟨hp, .zero _⟩,
    ofMatrix (Matrix.of fun r j ↦ Sum.casesOn r (fun i ↦ p i j) fun _ ↦ 0), ?_, ?_⟩
  · ext i j
    simp only [mul_apply, Fintype.sum_sum_type, conjTranspose_apply, ofMatrix_apply,
      Matrix.of_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [show (∑ a₁, star (p a₁ i) * p a₁ j) = (star p * p) i j by simp [mul_apply, star_apply],
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · ext (i | i) (j | j)
    · simp only [mul_apply, conjTranspose_apply, ofMatrix_apply, Matrix.of_apply,
        fromBlocks_apply₁₁]
      rw [show (∑ k, p i k * star (p j k)) = (p * star p) i j by simp [mul_apply, star_apply],
        hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    · simp [mul_apply]
    · simp [mul_apply]
    · simp [mul_apply]

/-- Reindexing a star projection along any bijection `e : m ≃ n` yields a Murray–von Neumann
equivalent projection, even over a non-unital coefficient ring `A`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindex {p : CStarMatrix m m A}
    (hp : IsStarProjection p) (e : m ≃ n) :
    p.MurrayVonNeumannEquiv (reindexₐ ℕ A e p) := by
  refine ⟨hp, hp.map (reindexₐ ℕ A e).toNonUnitalStarAlgHom,
    reindexₗ ℕ A e (Equiv.refl m) p, ?_, ?_⟩
  · rw [conjTranspose_reindexₗ, reindexₗ_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq]
    rfl
  · rw [conjTranspose_reindexₗ, reindexₗ_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq]
    rfl

/-- `MurrayVonNeumannEquiv` is invariant under arbitrary finite reindexings on both sides. -/
@[simp]
theorem MurrayVonNeumannEquiv.reindex_iff {p : CStarMatrix l l A} {q : CStarMatrix m m A}
    (e₁ : l ≃ n) (e₂ : m ≃ o) :
    (reindexₐ ℕ A e₁ p).MurrayVonNeumannEquiv (reindexₐ ℕ A e₂ q) ↔
      p.MurrayVonNeumannEquiv q := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp : IsStarProjection p := by
      have hp' := h.isStarProjection_left.map (reindexₐ ℕ A e₁.symm).toNonUnitalStarAlgHom
      simpa using hp'
    have hq : IsStarProjection q := by
      have hq' := h.isStarProjection_right.map (reindexₐ ℕ A e₂.symm).toNonUnitalStarAlgHom
      simpa using hq'
    exact (hp.murrayVonNeumannEquiv_reindex e₁).trans
      (h.trans (hq.murrayVonNeumannEquiv_reindex e₂).symm)
  · exact (h.isStarProjection_left.murrayVonNeumannEquiv_reindex e₁).symm.trans
      (h.trans (h.isStarProjection_right.murrayVonNeumannEquiv_reindex e₂))

/-- Padding a star projection by zero blocks in the bottom-right corner preserves its
Murray–von Neumann equivalence class. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_inrCorner {q : CStarMatrix n n A}
    (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (fromBlocks (0 : CStarMatrix m m A) 0 0 q) := by
  have h1 := hq.murrayVonNeumannEquiv_inlCorner (n := m)
  have h2 := (isStarProjection_fromBlocks.mpr ⟨hq, .zero (CStarMatrix m m A)⟩)
    |>.murrayVonNeumannEquiv_reindex (Equiv.sumComm n m)
  rw [reindexₐ_sumComm_fromBlocks] at h2
  exact h1.trans h2

/-- Block-diagonal direct sum of star projections is commutative up to `MurrayVonNeumannEquiv`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_comm
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (fromBlocks p 0 0 q).MurrayVonNeumannEquiv (fromBlocks q 0 0 p) := by
  have h := (isStarProjection_fromBlocks.mpr ⟨hp, hq⟩).murrayVonNeumannEquiv_reindex
    (Equiv.sumComm m n)
  rwa [reindexₐ_sumComm_fromBlocks] at h

/-- Block-diagonal direct sum of star projections is associative up to `MurrayVonNeumannEquiv`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_assoc
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {s : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hs : IsStarProjection s) :
    (fromBlocks (fromBlocks p 0 0 q) 0 0 s).MurrayVonNeumannEquiv
      (fromBlocks p 0 0 (fromBlocks q 0 0 s)) := by
  have hpq : IsStarProjection (fromBlocks p 0 0 q) := isStarProjection_fromBlocks.mpr ⟨hp, hq⟩
  have h := (isStarProjection_fromBlocks.mpr ⟨hpq, hs⟩).murrayVonNeumannEquiv_reindex
    (Equiv.sumAssoc l m n)
  rwa [reindexₐ_sumAssoc_fromBlocks] at h

end PaddingAndReindex

/-- A `1 × 1` star projection `toOneByOne m ℕ A a` is Murray–von Neumann equivalent to its `(i, i)`
diagonal corner `singleCorner i a` in `CStarMatrix n n A`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_singleCorner
    [Unique m] [Fintype n] [DecidableEq n] [NonUnitalSemiring A] [StarRing A]
    {a : A} (ha : IsStarProjection a) (i : n) :
    (toOneByOne m ℕ A a).MurrayVonNeumannEquiv (singleCorner (R := ℕ) i a) := by
  have ha₁ : IsStarProjection (toOneByOne m ℕ A a) := by
    refine ⟨?_, ?_⟩
    · ext x y
      simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact ha.isIdempotentElem.eq
    · ext x y
      simp only [star_eq_conjTranspose, conjTranspose_apply]
      exact ha.isSelfAdjoint.star_eq
  refine ⟨ha₁, (isStarProjection_singleCorner (R := ℕ) i).mpr ha,
    ofMatrix (Matrix.single i (default : m) a), ?_, ?_⟩
  · ext x y
    rw [Subsingleton.elim x default, Subsingleton.elim y default]
    simp only [mul_apply, conjTranspose_apply, ofMatrix_apply]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.single_apply_same, ha.isSelfAdjoint.star_eq, ha.isIdempotentElem.eq]
      rfl
    · intro j _ hji
      simp [hji.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · ext j k
    simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton, conjTranspose_apply,
      ofMatrix_apply, singleCorner_apply]
    rcases eq_or_ne i j with rfl | hj
    · rcases eq_or_ne i k with rfl | hk
      · simp [ha.isSelfAdjoint.star_eq, ha.isIdempotentElem.eq]
      · simp [hk]
    · simp [hj]

end Algebraic

section SquarePartialIsometry

variable {n A : Type*} [Fintype n]

/-- Every partial isometry `v : CStarMatrix n n A` implements a Murray–von Neumann equivalence
between its initial projection `star v * v` and its final projection `v * star v`. -/
theorem _root_.TauCeti.IsPartialIsometry.murrayVonNeumannEquiv [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n n A} (hv : IsPartialIsometry v) :
    (star v * v).MurrayVonNeumannEquiv (v * star v) :=
  ⟨hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self, v, rfl, rfl⟩

/-- For square matrices over any star ring where `CStarMatrix n n A` has a proper star (in
particular over any C⋆-algebra `A`), `MurrayVonNeumannEquiv` is implemented precisely by partial
isometries `TauCeti.IsPartialIsometry`. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry [NonUnitalRing A] [StarRing A]
    [IsProperStar (CStarMatrix n n A)] {p q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n n A, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hp, -, v, hv₁, hv₂⟩
    have hv_pi : IsPartialIsometry v := by
      rw [isPartialIsometry_iff_isStarProjection_star_mul_self, star_eq_conjTranspose, hv₁]
      exact hp
    exact ⟨v, hv_pi, hv₁, hv₂⟩
  · rintro ⟨v, hv_pi, rfl, rfl⟩
    exact hv_pi.murrayVonNeumannEquiv

end SquarePartialIsometry

section PerturbationAndPath

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]

/-- Smart constructor over a C⋆-algebra: if `IsStarProjection p` and `v.conjTranspose * v = p`,
`v * v.conjTranspose = q`, then `q` is automatically a star projection and
`p.MurrayVonNeumannEquiv q`. -/
theorem MurrayVonNeumannEquiv.of_conjTranspose_mul_self {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} (hp : IsStarProjection p) (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    p.MurrayVonNeumannEquiv q := by
  refine ⟨hp, ?_, v, hv₁, hv₂⟩
  rw [← hv₂]
  exact isStarProjection_mul_conjTranspose_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)

/-- Unitary conjugacy in the unitization `Unitization ℂ (CStarMatrix n n A)` implies
Murray–von Neumann equivalence in `CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_unitization_unitary_conj [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (u : unitary (Unitization ℂ (CStarMatrix n n A)))
    (hconj : (u : Unitization ℂ (CStarMatrix n n A)) * (p : Unitization ℂ (CStarMatrix n n A)) *
      star (u : Unitization ℂ (CStarMatrix n n A)) = (q : Unitization ℂ (CStarMatrix n n A))) :
    p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_iff_exists_isPartialIsometry]
  exact ⟨unitizationConjElem (u : Unitization ℂ (CStarMatrix n n A)) p,
    isPartialIsometry_unitizationConjElem u.property hp,
    star_unitizationConjElem_mul_self u.property hp,
    unitizationConjElem_mul_star_self hp hconj⟩

/-- Nearby matrix projections (`‖p - q‖ < 1`) in `CStarMatrix n n A` are Murray–von Neumann
equivalent, even when `A` is non-unital. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_of_norm_sub_lt_one
    [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_iff_exists_isPartialIsometry]
  exact hp.exists_isPartialIsometry_of_norm_sub_lt_one hq h

/-- Endpoints of any norm-continuous path of star projections in `CStarMatrix n n A` are
Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_path {p q : CStarMatrix n n A} (γ : Path p q)
    (hγ : ∀ t : I, IsStarProjection (γ t)) : p.MurrayVonNeumannEquiv q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [murrayVonNeumannEquiv_iff_exists_isPartialIsometry]
  exact IsStarProjection.exists_isPartialIsometry_of_path γ hγ

end PerturbationAndPath

section StabilizedHomotopy

variable {m n : Type*}

section UnitalSymmetry

variable {A : Type*} [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]

/-- The block symmetry `w = fromBlocks (1 - p) v.conjTranspose v (1 - q)` over a unital ring `A`
that conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` when `v` implements a Murray–von
Neumann equivalence between `p` and `q`. -/
def stabilizedSymmetry (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks (1 - p) v.conjTranspose v (1 - q)

/-- `stabilizedSymmetry p q v` is self-adjoint whenever `p` and `q` are self-adjoint. -/
theorem isSelfAdjoint_stabilizedSymmetry {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) (v : CStarMatrix n m A) :
    IsSelfAdjoint (stabilizedSymmetry p q v) := by
  rw [isSelfAdjoint_iff, stabilizedSymmetry, star_fromBlocks, star_eq_conjTranspose,
    conjTranspose_sub, conjTranspose_one, ← star_eq_conjTranspose, hp.star_eq,
    star_eq_conjTranspose, conjTranspose_sub, conjTranspose_one, ← star_eq_conjTranspose,
    hq.star_eq, conjTranspose_conjTranspose]

/-- Using `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq`, `stabilizedSymmetry p q v` squares to `1`
when `v.conjTranspose * v = p`, `v * v.conjTranspose = q`, and `v * v.conjTranspose * v = v`. -/
theorem stabilizedSymmetry_mul_self [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hvvv : v * v.conjTranspose * v = v) :
    stabilizedSymmetry p q v * stabilizedSymmetry p q v = 1 := by
  have hvp : v * p = v := by rwa [← hv₁, ← hMul_assoc]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    have := congrArg conjTranspose hvp
    rwa [conjTranspose_mul, show p.conjTranspose = p by
      rw [← hv₁, conjTranspose_mul, conjTranspose_conjTranspose]] at this
  apply ofMatrix.symm.injective
  change ofMatrix.symm (stabilizedSymmetry p q v) * ofMatrix.symm (stabilizedSymmetry p q v) = 1
  rw [stabilizedSymmetry, ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq
    (a := (ofMatrix.symm v)ᴴ) (b := ofMatrix.symm v)
    (congrArg ofMatrix.symm hv₁) (congrArg ofMatrix.symm hv₂)
    (congrArg ofMatrix.symm hpv) (congrArg ofMatrix.symm hvp)

/-- Under the hypotheses of `stabilizedSymmetry_mul_self`, `stabilizedSymmetry p q v` is unitary. -/
theorem stabilizedSymmetry_mem_unitary [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hvvv : v * v.conjTranspose * v = v) :
    stabilizedSymmetry p q v ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hsa := isSelfAdjoint_stabilizedSymmetry hp hq v
  have hsq := stabilizedSymmetry_mul_self hv₁ hv₂ hvvv
  exact ⟨by rwa [hsa.star_eq], by rwa [hsa.star_eq]⟩

/-- Using `Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`, conjugating
`fromBlocks p 0 0 0` by `stabilizedSymmetry p q v` yields `fromBlocks 0 0 0 q`. -/
theorem stabilizedSymmetry_mul_fromBlocks_mul [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hvvv : v * v.conjTranspose * v = v) :
    stabilizedSymmetry p q v * fromBlocks p 0 0 0 * stabilizedSymmetry p q v =
      fromBlocks 0 0 0 q := by
  have hvp : v * p = v := by rwa [← hv₁, ← hMul_assoc]
  apply ofMatrix.symm.injective
  change ofMatrix.symm (stabilizedSymmetry p q v) *
      ofMatrix.symm (fromBlocks p (0 : CStarMatrix m n A) 0 0) *
      ofMatrix.symm (stabilizedSymmetry p q v) =
    ofMatrix.symm (fromBlocks (0 : CStarMatrix m m A) 0 0 q)
  rw [stabilizedSymmetry, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (a := (ofMatrix.symm v)ᴴ) (b := ofMatrix.symm v)
    (congrArg ofMatrix.symm hv₁) (congrArg ofMatrix.symm hv₂) (congrArg ofMatrix.symm hvp)

end UnitalSymmetry

section RotationPath

/-- The stabilized star projection `r = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q` in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. Over a unital algebra this equals `(1 / 2 : ℝ) • (1 - w)` for
`w = stabilizedSymmetry p q v`, yet `r` itself requires neither a unit in `A` nor `DecidableEq` on
the index types. -/
def stabilizedProjection {A : Type*} [Neg A] [SMul ℝ A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q

/-- Over a unital ring with `ℝ`-module structure, `stabilizedProjection p q v` equals
`(1 / 2 : ℝ) • (1 - w)` where `w = stabilizedSymmetry p q v`. -/
theorem stabilizedProjection_eq_half_one_sub {B : Type*} [Ring B] [StarRing B] [Module ℝ B]
    [DecidableEq m] [DecidableEq n] (p : CStarMatrix m m B) (q : CStarMatrix n n B)
    (v : CStarMatrix n m B) :
    stabilizedProjection p q v = (1 / 2 : ℝ) • (1 - stabilizedSymmetry p q v) := by
  rw [stabilizedProjection, stabilizedSymmetry, ← fromBlocks_one, fromBlocks_sub]
  congr 1
  ext (i | i) (j | j) <;> simp

/-- Over a unital ring with `ℝ`-module structure, `1 - (2 : ℝ) • stabilizedProjection p q v` equals
`stabilizedSymmetry p q v`. -/
theorem one_sub_two_smul_stabilizedProjection {B : Type*} [Ring B] [StarRing B] [Module ℝ B]
    [DecidableEq m] [DecidableEq n] (p : CStarMatrix m m B) (q : CStarMatrix n n B)
    (v : CStarMatrix n m B) :
    1 - (2 : ℝ) • stabilizedProjection p q v = stabilizedSymmetry p q v := by
  rw [stabilizedProjection_eq_half_one_sub, smul_smul]
  norm_num

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- When `v` implements a Murray–von Neumann equivalence between `p` and `q`,
`stabilizedProjection p q v` is a star projection in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_stabilizedProjection [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    IsStarProjection (stabilizedProjection p q v) := by
  have hvvv : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  have hvvv' : v.conjTranspose * v * v.conjTranspose = v.conjTranspose :=
    conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  have hvp : v * p = v := by rw [← hv₁, ← hMul_assoc, hvvv]
  have hpv : p * v.conjTranspose = v.conjTranspose := by rw [← hv₁, hvvv']
  have hqv : q * v = v := by rw [← hv₂, hvvv]
  have hvq : v.conjTranspose * q = v.conjTranspose := by rw [← hv₂, ← hMul_assoc, hvvv']
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, stabilizedProjection, smul_mul, mul_smul, smul_smul, fromBlocks_mul]
    have h11 : p * p + (-v.conjTranspose) * (-v) = (2 : ℝ) • p := by
      have : (-v.conjTranspose) * (-v) = v.conjTranspose * v := by
        ext i j; simp [mul_apply]
      rw [this, hp.isIdempotentElem.eq, hv₁, two_smul]
    have h12 : p * (-v.conjTranspose) + (-v.conjTranspose) * q = (2 : ℝ) • (-v.conjTranspose) := by
      have hpv_neg : p * (-v.conjTranspose) = -(p * v.conjTranspose) := by
        ext i j; simp [mul_apply]
      have hvq_neg : (-v.conjTranspose) * q = -(v.conjTranspose * q) := by
        ext i j; simp [mul_apply]
      rw [hpv_neg, hvq_neg, hpv, hvq, two_smul]
    have h21 : (-v) * p + q * (-v) = (2 : ℝ) • (-v) := by
      have hvp_neg : (-v) * p = -(v * p) := by ext i j; simp [mul_apply]
      have hqv_neg : q * (-v) = -(q * v) := by ext i j; simp [mul_apply]
      rw [hvp_neg, hqv_neg, hvp, hqv, two_smul]
    have h22 : (-v) * (-v.conjTranspose) + q * q = (2 : ℝ) • q := by
      have : (-v) * (-v.conjTranspose) = v * v.conjTranspose := by
        ext i j; simp [mul_apply]
      rw [this, hv₂, hq.isIdempotentElem.eq, two_smul]
    rw [h11, h12, h21, h22, ← fromBlocks_smul, smul_smul]
    norm_num
  · rw [isSelfAdjoint_iff, stabilizedProjection, star_smul, star_trivial, star_fromBlocks,
      hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, conjTranspose_neg, conjTranspose_neg,
      conjTranspose_conjTranspose]

/-- Over a unital C⋆-algebra `B`, `expUnitary (π • r) = stabilizedSymmetry p q v` for
`r = stabilizedProjection p q v`, so `selfAdjoint.expUnitaryPathToOne (π • r)` explicitly joins `1`
to `stabilizedSymmetry p q v` along `t ↦ expUnitary ((t * π) • r)`. -/
theorem coe_expUnitary_pi_stabilizedProjection [Fintype m] [Fintype n]
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [DecidableEq m] [DecidableEq n] {p : CStarMatrix m m B} {q : CStarMatrix n n B}
    {v : CStarMatrix n m B} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    (selfAdjoint.expUnitary (π • ⟨stabilizedProjection p q v,
      selfAdjoint.mem_iff.mpr
        (isStarProjection_stabilizedProjection hp hq hv₁ hv₂).isSelfAdjoint⟩) :
        CStarMatrix (m ⊕ n) (m ⊕ n) B) = stabilizedSymmetry p q v := by
  have hr := isStarProjection_stabilizedProjection hp hq hv₁ hv₂
  exact (hr.coe_expUnitary_pi_smul).trans (one_sub_two_smul_stabilizedProjection p q v)

/-- Explicit rotation family `stabilizedRotation p q v t` in `CStarMatrix (m ⊕ n) (m ⊕ n) A` joining
`fromBlocks p 0 0 0` (at `t = 0`) to `fromBlocks 0 0 0 q` (at `t = 1`). In the unitization this
equals `expUnitary ((t * π) • r) * fromBlocks p 0 0 0 * star (expUnitary ((t * π) • r))` where
`r = stabilizedProjection p q v`, while staying inside `CStarMatrix (m ⊕ n) (m ⊕ n) A` even for
non-unital `A`. -/
def stabilizedRotation (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : ℝ) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks ((Real.cos (π * t / 2) ^ 2 : ℝ) • p)
    (((Complex.I / 2) * Real.sin (π * t)) • v.conjTranspose)
    ((-(Complex.I / 2) * Real.sin (π * t)) • v)
    ((Real.sin (π * t / 2) ^ 2 : ℝ) • q)

/-- At `t = 0`, `stabilizedRotation p q v 0` is the top-left corner `fromBlocks p 0 0 0`. -/
@[simp]
theorem stabilizedRotation_zero (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v 0 = fromBlocks p 0 0 0 := by
  simp [stabilizedRotation]

/-- At `t = 1`, `stabilizedRotation p q v 1` is the bottom-right corner `fromBlocks 0 0 0 q`. -/
@[simp]
theorem stabilizedRotation_one (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v 1 = fromBlocks 0 0 0 q := by
  simp [stabilizedRotation]

/-- At the midpoint `t = 1 / 2`, `stabilizedRotation p q v (1 / 2)` is the projection
`fromBlocks ((1 / 2 : ℝ) • p) ((I / 2) • v.conjTranspose) (-(I / 2) • v) ((1 / 2 : ℝ) • q)`. -/
theorem stabilizedRotation_half (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v (1 / 2) =
      fromBlocks ((1 / 2 : ℝ) • p) ((Complex.I / 2) • v.conjTranspose)
        (-(Complex.I / 2) • v) ((1 / 2 : ℝ) • q) := by
  have hangle : π * (1 / 2 : ℝ) / 2 = π / 4 := by ring
  have hangle2 : π * (1 / 2 : ℝ) = π / 2 := by ring
  have hcos : Real.cos (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]
    norm_num
  have hsin : Real.sin (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]
    norm_num
  rw [stabilizedRotation, hangle, hangle2, hcos, hsin, Real.sin_pi_div_two]
  simp

/-- In `Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)`, `stabilizedRotation p q v t` is literally
the unitary conjugate of `fromBlocks p 0 0 0` by `expUnitary ((t * π) • r)` for
`r = stabilizedProjection p q v`. -/
theorem inr_stabilizedRotation_eq_expUnitary_conj [Fintype m] [Fintype n]
    [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} {v : CStarMatrix n m A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (t : ℝ) :
    ((stabilizedRotation p q v t : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (selfAdjoint.expUnitary ((t * π) •
          ⟨((stabilizedProjection p q v : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
              Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
            selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
              (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint)⟩) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        ((fromBlocks p (0 : CStarMatrix m n A) 0 0 : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
      star (selfAdjoint.expUnitary ((t * π) •
          ⟨((stabilizedProjection p q v : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
              Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
            selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
              (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint)⟩) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  set B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  set r : B := stabilizedProjection p q v
  set x : B := fromBlocks p (0 : CStarMatrix m n A) 0 0
  have hr : IsStarProjection r := isStarProjection_stabilizedProjection hp hq hv₁ hv₂
  have hr_inr : IsStarProjection (r : Unitization ℂ B) :=
    hr.map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hvvv : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  have hvvv' : v.conjTranspose * v * v.conjTranspose = v.conjTranspose :=
    conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  have hvp : v * p = v := by rw [← hv₁, ← hMul_assoc, hvvv]
  have hpv : p * v.conjTranspose = v.conjTranspose := by rw [← hv₁, hvvv']
  -- Compute `r * x`, `x * r`, and `r * x * r` inside `B`.
  have hrx : r * x = (1 / 2 : ℝ) • fromBlocks p 0 (-v) 0 := by
    have hvp_neg : (-v) * p = -v := by
      have : (-v) * p = -(v * p) := by ext i j; simp [mul_apply]
      rw [this, hvp]
    rw [show r = stabilizedProjection p q v from rfl, show x = _ from rfl, stabilizedProjection,
      smul_mul, fromBlocks_mul]
    simp [hp.isIdempotentElem.eq, hvp_neg]
  have hxr : x * r = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) 0 0 := by
    have hpv_neg : p * (-v.conjTranspose) = -v.conjTranspose := by
      have : p * (-v.conjTranspose) = -(p * v.conjTranspose) := by ext i j; simp [mul_apply]
      rw [this, hpv]
    rw [show r = stabilizedProjection p q v from rfl, show x = _ from rfl, stabilizedProjection,
      mul_smul, fromBlocks_mul]
    simp [hp.isIdempotentElem.eq, hpv_neg]
  have hrxr : r * x * r = (1 / 4 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := by
    have hpv_neg : p * (-v.conjTranspose) = -v.conjTranspose := by
      have : p * (-v.conjTranspose) = -(p * v.conjTranspose) := by ext i j; simp [mul_apply]
      rw [this, hpv]
    have hvp_neg : (-v) * p = -v := by
      have : (-v) * p = -(v * p) := by ext i j; simp [mul_apply]
      rw [this, hvp]
    have hvv_neg : (-v) * (-v.conjTranspose) = q := by
      have : (-v) * (-v.conjTranspose) = v * v.conjTranspose := by ext i j; simp [mul_apply]
      rw [this, hv₂]
    rw [hrx, show r = stabilizedProjection p q v from rfl, stabilizedProjection, smul_mul, mul_smul,
      smul_smul, fromBlocks_mul]
    simp only [hp.isIdempotentElem.eq, CStarMatrix.zero_mul, add_zero, hpv_neg, hvp_neg, hvv_neg]
    norm_num
  -- Expand `(1 + (ζ - 1) r) x (1 + (star ζ - 1) r)` in `Unitization ℂ B`.
  set ζ : ℂ := Complex.exp (Complex.I * (t * π))
  have h_exp : (selfAdjoint.expUnitary ((t * π) •
      ⟨(r : Unitization ℂ B), selfAdjoint.mem_iff.mpr hr_inr.isSelfAdjoint⟩) :
      Unitization ℂ B) = 1 + (ζ - 1) • (r : Unitization ℂ B) := by
    simpa [ζ] using hr_inr.coe_expUnitary_smul (t * π)
  rw [h_exp, star_add, star_one, star_smul, star_sub, star_one, hr_inr.isSelfAdjoint.star_eq]
  have hexpand :
      (1 + (ζ - 1) • (r : Unitization ℂ B)) * (x : Unitization ℂ B) *
          (1 + (star ζ - 1) • (r : Unitization ℂ B)) =
        ((x + (ζ - 1) • (r * x) + (star ζ - 1) • (x * r) +
          ((ζ - 1) * (star ζ - 1)) • (r * x * r) : B) : Unitization ℂ B) := by
    push_cast
    simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_assoc, mul_comm (star ζ - 1) (ζ - 1)]
    abel
  rw [hexpand]
  congr 1
  -- Match the four `2 × 2` blocks via Euler's formula `ζ = cos (π t) + I * sin (π t)`.
  have hζ : ζ = (Real.cos (π * t) : ℂ) + (Real.sin (π * t) : ℂ) * Complex.I := by
    have : Complex.I * (t * π : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [show ζ = Complex.exp (Complex.I * (t * π : ℂ)) from rfl, this, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hζ_star : star ζ = (Real.cos (π * t) : ℂ) - (Real.sin (π * t) : ℂ) * Complex.I := by
    rw [hζ, star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have hcos_sq : ((Real.cos (π * t / 2) ^ 2 : ℝ) : ℂ) = (1 + (Real.cos (π * t) : ℂ)) / 2 := by
    have h := Real.cos_sq (π * t / 2)
    rw [show 2 * (π * t / 2) = π * t by ring] at h
    rw [h]
    push_cast
    ring
  have hsin_sq : ((Real.sin (π * t / 2) ^ 2 : ℝ) : ℂ) = (1 - (Real.cos (π * t) : ℂ)) / 2 := by
    rw [Real.sin_sq, Complex.ofReal_sub, Complex.ofReal_one, hcos_sq]
    ring
  have hpyth : (Real.cos (π * t) : ℂ) ^ 2 + (Real.sin (π * t) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (π * t)
  have hc11 : 1 + (ζ - 1) * (1 / 2 : ℂ) + (star ζ - 1) * (1 / 2 : ℂ) +
      ((ζ - 1) * (star ζ - 1)) * (1 / 4 : ℂ) = ((Real.cos (π * t / 2) ^ 2 : ℝ) : ℂ) := by
    rw [hcos_sq, hζ_star, hζ]
    linear_combination (1 / 4 : ℂ) * hpyth - (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  have hc12 : -((star ζ - 1) * (1 / 2 : ℂ)) - ((ζ - 1) * (star ζ - 1)) * (1 / 4 : ℂ) =
      (Complex.I / 2) * (Real.sin (π * t) : ℂ) := by
    rw [hζ_star, hζ]
    linear_combination -(1 / 4 : ℂ) * hpyth +
      (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  have hc21 : -((ζ - 1) * (1 / 2 : ℂ)) - ((ζ - 1) * (star ζ - 1)) * (1 / 4 : ℂ) =
      -(Complex.I / 2) * (Real.sin (π * t) : ℂ) := by
    rw [hζ_star, hζ]
    linear_combination -(1 / 4 : ℂ) * hpyth +
      (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  have hc22 : ((ζ - 1) * (star ζ - 1)) * (1 / 4 : ℂ) =
      ((Real.sin (π * t / 2) ^ 2 : ℝ) : ℂ) := by
    rw [hsin_sq, hζ_star, hζ]
    linear_combination (1 / 4 : ℂ) * hpyth - (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  rw [stabilizedRotation, hrxr, hrx, hxr]
  dsimp only [B, x]
  ext (i | i) (j | j)
  · simp only [add_apply, smul_apply, fromBlocks_apply₁₁, ← Complex.coe_smul, smul_smul]
    nth_rw 2 [← one_smul ℂ (p i j)]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1; push_cast at hc11 ⊢; exact hc11.symm
  · simp only [add_apply, smul_apply, neg_apply, zero_apply, fromBlocks_apply₁₂, smul_zero,
      smul_neg, zero_add, ← Complex.coe_smul, smul_smul]
    rw [← neg_smul, ← neg_smul, ← add_smul]
    congr 1; push_cast at hc12 ⊢; linear_combination -hc12
  · simp only [add_apply, smul_apply, neg_apply, zero_apply, fromBlocks_apply₂₁, smul_zero,
      smul_neg, zero_add, add_zero, ← Complex.coe_smul, smul_smul]
    rw [← neg_smul, ← neg_smul, ← add_smul]
    congr 1; push_cast at hc21 ⊢; linear_combination -hc21
  · simp only [add_apply, smul_apply, zero_apply, fromBlocks_apply₂₂, smul_zero, zero_add,
      ← Complex.coe_smul, smul_smul]
    congr 1; push_cast at hc22 ⊢; exact hc22.symm

/-- For every `t : ℝ`, `stabilizedRotation p q v t` is a star projection in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_stabilizedRotation [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : ℝ) :
    IsStarProjection (stabilizedRotation p q v t) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  let u := selfAdjoint.expUnitary ((t * π) •
    ⟨((stabilizedProjection p q v : B) : Unitization ℂ B),
      selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
        (Unitization.inrNonUnitalStarAlgHom ℂ B)).isSelfAdjoint)⟩)
  set x0 : Unitization ℂ B := ((fromBlocks p (0 : CStarMatrix m n A) 0 0 : B) : Unitization ℂ B)
  have hx : IsStarProjection x0 :=
    (isStarProjection_fromBlocks.mpr ⟨hp, .zero _⟩).map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hconj_proj : IsStarProjection ((u : Unitization ℂ B) * x0 * star (u : Unitization ℂ B)) := by
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (u : Unitization ℂ B) * x0 * star (u : Unitization ℂ B) *
              ((u : Unitization ℂ B) * x0 * star (u : Unitization ℂ B))
          = (u : Unitization ℂ B) * x0 * (star (u : Unitization ℂ B) * (u : Unitization ℂ B)) *
              x0 * star (u : Unitization ℂ B) := by simp only [mul_assoc]
        _ = (u : Unitization ℂ B) * x0 * star (u : Unitization ℂ B) := by
          rw [Unitary.star_mul_self_of_mem u.property, mul_one,
            mul_assoc (u : Unitization ℂ B), hx.isIdempotentElem.eq]
    · rw [isSelfAdjoint_iff, star_mul, star_mul, star_star, hx.isSelfAdjoint.star_eq, mul_assoc]
  rw [← inr_stabilizedRotation_eq_expUnitary_conj hp hq hv₁ hv₂ t] at hconj_proj
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    exact Unitization.inr_injective (R := ℂ)
      (by simpa only [Unitization.inr_mul] using hconj_proj.isIdempotentElem.eq)
  · rw [isSelfAdjoint_iff]
    exact Unitization.inr_injective (R := ℂ)
      (by simpa only [Unitization.inr_star] using hconj_proj.isSelfAdjoint.star_eq)

section TopologicalPath

/-- Continuity of `t ↦ stabilizedRotation p q v t` in operator norm. -/
theorem continuous_stabilizedRotation (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : Continuous (stabilizedRotation p q v) := by
  have hdecomp : stabilizedRotation p q v = fun t : ℝ ↦
      (Real.cos (π * t / 2) ^ 2 : ℝ) • fromBlocks p (0 : CStarMatrix m n A) 0 0 +
      (((Complex.I / 2) * Real.sin (π * t)) •
        fromBlocks (0 : CStarMatrix m m A) v.conjTranspose 0 0 +
      (((-(Complex.I / 2) * Real.sin (π * t)) •
        fromBlocks (0 : CStarMatrix m m A) (0 : CStarMatrix m n A) v 0) +
      (Real.sin (π * t / 2) ^ 2 : ℝ) • fromBlocks (0 : CStarMatrix m m A) 0 0 q)) :=
    funext fun t ↦ by simp [stabilizedRotation]
  rw [hdecomp]
  fun_prop

/-- Bundled norm-continuous `Path` in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q` through star projections, constructed from a rectangular implementing matrix
`v : CStarMatrix n m A`. -/
def stabilizedPath (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    Path (fromBlocks p (0 : CStarMatrix m n A) 0 0)
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) where
  toFun t := stabilizedRotation p q v t
  continuous_toFun := (continuous_stabilizedRotation p q v).comp continuous_subtype_val
  source' := stabilizedRotation_zero p q v
  target' := stabilizedRotation_one p q v

/-- Evaluation of `stabilizedPath` at `t : I` gives `stabilizedRotation` at `(t : ℝ)`. -/
@[simp]
theorem stabilizedPath_apply (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : I) :
    stabilizedPath p q v t = stabilizedRotation p q v t :=
  (rfl)

/-- Every point on `stabilizedPath p q v` is a star projection when `v` implements a Murray–von
Neumann equivalence between `p` and `q`. -/
theorem isStarProjection_stabilizedPath [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : I) :
    IsStarProjection (stabilizedPath p q v t) :=
  isStarProjection_stabilizedRotation hp hq hv₁ hv₂ t

/-- **Stabilized homotopy of Murray–von Neumann equivalent projections**: if
`p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann equivalent over a
possibly non-unital C⋆-algebra `A`, then `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are joined
by a norm-continuous path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_path [Fintype m] [Fintype n]
    {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p (0 : CStarMatrix m n A) 0 0)
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨hp, hq, v, hv₁, hv₂⟩ := h
  exact ⟨stabilizedPath p q v, isStarProjection_stabilizedPath hp hq hv₁ hv₂⟩

/-- **Characterization of Murray–von Neumann equivalence via stabilized homotopy**: two star
projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` over a C⋆-algebra `A` are
Murray–von Neumann equivalent if and only if `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are
joined by a norm-continuous path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_stabilized_path [Fintype m] [Fintype n]
    {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ γ : Path (fromBlocks p (0 : CStarMatrix m n A) 0 0)
          (fromBlocks (0 : CStarMatrix m m A) 0 0 q),
        ∀ t : I, IsStarProjection (γ t) := by
  refine ⟨MurrayVonNeumannEquiv.exists_stabilized_path, ?_⟩
  rintro ⟨γ, hγ⟩
  exact (hp.murrayVonNeumannEquiv_inlCorner (n := n)).trans
    ((MurrayVonNeumannEquiv.of_path γ hγ).trans
      (hq.murrayVonNeumannEquiv_inrCorner (m := m)).symm)

end TopologicalPath

end RotationPath

end StabilizedHomotopy

end CStarMatrix
