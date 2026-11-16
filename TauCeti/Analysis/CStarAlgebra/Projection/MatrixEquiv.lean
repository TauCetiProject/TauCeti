/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Homotopy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Data.Matrix.Block

/-!
# Rectangular Murray–von Neumann equivalence and stabilized homotopy of matrix projections

This file develops rectangular Murray–von Neumann equivalence for star projections in
`CStarMatrix` over (possibly non-unital) complex C⋆-algebras, connecting it to partial isometries,
algebraic equivalence, nearby-projection perturbation, and stabilized projection homotopy:

* Rectangular partial-isometry identities in `CStarMatrix`: if `vᴴ * v` is a star projection over
  a star-ordered ring with proper star, then `v * vᴴ * v = v` and `v * vᴴ` is a star projection.
* `CStarMatrix.MurrayVonNeumannEquiv`: two projections `p : CStarMatrix m m A` and
  `q : CStarMatrix n n A` (possibly of different finite matrix sizes) are Murray–von Neumann
  equivalent when there exists a rectangular matrix `v : CStarMatrix n m A` with `vᴴ * v = p` and
  `v * vᴴ = q`.
* Equivalence relation and structural properties: reflexivity, symmetry, transitivity, zero
  projections, block-diagonal sums, orthogonal sums, corner inclusions, arbitrary finite
  reindexing, commutativity and associativity of block sums, preservation by non-unital and unital
  ⋆-homomorphisms, and implication from unitary conjugacy.
* Square matrix identification with `TauCeti.IsPartialIsometry`, upgrade of rectangular algebraic
  equivalence `x * y = p`, `y * x = q` to Murray–von Neumann equivalence (Blackadar, Proposition
  4.6.4), and implications from norm proximity `‖p - q‖ < 1` and norm-continuous paths of
  projections.
* Stabilized unitary conjugacy and projection homotopy: the explicit self-adjoint reflection
  unitary `[[1 - p, vᴴ], [v, 1 - q]]` and rotation unitary `[[1 - p, -vᴴ], [v, 1 - q]]` built
  via `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq` and
  `Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`, the explicit
  exponential path joining `1` to the reflection unitary (with closed-form midpoint evaluation at
  `t = 1/2`), and non-unital stabilized projection paths from `p ⊕ 0` to `0 ⊕ q` and (for equal
  sizes) from `p ⊕ 0` to `q ⊕ 0`.

## Main declarations

* `CStarMatrix.mul_conjTranspose_mul_self_of_isStarProjection`: `v * vᴴ * v = v` whenever
  `vᴴ * v` is a star projection over a star-ordered ring with proper star.
* `CStarMatrix.MurrayVonNeumannEquiv`: rectangular Murray–von Neumann equivalence of matrix
  projections.
* `CStarMatrix.murrayVonNeumannEquiv_iff_exists_isPartialIsometry`: equivalence with
  `TauCeti.IsPartialIsometry` for square matrices.
* `CStarMatrix.MurrayVonNeumannEquiv.of_mul_eq`: rectangular algebraic equivalence of projections
  implies Murray–von Neumann equivalence.
* `CStarMatrix.stabilizedReflectionUnitary` and `CStarMatrix.stabilizedRotationUnitary`: explicit
  stabilized unitaries conjugating `p ⊕ 0` to `0 ⊕ q`.
* `CStarMatrix.stabilizedReflectionPath_conj_half`: midpoint formula along the exponential
  reflection path, `[[(1/2) • p, (i/2) • vᴴ], [(-i/2) • v, (1/2) • q]]`.
* `CStarMatrix.MurrayVonNeumannEquiv.exists_stabilized_path` and
  `CStarMatrix.MurrayVonNeumannEquiv.exists_stabilized_path_left`: non-unital stabilized paths of
  projections from `p ⊕ 0` to `0 ⊕ q` and to `q ⊕ 0`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Chapter III, §4.6 (Definition 4.6.1 and
  Propositions 4.6.2–4.6.6).
-/

public section

open scoped ComplexOrder CStarAlgebra unitInterval

namespace CStarMatrix

section RectangularPartialIsometry

variable {m n A : Type*}

/-- If `v.conjTranspose * v` is a star projection for a rectangular C⋆-matrix `v` over a
star-ordered ring with proper star, then `v * v.conjTranspose * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isStarProjection [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix n m A} (hv : IsStarProjection (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  have hidem : (v.conjTranspose * v) * (v.conjTranspose * v) = v.conjTranspose * v :=
    hv.isIdempotentElem.eq
  have hzero : (v - v * (v.conjTranspose * v)).conjTranspose *
      (v - v * (v.conjTranspose * v)) = 0 := by
    calc (v - v * (v.conjTranspose * v)).conjTranspose * (v - v * (v.conjTranspose * v))
        = (v.conjTranspose - (v.conjTranspose * v) * v.conjTranspose) *
            (v - v * (v.conjTranspose * v)) := by
          simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
      _ = v.conjTranspose * v - (v.conjTranspose * v) * (v.conjTranspose * v) -
            (v.conjTranspose * v) * (v.conjTranspose * v) +
            (v.conjTranspose * v) * ((v.conjTranspose * v) * (v.conjTranspose * v)) := by
          simp only [CStarMatrix.sub_mul, CStarMatrix.mul_sub, mul_assoc]
          abel
      _ = 0 := by
          rw [hidem, hidem]
          abel
  have hsub : v - v * (v.conjTranspose * v) = 0 := conjTranspose_mul_self_eq_zero.mp hzero
  rw [mul_assoc]
  exact (sub_eq_zero.mp hsub).symm

/-- If `v.conjTranspose * v` is a star projection for a rectangular C⋆-matrix `v`, then
`v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_mul_conjTranspose_of_isStarProjection [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix n m A} (hv : IsStarProjection (v.conjTranspose * v)) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  have h := congr_arg conjTranspose (mul_conjTranspose_mul_self_of_isStarProjection hv)
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc] using h

/-- If `v.conjTranspose * v` is a star projection for a rectangular C⋆-matrix `v` over a
star-ordered ring with proper star, then `v * v.conjTranspose` is also a star projection. -/
theorem isStarProjection_mul_conjTranspose_of_conjTranspose_mul [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix n m A} (hv : IsStarProjection (v.conjTranspose * v)) :
    IsStarProjection (v * v.conjTranspose) where
  isIdempotentElem := by
    rw [IsIdempotentElem, ← mul_assoc, mul_conjTranspose_mul_self_of_isStarProjection hv]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

private theorem mul_proj_eq_of_conjTranspose_mul_eq [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    v * p = v ∧ q * v = v ∧ p * v.conjTranspose = v.conjTranspose ∧
      v.conjTranspose * q = v.conjTranspose := by
  have hv : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isStarProjection (hvp ▸ hp)
  have hvp' : v * p = v := by rw [← hvp, ← mul_assoc, hv]
  have hqv' : q * v = v := by rw [← hvq, hv]
  have hpv' : p * v.conjTranspose = v.conjTranspose := by
    have h := congr_arg conjTranspose hvp'
    simpa only [conjTranspose_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using h
  have hq_star : q.conjTranspose = q := by
    rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  have hvq' : v.conjTranspose * q = v.conjTranspose := by
    have h := congr_arg conjTranspose hqv'
    simpa only [conjTranspose_mul, hq_star] using h
  exact ⟨hvp', hqv', hpv', hvq'⟩

end RectangularPartialIsometry

section MurrayVonNeumannDef

variable {l m n k R A B : Type*}

/-- Two star projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A`, possibly of
different finite matrix sizes, are **Murray–von Neumann equivalent** if there exists a rectangular
matrix `v : CStarMatrix n m A` with `vᴴ * v = p` and `v * vᴴ = q` (Blackadar, Definition 4.6.1). -/
def MurrayVonNeumannEquiv [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

theorem murrayVonNeumannEquiv_iff [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      IsStarProjection p ∧ IsStarProjection q ∧
        ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  Iff.rfl

namespace MurrayVonNeumannEquiv

theorem isStarProjection_left [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection p :=
  h.1

theorem isStarProjection_right [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection q :=
  h.2.1

/-- Construct a Murray–von Neumann equivalence over a star-ordered ring with proper star from
`vᴴ * v = p` and `v * vᴴ = q` assuming only that `p` is a star projection. -/
theorem of_conjTranspose_mul_eq [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsStarProjection p)
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    p.MurrayVonNeumannEquiv q :=
  ⟨hp, hvq ▸ isStarProjection_mul_conjTranspose_of_conjTranspose_mul (hvp ▸ hp), v, hvp, hvq⟩

/-- Murray–von Neumann equivalence is reflexive on star projections. -/
theorem refl [Fintype m] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv p := by
  refine ⟨hp, hp, p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

/-- Murray–von Neumann equivalence is symmetric. -/
theorem symm [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [InvolutiveStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    q.MurrayVonNeumannEquiv p := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  refine ⟨hq, hp, v.conjTranspose, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose, hvq]
  · rw [conjTranspose_conjTranspose, hvp]

/-- Murray–von Neumann equivalence is transitive across arbitrary finite matrix sizes. -/
theorem trans [Fintype l] [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hpq : p.MurrayVonNeumannEquiv q) (hqr : q.MurrayVonNeumannEquiv r) :
    p.MurrayVonNeumannEquiv r := by
  obtain ⟨hp, -, v, hvp, hvq⟩ := hpq
  obtain ⟨-, hr, w, hwq, hwr⟩ := hqr
  refine ⟨hp, hr, w * v, ?_, ?_⟩
  · calc (w * v).conjTranspose * (w * v)
        = v.conjTranspose * (w.conjTranspose * w) * v := by
          simp only [conjTranspose_mul, mul_assoc]
      _ = v.conjTranspose * (v * v.conjTranspose) * v := by rw [hwq, ← hvq]
      _ = (v.conjTranspose * v) * (v.conjTranspose * v) := by simp only [mul_assoc]
      _ = p := by rw [hvp, hp.isIdempotentElem.eq]
  · calc (w * v) * (w * v).conjTranspose
        = w * (v * v.conjTranspose) * w.conjTranspose := by
          simp only [conjTranspose_mul, mul_assoc]
      _ = w * (w.conjTranspose * w) * w.conjTranspose := by rw [hvq, ← hwq]
      _ = (w * w.conjTranspose) * (w * w.conjTranspose) := by simp only [mul_assoc]
      _ = r := by rw [hwr, hr.isIdempotentElem.eq]

/-- Zero matrices of any two finite sizes are Murray–von Neumann equivalent. -/
theorem zero [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquiv (0 : CStarMatrix n n A) :=
  ⟨IsStarProjection.zero _, IsStarProjection.zero _, 0, by simp, by simp⟩

/-- Murray–von Neumann equivalence is compatible with block-diagonal sums. -/
theorem fromBlocks [Fintype l] [Fintype m] [Fintype n] [Fintype k]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix l l A} {q₁ : CStarMatrix m m A}
    {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix k k A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.fromBlocks p₁ 0 0 p₂).MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks q₁ 0 0 q₂) := by
  obtain ⟨hp₁, hq₁, v₁, hv₁p, hv₁q⟩ := h₁
  obtain ⟨hp₂, hq₂, v₂, hv₂p, hv₂q⟩ := h₂
  refine ⟨isStarProjection_fromBlocks_diag.mpr ⟨hp₁, hp₂⟩,
    isStarProjection_fromBlocks_diag.mpr ⟨hq₁, hq₂⟩,
    CStarMatrix.fromBlocks v₁ 0 0 v₂, ?_, ?_⟩
  · simp [hv₁p, hv₂p]
  · simp [hv₁q, hv₂q]

/-- Murray–von Neumann equivalence is compatible with sums of orthogonal projections. -/
theorem add [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) := by
  obtain ⟨hp₁, hq₁, v₁, hv₁p, hv₁q⟩ := h₁
  obtain ⟨hp₂, hq₂, v₂, hv₂p, hv₂q⟩ := h₂
  have hp' : p₂ * p₁ = 0 := by
    simpa only [star_mul, star_zero, hp₁.isSelfAdjoint.star_eq,
      hp₂.isSelfAdjoint.star_eq] using congr_arg star hp
  have hq' : q₂ * q₁ = 0 := by
    simpa only [star_mul, star_zero, hq₁.isSelfAdjoint.star_eq,
      hq₂.isSelfAdjoint.star_eq] using congr_arg star hq
  obtain ⟨hv₁_r, hv₁_l, hv₁s_l, hv₁s_r⟩ := mul_proj_eq_of_conjTranspose_mul_eq hp₁ hv₁p hv₁q
  obtain ⟨hv₂_r, hv₂_l, hv₂s_l, hv₂s_r⟩ := mul_proj_eq_of_conjTranspose_mul_eq hp₂ hv₂p hv₂q
  have h12 : v₁.conjTranspose * v₂ = 0 := by
    calc v₁.conjTranspose * v₂ = (v₁.conjTranspose * q₁) * (q₂ * v₂) := by rw [hv₁s_r, hv₂_l]
      _ = v₁.conjTranspose * (q₁ * q₂) * v₂ := by simp only [mul_assoc]
      _ = 0 := by rw [hq, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h21 : v₂.conjTranspose * v₁ = 0 := by
    calc v₂.conjTranspose * v₁ = (v₂.conjTranspose * q₂) * (q₁ * v₁) := by rw [hv₂s_r, hv₁_l]
      _ = v₂.conjTranspose * (q₂ * q₁) * v₁ := by simp only [mul_assoc]
      _ = 0 := by rw [hq', CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h12' : v₁ * v₂.conjTranspose = 0 := by
    calc v₁ * v₂.conjTranspose = (v₁ * p₁) * (p₂ * v₂.conjTranspose) := by rw [hv₁_r, hv₂s_l]
      _ = v₁ * (p₁ * p₂) * v₂.conjTranspose := by simp only [mul_assoc]
      _ = 0 := by rw [hp, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h21' : v₂ * v₁.conjTranspose = 0 := by
    calc v₂ * v₁.conjTranspose = (v₂ * p₂) * (p₁ * v₁.conjTranspose) := by rw [hv₂_r, hv₁s_l]
      _ = v₂ * (p₂ * p₁) * v₁.conjTranspose := by simp only [mul_assoc]
      _ = 0 := by rw [hp', CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  refine ⟨hp₁.add hp₂ hp, hq₁.add hq₂ hq, v₁ + v₂, ?_, ?_⟩
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hv₁p, hv₂p, h12, h21, add_zero, zero_add]
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hv₁q, hv₂q, h12', h21', add_zero, zero_add]

/-- Every star projection is Murray–von Neumann equivalent to its upper-left corner embedding
`fromBlocks p 0 0 0`. -/
theorem cornerInl [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A)) := by
  let v : CStarMatrix (m ⊕ n) m A :=
    ofMatrix (Matrix.of fun i j => Sum.elim (fun i₁ => p i₁ j) (fun _ => 0) i)
  have hvl : ∀ i j, v (Sum.inl i) j = p i j := fun _ _ => rfl
  have hvr : ∀ i j, v (Sum.inr i) j = 0 := fun _ _ => rfl
  refine ⟨hp, isStarProjection_fromBlocks_diag.mpr ⟨hp, IsStarProjection.zero _⟩, v, ?_, ?_⟩
  · ext i j
    simp only [mul_apply, conjTranspose_apply, Fintype.sum_sum_type, hvl, hvr,
      star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hpp : star p * p = p := by
      rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    simpa [mul_apply, star_eq_conjTranspose, conjTranspose_apply] using
      congrFun (congrFun hpp i) j
  · have hpp : p * star p = p := by
      rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    ext (i | i) (j | j)
    · simp only [mul_apply, conjTranspose_apply, hvl, fromBlocks_apply₁₁]
      simpa [mul_apply, star_eq_conjTranspose, conjTranspose_apply] using
        congrFun (congrFun hpp i) j
    · simp [mul_apply, hvl, hvr]
    · simp [mul_apply, hvl, hvr]
    · simp [mul_apply, hvr]

/-- Every star projection is Murray–von Neumann equivalent to its lower-right corner embedding
`fromBlocks 0 0 0 q`. -/
theorem cornerInr [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q) := by
  let v : CStarMatrix (m ⊕ n) n A :=
    ofMatrix (Matrix.of fun i j => Sum.elim (fun _ => 0) (fun i₂ => q i₂ j) i)
  have hvl : ∀ i j, v (Sum.inl i) j = 0 := fun _ _ => rfl
  have hvr : ∀ i j, v (Sum.inr i) j = q i j := fun _ _ => rfl
  refine ⟨hq, isStarProjection_fromBlocks_diag.mpr ⟨IsStarProjection.zero _, hq⟩, v, ?_, ?_⟩
  · ext i j
    simp only [mul_apply, conjTranspose_apply, Fintype.sum_sum_type, hvl, hvr,
      star_zero, zero_mul, Finset.sum_const_zero, zero_add]
    have hqq : star q * q = q := by
      rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]
    simpa [mul_apply, star_eq_conjTranspose, conjTranspose_apply] using
      congrFun (congrFun hqq i) j
  · have hqq : q * star q = q := by
      rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]
    ext (i | i) (j | j)
    · simp [mul_apply, hvl]
    · simp [mul_apply, hvl, hvr]
    · simp [mul_apply, hvl, hvr]
    · simp only [mul_apply, conjTranspose_apply, hvr, fromBlocks_apply₂₂]
      simpa [mul_apply, star_eq_conjTranspose, conjTranspose_apply] using
        congrFun (congrFun hqq i) j

/-- Reindexing a star projection along any equivalence `e : m ≃ n` produces a Murray–von Neumann
equivalent projection, without assuming `A` is unital. -/
theorem reindex [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Star A] (e : m ≃ n) {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (reindexₐ R A e p) := by
  let v : CStarMatrix n m A := ofMatrix (Matrix.of fun i j => p (e.symm i) j)
  have hv : ∀ i j, v i j = p (e.symm i) j := fun _ _ => rfl
  refine ⟨hp, hp.map (reindexₐ R A e), v, ?_, ?_⟩
  · ext i j
    simp only [mul_apply, conjTranspose_apply, hv]
    have hsum : ∑ k : n, star (p (e.symm k) i) * p (e.symm k) j =
        ∑ k : m, star (p k i) * p k j :=
      Fintype.sum_equiv e.symm _ _ fun _ => rfl
    rw [hsum]
    have hpp : star p * p = p := by
      rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    simpa [mul_apply, star_eq_conjTranspose, conjTranspose_apply] using
      congrFun (congrFun hpp i) j
  · ext i j
    have hpp : p * star p = p := by
      rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    have hval : (reindexₐ R A e p) i j = p (e.symm i) (e.symm j) := by
      rw [reindexₐ_apply]
      rfl
    rw [mul_apply, hval]
    simpa [mul_apply, star_eq_conjTranspose, conjTranspose_apply, hv] using
      congrFun (congrFun hpp (e.symm i)) (e.symm j)

/-- Block-diagonal sums of star projections are commutative up to Murray–von Neumann
equivalence. -/
theorem fromBlocks_comm [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (CStarMatrix.fromBlocks p 0 0 q).MurrayVonNeumannEquiv (CStarMatrix.fromBlocks q 0 0 p) := by
  rw [← reindexₐ_sumComm_fromBlocks (R := ℕ) p q]
  exact reindex (R := ℕ) (Equiv.sumComm m n) (isStarProjection_fromBlocks_diag.mpr ⟨hp, hq⟩)

/-- Block-diagonal sums of star projections are associative up to Murray–von Neumann
equivalence. -/
theorem fromBlocks_assoc [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r) :
    (CStarMatrix.fromBlocks (CStarMatrix.fromBlocks p 0 0 q) 0 0 r).MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks p 0 0 (CStarMatrix.fromBlocks q 0 0 r)) := by
  rw [← reindexₐ_sumAssoc_fromBlocks (R := ℕ) p q r]
  exact reindex (R := ℕ) (Equiv.sumAssoc l m n)
    (isStarProjection_fromBlocks_diag.mpr ⟨isStarProjection_fromBlocks_diag.mpr ⟨hp, hq⟩, hr⟩)

/-- Non-unital ⋆-algebra homomorphisms preserve Murray–von Neumann equivalence of matrix
projections. -/
theorem mapₙₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (f : A →⋆ₙₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₙₐ f p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ f q) := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  refine ⟨hp.map (CStarMatrix.mapₙₐ f), hq.map (CStarMatrix.mapₙₐ f), v.map f, ?_, ?_⟩
  · rw [conjTranspose_map f v, ← CStarMatrix.map_mul f v.conjTranspose v, hvp]
    rfl
  · rw [conjTranspose_map f v, ← CStarMatrix.map_mul f v v.conjTranspose, hvq]
    rfl

/-- Unital ⋆-algebra homomorphisms preserve Murray–von Neumann equivalence of matrix
projections. -/
theorem mapₐ [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₐ f p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ f q) := by
  rw [mapₐ_eq_mapₙₐ, mapₐ_eq_mapₙₐ]
  exact h.mapₙₐ f.toNonUnitalStarAlgHom

/-- Unitarily conjugate star projections in a unital matrix ring are Murray–von Neumann
equivalent. -/
theorem of_unitary_conj [Fintype m] [DecidableEq m] [Semiring A] [StarRing A]
    {p q : CStarMatrix m m A} (hp : IsStarProjection p)
    {u : unitary (CStarMatrix m m A)}
    (hconj : (u : CStarMatrix m m A) * p * star (u : CStarMatrix m m A) = q) :
    p.MurrayVonNeumannEquiv q := by
  refine ⟨hp, hconj ▸ hp.unitaryConj u, (u : CStarMatrix m m A) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq, _root_.mul_assoc,
      ← _root_.mul_assoc (star (u : CStarMatrix m m A)), Unitary.star_mul_self_of_mem u.property,
      _root_.one_mul, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq, ← _root_.mul_assoc,
      _root_.mul_assoc (u : CStarMatrix m m A), hp.isIdempotentElem.eq, hconj]

/-- Star projections conjugate by a unitary in `Unitization R (CStarMatrix m m A)` are
Murray–von Neumann equivalent. -/
theorem of_unitization_unitary_conj [Fintype m] [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] {p q : CStarMatrix m m A} (hp : IsStarProjection p)
    {u : unitary (Unitization R (CStarMatrix m m A))}
    (hconj : (u : Unitization R (CStarMatrix m m A)) *
        (p : Unitization R (CStarMatrix m m A)) *
        star (u : Unitization R (CStarMatrix m m A)) =
      (q : Unitization R (CStarMatrix m m A))) :
    p.MurrayVonNeumannEquiv q := by
  obtain ⟨v, hv, hvp, hvq⟩ := hp.exists_isPartialIsometry_of_unitization_unitary_conj hconj
  exact ⟨hp, hvq ▸ hv.isStarProjection_mul_star_self, v, hvp, hvq⟩

end MurrayVonNeumannEquiv

end MurrayVonNeumannDef

section CStarEquivalence

variable {m n A : Type*}

/-- For square matrices over a star-ordered ring with proper star, Murray–von Neumann equivalence
is equivalent to the existence of a partial isometry (`TauCeti.IsPartialIsometry`) with initial
projection `p` and final projection `q`. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry [Fintype m]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p q : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix m m A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  constructor
  · rintro ⟨hp, -, v, hvp, hvq⟩
    refine ⟨v, ?_, hvp, hvq⟩
    rw [TauCeti.isPartialIsometry_iff, star_eq_conjTranspose]
    exact mul_conjTranspose_mul_self_of_isStarProjection (hvp ▸ hp)
  · rintro ⟨v, hv, hvp, hvq⟩
    exact ⟨hvp ▸ hv.isStarProjection_star_mul_self, hvq ▸ hv.isStarProjection_mul_star_self,
      v, hvp, hvq⟩

namespace MurrayVonNeumannEquiv

/-- Rectangular algebraic equivalence of star projections implies Murray–von Neumann equivalence:
if `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are star projections and `x * y = p`,
`y * x = q` for rectangular matrices `x, y`, then `p` and `q` are Murray–von Neumann equivalent
(Blackadar, Proposition 4.6.4). -/
theorem of_mul_eq [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n A} {y : CStarMatrix n m A} (hxy : x * y = p) (hyx : y * x = q) :
    p.MurrayVonNeumannEquiv q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let P : CStarMatrix (m ⊕ n) (m ⊕ n) A := CStarMatrix.fromBlocks p 0 0 0
  let Q : CStarMatrix (m ⊕ n) (m ⊕ n) A := CStarMatrix.fromBlocks 0 0 0 q
  let X : CStarMatrix (m ⊕ n) (m ⊕ n) A := CStarMatrix.fromBlocks 0 x 0 0
  let Y : CStarMatrix (m ⊕ n) (m ⊕ n) A := CStarMatrix.fromBlocks 0 0 y 0
  have hP : IsStarProjection P :=
    isStarProjection_fromBlocks_diag.mpr ⟨hp, IsStarProjection.zero _⟩
  have hQ : IsStarProjection Q :=
    isStarProjection_fromBlocks_diag.mpr ⟨IsStarProjection.zero _, hq⟩
  have hXY : X * Y = P := by simp [X, Y, P, hxy]
  have hYX : Y * X = Q := by simp [X, Y, Q, hyx]
  obtain ⟨V, hV, hVP, hVQ⟩ := hP.exists_isPartialIsometry_of_mul_eq hQ hXY hYX
  let v : CStarMatrix n m A := ofMatrix (Matrix.of fun i j => V (Sum.inr i) (Sum.inl j))
  have hV_eq : V = CStarMatrix.fromBlocks 0 0 v 0 := by
    have hQV : Q * V = V := by rw [← hVQ, hV.mul_star_mul_self]
    have hVP' : V * P = V := by rw [← hVP, ← _root_.mul_assoc, hV.mul_star_mul_self]
    have hQVP : Q * V * P = V := by rw [hQV, hVP']
    ext (i | i) (j | j)
    · rw [← hQVP]
      simp [Q, P, mul_apply, Fintype.sum_sum_type]
    · rw [← hQVP]
      simp [Q, P, mul_apply, Fintype.sum_sum_type]
    · simp [v]
    · rw [← hQVP]
      simp [Q, P, mul_apply, Fintype.sum_sum_type]
  rw [hV_eq] at hVP hVQ
  simp only [fromBlocks_star, conjTranspose_zero, fromBlocks_multiply, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, P, Q, fromBlocks_inj] at hVP hVQ
  exact ⟨hp, hq, v, hVP.1, hVQ.2.2.2⟩

/-- Star projections in `CStarMatrix m m A` at distance `< 1` are Murray–von Neumann equivalent. -/
theorem of_norm_sub_lt_one [Fintype m] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix m m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hnorm : ‖p - q‖ < 1) :
    p.MurrayVonNeumannEquiv q :=
  murrayVonNeumannEquiv_iff_exists_isPartialIsometry.mpr
    (hp.exists_isPartialIsometry_of_norm_sub_lt_one hq hnorm)

/-- Endpoints of a norm-continuous path of star projections in `CStarMatrix m m A` are Murray–von
Neumann equivalent. -/
theorem of_continuous_path [Fintype m] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {γ : I → CStarMatrix m m A} (hγ : Continuous γ) (hproj : ∀ t : I, IsStarProjection (γ t)) :
    (γ 0).MurrayVonNeumannEquiv (γ 1) :=
  murrayVonNeumannEquiv_iff_exists_isPartialIsometry.mpr
    (IsStarProjection.exists_isPartialIsometry_of_continuous_path hγ hproj)

end MurrayVonNeumannEquiv

end CStarEquivalence

section StabilizedConjugacy

variable {m n A : Type*}

/-- The self-adjoint block reflection unitary `[[1 - p, vᴴ], [v, 1 - q]]` associated to a
rectangular partial isometry `v` with `vᴴ * v = p`, `v * vᴴ = q`, and `v * p = v`. -/
def stabilizedReflectionUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    have hp_star : p.conjTranspose = p := by
      rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
    have hq_star : q.conjTranspose = q := by
      rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
    have hpv' : p * v.conjTranspose = v.conjTranspose := by
      have := congr_arg conjTranspose hvp'
      simpa only [conjTranspose_mul, hp_star] using this
    have hsa : star (fromBlocks (1 - p) v.conjTranspose v (1 - q)) =
        fromBlocks (1 - p) v.conjTranspose v (1 - q) := by
      rw [fromBlocks_star]
      simp only [conjTranspose_conjTranspose, star_sub, star_one, star_eq_conjTranspose,
        hp_star, hq_star]
    have hsq : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
        fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
      apply ofMatrix.symm.injective
      rw [ofMatrix_symm_hMul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_sub,
        ofMatrix_symm_one, ofMatrix_symm_one, ofMatrix_symm_one]
      exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq
        (a := ofMatrix.symm v.conjTranspose) (b := ofMatrix.symm v)
        (e := ofMatrix.symm p) (f := ofMatrix.symm q)
        (congr_arg ofMatrix.symm hvp) (congr_arg ofMatrix.symm hvq)
        (congr_arg ofMatrix.symm hpv') (congr_arg ofMatrix.symm hvp')
    rw [Unitary.mem_iff, hsa, hsq]
    exact ⟨rfl, rfl⟩⟩

@[simp]
theorem coe_stabilizedReflectionUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    (stabilizedReflectionUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)

theorem isSelfAdjoint_stabilizedReflectionUnitary [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    IsSelfAdjoint (stabilizedReflectionUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hp_star : p.conjTranspose = p := by
    rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hq_star : q.conjTranspose = q := by
    rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [IsSelfAdjoint, coe_stabilizedReflectionUnitary, fromBlocks_star]
  simp only [conjTranspose_conjTranspose, star_sub, star_one, star_eq_conjTranspose,
    hp_star, hq_star]

/-- The block reflection unitary `[[1 - p, vᴴ], [v, 1 - q]]` conjugates `p ⊕ 0` to `0 ⊕ q`. -/
theorem stabilizedReflectionUnitary_conj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    (stabilizedReflectionUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedReflectionUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  rw [(isSelfAdjoint_stabilizedReflectionUnitary hvp hvq hvp').star_eq,
    coe_stabilizedReflectionUnitary]
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_hMul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_one,
    ofMatrix_symm_zero]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (a := ofMatrix.symm v.conjTranspose) (b := ofMatrix.symm v)
    (e := ofMatrix.symm p) (f := ofMatrix.symm q)
    (congr_arg ofMatrix.symm hvp) (congr_arg ofMatrix.symm hvq) (congr_arg ofMatrix.symm hvp')

/-- The block rotation unitary `[[1 - p, -vᴴ], [v, 1 - q]]` conjugating `p ⊕ 0` to `0 ⊕ q`. -/
def stabilizedRotationUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) (-v.conjTranspose) v (1 - q), by
    have hp_star : p.conjTranspose = p := by
      rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
    have hq_star : q.conjTranspose = q := by
      rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
    have hpv' : p * v.conjTranspose = v.conjTranspose := by
      have := congr_arg conjTranspose hvp'
      simpa only [conjTranspose_mul, hp_star] using this
    have hvq' : q * v = v := by rw [← hvq, mul_assoc, hvp, hvp']
    have hqv' : v.conjTranspose * q = v.conjTranspose := by
      have := congr_arg conjTranspose hvq'
      simpa only [conjTranspose_mul, hq_star] using this
    have hpp : p * p = p := by nth_rw 1 [← hvp]; rw [mul_assoc, hvp', hvp]
    have hqq : q * q = q := by nth_rw 1 [← hvq]; rw [mul_assoc, hqv', hvq]
    rw [Unitary.mem_iff, fromBlocks_star, conjTranspose_neg, conjTranspose_conjTranspose]
    simp only [star_sub, star_one, star_eq_conjTranspose, hp_star, hq_star, fromBlocks_multiply,
      ← fromBlocks_one, fromBlocks_inj, CStarMatrix.sub_mul, CStarMatrix.mul_sub,
      CStarMatrix.one_mul, CStarMatrix.mul_one, CStarMatrix.neg_mul, CStarMatrix.mul_neg,
      hvp, hvq, hvp', hpv', hvq', hqv', hpp, hqq]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> abel⟩

@[simp]
theorem coe_stabilizedRotationUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    (stabilizedRotationUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) (-v.conjTranspose) v (1 - q) := (rfl)

/-- The block rotation unitary `[[1 - p, -vᴴ], [v, 1 - q]]` conjugates `p ⊕ 0` to `0 ⊕ q`. -/
theorem stabilizedRotationUnitary_conj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hvp' : v * p = v) :
    (stabilizedRotationUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedRotationUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  have hp_star : p.conjTranspose = p := by
    rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hq_star : q.conjTranspose = q := by
    rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  have hpp : p * p = p := by nth_rw 1 [← hvp]; rw [mul_assoc, hvp', hvp]
  rw [coe_stabilizedRotationUnitary, fromBlocks_star, conjTranspose_neg,
    conjTranspose_conjTranspose]
  simp only [star_sub, star_one, star_eq_conjTranspose, hp_star, hq_star, fromBlocks_multiply,
    CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.one_mul, CStarMatrix.mul_one,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, CStarMatrix.mul_neg,
    hpp, hvp', hvq, sub_self, neg_zero, add_zero]

/-- The explicit exponential unitary path from `1` to `stabilizedReflectionUnitary`. -/
noncomputable def stabilizedReflectionPath [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hvp' : v * p = v) :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A))
      (stabilizedReflectionUnitary hvp hvq hvp') :=
  Unitary.selfAdjointExpPath (stabilizedReflectionUnitary hvp hvq hvp')
    (isSelfAdjoint_stabilizedReflectionUnitary hvp hvq hvp')

/-- At the midpoint `t = 1/2`, conjugating `p ⊕ 0` along `stabilizedReflectionPath` yields the
projection `[[(1/2) • p, (i/2) • vᴴ], [(-i/2) • v, (1/2) • q]]`. -/
theorem stabilizedReflectionPath_conj_half [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hvp' : v * p = v) :
    Unitary.conjPath (fromBlocks p 0 0 0) (stabilizedReflectionPath hvp hvq hvp')
        ⟨1 / 2, by norm_num, by norm_num⟩ =
      fromBlocks (((1 : ℂ) / 2) • p) ((Complex.I / 2) • v.conjTranspose)
        ((-Complex.I / 2) • v) (((1 : ℂ) / 2) • q) := by
  have hp_star : p.conjTranspose = p := by
    rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hq_star : q.conjTranspose = q := by
    rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  have hpv' : p * v.conjTranspose = v.conjTranspose := by
    have := congr_arg conjTranspose hvp'
    simpa only [conjTranspose_mul, hp_star] using this
  have hpp : p * p = p := by nth_rw 1 [← hvp]; rw [mul_assoc, hvp', hvp]
  let c : ℂ := (Complex.I - 1) * (2 : ℂ)⁻¹
  have hu : ((stabilizedReflectionPath hvp hvq hvp' ⟨1 / 2, by norm_num, by norm_num⟩ :
        unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 + c • p) ((-c) • v.conjTranspose) ((-c) • v) (1 + c • q) := by
    have hexp : Complex.exp (Complex.I * (((1 / 2 : ℝ) : ℂ) * Real.pi)) = Complex.I := by
      have harg : Complex.I * (((1 / 2 : ℝ) : ℂ) * Real.pi) = Real.pi / 2 * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_pi_div_two_mul_I]
    rw [stabilizedReflectionPath, Unitary.coe_selfAdjointExpPath, hexp,
      coe_stabilizedReflectionUnitary, ← fromBlocks_one, fromBlocks_sub]
    simp only [sub_sub_cancel, zero_sub, zero_add, fromBlocks_smul, fromBlocks_add, smul_smul,
      smul_neg, neg_smul, c]
  have hsu : star (fromBlocks (1 + c • p) ((-c) • v.conjTranspose) ((-c) • v) (1 + c • q)) =
      fromBlocks (1 + star c • p) ((-star c) • v.conjTranspose)
        ((-star c) • v) (1 + star c • q) := by
    rw [fromBlocks_star]
    simp only [star_add, star_one, star_smul, star_eq_conjTranspose, hp_star, hq_star,
      conjTranspose_smul, conjTranspose_conjTranspose, star_neg]
  have hleft : fromBlocks (1 + c • p) ((-c) • v.conjTranspose) ((-c) • v) (1 + c • q) *
      fromBlocks p 0 0 0 =
      fromBlocks ((1 + c) • p) 0 ((-c) • v) 0 := by
    simp only [fromBlocks_multiply, CStarMatrix.mul_zero, add_zero,
      CStarMatrix.add_mul, CStarMatrix.one_mul, CStarMatrix.smul_mul, hpp, hvp', add_smul,
      one_smul]
  have h11 : 1 + c + star c * (1 + c) = (1 : ℂ) / 2 := by
    apply Complex.ext <;> simp [c] <;> norm_num
  have h12 : -star c * (1 + c) = Complex.I / 2 := by
    apply Complex.ext <;> simp [c] <;> norm_num
  have h21 : -c + star c * -c = -Complex.I / 2 := by
    apply Complex.ext <;> simp [c] <;> norm_num
  have h22 : -star c * -c = (1 : ℂ) / 2 := by
    apply Complex.ext <;> simp [c] ; norm_num
  rw [Unitary.conjPath_apply, hu, hleft, hsu, fromBlocks_multiply]
  simp only [CStarMatrix.zero_mul, CStarMatrix.mul_add, CStarMatrix.mul_one, CStarMatrix.smul_mul,
    CStarMatrix.mul_smul, hpp, hvp', hpv', hvq, smul_smul, smul_zero, add_zero, ← add_smul,
    h11, h12, h21, h22]

/-- For `p = q = 1` in `CStarMatrix (Fin 1) (Fin 1) ℂ` and `v = 1`, the midpoint of
`stabilizedReflectionPath` is `[[1/2, i/2], [-i/2, 1/2]]`. -/
theorem stabilizedReflectionPath_one_conj_half :
    Unitary.conjPath
        (fromBlocks (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) 0 0
          (0 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        (stabilizedReflectionPath (m := Fin 1) (n := Fin 1) (A := ℂ)
          (p := 1) (q := 1) (v := 1) (by simp) (by simp) (by simp))
        ⟨1 / 2, by norm_num, by norm_num⟩ =
      fromBlocks (((1 : ℂ) / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        ((Complex.I / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        ((-Complex.I / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        (((1 : ℂ) / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ)) := by
  simpa only [conjTranspose_one] using
    stabilizedReflectionPath_conj_half (m := Fin 1) (n := Fin 1) (A := ℂ)
      (p := 1) (q := 1) (v := 1) (by simp) (by simp) (by simp)

namespace MurrayVonNeumannEquiv

/-- In a (possibly non-unital) C⋆-algebra, Murray–von Neumann equivalent matrix projections `p`
and `q` become conjugate after stabilization by a unitary in the identity component of
`(CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹`. -/
theorem exists_stabilized_unitization_unitary_conj [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹,
      (u : (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) *
          (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A) :
            (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) *
          star (u : (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) =
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q :
          (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) ∧
        Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) u := by
  obtain ⟨hp, -, v, hvp, hvq⟩ := h
  let B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  let V : B := CStarMatrix.fromBlocks 0 0 v 0
  have hVP : star V * V = CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A) := by
    dsimp only [V, B]
    rw [fromBlocks_star]
    simp [hvp]
  have hVQ : V * star V = CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q := by
    dsimp only [V, B]
    rw [fromBlocks_star]
    simp [hvq]
  have hV_pi : TauCeti.IsPartialIsometry V := by
    rw [TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self, hVP]
    exact isStarProjection_fromBlocks_diag.mpr ⟨hp, IsStarProjection.zero _⟩
  let V' : B⁺¹ := (V : B⁺¹)
  have hV'_pi : TauCeti.IsPartialIsometry V' := by
    rw [TauCeti.isPartialIsometry_iff, ← Unitization.inr_star, ← Unitization.inr_mul,
      ← Unitization.inr_mul, hV_pi.mul_star_mul_self]
  have hV'_init :
      star V' * V' = ((CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A) : B) : B⁺¹) := by
    rw [← Unitization.inr_star, ← Unitization.inr_mul, hVP]
  have hV'_final :
      V' * star V' = ((CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q : B) : B⁺¹) := by
    rw [← Unitization.inr_star, ← Unitization.inr_mul, hVQ]
  have horth : (star V' * V') * (V' * star V') = 0 := by
    rw [hV'_init, hV'_final, ← Unitization.inr_mul]
    simp [B]
  let w : unitary B⁺¹ := hV'_pi.reflectionUnitary horth
  refine ⟨w, ?_, ⟨Unitary.selfAdjointExpPath w (hV'_pi.isSelfAdjoint_reflectionUnitary horth)⟩⟩
  rw [← hV'_init, ← hV'_final]
  exact hV'_pi.reflectionUnitary_conj horth

/-- In a (possibly non-unital) C⋆-algebra, Murray–von Neumann equivalent matrix projections `p` and
`q` are joined after stabilization by a continuous path of star projections from `p ⊕ 0` to
`0 ⊕ q`. -/
theorem exists_stabilized_path [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨u, hconj, ⟨γu⟩⟩ := h.exists_stabilized_unitization_unitary_conj
  have hP : IsStarProjection (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_diag.mpr ⟨h.isStarProjection_left, IsStarProjection.zero _⟩
  have htarget :
      CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q =
        ((u : (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) *
            (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A) :
              (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹) *
            star (u : (CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹)).snd := by
    rw [hconj]
    rfl
  refine ⟨(Unitary.unitizationConjPath (CStarMatrix.fromBlocks p 0 0 0) γu).cast rfl htarget,
    fun t => ?_⟩
  exact hP.isStarProjection_unitizationConjPath γu t

/-- For same-size Murray–von Neumann equivalent matrix projections `p, q : CStarMatrix m m A` over
a (possibly non-unital) C⋆-algebra, `p ⊕ 0` and `q ⊕ 0` are joined by a continuous path of star
projections in `CStarMatrix (m ⊕ m) (m ⊕ m) A`. -/
theorem exists_stabilized_path_left [Fintype m]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix m m A))
        (CStarMatrix.fromBlocks q 0 0 (0 : CStarMatrix m m A)),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨γ₁, hγ₁⟩ := h.exists_stabilized_path
  obtain ⟨γ₂, hγ₂⟩ := (refl h.isStarProjection_right).exists_stabilized_path
  refine ⟨γ₁.trans γ₂.symm, fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs
  · exact hγ₁ _
  · exact hγ₂ _

/-- In a unital C⋆-algebra, Murray–von Neumann equivalent matrix projections `p` and `q` satisfy
that `p ⊕ 0` and `0 ⊕ q` are conjugate by a unitary in the identity component of
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem exists_stabilized_unitary_conj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * CStarMatrix.fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = CStarMatrix.fromBlocks 0 0 0 q ∧
        Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) u := by
  obtain ⟨hp, -, v, hvp, hvq⟩ := h
  have hvp' : v * p = v := by
    rw [← hvp, ← mul_assoc]
    exact mul_conjTranspose_mul_self_of_isStarProjection (hvp ▸ hp)
  exact ⟨stabilizedReflectionUnitary hvp hvq hvp',
    stabilizedReflectionUnitary_conj hvp hvq hvp',
    ⟨stabilizedReflectionPath hvp hvq hvp'⟩⟩

/-- In a unital C⋆-algebra, same-size Murray–von Neumann equivalent projections `p` and `q` satisfy
that `p ⊕ 0` and `q ⊕ 0` are conjugate by a unitary in the identity component of
`unitary (CStarMatrix (m ⊕ m) (m ⊕ m) A)`. -/
theorem exists_stabilized_unitary_conj_left [Fintype m] [DecidableEq m]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (m ⊕ m) (m ⊕ m) A),
      (u : CStarMatrix (m ⊕ m) (m ⊕ m) A) * CStarMatrix.fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ m) (m ⊕ m) A) = CStarMatrix.fromBlocks q 0 0 0 ∧
        Joined (1 : unitary (CStarMatrix (m ⊕ m) (m ⊕ m) A)) u := by
  let B := CStarMatrix (m ⊕ m) (m ⊕ m) A
  obtain ⟨u₁, hu₁, hjoin₁⟩ := h.exists_stabilized_unitary_conj
  have hq : IsStarProjection q := h.isStarProjection_right
  have hqq : q.conjTranspose * q = q := by
    rw [← star_eq_conjTranspose, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]
  have hqq' : q * q.conjTranspose = q := by
    rw [← star_eq_conjTranspose, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]
  let w₂ : unitary B := stabilizedReflectionUnitary hqq hqq' hq.isIdempotentElem.eq
  have hw₂_sa : IsSelfAdjoint (w₂ : B) :=
    isSelfAdjoint_stabilizedReflectionUnitary hqq hqq' hq.isIdempotentElem.eq
  have hw₂_sq : (w₂ : B) * (w₂ : B) = 1 := by
    simpa only [hw₂_sa.star_eq] using Unitary.star_mul_self_of_mem w₂.property
  have hw₂_conj : (w₂ : B) * CStarMatrix.fromBlocks 0 0 0 q * star (w₂ : B) =
      CStarMatrix.fromBlocks q 0 0 0 := by
    have h1 : (w₂ : B) * CStarMatrix.fromBlocks q 0 0 0 * star (w₂ : B) =
        CStarMatrix.fromBlocks 0 0 0 q :=
      stabilizedReflectionUnitary_conj hqq hqq' hq.isIdempotentElem.eq
    rw [← h1, hw₂_sa.star_eq]
    calc (w₂ : B) * ((w₂ : B) * CStarMatrix.fromBlocks q 0 0 0 * (w₂ : B)) * (w₂ : B)
        = ((w₂ : B) * (w₂ : B)) * CStarMatrix.fromBlocks q 0 0 0 * ((w₂ : B) * (w₂ : B)) := by
          simp only [_root_.mul_assoc]
      _ = CStarMatrix.fromBlocks q 0 0 0 := by rw [hw₂_sq, _root_.one_mul, _root_.mul_one]
  refine ⟨w₂ * u₁, ?_, ?_⟩
  · calc ((w₂ * u₁ : unitary B) : B) * CStarMatrix.fromBlocks p 0 0 0 *
            star ((w₂ * u₁ : unitary B) : B)
        = (w₂ : B) * ((u₁ : B) * CStarMatrix.fromBlocks p 0 0 0 * star (u₁ : B)) *
            star (w₂ : B) := by simp only [Submonoid.coe_mul, star_mul, _root_.mul_assoc]
      _ = (w₂ : B) * CStarMatrix.fromBlocks 0 0 0 q * star (w₂ : B) := by rw [hu₁]
      _ = CStarMatrix.fromBlocks q 0 0 0 := hw₂_conj
  · have hjoin₂ : Joined (1 : unitary B) w₂ :=
      ⟨stabilizedReflectionPath hqq hqq' hq.isIdempotentElem.eq⟩
    simpa using hjoin₂.mul hjoin₁

end MurrayVonNeumannEquiv

end StabilizedConjugacy

end CStarMatrix
