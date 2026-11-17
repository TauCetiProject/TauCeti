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
`CStarMatrix` over (possibly non-unital) complex C⋆-algebras:

* `CStarMatrix.mul_conjTranspose_mul_self_of_isStarProjection`: rectangular partial-isometry
  identities (`v * vᴴ * v = v` and `IsStarProjection (v * vᴴ)` when `vᴴ * v` is a projection).
* `CStarMatrix.MurrayVonNeumannEquiv`: rectangular Murray–von Neumann equivalence (reflexivity,
  symmetry, transitivity, block-diagonal/orthogonal sums, corners, reindexing, functoriality,
  unitary conjugacy) and its identification with `TauCeti.IsPartialIsometry` for square matrices.
* `CStarMatrix.MurrayVonNeumannEquiv.of_mul_eq`, `of_norm_sub_lt_one`, `of_continuous_path`:
  implications from rectangular algebraic equivalence, `‖p - q‖ < 1`, and continuous paths.
* `CStarMatrix.stabilizedReflectionUnitary`, `CStarMatrix.stabilizedRotationUnitary`,
  `CStarMatrix.stabilizedReflectionPath_conj_half`, `exists_stabilized_path`, and
  `exists_stabilized_path_left`: explicit stabilized unitaries, midpoint evaluation at `t = 1/2`,
  and non-unital/unital stabilized paths from `p ⊕ 0` to `0 ⊕ q` and to `q ⊕ 0`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Chapter III, §4.6 (Definition 4.6.1 and
  Propositions 4.6.2–4.6.6).
-/

public section

open scoped ComplexOrder CStarAlgebra unitInterval

namespace CStarMatrix

section RectangularPartialIsometry

variable {m n A : Type*} [Fintype m] [Fintype n]
  [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]

/-- If `v.conjTranspose * v` is a star projection for a rectangular C⋆-matrix `v` over a
star-ordered ring with proper star, then `v * v.conjTranspose * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isStarProjection {v : CStarMatrix n m A}
    (hv : IsStarProjection (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  have hidem : v.conjTranspose * (v * (v.conjTranspose * v)) = v.conjTranspose * v := by
    simpa only [mul_assoc] using hv.1.eq
  have hzero : (v - v * (v.conjTranspose * v)).conjTranspose *
      (v - v * (v.conjTranspose * v)) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
      CStarMatrix.sub_mul, CStarMatrix.mul_sub, mul_assoc, hidem]; abel
  rw [mul_assoc]
  exact (sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hzero)).symm

/-- If `v.conjTranspose * v` is a star projection for a rectangular C⋆-matrix `v`, then
`v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_mul_conjTranspose_of_isStarProjection {v : CStarMatrix n m A}
    (hv : IsStarProjection (v.conjTranspose * v)) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc] using
    congr_arg conjTranspose (mul_conjTranspose_mul_self_of_isStarProjection hv)

/-- If `v.conjTranspose * v` is a star projection for a rectangular C⋆-matrix `v` over a
star-ordered ring with proper star, then `v * v.conjTranspose` is also a star projection. -/
theorem isStarProjection_mul_conjTranspose_of_conjTranspose_mul {v : CStarMatrix n m A}
    (hv : IsStarProjection (v.conjTranspose * v)) :
    IsStarProjection (v * v.conjTranspose) where
  isIdempotentElem := by
    rw [IsIdempotentElem, ← mul_assoc, mul_conjTranspose_mul_self_of_isStarProjection hv]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

private theorem mul_proj_eq_of_conjTranspose_mul_eq {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    v * p = v ∧ q * v = v ∧ p * v.conjTranspose = v.conjTranspose ∧
      v.conjTranspose * q = v.conjTranspose := by
  have hv : v * v.conjTranspose * v = v := mul_conjTranspose_mul_self_of_isStarProjection (hvp ▸ hp)
  have hvp' : v * p = v := by rw [← hvp, ← mul_assoc, hv]
  have hqv' : q * v = v := by rw [← hvq, hv]
  have hq_star : q.conjTranspose = q := by
    rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  exact ⟨hvp', hqv',
    by simpa only [conjTranspose_mul, ← star_eq_conjTranspose, hp.2.star_eq] using
      congr_arg conjTranspose hvp',
    by simpa only [conjTranspose_mul, hq_star] using congr_arg conjTranspose hqv'⟩

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

private theorem sum_star_mul_proj [Fintype m] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) (i j : m) :
    (∑ k, star (p k i) * p k j) = p i j ∧ (∑ k, p i k * star (p j k)) = p i j := by
  have h1 : star p * p = p := by rw [hp.2.star_eq, hp.1.eq]
  have h2 : p * star p = p := by rw [hp.2.star_eq, hp.1.eq]
  exact ⟨by simpa [mul_apply, star_eq_conjTranspose] using congrFun (congrFun h1 i) j,
    by simpa [mul_apply, star_eq_conjTranspose] using congrFun (congrFun h2 i) j⟩

theorem MurrayVonNeumannEquiv.isStarProjection_left [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection p := h.1

theorem MurrayVonNeumannEquiv.isStarProjection_right [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection q := h.2.1

/-- Construct a Murray–von Neumann equivalence over a star-ordered ring with proper star from
`vᴴ * v = p` and `v * vᴴ = q` assuming only that `p` is a star projection. -/
theorem MurrayVonNeumannEquiv.of_conjTranspose_mul_eq [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsStarProjection p)
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    p.MurrayVonNeumannEquiv q :=
  ⟨hp, hvq ▸ isStarProjection_mul_conjTranspose_of_conjTranspose_mul (hvp ▸ hp), v, hvp, hvq⟩

/-- Murray–von Neumann equivalence is reflexive on star projections. -/
theorem MurrayVonNeumannEquiv.refl [Fintype m] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv p :=
  ⟨hp, hp, p, by rw [← star_eq_conjTranspose, hp.2.star_eq, hp.1.eq],
    by rw [← star_eq_conjTranspose, hp.2.star_eq, hp.1.eq]⟩

/-- Murray–von Neumann equivalence is symmetric. -/
theorem MurrayVonNeumannEquiv.symm [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [InvolutiveStar A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : q.MurrayVonNeumannEquiv p := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  exact ⟨hq, hp, v.conjTranspose, by rw [conjTranspose_conjTranspose, hvq],
    by rw [conjTranspose_conjTranspose, hvp]⟩

/-- Murray–von Neumann equivalence is transitive across arbitrary finite matrix sizes. -/
theorem MurrayVonNeumannEquiv.trans [Fintype l] [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hpq : p.MurrayVonNeumannEquiv q) (hqr : q.MurrayVonNeumannEquiv r) :
    p.MurrayVonNeumannEquiv r := by
  obtain ⟨hp, -, v, hvp, hvq⟩ := hpq
  obtain ⟨-, hr, w, hwq, hwr⟩ := hqr
  refine ⟨hp, hr, w * v, ?_, ?_⟩
  · calc (w * v).conjTranspose * (w * v)
        = v.conjTranspose * (w.conjTranspose * w) * v := by simp only [conjTranspose_mul, mul_assoc]
      _ = (v.conjTranspose * v) * (v.conjTranspose * v) := by rw [hwq, ← hvq]; simp only [mul_assoc]
      _ = p := by rw [hvp, hp.1.eq]
  · calc (w * v) * (w * v).conjTranspose
        = w * (v * v.conjTranspose) * w.conjTranspose := by simp only [conjTranspose_mul, mul_assoc]
      _ = (w * w.conjTranspose) * (w * w.conjTranspose) := by rw [hvq, ← hwq]; simp only [mul_assoc]
      _ = r := by rw [hwr, hr.1.eq]

/-- Zero matrices of any two finite sizes are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.zero [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] : (0 : CStarMatrix m m A).MurrayVonNeumannEquiv (0 : CStarMatrix n n A) :=
  ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- Murray–von Neumann equivalence is compatible with block-diagonal sums. -/
theorem MurrayVonNeumannEquiv.fromBlocks [Fintype l] [Fintype m] [Fintype n] [Fintype k]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix l l A} {q₁ : CStarMatrix m m A}
    {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix k k A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.fromBlocks p₁ 0 0 p₂).MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks q₁ 0 0 q₂) := by
  obtain ⟨hp₁, hq₁, v₁, hv₁p, hv₁q⟩ := h₁
  obtain ⟨hp₂, hq₂, v₂, hv₂p, hv₂q⟩ := h₂
  exact ⟨isStarProjection_fromBlocks_diag.mpr ⟨hp₁, hp₂⟩,
    isStarProjection_fromBlocks_diag.mpr ⟨hq₁, hq₂⟩,
    CStarMatrix.fromBlocks v₁ 0 0 v₂, by simp [hv₁p, hv₂p], by simp [hv₁q, hv₂q]⟩

private theorem mul_eq_zero_of_mul_proj_eq [Fintype m] [NonUnitalRing A]
    {a : CStarMatrix l m A} {b : CStarMatrix m n A} {r s : CStarMatrix m m A}
    (har : a * r = a) (hsb : s * b = b) (hrs : r * s = 0) : a * b = 0 := by
  rw [← har, ← hsb, ← mul_assoc, mul_assoc a, hrs, CStarMatrix.mul_zero, CStarMatrix.zero_mul]

/-- Murray–von Neumann equivalence is compatible with sums of orthogonal projections. -/
theorem MurrayVonNeumannEquiv.add [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) := by
  obtain ⟨hp₁, hq₁, v₁, hv₁p, hv₁q⟩ := h₁
  obtain ⟨hp₂, hq₂, v₂, hv₂p, hv₂q⟩ := h₂
  have hp' : p₂ * p₁ = 0 := by
    simpa only [star_mul, star_zero, hp₁.2.star_eq, hp₂.2.star_eq] using congr_arg star hp
  have hq' : q₂ * q₁ = 0 := by
    simpa only [star_mul, star_zero, hq₁.2.star_eq, hq₂.2.star_eq] using congr_arg star hq
  obtain ⟨hv₁_r, hv₁_l, hv₁s_l, hv₁s_r⟩ := mul_proj_eq_of_conjTranspose_mul_eq hp₁ hv₁p hv₁q
  obtain ⟨hv₂_r, hv₂_l, hv₂s_l, hv₂s_r⟩ := mul_proj_eq_of_conjTranspose_mul_eq hp₂ hv₂p hv₂q
  refine ⟨hp₁.add hp₂ hp, hq₁.add hq₂ hq, v₁ + v₂, ?_, ?_⟩
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add, hv₁p,
      hv₂p, mul_eq_zero_of_mul_proj_eq hv₁s_r hv₂_l hq,
      mul_eq_zero_of_mul_proj_eq hv₂s_r hv₁_l hq', add_zero, zero_add]
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add, hv₁q,
      hv₂q, mul_eq_zero_of_mul_proj_eq hv₁_r hv₂s_l hp,
      mul_eq_zero_of_mul_proj_eq hv₂_r hv₁s_l hp', add_zero, zero_add]

/-- Every star projection is Murray–von Neumann equivalent to its upper-left corner embedding
`fromBlocks p 0 0 0`. -/
theorem MurrayVonNeumannEquiv.cornerInl [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A)) := by
  refine ⟨hp, isStarProjection_fromBlocks_diag.mpr ⟨hp, .zero _⟩,
    ofMatrix (Matrix.of fun i j => Sum.elim (fun i₁ => p i₁ j) (fun _ => 0) i), ?_, ?_⟩
  · ext i j; simp [mul_apply, Fintype.sum_sum_type, (sum_star_mul_proj hp i j).1]
  · ext (i | i) (j | j) <;>
      first | (simp [mul_apply]; done) | simp [mul_apply, (sum_star_mul_proj hp i j).2]

/-- Every star projection is Murray–von Neumann equivalent to its lower-right corner embedding
`fromBlocks 0 0 0 q`. -/
theorem MurrayVonNeumannEquiv.cornerInr [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q) := by
  refine ⟨hq, isStarProjection_fromBlocks_diag.mpr ⟨.zero _, hq⟩,
    ofMatrix (Matrix.of fun i j => Sum.elim (fun _ => 0) (fun i₂ => q i₂ j) i), ?_, ?_⟩
  · ext i j; simp [mul_apply, Fintype.sum_sum_type, (sum_star_mul_proj hq i j).1]
  · ext (i | i) (j | j) <;>
      first | (simp [mul_apply]; done) | simp [mul_apply, (sum_star_mul_proj hq i j).2]

/-- Reindexing a star projection along any equivalence `e : m ≃ n` produces a Murray–von Neumann
equivalent projection, without assuming `A` is unital. -/
theorem MurrayVonNeumannEquiv.reindex [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A] (e : m ≃ n) {p : CStarMatrix m m A}
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv (reindexₐ R A e p) := by
  refine ⟨hp, hp.map (reindexₐ R A e), ofMatrix (Matrix.of fun i j => p (e.symm i) j), ?_, ?_⟩
  · ext i j
    simp only [mul_apply, conjTranspose_apply, ofMatrix_apply, Matrix.of_apply]
    rw [Fintype.sum_equiv e.symm _ (fun k => star (p k i) * p k j) fun _ => rfl]
    exact (sum_star_mul_proj hp i j).1
  · ext i j; rw [mul_apply, reindexₐ_apply]; exact (sum_star_mul_proj hp (e.symm i) (e.symm j)).2

/-- Block-diagonal sums of star projections are commutative up to Murray–von Neumann
equivalence. -/
theorem MurrayVonNeumannEquiv.fromBlocks_comm [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (CStarMatrix.fromBlocks p 0 0 q).MurrayVonNeumannEquiv (CStarMatrix.fromBlocks q 0 0 p) := by
  rw [← reindexₐ_sumComm_fromBlocks (R := ℕ) p q]
  exact MurrayVonNeumannEquiv.reindex (R := ℕ) (Equiv.sumComm m n)
    (isStarProjection_fromBlocks_diag.mpr ⟨hp, hq⟩)

/-- Block-diagonal sums of star projections are associative up to Murray–von Neumann
equivalence. -/
theorem MurrayVonNeumannEquiv.fromBlocks_assoc [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r) :
    (CStarMatrix.fromBlocks (CStarMatrix.fromBlocks p 0 0 q) 0 0 r).MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks p 0 0 (CStarMatrix.fromBlocks q 0 0 r)) := by
  rw [← reindexₐ_sumAssoc_fromBlocks (R := ℕ) p q r]
  exact MurrayVonNeumannEquiv.reindex (R := ℕ) (Equiv.sumAssoc l m n)
    (isStarProjection_fromBlocks_diag.mpr ⟨isStarProjection_fromBlocks_diag.mpr ⟨hp, hq⟩, hr⟩)

/-- Non-unital ⋆-algebra homomorphisms preserve Murray–von Neumann equivalence of matrix
projections. -/
theorem MurrayVonNeumannEquiv.mapₙₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (f : A →⋆ₙₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₙₐ f p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ f q) := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  exact ⟨hp.map (CStarMatrix.mapₙₐ f), hq.map (CStarMatrix.mapₙₐ f), v.map f,
    by rw [conjTranspose_map f v, ← CStarMatrix.map_mul f v.conjTranspose v, hvp]; rfl,
    by rw [conjTranspose_map f v, ← CStarMatrix.map_mul f v v.conjTranspose, hvq]; rfl⟩

/-- Unital ⋆-algebra homomorphisms preserve Murray–von Neumann equivalence of matrix
projections. -/
theorem MurrayVonNeumannEquiv.mapₐ [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₐ f p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ f q) := by
  rw [mapₐ_eq_mapₙₐ, mapₐ_eq_mapₙₐ]; exact h.mapₙₐ f.toNonUnitalStarAlgHom

/-- Unitarily conjugate star projections in a unital matrix ring are Murray–von Neumann
equivalent. -/
theorem MurrayVonNeumannEquiv.of_unitary_conj [Fintype m] [DecidableEq m] [Semiring A] [StarRing A]
    {p q : CStarMatrix m m A} (hp : IsStarProjection p) {u : unitary (CStarMatrix m m A)}
    (hconj : (u : CStarMatrix m m A) * p * star (u : CStarMatrix m m A) = q) :
    p.MurrayVonNeumannEquiv q := by
  refine ⟨hp, hconj ▸ hp.unitaryConj u, (u : CStarMatrix m m A) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.2.star_eq, _root_.mul_assoc,
      ← _root_.mul_assoc (star (u : CStarMatrix m m A)), Unitary.star_mul_self_of_mem u.property,
      _root_.one_mul, hp.1.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.2.star_eq, ← _root_.mul_assoc,
      _root_.mul_assoc (u : CStarMatrix m m A), hp.1.eq, hconj]

/-- Star projections conjugate by a unitary in `Unitization R (CStarMatrix m m A)` are
Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_unitization_unitary_conj [Fintype m] [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] {p q : CStarMatrix m m A} (hp : IsStarProjection p)
    {u : unitary (Unitization R (CStarMatrix m m A))}
    (hconj : (u : Unitization R (CStarMatrix m m A)) * (p : Unitization R (CStarMatrix m m A)) *
        star (u : Unitization R (CStarMatrix m m A)) = (q : Unitization R (CStarMatrix m m A))) :
    p.MurrayVonNeumannEquiv q := by
  obtain ⟨v, hv, hvp, hvq⟩ := hp.exists_isPartialIsometry_of_unitization_unitary_conj hconj
  exact ⟨hp, hvq ▸ hv.isStarProjection_mul_star_self, v, hvp, hvq⟩

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
      ∃ v : CStarMatrix m m A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q :=
  ⟨fun ⟨hp, _, v, hvp, hvq⟩ =>
      ⟨v, TauCeti.isPartialIsometry_iff.mpr
        (mul_conjTranspose_mul_self_of_isStarProjection (hvp ▸ hp)), hvp, hvq⟩,
    fun ⟨v, hv, hvp, hvq⟩ =>
      ⟨hvp ▸ hv.isStarProjection_star_mul_self, hvq ▸ hv.isStarProjection_mul_star_self,
        v, hvp, hvq⟩⟩

/-- Rectangular algebraic equivalence of star projections implies Murray–von Neumann equivalence:
if `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are star projections and `x * y = p`,
`y * x = q` for rectangular matrices `x, y`, then `p` and `q` are Murray–von Neumann equivalent
(Blackadar, Proposition 4.6.4). -/
theorem MurrayVonNeumannEquiv.of_mul_eq [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n A} {y : CStarMatrix n m A} (hxy : x * y = p) (hyx : y * x = q) :
    p.MurrayVonNeumannEquiv q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨V, hV, hVP, hVQ⟩ :=
    (isStarProjection_fromBlocks_diag.mpr ⟨hp, .zero _⟩).exists_isPartialIsometry_of_mul_eq
      (isStarProjection_fromBlocks_diag.mpr ⟨.zero _, hq⟩)
      (x := CStarMatrix.fromBlocks 0 x 0 0) (y := CStarMatrix.fromBlocks 0 0 y 0)
      (by simp [hxy]) (by simp [hyx])
  let v : CStarMatrix n m A := ofMatrix (Matrix.of fun i j => V (Sum.inr i) (Sum.inl j))
  have hV_eq : V = CStarMatrix.fromBlocks 0 0 v 0 := by
    have hQVP : CStarMatrix.fromBlocks 0 0 0 q * V * CStarMatrix.fromBlocks p 0 0 0 = V := by
      rw [show CStarMatrix.fromBlocks 0 0 0 q * V = V by rw [← hVQ, hV.mul_star_mul_self],
        ← hVP, ← _root_.mul_assoc, hV.mul_star_mul_self]
    ext (i | i) (j | j) <;>
      first | (simp [v]; done) | (rw [← hQVP]; simp [mul_apply, Fintype.sum_sum_type])
  rw [hV_eq] at hVP hVQ
  simp only [fromBlocks_star, conjTranspose_zero, fromBlocks_multiply, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, fromBlocks_inj] at hVP hVQ
  exact ⟨hp, hq, v, hVP.1, hVQ.2.2.2⟩

/-- Star projections in `CStarMatrix m m A` at distance `< 1` are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_norm_sub_lt_one [Fintype m] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : CStarMatrix m m A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hnorm : ‖p - q‖ < 1) : p.MurrayVonNeumannEquiv q :=
  murrayVonNeumannEquiv_iff_exists_isPartialIsometry.mpr
    (hp.exists_isPartialIsometry_of_norm_sub_lt_one hq hnorm)

/-- Endpoints of a norm-continuous path of star projections in `CStarMatrix m m A` are Murray–von
Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_continuous_path [Fintype m] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {γ : I → CStarMatrix m m A} (hγ : Continuous γ)
    (hproj : ∀ t : I, IsStarProjection (γ t)) : (γ 0).MurrayVonNeumannEquiv (γ 1) :=
  murrayVonNeumannEquiv_iff_exists_isPartialIsometry.mpr
    (IsStarProjection.exists_isPartialIsometry_of_continuous_path hγ hproj)

end CStarEquivalence

section StabilizedConjugacy

variable {m n A : Type*}

section RingStabilized

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
  (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hvp' : v * p = v)
include hvp hvq hvp'

omit [DecidableEq m] [DecidableEq n] in
private theorem stabilized_aux :
    p.conjTranspose = p ∧ q.conjTranspose = q ∧ p * v.conjTranspose = v.conjTranspose ∧
      q * v = v ∧ v.conjTranspose * q = v.conjTranspose ∧ p * p = p ∧ q * q = q := by
  have hp : p.conjTranspose = p := by rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  have hq : q.conjTranspose = q := by rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    simpa only [conjTranspose_mul, hp] using congr_arg conjTranspose hvp'
  have hqv : q * v = v := by rw [← hvq, mul_assoc, hvp, hvp']
  have hvq' : v.conjTranspose * q = v.conjTranspose := by
    simpa only [conjTranspose_mul, hq] using congr_arg conjTranspose hqv
  exact ⟨hp, hq, hpv, hqv, hvq', by nth_rw 1 [← hvp]; rw [mul_assoc, hvp', hvp],
    by nth_rw 1 [← hvq]; rw [mul_assoc, hvq', hvq]⟩

/-- The self-adjoint block reflection unitary `[[1 - p, vᴴ], [v, 1 - q]]` associated to a
rectangular partial isometry `v` with `vᴴ * v = p`, `v * vᴴ = q`, and `v * p = v`. -/
def stabilizedReflectionUnitary : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    obtain ⟨hp_star, hq_star, hpv', -⟩ := stabilized_aux hvp hvq hvp'
    have hsa : star (fromBlocks (1 - p) v.conjTranspose v (1 - q)) =
        fromBlocks (1 - p) v.conjTranspose v (1 - q) := by
      rw [fromBlocks_star]; simp [star_eq_conjTranspose, hp_star, hq_star]
    have hsq : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
        fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
      apply ofMatrix.symm.injective
      simp only [ofMatrix_symm_hMul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_one]
      exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq (congr_arg ofMatrix.symm hvp)
        (congr_arg ofMatrix.symm hvq) (congr_arg ofMatrix.symm hpv') (congr_arg ofMatrix.symm hvp')
    rw [Unitary.mem_iff, hsa, hsq]; exact ⟨rfl, rfl⟩⟩

@[simp] theorem coe_stabilizedReflectionUnitary :
    (stabilizedReflectionUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)

theorem isSelfAdjoint_stabilizedReflectionUnitary :
    IsSelfAdjoint (stabilizedReflectionUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  obtain ⟨hp_star, hq_star, -⟩ := stabilized_aux hvp hvq hvp'
  rw [IsSelfAdjoint, coe_stabilizedReflectionUnitary, fromBlocks_star]
  simp [star_eq_conjTranspose, hp_star, hq_star]

/-- The block reflection unitary `[[1 - p, vᴴ], [v, 1 - q]]` conjugates `p ⊕ 0` to `0 ⊕ q`. -/
theorem stabilizedReflectionUnitary_conj :
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
    (congr_arg ofMatrix.symm hvp) (congr_arg ofMatrix.symm hvq) (congr_arg ofMatrix.symm hvp')

/-- The block rotation unitary `[[1 - p, -vᴴ], [v, 1 - q]]` conjugating `p ⊕ 0` to `0 ⊕ q`. -/
def stabilizedRotationUnitary : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) (-v.conjTranspose) v (1 - q), by
    obtain ⟨hp_star, hq_star, hpv', hvq', hqv', hpp, hqq⟩ := stabilized_aux hvp hvq hvp'
    rw [Unitary.mem_iff, fromBlocks_star, conjTranspose_neg, conjTranspose_conjTranspose]
    simp only [star_sub, star_one, star_eq_conjTranspose, hp_star, hq_star, fromBlocks_multiply,
      ← fromBlocks_one, fromBlocks_inj, CStarMatrix.sub_mul, CStarMatrix.mul_sub,
      CStarMatrix.one_mul, CStarMatrix.mul_one, CStarMatrix.neg_mul, CStarMatrix.mul_neg,
      hvp, hvq, hvp', hpv', hvq', hqv', hpp, hqq]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> abel⟩

@[simp] theorem coe_stabilizedRotationUnitary :
    (stabilizedRotationUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) (-v.conjTranspose) v (1 - q) := (rfl)

/-- The block rotation unitary `[[1 - p, -vᴴ], [v, 1 - q]]` conjugates `p ⊕ 0` to `0 ⊕ q`. -/
theorem stabilizedRotationUnitary_conj :
    (stabilizedRotationUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedRotationUnitary hvp hvq hvp' : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  obtain ⟨hp_star, hq_star, -, -, -, hpp, -⟩ := stabilized_aux hvp hvq hvp'
  rw [coe_stabilizedRotationUnitary, fromBlocks_star, conjTranspose_neg,
    conjTranspose_conjTranspose]
  simp only [star_sub, star_one, star_eq_conjTranspose, hp_star, hq_star, fromBlocks_multiply,
    CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.one_mul, CStarMatrix.mul_one,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, CStarMatrix.mul_neg,
    hpp, hvp', hvq, sub_self, neg_zero, add_zero]

end RingStabilized

section CStarStabilized

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
  (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hvp' : v * p = v)
include hvp hvq hvp'

/-- The explicit exponential unitary path from `1` to `stabilizedReflectionUnitary`. -/
noncomputable def stabilizedReflectionPath :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A))
      (stabilizedReflectionUnitary hvp hvq hvp') :=
  Unitary.selfAdjointExpPath (stabilizedReflectionUnitary hvp hvq hvp')
    (isSelfAdjoint_stabilizedReflectionUnitary hvp hvq hvp')

/-- At the midpoint `t = 1/2`, conjugating `p ⊕ 0` along `stabilizedReflectionPath` yields the
projection `[[(1/2) • p, (i/2) • vᴴ], [(-i/2) • v, (1/2) • q]]`. -/
theorem stabilizedReflectionPath_conj_half :
    Unitary.conjPath (fromBlocks p 0 0 0) (stabilizedReflectionPath hvp hvq hvp')
        ⟨1 / 2, by norm_num, by norm_num⟩ =
      fromBlocks (((1 : ℂ) / 2) • p) ((Complex.I / 2) • v.conjTranspose)
        ((-Complex.I / 2) • v) (((1 : ℂ) / 2) • q) := by
  obtain ⟨hp_star, hq_star, hpv', -, -, hpp, -⟩ := stabilized_aux hvp hvq hvp'
  let c : ℂ := (Complex.I - 1) * (2 : ℂ)⁻¹
  have hu : ((stabilizedReflectionPath hvp hvq hvp' ⟨1 / 2, by norm_num, by norm_num⟩ :
        unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 + c • p) ((-c) • v.conjTranspose) ((-c) • v) (1 + c • q) := by
    have hexp : Complex.exp (Complex.I * (((1 / 2 : ℝ) : ℂ) * Real.pi)) = Complex.I := by
      rw [show Complex.I * (((1 / 2 : ℝ) : ℂ) * Real.pi) = Real.pi / 2 * Complex.I by
        push_cast; ring, Complex.exp_pi_div_two_mul_I]
    rw [stabilizedReflectionPath, Unitary.coe_selfAdjointExpPath, hexp,
      coe_stabilizedReflectionUnitary, ← fromBlocks_one, fromBlocks_sub]
    simp only [sub_sub_cancel, zero_sub, zero_add, fromBlocks_smul, fromBlocks_add, smul_smul,
      smul_neg, neg_smul, c]
  have hsu : star (fromBlocks (1 + c • p) ((-c) • v.conjTranspose) ((-c) • v) (1 + c • q)) =
      fromBlocks (1 + star c • p) ((-star c) • v.conjTranspose)
        ((-star c) • v) (1 + star c • q) := by
    rw [fromBlocks_star]
    simp only [star_add, star_one, star_smul, star_eq_conjTranspose, hp_star,
      hq_star, conjTranspose_smul, conjTranspose_conjTranspose, star_neg]
  have hleft : fromBlocks (1 + c • p) ((-c) • v.conjTranspose) ((-c) • v) (1 + c • q) *
      fromBlocks p 0 0 0 = fromBlocks ((1 + c) • p) 0 ((-c) • v) 0 := by
    simp only [fromBlocks_multiply, CStarMatrix.mul_zero, add_zero, CStarMatrix.add_mul,
      CStarMatrix.one_mul, CStarMatrix.smul_mul, hpp, hvp', add_smul, one_smul]
  have ⟨h11, h12, h21, h22⟩ : 1 + c + star c * (1 + c) = (1 : ℂ) / 2 ∧
      -star c * (1 + c) = Complex.I / 2 ∧ -c + star c * -c = -Complex.I / 2 ∧
      -star c * -c = (1 : ℂ) / 2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Complex.ext <;> simp [c] <;> norm_num)
  rw [Unitary.conjPath_apply, hu, hleft, hsu, fromBlocks_multiply]
  simp only [CStarMatrix.zero_mul, CStarMatrix.mul_add, CStarMatrix.mul_one, CStarMatrix.smul_mul,
    CStarMatrix.mul_smul, hpp, hvp', hpv', hvq, smul_smul, smul_zero, add_zero, ← add_smul,
    h11, h12, h21, h22]

end CStarStabilized

/-- For `p = q = 1` in `CStarMatrix (Fin 1) (Fin 1) ℂ` and `v = 1`, the midpoint of
`stabilizedReflectionPath` is `[[1/2, i/2], [-i/2, 1/2]]`. -/
theorem stabilizedReflectionPath_one_conj_half :
    Unitary.conjPath (fromBlocks (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) 0 0
        (0 : CStarMatrix (Fin 1) (Fin 1) ℂ))
      (stabilizedReflectionPath (m := Fin 1) (n := Fin 1) (A := ℂ) (p := 1) (q := 1) (v := 1)
        (by simp) (by simp) (by simp)) ⟨1 / 2, by norm_num, by norm_num⟩ =
      fromBlocks (((1 : ℂ) / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        ((Complex.I / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        ((-Complex.I / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ))
        (((1 : ℂ) / 2) • (1 : CStarMatrix (Fin 1) (Fin 1) ℂ)) := by
  simpa only [conjTranspose_one] using stabilizedReflectionPath_conj_half (m := Fin 1) (n := Fin 1)
    (A := ℂ) (p := 1) (q := 1) (v := 1) (by simp) (by simp) (by simp)

section NonUnitalStabilized
variable [Fintype m] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a (possibly non-unital) C⋆-algebra, Murray–von Neumann equivalent matrix projections `p`
and `q` become conjugate after stabilization by a unitary in the identity component of
`(CStarMatrix (m ⊕ n) (m ⊕ n) A)⁺¹`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitization_unitary_conj [Fintype n]
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
  let V' : B⁺¹ := (V : B⁺¹)
  have hV'_init : star V' * V' = ((CStarMatrix.fromBlocks p 0 0 0 : B) : B⁺¹) := by
    rw [← Unitization.inr_star, ← Unitization.inr_mul]; simp [V, B, hvp]
  have hV'_final : V' * star V' = ((CStarMatrix.fromBlocks 0 0 0 q : B) : B⁺¹) := by
    rw [← Unitization.inr_star, ← Unitization.inr_mul]; simp [V, B, hvq]
  have hV'_pi : TauCeti.IsPartialIsometry V' := by
    rw [TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self, hV'_init]
    exact (isStarProjection_fromBlocks_diag.mpr ⟨hp, .zero _⟩).map
      (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have horth : (star V' * V') * (V' * star V') = 0 := by
    rw [hV'_init, hV'_final, ← Unitization.inr_mul]; simp [B]
  let w : unitary B⁺¹ := hV'_pi.reflectionUnitary horth
  exact ⟨w, by rw [← hV'_init, ← hV'_final]; exact hV'_pi.reflectionUnitary_conj horth,
    ⟨Unitary.selfAdjointExpPath w (hV'_pi.isSelfAdjoint_reflectionUnitary horth)⟩⟩

/-- In a (possibly non-unital) C⋆-algebra, Murray–von Neumann equivalent matrix projections `p` and
`q` are joined after stabilization by a continuous path of star projections from `p ⊕ 0` to
`0 ⊕ q`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_path [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨u, hconj, ⟨γu⟩⟩ := h.exists_stabilized_unitization_unitary_conj
  exact ⟨(Unitary.unitizationConjPath (CStarMatrix.fromBlocks p 0 0 0) γu).cast rfl
      (by rw [hconj]; rfl),
    (isStarProjection_fromBlocks_diag.mpr ⟨h.isStarProjection_left, .zero _⟩)
      |>.isStarProjection_unitizationConjPath γu⟩

/-- For same-size Murray–von Neumann equivalent matrix projections `p, q : CStarMatrix m m A` over
a (possibly non-unital) C⋆-algebra, `p ⊕ 0` and `q ⊕ 0` are joined by a continuous path of star
projections in `CStarMatrix (m ⊕ m) (m ⊕ m) A`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_path_left
    {p q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix m m A))
        (CStarMatrix.fromBlocks q 0 0 (0 : CStarMatrix m m A)),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨γ₁, hγ₁⟩ := h.exists_stabilized_path
  obtain ⟨γ₂, hγ₂⟩ := (MurrayVonNeumannEquiv.refl h.isStarProjection_right).exists_stabilized_path
  refine ⟨γ₁.trans γ₂.symm, fun t => ?_⟩
  rw [Path.trans_apply]; split_ifs <;> [exact hγ₁ _; exact hγ₂ _]

end NonUnitalStabilized

section UnitalStabilized
variable [Fintype m] [DecidableEq m] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, Murray–von Neumann equivalent matrix projections `p` and `q` satisfy
that `p ⊕ 0` and `0 ⊕ q` are conjugate by a unitary in the identity component of
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj [Fintype n] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * CStarMatrix.fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = CStarMatrix.fromBlocks 0 0 0 q ∧
        Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) u := by
  obtain ⟨hp, -, v, hvp, hvq⟩ := h
  have hvp' : v * p = v := by
    rw [← hvp, ← mul_assoc]; exact mul_conjTranspose_mul_self_of_isStarProjection (hvp ▸ hp)
  exact ⟨stabilizedReflectionUnitary hvp hvq hvp', stabilizedReflectionUnitary_conj hvp hvq hvp',
    ⟨stabilizedReflectionPath hvp hvq hvp'⟩⟩

/-- In a unital C⋆-algebra, same-size Murray–von Neumann equivalent projections `p` and `q` satisfy
that `p ⊕ 0` and `q ⊕ 0` are conjugate by a unitary in the identity component of
`unitary (CStarMatrix (m ⊕ m) (m ⊕ m) A)`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj_left
    {p q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (m ⊕ m) (m ⊕ m) A),
      (u : CStarMatrix (m ⊕ m) (m ⊕ m) A) * CStarMatrix.fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ m) (m ⊕ m) A) = CStarMatrix.fromBlocks q 0 0 0 ∧
        Joined (1 : unitary (CStarMatrix (m ⊕ m) (m ⊕ m) A)) u := by
  let B := CStarMatrix (m ⊕ m) (m ⊕ m) A
  obtain ⟨u₁, hu₁, hj₁⟩ := h.exists_stabilized_unitary_conj
  obtain ⟨u₂, hu₂, ⟨γ₂⟩⟩ :=
    (MurrayVonNeumannEquiv.refl h.isStarProjection_right).exists_stabilized_unitary_conj
  have hinv : Continuous (Inv.inv : unitary B → unitary B) :=
    continuous_induced_rng.mpr (continuous_star.comp continuous_subtype_val)
  have hj₂ : Joined (1 : unitary B) u₂⁻¹ := ⟨(γ₂.map hinv).cast inv_one.symm rfl⟩
  refine ⟨u₂⁻¹ * u₁, ?_, by simpa using hj₂.mul hj₁⟩
  calc ((u₂⁻¹ * u₁ : unitary B) : B) * CStarMatrix.fromBlocks p 0 0 0 *
        star ((u₂⁻¹ * u₁ : unitary B) : B)
      = star (u₂ : B) * ((u₁ : B) * CStarMatrix.fromBlocks p 0 0 0 * star (u₁ : B)) *
          (u₂ : B) := by simp [← Unitary.star_eq_inv, _root_.mul_assoc]
    _ = star (u₂ : B) * (u₂ : B) * CStarMatrix.fromBlocks q 0 0 0 *
          (star (u₂ : B) * (u₂ : B)) := by rw [hu₁, ← hu₂]; simp only [_root_.mul_assoc]
    _ = CStarMatrix.fromBlocks q 0 0 0 := by simp

end UnitalStabilized

end StabilizedConjugacy

end CStarMatrix
