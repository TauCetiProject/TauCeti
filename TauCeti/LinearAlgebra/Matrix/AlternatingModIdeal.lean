/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IdealEntries

/-!
# Matrices alternating modulo an ideal

A square matrix `N` over a commutative ring is *alternating modulo an ideal* `I`
(`Matrix.IsAltMod`) when its diagonal entries and its symmetric sums `N i j + N j i` lie in `I`.
Then the quadratic expression `xᵀ N x` lies in `I` for every vector `x`
(`Matrix.IsAltMod.sum_mul_mul_mem`), and `Pᵀ N P` is again alternating modulo `I` for every
square matrix `P` (`Matrix.IsAltMod.transpose_mul_mul`). Modulo `⊥` this says exactly that the
quadratic form `x ↦ xᵀ N x` vanishes (`Matrix.isAltMod_bot_iff`).

This is the condition that cuts the orthogonal group scheme of a quadratic form out of `GLₙ` in
every characteristic: `g` preserves the form with coefficient matrix `M` exactly when
`gᵀ M g - M` is alternating, which is weaker than `gᵀ M g = M` when `M` is not symmetric.

## Main declarations

* `Matrix.IsAltMod`: alternating modulo an ideal.
* `Matrix.IsAltMod.sum_mul_mul_mem`: the quadratic expression of such a matrix lies in the ideal.
* `Matrix.IsAltMod.transpose_mul_mul`: stability under framing `N ↦ Pᵀ N P`.
* `Matrix.IsAltMod.map`: stability under a ring morphism carrying the ideal into another.
* `Matrix.isAltMod_bot_iff`: alternating modulo `⊥` means the quadratic form vanishes.
-/

public section

open scoped Matrix

namespace Matrix

variable {ι S : Type*} [CommRing S]

/-- A square matrix is **alternating modulo an ideal** `I` when its diagonal entries and its
symmetric sums `N i j + N j i` lie in `I`: equivalently, `xᵀ N x ∈ I` for every vector `x`. -/
@[expose] def IsAltMod (I : Ideal S) (N : Matrix ι ι S) : Prop :=
  (∀ i, N i i ∈ I) ∧ ∀ i j, N i j + N j i ∈ I

namespace IsAltMod

variable {I J : Ideal S} {N N' : Matrix ι ι S}

/-- The zero matrix is alternating modulo every ideal. -/
theorem zero : IsAltMod I (0 : Matrix ι ι S) :=
  ⟨fun _ => by simp, fun _ _ => by simp⟩

/-- The quadratic expression `Σᵢ Σⱼ aᵢ aⱼ Nᵢⱼ` of a matrix alternating modulo `I` lies in `I`. -/
theorem sum_mul_mul_mem [Fintype ι] (hN : IsAltMod I N) (a : ι → S) :
    ∑ i, ∑ j, a i * a j * N i j ∈ I := by
  classical
  suffices h : ∀ s : Finset ι, ∑ i ∈ s, ∑ j ∈ s, a i * a j * N i j ∈ I from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    -- Split off the row and the column of the new index `k`.
    have hsplit : ∑ i ∈ insert k s, ∑ j ∈ insert k s, a i * a j * N i j =
        a k * a k * N k k + ∑ j ∈ s, a k * a j * (N k j + N j k) +
          ∑ i ∈ s, ∑ j ∈ s, a i * a j * N i j := by
      simp only [Finset.sum_insert hk, Finset.sum_add_distrib, mul_add]
      have hcol : ∑ i ∈ s, a i * a k * N i k = ∑ j ∈ s, a k * a j * N j k :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [hcol]
      ring
    rw [hsplit]
    exact add_mem (add_mem (I.mul_mem_left _ (hN.1 k))
      (Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hN.2 k j))) ih

/-- A matrix alternating modulo `I` stays so when framed by any matrix: `Pᵀ N P`. -/
theorem transpose_mul_mul [Fintype ι] (hN : IsAltMod I N) (P : Matrix ι ι S) :
    IsAltMod I (Pᵀ * N * P) := by
  refine ⟨fun k => ?_, fun k l => ?_⟩
  · have h := hN.sum_mul_mul_mem (fun i => P i k)
    convert h using 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · have hsum : (Pᵀ * N * P) k l + (Pᵀ * N * P) l k = (Pᵀ * (N + Nᵀ) * P) k l := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      congr 1
      rw [← Matrix.transpose_apply (Pᵀ * N * P) k l, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [hsum]
    exact Matrix.mul_mul_apply_mem (fun i j => hN.2 i j) _ _ k l

/-- The sum of two matrices alternating modulo `I` is alternating modulo `I`. -/
theorem add (hN : IsAltMod I N) (hN' : IsAltMod I N') : IsAltMod I (N + N') :=
  ⟨fun i => by simpa using add_mem (hN.1 i) (hN'.1 i),
    fun i j => by
      rw [Matrix.add_apply, Matrix.add_apply, add_add_add_comm]
      exact add_mem (hN.2 i j) (hN'.2 i j)⟩

/-- The negative of a matrix alternating modulo `I` is alternating modulo `I`. -/
theorem neg (hN : IsAltMod I N) : IsAltMod I (-N) :=
  ⟨fun i => by simpa using neg_mem (hN.1 i),
    fun i j => by
      rw [Matrix.neg_apply, Matrix.neg_apply, ← neg_add]
      exact neg_mem (hN.2 i j)⟩

/-- Being alternating modulo an ideal is inherited by every larger ideal. -/
theorem mono (hIJ : I ≤ J) (hN : IsAltMod I N) : IsAltMod J N :=
  ⟨fun i => hIJ (hN.1 i), fun i j => hIJ (hN.2 i j)⟩

/-- A ring morphism carrying `I` into `J` carries matrices alternating modulo `I` to matrices
alternating modulo `J`. -/
theorem map {T F : Type*} [CommRing T] [FunLike F S T] [RingHomClass F S T] {J : Ideal T}
    (hN : IsAltMod I N) (f : F) (hIJ : I.map f ≤ J) : IsAltMod J (N.map f) :=
  ⟨fun i => hIJ (Ideal.mem_map_of_mem f (hN.1 i)),
    fun i j => by
      rw [Matrix.map_apply, Matrix.map_apply, ← map_add]
      exact hIJ (Ideal.mem_map_of_mem f (hN.2 i j))⟩

end IsAltMod

/-- A matrix is alternating modulo `⊥` exactly when its quadratic form `x ↦ xᵀ N x` vanishes. -/
theorem isAltMod_bot_iff [Fintype ι] (N : Matrix ι ι S) :
    IsAltMod ⊥ N ↔ ∀ x : ι → S, x ⬝ᵥ (N *ᵥ x) = 0 := by
  classical
  have hform (x : ι → S) : x ⬝ᵥ (N *ᵥ x) = ∑ i, ∑ j, x i * x j * N i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsingle (i j : ι) : (Pi.single i 1 : ι → S) ⬝ᵥ (N *ᵥ Pi.single j 1) = N i j := by
    simp
  refine ⟨fun h x => by simpa [hform] using h.sum_mul_mul_mem x, fun h => ⟨fun i => ?_,
    fun i j => ?_⟩⟩
  · rw [Ideal.mem_bot, ← hsingle]
    exact h _
  · have hij := h (Pi.single i 1 + Pi.single j 1)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hsingle] at hij
    rw [Ideal.mem_bot]
    have hi := hsingle i i ▸ h (Pi.single i 1)
    have hj := hsingle j j ▸ h (Pi.single j 1)
    rw [hi, hj, zero_add, add_zero, add_comm] at hij
    exact hij

end Matrix
