/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.FirstMinimum.Basic
import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PointLattice

/-!
# First minima for positive definite adelic frames

The pairing of two rational lattice vectors is an algebraic integer. In positive definite
signature, the values of a vector's self-pairing at the infinite places are the squared
Euclidean lengths of its local coordinates. The product formula therefore rules out
nonzero lattice vectors of length less than one. The truncated first minimum, including
at every translate of the frame, is exactly one.

This is the definite first-minimum bound of `New.Space.one_le_firstMinimum` and
`New.Space.firstMinimum_move_eq_one` in `Lib/Adelic/Reduction/FirstMinimumShortBases.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open Matrix NumberField

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ}

/-- At an infinite place the Hermitian pairing is the signed dot product of the archimedean
coordinates in the inverse frame. -/
theorem embedding_dotProduct_gram_mulVec (V : FramedHermitianSpace E s) (w : InfinitePlace E)
    (y z : ι → E) : w.embedding (star y ⬝ᵥ (V.gram *ᵥ z)) =
      ∑ i, star (V.archCoords y (i, w)) * ((s i : ℤ) : ℂ) * V.archCoords z (i, w) := by
  let f := algebraMap E (InfiniteAdeleRing E)
  let e : InfiniteAdeleRing E →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    (Pi.evalRingHom (fun v : InfinitePlace E ↦ v.Completion) w)
  let g : Matrix ι ι (InfiniteAdeleRing E) := V.frame.1
  let C (x : ι → E) := (↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ (f ∘ x)
  have hC (x : ι → E) : g *ᵥ C x = f ∘ x := by
    simp only [g, C, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hmap : f (star y ⬝ᵥ (V.gram *ᵥ z)) =
      star (f ∘ y) ⬝ᵥ (V.gram.map f *ᵥ (f ∘ z)) := by
    have hstar : f ∘ star y = star (f ∘ y) := funext fun i ↦ algebraMap_star_comm (y i)
    have hzmap : f ∘ (V.gram *ᵥ z) = V.gram.map f *ᵥ (f ∘ z) := funext (f.map_mulVec V.gram z)
    rw [f.map_dotProduct, hstar, hzmap]
  have hframe : star g * V.gram.map f * g = diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) :=
    V.star_mul_gram_mul_fst
  have hform : star (f ∘ y) ⬝ᵥ (V.gram.map f *ᵥ (f ∘ z)) =
      star (C y) ⬝ᵥ (diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) *ᵥ C z) := by
    rw [← hC y, ← hC z, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      mulVec_mulVec, ← star_eq_conjTranspose, hframe]
  have he_apply (x : InfiniteAdeleRing E) :
      e x = InfinitePlace.Completion.extensionEmbedding w (x w) := rfl
  have he (x : E) : e (f x) = w.embedding x := by
    simp [he_apply, f]
  have he_star (x : InfiniteAdeleRing E) : e (star x) = star (e x) :=
    InfiniteAdeleRing.extensionEmbedding_star_apply x w
  rw [← he, hmap, hform, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.star_apply, mulVec_diagonal, map_mul, map_intCast, he_star, mul_assoc]
  simp only [archCoords_apply, he_apply, C, f]

variable (V : FramedHermitianSpace E (fun _ : ι ↦ 1))

/-- For a positive definite frame the squared length is a sum of the absolute values of the
self-pairing at the infinite places. -/
theorem vectorLength_sq_eq_sum_infinitePlace (y : ι → E) :
    V.vectorLength y ^ 2 = ∑ w : InfinitePlace E, w (star y ⬝ᵥ (V.gram *ᵥ y)) := by
  rw [V.vectorLength_def, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [← w.norm_embedding_eq, V.embedding_dotProduct_gram_mulVec]
  have hsum : (∑ i, (↑(‖V.archCoords y (i, w)‖ ^ 2) : ℂ)) =
      ↑(∑ i, ‖V.archCoords y (i, w)‖ ^ 2) := (Complex.ofReal_sum _ _).symm
  simp only [Units.val_one, Int.cast_one, mul_one, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow] at hsum ⊢
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- A nonzero lattice vector in a positive definite adelic frame has length at least one. -/
theorem one_le_vectorLength_of_definite {y : ι → E} (hy : y ∈ V.lattice) (hyn : y ≠ 0) :
    1 ≤ V.vectorLength y := by
  let a := star y ⬝ᵥ (V.gram *ᵥ y)
  have hsum : V.vectorLength y ^ 2 = ∑ w : InfinitePlace E, w a :=
    V.vectorLength_sq_eq_sum_infinitePlace y
  have ha : a ≠ 0 := by
    intro hzero
    rw [hzero] at hsum
    exact (pow_pos (V.vectorLength_pos hyn) 2).ne'
      (by simpa only [map_zero, Finset.sum_const_zero] using hsum)
  let A : 𝓞 E := ⟨a, V.isIntegral_dotProduct_gram_mulVec hy hy⟩
  have hA : A ≠ 0 := by
    intro h
    have hcoe : (A : E) = a := RingOfIntegers.coe_mk (V.isIntegral_dotProduct_gram_mulVec hy hy)
    exact ha (hcoe.symm.trans (congrArg (fun b : 𝓞 E ↦ (b : E)) h))
  by_contra! hlt
  have hw (w : InfinitePlace E) : w a < 1 := calc
    _ ≤ ∑ v : InfinitePlace E, v a :=
      Finset.single_le_sum (fun v _ ↦ by rw [← v.norm_embedding_eq]; exact norm_nonneg _)
        (Finset.mem_univ w)
    _ < 1 := by
      rw [← hsum, sq_lt_one_iff_abs_lt_one, abs_of_nonneg (V.vectorLength_nonneg y)]
      exact hlt
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  exact (hw w).not_ge (InfinitePlace.one_le_of_lt_one hA fun v _ ↦ hw v)

/-- The truncated first minimum of a positive definite adelic frame is one. -/
@[simp] theorem firstMinimum_eq_one_of_definite : V.firstMinimum = 1 :=
  V.firstMinimum_eq_one_iff.mpr fun _ ↦ V.one_le_vectorLength_of_definite

/-- At every adelic unitary point the height of a positive definite frame is one. -/
@[simp] theorem height_eq_one_of_definite (g : adelicUnitaryGroup E (fun _ : ι ↦ 1)) :
    V.height g = 1 := by
  rw [V.height_def, firstMinimum_eq_one_of_definite, inv_one]

end TauCeti.FramedHermitianSpace
