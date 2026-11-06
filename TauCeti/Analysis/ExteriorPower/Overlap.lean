/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ExteriorPower.Nonarchimedean
import Mathlib.Basic.Real.Pointwise

/-!
# Nonarchimedean exterior norms of overlapping families

For row families `x`, `y` and `z`, the exterior maximum norms satisfy
`N(x) N(x, y, z) ≤ N(x, y) N(x, z)`. Here `N` is the maximum absolute value
of the maximal minors, with value one for the empty family and zero for a
dependent family. This is the nonarchimedean local inequality underlying
submodularity of Euclidean subspace heights; the archimedean counterpart is
Koteljanskii's inequality for Gram determinants.

The proof uses `AbsoluteValue.exists_integral_plucker_reduction` to support the
common rows on pivot coordinates without changing any exterior norm. Row
normalization makes them coordinate vectors, and subtracting their components
reduces the estimate to submultiplicativity under concatenation. Neither a
discrete value group nor completeness of the valued field is needed.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §2.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.12).
-/

public section

open scoped BigOperators Matrix
open Set TauCeti

namespace AbsoluteValue

variable {K ι : Type*} [LinearOrder ι] {p q : ℕ}

/-- Row operations on the two blocks of a concatenation scale its exterior
maximum norm by the product of their determinant moduli. -/
theorem iSup_plucker_append_mul_left [CommRing K] (v : AbsoluteValue K ℝ)
    (A : Matrix (Fin p) (Fin p) K) (B : Matrix (Fin q) (Fin q) K)
    (x : Matrix (Fin p) ι K) (y : Matrix (Fin q) ι K) :
    (⨆ s, v (plucker (Fin.append (A * x).row (B * y).row) s)) =
      v A.det * v B.det * ⨆ s, v (plucker (Fin.append x.row y.row) s) := by
  simp_rw [Matrix.plucker_append_mul, map_mul,
    ← Real.mul_iSup_of_nonneg (mul_nonneg (v.nonneg _) (v.nonneg _))]

variable [Field K] [Finite ι]

/-- Concatenation is submultiplicative for the nonarchimedean exterior maximum
norm. Empty blocks, dependent rows and more rows than coordinates are allowed. -/
theorem iSup_plucker_append_le (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (x : Fin p → ι → K) (y : Fin q → ι → K) :
    (⨆ s, v (plucker (Fin.append x y) s)) ≤
      (⨆ s, v (plucker x s)) * ⨆ s, v (plucker y s) := by
  classical
  by_cases hx : LinearIndependent K x
  · by_cases hy : LinearIndependent K y
    · -- Normalize each block by a largest minor. Every entry is then integral,
      -- so the elementary nonarchimedean row-norm bound has constant one.
      obtain ⟨e, he, hm, hb⟩ := v.exists_pivot_inv_mul_le_one hx
      obtain ⟨f, hf, hn, hc⟩ := v.exists_pivot_inv_mul_le_one hy
      have hox : Matrix.of x = (x : Matrix (Fin p) ι K) := by ext; simp
      have hoy : Matrix.of y = (y : Matrix (Fin q) ι K) := by ext; simp
      let A := (Matrix.of x).submatrix id e
      let B := (Matrix.of y).submatrix id f
      have hA : A * (A⁻¹ * Matrix.of x) = Matrix.of x := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr he),
          Matrix.one_mul]
      have hB : B * (B⁻¹ * Matrix.of y) = Matrix.of y := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hf),
          Matrix.one_mul]
      refine Real.iSup_le (fun s ↦ ?_) (mul_nonneg
        (Real.iSup_nonneg_of_nonnegHomClass v _) (Real.iSup_nonneg_of_nonnegHomClass v _))
      have h := Matrix.plucker_append_mul A B (A⁻¹ * Matrix.of x) (B⁻¹ * Matrix.of y) s
      rw [hA, hB] at h
      simp only [Matrix.row_eq_self, Equiv.symm_apply_apply] at h
      have hm' : v A.det = ⨆ s, v (plucker x s) := hm
      have hn' : v B.det = ⨆ s, v (plucker y s) := hn
      rw [h, map_mul, map_mul, hm', hn']
      refine mul_le_of_le_one_right (mul_nonneg
        (Real.iSup_nonneg_of_nonnegHomClass v _) (Real.iSup_nonneg_of_nonnegHomClass v _)) ?_
      refine (v.plucker_le_prod_iSup hv _ s).trans ?_
      refine (Finset.prod_le_prod₀ (fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
        fun i _ ↦ ?_).trans_eq Finset.prod_const_one
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      rcases i with i | i
      · refine Real.iSup_le (fun j ↦ ?_) zero_le_one
        simpa [A, hox] using hb i j
      · refine Real.iSup_le (fun j ↦ ?_) zero_le_one
        simpa [B, hoy] using hc i j
    · have hz : plucker y = 0 := not_ne_iff.mp ((plucker_ne_zero_iff y).not.mpr hy)
      have hxy : ¬LinearIndependent K (Fin.append x y) := fun h ↦
        hy (by simpa [Function.comp_def] using
          h.comp (Fin.natAdd p) (Fin.natAdd_injective _ _))
      have hzero : plucker (Fin.append x y) = 0 :=
        not_ne_iff.mp ((plucker_ne_zero_iff _).not.mpr hxy)
      simp [hz, hzero]
  · have hz : plucker x = 0 := not_ne_iff.mp ((plucker_ne_zero_iff x).not.mpr hx)
    have hxy : ¬LinearIndependent K (Fin.append x y) := fun h ↦
      hx (by simpa [Function.comp_def] using
        h.comp (Fin.castAdd q) (Fin.castAdd_injective _ _))
    have hzero : plucker (Fin.append x y) = 0 :=
      not_ne_iff.mp ((plucker_ne_zero_iff _).not.mpr hxy)
    simp [hz, hzero]

private theorem iSup_plucker_append_single_eq (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (e : Fin p ↪ ι) (y : Matrix (Fin q) ι K)
    (hy : ∀ i a, y i (e a) = 0) :
    (⨆ s, v (plucker (Fin.append (fun i ↦ Pi.single (e i) 1) y.row) s)) =
      ⨆ s, v (plucker y.row s) := by
  classical
  let u : Fin p → ι → K := fun i ↦ Pi.single (e i) 1
  have hu : (⨆ s, v (plucker u s)) ≤ 1 := by
    refine Real.iSup_le (fun s ↦ (v.plucker_le_prod_iSup hv u s).trans ?_) zero_le_one
    refine (Finset.prod_le_prod₀ (fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
      fun i _ ↦ Real.iSup_le (fun j ↦ ?_) zero_le_one).trans_eq Finset.prod_const_one
    simp only [u, Pi.single_apply]
    split_ifs <;> simp
  apply le_antisymm
  · exact (v.iSup_plucker_append_le hv u y.row).trans
      (mul_le_of_le_one_left (Real.iSup_nonneg_of_nonnegHomClass v _) hu)
  · refine Real.iSup_le (fun s ↦ ?_) (Real.iSup_nonneg_of_nonnegHomClass v _)
    let f := powersetCard.ofFinEmbEquiv.symm s
    let A := Matrix.of (Fin.append u y.row)
    have hblock : (A.submatrix id (Fin.append e f)).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks 1 (Matrix.of fun i j ↦ u i (f j)) 0 (y.submatrix id f) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [A, u, Pi.single_apply, Matrix.one_apply, e.injective.eq_iff, hy, eq_comm]
    have hd : (A.submatrix id (Fin.append e f)).det = plucker y.row s := by
      rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock,
        Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, plucker_apply]
      rfl
    have h := v.det_submatrix_le_iSup_plucker A (Fin.append e f)
    rw [hd] at h
    exact h

private theorem iSup_plucker_append_single (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (e : Fin p ↪ ι) (y : Matrix (Fin q) ι K) :
    (⨆ s, v (plucker (Fin.append (fun i ↦ Pi.single (e i) 1) y.row) s)) =
      ⨆ s, v (plucker (fun i j ↦ if j ∈ range e then 0 else y i j) s) := by
  classical
  let u : Matrix (Fin p) ι K := Matrix.of fun i ↦ Pi.single (e i) 1
  let C : Matrix (Fin q) (Fin p) K := y.submatrix id e
  have hsub : (y - C * u).row = fun i j ↦ if j ∈ range e then 0 else y i j := by
    ext i j
    by_cases hj : j ∈ range e
    · obtain ⟨a, rfl⟩ := hj
      simp [C, u, Matrix.mul_apply, Pi.single_apply, e.injective.eq_iff]
    · have hz : ∀ a, e a ≠ j := fun a h ↦ hj ⟨a, h⟩
      simp [hj, C, u, Matrix.mul_apply, hz, Ne.symm]
  have hu : u.row = fun i ↦ Pi.single (e i) 1 := by ext; simp [u]
  have hs (s) := Matrix.plucker_append_sub_mul u y C s
  rw [hu] at hs
  calc
    _ = ⨆ s, v (plucker (Fin.append (fun i ↦ Pi.single (e i) 1) (y - C * u).row) s) := by
      simp_rw [hs]
    _ = ⨆ s, v (plucker (y - C * u).row s) :=
      v.iSup_plucker_append_single_eq hv e _ (by
        intro i a
        have h := congrFun (congrFun hsub i) (e a)
        simpa only [Matrix.row_apply, mem_range_self, ↓reduceIte] using h)
    _ = _ := by rw [hsub]

private theorem iSup_plucker_single_overlap_le {r : ℕ} (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (e : Fin p ↪ ι)
    (y : Fin q → ι → K) (z : Fin r → ι → K) :
    (⨆ s, v (plucker (Fin.append (fun i ↦ Pi.single (e i) 1) (Fin.append y z)) s)) ≤
      (⨆ s, v (plucker (Fin.append (fun i ↦ Pi.single (e i) 1) y) s)) *
        ⨆ s, v (plucker (Fin.append (fun i ↦ Pi.single (e i) 1) z) s) := by
  classical
  have ha := v.iSup_plucker_append_single hv e (Matrix.of (Fin.append y z))
  have hb := v.iSup_plucker_append_single hv e (Matrix.of y)
  have hc := v.iSup_plucker_append_single hv e (Matrix.of z)
  simp only [Matrix.row_eq_self, Equiv.symm_apply_apply, Matrix.of_apply] at ha hb hc
  rw [ha, hb, hc]
  have hfun : (fun i j ↦ if j ∈ range e then 0 else Fin.append y z i j) =
      Fin.append (fun i j ↦ if j ∈ range e then 0 else y i j)
        (fun i j ↦ if j ∈ range e then 0 else z i j) := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> simp
  rw [hfun]
  exact v.iSup_plucker_append_le hv _ _

omit [Finite ι] in
/-- If the column change `Q` kills `x` off the pivot columns `e`, then normalizing by the inverse of
the pivot matrix turns the rows of `x * Q` into coordinate vectors. -/
private theorem inv_submatrix_mul_row_eq_single [Fintype ι] {x : Matrix (Fin p) ι K}
    {e : Fin p ↪ ι} {Q : Matrix ι ι K} (he : (x.submatrix id e).det ≠ 0)
    (hred : ∀ i j, (x * Q) i j = if j ∈ range e then x i j else 0) :
    ((x.submatrix id e)⁻¹ * (x * Q)).row = fun i ↦ Pi.single (e i) 1 := by
  set P := x.submatrix id e
  ext i j
  by_cases hj : j ∈ range e
  · obtain ⟨b, rfl⟩ := hj
    have h := congrArg (fun M : Matrix (Fin p) (Fin p) K ↦ M i b)
      (Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr he))
    simpa [P, Matrix.mul_apply, hred, Pi.single_apply,
      e.injective.eq_iff, Matrix.one_apply, eq_comm] using h
  · have hz : ∀ b, e b ≠ j := fun b h ↦ hj ⟨b, h⟩
    simp [Matrix.mul_apply, hred, hj, hz, Ne.symm]

omit [Finite ι] in
/-- Changing coordinates by an integral invertible matrix `Q` preserves the exterior maximum norm
of a concatenation, and normalizing the first block by the inverse of a square matrix `P`
multiplies it by `v P⁻¹.det`. -/
theorem iSup_plucker_append_inv_mul_mul_eq [Fintype ι] {n : ℕ} (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (P : Matrix (Fin p) (Fin p) K) (x : Matrix (Fin p) ι K)
    (t : Matrix (Fin n) ι K) {Q Q' : Matrix ι ι K}
    (hQ : ∀ i j, v (Q i j) ≤ 1) (hQ' : ∀ i j, v (Q' i j) ≤ 1) (hQQ' : Q * Q' = 1) :
    (⨆ s, v (plucker (Fin.append (P⁻¹ * (x * Q)).row (t * Q).row) s)) =
      v P⁻¹.det * ⨆ s, v (plucker (Fin.append x.row t.row) s) := by
  have hleft := v.iSup_plucker_append_mul_left P⁻¹ 1 (x * Q) (t * Q)
  simp only [Matrix.one_mul, Matrix.det_one, map_one, mul_one] at hleft
  rw [hleft]
  congr 1
  have hfun : Fin.append (x * Q).row (t * Q).row =
      (Matrix.of (Fin.append x.row t.row) * Q).row := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> simp [Matrix.mul_apply]
  rw [hfun, v.iSup_plucker_mul_eq hv _ hQ hQ' hQQ']
  simp only [Matrix.row_eq_self, Equiv.symm_apply_apply]

/-- **The nonarchimedean overlapping-family inequality.** The exterior maximum
norm of a common family times that of the union is at most the product of the
exterior maximum norms of the two extensions. No independence, discreteness or
completeness hypothesis is required. -/
theorem iSup_plucker_overlap_le {r : ℕ} (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : Fin p → ι → K)
    (y : Fin q → ι → K) (z : Fin r → ι → K) :
    (⨆ s, v (plucker x s)) *
        (⨆ s, v (plucker (Fin.append x (Fin.append y z)) s)) ≤
      (⨆ s, v (plucker (Fin.append x y) s)) *
        ⨆ s, v (plucker (Fin.append x z) s) := by
  classical
  let _ := Fintype.ofFinite ι
  by_cases hx : LinearIndependent K x
  · obtain ⟨e, Q, Q', he, hm, hQQ', -, hQ, hQ', hred⟩ :=
      v.exists_integral_plucker_reduction hv (x := Matrix.of x) (by
        simpa only [Matrix.row_eq_self, Equiv.symm_apply_apply] using hx)
    let P := (Matrix.of x).submatrix id e
    let X := P⁻¹ * (Matrix.of x * Q)
    let Y := Matrix.of y * Q
    let Z := Matrix.of z * Q
    let a := v P⁻¹.det
    have ha : 0 < a := v.pos (Matrix.det_ne_zero_of_left_inverse
      (Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr he)))
    have hnorm : a * (⨆ s, v (plucker x s)) = 1 := by
      simp only [Matrix.row_eq_self, Equiv.symm_apply_apply] at hm
      rw [← hm]
      exact (v.map_mul _ _).symm.trans (by
        rw [Matrix.det_nonsing_inv_mul_det _ (isUnit_iff_ne_zero.mpr he), map_one])
    -- Integral column reduction supports the common rows on the pivot columns;
    -- normalizing their pivot matrix then makes them coordinate vectors.
    have hX : X.row = fun i ↦ Pi.single (e i) 1 :=
      inv_submatrix_mul_row_eq_single (x := Matrix.of x) he hred
    -- The same column change preserves every exterior norm; the row operation
    -- on the common block multiplies each extended exterior norm by a.
    have hright {n : ℕ} (t : Fin n → ι → K) :
        (⨆ s, v (plucker (Fin.append X.row (Matrix.of t * Q).row) s)) =
          a * ⨆ s, v (plucker (Fin.append x t) s) :=
      v.iSup_plucker_append_inv_mul_mul_eq hv P (Matrix.of x) (Matrix.of t) hQ hQ' hQQ'
    have hyz : (Matrix.of (Fin.append y z) * Q).row = Fin.append Y.row Z.row := by
      ext i j
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      rcases i with i | i <;> simp [Y, Z, Matrix.mul_apply]
    have h := v.iSup_plucker_single_overlap_le hv e Y.row Z.row
    rw [← hX, ← hyz, hright, hright, hright] at h
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ha)).mp
    calc
      _ = (a * (⨆ s, v (plucker x s))) *
          (a * ⨆ s, v (plucker (Fin.append x (Fin.append y z)) s)) := by ring
      _ = a * ⨆ s, v (plucker (Fin.append x (Fin.append y z)) s) := by rw [hnorm, one_mul]
      _ ≤ _ := h
      _ = _ := by ring
  · have hz : plucker x = 0 := not_ne_iff.mp ((plucker_ne_zero_iff x).not.mpr hx)
    have h : 0 ≤ (⨆ s, v (plucker (Fin.append x y) s)) *
        ⨆ s, v (plucker (Fin.append x z) s) :=
      mul_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _)
        (Real.iSup_nonneg_of_nonnegHomClass v _)
    simpa [hz] using h

end AbsoluteValue
