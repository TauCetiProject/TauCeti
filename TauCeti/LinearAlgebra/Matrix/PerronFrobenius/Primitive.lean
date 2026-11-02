/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Normed.Algebra.GelfandFormula
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible

/-!
# The Perron–Frobenius theorem for primitive matrices

A square real matrix `A` is primitive (`Matrix.IsPrimitive`) when its entries are nonnegative and
some positive power of it is strictly positive. A primitive matrix is irreducible
(`Matrix.IsPrimitive.isIrreducible`), so it has a strictly positive eigenvector for its spectral
radius `r`, the Perron root, which is a simple eigenvalue
(`TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible`). Primitivity adds that `r` is the only
eigenvalue of modulus `r`: every other complex eigenvalue `μ` satisfies `‖μ‖ < r`. Consequently the
powers of `A / r` converge, to the rank one projection `v uᵀ / (u ⬝ v)` built from right and left
Perron eigenvectors `v` and `u`.

The proof of strict dominance starts with an irreducible matrix and a complex eigenvector `z` for
an eigenvalue of modulus `r`. Taking moduli entrywise gives `r ‖z‖ ≤ A ‖z‖`, so by subinvariance
the vector of moduli `‖z‖` is an eigenvector for `r`. If `A` is strictly positive, equality in the
triangle inequality for a single row of `A z` forces all entries of `z` to have the same argument,
so `z` is a complex multiple of the Perron eigenvector and its eigenvalue is `r`. A primitive
matrix reduces to this case through a strictly positive power. Convergence of the powers follows
from Gelfand's formula: `A / r` minus the Perron projection has spectral radius less than one.

## Main results

* `Matrix.IsIrreducible.mulVec_norm_eq_smul_of_norm_eq`: for an irreducible matrix with Perron
  root `r`, the entrywise moduli of a complex eigenvector for an eigenvalue of modulus `r` form an
  eigenvector for `r`.
* `Matrix.IsPrimitive.exists_eq_smul_of_mulVec_eq_smul_of_norm_eq`: for a primitive matrix, every
  complex eigenvector for an eigenvalue of modulus `r` is a multiple of the Perron eigenvector.
* `Matrix.IsPrimitive.eq_of_mulVec_eq_smul_of_norm_eq`: the only eigenvalue of modulus `r` of a
  primitive matrix is `r`.
* `Matrix.IsPrimitive.norm_lt_of_mulVec_eq_smul`: every other complex eigenvalue of a primitive
  matrix has modulus strictly less than `r`.
* `Matrix.IsPrimitive.tendsto_pow_smul`: the powers of `r⁻¹ • A` converge to the Perron projection
  `(u ⬝ᵥ v)⁻¹ • vecMulVec v u`.

The strict dominance statements are also stated for strictly positive matrices, which are
primitive by `Matrix.isPrimitive_of_pos`.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Theorems 1.1 and 1.2
  (Perron–Frobenius for primitive matrices) and Section 1.1 (the convergence of `(A / r) ^ k`).
-/

public section

open scoped Matrix ComplexConjugate
open Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A matrix with strictly positive entries over a linearly ordered ring is primitive: its first
power is strictly positive. -/
theorem isPrimitive_of_pos {R : Type*} [Ring R] [LinearOrder R] [DecidableEq n] {A : Matrix n n R}
    (hA : ∀ i j, 0 < A i j) : A.IsPrimitive :=
  ⟨fun i j => (hA i j).le, 1, one_pos, by simpa using hA⟩

section Real

variable {A : Matrix n n ℝ} {u v : n → ℝ} {r : ℝ} {z : n → ℂ} {μ : ℂ}

/-- For an irreducible real matrix `A` with a strictly positive eigenvector for `r`, the vector of
entrywise moduli of a complex eigenvector of `A` for an eigenvalue of modulus `r` is an eigenvector
of `A` for `r`. -/
theorem IsIrreducible.mulVec_norm_eq_smul_of_norm_eq (hA : A.IsIrreducible) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : ‖μ‖ = r) :
    A *ᵥ (fun i => ‖z i‖) = r • fun i => ‖z i‖ := by
  refine hA.mulVec_eq_smul_of_smul_le_mulVec hv hAv fun i => ?_
  calc (r • fun i => ‖z i‖) i = ‖(A.map (↑) *ᵥ z) i‖ := by simp [hAz, hμ]
    _ ≤ ∑ j, ‖((A i j : ℝ) : ℂ) * z j‖ := norm_sum_le _ _
    _ = (A *ᵥ fun i => ‖z i‖) i := by
      simp [mulVec, dotProduct, Complex.norm_real, abs_of_nonneg (hA.nonneg i _)]

/-- The coercion of `Complex.ofRealHom` to a function, in the form `Matrix.map` uses below. -/
private theorem coe_ofRealHom : (Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal :=
  rfl

/-- The complexification of a real eigenvector is an eigenvector of the complexified matrix. -/
private theorem map_ofReal_mulVec_ofReal (hAv : A *ᵥ v = r • v) :
    A.map (↑) *ᵥ (fun i => (v i : ℂ)) = (r : ℂ) • fun i => (v i : ℂ) := by
  ext i
  have h := (RingHom.map_mulVec Complex.ofRealHom A v i).symm
  rw [hAv, coe_ofRealHom] at h
  simpa [Function.comp_def] using h

/-- If a complex multiple of a real eigenvector of `A` for `r` is a nonzero eigenvector of the
complexified matrix for `μ`, then `μ = r`. -/
private theorem eq_of_mulVec_smul_ofReal (hAv : A *ᵥ v = r • v) {c : ℂ}
    (hz : (c • fun i => (v i : ℂ)) ≠ 0)
    (hAz : A.map (↑) *ᵥ (c • fun i => (v i : ℂ)) = μ • c • fun i => (v i : ℂ)) : μ = r := by
  rw [mulVec_smul, map_ofReal_mulVec_ofReal hAv, smul_comm] at hAz
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
  exact mul_right_cancel₀ hj (congrFun hAz j).symm

/-- For a strictly positive real matrix `A` with a strictly positive eigenvector `v` for `r`, every
complex eigenvector of `A` for an eigenvalue of modulus `r` is a complex multiple of `v`. -/
theorem exists_eq_smul_of_mulVec_eq_smul_of_norm_eq (hA : ∀ i j, 0 < A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : ‖μ‖ = r) :
    ∃ c : ℂ, z = c • fun i => (v i : ℂ) := by
  classical
  set y : n → ℝ := fun i => ‖z i‖ with hy
  have hAy : A *ᵥ y = r • y :=
    (isPrimitive_of_pos hA).isIrreducible.mulVec_norm_eq_smul_of_norm_eq hv hAv hAz hμ
  obtain ⟨c, hc⟩ := exists_eq_smul_of_mulVec_eq_smul hA hv hAv hAy
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hy0 : y ≠ 0 := fun h => hz (funext fun i => norm_eq_zero.1 (congrFun h i))
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hz
  -- The `i₀`-th entry `s` of `A z` has modulus `∑ j, A i₀ j ‖z j‖`: the triangle inequality for it
  -- is an equality.
  set s : ℂ := (A.map (↑) *ᵥ z) i₀ with hs
  have hsum : s = ∑ j, (A i₀ j : ℂ) * z j := rfl
  have hnorm : ‖s‖ = (A *ᵥ y) i₀ := by
    rw [hAy, hs, hAz]
    simp [hy, hμ]
  have hpos : 0 < (A *ᵥ y) i₀ := mulVec_pos hA (fun i => norm_nonneg _) hy0 i₀
  -- Rotating by `conj s` makes every term `conj s * z j` a nonnegative real.
  have hre : ∀ j, (conj s * z j).re = ‖conj s * z j‖ := by
    have h : ∑ j, A i₀ j * (‖conj s * z j‖ - (conj s * z j).re) = 0 := by
      have h1 : ∑ j, A i₀ j * (conj s * z j).re = ‖s‖ ^ 2 := by
        have : conj s * s = ∑ j, (A i₀ j : ℂ) * (conj s * z j) := by
          rw [hsum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        have h2 := congrArg Complex.re this
        rw [Complex.re_sum, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
        simpa [Complex.re_ofReal_mul, ← Complex.ofReal_pow] using h2.symm
      have h3 : ∑ j, A i₀ j * ‖conj s * z j‖ = ‖s‖ ^ 2 := by
        simp only [norm_mul, Complex.norm_conj]
        rw [sq, hnorm]
        simp [mulVec, dotProduct, hy, Finset.mul_sum, mul_left_comm]
      simp only [mul_sub, Finset.sum_sub_distrib, h1, h3, sub_self]
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (hA i₀ j).le (sub_nonneg.2 (Complex.re_le_norm _))).1 h j (Finset.mem_univ j)
    have := (mul_eq_zero.1 this).resolve_left (hA i₀ j).ne'
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hpos.ne hnorm
  have hs0' : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs0
  -- So `z j = (s / ‖s‖) ‖z j‖`, and `‖z‖ = c v`.
  refine ⟨s / ‖s‖ * c, funext fun j => ?_⟩
  have h := Complex.eq_coe_norm_of_nonneg (Complex.re_eq_norm.1 (hre j))
  rw [norm_mul, Complex.norm_conj] at h
  have hyj : (‖z j‖ : ℂ) = c * v j := by exact_mod_cast congrFun hc j
  have key : (‖s‖ : ℂ) * (‖s‖ : ℂ) * z j = s * ((‖s‖ * ‖z j‖ : ℝ) : ℂ) := by
    rw [← h, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast at key
  rw [hyj] at key
  apply mul_left_cancel₀ (mul_ne_zero hs0' hs0')
  rw [key]
  field_simp

/-- For a strictly positive real matrix with a strictly positive eigenvector for `r`, the only
complex eigenvalue of modulus `r` is `r` itself. -/
theorem eq_of_mulVec_eq_smul_of_norm_eq (hA : ∀ i j, 0 < A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hz : z ≠ 0) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : ‖μ‖ = r) :
    μ = r := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_mulVec_eq_smul_of_norm_eq hA hv hAv hAz hμ
  exact eq_of_mulVec_smul_ofReal hAv hz hAz

/-- **Perron–Frobenius for positive matrices**, strict dominance: every complex eigenvalue of a
strictly positive real matrix other than its Perron root `r` has modulus strictly less than `r`. -/
theorem norm_lt_of_mulVec_eq_smul (hA : ∀ i j, 0 < A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hz : z ≠ 0) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : μ ≠ r) :
    ‖μ‖ < r :=
  (norm_le_of_mulVec_le_smul (fun i j => (hA i j).le) hv hAv.le hz hAz).lt_of_ne
    fun h => hμ (eq_of_mulVec_eq_smul_of_norm_eq hA hv hAv hz hAz h)

variable [DecidableEq n]

/-- For a primitive real matrix `A` with a strictly positive eigenvector `v` for `r`, every complex
eigenvector of `A` for an eigenvalue of modulus `r` is a complex multiple of `v`. -/
theorem IsPrimitive.exists_eq_smul_of_mulVec_eq_smul_of_norm_eq (hA : A.IsPrimitive)
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : ‖μ‖ = r) :
    ∃ c : ℂ, z = c • fun i => (v i : ℂ) := by
  obtain ⟨-, k, -, hk⟩ := hA
  -- Pass to the strictly positive power `A ^ k`, with eigenvalues `r ^ k` and `μ ^ k`.
  refine Matrix.exists_eq_smul_of_mulVec_eq_smul_of_norm_eq hk hv (pow_mulVec_eq_pow_smul hAv k) ?_
    (by rw [norm_pow, hμ])
  have h := map_pow Complex.ofRealHom.mapMatrix A k
  simp only [RingHom.mapMatrix_apply, coe_ofRealHom] at h
  rw [h]
  exact pow_mulVec_eq_pow_smul hAz k

/-- For a primitive real matrix with a strictly positive eigenvector for `r`, the only complex
eigenvalue of modulus `r` is `r` itself. -/
theorem IsPrimitive.eq_of_mulVec_eq_smul_of_norm_eq (hA : A.IsPrimitive) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hz : z ≠ 0) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : ‖μ‖ = r) :
    μ = r := by
  obtain ⟨c, rfl⟩ := hA.exists_eq_smul_of_mulVec_eq_smul_of_norm_eq hv hAv hAz hμ
  exact eq_of_mulVec_smul_ofReal hAv hz hAz

/-- **Perron–Frobenius for primitive matrices**, strict dominance: every complex eigenvalue of a
primitive real matrix other than its Perron root `r` has modulus strictly less than `r`. -/
theorem IsPrimitive.norm_lt_of_mulVec_eq_smul (hA : A.IsPrimitive) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hz : z ≠ 0) (hAz : A.map (↑) *ᵥ z = μ • z) (hμ : μ ≠ r) :
    ‖μ‖ < r :=
  (norm_le_of_mulVec_le_smul hA.nonneg hv hAv.le hz hAz).lt_of_ne
    fun h => hμ (hA.eq_of_mulVec_eq_smul_of_norm_eq hv hAv hz hAz h)

/-- **Perron–Frobenius for primitive matrices**, convergence of powers: if `A` is a primitive real
matrix with a strictly positive eigenvector `v` for `r`, and `u ≠ 0` is a left eigenvector of `A`
for `r`, then the powers of `r⁻¹ • A` converge to the rank one projection
`(u ⬝ᵥ v)⁻¹ • vecMulVec v u` onto the line spanned by `v`. -/
theorem IsPrimitive.tendsto_pow_smul (hA : A.IsPrimitive) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hu : u ≠ 0) (huA : u ᵥ* A = r • u) :
    Tendsto (fun m : ℕ => (r⁻¹ • A) ^ m) atTop (𝓝 ((u ⬝ᵥ v)⁻¹ • vecMulVec v u)) := by
  have : Nonempty n := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hu
    exact ⟨i⟩
  -- The Perron root is nonzero, since a strictly positive power of `A` maps `v` to `r ^ k v`.
  have hr : r ≠ 0 := by
    rintro rfl
    obtain ⟨-, k, hk0, hk⟩ := hA
    obtain ⟨i⟩ := ‹Nonempty n›
    have h := mulVec_pos hk (fun j => (hv j).le) (fun h => (hv i).ne' (congrFun h i)) i
    rw [pow_mulVec_eq_pow_smul hAv k, zero_pow hk0.ne', zero_smul] at h
    exact h.false
  -- The left eigenvector `u` is a multiple of a strictly positive one, so `u ⬝ᵥ v ≠ 0`.
  have huv : u ⬝ᵥ v ≠ 0 := by
    obtain ⟨w, hw, hwA⟩ := hA.isIrreducible.exists_vecMul_eq_smul hv hAv
    obtain ⟨c, rfl⟩ := hA.isIrreducible.transpose.exists_eq_smul_of_mulVec_eq_smul hw
      (by rw [mulVec_transpose, hwA]) (by rw [mulVec_transpose, huA])
    have hc : c ≠ 0 := by
      rintro rfl
      exact hu (zero_smul _ _)
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero hc
      (Finset.sum_pos (fun i _ => mul_pos (hw i) (hv i)) Finset.univ_nonempty).ne'
  set T : Matrix n n ℝ := r⁻¹ • A with hT
  set P : Matrix n n ℝ := (u ⬝ᵥ v)⁻¹ • vecMulVec v u with hP
  have hTv : T *ᵥ v = v := by rw [hT, smul_mulVec, hAv, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have huT : u ᵥ* T = u := by rw [hT, vecMul_smul, huA, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have hPv : P *ᵥ v = v := by
    rw [hP, smul_mulVec, vecMulVec_mulVec, dotProduct_comm u v]
    simp [smul_smul, inv_mul_cancel₀ (dotProduct_comm u v ▸ huv)]
  have hTP : T * P = P := by rw [hP, Matrix.mul_smul, mul_vecMulVec, hTv]
  have hPT : P * T = P := by rw [hP, Matrix.smul_mul, vecMulVec_mul, huT]
  have hPP : P * P = P := by
    rw [hP, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, smul_smul, vecMulVec_smul,
      smul_smul, mul_assoc, inv_mul_cancel₀ huv, mul_one]
  -- For `m ≥ 1`, `T ^ m - P = (T - P) ^ m`.
  have hTmP : ∀ m : ℕ, T ^ m * P = P := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hTP, ih]
  have hpow : ∀ m : ℕ, (T - P) ^ (m + 1) = T ^ (m + 1) - P := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, sub_mul, mul_sub, mul_sub, ← pow_succ, hTmP, hPT, hPP]
      abel
  -- It suffices that `(T - P) ^ m → 0`, which follows from Gelfand's formula once the
  -- complexification `B` of `T - P` has spectral radius less than one.
  suffices h : Tendsto (fun m : ℕ => (T - P) ^ m) atTop (𝓝 0) by
    have h' := ((h.comp (tendsto_add_atTop_nat 1)).add_const P)
    simp only [Function.comp_def, hpow, sub_add_cancel, zero_add] at h'
    exact (tendsto_add_atTop_iff_nat 1).1 h'
  set B : Matrix n n ℂ := (T - P).map (↑) with hB
  have hBpow : ∀ m : ℕ, (B ^ m).map Complex.re = (T - P) ^ m := fun m => by
    have h := map_pow Complex.ofRealHom.mapMatrix (T - P) m
    simp only [RingHom.mapMatrix_apply, coe_ofRealHom] at h
    rw [hB, ← h, map_map]
    simp [Function.comp_def]
  -- Every eigenvalue `k` of `B` has modulus less than one.
  have hspec : ∀ k ∈ spectrum ℂ B, ‖k‖ < 1 := by
    intro k hk
    obtain ⟨z, hz, hBz⟩ := mem_spectrum_iff_exists_mulVec_eq_smul.1 hk
    by_cases hk0 : k = 0
    · simp [hk0]
    have hmap : ∀ M N : Matrix n n ℝ, (M * N).map ((↑) : ℝ → ℂ) = M.map (↑) * N.map (↑) :=
      fun M N => by simpa [coe_ofRealHom] using map_mul Complex.ofRealHom.mapMatrix M N
    -- `P B = 0`, so the eigenvector `z` is killed by `P`, and is an eigenvector of `A` for `r k`.
    have hPB : P.map ((↑) : ℝ → ℂ) * B = 0 := by
      rw [hB, ← hmap, mul_sub, hPT, hPP, sub_self]
      simp
    have hPz : P.map ((↑) : ℝ → ℂ) *ᵥ z = 0 := by
      have h := congrArg (P.map ((↑) : ℝ → ℂ) *ᵥ ·) hBz
      simp only [mulVec_mulVec, hPB, zero_mulVec, mulVec_smul] at h
      exact (smul_eq_zero.1 h.symm).resolve_left hk0
    have hAz : A.map (↑) *ᵥ z = ((r : ℂ) * k) • z := by
      have hAT : A.map ((↑) : ℝ → ℂ) = (r : ℂ) • (B + P.map (↑)) := by
        rw [hB, ← Matrix.map_add _ Complex.ofReal_add, sub_add_cancel, hT]
        ext i j
        simp [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hr)]
      rw [hAT, smul_mulVec, add_mulVec, hBz, hPz, add_zero, smul_smul]
    -- By strict dominance, `‖r k‖ < r`, since `‖r k‖ = r` would make `z` a multiple of `v`.
    have hlt : ‖(r : ℂ) * k‖ < r := by
      refine (norm_le_of_mulVec_le_smul hA.nonneg hv hAv.le hz hAz).lt_of_ne fun h => ?_
      obtain ⟨c, rfl⟩ := hA.exists_eq_smul_of_mulVec_eq_smul_of_norm_eq hv hAv hAz h
      refine hz ?_
      have hPv' : P.map ((↑) : ℝ → ℂ) *ᵥ (fun i => (v i : ℂ)) = fun i => (v i : ℂ) := by
        ext i
        have h := (RingHom.map_mulVec Complex.ofRealHom P v i).symm
        rw [hPv, coe_ofRealHom] at h
        simpa [Function.comp_def] using h
      rw [mulVec_smul, hPv'] at hPz
      exact hPz
    have hr0 : 0 < r := (norm_nonneg _).trans_lt hlt
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le] at hlt
    exact (mul_lt_iff_lt_one_right hr0).1 hlt
  -- Gelfand's formula, for the `L∞` operator norm, whose topology is the entrywise one.
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  have hρ : spectralRadius ℂ B < 1 := by
    obtain ⟨k, hk, hkB⟩ := spectrum.exists_nnnorm_eq_spectralRadius B
    rw [← hkB]
    exact_mod_cast hspec k hk
  have hlim : Tendsto (fun m : ℕ => B ^ m) atTop (𝓝 0) :=
    spectrum.tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one hρ
  have hre := ((continuous_id.matrix_map Complex.continuous_re).tendsto 0).comp hlim
  simpa [Function.comp_def, hBpow] using hre

end Real

end Matrix
