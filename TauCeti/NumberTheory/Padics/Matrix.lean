/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.LinearCombination
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.Topology.Instances.Matrix

/-!
# Matrices over the `p`-adic integers and the `p`-adic numbers

A matrix over `𝔽_p` with nonzero determinant, lifted entrywise to `ℤ_p`, has a unit determinant,
because its reduction modulo `p` has nonzero determinant. A matrix over `ℚ_p` becomes integral
after multiplication by a suitable power of `p`. A matrix over `ℤ_p` reduces to `0` modulo `p`
exactly when it is `p` times a matrix over `ℤ_p`.

Expanding `det (1 + m X) = 1 + m tr X + m² (⋯)` to first order shows that `X` has trace zero modulo
`p` whenever `1 + m X` has determinant `1` for a nonzero multiple `m` of `p`. Matrices congruent to
`g` modulo ever higher powers of `p` converge to `g`, since `‖p‖ < 1`.

## Main results

* `Matrix.isUnit_det_transpose_map_cast`: the transpose of the entrywise lift to `ℤ_p` of a matrix
  over `𝔽_p` with nonzero determinant has a unit determinant.
* `Matrix.exists_map_padicInt_eq_pow_smul`: some `p ^ k M` of a matrix `M` over `ℚ_p` has entries
  in `ℤ_p`.
* `Matrix.map_toZMod_nsmul_eq_zero`, `Matrix.exists_eq_nsmul_of_map_toZMod_eq_zero`: a matrix over
  `ℤ_p` reduces to `0` modulo `p` exactly when it is `p` times a matrix over `ℤ_p`.
* `Matrix.map_toZMod_add_nsmul`: adding `m • W` with `p ∣ m` does not change the reduction modulo
  `p`.
* `Matrix.trace_map_toZMod_eq_zero_of_det_one_add_nsmul`: if `p ∣ m`, `m ≠ 0` and
  `det (1 + m • X) = 1`, then `X` has trace zero modulo `p`.
* `Matrix.tendsto_of_eq_add_pow_nsmul`: if `g = h k + p ^ (k + 1) • Z k` for every `k`, then
  `h k → g`.
-/

public section

variable {p : ℕ} [Fact p.Prime]

namespace Matrix

/-- **The lifted degree-one matrix of a nondegenerate form has unit determinant.** The matrix
over `𝔽_p` with nonzero determinant, lifted entrywise to `ℤ_p` and transposed, has a unit
determinant, since its reduction modulo `p` has nonzero determinant. -/
theorem isUnit_det_transpose_map_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι (ZMod p)) (hB : B.det ≠ 0) :
    IsUnit (B.map (ZMod.cast : ZMod p → ℤ_[p]))ᵀ.det := by
  have h1 : (PadicInt.toZMod (p := p)).mapMatrix (B.map (ZMod.cast : ZMod p → ℤ_[p]))ᵀ = Bᵀ := by
    ext i j
    simp [ZMod.ringHom_map_cast]
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det,
    h1, Matrix.det_transpose]
  exact hB

/-- **Clearing denominators in a `p`-adic matrix**: some `p ^ k M` is the entrywise image of a
matrix over `ℤ_[p]`. -/
theorem exists_map_padicInt_eq_pow_smul {m n : Type*} [Finite m] [Finite n]
    (M : Matrix m n ℚ_[p]) :
    ∃ (k : ℕ) (A : Matrix m n ℤ_[p]), A.map ((↑) : ℤ_[p] → ℚ_[p]) = (p : ℚ_[p]) ^ k • M := by
  obtain ⟨k, hk⟩ := Padic.exists_forall_norm_pow_mul_le_one fun ij : m × n ↦ M ij.1 ij.2
  exact ⟨k, of fun i j ↦ ⟨_, hk (i, j)⟩, by ext; rfl⟩

/-- A multiple `m • X` of a matrix over `ℤ_p` with `p ∣ m` reduces to `0` modulo `p`. -/
theorem map_toZMod_nsmul_eq_zero {m n : Type*} {k : ℕ} (hk : p ∣ k) (X : Matrix m n ℤ_[p]) :
    (k • X).map PadicInt.toZMod = 0 := by
  ext i j
  simp [(ZMod.natCast_eq_zero_iff k p).2 hk]

/-- A matrix over `ℤ_p` that reduces to `0` modulo `p` is `p` times a matrix over `ℤ_p`. -/
theorem exists_eq_nsmul_of_map_toZMod_eq_zero {m n : Type*} {X : Matrix m n ℤ_[p]}
    (hX : X.map PadicInt.toZMod = 0) : ∃ Y : Matrix m n ℤ_[p], X = p • Y := by
  have h : ∀ i j, (p : ℤ_[p]) ∣ X i j := fun i j ↦
    (PadicInt.toZMod_eq_zero_iff_dvd _).1 (by simpa using congrFun (congrFun hX i) j)
  choose Y hY using h
  exact ⟨of Y, by ext i j; simp [hY i j, nsmul_eq_mul]⟩

/-- Adding `k • W` with `p ∣ k` to a matrix over `ℤ_p` does not change its reduction modulo `p`. -/
theorem map_toZMod_add_nsmul {m n : Type*} {k : ℕ} (hk : p ∣ k) (X W : Matrix m n ℤ_[p]) :
    (X + k • W).map PadicInt.toZMod = X.map PadicInt.toZMod := by
  rw [Matrix.map_add _ (map_add _), map_toZMod_nsmul_eq_zero hk, add_zero]

/-- If `1 + m • X` has determinant `1` for a nonzero multiple `m` of `p`, the reduction of `X`
modulo `p` has trace zero: `det (1 + m • X) = 1 + m tr X + m² e` gives `tr X = -m e`. -/
theorem trace_map_toZMod_eq_zero_of_det_one_add_nsmul {n : Type*} [Fintype n] [DecidableEq n]
    {m : ℕ} (hm : p ∣ m) (hm0 : m ≠ 0) {X : Matrix n n ℤ_[p]} (hX : (1 + m • X).det = 1) :
    (X.map PadicInt.toZMod).trace = 0 := by
  have hc0 : (m : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hm0
  obtain ⟨e, he⟩ : ∃ e, (1 + (m : ℤ_[p]) • X).det = 1 + X.trace * m + e * m ^ 2 :=
    ⟨_, det_one_add_smul _ X⟩
  rw [Nat.cast_smul_eq_nsmul, hX] at he
  have htr : X.trace = -(e * m) := mul_right_cancel₀ hc0 (by linear_combination -he)
  rw [← AddMonoidHom.map_trace, htr]
  simp [(ZMod.natCast_eq_zero_iff m p).2 hm]

open Filter Topology in
/-- Matrices `h k` over `ℤ_p` congruent to `g` modulo `p ^ (k + 1)` converge to `g`. -/
theorem tendsto_of_eq_add_pow_nsmul {m n : Type*} {g : Matrix m n ℤ_[p]}
    {h Z : ℕ → Matrix m n ℤ_[p]} (hZ : ∀ k, g = h k + p ^ (k + 1) • Z k) :
    Tendsto h atTop (𝓝 g) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hlim : Tendsto (fun k : ℕ ↦ ((p : ℝ)⁻¹) ^ (k + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hp.le)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))).comp
      (tendsto_add_atTop_nat 1)
  refine tendsto_iff_tendsto_apply.2 fun i j ↦ tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hlim)
  have hk := congrFun (congrFun (hZ k) i) j
  rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Nat.cast_pow] at hk
  rw [hk, sub_add_cancel_left, norm_neg, norm_mul, norm_pow, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

end Matrix
