/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Level sets of complex quadratic forms are path-connected

Let `Q` be a nondegenerate quadratic form on a complex vector space `V` of dimension at least two.
Every level set `{v | Q v = c}` is path-connected. Unlike the real case, there is no signature to
separate components: the complex quadric `z₁² + ⋯ + zₙ² = 1` deformation retracts onto the real
unit sphere, which is path-connected in dimension at least two.

The level `0` is the isotropic cone, which is star-shaped about the origin. For `c ≠ 0` the proof
diagonalizes `Q` to the sum of squares and rescales the level `c` to `1`. For `z` on the
quadric write `z = x + i y` with `x, y` real. Comparing real and imaginary parts of `∑ zⱼ² = 1`
gives `‖x‖² = 1 + ‖y‖²` and `⟪x, y⟫ = 0`, so for `0 ≤ s ≤ 1`

`(x + i s y) / √(1 + (1 - s²) ‖y‖²)`

stays on the quadric. At `s = 1` it is `z`, and at `s = 0` it is the real unit vector `x / ‖x‖`.

The dimension bound is sharp: in dimension one the level set `{z | z² = c}` with `c ≠ 0` consists
of the two square roots of `c`.

This is the topological input for path-connectedness of the complex Spin groups in dimension at
least two, where reflection-pair lifts of unit vectors generate the Spin group.

## Main result

* `QuadraticForm.isPathConnected_setOf_apply_eq`: a level set of a nondegenerate complex
  quadratic form in dimension at least two is path-connected.
-/

public section

open Complex Module Set

namespace QuadraticForm

/-- Expanding `∑ (xⱼ + i s yⱼ)²` into its real and imaginary parts. -/
private theorem sum_ofReal_add_mul_I_mul_self {n : ℕ} (x y : Fin n → ℝ) (s : ℝ) :
    ∑ j, ((x j : ℂ) + s * y j * I) * ((x j : ℂ) + s * y j * I) =
      ((∑ j, x j ^ 2 - s ^ 2 * ∑ j, y j ^ 2 : ℝ) : ℂ) + ((2 * s * ∑ j, x j * y j : ℝ) : ℂ) * I := by
  have h (j : Fin n) : ((x j : ℂ) + s * y j * I) * ((x j : ℂ) + s * y j * I) =
      ((x j ^ 2 - s ^ 2 * y j ^ 2 : ℝ) : ℂ) + ((2 * s * (x j * y j) : ℝ) : ℂ) * I := by
    push_cast
    linear_combination ((s : ℂ) ^ 2 * (y j : ℂ) ^ 2) * I_sq
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, ← ofReal_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

/-- Every point `z = x + i y` of the complex unit quadric `∑ zⱼ² = 1` is joined, inside the quadric,
to the real unit vector `x / ‖x‖`, along `s ↦ (x + i s y) / √(1 + (1 - s²) ‖y‖²)`. -/
private theorem exists_joinedIn_ofReal_of_sum_mul_self_eq_one {n : ℕ} {z : Fin n → ℂ}
    (hz : ∑ j, z j * z j = 1) :
    ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧
      JoinedIn {z : Fin n → ℂ | ∑ j, z j * z j = 1} (fun j ↦ (w j : ℂ)) z := by
  set x : Fin n → ℝ := fun j ↦ (z j).re
  set y : Fin n → ℝ := fun j ↦ (z j).im
  set B := ∑ j, y j ^ 2
  -- The real and imaginary parts of `∑ zⱼ² = 1` say `‖x‖² - ‖y‖² = 1` and `⟪x, y⟫ = 0`.
  have hz' : z = fun j ↦ (x j : ℂ) + (1 : ℝ) * y j * I := by
    ext1 j
    simp [x, y, re_add_im]
  rw [hz', sum_ofReal_add_mul_I_mul_self] at hz
  have hre := congrArg re hz
  have him := congrArg im hz
  simp only [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, one_re, add_im,
    ofReal_im, im_ofReal_mul, I_im, mul_one, zero_add, one_im, one_pow, one_mul] at hre him
  have hxy : ∑ j, x j * y j = 0 := by linarith
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ ↦ sq_nonneg (y j)
  have hpos (s : ℝ) (hs : s ∈ unitInterval) : 0 < 1 + (1 - s ^ 2) * B := by
    have : 0 ≤ (1 - s ^ 2) * B := mul_nonneg (by nlinarith [hs.1, hs.2]) hB
    linarith
  let c : ℝ → ℝ := fun s ↦ (Real.sqrt (1 + (1 - s ^ 2) * B))⁻¹
  have hc (s : ℝ) (hs : s ∈ unitInterval) : c s * c s * (1 + (1 - s ^ 2) * B) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt (hpos s hs).le, inv_mul_cancel₀ (hpos s hs).ne']
  let f : ℝ → Fin n → ℂ := fun s j ↦ (c s : ℂ) * ((x j : ℂ) + s * y j * I)
  refine ⟨WithLp.toLp 2 fun j ↦ c 0 * x j, ?_, JoinedIn.ofLine (f := f) ?_ ?_ ?_ ?_⟩
  · have h0 := hc 0 ⟨le_rfl, zero_le_one⟩
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum]
    nlinarith
  · refine continuousOn_pi.2 fun j ↦ ContinuousOn.mul ?_ (by fun_prop)
    refine continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀ (by fun_prop) ?_)
    exact fun s hs ↦ (Real.sqrt_pos.2 (hpos s hs)).ne'
  · ext1 j
    simp [f]
  · ext1 j
    simp [f, c, x, y, re_add_im]
  · rintro _ ⟨s, hs, rfl⟩
    have h : c s * c s * (∑ j, x j ^ 2 - s ^ 2 * B) = 1 := by
      rw [← hc s hs]
      congr 1
      linarith
    simp only [f, mem_ofPred_eq, mul_mul_mul_comm _ ((x _ : ℂ) + _), ← Finset.mul_sum,
      sum_ofReal_add_mul_I_mul_self, hxy, mul_zero, ofReal_zero, zero_mul, add_zero]
    exact_mod_cast h

/-- The complex unit quadric `∑ zⱼ² = 1` is path-connected in dimension at least two. -/
private theorem isPathConnected_setOf_sum_mul_self_eq_one {n : ℕ} (hn : 2 ≤ n) :
    IsPathConnected {z : Fin n → ℂ | ∑ j, z j * z j = 1} := by
  set S := {z : Fin n → ℂ | ∑ j, z j * z j = 1}
  -- The real unit sphere, read in complex coordinates, is a path-connected subset of `S`.
  let r : EuclideanSpace ℝ (Fin n) → Fin n → ℂ := fun x j ↦ (x j : ℂ)
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  have hR : IsPathConnected (r '' Metric.sphere 0 1) :=
    (isPathConnected_sphere hrank 0 zero_le_one).image (by fun_prop)
  have hRS : r '' Metric.sphere 0 1 ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ∑ j, x j ^ 2 = 1 := by
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hx
      simpa only [Real.norm_eq_abs, sq_abs] using hx
    simp only [S, r, mem_ofPred_eq, ← sq]
    exact_mod_cast hx'
  obtain ⟨w₀, hw₀, hR'⟩ := hR
  refine ⟨w₀, hRS hw₀, fun {z} hz ↦ ?_⟩
  obtain ⟨w, hw, hwz⟩ := exists_joinedIn_ofReal_of_sum_mul_self_eq_one hz
  exact ((hR' ⟨w, mem_sphere_zero_iff_norm.2 hw, rfl⟩).mono hRS).trans hwz

/-- **Level sets of a complex quadratic form are path-connected.** For a nondegenerate quadratic
form `Q` on a complex vector space of dimension at least two, every level set `{v | Q v = c}` is
path-connected. -/
theorem isPathConnected_setOf_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [TopologicalSpace V] [IsModuleTopology ℂ V]
    {Q : QuadraticForm ℂ V} (hQ : Q.Nondegenerate) (hV : 2 ≤ finrank ℂ V) (c : ℂ) :
    IsPathConnected {v | Q v = c} := by
  have _ := IsModuleTopology.toContinuousAdd ℂ V
  rcases eq_or_ne c 0 with rfl | hc
  · -- The isotropic cone is joined to the origin along rays.
    refine ⟨0, by simp, fun {v} (hv : Q v = 0) ↦ JoinedIn.ofLine (f := fun t : ℝ ↦ (t : ℂ) • v)
      (by fun_prop) (by simp) (by simp) ?_⟩
    rintro _ ⟨t, -, rfl⟩
    exact (QuadraticMap.map_smul Q (t : ℂ) v).trans (by rw [hv, smul_zero])
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hc (by simp [← ha])
  have hset : {v | Q v = c} =
      (fun z ↦ a • e.symm z) '' {z : Fin (finrank ℂ V) → ℂ | ∑ j, z j * z j = 1} := by
    ext v
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro hv
      refine ⟨e (a⁻¹ • v), ?_, by simp [smul_smul, ha0]⟩
      have := e.map_app (a⁻¹ • v)
      simp only [QuadraticMap.weightedSumSquares_apply, Pi.one_apply, one_smul] at this
      rw [this, QuadraticMap.map_smul, hv, ← ha, smul_eq_mul]
      field_simp
    · rintro ⟨z, hz, rfl⟩
      have := e.symm.map_app z
      simp only [QuadraticMap.weightedSumSquares_apply, Pi.one_apply, one_smul] at this
      rw [QuadraticMap.map_smul, this, hz, ← ha]
      ring
  rw [hset]
  exact (isPathConnected_setOf_sum_mul_self_eq_one hV).image <|
    continuous_const.smul
      (IsModuleTopology.continuous_of_linearMap e.symm.toLinearEquiv.toLinearMap)

end QuadraticForm
