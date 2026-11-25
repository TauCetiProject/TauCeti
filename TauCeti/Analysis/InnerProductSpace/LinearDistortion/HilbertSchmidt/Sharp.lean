/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion.HilbertSchmidt
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
import TauCeti.Analysis.Real.Sqrt

/-!
# Sharpness of `q_O ≤ n^{n/2} q_S`

The outer distortion `q_O` and the Hilbert–Schmidt distortion `q_S` of a linear map satisfy
`q_S ≤ q_O ≤ n^{n/2} q_S` (`Orientation.hilbertSchmidtDistortion_le_outerDistortion`,
`Orientation.outerDistortion_le_mul_hilbertSchmidtDistortion`). This file shows that the
constant `n^{n/2}` cannot be lowered, using the stretch `diag(1, ε, …, ε)` in an orthonormal
basis `b` (`OrthonormalBasis.scaleTail`): for `0 < ε ≤ 1` its outer distortion is
`n^{n/2} / (1 + (n - 1) ε²)^{n/2}` times its Hilbert–Schmidt distortion, and this factor tends to
`n^{n/2}` as `ε → 0`.

It also records worked examples on the plane and in dimension three: `q_O / q_S = 2 / (1 + ε²) → 2`
for `diag(1, ε)`, never reaching `2`, and `q_O / q_S = 3^{3/2} / (1 + 2ε²)^{3/2} → 3^{3/2}` for
`diag(1, ε, ε)`.

## Main declarations

* `OrthonormalBasis.scaleTail`: the stretch `diag(1, ε, …, ε)`, which fixes `b 0` and multiplies
  the other basis vectors by `ε`.
* `OrthonormalBasis.outerDistortion_scaleTail`: its outer distortion is
  `n^{n/2} / (1 + (n - 1) ε²)^{n/2}` times its Hilbert–Schmidt distortion.
* `Orientation.exists_mul_hilbertSchmidtDistortion_lt_outerDistortion`: for every `c < n^{n/2}`
  there is a linear map with `J(A) > 0` and `c q_S(A) < q_O(A)`.

## References

* O. Martio, S. Rickman and J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), Section 2, (2.24).
-/

public section

noncomputable section

open Module Matrix LinearMap Filter Topology TauCeti.UnitarilyInvariantSeminorm
open scoped ENNReal

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- The stretch `diag(1, ε, …, ε)` in an orthonormal basis `b`: it fixes `b 0` and multiplies the
other basis vectors by `ε`. For `ε → 0` it is the extremal family for `q_O ≤ n^{n/2} q_S`. -/
def scaleTail (b : OrthonormalBasis (Fin n) ℝ V) (ε : ℝ) : V →ₗ[ℝ] V :=
  toLin b.toBasis b.toBasis (diagonal fun i ↦ if (i : ℕ) = 0 then 1 else ε)

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = n)] in
theorem scaleTail_def (b : OrthonormalBasis (Fin n) ℝ V) (ε : ℝ) :
    b.scaleTail ε =
      toLin b.toBasis b.toBasis (diagonal fun i ↦ if (i : ℕ) = 0 then 1 else ε) :=
  (rfl)

variable (b : OrthonormalBasis (Fin n) ℝ V) {ε : ℝ}

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = n)] in
/-- `diag(1, ε, …, ε)` fixes `b 0` and multiplies every other basis vector `b i` by `ε`. -/
theorem scaleTail_apply (ε : ℝ) (i : Fin n) :
    b.scaleTail ε (b i) = if (i : ℕ) = 0 then b i else ε • b i := by
  rw [scaleTail_def, ← b.coe_toBasis, toLin_self]
  simp [diagonal_apply]

omit [Fact (finrank ℝ V = n)] in
/-- The singular values of `diag(1, ε, …, ε)` for `0 ≤ ε ≤ 1` are `1, ε, …, ε`. -/
theorem singularValues_scaleTail (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {k : ℕ}
    (hk : k < n) :
    (b.scaleTail ε).singularValues k = if k = 0 then 1 else ε := by
  have hanti : Antitone fun k : Fin n ↦
      ‖(fun i : Fin n ↦ if (i : ℕ) = 0 then (1 : ℝ) else ε) (Equiv.refl (Fin n) k)‖ := by
    intro i j hij
    simp only [Equiv.refl_apply]
    by_cases hj : (j : ℕ) = 0
    · have hi : (i : ℕ) = 0 := by have := Fin.le_def.mp hij; omega
      simp [hi, hj]
    · by_cases hi : (i : ℕ) = 0 <;> simp [hi, hj, abs_of_nonneg hε₀, hε₁]
  have h := singularValues_toLin_diagonal b (fun i : Fin n ↦ if (i : ℕ) = 0 then (1 : ℝ) else ε)
    (Equiv.refl _) hanti ⟨k, hk⟩
  rw [scaleTail_def, h]
  by_cases hk0 : k = 0 <;> simp [hk0, abs_of_nonneg hε₀]

omit [FiniteDimensional ℝ V] in
/-- The oriented Jacobian of `diag(1, ε, …, ε)` is `εⁿ⁻¹`. -/
@[simp]
theorem orientedJacobian_scaleTail :
    b.toBasis.orientation.orientedJacobian b.toBasis.orientation (b.scaleTail ε) =
      ε ^ (n - 1) := by
  rw [Orientation.orientedJacobian_self, scaleTail_def, det_toLin, det_diagonal]
  rcases n with - | m
  · simp
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ if i = 0 then (1 : ℝ) else ε), Finset.prod_range_succ']
  simp

omit [Fact (finrank ℝ V = n)] in
/-- The operator norm of `diag(1, ε, …, ε)` for `0 ≤ ε ≤ 1` is `1`. -/
theorem norm_toContinuousLinearMap_scaleTail (hn : 0 < n) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ‖LinearMap.toContinuousLinearMap (b.scaleTail ε)‖ = 1 := by
  rw [norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_scaleTail b hε₀ hε₁ hn]
  simp

omit [Fact (finrank ℝ V = n)] in
/-- The Frobenius norm of `diag(1, ε, …, ε)` is `√(1 + (n - 1) ε²)`. -/
theorem frobenius_scaleTail (hn : 0 < n) :
    frobenius ℝ V V (b.scaleTail ε) = √(1 + (n - 1 : ℕ) * ε ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [frobenius_apply b, Fin.sum_univ_succ]
  simp [scaleTail_apply, norm_smul]

/-- For `0 < ε ≤ 1`, the outer distortion of `diag(1, ε, …, ε)` is
`n^{n/2} / (1 + (n - 1) ε²)^{n/2}` times its Hilbert–Schmidt distortion. -/
theorem outerDistortion_scaleTail (hn : 0 < n) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    b.toBasis.orientation.outerDistortion b.toBasis.orientation (b.scaleTail ε) =
      ENNReal.ofReal (√(n : ℝ) ^ n / √(1 + (n - 1 : ℕ) * ε ^ 2) ^ n) *
        b.toBasis.orientation.hilbertSchmidtDistortion b.toBasis.orientation
          (b.scaleTail ε) := by
  have hJ := b.orientedJacobian_scaleTail (ε := ε)
  have hJpos : 0 < ε ^ (n - 1) := pow_pos hε₀ _
  rw [Orientation.outerDistortion_of_pos _ _ (hJ ▸ hJpos),
    Orientation.hilbertSchmidtDistortion_of_pos _ _ (hJ ▸ hJpos), hJ,
    norm_toContinuousLinearMap_scaleTail b hn hε₀.le hε₁, frobenius_scaleTail b hn,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_pow]
  field_simp

end OrthonormalBasis

namespace Orientation

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- **The constant `n^{n/2}` in `q_O ≤ n^{n/2} q_S` cannot be lowered**: for every `c < n^{n/2}`
there is a linear map `A` with `J(A) > 0` and `c q_S(A) < q_O(A)`. -/
theorem exists_mul_hilbertSchmidtDistortion_lt_outerDistortion (hn : 0 < n)
    (oV : Orientation ℝ V (Fin n)) {c : ℝ} (hc : c < √(n : ℝ) ^ n) :
    ∃ A : V →ₗ[ℝ] V, 0 < oV.orientedJacobian oV A ∧
      ENNReal.ofReal c * oV.hilbertSchmidtDistortion oV A < oV.outerDistortion oV A := by
  obtain ⟨b, rfl⟩ : ∃ b : OrthonormalBasis (Fin n) ℝ V, b.toBasis.orientation = oV :=
    ⟨_, oV.finOrthonormalBasis_orientation hn Fact.out⟩
  -- Choose `0 < ε ≤ 1` with `c (1 + (n - 1) ε²)^{n/2} < n^{n/2}`.
  have hcont : Continuous fun ε : ℝ ↦ c * √(1 + (n - 1 : ℕ) * ε ^ 2) ^ n := by fun_prop
  have h0 : ∀ᶠ ε in 𝓝 (0 : ℝ), c * √(1 + (n - 1 : ℕ) * ε ^ 2) ^ n < √(n : ℝ) ^ n :=
    (hcont.tendsto 0).eventually (gt_mem_nhds (by simpa using hc))
  have hlim : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * √(1 + (n - 1 : ℕ) * ε ^ 2) ^ n < √(n : ℝ) ^ n ∧
      0 < ε ∧ ε ≤ 1 := by
    filter_upwards [nhdsWithin_le_nhds h0, Ioo_mem_nhdsGT one_pos] with ε h hε
    exact ⟨h, hε.1, hε.2.le⟩
  obtain ⟨ε, hε, hε₀, hε₁⟩ := hlim.exists
  have hJ := b.orientedJacobian_scaleTail (ε := ε)
  have hJpos : 0 < ε ^ (n - 1) := pow_pos hε₀ _
  refine ⟨b.scaleTail ε, hJ ▸ hJpos, ?_⟩
  have hS := b.toBasis.orientation.hilbertSchmidtDistortion_ne_top_of_pos b.toBasis.orientation
    (hJ ▸ hJpos)
  have hS0 : b.toBasis.orientation.hilbertSchmidtDistortion b.toBasis.orientation
      (b.scaleTail ε) ≠ 0 := by
    simpa using (lt_of_lt_of_le one_pos
      (b.toBasis.orientation.one_le_hilbertSchmidtDistortion _ (hJ ▸ hJpos))).ne'
  have hF : 0 < √(1 + (n - 1 : ℕ) * ε ^ 2) ^ n :=
    pow_pos (Real.sqrt_pos.mpr (by positivity)) _
  rw [b.outerDistortion_scaleTail hn hε₀ hε₁]
  exact ENNReal.mul_lt_mul_left hS0 hS
    ((ENNReal.ofReal_lt_ofReal_iff (div_pos (Real.sqrt_natCast_pow_self_pos n) hF)).mpr
      ((lt_div_iff₀ hF).mpr hε))

end Orientation

/-! ### Checks -/

namespace TauCeti.HilbertSchmidtDistortionChecks

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (finrank ℝ E = 2)] (e : OrthonormalBasis (Fin 2) ℝ E)

/-- `diag(1, ε)` with `0 < ε ≤ 1` has `q_O = (2 / (1 + ε²)) q_S`. -/
example {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation (e.scaleTail ε) =
      ENNReal.ofReal (2 / (1 + ε ^ 2)) *
        e.toBasis.orientation.hilbertSchmidtDistortion e.toBasis.orientation
          (e.scaleTail ε) := by
  rw [OrthonormalBasis.outerDistortion_scaleTail e two_pos hε₀ hε₁]
  norm_num [Real.sq_sqrt, add_nonneg zero_le_one (sq_nonneg ε)]

/-- The ratio `2 / (1 + ε²)` of `diag(1, ε)` is below `n^{n/2} = 2` for `ε ≠ 0` and tends to `2`
as `ε → 0`. -/
example : (∀ ε : ℝ, ε ≠ 0 → 2 / (1 + ε ^ 2) < 2) ∧
    Tendsto (fun ε : ℝ ↦ 2 / (1 + ε ^ 2)) (𝓝 0) (𝓝 2) := by
  refine ⟨fun ε hε ↦ ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos (abs_pos.mpr hε) 2, sq_abs ε]
  · have : Continuous fun ε : ℝ ↦ 2 / (1 + ε ^ 2) :=
      continuous_const.div (by fun_prop) fun ε ↦ by positivity
    simpa using this.tendsto 0

/-- In dimension three `diag(1, ε, ε)` has `q_O = (3^{3/2} / (1 + 2ε²)^{3/2}) q_S`, and the ratio
tends to `3^{3/2}` as `ε → 0`. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fact (finrank ℝ F = 3)] (f : OrthonormalBasis (Fin 3) ℝ F) {ε : ℝ} (hε₀ : 0 < ε)
    (hε₁ : ε ≤ 1) :
    f.toBasis.orientation.outerDistortion f.toBasis.orientation (f.scaleTail ε) =
        ENNReal.ofReal (√3 ^ 3 / √(1 + 2 * ε ^ 2) ^ 3) *
          f.toBasis.orientation.hilbertSchmidtDistortion f.toBasis.orientation
            (f.scaleTail ε) ∧
      Tendsto (fun ε : ℝ ↦ √3 ^ 3 / √(1 + 2 * ε ^ 2) ^ 3) (𝓝 0) (𝓝 (√3 ^ 3)) := by
  refine ⟨?_, ?_⟩
  · rw [OrthonormalBasis.outerDistortion_scaleTail f (by norm_num) hε₀ hε₁]
    norm_num
  · have : Continuous fun ε : ℝ ↦ √3 ^ 3 / √(1 + 2 * ε ^ 2) ^ 3 :=
      continuous_const.div (by fun_prop) fun ε ↦
        (pow_pos (Real.sqrt_pos.mpr (by positivity)) 3).ne'
    simpa using this.tendsto 0

end TauCeti.HilbertSchmidtDistortionChecks
