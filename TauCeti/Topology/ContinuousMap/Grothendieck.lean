/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Convex.PartitionOfUnity
import TauCeti.Analysis.Matrix.Grothendieck
import TauCeti.LinearAlgebra.BilinearMap.Sum

/-!
# Grothendieck's inequality for bilinear forms on spaces of continuous functions

Let `K` and `L` be compact normal spaces (for example compact Hausdorff spaces) and let `B` be a
bilinear form on `C(K, 𝕜) × C(L, 𝕜)` with `‖B f g‖ ≤ C * ‖f‖ * ‖g‖` for the uniform norms; a
continuous bilinear form satisfies this with `C = ‖B‖` (`ContinuousLinearMap.le_opNorm₂`, applied
to `ContinuousLinearMap.toLinearMap₁₂`). For finite families `f i` in `C(K, 𝕜)` and `g i` in
`C(L, 𝕜)` whose square functions `∑ i, ‖f i x‖ ^ 2` and `∑ i, ‖g i y‖ ^ 2` are bounded by one,
Grothendieck's inequality bounds `‖∑ i, B (f i) (g i)‖` by the universal constant `κ_𝕜` times
`C`, with `κ_ℝ = 8` and `κ_𝕜 = 16` for a general `RCLike` field. The constants are those of the
matrix inequality and are not optimal.

The proof reduces to Grothendieck's inequality for matrices. Choose finite partitions of unity
`ρ k` on `K` and `σ l` on `L`, indexed by finitely many points, along which the families `f` and
`g` are uniformly approximated by their values at these points
(`ContinuousMap.exists_partitionOfUnity_norm_sum_smul_sub_le`). The matrix
`a k l = B (ρ k) (σ l)` has scalar bound `C`, because `∑ k, s k * ρ k` has uniform norm at most
one whenever every `‖s k‖ ≤ 1` (`PartitionOfUnity.norm_sum_smul_le_one`), and the approximating
sum is `∑ k, ∑ l, a k l * ⟪u k, v l⟫` for the vectors `u k = (conj (f i k))ᵢ` and
`v l = (g i l)ᵢ` of Euclidean norm at most one. Letting the approximation error tend to zero
gives the result.

## Main declarations

* `LinearMap.norm_sum_apply_apply_le_sixteen_mul`: Grothendieck's inequality for bounded
  bilinear forms on `C(K, 𝕜) × C(L, 𝕜)` over an `RCLike` field, with constant `16`.
* `LinearMap.abs_sum_apply_apply_le_eight_mul`: the real version, with constant `8`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {K L 𝕜 ι : Type*} [TopologicalSpace K] [CompactSpace K] [TopologicalSpace L]
  [CompactSpace L] [RCLike 𝕜]

variable [Fintype ι]

/-- The matrix reduction: `∑ i, B (f i) (g i)` is within `2 * |ι| * C * δ` of a sum
`∑ k, ∑ l, a k l * ⟪u k, v l⟫` for a finite matrix `a` with scalar bound `C` and Euclidean
vectors of norm at most one. -/
private theorem exists_matrix_norm_sub_le [NormalSpace K] [NormalSpace L]
    (B : C(K, 𝕜) →ₗ[𝕜] C(L, 𝕜) →ₗ[𝕜] 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ f g, ‖B f g‖ ≤ C * ‖f‖ * ‖g‖) {f : ι → C(K, 𝕜)} {g : ι → C(L, 𝕜)}
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ 1) (hg : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset K) (t : Finset L) (a : Matrix s t 𝕜) (u : s → EuclideanSpace 𝕜 ι)
      (v : t → EuclideanSpace 𝕜 ι),
      (∀ (σ : s → 𝕜) (τ : t → 𝕜), (∀ k, ‖σ k‖ ≤ 1) → (∀ l, ‖τ l‖ ≤ 1) →
        ‖∑ k, ∑ l, a k l * σ k * τ l‖ ≤ C) ∧ (∀ k, ‖u k‖ ≤ 1) ∧ (∀ l, ‖v l‖ ≤ 1) ∧
      ‖∑ i, B (f i) (g i) - ∑ k, ∑ l, a k l * ⟪u k, v l⟫_𝕜‖ ≤ 2 * Fintype.card ι * C * δ := by
  -- Approximate both families along finite partitions of unity.
  obtain ⟨s, ρ, hρ⟩ := ContinuousMap.exists_partitionOfUnity_norm_sum_smul_sub_le f hδ
  obtain ⟨t, σ, hσ⟩ := ContinuousMap.exists_partitionOfUnity_norm_sum_smul_sub_le g hδ
  have hB' {x : C(K, 𝕜)} {y : C(L, 𝕜)} {a b : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
      ‖B x y‖ ≤ C * a * b :=
    (hB x y).trans <| mul_le_mul (mul_le_mul_of_nonneg_left hx hC) hy (norm_nonneg _)
      (mul_nonneg hC ((norm_nonneg _).trans hx))
  -- The values of families with square function at most one have norm at most one.
  have hcoord (w : ι → 𝕜) (hw : ∑ i, ‖w i‖ ^ 2 ≤ 1) (i : ι) : ‖w i‖ ≤ 1 :=
    (sq_le_one_iff₀ (norm_nonneg _)).1 <|
      (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖w j‖) (Finset.mem_univ i)).trans hw
  set φ : s → C(K, 𝕜) := fun k ↦ ⟨fun x ↦ (ρ k x : 𝕜), by fun_prop⟩
  set ψ : t → C(L, 𝕜) := fun l ↦ ⟨fun y ↦ (σ l y : 𝕜), by fun_prop⟩
  refine ⟨s, t, fun k l ↦ B (φ k) (ψ l), fun k ↦ WithLp.toLp 2 fun i ↦ star (f i k),
    fun l ↦ WithLp.toLp 2 fun i ↦ g i l, fun c d hc hd ↦ ?_, fun k ↦ ?_, fun l ↦ ?_, ?_⟩
  · have h := hB' (ρ.norm_sum_smul_le_one hc) (σ.norm_sum_smul_le_one hd)
    rw [apply_sum_smul_sum_smul, mul_one, mul_one] at h
    refine h.trans_eq' <| congrArg norm <| Finset.sum_congr rfl fun k _ ↦
      Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [smul_eq_mul]
    ring
  · rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
    simpa using hf k
  · rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
    simpa using hg l
  -- The approximating sum is the matrix sum, and the error is controlled by `δ`.
  set f' : ι → C(K, 𝕜) := fun i ↦ ∑ k : s, f i k • φ k
  set g' : ι → C(L, 𝕜) := fun i ↦ ∑ l : t, g i l • ψ l
  have hmat : ∑ k : s, ∑ l : t, B (φ k) (ψ l) * ⟪(WithLp.toLp 2 fun i ↦ star (f i k) :
      EuclideanSpace 𝕜 ι), WithLp.toLp 2 fun i ↦ g i l⟫_𝕜 = ∑ i, B (f' i) (g' i) := by
    simp only [f', g', apply_sum_smul_sum_smul, smul_eq_mul, EuclideanSpace.inner_toLp_toLp,
      dotProduct, Pi.star_apply, star_star, Finset.mul_sum]
    calc _ = ∑ k : s, ∑ l : t, ∑ i, B (φ k) (ψ l) * f i k * g i l :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦
            Finset.sum_congr rfl fun i _ ↦ by ring
      _ = ∑ k : s, ∑ i, ∑ l : t, B (φ k) (ψ l) * f i k * g i l :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
      _ = ∑ i, ∑ k : s, ∑ l : t, B (φ k) (ψ l) * f i k * g i l := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
          Finset.sum_congr rfl fun l _ ↦ by ring
  rw [hmat, ← Finset.sum_sub_distrib]
  have hterm (i : ι) : ‖B (f i) (g i) - B (f' i) (g' i)‖ ≤ 2 * C * δ := by
    have heq : B (f i) (g i) - B (f' i) (g' i) =
        B (f i - f' i) (g i) + B (f' i) (g i - g' i) := by
      simp only [map_sub, sub_apply]
      ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have h₁ := hB' ((norm_sub_rev _ _).trans_le (hρ i))
      ((ContinuousMap.norm_le _ zero_le_one).2 fun y ↦ hcoord (fun j ↦ g j y) (hg y) i)
    have h₂ := hB'
      (ρ.norm_sum_smul_le_one fun k ↦ hcoord (fun j ↦ f j k) (hf k) i)
      ((norm_sub_rev _ _).trans_le (hσ i))
    linarith
  refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun i _ ↦ hterm i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Grothendieck's inequality for bilinear forms follows from any matrix inequality with a
constant `c`, by letting the error of the matrix reduction tend to zero. -/
private theorem norm_sum_apply_apply_le_of_matrix [NormalSpace K] [NormalSpace L]
    (B : C(K, 𝕜) →ₗ[𝕜] C(L, 𝕜) →ₗ[𝕜] 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ f g, ‖B f g‖ ≤ C * ‖f‖ * ‖g‖) {f : ι → C(K, 𝕜)} {g : ι → C(L, 𝕜)}
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ 1) (hg : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ 1) {c : ℝ}
    (hc : ∀ (s : Finset K) (t : Finset L) (a : Matrix s t 𝕜) (u : s → EuclideanSpace 𝕜 ι)
      (v : t → EuclideanSpace 𝕜 ι),
      (∀ (σ : s → 𝕜) (τ : t → 𝕜), (∀ k, ‖σ k‖ ≤ 1) → (∀ l, ‖τ l‖ ≤ 1) →
        ‖∑ k, ∑ l, a k l * σ k * τ l‖ ≤ C) → (∀ k, ‖u k‖ ≤ 1) → (∀ l, ‖v l‖ ≤ 1) →
      ‖∑ k, ∑ l, a k l * ⟪u k, v l⟫_𝕜‖ ≤ c * C) :
    ‖∑ i, B (f i) (g i)‖ ≤ c * C := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hN : 0 < 2 * Fintype.card ι * C + 1 := by positivity
  obtain ⟨s, t, a, u, v, ha, hu, hv, herr⟩ :=
    exists_matrix_norm_sub_le B hC hB hf hg (div_pos hε hN)
  have hδ : 2 * Fintype.card ι * C * (ε / (2 * Fintype.card ι * C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hN]
    nlinarith
  have := norm_le_norm_sub_add (∑ i, B (f i) (g i)) (∑ k, ∑ l, a k l * ⟪u k, v l⟫_𝕜)
  linarith [hc s t a u v ha hu hv]

/-- **Grothendieck's inequality** for bounded bilinear forms on spaces of continuous functions,
over an `RCLike` field with constant `κ_𝕜 = 16`. Let `K` and `L` be compact normal spaces and
`B` a bilinear form on `C(K, 𝕜) × C(L, 𝕜)` with `‖B f g‖ ≤ C * ‖f‖ * ‖g‖`, such as a continuous
bilinear form with `C = ‖B‖`. If the families `f i` in `C(K, 𝕜)` and `g i` in `C(L, 𝕜)` have
square functions bounded by one, then `‖∑ i, B (f i) (g i)‖ ≤ 16 * C`. Over `ℝ`,
`LinearMap.abs_sum_apply_apply_le_eight_mul` gives the constant `8`. -/
theorem norm_sum_apply_apply_le_sixteen_mul [NormalSpace K] [NormalSpace L]
    (B : C(K, 𝕜) →ₗ[𝕜] C(L, 𝕜) →ₗ[𝕜] 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ f g, ‖B f g‖ ≤ C * ‖f‖ * ‖g‖) {f : ι → C(K, 𝕜)} {g : ι → C(L, 𝕜)}
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ 1) (hg : ∀ y, ∑ i, ‖g i y‖ ^ 2 ≤ 1) :
    ‖∑ i, B (f i) (g i)‖ ≤ 16 * C :=
  norm_sum_apply_apply_le_of_matrix B hC hB hf hg fun _ _ a _ _ ha hu hv ↦
    a.norm_sum_sum_mul_inner_le_sixteen_mul ha hu hv

/-- **Grothendieck's inequality** for bounded real bilinear forms on spaces of continuous
functions, with constant `κ_ℝ = 8`. Let `K` and `L` be compact normal spaces and `B` a bilinear
form on `C(K, ℝ) × C(L, ℝ)` with `|B f g| ≤ C * ‖f‖ * ‖g‖`. If `∑ i, f i x ^ 2 ≤ 1` and
`∑ i, g i y ^ 2 ≤ 1` everywhere, then `|∑ i, B (f i) (g i)| ≤ 8 * C`. -/
theorem abs_sum_apply_apply_le_eight_mul [NormalSpace K] [NormalSpace L]
    (B : C(K, ℝ) →ₗ[ℝ] C(L, ℝ) →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ f g, |B f g| ≤ C * ‖f‖ * ‖g‖) {f : ι → C(K, ℝ)} {g : ι → C(L, ℝ)}
    (hf : ∀ x, ∑ i, f i x ^ 2 ≤ 1) (hg : ∀ y, ∑ i, g i y ^ 2 ≤ 1) :
    |∑ i, B (f i) (g i)| ≤ 8 * C := by
  rw [← Real.norm_eq_abs]
  refine norm_sum_apply_apply_le_of_matrix B hC (by simpa only [Real.norm_eq_abs] using hB)
    (by simpa using hf) (by simpa using hg) fun _ _ a _ _ ha hu hv ↦ ?_
  simpa only [Real.norm_eq_abs] using a.abs_sum_sum_mul_inner_le_eight_mul
    (fun s t hs ht ↦ by
      simpa only [Real.norm_eq_abs] using ha s t (by simpa using hs) (by simpa using ht)) hu hv

end LinearMap
