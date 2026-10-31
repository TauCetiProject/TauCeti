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
(`ContinuousMap.exists_partitionOfUnity_dist_finsum_smul_le`). The matrix
`a k l = B (ρ k) (σ l)` has scalar bound `C`, because `∑ k, s k * ρ k` has uniform norm at most
one whenever every `‖s k‖ ≤ 1`, and the approximating sum is
`∑ k, ∑ l, a k l * ⟪u k, v l⟫` for the vectors `u k = (conj (f i k))ᵢ` and `v l = (g i l)ᵢ` of
Euclidean norm at most one. Letting the approximation error tend to zero gives the result.

## Main declarations

* `LinearMap.norm_sum_apply_apply_le_sixteen_mul`: Grothendieck's inequality for bounded
  bilinear forms on `C(K, 𝕜) × C(L, 𝕜)` over an `RCLike` field, with constant `16`.
* `LinearMap.abs_sum_apply_apply_le_eight_mul`: the real version, with constant `8`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open scoped InnerProductSpace

/-- The coordinates of a family whose square function is bounded by one are bounded by one. -/
private theorem norm_apply_le_one_of_sum_sq_le {X 𝕜 ι : Type*} [TopologicalSpace X] [RCLike 𝕜]
    [Fintype ι] {h : ι → C(X, 𝕜)} (hh : ∀ x, ∑ i, ‖h i x‖ ^ 2 ≤ 1) (i : ι) (x : X) :
    ‖h i x‖ ≤ 1 :=
  (sq_le_one_iff₀ (norm_nonneg _)).1 <|
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖h j x‖) (Finset.mem_univ i)).trans (hh x)

namespace LinearMap

variable {K L 𝕜 ι : Type*} [TopologicalSpace K] [CompactSpace K] [TopologicalSpace L]
  [CompactSpace L] [RCLike 𝕜]

/-- A finite family in `C(K, 𝕜)` is uniformly within `δ > 0` of the combinations
`∑ k, f i k • ρ k` of its values at the points of a finite set, for a partition of unity `ρ`
indexed by those points. -/
private theorem exists_partitionOfUnity_norm_sum_smul_sub_le [NormalSpace K] [Finite ι]
    (f : ι → C(K, 𝕜)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset K) (ρ : PartitionOfUnity s K), ∀ i,
      ‖∑ k : s, f i k • (⟨fun x ↦ (ρ k x : 𝕜), by fun_prop⟩ : C(K, 𝕜)) - f i‖ ≤ δ := by
  have := Fintype.ofFinite ι
  obtain ⟨s, ρ, hρ⟩ := (ContinuousMap.pi f).exists_partitionOfUnity_dist_finsum_smul_le hδ
  refine ⟨s, ρ, fun i ↦ (ContinuousMap.norm_le _ hδ.le).2 fun x ↦ ?_⟩
  have hx := (norm_le_pi_norm (∑ᶠ k, ρ k x • ContinuousMap.pi f k - ContinuousMap.pi f x) i).trans
    ((dist_eq_norm _ _).symm.trans_le (hρ x))
  simpa only [ContinuousMap.sub_apply, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
    ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ContinuousMap.pi_eval,
    finsum_eq_sum_of_fintype, Pi.sub_apply, RCLike.real_smul_eq_coe_mul, mul_comm] using hx

/-- For a finite partition of unity `ρ` and scalars `c k` of norm at most one, the continuous
function `∑ k, c k * ρ k` has uniform norm at most one. -/
private theorem norm_sum_smul_le_one {κ : Type*} [Fintype κ] (ρ : PartitionOfUnity κ K)
    {c : κ → 𝕜} (hc : ∀ k, ‖c k‖ ≤ 1) :
    ‖∑ k, c k • (⟨fun x ↦ (ρ k x : 𝕜), by fun_prop⟩ : C(K, 𝕜))‖ ≤ 1 := by
  refine (ContinuousMap.norm_le _ zero_le_one).2 fun x ↦ ?_
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul]
  calc ‖∑ k, c k * (ρ k x : 𝕜)‖ ≤ ∑ k, ‖c k * (ρ k x : 𝕜)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ρ k x := Finset.sum_le_sum fun k _ ↦ by
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (ρ.nonneg k x)]
        exact mul_le_of_le_one_left (ρ.nonneg k x) (hc k)
    _ ≤ 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x

/-- A bilinear map evaluated on finite linear combinations. -/
private theorem apply_sum_smul_sum_smul {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    [Module 𝕜 E] [Module 𝕜 F] {κ κ' : Type*} [Fintype κ] [Fintype κ'] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (φ : κ → E) (ψ : κ' → F) (c : κ → 𝕜) (d : κ' → 𝕜) :
    B (∑ k, c k • φ k) (∑ l, d l • ψ l) = ∑ k, ∑ l, B (φ k) (ψ l) * c k * d l := by
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

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
  obtain ⟨s, ρ, hρ⟩ := exists_partitionOfUnity_norm_sum_smul_sub_le f hδ
  obtain ⟨t, σ, hσ⟩ := exists_partitionOfUnity_norm_sum_smul_sub_le g hδ
  have hB' {x : C(K, 𝕜)} {y : C(L, 𝕜)} {a b : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
      ‖B x y‖ ≤ C * a * b :=
    (hB x y).trans <| mul_le_mul (mul_le_mul_of_nonneg_left hx hC) hy (norm_nonneg _)
      (mul_nonneg hC ((norm_nonneg _).trans hx))
  set φ : s → C(K, 𝕜) := fun k ↦ ⟨fun x ↦ (ρ k x : 𝕜), by fun_prop⟩
  set ψ : t → C(L, 𝕜) := fun l ↦ ⟨fun y ↦ (σ l y : 𝕜), by fun_prop⟩
  refine ⟨s, t, fun k l ↦ B (φ k) (ψ l), fun k ↦ WithLp.toLp 2 fun i ↦ star (f i k),
    fun l ↦ WithLp.toLp 2 fun i ↦ g i l, fun c d hc hd ↦ ?_, fun k ↦ ?_, fun l ↦ ?_, ?_⟩
  · rw [← apply_sum_smul_sum_smul]
    exact (hB' (norm_sum_smul_le_one ρ hc) (norm_sum_smul_le_one σ hd)).trans_eq (by ring)
  · rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
    simpa using hf k
  · rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
    simpa using hg l
  -- The approximating sum is the matrix sum, and the error is controlled by `δ`.
  set f' : ι → C(K, 𝕜) := fun i ↦ ∑ k : s, f i k • φ k
  set g' : ι → C(L, 𝕜) := fun i ↦ ∑ l : t, g i l • ψ l
  have hmat : ∑ k : s, ∑ l : t, B (φ k) (ψ l) * ⟪(WithLp.toLp 2 fun i ↦ star (f i k) :
      EuclideanSpace 𝕜 ι), WithLp.toLp 2 fun i ↦ g i l⟫_𝕜 = ∑ i, B (f' i) (g' i) := by
    simp only [f', g', apply_sum_smul_sum_smul, EuclideanSpace.inner_toLp_toLp, dotProduct,
      Pi.star_apply, star_star, Finset.mul_sum]
    calc _ = ∑ k : s, ∑ l : t, ∑ i, B (φ k) (ψ l) * f i k * g i l :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦
            Finset.sum_congr rfl fun i _ ↦ by ring
      _ = ∑ k : s, ∑ i, ∑ l : t, B (φ k) (ψ l) * f i k * g i l :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hmat, ← Finset.sum_sub_distrib]
  have hterm (i : ι) : ‖B (f i) (g i) - B (f' i) (g' i)‖ ≤ 2 * C * δ := by
    have heq : B (f i) (g i) - B (f' i) (g' i) =
        B (f i - f' i) (g i) + B (f' i) (g i - g' i) := by
      simp only [map_sub, sub_apply]
      ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have h₁ := hB' ((norm_sub_rev _ _).trans_le (hρ i))
      ((ContinuousMap.norm_le _ zero_le_one).2 (norm_apply_le_one_of_sum_sq_le hg i))
    have h₂ := hB'
      (norm_sum_smul_le_one ρ fun k ↦ norm_apply_le_one_of_sum_sq_le hf i k)
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
