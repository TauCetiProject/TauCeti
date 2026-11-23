/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.JohnEllipsoid

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Snoc
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# The Dvoretzky–Rogers lemma

Let `T : E ≃L[𝕜] F` be a maximal-volume ellipsoid from an `n`-dimensional inner product space `E`
into a normed space `F`, so that the norm `x ↦ ‖T x‖` on `E` is in John's position: it is at most
the Euclidean norm, and the Euclidean unit ball is the inscribed ellipsoid of maximal volume. The
**Dvoretzky–Rogers lemma** says that this norm cannot be small on a large subspace: there is an
orthonormal basis `e₀, …, eₙ₋₁` of `E` with

`2 ^ (-n / (n - j)) ≤ ‖T eⱼ‖`

for every `j`. In particular `‖T eⱼ‖ ≥ 1 / 4` whenever `2 j ≤ n`, so about half of the vectors of
this Euclidean basis have norm bounded below independently of the dimension. This is the
dimension-growth step of Dvoretzky's theorem: the norm on the span of these vectors has a large mean
on the Euclidean sphere.

The proof bounds the norm on the orthogonal complement of any subspace `K` of dimension `k < n`.
Let `a` be the largest value of `‖T z‖` on the unit sphere of `Kᗮ`. Writing `x = p + q` with
`p ∈ K` and `q ∈ Kᗮ`, the map `x ↦ T (p / 2 + q / (2 a))` is still a contraction, because
`‖T p‖ ≤ ‖p‖` and `‖T q‖ ≤ a ‖q‖`. Its determinant relative to `T` is `2⁻ⁿ a⁻⁽ⁿ⁻ᵏ⁾`, which by
maximality of the volume of `T` has norm at most one, so `2⁻ⁿ ≤ aⁿ⁻ᵏ`. Choosing the basis vectors
one at a time in the orthogonal complement of the previous ones gives the lemma.

## Main declarations

All in the namespace `ContinuousLinearEquiv.IsMaxVolumeEllipsoid`:

* `inv_two_pow_le_pow_of_forall_mem_orthogonal`: if `‖T q‖ ≤ a ‖q‖` for every `q` orthogonal to a
  `k`-dimensional subspace `K`, then `2⁻ⁿ ≤ a ^ (n - k)`.
* `exists_mem_orthogonal_inv_two_pow_le_norm_apply_pow`: for every subspace `K` of dimension
  `k < n` there is a unit vector `z ⊥ K` with `2⁻ⁿ ≤ ‖T z‖ ^ (n - k)`.
* `exists_orthonormalBasis_inv_two_pow_le_norm_apply_pow`: **the Dvoretzky–Rogers lemma**, an
  orthonormal basis `b` with `2⁻ⁿ ≤ ‖T (b j)‖ ^ (n - j)`.
* `exists_orthonormalBasis_two_rpow_le_norm_apply`: the same bound in the form
  `2 ^ (-n / (n - j)) ≤ ‖T (b j)‖`.
* `exists_orthonormalBasis_forall_le_norm_apply`: the same basis has `1 / 4 ≤ ‖T (b j)‖` whenever
  `2 j ≤ n`.

## References

* A. Dvoretzky and C. A. Rogers, *Absolute and unconditional convergence in normed linear spaces*,
  Proc. Nat. Acad. Sci. U.S.A. **36** (1950), 192–197.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Lemma 13.3.5.
-/

public section

open Module Metric Submodule
open scoped InnerProductSpace

namespace ContinuousLinearEquiv.IsMaxVolumeEllipsoid

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] {T : E ≃L[𝕜] F}

omit [FiniteDimensional 𝕜 E] in
/-- The contraction estimate behind `inv_two_pow_le_pow_of_forall_mem_orthogonal`: if `‖T‖ ≤ 1`
and `‖T q‖ ≤ a ‖q‖` on `Kᗮ`, then `‖T p / 2 + T q / (2 a)‖ ≤ ‖p + q‖` for `p ∈ K` and `q ∈ Kᗮ`. -/
private theorem norm_smul_add_smul_le (hT : ‖(T : E →L[𝕜] F)‖ ≤ 1) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {a : ℝ} (ha : 0 < a) (h : ∀ q ∈ Kᗮ, ‖T q‖ ≤ a * ‖q‖) {p q : E}
    (hp : p ∈ K) (hq : q ∈ Kᗮ) :
    ‖((2⁻¹ : ℝ) : 𝕜) • T p + (((2 * a)⁻¹ : ℝ) : 𝕜) • T q‖ ≤ ‖p + q‖ := by
  -- By Pythagoras both `‖p‖` and `‖q‖` are at most `‖p + q‖`.
  have hpx : ‖p‖ ≤ ‖p + q‖ :=
    K.mem_iff_forall_mem_orthogonal_norm_le_norm_add.1 hp q hq
  have hqx : ‖q‖ ≤ ‖p + q‖ := add_comm p q ▸
    Kᗮ.mem_iff_forall_mem_orthogonal_norm_le_norm_add.1 hq p (K.le_orthogonal_orthogonal hp)
  have hTp : ‖T p‖ ≤ ‖p‖ := by
    simpa using (T : E →L[𝕜] F).le_of_opNorm_le hT p
  calc _ ≤ 2⁻¹ * ‖T p‖ + (2 * a)⁻¹ * ‖T q‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        simp only [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity : (0 : ℝ) < 2⁻¹),
          abs_of_pos (by positivity : 0 < (2 * a)⁻¹)]
    _ ≤ 2⁻¹ * ‖p‖ + (2 * a)⁻¹ * (a * ‖q‖) := by
        gcongr
        exact h q hq
    _ = (‖p‖ + ‖q‖) / 2 := by field_simp
    _ ≤ ‖p + q‖ := by linarith

/-- **Volume bound for the norm on an orthogonal complement.** Let `T` be a maximal-volume
ellipsoid on an `n`-dimensional inner product space `E` and `K` a subspace of dimension `k`. If
`‖T q‖ ≤ a ‖q‖` for every `q ⊥ K`, then `2⁻ⁿ ≤ a ^ (n - k)`. -/
theorem inv_two_pow_le_pow_of_forall_mem_orthogonal (hT : T.IsMaxVolumeEllipsoid)
    (K : Submodule 𝕜 E) {a : ℝ} (h : ∀ q ∈ Kᗮ, ‖T q‖ ≤ a * ‖q‖) :
    (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ a ^ (finrank 𝕜 E - finrank 𝕜 K) := by
  set n := finrank 𝕜 E
  set k := finrank 𝕜 K
  have hKo : finrank 𝕜 Kᗮ = n - k := by
    have := K.finrank_add_finrank_orthogonal
    omega
  -- If `Kᗮ = 0` the right side is `1`; otherwise a nonzero `q ⊥ K` shows that `a > 0`.
  rcases eq_or_ne Kᗮ ⊥ with hK | hK
  · rw [← hKo, hK, finrank_bot, pow_zero]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨q₀, hq₀K, hq₀⟩ := exists_mem_ne_zero_of_ne_bot hK
  have ha : 0 < a := pos_of_mul_pos_left ((norm_pos_iff.2 ((map_ne_zero_iff T T.injective).2
    hq₀)).trans_le (h q₀ hq₀K)) (norm_nonneg q₀)
  have hc : IsCompl K Kᗮ := K.isCompl_orthogonal
  set e := K.prodEquivOfIsCompl Kᗮ hc
  set β : 𝕜 := ((2⁻¹ : ℝ) : 𝕜)
  set γ : 𝕜 := (((2 * a)⁻¹ : ℝ) : 𝕜)
  set A : E →ₗ[𝕜] E := (e : (K × Kᗮ) →ₗ[𝕜] E) ∘ₗ
    LinearMap.prodMap (β • LinearMap.id) (γ • LinearMap.id) ∘ₗ (e.symm : E →ₗ[𝕜] K × Kᗮ)
  have hdetA : LinearMap.det A = β ^ k * γ ^ (n - k) := by
    simp only [A, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
      LinearMap.det_id, mul_one, hKo, k]
  set S : E →L[𝕜] F := (T : E →L[𝕜] F).comp (LinearMap.toContinuousLinearMap A)
  have hS : ‖S‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    have hpq : ((e.symm x).1 : E) + (e.symm x).2 = x :=
      (coe_prodEquivOfIsCompl' K Kᗮ hc _).symm.trans (e.apply_symm_apply x)
    have hSx : S x = β • T (e.symm x).1 + γ • T (e.symm x).2 := by
      simp [S, A, e]
    rw [hSx, one_mul]
    conv_rhs => rw [← hpq]
    exact norm_smul_add_smul_le hT.norm_le_one ha h (e.symm x).1.property (e.symm x).2.property
  -- Comparing its volume with that of the maximal ellipsoid gives `2⁻ⁿ a⁻⁽ⁿ⁻ᵏ⁾ ≤ 1`.
  have hdet := hT.norm_det_le_one S hS
  have hTS : (T.symm : F →L[𝕜] E).comp S = LinearMap.toContinuousLinearMap A := by
    rw [← ContinuousLinearMap.comp_assoc, T.coe_symm_comp_coe, ContinuousLinearMap.id_comp]
  have hkn : k ≤ n := K.finrank_le
  have hnorm : ‖LinearMap.det A‖ * a ^ (n - k) = 2⁻¹ ^ n := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkn
    rw [hdetA, hm, Nat.add_sub_cancel_left]
    simp only [β, γ, norm_mul, norm_pow, RCLike.norm_ofReal, abs_inv, abs_mul, abs_two,
      abs_of_pos ha, mul_inv, mul_pow, inv_pow]
    field_simp
    ring
  rw [hTS, LinearMap.det_toContinuousLinearMap] at hdet
  rw [← hnorm]
  exact mul_le_of_le_one_left (by positivity) hdet

/-- **The norm in John's position is large on orthogonal complements.** If `T` is a maximal-volume
ellipsoid on an `n`-dimensional inner product space `E` and `K` is a subspace of dimension `k < n`,
then some unit vector `z` orthogonal to `K` has `2⁻ⁿ ≤ ‖T z‖ ^ (n - k)`. -/
theorem exists_mem_orthogonal_inv_two_pow_le_norm_apply_pow (hT : T.IsMaxVolumeEllipsoid)
    (K : Submodule 𝕜 E) (hK : finrank 𝕜 K < finrank 𝕜 E) :
    ∃ z ∈ Kᗮ, ‖z‖ = 1 ∧ (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ ‖T z‖ ^ (finrank 𝕜 E - finrank 𝕜 K) := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  -- `‖T ·‖` attains its maximum on the unit sphere of `Kᗮ`, which is nonempty.
  obtain ⟨w, hwK, hw⟩ := exists_mem_ne_zero_of_ne_bot fun h : Kᗮ = ⊥ ↦ by
    have := K.finrank_add_finrank_orthogonal
    rw [h, finrank_bot] at this
    omega
  have hw' : ((‖w‖⁻¹ : ℝ) : 𝕜) • w ∈ sphere (0 : E) 1 ∩ Kᗮ :=
    ⟨by simp [norm_smul, norm_ne_zero_iff.2 hw], Kᗮ.smul_mem _ hwK⟩
  obtain ⟨z, ⟨hz, hzK⟩, hmax⟩ := ((isCompact_sphere (0 : E) 1).inter_right
    K.isClosed_orthogonal).exists_isMaxOn ⟨_, hw'⟩ T.continuous.norm.continuousOn
  rw [mem_sphere_zero_iff_norm] at hz
  refine ⟨z, hzK, hz, hT.inv_two_pow_le_pow_of_forall_mem_orthogonal K fun q hq ↦ ?_⟩
  -- By homogeneity, the maximum bounds `‖T q‖ / ‖q‖` for every nonzero `q ⊥ K`.
  rcases eq_or_ne q 0 with rfl | hq₀
  · simp
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq₀
  have := hmax (show ((‖q‖⁻¹ : ℝ) : 𝕜) • q ∈ sphere (0 : E) 1 ∩ Kᗮ from
    ⟨by simp [norm_smul, hq'], Kᗮ.smul_mem _ hq⟩)
  simp only [Set.mem_ofPred_eq, map_smul, norm_smul, RCLike.norm_ofReal, abs_inv,
    abs_norm] at this
  rwa [inv_mul_le_iff₀ (norm_pos_iff.2 hq₀), mul_comm] at this

/-- An orthonormal family `v₀, …, vₖ₋₁` with `2⁻ⁿ ≤ ‖T vⱼ‖ ^ (n - j)`, for every `k ≤ n`, obtained
by choosing each vector in the orthogonal complement of the previous ones. -/
private theorem exists_orthonormal_inv_two_pow_le_norm_apply_pow (hT : T.IsMaxVolumeEllipsoid)
    {k : ℕ} (hk : k ≤ finrank 𝕜 E) :
    ∃ v : Fin k → E, Orthonormal 𝕜 v ∧
      ∀ j : Fin k, (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ ‖T (v j)‖ ^ (finrank 𝕜 E - j) := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, fun j ↦ j.elim0⟩
  | succ k ih =>
    obtain ⟨v, hv, hvT⟩ := ih (by omega)
    set K := span 𝕜 (Set.range v)
    have hK : finrank 𝕜 K = k := by simp [K, finrank_span_eq_card hv.linearIndependent]
    obtain ⟨z, hzK, hz, hzT⟩ :=
      hT.exists_mem_orthogonal_inv_two_pow_le_norm_apply_pow K (by omega)
    refine ⟨Fin.snoc v z, hv.snoc hz fun i ↦
      K.inner_right_of_mem_orthogonal (subset_span (Set.mem_range_self i)) hzK, fun j ↦ ?_⟩
    induction j using Fin.lastCases with
    | last => simpa [hK] using hzT
    | cast j => simpa using hvT j

/-- **The Dvoretzky–Rogers lemma.** If `T` is a maximal-volume ellipsoid on an `n`-dimensional inner
product space `E`, then `E` has an orthonormal basis `b` with `2⁻ⁿ ≤ ‖T (b j)‖ ^ (n - j)` for every
`j`, that is, `2 ^ (-n / (n - j)) ≤ ‖T (b j)‖`. -/
theorem exists_orthonormalBasis_inv_two_pow_le_norm_apply_pow (hT : T.IsMaxVolumeEllipsoid) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∀ j, (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ ‖T (b j)‖ ^ (finrank 𝕜 E - j) := by
  obtain ⟨v, hv, hvT⟩ := hT.exists_orthonormal_inv_two_pow_le_norm_apply_pow le_rfl
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank'
    (Fintype.card_fin _)).ge, fun j ↦ ?_⟩
  simpa using hvT j

/-- **The Dvoretzky–Rogers lemma**, in the form `2 ^ (-n / (n - j)) ≤ ‖T (b j)‖` for an
orthonormal basis `b` of the `n`-dimensional inner product space `E`, when `T` is a maximal-volume
ellipsoid. -/
theorem exists_orthonormalBasis_two_rpow_le_norm_apply (hT : T.IsMaxVolumeEllipsoid) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∀ j : Fin (finrank 𝕜 E),
        (2 : ℝ) ^ (-(finrank 𝕜 E : ℝ) / (finrank 𝕜 E - j : ℕ)) ≤ ‖T (b j)‖ := by
  obtain ⟨b, hb⟩ := hT.exists_orthonormalBasis_inv_two_pow_le_norm_apply_pow
  refine ⟨b, fun j ↦ ?_⟩
  have hm : (0 : ℝ) < (finrank 𝕜 E - j : ℕ) := Nat.cast_pos.2 (by omega)
  have h2 : (2 : ℝ) ^ (-(finrank 𝕜 E : ℝ)) = 2⁻¹ ^ finrank 𝕜 E := by
    rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, inv_pow]
  -- Take `(n - j)`-th roots of `2⁻ⁿ ≤ ‖T (b j)‖ ^ (n - j)`.
  rw [div_eq_mul_inv, Real.rpow_mul zero_le_two, h2,
    Real.rpow_inv_le_iff_of_pos (by positivity) (norm_nonneg _) hm, Real.rpow_natCast]
  exact hb j

/-- **The Dvoretzky–Rogers lemma**, half-dimensional form: if `T` is a maximal-volume ellipsoid on
an `n`-dimensional inner product space `E`, then `E` has an orthonormal basis `b` with
`1 / 4 ≤ ‖T (b j)‖` whenever `2 j ≤ n`. -/
theorem exists_orthonormalBasis_forall_le_norm_apply (hT : T.IsMaxVolumeEllipsoid) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∀ j : Fin (finrank 𝕜 E), 2 * (j : ℕ) ≤ finrank 𝕜 E → 1 / 4 ≤ ‖T (b j)‖ := by
  obtain ⟨b, hb⟩ := hT.exists_orthonormalBasis_inv_two_pow_le_norm_apply_pow
  refine ⟨b, fun j hj ↦ ?_⟩
  have hm : finrank 𝕜 E - j ≠ 0 := by omega
  -- `(1 / 4) ^ (n - j) = 2⁻¹ ^ (2 (n - j)) ≤ 2⁻¹ ^ n ≤ ‖T (b j)‖ ^ (n - j)`.
  refine (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) hm).1 ?_
  calc (1 / 4 : ℝ) ^ (finrank 𝕜 E - j) = (2⁻¹ : ℝ) ^ (2 * (finrank 𝕜 E - j)) := by
        rw [pow_mul]
        norm_num
    _ ≤ (2⁻¹ : ℝ) ^ finrank 𝕜 E := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ ‖T (b j)‖ ^ (finrank 𝕜 E - j) := hb j

end ContinuousLinearEquiv.IsMaxVolumeEllipsoid
