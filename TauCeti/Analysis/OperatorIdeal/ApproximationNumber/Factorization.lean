/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Scalar factorization through approximation numbers

If `H₁` is a complete inner product space, `T : H₁ →L[𝕜] H₂` and `0 ≤ c < aₙ(T)`, then there are
contractions `A : ℓ₂^{n+1} → H₁` and `B : H₂ → ℓ₂^{n+1}` with `B ∘ T ∘ A = c • id`. By the
converse min–max localization, `T` is `t`-coercive on an `(n + 1)`-dimensional subspace `V` for
some `t > c`; `A` is an isometry of `ℓ₂^{n+1}` onto `V`, and `B` is `c` times the inverse of
`T ∘ A` on its range, precomposed with the orthogonal projection onto that range.

The factorization says that `c • id` on `ℓ₂^{n+1}` is a contraction-compression of `T`. It is the
key input to the uniqueness of s-numbers on Hilbert spaces.

## Main declarations

* `TauCeti.HasMinMaxLowerBound.exists_comp_comp_eq_smul_id`: the scalar factorization on a pair
  of inner product spaces with the converse min–max localization property.
* `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: the scalar factorization for a complete
  inner product source space.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §5,
  Theorem 5.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.11.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean`: an earlier Lean formalization of the factorization.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Scalar factorization.** On a pair of inner product spaces with the converse min–max
localization property, for every `T : E →L[𝕜] F` and every `0 ≤ c < aₙ(T)` there are
contractions `A : ℓ₂^{n+1} → E` and `B : F → ℓ₂^{n+1}` with `B ∘ T ∘ A = c • id`. -/
theorem HasMinMaxLowerBound.exists_comp_comp_eq_smul_id (h : HasMinMaxLowerBound 𝕜 E F)
    (T : E →L[𝕜] F) {n : ℕ} {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  -- `T` is `t`-coercive, `c < t`, on a subspace `V` of rank `n + 1`.
  set t : ℝ := (c + T.singularValue n) / 2
  have hct : c < t := by simp only [t]; linarith
  have ht : 0 < t := hc₀.trans_lt hct
  obtain ⟨V, hVrank, hV⟩ := h.exists_rank_eq_coercive T ht.le fun k hk ↦
    (show t < T.singularValue n by simp only [t]; linarith).trans_le
      (NNReal.coe_le_coe.mpr (T.antitone_singularValue (Nat.lt_succ_iff.mp hk)))
  have : FiniteDimensional 𝕜 V := Module.finite_of_rank_eq_nat hVrank
  have hVfin : Module.finrank 𝕜 V = n + 1 := Module.finrank_eq_of_rank_eq hVrank
  -- `A` is an isometry of `ℓ₂^{n+1}` onto `V`.
  set e : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] E :=
    V.subtypeₗᵢ.comp
      ((stdOrthonormalBasis 𝕜 V).reindex (finCongr hVfin)).repr.symm.toLinearIsometry
  set A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] E := e.toContinuousLinearMap
  set S : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] F := T ∘L A
  have hS (x : EuclideanSpace 𝕜 (Fin (n + 1))) : t * ‖x‖ ≤ ‖S x‖ := by
    have h := hV (e x) (by simp [e])
    rwa [e.norm_map] at h
  have hSinj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
    have := hS x
    rw [hx, norm_zero] at this
    nlinarith [norm_nonneg x]
  -- `G` inverts `S` on its range `W`, with norm at most `t⁻¹`.
  set W : Submodule 𝕜 F := LinearMap.range (S : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] F)
  set eS := LinearEquiv.ofInjective (S : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] F) hSinj
  set G : W →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    LinearMap.toContinuousLinearMap (eS.symm : W →ₗ[𝕜] _)
  have hG : ‖G‖ ≤ t⁻¹ := by
    refine G.opNorm_le_bound (inv_nonneg.mpr ht.le) fun w ↦ ?_
    obtain ⟨x, rfl⟩ := eS.surjective w
    have hx : ((eS x : W) : F) = S x := LinearEquiv.ofInjective_apply _ _
    rw [inv_mul_eq_div, le_div_iff₀ ht, mul_comm, ← Submodule.norm_coe, hx]
    simpa [G] using hS x
  have hGS (x : EuclideanSpace 𝕜 (Fin (n + 1))) : G (W.orthogonalProjectionOnto (S x)) = x := by
    have hx : (⟨S x, LinearMap.mem_range_self _ x⟩ : W) = eS x :=
      Subtype.ext (LinearEquiv.ofInjective_apply _ _).symm
    rw [W.orthogonalProjectionOnto_mem_subspace_eq_self ⟨S x, LinearMap.mem_range_self _ x⟩, hx]
    simp [G]
  -- `B = c • G ∘ P_W` has norm at most `c / t ≤ 1`.
  refine ⟨A, (c : 𝕜) • (G ∘L W.orthogonalProjectionOnto), e.norm_toContinuousLinearMap_le,
    ?_, ?_⟩
  · calc ‖(c : 𝕜) • (G ∘L W.orthogonalProjectionOnto)‖
        ≤ ‖(c : 𝕜)‖ * (‖G‖ * ‖W.orthogonalProjectionOnto‖) :=
          (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_left (G.opNorm_comp_le _) (norm_nonneg _))
      _ ≤ c * (t⁻¹ * 1) := by
          rw [RCLike.norm_ofReal, abs_of_nonneg hc₀]
          gcongr
          exact W.orthogonalProjectionOnto_norm_le
      _ ≤ 1 := by rw [mul_one, ← div_eq_mul_inv, div_le_one ht]; exact hct.le
  · ext1 x
    simpa [S] using congrArg ((c : 𝕜) • ·) (hGS x)

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Scalar factorization.** If `E` is a complete inner product space, then for every
`T : E →L[𝕜] F` into an inner product space and every `0 ≤ c < aₙ(T)` there are contractions
`A : ℓ₂^{n+1} → E` and `B : F → ℓ₂^{n+1}` with `B ∘ T ∘ A = c • id`. -/
theorem exists_comp_comp_eq_smul_id (T : E →L[𝕜] F) {n : ℕ} {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) :=
  TauCeti.HasMinMaxLowerBound.of_completeSpace.exists_comp_comp_eq_smul_id T hc₀ hc

end ContinuousLinearMap
