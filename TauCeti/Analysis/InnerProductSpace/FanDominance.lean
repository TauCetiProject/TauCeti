/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.DiagonalSum
public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Fan dominance and the ideal inequalities

For linear maps `A C : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, this file
proves that `A` lies in the convex hull of the two-sided unitary orbit `{U C V}` of `C` exactly
when every Ky Fan sum of `A` is at most the corresponding Ky Fan sum of `C`:

  `A ∈ conv {U C V} ↔ ∀ k, σ₀(A) + ⋯ + σₖ₋₁(A) ≤ σ₀(C) + ⋯ + σₖ₋₁(C)`.

Every unitarily invariant seminorm is bounded on that hull by its value at `C`, so this gives
**Fan dominance**: if the Ky Fan sums of `A` are dominated by those of `C`, then `N A ≤ N C` for
every unitarily invariant seminorm `N`. A single family of Ky Fan estimates thus yields the
corresponding estimates in the operator, Frobenius, Ky Fan and nuclear norms at once.

The hard direction reduces to the transfer descent for weak majorization
(`TauCeti.IsSymmetricConvex.mem_of_prefixSum_le`). With `p = min (dim E) (dim F)`, write
`C = ∑ᵢ σᵢ(C) wᵢ ⊗ vᵢ` over orthonormal families `(vᵢ)_{i < p}` and `(wᵢ)_{i < p}`
(`LinearMap.exists_orthonormal_eq_sum_singularValues_smul_rankOne`). The tuples
`x : Fin p → ℝ` with `∑ᵢ xᵢ wᵢ ⊗ vᵢ` in the hull form a symmetric convex set: permuting or changing
the sign of the coordinates of `x` amounts to permuting or changing the sign of the vectors `wᵢ`
and `vᵢ`, which is realized by unitaries of `F` and `E`. This set contains the singular values of
`C`, so it contains those of `A`, which are weakly majorized by them; and `A` itself is a unitary
multiple of `∑ᵢ σᵢ(A) wᵢ ⊗ vᵢ`.

Two consequences follow. Since `σᵢ(C A) ≤ ‖C‖ σᵢ(A)`, Fan dominance gives the **ideal
inequalities** `N (C A) ≤ ‖C‖ N A` and, through adjoints, `N (A C) ≤ ‖C‖ N A`. Applied to the
inverse of a map `C` bounded below by `c > 0`, they give the reverse inequalities
`c N A ≤ N (C A)` and `c N A ≤ N (A C)`.

## Main results

* `LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le`: the orbit-hull characterization of
  Ky Fan domination.
* `TauCeti.UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`: Fan dominance.
* `TauCeti.UnitarilyInvariantSeminorm.map_comp_le_left`,
  `TauCeti.UnitarilyInvariantSeminorm.map_comp_le_right`: the ideal inequalities.
* `TauCeti.UnitarilyInvariantSeminorm.mul_map_le_map_comp_left`,
  `TauCeti.UnitarilyInvariantSeminorm.mul_map_le_map_comp_right`: the reverse ideal inequalities
  for factors bounded below.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Theorem IV.2.2
  (Fan dominance) and Proposition IV.2.4 (ideal inequalities).
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. Oxford
  Ser. (2) **11** (1960), 50–59.
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- **Orbit-hull characterization of Ky Fan domination.** A map `A` lies in the convex hull of the
two-sided unitary orbit of `C` exactly when every Ky Fan sum of `A` is at most the corresponding
Ky Fan sum of `C`. -/
theorem mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le {A C : E →ₗ[𝕜] F} :
    A ∈ C.twoSidedUnitaryOrbitHull ↔ ∀ k, A.kyFanSum k ≤ C.kyFanSum k := by
  constructor
  · -- Each Ky Fan sum is subadditive, homogeneous, and constant on the orbit of `C`.
    intro hA k
    obtain ⟨n, t, Y, ht, htsum, hY, rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp hA
    calc (∑ i, (t i : 𝕜) • Y i).kyFanSum k ≤ ∑ i, ((t i : 𝕜) • Y i).kyFanSum k :=
          Finset.le_sum_of_subadditive (kyFanSum · k) (by simp) (fun X Y ↦ kyFanSum_add_le X Y k)
            _ _
      _ = ∑ i, t i * C.kyFanSum k := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [kyFanSum_smul, RCLike.norm_ofReal, abs_of_nonneg (ht i), kyFanSum_def,
            kyFanSum_def, singularValues_eq_of_mem_twoSidedUnitaryOrbit (hY i)]
      _ = C.kyFanSum k := by rw [← Finset.sum_mul, htsum, one_mul]
  · intro h
    classical
    obtain ⟨vA, wA, hvA, hwA, hA⟩ := A.exists_orthonormal_eq_sum_singularValues_smul_rankOne
    obtain ⟨vC, wC, hvC, hwC, hC⟩ := C.exists_orthonormal_eq_sum_singularValues_smul_rankOne
    replace hA : A = diagonalSum 𝕜 vA wA fun i ↦ A.singularValues i := by
      simpa only [diagonalSum_def] using hA
    replace hC : C = diagonalSum 𝕜 vC wC fun i ↦ C.singularValues i := by
      simpa only [diagonalSum_def] using hC
    -- The coefficient tuples `x` whose diagonal sum over `(vC, wC)` lies in the hull form a
    -- symmetric convex set.
    let K : Set (Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ) :=
      {x | diagonalSum 𝕜 vC wC x ∈ C.twoSidedUnitaryOrbitHull}
    have horbit {v : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → E}
        {w : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → F} (hv : Orthonormal 𝕜 v)
        (hw : Orthonormal 𝕜 w) {x} (hx : x ∈ K) :
        diagonalSum 𝕜 v w x ∈ C.twoSidedUnitaryOrbitHull := by
      obtain ⟨U, V, hUV⟩ :=
        mem_twoSidedUnitaryOrbit.mp (diagonalSum_mem_twoSidedUnitaryOrbit hvC hv hwC hw x)
      rw [← hUV]
      exact linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbitHull hx U V
    have hK : TauCeti.IsSymmetricConvex K := by
      refine ⟨fun x hx y hy a b ha hb hab ↦ ?_, fun π x hx ↦ ?_, fun x hx i ↦ ?_⟩
      · simpa only [K, Set.mem_ofPred_eq, diagonalSum_add_smul] using
          smul_add_smul_mem_twoSidedUnitaryOrbitHull hx hy ha hb hab
      · simpa only [K, Set.mem_ofPred_eq, diagonalSum_comp_perm] using
          horbit (hvC.comp _ π.symm.injective) (hwC.comp _ π.symm.injective) hx
      · have hw : Orthonormal 𝕜 (Function.update wC i (-wC i)) :=
          hwC.orthonormal_of_forall_eq_or_eq_neg fun j ↦ by
            rcases eq_or_ne j i with rfl | hj
            · simp
            · simp [Function.update_of_ne hj]
        simpa only [K, Set.mem_ofPred_eq, diagonalSum_update_neg] using horbit hvC hw hx
    have hCK : (fun i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) ↦ C.singularValues i) ∈ K := by
      simp only [K, Set.mem_ofPred_eq, ← hC, self_mem_twoSidedUnitaryOrbitHull]
    -- The singular values of `A` are weakly majorized by those of `C`, so they lie in `K`.
    have hAK : (fun i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) ↦ A.singularValues i) ∈ K :=
      hK.mem_of_prefixSum_le hCK (fun _ _ hij ↦ A.singularValues_antitone hij)
        (fun _ ↦ A.singularValues_nonneg _) fun k ↦ by
          simpa only [TauCeti.prefixSum_eq_sum_range, kyFanSum_def] using h _
    rw [hA]
    exact horbit hvA hwA hAK

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Fan dominance.** If every Ky Fan sum of `A` is at most the corresponding Ky Fan sum of `C`,
then `N A ≤ N C` for every unitarily invariant seminorm `N`. -/
theorem map_le_of_kyFanSum_le (N : UnitarilyInvariantSeminorm 𝕜 E F) {A C : E →ₗ[𝕜] F}
    (h : ∀ k, A.kyFanSum k ≤ C.kyFanSum k) : N A ≤ N C :=
  N.map_le_of_mem_twoSidedUnitaryOrbitHull
    (LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr h)

/-! ### Ideal inequalities -/

/-- **Ideal inequality, left factor.** If `‖C y‖ ≤ c * ‖y‖` for every `y` (for `c ≥ 0`: if `C` has
operator norm at most `c`), then `N (C A) ≤ c * N A` for every unitarily invariant seminorm `N`. -/
theorem map_comp_le_left (N : UnitarilyInvariantSeminorm 𝕜 E F) (C : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F)
    {c : ℝ} (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (C ∘ₗ A) ≤ c * N A := by
  rcases lt_or_ge c 0 with hc | hc
  · -- A negative constant forces `A = 0`.
    have hA : A = 0 := LinearMap.ext fun x ↦ norm_le_zero_iff.mp <|
      nonpos_of_mul_nonneg_right ((norm_nonneg _).trans (hC (A x))) hc
    simp [hA]
  calc N (C ∘ₗ A) ≤ N ((c : 𝕜) • A) := N.map_le_of_kyFanSum_le fun k ↦ by
        simp only [LinearMap.kyFanSum_def, LinearMap.singularValues_smul, RCLike.norm_ofReal,
          abs_of_nonneg hc, Finsupp.smul_apply, smul_eq_mul]
        exact Finset.sum_le_sum fun i _ ↦ LinearMap.singularValues_comp_le C A hC i
    _ = c * N A := by rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg hc]

/-- **Ideal inequality, right factor.** If `‖C x‖ ≤ c * ‖x‖` for every `x` (for `c ≥ 0`: if `C`
has operator norm at most `c`), then `N (A C) ≤ c * N A` for every unitarily invariant seminorm
`N`. -/
theorem map_comp_le_right (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E)
    {c : ℝ} (hC : ∀ x, ‖C x‖ ≤ c * ‖x‖) : N (A ∘ₗ C) ≤ c * N A := by
  rcases lt_or_ge c 0 with hc | hc
  · -- A negative constant forces `E = 0`.
    have hE (x : E) : x = 0 := norm_le_zero_iff.mp <|
      nonpos_of_mul_nonneg_right ((norm_nonneg _).trans (hC x)) hc
    have hA : A = 0 := LinearMap.ext fun x ↦ by simp [hE x]
    simp [hA]
  -- Pass to adjoints, where `C†` is a left factor with the same bound.
  have h := N.compAdjoint.map_comp_le_left (LinearMap.adjoint C) (LinearMap.adjoint A)
    (LinearMap.norm_adjoint_apply_le hc hC)
  rwa [compAdjoint_apply, compAdjoint_apply, ← LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.adjoint_adjoint] at h

/-- **Reverse ideal inequality, left factor.** If `c * ‖y‖ ≤ ‖C y‖` for every `y`, then
`c * N A ≤ N (C A)` for every unitarily invariant seminorm `N`. -/
theorem mul_map_le_map_comp_left (N : UnitarilyInvariantSeminorm 𝕜 E F) (C : F →ₗ[𝕜] F)
    (A : E →ₗ[𝕜] F) {c : ℝ} (hC : ∀ y, c * ‖y‖ ≤ ‖C y‖) : c * N A ≤ N (C ∘ₗ A) := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (apply_nonneg _ _)).trans (apply_nonneg _ _)
  -- `A = C⁻¹ (C A)` and `C⁻¹` has operator norm at most `c⁻¹`.
  obtain ⟨G, -, hGC, hG⟩ := LinearMap.exists_comp_eq_id_of_mul_norm_le hc hC
  have h := N.map_comp_le_left G (C ∘ₗ A) hG
  rw [← LinearMap.comp_assoc, hGC, LinearMap.id_comp] at h
  rwa [le_inv_mul_iff₀ hc] at h

/-- **Reverse ideal inequality, right factor.** If `c * ‖x‖ ≤ ‖C x‖` for every `x`, then
`c * N A ≤ N (A C)` for every unitarily invariant seminorm `N`. -/
theorem mul_map_le_map_comp_right (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E →ₗ[𝕜] F)
    (C : E →ₗ[𝕜] E) {c : ℝ} (hC : ∀ x, c * ‖x‖ ≤ ‖C x‖) : c * N A ≤ N (A ∘ₗ C) := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (apply_nonneg _ _)).trans (apply_nonneg _ _)
  -- `A = (A C) C⁻¹` and `C⁻¹` has operator norm at most `c⁻¹`.
  obtain ⟨G, hCG, -, hG⟩ := LinearMap.exists_comp_eq_id_of_mul_norm_le hc hC
  have h := N.map_comp_le_right (A ∘ₗ C) G hG
  rw [LinearMap.comp_assoc, hCG, LinearMap.comp_id] at h
  rwa [le_inv_mul_iff₀ hc] at h

end TauCeti.UnitarilyInvariantSeminorm
