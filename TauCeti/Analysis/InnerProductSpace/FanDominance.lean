/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic

/-!
# Fan dominance

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

## Main results

* `LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le`: the orbit-hull characterization of
  Ky Fan domination.
* `TauCeti.UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`: Fan dominance.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Theorem IV.2.2.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. Oxford
  Ser. (2) **11** (1960), 50–59.
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section DiagonalSum

variable {ι : Type*} [Fintype ι]

variable (𝕜) in
/-- The map `∑ᵢ xᵢ wᵢ ⊗ vᵢ`, sending `y` to `∑ᵢ xᵢ ⟪vᵢ, y⟫ wᵢ`. For orthonormal families `(vᵢ)`
and `(wᵢ)` and a nonnegative tuple `x`, this is the map with singular system `(vᵢ, wᵢ, xᵢ)`. -/
private noncomputable def diagonalSum (v : ι → E) (w : ι → F) (x : ι → ℝ) : E →ₗ[𝕜] F :=
  ∑ i, (x i : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap

private theorem diagonalSum_apply (v : ι → E) (w : ι → F) (x : ι → ℝ) (y : E) :
    diagonalSum 𝕜 v w x y = ∑ i, (x i : 𝕜) • ⟪v i, y⟫ • w i := by
  simp [diagonalSum]

/-- Unitaries on either side act on the vectors of a diagonal sum. -/
private theorem linearIsometryEquiv_comp_diagonalSum_comp (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (v : ι → E) (w : ι → F) (x : ι → ℝ) :
    (U : F →ₗ[𝕜] F) ∘ₗ diagonalSum 𝕜 v w x ∘ₗ (V : E →ₗ[𝕜] E) =
      diagonalSum 𝕜 (V.symm ∘ v) (U ∘ w) x := by
  ext y
  simp [diagonalSum_apply, LinearIsometryEquiv.inner_map_eq_flip]

private theorem diagonalSum_add_smul (v : ι → E) (w : ι → F) (x y : ι → ℝ) (a b : ℝ) :
    diagonalSum 𝕜 v w (a • x + b • y) =
      (a : 𝕜) • diagonalSum 𝕜 v w x + (b : 𝕜) • diagonalSum 𝕜 v w y := by
  simp only [diagonalSum, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp

/-- Permuting the coefficients of a diagonal sum permutes its vectors. -/
private theorem diagonalSum_comp_perm (v : ι → E) (w : ι → F) (x : ι → ℝ) (π : Equiv.Perm ι) :
    diagonalSum 𝕜 v w (x ∘ π) = diagonalSum 𝕜 (v ∘ π.symm) (w ∘ π.symm) x := by
  simp only [diagonalSum, Function.comp_apply]
  exact (π.symm.sum_comp fun i ↦ (x (π i) : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap).symm.trans
    (by simp)

/-- Changing the sign of one coefficient of a diagonal sum changes the sign of one vector. -/
private theorem diagonalSum_update_neg [DecidableEq ι] (v : ι → E) (w : ι → F) (x : ι → ℝ)
    (i : ι) :
    diagonalSum 𝕜 v w (Function.update x i (-x i)) =
      diagonalSum 𝕜 v (Function.update w i (-w i)) x := by
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Diagonal sums over two pairs of orthonormal families with the same coefficients are related by
unitaries of the source and of the target. -/
private theorem diagonalSum_mem_twoSidedUnitaryOrbit {v v' : ι → E} {w w' : ι → F}
    (hv : Orthonormal 𝕜 v) (hv' : Orthonormal 𝕜 v') (hw : Orthonormal 𝕜 w)
    (hw' : Orthonormal 𝕜 w') (x : ι → ℝ) :
    diagonalSum 𝕜 v' w' x ∈ (diagonalSum 𝕜 v w x).twoSidedUnitaryOrbit := by
  classical
  obtain ⟨P, hP⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq (v := v) (w := v') fun i j ↦ by
    rw [orthonormal_iff_ite.mp hv, orthonormal_iff_ite.mp hv']
  obtain ⟨Q, hQ⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq (v := w) (w := w') fun i j ↦ by
    rw [orthonormal_iff_ite.mp hw, orthonormal_iff_ite.mp hw']
  refine mem_twoSidedUnitaryOrbit.mpr ⟨Q, P.symm, ?_⟩
  rw [linearIsometryEquiv_comp_diagonalSum_comp, LinearIsometryEquiv.symm_symm]
  congr 1 <;> ext i <;> simp [hP, hQ]

end DiagonalSum

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
      simpa only [diagonalSum] using hA
    replace hC : C = diagonalSum 𝕜 vC wC fun i ↦ C.singularValues i := by
      simpa only [diagonalSum] using hC
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

end TauCeti.UnitarilyInvariantSeminorm
