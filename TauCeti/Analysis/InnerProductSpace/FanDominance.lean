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
# Fan dominance and the gauge representation

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
inequalities** `N (C A) ≤ ‖C‖ N A` and, through adjoints, `N (A C) ≤ ‖C‖ N A`.

The same diagonal sums give the **gauge representation** of von Neumann and Mirsky. The gauge
`g = N.gauge` of a unitarily invariant seminorm `N` sends `x : Fin p → ℝ` to `N (∑ᵢ xᵢ wᵢ ⊗ vᵢ)`
for any orthonormal families `(vᵢ)` and `(wᵢ)`. By the symmetries above it is a symmetric gauge:
a seminorm on `p`-tuples invariant under permuting coordinates and changing their signs. The
singular value decomposition of `A` then reads `N A = g (σ₀(A), …, σₚ₋₁(A))`. Conversely, every
symmetric gauge `g` on `p`-tuples defines the unitarily invariant seminorm
`A ↦ g (σ₀(A), …, σₚ₋₁(A))`, whose subadditivity is the weak majorization
`σ(A + B) ≺w σ(A) + σ(B)`, and the two constructions are mutually inverse.

## Main results

* `LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le`: the orbit-hull characterization of
  Ky Fan domination.
* `TauCeti.UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`: Fan dominance.
* `TauCeti.UnitarilyInvariantSeminorm.map_comp_le_left`,
  `TauCeti.UnitarilyInvariantSeminorm.map_comp_le_right`: the ideal inequalities.
* `TauCeti.UnitarilyInvariantSeminorm.gauge`: the symmetric gauge of a unitarily invariant
  seminorm, with `TauCeti.UnitarilyInvariantSeminorm.isSymmetricGauge_gauge`.
* `TauCeti.UnitarilyInvariantSeminorm.map_eq_gauge_singularValues`: the gauge representation
  `N A = N.gauge (σ₀(A), …, σₚ₋₁(A))`; `exists_isSymmetricGauge_forall_map_eq` restates it for
  square operators with tuples of length `dim E`.
* `TauCeti.UnitarilyInvariantSeminorm.ofIsSymmetricGauge`: the unitarily invariant seminorm of a
  symmetric gauge; `ofIsSymmetricGauge_gauge` and `gauge_ofIsSymmetricGauge` show that the two
  constructions are mutually inverse.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Theorem IV.2.2
  (Fan dominance), Proposition IV.2.4 (ideal inequalities) and Theorem IV.2.1 (gauge
  representation).
* J. von Neumann, *Some matrix-inequalities and metrization of matric-space*, Tomsk Univ. Rev.
  **1** (1937), 286–300.
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

private theorem diagonalSum_add (v : ι → E) (w : ι → F) (x y : ι → ℝ) :
    diagonalSum 𝕜 v w (x + y) = diagonalSum 𝕜 v w x + diagonalSum 𝕜 v w y := by
  simpa using diagonalSum_add_smul (𝕜 := 𝕜) v w x y 1 1

private theorem diagonalSum_smul (v : ι → E) (w : ι → F) (a : ℝ) (x : ι → ℝ) :
    diagonalSum 𝕜 v w (a • x) = (a : 𝕜) • diagonalSum 𝕜 v w x := by
  simpa using diagonalSum_add_smul (𝕜 := 𝕜) v w x 0 a 0

private theorem diagonalSum_neg (v : ι → E) (w : ι → F) (x : ι → ℝ) :
    diagonalSum 𝕜 v w (-x) = -diagonalSum 𝕜 v w x := by
  simpa using diagonalSum_smul (𝕜 := 𝕜) v w (-1) x

/-- Over an orthonormal family `(wᵢ)`, `‖(∑ᵢ xᵢ wᵢ ⊗ vᵢ) y‖² = ∑ᵢ xᵢ² ‖⟪vᵢ, y⟫‖²`. -/
private theorem norm_diagonalSum_apply_sq (v : ι → E) {w : ι → F} (hw : Orthonormal 𝕜 w)
    (x : ι → ℝ) (y : E) :
    ‖diagonalSum 𝕜 v w x y‖ ^ 2 = ∑ i, x i ^ 2 * ‖⟪v i, y⟫‖ ^ 2 := by
  set c : ι → 𝕜 := fun i ↦ (x i : 𝕜) * ⟪v i, y⟫
  have hD : diagonalSum 𝕜 v w x y = ∑ i, c i • w i := by
    simp [c, diagonalSum_apply, smul_smul]
  have h := hw.inner_sum c c Finset.univ
  simp only [RCLike.conj_mul, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖∑ i, c i • w i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast h
  rw [hD, h']
  simp [c, norm_mul, mul_pow]

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

/-! ### The gauge representation -/

/-- The first `min (dim E) (dim F)` vectors of the standard orthonormal basis of `E`. -/
private noncomputable abbrev stdFamilyLeft (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] :
    Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → E :=
  stdOrthonormalBasis 𝕜 E ∘ Fin.castLE (min_le_left _ _)

/-- The first `min (dim E) (dim F)` vectors of the standard orthonormal basis of `F`. -/
private noncomputable abbrev stdFamilyRight (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → F :=
  stdOrthonormalBasis 𝕜 F ∘ Fin.castLE (min_le_right _ _)

omit [FiniteDimensional 𝕜 F] in
private theorem orthonormal_stdFamilyLeft : Orthonormal 𝕜 (stdFamilyLeft 𝕜 E F) :=
  (stdOrthonormalBasis 𝕜 E).orthonormal.comp _ (Fin.castLE_injective _)

omit [FiniteDimensional 𝕜 E] in
private theorem orthonormal_stdFamilyRight : Orthonormal 𝕜 (stdFamilyRight 𝕜 E F) :=
  (stdOrthonormalBasis 𝕜 F).orthonormal.comp _ (Fin.castLE_injective _)

/-- The **symmetric gauge** of a unitarily invariant seminorm `N` on `E →ₗ[𝕜] F`: with
`p = min (dim E) (dim F)`, its value at `x : Fin p → ℝ` is `N (∑ᵢ xᵢ wᵢ ⊗ vᵢ)` for orthonormal
families `(vᵢ)` in `E` and `(wᵢ)` in `F`, which does not depend on the choice of the families
(`TauCeti.UnitarilyInvariantSeminorm.gauge_apply`). It is a symmetric gauge
(`TauCeti.UnitarilyInvariantSeminorm.isSymmetricGauge_gauge`), and `N A` is its value at the
singular values of `A` (`TauCeti.UnitarilyInvariantSeminorm.map_eq_gauge_singularValues`). -/
noncomputable def gauge (N : UnitarilyInvariantSeminorm 𝕜 E F) :
    Seminorm ℝ (Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ) where
  toFun x := N (LinearMap.diagonalSum 𝕜 (stdFamilyLeft 𝕜 E F) (stdFamilyRight 𝕜 E F) x)
  map_zero' := by simp [LinearMap.diagonalSum]
  add_le' x y := by
    simp only [LinearMap.diagonalSum_add]
    exact map_add_le_add N _ _
  neg' x := by simp only [LinearMap.diagonalSum_neg, map_neg_eq_map]
  smul' a x := by
    simp only [LinearMap.diagonalSum_smul, map_smul_eq_mul, RCLike.norm_ofReal, Real.norm_eq_abs]

/-- The gauge of `N` is computed by diagonal sums over any orthonormal families. -/
private theorem gauge_eq_diagonalSum (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {v : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → E}
    {w : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → F} (hv : Orthonormal 𝕜 v)
    (hw : Orthonormal 𝕜 w) (x : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ) :
    N.gauge x = N (LinearMap.diagonalSum 𝕜 v w x) :=
  (N.map_eq_of_mem_twoSidedUnitaryOrbit <| LinearMap.diagonalSum_mem_twoSidedUnitaryOrbit
    orthonormal_stdFamilyLeft hv orthonormal_stdFamilyRight hw x).symm

/-- The gauge of `N` evaluated through arbitrary orthonormal families: with `p = min (dim E)
(dim F)`, `N.gauge x = N (∑ᵢ xᵢ wᵢ ⊗ vᵢ)` for all orthonormal families `(vᵢ)_{i < p}` in `E` and
`(wᵢ)_{i < p}` in `F`. -/
theorem gauge_apply (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {v : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → E}
    {w : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → F} (hv : Orthonormal 𝕜 v)
    (hw : Orthonormal 𝕜 w) (x : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ) :
    N.gauge x = N (∑ i, (x i : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap) :=
  N.gauge_eq_diagonalSum hv hw x

/-- The gauge of a unitarily invariant seminorm is a symmetric gauge. -/
theorem isSymmetricGauge_gauge (N : UnitarilyInvariantSeminorm 𝕜 E F) :
    N.gauge.IsSymmetricGauge where
  map_comp_perm π x := by
    rw [N.gauge_eq_diagonalSum orthonormal_stdFamilyLeft orthonormal_stdFamilyRight,
      LinearMap.diagonalSum_comp_perm, ← N.gauge_eq_diagonalSum
        (orthonormal_stdFamilyLeft.comp _ π.symm.injective)
        (orthonormal_stdFamilyRight.comp _ π.symm.injective)]
  map_update_neg x i := by
    have hw : Orthonormal 𝕜
        (Function.update (stdFamilyRight 𝕜 E F) i (-stdFamilyRight 𝕜 E F i)) :=
      orthonormal_stdFamilyRight.orthonormal_of_forall_eq_or_eq_neg fun j ↦ by
        rcases eq_or_ne j i with rfl | hj
        · simp
        · simp [Function.update_of_ne hj]
    rw [N.gauge_eq_diagonalSum orthonormal_stdFamilyLeft orthonormal_stdFamilyRight,
      LinearMap.diagonalSum_update_neg, ← N.gauge_eq_diagonalSum orthonormal_stdFamilyLeft hw]

/-- **Gauge representation.** Every unitarily invariant seminorm `N` on `E →ₗ[𝕜] F` is a symmetric
gauge of the singular values: `N A = g (σ₀(A), …, σₚ₋₁(A))` with `p = min (dim E) (dim F)` and
`g = N.gauge`. For square operators `p = dim E`. -/
theorem map_eq_gauge_singularValues (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E →ₗ[𝕜] F) :
    N A = N.gauge fun i ↦ A.singularValues i := by
  obtain ⟨v, w, hv, hw, hA⟩ := A.exists_orthonormal_eq_sum_singularValues_smul_rankOne
  rw [N.gauge_apply hv hw, ← hA]

/-- **Gauge representation for square operators.** Every unitarily invariant seminorm `N` on the
endomorphisms of `E` is a symmetric gauge of the `dim E` singular values of its argument. This is
`TauCeti.UnitarilyInvariantSeminorm.map_eq_gauge_singularValues` with the gauge reindexed along
`min (dim E) (dim E) = dim E`. -/
theorem exists_isSymmetricGauge_forall_map_eq (N : UnitarilyInvariantSeminorm 𝕜 E E) :
    ∃ g : Seminorm ℝ (Fin (finrank 𝕜 E) → ℝ), g.IsSymmetricGauge ∧
      ∀ A, N A = g fun i ↦ A.singularValues i := by
  let e := finCongr (min_self (finrank 𝕜 E))
  refine ⟨N.gauge.comp (LinearMap.funLeft ℝ ℝ e), N.isSymmetricGauge_gauge.comp_funLeft e,
    fun A ↦ ?_⟩
  rw [N.map_eq_gauge_singularValues, Seminorm.comp_apply]
  -- Reindexing along `Fin.cast` does not change the underlying natural-number indices.
  congr 1

/-! ### Unitarily invariant seminorms from symmetric gauges -/

/-- The unitarily invariant seminorm `A ↦ g (σ₀(A), …, σₙ₋₁(A))` of a symmetric gauge `g` on
`n`-tuples. Subadditivity comes from the weak majorization `σ(A + B) ≺w σ(A) + σ(B)`, along which
symmetric gauges are monotone. -/
noncomputable def ofIsSymmetricGauge {n : ℕ} (g : Seminorm ℝ (Fin n → ℝ))
    (hg : g.IsSymmetricGauge) : UnitarilyInvariantSeminorm 𝕜 E F where
  toFun A := g fun i ↦ A.singularValues i
  map_zero' := by
    simp only [LinearMap.singularValues_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact map_zero g
  add_le' A B := by
    calc g (fun i ↦ (A + B).singularValues i)
        ≤ g ((fun i : Fin n ↦ A.singularValues i) + fun i : Fin n ↦ B.singularValues i) :=
          (LinearMap.isWeaklyMajorizedBy_singularValues_add A B n).apply_le hg
      _ ≤ _ := map_add_le_add g _ _
  neg' A := by
    rw [← neg_one_smul 𝕜 A, LinearMap.singularValues_smul]
    simp
  smul' c A := by
    have h : (fun i : Fin n ↦ (c • A).singularValues i) =
        ‖c‖ • fun i : Fin n ↦ A.singularValues i := by
      ext i
      rw [Pi.smul_apply, LinearMap.singularValues_smul, Finsupp.smul_apply]
    rw [h, map_smul_eq_mul, norm_norm]
  map_linearIsometryEquiv_comp_comp' U V A := congrArg g <| funext fun i ↦ by
    rw [LinearMap.singularValues_linearIsometryEquiv_comp,
      LinearMap.singularValues_comp_linearIsometryEquiv]

@[simp]
theorem ofIsSymmetricGauge_apply {n : ℕ} (g : Seminorm ℝ (Fin n → ℝ)) (hg : g.IsSymmetricGauge)
    (A : E →ₗ[𝕜] F) : ofIsSymmetricGauge g hg A = g fun i ↦ A.singularValues i :=
  (rfl)

/-- A unitarily invariant seminorm is recovered from its gauge. -/
@[simp]
theorem ofIsSymmetricGauge_gauge (N : UnitarilyInvariantSeminorm 𝕜 E F) :
    ofIsSymmetricGauge N.gauge N.isSymmetricGauge_gauge = N :=
  ext fun A ↦ (N.map_eq_gauge_singularValues A).symm

/-- With `p = min (dim E) (dim F)`, the diagonal sum `∑ᵢ yᵢ wᵢ ⊗ vᵢ` over the standard orthonormal
families has the singular values `y` when `y` is nonincreasing and nonnegative. -/
private theorem singularValues_diagonalSum_stdFamily
    {y : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ} (hy : Antitone y) (hy0 : 0 ≤ y)
    (i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F))) :
    (LinearMap.diagonalSum 𝕜 (stdFamilyLeft 𝕜 E F) (stdFamilyRight 𝕜 E F) y).singularValues i =
      y i := by
  set e := stdOrthonormalBasis 𝕜 E
  -- The diagonal operator of `y`, padded by zeros, in the basis `e`.
  let d : Fin (finrank 𝕜 E) → ℝ := fun k ↦
    if h : (k : ℕ) < min (finrank 𝕜 E) (finrank 𝕜 F) then y ⟨k, h⟩ else 0
  have hd0 (k : Fin (finrank 𝕜 E)) : 0 ≤ d k := by
    simp only [d]
    split_ifs
    exacts [hy0 _, le_rfl]
  have hdiag : LinearMap.diagonalSum 𝕜 e e d =
      Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal fun k ↦ (d k : 𝕜)) := by
    refine e.toBasis.ext fun k ↦ ?_
    rw [OrthonormalBasis.coe_toBasis, Matrix.toLin_diagonal_apply_self,
      LinearMap.diagonalSum_apply]
    simp [orthonormal_iff_ite.mp e.orthonormal]
  -- Both maps have the same norms, `∑ᵢ yᵢ² ‖⟪eᵢ, z⟫‖²`.
  have hnorm (z : E) :
      ‖LinearMap.diagonalSum 𝕜 (stdFamilyLeft 𝕜 E F) (stdFamilyRight 𝕜 E F) y z‖ =
        ‖LinearMap.diagonalSum 𝕜 e e d z‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [LinearMap.norm_diagonalSum_apply_sq _ orthonormal_stdFamilyRight,
      LinearMap.norm_diagonalSum_apply_sq _ e.orthonormal]
    refine Fintype.sum_of_injective (Fin.castLE (min_le_left _ _)) (Fin.castLE_injective _) _ _
      (fun k hk ↦ ?_) fun j ↦ ?_
    · have hk' : ¬ (k : ℕ) < min (finrank 𝕜 E) (finrank 𝕜 F) := fun h ↦ hk ⟨⟨k, h⟩, rfl⟩
      simp only [d, hk', ↓reduceDIte]
      ring
    · simp only [d, Fin.val_castLE, j.isLt, ↓reduceDIte, Fin.eta, Function.comp_apply, e]
  have hanti : Antitone fun k ↦ ‖(d k : 𝕜)‖ := fun k l hkl ↦ by
    dsimp only
    rw [RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg (hd0 k), abs_of_nonneg (hd0 l)]
    by_cases hl : (l : ℕ) < min (finrank 𝕜 E) (finrank 𝕜 F)
    · have hk := lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hkl) hl
      simp only [d, hl, hk, ↓reduceDIte]
      exact hy (Fin.mk_le_mk.mpr hkl)
    · simp only [d, hl, ↓reduceDIte]
      exact hd0 k
  have h := Matrix.singularValues_toLin_diagonal e (fun k ↦ (d k : 𝕜)) (Equiv.refl _) hanti
    (Fin.castLE (min_le_left _ _) i)
  rw [LinearMap.singularValues_eq_of_norm_apply_eq hnorm, hdiag]
  have hi := (lt_min_iff.mp i.isLt).2
  simpa [d, hi, abs_of_nonneg (hy0 i)] using h

/-- A symmetric gauge is recovered from its unitarily invariant seminorm: with
`p = min (dim E) (dim F)`, the gauge of `A ↦ g (σ₀(A), …, σₚ₋₁(A))` is `g`. Together with
`TauCeti.UnitarilyInvariantSeminorm.ofIsSymmetricGauge_gauge`, this makes `N ↦ N.gauge` a bijection
between unitarily invariant seminorms on `E →ₗ[𝕜] F` and symmetric gauges on `p`-tuples. -/
@[simp]
theorem gauge_ofIsSymmetricGauge (g : Seminorm ℝ (Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ))
    (hg : g.IsSymmetricGauge) :
    (ofIsSymmetricGauge g hg : UnitarilyInvariantSeminorm 𝕜 E F).gauge = g := by
  refine (isSymmetricGauge_gauge _).ext_of_antitone hg fun y hy hy0 ↦ ?_
  rw [gauge_eq_diagonalSum _ orthonormal_stdFamilyLeft orthonormal_stdFamilyRight,
    ofIsSymmetricGauge_apply]
  congr 1
  ext i
  exact singularValues_diagonalSum_stdFamily hy hy0 i

end TauCeti.UnitarilyInvariantSeminorm
