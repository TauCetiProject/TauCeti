/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.DiagonalSum
public import TauCeti.Analysis.InnerProductSpace.KyFan

/-!
# The gauge representation of unitarily invariant seminorms

With `p = min (dim E) (dim F)`, the gauge `g = N.gauge` of a unitarily invariant seminorm `N` on
`E →ₗ[𝕜] F` sends `x : Fin p → ℝ` to `N (∑ᵢ xᵢ wᵢ ⊗ vᵢ)` for any orthonormal families `(vᵢ)` in
`E` and `(wᵢ)` in `F`; the choice of the families does not matter because diagonal sums with the
same coefficients lie in one two-sided unitary orbit. Permuting the coordinates of `x` or changing
their signs permutes the vectors or changes their signs, so `g` is a symmetric gauge: a seminorm on
`p`-tuples invariant under permuting coordinates and changing their signs. The singular value
decomposition of `A` then reads `N A = g (σ₀(A), …, σₚ₋₁(A))`, the **gauge representation** of von
Neumann and Mirsky.

Conversely, every symmetric gauge `g` on `p`-tuples defines the unitarily invariant seminorm
`A ↦ g (σ₀(A), …, σₚ₋₁(A))`, whose subadditivity is the weak majorization
`σ(A + B) ≺w σ(A) + σ(B)`, and the two constructions are mutually inverse.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.gauge`: the symmetric gauge of a unitarily invariant
  seminorm, with `TauCeti.UnitarilyInvariantSeminorm.isSymmetricGauge_gauge`.
* `TauCeti.UnitarilyInvariantSeminorm.map_eq_gauge_singularValues`: the gauge representation
  `N A = N.gauge (σ₀(A), …, σₚ₋₁(A))`; `exists_isSymmetricGauge_forall_map_eq` restates it for
  square operators with tuples of length `dim E`.
* `TauCeti.UnitarilyInvariantSeminorm.ofIsSymmetricGauge`: the unitarily invariant seminorm of a
  symmetric gauge; `ofIsSymmetricGauge_gauge` and `gauge_ofIsSymmetricGauge` show that the two
  constructions are mutually inverse.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Theorem IV.2.1.
* J. von Neumann, *Some matrix-inequalities and metrization of matric-space*, Tomsk Univ. Rev.
  **1** (1937), 286–300.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. Oxford
  Ser. (2) **11** (1960), 50–59.
-/

public section

open Module InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

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
  map_zero' := by simp [LinearMap.diagonalSum_def]
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
    N.gauge x = N (∑ i, (x i : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap) := by
  rw [N.gauge_eq_diagonalSum hv hw x, LinearMap.diagonalSum_def]

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
