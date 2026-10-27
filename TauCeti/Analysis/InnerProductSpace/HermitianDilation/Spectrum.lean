/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HermitianDilation.Basic
public import TauCeti.Analysis.InnerProductSpace.SingularSubspace.Basic
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Spectral transfer for the Hermitian dilation

For a linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the Hermitian
dilation `D = [[0, A†], [A, 0]]` on `WithLp 2 (E × F)` is self-adjoint, and its spectral data
recover the singular data of `A`. A vector `(x, y)` is an eigenvector of `D` for `μ` exactly when
`A† y = μ x` and `A x = μ y`. Then `A† A x = μ² x` and `A A† y = μ² y`, and conversely every
eigenvector `x` of `A† A` for `μ²` extends to the eigenvector `(x, μ⁻¹ A x)` of `D` for `μ`.

Consequently:

* the two coordinate projections map the eigenspace of `D` for a real `μ` onto the eigenspaces of
  `A† A` and of `A A†` for `μ²`, and they are injective on it when `μ ≠ 0`, so that `D` has the
  eigenvalues `±σ` with the multiplicity of the squared singular value `σ²`;
* the coordinate projections map the point-spectral subspace of `D` selected by `Ω` onto the right
  and left singular subspaces of `A` selected by the squared values `{μ² | μ ∈ Ω}`;
* for a set `Λ` of squared singular values, the point-spectral subspace of `D` selected by the
  symmetric set `{μ | μ² ∈ Λ}`, which is the sum of its positive and negative spectral blocks, is
  the product of the right and left singular subspaces of `A` selected by `Λ`;
* if `A vᵢ = σᵢ uᵢ` and `A† uᵢ = σᵢ vᵢ` are the singular relations, then `(vᵢ, uᵢ)` and
  `(vᵢ, -uᵢ)` are eigenvectors of `D` for `σᵢ` and `-σᵢ`.

These identities transfer spectral-subspace perturbation bounds for the self-adjoint operators
`D(A)` and `D(Â)` to the left and right singular subspaces of rectangular maps.

## Main statements

* `LinearMap.mem_eigenspace_hermitianDilation_iff`: the block form of the eigenvector equation.
* `LinearMap.map_fstₗ_eigenspace_hermitianDilation`,
  `LinearMap.map_sndₗ_eigenspace_hermitianDilation`: the coordinate images of an eigenspace.
* `LinearMap.finrank_eigenspace_hermitianDilation_eq_adjoint_comp_self`,
  `LinearMap.finrank_eigenspace_hermitianDilation_eq_self_comp_adjoint`: multiplicities.
* `LinearMap.hasEigenvalue_hermitianDilation_iff`: nonzero eigenvalues of `D` are the square roots
  of nonzero eigenvalues of `A† A`.
* `LinearMap.map_fstₗ_pointSpectralSubspace_hermitianDilation`,
  `LinearMap.map_sndₗ_pointSpectralSubspace_hermitianDilation`: spectral subspaces of `D` project
  onto singular subspaces of `A`.
* `LinearMap.mem_pointSpectralSubspace_hermitianDilation_preimage_sq_iff`: the symmetric spectral
  block of `D` is the product of the corresponding singular subspaces.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  §7.3.
* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan theorem for
  statisticians*, Biometrika **102** (2015), 315--323.
-/

public section

open Module (finrank)
open Module.End

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (A : E →ₗ[𝕜] F)

/-! ### Eigenvectors of the dilation -/

/-- A vector `(x, y)` is an eigenvector of the Hermitian dilation for `μ` exactly when
`A† y = μ x` and `A x = μ y`. -/
theorem mem_eigenspace_hermitianDilation_iff {z : WithLp 2 (E × F)} {μ : 𝕜} :
    z ∈ eigenspace A.hermitianDilation μ ↔
      A.adjoint z.snd = μ • z.fst ∧ A z.fst = μ • z.snd := by
  rw [mem_eigenspace_iff, ← (WithLp.ofLp_injective 2).eq_iff, Prod.ext_iff]
  simp [hermitianDilation_apply]

/-- An eigenvector `x` of `A† A` for `μ²` extends to the eigenvector `(x, μ⁻¹ A x)` of the
Hermitian dilation for `μ`. When `μ = 0` the second coordinate is `0`, as `A x = 0`. -/
theorem toLp_inv_smul_apply_mem_eigenspace_hermitianDilation {μ : ℝ} {x : E}
    (hx : x ∈ eigenspace (A.adjoint ∘ₗ A) ((μ ^ 2 : ℝ) : 𝕜)) :
    WithLp.toLp 2 (x, (μ : 𝕜)⁻¹ • A x) ∈ eigenspace A.hermitianDilation (μ : 𝕜) := by
  rw [mem_eigenspace_iff, comp_apply] at hx
  rw [mem_eigenspace_hermitianDilation_iff, WithLp.toLp_fst, WithLp.toLp_snd, map_smul, hx,
    smul_smul, smul_smul]
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hAx : A x = 0 := by
      rw [← mem_ker, ← ker_adjoint_comp_self, mem_ker, comp_apply, hx]
      simp
    simp [hAx]
  · have hμ' : (μ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hμ
    constructor
    · congr 1
      push_cast
      field_simp
    · rw [mul_inv_cancel₀ hμ', one_smul]

/-- An eigenvector `y` of `A A†` for `μ²` extends to the eigenvector `(μ⁻¹ A† y, y)` of the
Hermitian dilation for `μ`. When `μ = 0` the first coordinate is `0`, as `A† y = 0`. -/
theorem toLp_inv_smul_adjoint_apply_mem_eigenspace_hermitianDilation {μ : ℝ} {y : F}
    (hy : y ∈ eigenspace (A ∘ₗ A.adjoint) ((μ ^ 2 : ℝ) : 𝕜)) :
    WithLp.toLp 2 ((μ : 𝕜)⁻¹ • A.adjoint y, y) ∈ eigenspace A.hermitianDilation (μ : 𝕜) := by
  rw [mem_eigenspace_iff, comp_apply] at hy
  rw [mem_eigenspace_hermitianDilation_iff, WithLp.toLp_fst, WithLp.toLp_snd, map_smul, hy,
    smul_smul, smul_smul]
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hAy : A.adjoint y = 0 := by
      rw [← mem_ker, ← ker_self_comp_adjoint, mem_ker, comp_apply, hy]
      simp
    simp [hAy]
  · have hμ' : (μ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hμ
    constructor
    · rw [mul_inv_cancel₀ hμ', one_smul]
    · congr 1
      push_cast
      field_simp

/-- The first coordinate projection maps the eigenspace of the Hermitian dilation for a real `μ`
onto the eigenspace of `A† A` for `μ²`. -/
@[simp]
theorem map_fstₗ_eigenspace_hermitianDilation (μ : ℝ) :
    (eigenspace A.hermitianDilation (μ : 𝕜)).map (WithLp.fstₗ 2 𝕜 E F) =
      eigenspace (A.adjoint ∘ₗ A) ((μ ^ 2 : ℝ) : 𝕜) := by
  refine le_antisymm ?_ fun x hx ↦
    ⟨_, A.toLp_inv_smul_apply_mem_eigenspace_hermitianDilation hx, rfl⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_eigenspace_hermitianDilation_iff] at hz
  rw [mem_eigenspace_iff, WithLp.fstₗ_apply, comp_apply, hz.2, map_smul, hz.1, smul_smul]
  push_cast
  ring_nf

/-- The second coordinate projection maps the eigenspace of the Hermitian dilation for a real `μ`
onto the eigenspace of `A A†` for `μ²`. -/
@[simp]
theorem map_sndₗ_eigenspace_hermitianDilation (μ : ℝ) :
    (eigenspace A.hermitianDilation (μ : 𝕜)).map (WithLp.sndₗ 2 𝕜 E F) =
      eigenspace (A ∘ₗ A.adjoint) ((μ ^ 2 : ℝ) : 𝕜) := by
  refine le_antisymm ?_ fun y hy ↦
    ⟨_, A.toLp_inv_smul_adjoint_apply_mem_eigenspace_hermitianDilation hy, rfl⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_eigenspace_hermitianDilation_iff] at hz
  rw [mem_eigenspace_iff, WithLp.sndₗ_apply, comp_apply, hz.1, map_smul, hz.2, smul_smul]
  push_cast
  ring_nf

/-! ### Multiplicities and eigenvalues -/

/-- For `μ ≠ 0`, the eigenvalue `μ` of the Hermitian dilation has the multiplicity of the
eigenvalue `μ²` of `A† A`: the first coordinate projection is injective on the eigenspace. -/
theorem finrank_eigenspace_hermitianDilation_eq_adjoint_comp_self {μ : ℝ} (hμ : μ ≠ 0) :
    finrank 𝕜 (eigenspace A.hermitianDilation (μ : 𝕜)) =
      finrank 𝕜 (eigenspace (A.adjoint ∘ₗ A) ((μ ^ 2 : ℝ) : 𝕜)) := by
  set p := eigenspace A.hermitianDilation (μ : 𝕜)
  have hinj : Function.Injective (WithLp.fstₗ 2 𝕜 E F ∘ₗ p.subtype) := by
    refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
    have hz' := (A.mem_eigenspace_hermitianDilation_iff.mp z.2).2
    rw [comp_apply, Submodule.subtype_apply, WithLp.fstₗ_apply] at hz
    rw [hz, map_zero, eq_comm, smul_eq_zero] at hz'
    refine Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext hz ?_))
    simpa [hμ] using hz'
  rw [← A.map_fstₗ_eigenspace_hermitianDilation μ, ← finrank_range_of_inj hinj, range_comp,
    Submodule.range_subtype]

/-- For `μ ≠ 0`, the eigenvalue `μ` of the Hermitian dilation has the multiplicity of the
eigenvalue `μ²` of `A A†`: the second coordinate projection is injective on the eigenspace. -/
theorem finrank_eigenspace_hermitianDilation_eq_self_comp_adjoint {μ : ℝ} (hμ : μ ≠ 0) :
    finrank 𝕜 (eigenspace A.hermitianDilation (μ : 𝕜)) =
      finrank 𝕜 (eigenspace (A ∘ₗ A.adjoint) ((μ ^ 2 : ℝ) : 𝕜)) := by
  set p := eigenspace A.hermitianDilation (μ : 𝕜)
  have hinj : Function.Injective (WithLp.sndₗ 2 𝕜 E F ∘ₗ p.subtype) := by
    refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
    have hz' := (A.mem_eigenspace_hermitianDilation_iff.mp z.2).1
    rw [comp_apply, Submodule.subtype_apply, WithLp.sndₗ_apply] at hz
    rw [hz, map_zero, eq_comm, smul_eq_zero] at hz'
    refine Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext ?_ hz))
    simpa [hμ] using hz'
  rw [← A.map_sndₗ_eigenspace_hermitianDilation μ, ← finrank_range_of_inj hinj, range_comp,
    Submodule.range_subtype]

/-- A nonzero real `μ` is an eigenvalue of the Hermitian dilation exactly when `μ²` is an
eigenvalue of `A† A`, that is, when `|μ|` is a nonzero singular value of `A`. -/
theorem hasEigenvalue_hermitianDilation_iff {μ : ℝ} (hμ : μ ≠ 0) :
    HasEigenvalue A.hermitianDilation (μ : 𝕜) ↔
      HasEigenvalue (A.adjoint ∘ₗ A) ((μ ^ 2 : ℝ) : 𝕜) := by
  simp only [hasEigenvalue_iff, ne_eq, ← Submodule.finrank_eq_zero,
    A.finrank_eigenspace_hermitianDilation_eq_adjoint_comp_self hμ]

/-- The singular pair `(vᵢ, uᵢ)` is an eigenvector of the Hermitian dilation for `σᵢ`. -/
theorem hermitianDilation_toLp_rightSingularBasis_leftSingularVector (i : Fin (finrank 𝕜 E)) :
    A.hermitianDilation (WithLp.toLp 2 (A.rightSingularBasis i, A.leftSingularVector i)) =
      ((A.singularValues i : ℝ) : 𝕜) •
        WithLp.toLp 2 (A.rightSingularBasis i, A.leftSingularVector i) := by
  rw [← mem_eigenspace_iff, mem_eigenspace_hermitianDilation_iff]
  exact ⟨A.adjoint_leftSingularVector i, A.apply_rightSingularBasis i⟩

/-- The reflected singular pair `(vᵢ, -uᵢ)` is an eigenvector of the Hermitian dilation for
`-σᵢ`. -/
theorem hermitianDilation_toLp_rightSingularBasis_neg_leftSingularVector
    (i : Fin (finrank 𝕜 E)) :
    A.hermitianDilation (WithLp.toLp 2 (A.rightSingularBasis i, -A.leftSingularVector i)) =
      ((-A.singularValues i : ℝ) : 𝕜) •
        WithLp.toLp 2 (A.rightSingularBasis i, -A.leftSingularVector i) := by
  rw [← mem_eigenspace_iff, mem_eigenspace_hermitianDilation_iff, WithLp.toLp_fst,
    WithLp.toLp_snd, map_neg, A.adjoint_leftSingularVector, A.apply_rightSingularBasis]
  simp

/-- Every singular value `σᵢ` of `A`, including zero, is an eigenvalue of its Hermitian
dilation. -/
theorem hasEigenvalue_hermitianDilation_singularValues (i : Fin (finrank 𝕜 E)) :
    HasEigenvalue A.hermitianDilation ((A.singularValues i : ℝ) : 𝕜) := by
  refine hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2
    (A.rightSingularBasis i, A.leftSingularVector i)) ⟨?_, ?_⟩
  · exact mem_eigenspace_iff.mpr (A.hermitianDilation_toLp_rightSingularBasis_leftSingularVector i)
  · intro h
    exact A.rightSingularBasis.orthonormal.ne_zero i (by simpa using congrArg WithLp.fst h)

/-- The negative `-σᵢ` of every singular value of `A` is an eigenvalue of its Hermitian
dilation. -/
theorem hasEigenvalue_hermitianDilation_neg_singularValues (i : Fin (finrank 𝕜 E)) :
    HasEigenvalue A.hermitianDilation ((-A.singularValues i : ℝ) : 𝕜) := by
  refine hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2
    (A.rightSingularBasis i, -A.leftSingularVector i)) ⟨?_, ?_⟩
  · exact mem_eigenspace_iff.mpr
      (A.hermitianDilation_toLp_rightSingularBasis_neg_leftSingularVector i)
  · intro h
    exact A.rightSingularBasis.orthonormal.ne_zero i (by simpa using congrArg WithLp.fst h)

/-! ### Spectral subspaces -/

/-- The first coordinate projection maps the point-spectral subspace of the Hermitian dilation
selected by `Ω` onto the right singular subspace of `A` selected by the squares of `Ω`. -/
@[simp]
theorem map_fstₗ_pointSpectralSubspace_hermitianDilation (Ω : Set ℝ) :
    (pointSpectralSubspace A.hermitianDilation Ω).map (WithLp.fstₗ 2 𝕜 E F) =
      A.rightSingularSubspace ((· ^ 2) '' Ω) := by
  simp only [pointSpectralSubspace_eq_iSup, rightSingularSubspace_eq_pointSpectralSubspace,
    Submodule.map_iSup, map_fstₗ_eigenspace_hermitianDilation, iSup_image]

/-- The second coordinate projection maps the point-spectral subspace of the Hermitian dilation
selected by `Ω` onto the left singular subspace of `A` selected by the squares of `Ω`. -/
@[simp]
theorem map_sndₗ_pointSpectralSubspace_hermitianDilation (Ω : Set ℝ) :
    (pointSpectralSubspace A.hermitianDilation Ω).map (WithLp.sndₗ 2 𝕜 E F) =
      A.leftSingularSubspace ((· ^ 2) '' Ω) := by
  simp only [pointSpectralSubspace_eq_iSup, leftSingularSubspace_eq_pointSpectralSubspace,
    Submodule.map_iSup, map_sndₗ_eigenspace_hermitianDilation, iSup_image]

/-- A pair of eigenvectors of `A† A` and `A A†` for a common value `ν ∈ Λ` lies in the spectral
block of the dilation selected by `{μ | μ² ∈ Λ}`: with `σ = √ν`, it is the average of eigenvectors
of the dilation for `σ` and for `-σ`. -/
private theorem toLp_mem_pointSpectralSubspace_hermitianDilation_preimage_sq {Λ : Set ℝ} {ν : ℝ}
    (hν : ν ∈ Λ) {x : E} {y : F} (hx : x ∈ eigenspace (A.adjoint ∘ₗ A) (ν : 𝕜))
    (hy : y ∈ eigenspace (A ∘ₗ A.adjoint) (ν : 𝕜)) :
    WithLp.toLp 2 (x, y) ∈ pointSpectralSubspace A.hermitianDilation ((· ^ 2) ⁻¹' Λ) := by
  set S := pointSpectralSubspace A.hermitianDilation ((· ^ 2) ⁻¹' Λ)
  rcases lt_or_ge ν 0 with hν0 | hν0
  · -- The positive Gram operators have no negative eigenvalues.
    obtain rfl : x = 0 := by
      by_contra hx0
      exact hν0.not_ge (eigenvalue_nonneg_of_nonneg (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)
        A.isPositive_adjoint_comp_self.re_inner_nonneg_right)
    obtain rfl : y = 0 := by
      by_contra hy0
      exact hν0.not_ge (eigenvalue_nonneg_of_nonneg (hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩)
        A.isPositive_self_comp_adjoint.re_inner_nonneg_right)
    simpa only [Prod.mk_zero_zero, WithLp.toLp_zero] using S.zero_mem
  set σ := √ν
  have hmem (μ : ℝ) (hμ : μ ^ 2 = ν) {w : WithLp 2 (E × F)}
      (hw : w ∈ eigenspace A.hermitianDilation (μ : 𝕜)) : w ∈ S :=
    eigenspace_le_pointSpectralSubspace (by rwa [Set.mem_preimage, hμ]) hw
  have hpair (μ : ℝ) (hμ : μ ^ 2 = ν) :
      WithLp.toLp 2 (x, (μ : 𝕜)⁻¹ • A x) + WithLp.toLp 2 ((μ : 𝕜)⁻¹ • A.adjoint y, y) ∈ S :=
    S.add_mem
      (hmem μ hμ (A.toLp_inv_smul_apply_mem_eigenspace_hermitianDilation (by rwa [hμ])))
      (hmem μ hμ (A.toLp_inv_smul_adjoint_apply_mem_eigenspace_hermitianDilation (by rwa [hμ])))
  have hσ : σ ^ 2 = ν := Real.sq_sqrt hν0
  convert S.smul_mem (2⁻¹ : 𝕜) (S.add_mem (hpair σ hσ) (hpair (-σ) (by rw [neg_sq, hσ])))
    using 1
  apply WithLp.ofLp_injective 2
  ext <;> simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, RCLike.ofReal_neg, inv_neg, neg_smul] <;> module

/-- The point-spectral subspace of the Hermitian dilation selected by `{μ | μ² ∈ Λ}` consists of
the pairs `(x, y)` with `x` in the right and `y` in the left singular subspace of `A` selected by
`Λ`. The selecting set is symmetric under `μ ↦ -μ`, so this block contains the positive and the
negative spectral blocks of the dilation together. -/
theorem mem_pointSpectralSubspace_hermitianDilation_preimage_sq_iff (Λ : Set ℝ)
    {z : WithLp 2 (E × F)} :
    z ∈ pointSpectralSubspace A.hermitianDilation ((· ^ 2) ⁻¹' Λ) ↔
      z.fst ∈ A.rightSingularSubspace Λ ∧ z.snd ∈ A.leftSingularSubspace Λ := by
  set S := pointSpectralSubspace A.hermitianDilation ((· ^ 2) ⁻¹' Λ)
  constructor
  · intro hz
    refine ⟨A.rightSingularSubspace_mono (Set.image_preimage_subset (· ^ 2) Λ) ?_,
      A.leftSingularSubspace_mono (Set.image_preimage_subset (· ^ 2) Λ) ?_⟩
    · rw [← map_fstₗ_pointSpectralSubspace_hermitianDilation]
      exact ⟨z, hz, rfl⟩
    · rw [← map_sndₗ_pointSpectralSubspace_hermitianDilation]
      exact ⟨z, hz, rfl⟩
  · rintro ⟨hx, hy⟩
    have hfst : A.rightSingularSubspace Λ ≤ S.comap
        ((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ LinearMap.inl 𝕜 E F) := by
      rw [rightSingularSubspace_eq_pointSpectralSubspace, pointSpectralSubspace_eq_iSup]
      exact iSup₂_le fun ν hν x hx ↦
        A.toLp_mem_pointSpectralSubspace_hermitianDilation_preimage_sq hν hx (zero_mem _)
    have hsnd : A.leftSingularSubspace Λ ≤ S.comap
        ((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E F) := by
      rw [leftSingularSubspace_eq_pointSpectralSubspace, pointSpectralSubspace_eq_iSup]
      exact iSup₂_le fun ν hν y hy ↦
        A.toLp_mem_pointSpectralSubspace_hermitianDilation_preimage_sq hν (zero_mem _) hy
    have hz : z = WithLp.toLp 2 (z.fst, 0) + WithLp.toLp 2 (0, z.snd) := by
      apply WithLp.ofLp_injective 2
      ext <;> simp
    rw [hz]
    exact S.add_mem (hfst hx) (hsnd hy)

end LinearMap
