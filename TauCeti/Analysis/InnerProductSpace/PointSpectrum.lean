/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.SymmetricFunctionalCalculus

/-!
# Restricted point spectra and point-spectral subspaces

Let `A` be an endomorphism of a vector space `E` over `𝕜 = ℝ` or `ℂ`. This file sets up the
basis-free vocabulary in which spectral-subspace perturbation estimates are stated.

* The *restricted point spectrum* `A.restrictedPointSpectrum U` of `A` on a subspace `U` is the
  set of real `λ` for which some nonzero `x ∈ U` satisfies `A x = λ x`. The subspace `U` need not
  be invariant under `A`.
* `A.PointSpectrumIn U Ω` says that this restricted point spectrum is contained in a set
  `Ω ⊆ ℝ`.
* The *point-spectral subspace* `A.pointSpectralSubspace Ω` is the sum of the eigenspaces of `A`
  at the eigenvalues `λ ∈ Ω`, that is, the span of the eigenvectors with eigenvalue in `Ω`.

Eigenspaces for distinct eigenvalues are independent, so an eigenvector lying in
`A.pointSpectralSubspace Ω` has its eigenvalue in `Ω`: the point-spectral subspace selected by `Ω`
carries only point spectrum in `Ω` (`Module.End.pointSpectrumIn_pointSpectralSubspace`). This holds
for every endomorphism, in any dimension.

For a symmetric operator on a finite-dimensional inner product space, the eigenspaces at real
eigenvalues are mutually orthogonal and span `E`. Hence the point-spectral subspaces selected by
`Ω` and by its complement are orthogonal complements of each other, the point-spectral subspace is
the span of the vectors of an ordered eigenbasis whose eigenvalues lie in `Ω`, and its orthogonal
projection is the functional calculus `𝟙_Ω(A)` of the indicator function of `Ω`.

On a finite-dimensional subspace invariant under a symmetric operator, point-spectral containment
is equivalent to a quadratic-form bound: the restricted point spectrum lies in `(-∞, a]` exactly
when `re ⟪A x, x⟫ ≤ a ‖x‖²` on the subspace, and in `[a, ∞)` exactly when
`a ‖x‖² ≤ re ⟪A x, x⟫` there. The implication from the form bound to the spectral containment
needs neither symmetry, invariance, nor finite dimensionality.

## Main definitions

* `Module.End.restrictedPointSpectrum A U`: the real eigenvalues of `A` with an eigenvector in `U`.
* `Module.End.PointSpectrumIn A U Ω`: the restricted point spectrum of `A` on `U` lies in `Ω`.
* `Module.End.pointSpectralSubspace A Ω`: the sum of the eigenspaces of `A` at eigenvalues in `Ω`.

## Main statements

* `Module.End.mem_restrictedPointSpectrum_iff`: `λ` lies in the restricted point spectrum on `U`
  exactly when `A x = λ x` for some nonzero `x ∈ U`.
* `Module.End.pointSpectrumIn_pointSpectralSubspace`: the point-spectral subspace selected by `Ω`
  has restricted point spectrum in `Ω`.
* `LinearMap.IsSymmetric.orthogonal_pointSpectralSubspace`: for symmetric `A` in finite dimension,
  `(A.pointSpectralSubspace Ω)ᗮ = A.pointSpectralSubspace Ωᶜ`.
* `LinearMap.IsSymmetric.pointSpectralSubspace_eq_eigenvectorSpan`: the point-spectral subspace is
  spanned by the vectors of the ordered eigenbasis whose eigenvalues lie in `Ω`.
* `LinearMap.IsSymmetric.coe_starProjection_pointSpectralSubspace`: its orthogonal projection is
  the functional calculus of the indicator function of `Ω`.
* `LinearMap.IsSymmetric.pointSpectrumIn_Iic_iff`, `LinearMap.IsSymmetric.pointSpectrumIn_Ici_iff`:
  on a finite-dimensional invariant subspace, point-spectral containment in a half-line is a
  quadratic-form bound.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.3.
-/

public section

open Module.End
open scoped InnerProductSpace

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-! ### The restricted point spectrum -/

/-- The *restricted point spectrum* of `A` on a subspace `U`: the real numbers `λ` for which `A`
has an eigenvector in `U` with eigenvalue `λ`. The subspace `U` need not be invariant. -/
def restrictedPointSpectrum (A : Module.End 𝕜 E) (U : Submodule 𝕜 E) : Set ℝ :=
  {μ | ∃ x ∈ U, A.HasEigenvector (μ : 𝕜) x}

variable {A : Module.End 𝕜 E} {U V : Submodule 𝕜 E} {μ : ℝ}

/-- A real number lies in the restricted point spectrum of `A` on `U` exactly when `A x = μ x`
for some nonzero `x ∈ U`. -/
theorem mem_restrictedPointSpectrum_iff :
    μ ∈ A.restrictedPointSpectrum U ↔ ∃ x ∈ U, x ≠ 0 ∧ A x = (μ : 𝕜) • x := by
  simp [restrictedPointSpectrum, hasEigenvector_iff, and_comm]

/-- A nonzero vector `x ∈ U` with `A x = μ x` places `μ` in the restricted point spectrum of `A`
on `U`. -/
theorem mem_restrictedPointSpectrum {x : E} (hxU : x ∈ U) (hx0 : x ≠ 0)
    (hx : A x = (μ : 𝕜) • x) : μ ∈ A.restrictedPointSpectrum U :=
  mem_restrictedPointSpectrum_iff.mpr ⟨x, hxU, hx0, hx⟩

/-- A real number lies in the restricted point spectrum of `A` on `U` exactly when `U` meets the
corresponding eigenspace of `A` nontrivially. -/
theorem mem_restrictedPointSpectrum_iff_inf_eigenspace_ne_bot :
    μ ∈ A.restrictedPointSpectrum U ↔ U ⊓ A.eigenspace (μ : 𝕜) ≠ ⊥ := by
  simp [restrictedPointSpectrum, Submodule.ne_bot_iff, hasEigenvector_iff, and_assoc]

/-- The restricted point spectrum is monotone in the subspace. -/
theorem restrictedPointSpectrum_mono (hUV : U ≤ V) :
    A.restrictedPointSpectrum U ⊆ A.restrictedPointSpectrum V :=
  fun _ ⟨x, hx, hxe⟩ ↦ ⟨x, hUV hx, hxe⟩

/-- The restricted point spectrum on the zero subspace is empty. -/
@[simp]
theorem restrictedPointSpectrum_bot : A.restrictedPointSpectrum ⊥ = ∅ := by
  ext μ
  simp only [mem_restrictedPointSpectrum_iff, Submodule.mem_bot, Set.mem_empty_iff_false,
    iff_false, not_exists, not_and]
  exact fun _ hx hx0 ↦ (hx0 hx).elim

/-- The restricted point spectrum on the whole space is the set of real eigenvalues. -/
@[simp]
theorem restrictedPointSpectrum_top :
    A.restrictedPointSpectrum ⊤ = {μ : ℝ | A.HasEigenvalue (μ : 𝕜)} := by
  ext μ
  simp only [mem_restrictedPointSpectrum_iff_inf_eigenspace_ne_bot, top_inf_eq, Set.mem_ofPred_eq]
  exact Iff.rfl

/-! ### Point-spectral containment -/

/-- `A.PointSpectrumIn U Ω` says that every real eigenvalue of `A` carried by an eigenvector in
`U` lies in `Ω`. -/
def PointSpectrumIn (A : Module.End 𝕜 E) (U : Submodule 𝕜 E) (Ω : Set ℝ) : Prop :=
  A.restrictedPointSpectrum U ⊆ Ω

/-- Point-spectral containment in `Ω` says that `A x = μ x` with `x ∈ U` nonzero forces
`μ ∈ Ω`. -/
theorem pointSpectrumIn_iff {Ω : Set ℝ} :
    A.PointSpectrumIn U Ω ↔ ∀ x ∈ U, x ≠ 0 → ∀ μ : ℝ, A x = (μ : 𝕜) • x → μ ∈ Ω :=
  ⟨fun h _ hxU hx0 _ hx ↦ h (mem_restrictedPointSpectrum hxU hx0 hx), fun h _ hμ ↦
    let ⟨x, hxU, hx0, hx⟩ := mem_restrictedPointSpectrum_iff.mp hμ
    h x hxU hx0 _ hx⟩

/-- Point-spectral containment passes to smaller subspaces and larger sets of values. -/
theorem PointSpectrumIn.mono {Ω Ω' : Set ℝ} (h : A.PointSpectrumIn V Ω) (hUV : U ≤ V)
    (hΩ : Ω ⊆ Ω') : A.PointSpectrumIn U Ω' :=
  (restrictedPointSpectrum_mono hUV).trans (h.trans hΩ)

/-! ### Point-spectral subspaces -/

/-- The *point-spectral subspace* of `A` selected by `Ω ⊆ ℝ`: the sum of the eigenspaces of `A`
at the eigenvalues in `Ω`, that is, the span of the eigenvectors whose eigenvalue lies in `Ω`
(`Module.End.pointSpectralSubspace_eq_span`). -/
def pointSpectralSubspace (A : Module.End 𝕜 E) (Ω : Set ℝ) : Submodule 𝕜 E :=
  ⨆ μ ∈ Ω, A.eigenspace (μ : 𝕜)

variable {Ω Ω' : Set ℝ}

/-- The point-spectral subspace selected by `Ω` is the supremum of the eigenspaces of `A` at the
eigenvalues in `Ω`. -/
theorem pointSpectralSubspace_eq_iSup :
    A.pointSpectralSubspace Ω = ⨆ μ ∈ Ω, A.eigenspace (μ : 𝕜) :=
  (rfl)

/-- The point-spectral subspace selected by `Ω` lies in `V` exactly when every eigenspace of `A`
at an eigenvalue in `Ω` does. -/
theorem pointSpectralSubspace_le_iff :
    A.pointSpectralSubspace Ω ≤ V ↔ ∀ μ ∈ Ω, A.eigenspace (μ : 𝕜) ≤ V :=
  iSup₂_le_iff

/-- The eigenspace of `A` at an eigenvalue in `Ω` lies in the point-spectral subspace. -/
theorem eigenspace_le_pointSpectralSubspace (hμ : μ ∈ Ω) :
    A.eigenspace (μ : 𝕜) ≤ A.pointSpectralSubspace Ω :=
  le_biSup (fun ν : ℝ ↦ A.eigenspace (ν : 𝕜)) hμ

/-- The point-spectral subspace selected by `Ω` is the span of the eigenvectors of `A` whose
eigenvalues lie in `Ω`. -/
theorem pointSpectralSubspace_eq_span :
    A.pointSpectralSubspace Ω =
      Submodule.span 𝕜 {x | ∃ μ ∈ Ω, A.HasEigenvector (μ : 𝕜) x} := by
  refine le_antisymm (iSup₂_le fun μ hμ x hx ↦ ?_) (Submodule.span_le.mpr ?_)
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨μ, hμ, hx, hx0⟩
  · rintro x ⟨μ, hμ, hx, -⟩
    exact eigenspace_le_pointSpectralSubspace hμ hx

/-- The point-spectral subspace is monotone in the selected set of eigenvalues. -/
theorem pointSpectralSubspace_mono (h : Ω ⊆ Ω') :
    A.pointSpectralSubspace Ω ≤ A.pointSpectralSubspace Ω' :=
  biSup_mono h

/-- The point-spectral subspace selected by the empty set is zero. -/
@[simp]
theorem pointSpectralSubspace_empty : A.pointSpectralSubspace ∅ = ⊥ := by
  simp [pointSpectralSubspace]

/-- The point-spectral subspace of a union is the sum of the two point-spectral subspaces. -/
@[simp]
theorem pointSpectralSubspace_union :
    A.pointSpectralSubspace (Ω ∪ Ω') = A.pointSpectralSubspace Ω ⊔ A.pointSpectralSubspace Ω' :=
  iSup_union

/-- An endomorphism maps each of its point-spectral subspaces into itself. -/
theorem map_pointSpectralSubspace_le :
    (A.pointSpectralSubspace Ω).map A ≤ A.pointSpectralSubspace Ω := by
  refine Submodule.map_le_iff_le_comap.mpr (iSup₂_le fun μ hμ x hx ↦ ?_)
  rw [Submodule.mem_comap, (mem_eigenspace_iff.mp hx)]
  exact eigenspace_le_pointSpectralSubspace hμ (Submodule.smul_mem _ _ hx)

/-- Point-spectral subspaces selected by disjoint sets are disjoint, because eigenspaces for
distinct eigenvalues are independent. -/
theorem disjoint_pointSpectralSubspace (h : Disjoint Ω Ω') :
    Disjoint (A.pointSpectralSubspace Ω) (A.pointSpectralSubspace Ω') :=
  (A.eigenspaces_iSupIndep.comp RCLike.ofReal_injective).disjoint_biSup_biSup h

/-- **Spectral containment of point-spectral subspaces.** An eigenvector of `A` lying in the
point-spectral subspace selected by `Ω` has its eigenvalue in `Ω`. -/
theorem pointSpectrumIn_pointSpectralSubspace (A : Module.End 𝕜 E) (Ω : Set ℝ) :
    A.PointSpectrumIn (A.pointSpectralSubspace Ω) Ω := by
  intro μ hμ
  obtain ⟨x, hxΩ, hx0, hx⟩ := mem_restrictedPointSpectrum_iff.mp hμ
  by_contra hμΩ
  exact hx0 ((disjoint_pointSpectralSubspace (Set.disjoint_singleton_left.mpr hμΩ)).le_bot
    ⟨eigenspace_le_pointSpectralSubspace (Set.mem_singleton μ) (mem_eigenspace_iff.mpr hx), hxΩ⟩)

end Module.End

/-! ### Symmetric operators -/

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : Module.End 𝕜 E}

/-- Point-spectral subspaces of a symmetric operator selected by disjoint sets are orthogonal. -/
theorem isOrtho_pointSpectralSubspace (hA : A.IsSymmetric) {Ω Ω' : Set ℝ} (h : Disjoint Ω Ω') :
    A.pointSpectralSubspace Ω ⟂ A.pointSpectralSubspace Ω' := by
  refine Submodule.isOrtho_iSup_left.mpr fun μ ↦ Submodule.isOrtho_iSup_left.mpr fun hμ ↦
    Submodule.isOrtho_iSup_right.mpr fun ν ↦ Submodule.isOrtho_iSup_right.mpr fun hν ↦ ?_
  refine hA.orthogonalFamily_eigenspaces.isOrtho ?_
  rw [Ne, RCLike.ofReal_inj]
  rintro rfl
  exact Set.disjoint_left.mp h hμ hν

variable [FiniteDimensional 𝕜 E]

/-- For a symmetric operator on a finite-dimensional space, the point-spectral subspaces selected by
`Ω` and by its complement together span the space. -/
theorem pointSpectralSubspace_sup_compl_eq_top (hA : A.IsSymmetric) (Ω : Set ℝ) :
    A.pointSpectralSubspace Ω ⊔ A.pointSpectralSubspace Ωᶜ = ⊤ := by
  rw [← Module.End.pointSpectralSubspace_union, Set.union_compl_self, eq_top_iff,
    ← Submodule.orthogonal_eq_bot_iff.mp hA.orthogonalComplement_iSup_eigenspaces_eq_bot]
  refine iSup_le fun μ ↦ ?_
  by_cases hμ : A.HasEigenvalue μ
  · rw [← RCLike.conj_eq_iff_re.mp (hA.conj_eigenvalue_eq_self hμ)]
    exact Module.End.eigenspace_le_pointSpectralSubspace (Set.mem_univ _)
  · rw [Module.End.hasEigenvalue_iff, not_not] at hμ
    simp [hμ]

/-- For a symmetric operator on a finite-dimensional space, the orthogonal complement of the
point-spectral subspace selected by `Ω` is the point-spectral subspace selected by `Ωᶜ`. -/
theorem orthogonal_pointSpectralSubspace (hA : A.IsSymmetric) (Ω : Set ℝ) :
    (A.pointSpectralSubspace Ω)ᗮ = A.pointSpectralSubspace Ωᶜ := by
  set P := A.pointSpectralSubspace Ω
  have hle : A.pointSpectralSubspace Ωᶜ ≤ Pᗮ :=
    (hA.isOrtho_pointSpectralSubspace disjoint_compl_right).ge
  calc Pᗮ = (A.pointSpectralSubspace Ωᶜ ⊔ P) ⊓ Pᗮ := by
        rw [sup_comm, hA.pointSpectralSubspace_sup_compl_eq_top, top_inf_eq]
    _ = A.pointSpectralSubspace Ωᶜ := by
        rw [sup_inf_assoc_of_le _ hle, Submodule.inf_orthogonal_eq_bot, sup_bot_eq]

/-- For a symmetric operator on a finite-dimensional space, the point-spectral subspace selected by
`Ω` is spanned by the vectors of an ordered eigenbasis whose eigenvalues lie in `Ω`. -/
theorem pointSpectralSubspace_eq_eigenvectorSpan (hA : A.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (Ω : Set ℝ) :
    A.pointSpectralSubspace Ω = hA.eigenvectorSpan hn {i | hA.eigenvalues hn i ∈ Ω} := by
  have hle (Ω : Set ℝ) :
      hA.eigenvectorSpan hn {i | hA.eigenvalues hn i ∈ Ω} ≤ A.pointSpectralSubspace Ω := by
    intro x hx
    rw [mem_eigenvectorSpan_iff] at hx
    rw [← (hA.eigenvectorBasis hn).toBasis.sum_repr x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : i ∈ ((hA.eigenvectorBasis hn).toBasis.repr x).support
    · rw [OrthonormalBasis.coe_toBasis]
      exact Submodule.smul_mem _ _ (Module.End.eigenspace_le_pointSpectralSubspace (hx hi)
        (mem_eigenspace_iff.mpr (hA.apply_eigenvectorBasis hn i)))
    · rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
      exact Submodule.zero_mem _
  set S := hA.eigenvectorSpan hn {i | hA.eigenvalues hn i ∈ Ω}
  set Sc := hA.eigenvectorSpan hn {i | hA.eigenvalues hn i ∈ Ω}ᶜ
  have htop : S ⊔ Sc = ⊤ := by
    rw [← hA.eigenvectorSpan_union, Set.union_compl_self, hA.eigenvectorSpan_univ]
  have hbot : Sc ⊓ A.pointSpectralSubspace Ω = ⊥ :=
    ((Module.End.disjoint_pointSpectralSubspace disjoint_compl_left).mono_left (hle Ωᶜ)).eq_bot
  calc A.pointSpectralSubspace Ω = (S ⊔ Sc) ⊓ A.pointSpectralSubspace Ω := by
        rw [htop, top_inf_eq]
    _ = S := by rw [sup_inf_assoc_of_le _ (hle Ω), hbot, sup_bot_eq]

/-- For a symmetric operator on a finite-dimensional space, the dimension of the point-spectral
subspace selected by `Ω` is the number of eigenvalues in `Ω`, counted with multiplicity. -/
theorem finrank_pointSpectralSubspace (hA : A.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (Ω : Set ℝ) :
    Module.finrank 𝕜 (A.pointSpectralSubspace Ω) = {i | hA.eigenvalues hn i ∈ Ω}.ncard := by
  rw [hA.pointSpectralSubspace_eq_eigenvectorSpan hn, finrank_eigenvectorSpan]

/-- **The point-spectral projector.** For a symmetric operator `A` on a finite-dimensional space,
the orthogonal projection onto the point-spectral subspace selected by `Ω` is the functional
calculus `𝟙_Ω(A)` of the indicator function of `Ω`. -/
theorem coe_starProjection_pointSpectralSubspace (hA : A.IsSymmetric) (Ω : Set ℝ) :
    ((A.pointSpectralSubspace Ω).starProjection : E →ₗ[𝕜] E) = hA.cfc (Ω.indicator 1) := by
  refine (hA.eq_cfc_iff _).mpr fun μ x hx ↦ ?_
  have hxμ : x ∈ A.eigenspace (μ : 𝕜) := mem_eigenspace_iff.mpr hx
  by_cases hμ : μ ∈ Ω
  · rw [Set.indicator_of_mem hμ, Pi.one_apply, RCLike.ofReal_one, one_smul,
      ContinuousLinearMap.coe_coe, Submodule.starProjection_eq_self_iff]
    exact Module.End.eigenspace_le_pointSpectralSubspace hμ hxμ
  · rw [Set.indicator_of_notMem hμ, RCLike.ofReal_zero, zero_smul, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_apply_eq_zero_iff, hA.orthogonal_pointSpectralSubspace]
    exact Module.End.eigenspace_le_pointSpectralSubspace hμ hxμ

end LinearMap.IsSymmetric

/-! ### Quadratic-form bounds -/

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : Module.End 𝕜 E} {U : Submodule 𝕜 E} {a : ℝ}

/-- An upper quadratic-form bound `re ⟪A x, x⟫ ≤ a ‖x‖²` on `U` confines the restricted point
spectrum of `A` on `U` to `(-∞, a]`. -/
theorem pointSpectrumIn_Iic_of_re_inner_apply_self_le
    (h : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) : A.PointSpectrumIn U (Set.Iic a) := by
  refine pointSpectrumIn_iff.mpr fun x hxU hx0 μ hx ↦ ?_
  have := h x hxU
  rw [inner_re_symm, inner_product_apply_eigenvector hx] at this
  norm_cast at this
  exact le_of_mul_le_mul_right this (by positivity)

/-- A lower quadratic-form bound `a ‖x‖² ≤ re ⟪A x, x⟫` on `U` confines the restricted point
spectrum of `A` on `U` to `[a, ∞)`. -/
theorem pointSpectrumIn_Ici_of_le_re_inner_apply_self
    (h : ∀ x ∈ U, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) : A.PointSpectrumIn U (Set.Ici a) := by
  refine pointSpectrumIn_iff.mpr fun x hxU hx0 μ hx ↦ ?_
  have := h x hxU
  rw [inner_re_symm, inner_product_apply_eigenvector hx] at this
  norm_cast at this
  exact le_of_mul_le_mul_right this (by positivity)

end Module.End

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : Module.End 𝕜 E} {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U] {a : ℝ}

/-- The eigenvalues of the restriction of a symmetric operator to a finite-dimensional invariant
subspace `U` lie in the restricted point spectrum on `U`. -/
private theorem eigenvalues_restrict_mem (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U)
    (i : Fin (Module.finrank 𝕜 U)) :
    (hA.restrict_invariant hU).eigenvalues rfl i ∈ A.restrictedPointSpectrum U := by
  set hB := hA.restrict_invariant hU
  refine Module.End.mem_restrictedPointSpectrum (hB.eigenvectorBasis rfl i).2 ?_ ?_
  · exact_mod_cast (hB.eigenvectorBasis rfl).orthonormal.ne_zero i
  · exact congrArg Subtype.val (hB.apply_eigenvectorBasis rfl i)

/-- **Upper form bound from point spectrum.** If `U` is a finite-dimensional subspace invariant
under a symmetric operator `A`, and the restricted point spectrum of `A` on `U` lies in `(-∞, a]`,
then `re ⟪A x, x⟫ ≤ a ‖x‖²` for every `x ∈ U`. -/
theorem re_inner_apply_self_le_of_pointSpectrumIn (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U)
    (h : A.PointSpectrumIn U (Set.Iic a)) {x : E} (hx : x ∈ U) :
    RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2 := by
  set hB := hA.restrict_invariant hU
  have key := hB.re_inner_le_of_eigenbasis (hB.eigenvectorBasis rfl)
    (hB.apply_eigenvectorBasis rfl) (s := Set.univ)
    (fun i _ ↦ h (hA.eigenvalues_restrict_mem hU i)) (x := ⟨x, hx⟩)
    ((OrthonormalBasis.mem_spanIndices_iff _).mpr fun i hi ↦ (hi (Set.mem_univ i)).elim)
  simpa [Submodule.coe_inner] using key

/-- **Lower form bound from point spectrum.** If `U` is a finite-dimensional subspace invariant
under a symmetric operator `A`, and the restricted point spectrum of `A` on `U` lies in `[a, ∞)`,
then `a ‖x‖² ≤ re ⟪A x, x⟫` for every `x ∈ U`. -/
theorem le_re_inner_apply_self_of_pointSpectrumIn (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U)
    (h : A.PointSpectrumIn U (Set.Ici a)) {x : E} (hx : x ∈ U) :
    a * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  set hB := hA.restrict_invariant hU
  have key := hB.le_re_inner_of_eigenbasis (hB.eigenvectorBasis rfl)
    (hB.apply_eigenvectorBasis rfl) (s := Set.univ)
    (fun i _ ↦ h (hA.eigenvalues_restrict_mem hU i)) (x := ⟨x, hx⟩)
    ((OrthonormalBasis.mem_spanIndices_iff _).mpr fun i hi ↦ (hi (Set.mem_univ i)).elim)
  simpa [Submodule.coe_inner] using key

/-- On a finite-dimensional subspace `U` invariant under a symmetric operator `A`, the restricted
point spectrum lies in `(-∞, a]` exactly when `re ⟪A x, x⟫ ≤ a ‖x‖²` on `U`. -/
theorem pointSpectrumIn_Iic_iff (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) :
    A.PointSpectrumIn U (Set.Iic a) ↔ ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2 :=
  ⟨fun h _ hx ↦ hA.re_inner_apply_self_le_of_pointSpectrumIn hU h hx,
    Module.End.pointSpectrumIn_Iic_of_re_inner_apply_self_le⟩

/-- On a finite-dimensional subspace `U` invariant under a symmetric operator `A`, the restricted
point spectrum lies in `[a, ∞)` exactly when `a ‖x‖² ≤ re ⟪A x, x⟫` on `U`. -/
theorem pointSpectrumIn_Ici_iff (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) :
    A.PointSpectrumIn U (Set.Ici a) ↔ ∀ x ∈ U, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 :=
  ⟨fun h _ hx ↦ hA.le_re_inner_apply_self_of_pointSpectrumIn hU h hx,
    Module.End.pointSpectrumIn_Ici_of_le_re_inner_apply_self⟩

end LinearMap.IsSymmetric
