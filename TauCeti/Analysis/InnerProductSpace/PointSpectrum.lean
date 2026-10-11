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

Perturbation bounds for spectral subspaces assume that the spectral data being compared are
separated. Three forms of this hypothesis are named here, all stated over restricted point spectra
of two operators `A` on `E` and `B` on `F`: a *separation* `δ ≤ |μ - ν|` with no ordering, an
*ordered gap* `μ + δ ≤ ν`, and an *interval/exterior gap*, where the spectrum of `A` lies in
`[a, b]` and that of `B` outside `(a - δ, b + δ)`. The latter two imply the first.

## Main definitions

* `Module.End.restrictedPointSpectrum A U`: the real eigenvalues of `A` with an eigenvector in `U`.
* `Module.End.PointSpectrumIn A U Ω`: the restricted point spectrum of `A` on `U` lies in `Ω`.
* `Module.End.pointSpectralSubspace A Ω`: the sum of the eigenspaces of `A` at eigenvalues in `Ω`.
* `Module.End.PointSpectraSeparated A U B V δ`: the restricted point spectra of `A` on `U` and of
  `B` on `V` are at distance at least `δ`.
* `Module.End.PointOrderedGap A U B V δ`: the first lies below the second with margin `δ`.
* `Module.End.PointIntervalExteriorGap A U B V a b δ`: the first lies in `[a, b]` and the second
  outside `(a - δ, b + δ)`.

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
* `Module.End.PointOrderedGap.pointSpectraSeparated`,
  `Module.End.PointIntervalExteriorGap.pointSpectraSeparated`: ordered and interval/exterior gaps
  are separations.
* `Module.End.PointOrderedGap.of_pointSpectrumIn`,
  `Module.End.PointOrderedGap.of_re_inner_apply_self`: containment on opposite sides of a cut, or
  opposite quadratic-form bounds, give an ordered gap.
* `Module.End.exists_pos_pointSpectraSeparated_iff_disjoint`: in finite dimension, two restricted
  point spectra are separated by a positive distance exactly when they are disjoint.

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

/-! ### Spectral separation -/

namespace Module.End

section Separation

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  {A : Module.End 𝕜 E} {B : Module.End 𝕜 F} {U U' : Submodule 𝕜 E} {V V' : Submodule 𝕜 F}
  {a b δ δ' : ℝ}

/-- `A.PointSpectraSeparated U B V δ` says that the restricted point spectra of `A` on `U` and of
`B` on `V` are at distance at least `δ`: `δ ≤ |μ - ν|` for every eigenvalue `μ` of `A` carried by
`U` and every eigenvalue `ν` of `B` carried by `V`. No ordering of the two spectra is implied. -/
def PointSpectraSeparated (A : Module.End 𝕜 E) (U : Submodule 𝕜 E) (B : Module.End 𝕜 F)
    (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ μ ∈ A.restrictedPointSpectrum U, ∀ ν ∈ B.restrictedPointSpectrum V, δ ≤ |μ - ν|

/-- Restatement of `Module.End.PointSpectraSeparated` in terms of the restricted point
spectra. -/
theorem pointSpectraSeparated_iff :
    A.PointSpectraSeparated U B V δ ↔
      ∀ μ ∈ A.restrictedPointSpectrum U, ∀ ν ∈ B.restrictedPointSpectrum V, δ ≤ |μ - ν| :=
  Iff.rfl

/-- Eigenvalues carried by separated subspaces are at distance at least `δ`. -/
theorem PointSpectraSeparated.le_abs_sub (h : A.PointSpectraSeparated U B V δ) {μ ν : ℝ}
    (hμ : μ ∈ A.restrictedPointSpectrum U) (hν : ν ∈ B.restrictedPointSpectrum V) :
    δ ≤ |μ - ν| :=
  h μ hμ ν hν

/-- Separation is symmetric in the two operators. -/
theorem PointSpectraSeparated.symm (h : A.PointSpectraSeparated U B V δ) :
    B.PointSpectraSeparated V A U δ :=
  fun ν hν μ hμ ↦ abs_sub_comm μ ν ▸ h μ hμ ν hν

/-- Separation is symmetric in the two operators. -/
theorem pointSpectraSeparated_comm :
    A.PointSpectraSeparated U B V δ ↔ B.PointSpectraSeparated V A U δ :=
  ⟨.symm, .symm⟩

/-- Separation passes to smaller subspaces and smaller distances. -/
theorem PointSpectraSeparated.mono (h : A.PointSpectraSeparated U B V δ) (hU : U' ≤ U)
    (hV : V' ≤ V) (hδ : δ' ≤ δ) : A.PointSpectraSeparated U' B V' δ' :=
  fun μ hμ ν hν ↦
    hδ.trans (h μ (restrictedPointSpectrum_mono hU hμ) ν (restrictedPointSpectrum_mono hV hν))

/-- Restricted point spectra lying in sets `Ω` and `Ω'` at distance at least `δ` from each other
are separated by `δ`. -/
theorem PointSpectraSeparated.of_pointSpectrumIn {Ω Ω' : Set ℝ} (hA : A.PointSpectrumIn U Ω)
    (hB : B.PointSpectrumIn V Ω') (hΩ : ∀ μ ∈ Ω, ∀ ν ∈ Ω', δ ≤ |μ - ν|) :
    A.PointSpectraSeparated U B V δ :=
  fun μ hμ ν hν ↦ hΩ μ (hA hμ) ν (hB hν)

/-- Restricted point spectra separated by a positive distance are disjoint. -/
theorem PointSpectraSeparated.disjoint (h : A.PointSpectraSeparated U B V δ) (hδ : 0 < δ) :
    Disjoint (A.restrictedPointSpectrum U) (B.restrictedPointSpectrum V) :=
  Set.disjoint_left.mpr fun μ hμ hν ↦ (h μ hμ μ hν).not_gt (by simpa using hδ)

/-- Point-spectral subspaces selected by sets `Ω` and `Ω'` at distance at least `δ` from each other
carry point spectra separated by `δ`. -/
theorem pointSpectraSeparated_pointSpectralSubspace (A : Module.End 𝕜 E) (B : Module.End 𝕜 F)
    {Ω Ω' : Set ℝ} (hΩ : ∀ μ ∈ Ω, ∀ ν ∈ Ω', δ ≤ |μ - ν|) :
    A.PointSpectraSeparated (A.pointSpectralSubspace Ω) B (B.pointSpectralSubspace Ω') δ :=
  .of_pointSpectrumIn (A.pointSpectrumIn_pointSpectralSubspace Ω)
    (B.pointSpectrumIn_pointSpectralSubspace Ω') hΩ

/-- `A.PointOrderedGap U B V δ` says that the restricted point spectrum of `A` on `U` lies below
that of `B` on `V` with margin `δ`: `μ + δ ≤ ν` for every eigenvalue `μ` of `A` carried by `U` and
every eigenvalue `ν` of `B` carried by `V`. -/
def PointOrderedGap (A : Module.End 𝕜 E) (U : Submodule 𝕜 E) (B : Module.End 𝕜 F)
    (V : Submodule 𝕜 F) (δ : ℝ) : Prop :=
  ∀ μ ∈ A.restrictedPointSpectrum U, ∀ ν ∈ B.restrictedPointSpectrum V, μ + δ ≤ ν

/-- Restatement of `Module.End.PointOrderedGap` in terms of the restricted point spectra. -/
theorem pointOrderedGap_iff :
    A.PointOrderedGap U B V δ ↔
      ∀ μ ∈ A.restrictedPointSpectrum U, ∀ ν ∈ B.restrictedPointSpectrum V, μ + δ ≤ ν :=
  Iff.rfl

/-- An eigenvalue of `A` carried by `U` lies at least `δ` below every eigenvalue of `B`
carried by `V`. -/
theorem PointOrderedGap.add_le (h : A.PointOrderedGap U B V δ) {μ ν : ℝ}
    (hμ : μ ∈ A.restrictedPointSpectrum U) (hν : ν ∈ B.restrictedPointSpectrum V) : μ + δ ≤ ν :=
  h μ hμ ν hν

/-- An ordered gap passes to smaller subspaces and smaller margins. -/
theorem PointOrderedGap.mono (h : A.PointOrderedGap U B V δ) (hU : U' ≤ U) (hV : V' ≤ V)
    (hδ : δ' ≤ δ) : A.PointOrderedGap U' B V' δ' := fun μ hμ ν hν ↦ by
  have := h μ (restrictedPointSpectrum_mono hU hμ) ν (restrictedPointSpectrum_mono hV hν)
  linarith

/-- **An ordered gap is a separation.** If the restricted point spectrum of `A` on `U` lies below
that of `B` on `V` with margin `δ`, the two are separated by `δ`. -/
theorem PointOrderedGap.pointSpectraSeparated (h : A.PointOrderedGap U B V δ) :
    A.PointSpectraSeparated U B V δ := fun μ hμ ν hν ↦
  (le_sub_iff_add_le'.mpr (h μ hμ ν hν)).trans ((le_abs_self _).trans_eq (abs_sub_comm ν μ))

/-- **Opposite-side containment gives an ordered gap.** If the restricted point spectrum of `A`
on `U` lies in `(-∞, a]` and that of `B` on `V` lies in `[a + δ, ∞)`, then they are ordered with
margin `δ`. -/
theorem PointOrderedGap.of_pointSpectrumIn (hA : A.PointSpectrumIn U (Set.Iic a))
    (hB : B.PointSpectrumIn V (Set.Ici (a + δ))) : A.PointOrderedGap U B V δ :=
  fun μ hμ ν hν ↦ by
    have h₁ : μ ≤ a := hA hμ
    have h₂ : a + δ ≤ ν := hB hν
    linarith

/-- The point-spectral subspaces of `A` selected by `(-∞, a]` and by `[a + δ, ∞)` carry point
spectra ordered with margin `δ`. -/
theorem pointOrderedGap_pointSpectralSubspace (A : Module.End 𝕜 E) (a δ : ℝ) :
    A.PointOrderedGap (A.pointSpectralSubspace (Set.Iic a)) A
      (A.pointSpectralSubspace (Set.Ici (a + δ))) δ :=
  .of_pointSpectrumIn (A.pointSpectrumIn_pointSpectralSubspace _)
    (A.pointSpectrumIn_pointSpectralSubspace _)

/-- `A.PointIntervalExteriorGap U B V a b δ` says that the restricted point spectrum of `A` on
`U` lies in the interval `[a, b]`, while that of `B` on `V` lies outside its enlargement
`(a - δ, b + δ)`. -/
structure PointIntervalExteriorGap (A : Module.End 𝕜 E) (U : Submodule 𝕜 E)
    (B : Module.End 𝕜 F) (V : Submodule 𝕜 F) (a b δ : ℝ) : Prop where
  /-- The restricted point spectrum of `A` on `U` lies in `[a, b]`. -/
  pointSpectrumIn_Icc : A.PointSpectrumIn U (Set.Icc a b)
  /-- The restricted point spectrum of `B` on `V` avoids `(a - δ, b + δ)`. -/
  pointSpectrumIn_compl_Ioo : B.PointSpectrumIn V (Set.Ioo (a - δ) (b + δ))ᶜ

/-- An interval/exterior gap passes to smaller subspaces and smaller margins. -/
theorem PointIntervalExteriorGap.mono (h : A.PointIntervalExteriorGap U B V a b δ) (hU : U' ≤ U)
    (hV : V' ≤ V) (hδ : δ' ≤ δ) : A.PointIntervalExteriorGap U' B V' a b δ' where
  pointSpectrumIn_Icc := h.pointSpectrumIn_Icc.mono hU subset_rfl
  pointSpectrumIn_compl_Ioo := h.pointSpectrumIn_compl_Ioo.mono hV
    (Set.compl_subset_compl.mpr (Set.Ioo_subset_Ioo (by linarith) (by linarith)))

/-- **An interval/exterior gap is a separation.** If the restricted point spectrum of `A` on `U`
lies in `[a, b]` and that of `B` on `V` lies outside `(a - δ, b + δ)`, the two are separated
by `δ`. -/
theorem PointIntervalExteriorGap.pointSpectraSeparated
    (h : A.PointIntervalExteriorGap U B V a b δ) : A.PointSpectraSeparated U B V δ := by
  refine .of_pointSpectrumIn h.pointSpectrumIn_Icc h.pointSpectrumIn_compl_Ioo ?_
  rintro μ ⟨hμa, hμb⟩ ν hν
  rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hν
  rcases hν with hν | hν
  · exact le_abs.mpr (Or.inl (by linarith))
  · exact le_abs.mpr (Or.inr (by linarith))

/-- The point-spectral subspaces of `A` selected by `[a, b]` and by the complement of
`(a - δ, b + δ)` satisfy the interval/exterior gap. -/
theorem pointIntervalExteriorGap_pointSpectralSubspace (A : Module.End 𝕜 E) (a b δ : ℝ) :
    A.PointIntervalExteriorGap (A.pointSpectralSubspace (Set.Icc a b)) A
      (A.pointSpectralSubspace (Set.Ioo (a - δ) (b + δ))ᶜ) a b δ :=
  ⟨A.pointSpectrumIn_pointSpectralSubspace _, A.pointSpectrumIn_pointSpectralSubspace _⟩

/-- In finite dimension, the restricted point spectrum is finite. -/
theorem finite_restrictedPointSpectrum [FiniteDimensional 𝕜 E] (A : Module.End 𝕜 E)
    (U : Submodule 𝕜 E) : (A.restrictedPointSpectrum U).Finite :=
  (A.finite_hasEigenvalue.preimage RCLike.ofReal_injective.injOn).subset
    ((restrictedPointSpectrum_mono le_top).trans restrictedPointSpectrum_top.subset)

/-- In finite dimension, two restricted point spectra are separated by some positive distance
exactly when they are disjoint. -/
theorem exists_pos_pointSpectraSeparated_iff_disjoint [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] :
    (∃ δ > 0, A.PointSpectraSeparated U B V δ) ↔
      Disjoint (A.restrictedPointSpectrum U) (B.restrictedPointSpectrum V) := by
  refine ⟨fun ⟨δ, hδ, h⟩ ↦ h.disjoint hδ, fun hd ↦ ?_⟩
  -- The set of differences `μ - ν` is finite, hence closed, and avoids `0`.
  set D := Set.image2 (· - ·) (A.restrictedPointSpectrum U) (B.restrictedPointSpectrum V)
  have hD : D.Finite :=
    (A.finite_restrictedPointSpectrum U).image2 _ (B.finite_restrictedPointSpectrum V)
  have h0 : (0 : ℝ) ∈ Dᶜ := by
    rintro ⟨μ, hμ, ν, hν, hμν⟩
    exact Set.disjoint_left.mp hd hμ (sub_eq_zero.mp hμν ▸ hν)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD.isClosed.isOpen_compl 0 h0
  refine ⟨ε, hε, fun μ hμ ν hν ↦ not_lt.mp fun hlt ↦ hball ?_ (Set.mem_image2_of_mem hμ hν)⟩
  simpa [Real.dist_eq] using hlt

end Separation

section FormBound

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {A : Module.End 𝕜 E} {B : Module.End 𝕜 F}
  {U : Submodule 𝕜 E} {V : Submodule 𝕜 F} {a δ : ℝ}

/-- **Form bounds give an ordered gap.** If `re ⟪A x, x⟫ ≤ a ‖x‖²` on `U` and
`(a + δ) ‖y‖² ≤ re ⟪B y, y⟫` on `V`, then the restricted point spectra of `A` on `U` and of `B` on
`V` are ordered with margin `δ`. -/
theorem PointOrderedGap.of_re_inner_apply_self
    (hA : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hB : ∀ y ∈ V, (a + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪B y, y⟫_𝕜) : A.PointOrderedGap U B V δ :=
  .of_pointSpectrumIn (pointSpectrumIn_Iic_of_re_inner_apply_self_le hA)
    (pointSpectrumIn_Ici_of_le_re_inner_apply_self hB)

end FormBound

end Module.End
