/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral subspaces of a symmetric bilinear form relative to an inner product

Let `g` and `q` be bilinear forms on a module `V`. A vector `v` is an eigenvector of `q` relative
to `g`, with eigenvalue `μ`, when `q v w = μ * g v w` for every `w`. When `g` is an inner product
this is the eigenvalue problem of the operator representing `q`, but the relative notion needs no
inner product structure on `V`: the eigenspace `g.relativeEigenspace q μ` is the kernel of
`q - μ • g`, and the spectral subspace `g.relativeSpectralSubspace q Ω` is the sum of the
eigenspaces at the eigenvalues in `Ω`.

This is the form in which a fibre metric splits a symmetric form on the fibres of a vector bundle,
such as the normal Hessian along a critical submanifold, into its positive and negative parts:
the bundle fibres carry the two forms but no inner product space structure of their own.

Over a field, symmetric `g` and `q` make relative eigenspaces for distinct eigenvalues orthogonal
for both forms, so spectral subspaces selected by disjoint sets are orthogonal for both
(`LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace`). For a positive definite
symmetric `g` and a symmetric `q` on a finite-dimensional real space, an isometry from Euclidean
space identifies the relative spectral subspaces with the point-spectral subspaces of a symmetric
operator. Hence the relative eigenvectors span `V`, the negative spectral subspace is negative
definite for `q` and the nonnegative one is positive semidefinite, and by Sylvester's law of
inertia the dimension of the negative spectral subspace is the negative index of inertia of `q`,
whatever positive definite `g` is used. When `q` is nondegenerate the negative and positive
spectral subspaces are complementary.

## Main declarations

* `LinearMap.BilinForm.relativeEigenspace`: the eigenspace of `q` relative to `g` at `μ`.
* `LinearMap.BilinForm.relativeSpectralSubspace`: the sum of the relative eigenspaces at the
  eigenvalues in `Ω`.
* `LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂`: naturality under linear
  equivalences.
* `LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace`: spectral subspaces for
  disjoint sets are orthogonal for `g` and for `q`;
  `LinearMap.BilinForm.disjoint_relativeSpectralSubspace`: for positive definite `g` they meet
  only in `0`.
* `LinearMap.BilinForm.relativeSpectralSubspace_univ`: the relative eigenvectors span.
* `LinearMap.BilinForm.apply_self_neg_of_mem_relativeSpectralSubspace_Iio` and
  `LinearMap.BilinForm.apply_self_pos_of_mem_relativeSpectralSubspace_Ioi`: definiteness of `q` on
  the negative and positive spectral subspaces.
* `LinearMap.BilinForm.finrank_relativeSpectralSubspace_Iio` and
  `LinearMap.BilinForm.finrank_relativeSpectralSubspace_Ioi`: their dimensions are the negative
  and positive indices of inertia of `q`.
* `LinearMap.BilinForm.isCompl_relativeSpectralSubspace_Iio_Ioi`: for nondegenerate `q`, the
  negative and positive spectral subspaces are complementary.

The Euclidean isometry is built from a `g`-orthogonal basis
(`LinearMap.BilinForm.exists_orthogonal_basis`), and the spectral input is the point-spectral
theory of symmetric operators in `TauCeti.Analysis.InnerProductSpace.PointSpectrum`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, §7.6 (simultaneous diagonalization of a positive definite and a Hermitian form).
-/

public section

noncomputable section

open Module Set
open scoped InnerProductSpace

namespace LinearMap.BilinForm

section CommRing

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {g q : LinearMap.BilinForm R V} {μ : R} {Ω Ω' : Set R}

/-- The eigenspace of `q` relative to `g` at `μ`: the vectors `v` with `q v = μ • g v`, that is,
the kernel of `q - μ • g`. -/
def relativeEigenspace (g q : LinearMap.BilinForm R V) (μ : R) : Submodule R V :=
  LinearMap.ker (q - μ • g)

/-- A vector is a relative eigenvector at `μ` exactly when `q v w = μ * g v w` for every `w`. -/
theorem mem_relativeEigenspace_iff {v : V} :
    v ∈ g.relativeEigenspace q μ ↔ ∀ w, q v w = μ * g v w := by
  simp [relativeEigenspace, LinearMap.ext_iff, sub_eq_zero]

/-- The relative spectral subspace of `q` relative to `g` selected by `Ω`: the sum of the
eigenspaces of `q` relative to `g` at the eigenvalues in `Ω`. -/
def relativeSpectralSubspace (g q : LinearMap.BilinForm R V) (Ω : Set R) : Submodule R V :=
  ⨆ μ ∈ Ω, g.relativeEigenspace q μ

/-- The relative spectral subspace selected by `Ω` is the supremum of the relative eigenspaces at
the eigenvalues in `Ω`. -/
theorem relativeSpectralSubspace_def :
    g.relativeSpectralSubspace q Ω = ⨆ μ ∈ Ω, g.relativeEigenspace q μ :=
  (rfl)

/-- The relative eigenspace at an eigenvalue in `Ω` lies in the spectral subspace selected by
`Ω`. -/
theorem relativeEigenspace_le_relativeSpectralSubspace (hμ : μ ∈ Ω) :
    g.relativeEigenspace q μ ≤ g.relativeSpectralSubspace q Ω :=
  le_biSup (fun μ ↦ g.relativeEigenspace q μ) hμ

/-- The spectral subspace selected by `Ω` lies in `U` exactly when every relative eigenspace at an
eigenvalue in `Ω` does. -/
theorem relativeSpectralSubspace_le_iff {U : Submodule R V} :
    g.relativeSpectralSubspace q Ω ≤ U ↔ ∀ μ ∈ Ω, g.relativeEigenspace q μ ≤ U :=
  iSup₂_le_iff

/-- Relative spectral subspaces are monotone in the selected set. -/
theorem relativeSpectralSubspace_mono (h : Ω ⊆ Ω') :
    g.relativeSpectralSubspace q Ω ≤ g.relativeSpectralSubspace q Ω' :=
  relativeSpectralSubspace_le_iff.mpr fun _ hμ ↦ relativeEigenspace_le_relativeSpectralSubspace
    (h hμ)

@[simp]
theorem relativeSpectralSubspace_empty : g.relativeSpectralSubspace q ∅ = ⊥ := by
  simp [relativeSpectralSubspace]

theorem relativeSpectralSubspace_union :
    g.relativeSpectralSubspace q (Ω ∪ Ω') =
      g.relativeSpectralSubspace q Ω ⊔ g.relativeSpectralSubspace q Ω' :=
  iSup_union

@[simp]
theorem relativeSpectralSubspace_singleton :
    g.relativeSpectralSubspace q {μ} = g.relativeEigenspace q μ := by
  simp [relativeSpectralSubspace]

/-- The relative eigenspace at `0` is the kernel of `q`. -/
@[simp]
theorem relativeEigenspace_zero : g.relativeEigenspace q 0 = LinearMap.ker q := by
  ext v
  simp [mem_relativeEigenspace_iff, LinearMap.ext_iff]

/-- The eigenspace of `-q` at `μ` is the eigenspace of `q` at `-μ`. -/
@[simp]
theorem relativeEigenspace_neg : g.relativeEigenspace (-q) μ = g.relativeEigenspace q (-μ) := by
  ext v
  simp only [mem_relativeEigenspace_iff, LinearMap.neg_apply, neg_mul, neg_eq_iff_eq_neg]

/-- The spectral subspace of `-q` selected by `Ω` is the spectral subspace of `q` selected by
`-Ω`. -/
@[simp]
theorem relativeSpectralSubspace_neg :
    g.relativeSpectralSubspace (-q) Ω = g.relativeSpectralSubspace q (-Ω) := by
  refine le_antisymm (relativeSpectralSubspace_le_iff.mpr fun μ hμ ↦ ?_)
    (relativeSpectralSubspace_le_iff.mpr fun μ hμ ↦ ?_)
  · rw [relativeEigenspace_neg]
    exact relativeEigenspace_le_relativeSpectralSubspace (neg_mem_neg.mpr hμ)
  · simpa only [relativeEigenspace_neg, neg_neg] using
      relativeEigenspace_le_relativeSpectralSubspace (g := g) (q := -q) (mem_neg.mp hμ)

/-- Pulling both forms back along a linear equivalence `e` pulls the relative eigenspaces back
along `e`. -/
theorem relativeEigenspace_compl₁₂ (e : W ≃ₗ[R] V) :
    relativeEigenspace (g.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V))
        (q.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V)) μ =
      (g.relativeEigenspace q μ).comap (e : W →ₗ[R] V) := by
  ext v
  simp only [mem_relativeEigenspace_iff, compl₁₂_apply, LinearEquiv.coe_coe, Submodule.mem_comap]
  exact ⟨fun h w ↦ by simpa using h (e.symm w), fun h w ↦ h (e w)⟩

/-- **Naturality of relative spectral subspaces.** Pulling both forms back along a linear
equivalence `e` and mapping the resulting spectral subspace forward along `e` recovers the
original spectral subspace. -/
theorem map_relativeSpectralSubspace_compl₁₂ (e : W ≃ₗ[R] V) :
    (relativeSpectralSubspace (g.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V))
      (q.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V)) Ω).map (e : W →ₗ[R] V) =
      g.relativeSpectralSubspace q Ω := by
  simp only [relativeSpectralSubspace, Submodule.map_iSup, relativeEigenspace_compl₁₂,
    Submodule.map_comap_eq_of_surjective e.surjective]

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {g q : LinearMap.BilinForm K V}
  {Ω Ω' : Set K} {v w : V}

/-- Relative eigenvectors at distinct eigenvalues of symmetric forms are orthogonal for both
forms. -/
private theorem apply_eq_zero_of_mem_relativeEigenspace (hg : g.IsSymm) (hq : q.IsSymm)
    {μ ν : K} (hμν : μ ≠ ν) (hv : v ∈ g.relativeEigenspace q μ)
    (hw : w ∈ g.relativeEigenspace q ν) : g v w = 0 ∧ q v w = 0 := by
  rw [mem_relativeEigenspace_iff] at hv hw
  have hgvw : g v w = 0 := by
    have h := (hv w).symm.trans ((hq.eq v w).trans ((hw v).trans (by rw [hg.eq w v])))
    rw [← sub_eq_zero, ← sub_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμν)
  exact ⟨hgvw, by rw [hv w, hgvw, mul_zero]⟩

/-- **Orthogonality of relative spectral subspaces.** For symmetric `g` and `q`, the relative
spectral subspaces selected by disjoint sets are orthogonal for `g` and for `q`. -/
theorem apply_eq_zero_of_mem_relativeSpectralSubspace (hg : g.IsSymm) (hq : q.IsSymm)
    (h : Disjoint Ω Ω') (hv : v ∈ g.relativeSpectralSubspace q Ω)
    (hw : w ∈ g.relativeSpectralSubspace q Ω') : g v w = 0 ∧ q v w = 0 := by
  -- First fix a relative eigenvector `v₀` at `μ ∈ Ω` and vary `w`, then vary `v`.
  have hleft {μ : K} (hμ : μ ∈ Ω) {v₀ : V} (hv₀ : v₀ ∈ g.relativeEigenspace q μ) :
      g.relativeSpectralSubspace q Ω' ≤ LinearMap.ker (g v₀) ⊓ LinearMap.ker (q v₀) :=
    relativeSpectralSubspace_le_iff.mpr fun ν hν w₀ hw₀ ↦
      apply_eq_zero_of_mem_relativeEigenspace hg hq (fun hμν ↦ disjoint_left.mp h hμ (by rwa [hμν]))
        hv₀ hw₀
  have hright : g.relativeSpectralSubspace q Ω ≤
      LinearMap.ker (g.flip w) ⊓ LinearMap.ker (q.flip w) :=
    relativeSpectralSubspace_le_iff.mpr fun μ hμ v₀ hv₀ ↦ hleft hμ hv₀ hw
  exact hright hv

end Field

section Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {g q : LinearMap.BilinForm ℝ V}
  {Ω Ω' : Set ℝ} {v : V}

/-- For a positive definite symmetric `g` and a symmetric `q`, the relative spectral subspaces
selected by disjoint sets meet only in `0`. -/
theorem disjoint_relativeSpectralSubspace (hg : g.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < g v v)
    (hq : q.IsSymm) (h : Disjoint Ω Ω') :
    Disjoint (g.relativeSpectralSubspace q Ω) (g.relativeSpectralSubspace q Ω') := by
  refine Submodule.disjoint_def.mpr fun v hv hv' ↦ ?_
  by_contra hv0
  exact (hpos v hv0).ne' (apply_eq_zero_of_mem_relativeSpectralSubspace hg hq h hv hv').1

variable [FiniteDimensional ℝ V]

/-- A positive definite symmetric bilinear form on a finite-dimensional real space is the pullback
of the Euclidean inner product along a linear equivalence. -/
theorem exists_linearEquiv_euclideanSpace_apply_apply (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) :
    ∃ e : EuclideanSpace ℝ (Fin (finrank ℝ V)) ≃ₗ[ℝ] V, ∀ x y, g (e x) (e y) = ⟪x, y⟫_ℝ := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := exists_orthogonal_basis (isSymm_iff.mp hg)
  have hbpos (i) : 0 < g (b i) (b i) := hpos _ (b.ne_zero i)
  -- Normalize the orthogonal basis.
  let c (i : Fin (finrank ℝ V)) : ℝˣ := Units.mk0 (√(g (b i) (b i)))⁻¹
    (inv_ne_zero (Real.sqrt_pos.mpr (hbpos i)).ne')
  let b' := b.unitsSMul c
  let e := (EuclideanSpace.basisFun (Fin (finrank ℝ V)) ℝ).toBasis.equiv b' (Equiv.refl _)
  refine ⟨e, fun x y ↦ ?_⟩
  suffices h : g.compl₁₂ (e : _ →ₗ[ℝ] V) e = innerₗ _ from congr($h x y)
  refine ext_basis (EuclideanSpace.basisFun (Fin (finrank ℝ V)) ℝ).toBasis fun i j ↦ ?_
  rw [compl₁₂_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Basis.equiv_apply,
    Equiv.refl_apply, Equiv.refl_apply, innerₗ_apply_apply, OrthonormalBasis.coe_toBasis,
    orthonormal_iff_ite.mp (EuclideanSpace.basisFun _ ℝ).orthonormal i j]
  simp only [b', Basis.unitsSMul_apply, c, Units.smul_def, Units.val_mk0, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have hs := Real.mul_self_sqrt (hbpos i).le
    have hs0 := (Real.sqrt_pos.mpr (hbpos i)).ne'
    rw [ite_eq_left_iff.mpr (fun h ↦ (h rfl).elim)]
    field_simp
    rw [Real.sq_sqrt (hbpos i).le]
  · rw [ite_eq_right_iff.mpr (fun h ↦ (hij h).elim), hb hij, mul_zero, mul_zero]

/-- Over a Euclidean space, the eigenspaces of `q` relative to the inner product are the
eigenspaces of an operator `T` representing `q`. -/
private theorem relativeEigenspace_innerₗ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q : LinearMap.BilinForm ℝ E} {T : E →ₗ[ℝ] E}
    (hT : ∀ x y, q x y = ⟪T x, y⟫_ℝ)
    (μ : ℝ) : relativeEigenspace (innerₗ E) q μ = Module.End.eigenspace T μ := by
  ext x
  rw [mem_relativeEigenspace_iff, Module.End.mem_eigenspace_iff]
  simp only [hT, innerₗ_apply_apply]
  refine ⟨fun h ↦ ?_, fun h y ↦ by rw [h, real_inner_smul_left]⟩
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
  rw [inner_sub_left, h, real_inner_smul_left, inner_sub_right, real_inner_smul_right, mul_sub,
    sub_self]

/-- **Euclidean model.** For positive definite symmetric `g` and symmetric `q`, a linear isometry
from Euclidean space carries the point-spectral subspaces of a symmetric operator representing the
pulled-back `q` onto the relative spectral subspaces of `q`. -/
private theorem exists_euclidean_model (hg : g.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < g v v)
    (hq : q.IsSymm) :
    ∃ e : EuclideanSpace ℝ (Fin (finrank ℝ V)) ≃ₗ[ℝ] V,
      ∃ T : Module.End ℝ (EuclideanSpace ℝ (Fin (finrank ℝ V))),
        T.IsSymmetric ∧ (∀ x y, g (e x) (e y) = ⟪x, y⟫_ℝ) ∧
        (∀ x y, q (e x) (e y) = ⟪T x, y⟫_ℝ) ∧
        ∀ Ω, g.relativeSpectralSubspace q Ω = (T.pointSpectralSubspace Ω).map (e : _ →ₗ[ℝ] V) := by
  obtain ⟨e, he⟩ := exists_linearEquiv_euclideanSpace_apply_apply hg hpos
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  have hnd : (innerₗ E).Nondegenerate :=
    ⟨fun x hx ↦ inner_self_eq_zero.mp (hx x), fun y hy ↦ inner_self_eq_zero.mp (hy y)⟩
  -- The Riesz operator of the pulled-back form.
  let T : Module.End ℝ E := ((LinearMap.BilinForm.toDual (innerₗ E) hnd).symm :
    Dual ℝ E →ₗ[ℝ] E) ∘ₗ q.compl₁₂ (e : E →ₗ[ℝ] V) (e : E →ₗ[ℝ] V)
  have hT (x y : E) : q.compl₁₂ (e : E →ₗ[ℝ] V) (e : E →ₗ[ℝ] V) x y = ⟪T x, y⟫_ℝ := by
    rw [← innerₗ_apply_apply, ← toDual_def hnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have hge : g.compl₁₂ (e : E →ₗ[ℝ] V) (e : E →ₗ[ℝ] V) = innerₗ E := by
    ext x y
    rw [compl₁₂_apply, LinearEquiv.coe_coe, he, innerₗ_apply_apply]
  refine ⟨e, T, fun x y ↦ ?_, he, fun x y ↦ ?_, fun Ω ↦ ?_⟩
  · rw [← hT, real_inner_comm, ← hT]
    exact hq.eq (e x) (e y)
  · rw [← hT, compl₁₂_apply, LinearEquiv.coe_coe]
  · rw [← map_relativeSpectralSubspace_compl₁₂ e, hge]
    congr 1
    rw [relativeSpectralSubspace_def, Module.End.pointSpectralSubspace_eq_iSup]
    refine iSup_congr fun μ ↦ iSup_congr fun _ ↦ ?_
    rw [relativeEigenspace_innerₗ hT, RCLike.ofReal_real_eq_id, id_eq]

variable (hg : g.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hq : q.IsSymm)
include hg hpos hq

/-- **The relative eigenvectors span.** For a positive definite symmetric `g` and a symmetric
`q` on a finite-dimensional real space, the relative spectral subspaces selected by `Ω` and by its
complement span the whole space. -/
theorem relativeSpectralSubspace_sup_compl_eq_top :
    g.relativeSpectralSubspace q Ω ⊔ g.relativeSpectralSubspace q Ωᶜ = ⊤ := by
  obtain ⟨e, T, hT, -, -, hΩ⟩ := exists_euclidean_model hg hpos hq
  rw [hΩ, hΩ, ← Submodule.map_sup, hT.pointSpectralSubspace_sup_compl_eq_top,
    Submodule.map_top, LinearEquiv.range]

/-- For a positive definite symmetric `g` and a symmetric `q` on a finite-dimensional real space,
the relative eigenvectors of `q` span the space. -/
theorem relativeSpectralSubspace_univ : g.relativeSpectralSubspace q univ = ⊤ := by
  simpa using relativeSpectralSubspace_sup_compl_eq_top hg hpos hq (Ω := univ)

/-- **Upper form bound.** If every eigenvalue in `Ω` is at most `c`, then `q v v ≤ c * g v v` on
the relative spectral subspace selected by `Ω`. -/
theorem apply_self_le_mul_apply_self (c : ℝ) (hΩ : Ω ⊆ Iic c)
    (hv : v ∈ g.relativeSpectralSubspace q Ω) : q v v ≤ c * g v v := by
  obtain ⟨e, T, hT, he, hTq, hΩ'⟩ := exists_euclidean_model hg hpos hq
  rw [hΩ', hT.pointSpectralSubspace_eq_eigenvectorSpan rfl,
    LinearMap.IsSymmetric.eigenvectorSpan_eq_spanIndices] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have key := hT.re_inner_le_of_eigenbasis (hT.eigenvectorBasis rfl)
    (hT.apply_eigenvectorBasis rfl) (fun i hi ↦ hΩ hi) hx
  simpa [hTq, he, real_inner_self_eq_norm_sq] using key

/-- **The negative spectral subspace is negative definite.** For a positive definite symmetric
`g` and a symmetric `q` on a finite-dimensional real space, `q v v < 0` for every nonzero `v` in
the relative spectral subspace selected by the negative reals. -/
theorem apply_self_neg_of_mem_relativeSpectralSubspace_Iio
    (hv : v ∈ g.relativeSpectralSubspace q (Iio 0)) (hv0 : v ≠ 0) : q v v < 0 := by
  obtain ⟨e, T, hT, he, hTq, hΩ'⟩ := exists_euclidean_model hg hpos hq
  rw [hΩ', hT.pointSpectralSubspace_eq_eigenvectorSpan rfl,
    LinearMap.IsSymmetric.eigenvectorSpan_eq_spanIndices] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  -- The negative eigenvalues are finitely many, so they are bounded above by a negative number.
  set ev := hT.eigenvalues rfl
  set c := ((Finset.univ.filter fun i ↦ ev i < 0).image ev ∪ {-1}).max' ⟨-1, by simp⟩
  have hc : c < 0 := by
    refine (Finset.max'_lt_iff _ _).mpr fun a ha ↦ ?_
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at ha
    rcases ha with ⟨i, hi, rfl⟩ | rfl
    · exact hi
    · norm_num
  have hle (i) (hi : i ∈ {i | ev i ∈ Iio (0 : ℝ)}) : ev i ≤ c :=
    Finset.le_max' _ _ (by simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]; exact Or.inl ⟨i, hi, rfl⟩)
  have key := hT.re_inner_le_of_eigenbasis (hT.eigenvectorBasis rfl)
    (hT.apply_eigenvectorBasis rfl) hle hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hv0
  rw [LinearEquiv.coe_coe, hTq]
  simp only [RCLike.re_to_real] at key
  exact key.trans_lt (mul_neg_of_neg_of_pos hc (by positivity))

/-- **The positive spectral subspace is positive definite.** For a positive definite symmetric
`g` and a symmetric `q` on a finite-dimensional real space, `0 < q v v` for every nonzero `v` in
the relative spectral subspace selected by the positive reals. -/
theorem apply_self_pos_of_mem_relativeSpectralSubspace_Ioi
    (hv : v ∈ g.relativeSpectralSubspace q (Ioi 0)) (hv0 : v ≠ 0) : 0 < q v v := by
  have hv' : v ∈ g.relativeSpectralSubspace (-q) (Iio 0) := by simpa using hv
  simpa using apply_self_neg_of_mem_relativeSpectralSubspace_Iio hg hpos hq.neg hv' hv0

/-- The negative index of inertia of `q` is the dimension of its relative spectral subspace
selected by the negative reals, for every positive definite symmetric `g`. -/
theorem finrank_relativeSpectralSubspace_Iio :
    finrank ℝ (g.relativeSpectralSubspace q (Iio 0)) = sigNeg q.toQuadraticMap := by
  set N := g.relativeSpectralSubspace q (Iio 0)
  set P := g.relativeSpectralSubspace q (Ici 0)
  have hNP : IsCompl N P := by
    refine ⟨disjoint_relativeSpectralSubspace hg hpos hq (Iio_disjoint_Ici le_rfl),
      codisjoint_iff.mpr ?_⟩
    simpa [N, P, compl_Iio] using relativeSpectralSubspace_sup_compl_eq_top hg hpos hq
      (Ω := Iio 0)
  refine le_antisymm (le_sigNeg_of_negDef _ fun ⟨v, hv⟩ hv0 ↦ ?_) ?_
  · simpa using apply_self_neg_of_mem_relativeSpectralSubspace_Iio hg hpos hq hv
      (by simpa using hv0)
  · -- `q` is positive semidefinite on the complement `P`, so Sylvester bounds `sigNeg q`.
    have hP (v) (hv : v ∈ P) : (-q.toQuadraticMap) v ≤ 0 := by
      have h := apply_self_le_mul_apply_self hg hpos hq.neg 0 (Ω := -Ici 0) (by simp)
        (by simpa [P] using hv)
      simpa using h
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos hP
    rw [sigPos_neg, ← Submodule.finrank_add_eq_of_isCompl hNP] at h
    omega

/-- The positive index of inertia of `q` is the dimension of its relative spectral subspace
selected by the positive reals, for every positive definite symmetric `g`. -/
theorem finrank_relativeSpectralSubspace_Ioi :
    finrank ℝ (g.relativeSpectralSubspace q (Ioi 0)) = sigPos q.toQuadraticMap := by
  have h := finrank_relativeSpectralSubspace_Iio hg hpos hq.neg
  rw [relativeSpectralSubspace_neg, neg_Iio, neg_zero] at h
  simpa using h

/-- For nondegenerate `q`, the negative and positive relative spectral subspaces are
complementary. -/
theorem isCompl_relativeSpectralSubspace_Iio_Ioi (hker : LinearMap.ker q = ⊥) :
    IsCompl (g.relativeSpectralSubspace q (Iio 0)) (g.relativeSpectralSubspace q (Ioi 0)) := by
  refine ⟨disjoint_relativeSpectralSubspace hg hpos hq Iio_disjoint_Ioi_same,
    codisjoint_iff.mpr ?_⟩
  · have hsplit : (univ : Set ℝ) = (Iio 0 ∪ Ioi 0) ∪ {0} := by
      ext x
      simp
    have h := relativeSpectralSubspace_univ hg hpos hq
    rwa [hsplit, relativeSpectralSubspace_union, relativeSpectralSubspace_singleton,
      relativeEigenspace_zero, hker, sup_bot_eq, relativeSpectralSubspace_union] at h

end Real

end LinearMap.BilinForm
