/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.LinearAlgebra.BilinearForm.RelativeEigenspace
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Nondegenerate

/-!
# Spectral subspaces of a symmetric bilinear form relative to an inner product

Let `g` and `q` be bilinear forms on a finite-dimensional real vector space `V`, with `g`
symmetric and positive definite and `q` symmetric. The relative eigenspaces
`g.relativeEigenspace q μ` and spectral subspaces `g.relativeSpectralSubspace q Ω` of
`TauCeti.LinearAlgebra.BilinearForm.RelativeEigenspace` need no inner product space structure on
`V`. This is the form in which a fibre metric splits a symmetric form on the fibres of a vector
bundle, such as the normal Hessian along a critical submanifold, into its positive and negative
parts: the bundle fibres carry the two forms but no inner product space structure of their own.

An isometry from Euclidean space identifies the relative spectral subspaces with the
point-spectral subspaces of a symmetric operator. Hence the relative eigenvectors span `V`, the
negative spectral subspace is negative definite for `q` and the nonnegative one is positive
semidefinite, and by Sylvester's law of inertia the dimension of the negative spectral subspace is
the negative index of inertia of `q`, whatever positive definite `g` is used. When `q` is
nondegenerate the negative and positive spectral subspaces are complementary.

## Main declarations

* `LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply`: `g` is the pullback of the
  Euclidean inner product along a linear equivalence.
* `LinearMap.BilinForm.relativeEigenspace_innerₗ`: relative to an inner product, the relative
  eigenspaces are the eigenspaces of the operator representing `q`.
* `LinearMap.BilinForm.relativeSpectralSubspace_univ`: the relative eigenvectors span.
* `LinearMap.BilinForm.exists_neg_relativeSpectralSubspace_Iio_eq_Iic`: the negative relative
  eigenvalues are bounded away from `0`.
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

section Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {g q : LinearMap.BilinForm ℝ V}
  {Ω : Set ℝ} {v : V} [FiniteDimensional ℝ V]

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
  simp only [compl₁₂_apply, LinearEquiv.coe_coe, e, Basis.equiv_apply, Equiv.refl_apply]
  simp only [b', Basis.unitsSMul_apply, c, Units.smul_def, Units.val_mk0, map_smul,
    LinearMap.smul_apply, smul_eq_mul, innerₗ_apply_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, PiLp.single_apply]
  by_cases hij : i = j
  · subst hij
    have hs0 := (Real.sqrt_pos.mpr (hbpos i)).ne'
    field_simp
    simp [Real.sq_sqrt (hbpos i).le]
  · simp [hb hij, hij]

/-- Over a Euclidean space, the eigenspaces of `q` relative to the inner product are the
eigenspaces of an operator `T` representing `q`. -/
theorem relativeEigenspace_innerₗ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q : LinearMap.BilinForm ℝ E} {T : E →ₗ[ℝ] E}
    (hT : ∀ x y, q x y = ⟪T x, y⟫_ℝ)
    (μ : ℝ) : relativeEigenspace (innerₗ E) q μ = Module.End.eigenspace T μ := by
  ext x
  rw [mem_relativeEigenspace_iff, Module.End.mem_eigenspace_iff]
  simp only [hT, innerₗ_apply_apply]
  exact ⟨fun h ↦ ext_inner_right ℝ fun y ↦ by rw [h, real_inner_smul_left],
    fun h y ↦ by rw [h, real_inner_smul_left]⟩

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
  -- The Riesz operator of the pulled-back form.
  let T : Module.End ℝ E := symmCompOfNondegenerate (q.compl₁₂ (e : E →ₗ[ℝ] V) e) (innerₗ E)
    TauCeti.nondegenerate_inner
  have hT (x y : E) : q.compl₁₂ (e : E →ₗ[ℝ] V) e x y = ⟪T x, y⟫_ℝ :=
    (symmCompOfNondegenerate_left_apply _ TauCeti.nondegenerate_inner y x).symm
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
theorem apply_self_le_mul_apply_self_of_mem_relativeSpectralSubspace (c : ℝ) (hΩ : Ω ⊆ Iic c)
    (hv : v ∈ g.relativeSpectralSubspace q Ω) : q v v ≤ c * g v v := by
  obtain ⟨e, T, hT, he, hTq, hΩ'⟩ := exists_euclidean_model hg hpos hq
  rw [hΩ', hT.pointSpectralSubspace_eq_eigenvectorSpan rfl,
    LinearMap.IsSymmetric.eigenvectorSpan_eq_spanIndices] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have key := hT.re_inner_le_of_eigenbasis (hT.eigenvectorBasis rfl)
    (hT.apply_eigenvectorBasis rfl) (fun i hi ↦ hΩ hi) hx
  simpa [hTq, he, real_inner_self_eq_norm_sq] using key

/-- **The negative relative eigenvalues are bounded away from `0`.** For a positive definite
symmetric `g` and a symmetric `q` on a finite-dimensional real space, there are only finitely many
relative eigenvalues, so the relative spectral subspace selected by the negative reals is the one
selected by `(-∞, c]` for some `c < 0`. -/
theorem exists_neg_relativeSpectralSubspace_Iio_eq_Iic :
    ∃ c < 0, g.relativeSpectralSubspace q (Iio 0) = g.relativeSpectralSubspace q (Iic c) := by
  obtain ⟨e, T, -, -, -, hΩ⟩ := exists_euclidean_model hg hpos hq
  have hs := (T.finite_restrictedPointSpectrum ⊤).inter_of_left (Iio 0)
  set c := (insert (-1) hs.toFinset).max' (Finset.insert_nonempty _ _)
  have hc : c < 0 := (Finset.max'_lt_iff _ _).mpr fun a ha ↦ by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · norm_num
    · exact (hs.mem_toFinset.mp ha).2
  refine ⟨c, hc, le_antisymm ?_ (relativeSpectralSubspace_mono fun μ hμ ↦ lt_of_le_of_lt hμ hc)⟩
  rw [hΩ, hΩ]
  refine Submodule.map_mono (Module.End.pointSpectralSubspace_le_iff.mpr fun μ hμ ↦ ?_)
  by_cases h : T.eigenspace (μ : ℝ) = ⊥
  · simp [h]
  refine Module.End.eigenspace_le_pointSpectralSubspace (Finset.le_max' _ _ ?_)
  refine Finset.mem_insert_of_mem (hs.mem_toFinset.mpr ⟨?_, hμ⟩)
  exact Module.End.mem_restrictedPointSpectrum_iff_inf_eigenspace_ne_bot.mpr (by simpa using h)

/-- **The negative spectral subspace is negative definite.** For a positive definite symmetric
`g` and a symmetric `q` on a finite-dimensional real space, `q v v < 0` for every nonzero `v` in
the relative spectral subspace selected by the negative reals. -/
theorem apply_self_neg_of_mem_relativeSpectralSubspace_Iio
    (hv : v ∈ g.relativeSpectralSubspace q (Iio 0)) (hv0 : v ≠ 0) : q v v < 0 := by
  obtain ⟨c, hc, hΩ⟩ := exists_neg_relativeSpectralSubspace_Iio_eq_Iic hg hpos hq
  rw [hΩ] at hv
  exact (apply_self_le_mul_apply_self_of_mem_relativeSpectralSubspace hg hpos hq c subset_rfl
    hv).trans_lt (mul_neg_of_neg_of_pos hc (hpos v hv0))

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
    refine ⟨disjoint_relativeSpectralSubspace hg
      (fun v h ↦ by_contra fun hv ↦ (hpos v hv).ne' h) hq (Iio_disjoint_Ici le_rfl),
      codisjoint_iff.mpr ?_⟩
    simpa [N, P, compl_Iio] using relativeSpectralSubspace_sup_compl_eq_top hg hpos hq
      (Ω := Iio 0)
  refine le_antisymm (le_sigNeg_of_negDef _ fun ⟨v, hv⟩ hv0 ↦ ?_) ?_
  · simpa using apply_self_neg_of_mem_relativeSpectralSubspace_Iio hg hpos hq hv
      (by simpa using hv0)
  · -- `q` is positive semidefinite on the complement `P`, so Sylvester bounds `sigNeg q`.
    have hP (v) (hv : v ∈ P) : (-q.toQuadraticMap) v ≤ 0 := by
      have h := apply_self_le_mul_apply_self_of_mem_relativeSpectralSubspace hg hpos hq.neg 0
        (Ω := -Ici 0) (by simp) (by simpa [P] using hv)
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
  refine ⟨disjoint_relativeSpectralSubspace hg
    (fun v h ↦ by_contra fun hv ↦ (hpos v hv).ne' h) hq Iio_disjoint_Ioi_same,
    codisjoint_iff.mpr ?_⟩
  · have hsplit : (univ : Set ℝ) = (Iio 0 ∪ Ioi 0) ∪ {0} := by
      ext x
      simp
    have h := relativeSpectralSubspace_univ hg hpos hq
    rwa [hsplit, relativeSpectralSubspace_union, relativeSpectralSubspace_singleton,
      relativeEigenspace_zero, hker, sup_bot_eq, relativeSpectralSubspace_union] at h

end Real

end LinearMap.BilinForm
