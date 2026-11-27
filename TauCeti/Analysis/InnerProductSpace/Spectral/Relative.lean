/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.LinearAlgebra.BilinearForm.RelativeEigenspace
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
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

Conversely, every subspace `W` on which `q` is negative definite and whose dimension is the
negative index of inertia is the negative spectral subspace for some `g`: take `g = -q` on `W` and
any inner product on the `q`-orthogonal complement of `W`, the two being `g`-orthogonal. So the
negative spectral subspace depends on `g` unless it is `0` or the whole space, that is unless the
negative index of inertia is `0` or the dimension of `V`.

Applied to the symmetrization `s = g + g.flip` and the form `(v, w) ↦ s (f v) w`, this gives the
spectral theorem for an endomorphism `f` self-adjoint for a positive definite, not necessarily
symmetric, form `g`: its eigenspaces span `V`. This is how operators such as `ad X`, for `X` in
the `-1`-eigenspace of a Cartan involution, are diagonalized without choosing an inner product
space structure.

## Main declarations

* `LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply`: `g` is the pullback of the
  Euclidean inner product along a linear equivalence.
* `LinearMap.BilinForm.exists_continuousLinearEquiv_euclideanSpace_apply_self`: on a
  finite-dimensional Hausdorff topological vector space, that linear equivalence is continuous.
* `LinearMap.BilinForm.relativeEigenspace_innerₗ`: relative to an inner product, the relative
  eigenspaces are the eigenspaces of the operator representing `q`.
* `LinearMap.BilinForm.relativeSpectralSubspace_univ`: the relative eigenvectors span.
* `LinearMap.BilinForm.isCompl_relativeSpectralSubspace_compl`: the relative spectral subspaces
  selected by `Ω` and by its complement are complementary.
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
* `LinearMap.BilinForm.exists_relativeSpectralSubspace_Iio_eq_iff`: the negative spectral
  subspaces of `q`, as `g` varies, are exactly the subspaces of dimension the negative index of
  inertia on which `q` is negative definite.
* `LinearMap.BilinForm.exists_relativeSpectralSubspace_Ioi_eq_iff`: likewise, the positive
  spectral subspaces are the subspaces of dimension the positive index of inertia on which `q` is
  positive definite.
* `LinearMap.BilinForm.exists_ne_negDef_finrank_eq`: shearing a subspace on which `q` is negative
  definite towards a `q`-orthogonal vector outside it with `q (p, p) ≥ 0` gives another such
  subspace of the same dimension.
* `LinearMap.BilinForm.exists_relativeSpectralSubspace_Iio_ne_iff` and
  `LinearMap.BilinForm.exists_relativeSpectralSubspace_Ioi_ne_iff`: the negative spectral subspace
  depends on `g` exactly when the negative index of inertia is neither `0` nor `dim V`, and
  likewise for the positive spectral subspace and the positive index of inertia.
* `LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top`: an endomorphism self-adjoint for a positive
  definite form is diagonalizable.
* `ContinuousLinearEquiv.map_relativeSpectralSubspace_bilinearComp`: pulling continuous forms back
  along a continuous linear equivalence pulls back their relative spectral subspaces.

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
open scoped Pointwise

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

/-- A positive definite symmetric bilinear form on a finite-dimensional Hausdorff topological
vector space is the squared norm of a continuous linear identification with Euclidean space. -/
theorem exists_continuousLinearEquiv_euclideanSpace_apply_self [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) :
    ∃ e : EuclideanSpace ℝ (Fin (finrank ℝ V)) ≃L[ℝ] V, ∀ v, g v v = ‖e.symm v‖ ^ 2 := by
  obtain ⟨e, he⟩ := exists_linearEquiv_euclideanSpace_apply_apply hg hpos
  refine ⟨e.toContinuousLinearEquiv, fun v ↦ ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  simp [he]

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

/-- For a positive definite symmetric `g` and a symmetric `q` on a finite-dimensional real space,
the relative spectral subspaces selected by `Ω` and by its complement are complementary. -/
theorem isCompl_relativeSpectralSubspace_compl :
    IsCompl (g.relativeSpectralSubspace q Ω) (g.relativeSpectralSubspace q Ωᶜ) :=
  ⟨disjoint_relativeSpectralSubspace_of_pos hg hpos hq disjoint_compl_right,
    codisjoint_iff.mpr (relativeSpectralSubspace_sup_compl_eq_top hg hpos hq)⟩

/-- **Upper form bound.** If every eigenvalue in `Ω` is at most `c`, then `q v v ≤ c * g v v` on
the relative spectral subspace selected by `Ω`. -/
theorem apply_self_le_mul_apply_self_of_mem_relativeSpectralSubspace (c : ℝ) (hΩ : Ω ⊆ Iic c)
    (hv : v ∈ g.relativeSpectralSubspace q Ω) : q v v ≤ c * g v v := by
  obtain ⟨e, T, hT, he, hTq, hΩ'⟩ := exists_euclidean_model hg hpos hq
  rw [hΩ', hT.pointSpectralSubspace_eq_eigenvectorSpan rfl,
    LinearMap.IsSymmetric.eigenvectorSpan_eq_spanIndices] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have key := LinearMap.re_inner_le_of_eigenbasis T (hT.eigenvectorBasis rfl)
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
    simpa [N, P, compl_Iio] using isCompl_relativeSpectralSubspace_compl hg hpos hq (Ω := Iio 0)
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
  refine ⟨disjoint_relativeSpectralSubspace_of_pos hg hpos hq Iio_disjoint_Ioi_same,
    codisjoint_iff.mpr ?_⟩
  · have hsplit : (univ : Set ℝ) = (Iio 0 ∪ Ioi 0) ∪ {0} := by
      ext x
      simp
    have h := relativeSpectralSubspace_univ hg hpos hq
    rwa [hsplit, relativeSpectralSubspace_union, relativeSpectralSubspace_singleton,
      relativeEigenspace_zero, hker, sup_bot_eq, relativeSpectralSubspace_union] at h

end Real

/-! ### Which subspaces are negative spectral subspaces -/

section Realization

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {g q : LinearMap.BilinForm ℝ V}

/-- If `q` is negative definite on `W`, then for every positive definite symmetric `g` the form
`(x, y) ↦ -q (π x) (π y) + g (x - π x) (y - π y)`, where `π` projects onto `W` along its
`q`-orthogonal complement, is positive definite and symmetric, and `q` acts on `W` as `-1` times
it. -/
private theorem exists_le_relativeEigenspace_neg_one (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hq : q.IsSymm) {W : Submodule ℝ V}
    (hW : ∀ v ∈ W, v ≠ 0 → q v v < 0) :
    ∃ g' : LinearMap.BilinForm ℝ V, g'.IsSymm ∧ (∀ v, v ≠ 0 → 0 < g' v v) ∧
      W ≤ g'.relativeEigenspace q (-1) := by
  -- `q` is nondegenerate on `W`, so `W` is complementary to its `q`-orthogonal complement.
  have hc : IsCompl W (q.orthogonal W) := by
    have key (x : W) (hx : q.restrict W x x = 0) : x = 0 := by
      by_contra hx0
      exact (hW x x.property (by simpa using hx0)).ne hx
    exact isCompl_orthogonal_of_restrict_nondegenerate hq.isRefl
      ⟨fun x hx ↦ key x (hx x), fun x hx ↦ key x (hx x)⟩
  set π := W.projection (q.orthogonal W) hc
  set π' := (q.orthogonal W).projection W hc.symm
  have hπ (x : V) : π x + π' x = x := Submodule.projection_add_projection_eq_self hc x
  refine ⟨-(q.compl₁₂ π π) + g.compl₁₂ π' π', isSymm_def.mpr fun x y ↦ ?_, fun v hv ↦ ?_,
    fun w hw ↦ mem_relativeEigenspace_iff.mpr fun y ↦ ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.neg_apply, compl₁₂_apply]
    rw [hq.eq (π x), hg.eq (π' x)]
  · have h₁ : 0 ≤ -q (π v) (π v) := by
      rcases eq_or_ne (π v) 0 with h | h
      · simp [h]
      · exact (neg_pos.mpr (hW _ (Submodule.projection_apply_mem hc v) h)).le
    have h₂ : 0 ≤ g (π' v) (π' v) := by
      rcases eq_or_ne (π' v) 0 with h | h
      · simp [h]
      · exact (hpos _ h).le
    simp only [LinearMap.add_apply, LinearMap.neg_apply, compl₁₂_apply]
    -- One of the two components of the nonzero vector `v` is nonzero.
    rcases eq_or_ne (π v) 0 with h | h
    · have h' : π' v ≠ 0 := fun h' ↦ hv (by rw [← hπ v, h, h', add_zero])
      linarith [hpos _ h']
    · linarith [hW _ (Submodule.projection_apply_mem hc v) h]
  · have hπw : π w = w := Submodule.projection_apply_of_mem_left hc hw
    have hπ'w : π' w = 0 := Submodule.projection_apply_of_mem_right hc.symm hw
    have hy : q w (π' y) = 0 :=
      (mem_orthogonal_iff.mp (Submodule.projection_apply_mem hc.symm y)) w hw
    conv_lhs => rw [← hπ y]
    simp [hπw, hπ'w, hy]

/-- **The negative spectral subspaces of a symmetric form.** For a symmetric bilinear form `q` on a
finite-dimensional real space, a subspace `W` is the negative spectral subspace of `q` relative to
some positive definite symmetric `g` exactly when `q` is negative definite on `W` and the
dimension of `W` is the negative index of inertia of `q`. -/
theorem exists_relativeSpectralSubspace_Iio_eq_iff (hq : q.IsSymm) {W : Submodule ℝ V} :
    (∃ g : LinearMap.BilinForm ℝ V, g.IsSymm ∧ (∀ v, v ≠ 0 → 0 < g v v) ∧
        g.relativeSpectralSubspace q (Iio 0) = W) ↔
      (∀ v ∈ W, v ≠ 0 → q v v < 0) ∧ finrank ℝ W = sigNeg q.toQuadraticMap := by
  constructor
  · rintro ⟨g, hg, hpos, rfl⟩
    exact ⟨fun v hv hv0 ↦ apply_self_neg_of_mem_relativeSpectralSubspace_Iio hg hpos hq hv hv0,
      finrank_relativeSpectralSubspace_Iio hg hpos hq⟩
  · rintro ⟨hW, hWr⟩
    -- Any inner product on `V` serves as a positive definite symmetric form to start from.
    let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
    let e : V ≃ₗ[ℝ] E := LinearEquiv.ofFinrankEq _ _ (by simp [E])
    let g₀ : LinearMap.BilinForm ℝ V := (innerₗ E).compl₁₂ (e : V →ₗ[ℝ] E) (e : V →ₗ[ℝ] E)
    have hg₀ (x y : V) : g₀ x y = ⟪e x, e y⟫_ℝ := rfl
    obtain ⟨g, hg, hpos, hle⟩ := exists_le_relativeEigenspace_neg_one (g := g₀)
      (isSymm_def.mpr fun x y ↦ by rw [hg₀, hg₀, real_inner_comm])
      (fun v hv ↦ by rw [hg₀]; exact real_inner_self_pos.mpr (by simpa using hv)) hq hW
    refine ⟨g, hg, hpos, (Submodule.eq_of_le_of_finrank_eq (hle.trans
      (relativeEigenspace_le_relativeSpectralSubspace (by norm_num))) ?_).symm⟩
    rw [hWr, finrank_relativeSpectralSubspace_Iio hg hpos hq]

/-- **The positive spectral subspaces of a symmetric form.** For a symmetric bilinear form `q` on a
finite-dimensional real space, a subspace `W` is the positive spectral subspace of `q` relative to
some positive definite symmetric `g` exactly when `q` is positive definite on `W` and the
dimension of `W` is the positive index of inertia of `q`. -/
theorem exists_relativeSpectralSubspace_Ioi_eq_iff (hq : q.IsSymm) {W : Submodule ℝ V} :
    (∃ g : LinearMap.BilinForm ℝ V, g.IsSymm ∧ (∀ v, v ≠ 0 → 0 < g v v) ∧
        g.relativeSpectralSubspace q (Ioi 0) = W) ↔
      (∀ v ∈ W, v ≠ 0 → 0 < q v v) ∧ finrank ℝ W = sigPos q.toQuadraticMap := by
  have h := exists_relativeSpectralSubspace_Iio_eq_iff hq.neg (W := W)
  simp only [relativeSpectralSubspace_neg, neg_Iio, neg_zero, neg_apply, neg_lt_zero] at h
  simpa using h

omit [FiniteDimensional ℝ V] in
/-- **Shearing a negative definite subspace.** Let `q` be symmetric and negative definite on `N`,
let `n ∈ N` be nonzero, and let `p ∉ N` be `q`-orthogonal to `N` with `0 ≤ q p p`. For small
`t > 0`, the image of `N` under `x ↦ x + t q (n, x) p` is a subspace of the same dimension, other
than `N`, on which `q` is negative definite. -/
theorem exists_ne_negDef_finrank_eq (hq : q.IsSymm) {N : Submodule ℝ V}
    (hN : ∀ v ∈ N, v ≠ 0 → q v v < 0) {n p : V} (hn : n ∈ N) (hn0 : n ≠ 0) (hp : p ∉ N)
    (hxp : ∀ x ∈ N, q x p = 0) (hpp : 0 ≤ q p p) :
    ∃ W : Submodule ℝ V, W ≠ N ∧ (∀ v ∈ W, v ≠ 0 → q v v < 0) ∧ finrank ℝ W = finrank ℝ N := by
  have hnn : q n n < 0 := hN n hn hn0
  -- Cauchy–Schwarz for the positive semidefinite form `-q` on `N`.
  have hcs {x : V} (hx : x ∈ N) : q n x ^ 2 ≤ q n n * q x x := by
    have hs (y : N) : 0 ≤ (-q).restrict N y y := by
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · simpa using (hN y y.property (by simpa using hy)).le
    simpa using apply_sq_le_of_symm _ hs (isSymm_iff.mp (hq.neg.restrict N)) ⟨n, hn⟩ ⟨x, hx⟩
  set t := (1 + q p p * -q n n)⁻¹
  have ht : 0 < t := inv_pos.mpr (by nlinarith)
  have ht' : t * (1 + q p p * -q n n) = 1 := inv_mul_cancel₀ (by nlinarith)
  let T : V →ₗ[ℝ] V := LinearMap.id + t • (q n).smulRight p
  have hT (x : V) : T x = x + (t * q n x) • p := by simp [T, mul_smul]
  have hTinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun x hx ↦ ?_
    have hx' : x = -((t * q n x) • p) := eq_neg_of_add_eq_zero_left (by rw [← hT, hx])
    have : q n x = 0 := by
      rw [hx', map_neg, map_smul, hxp n hn]
      simp
    simpa [this] using hx'
  refine ⟨N.map T, fun h ↦ hp ?_, ?_, (Submodule.equivMapOfInjective T hTinj N).finrank_eq.symm⟩
  · -- `T n - n` is a nonzero multiple of `p`, so `T n` is not in `N`.
    have hTn : T n ∈ N := h ▸ Submodule.mem_map_of_mem hn
    have hmem : (t * q n n) • p ∈ N := by simpa [hT] using N.sub_mem hTn hn
    exact (N.smul_mem_iff (mul_ne_zero ht.ne' hnn.ne)).mp hmem
  · rintro _ ⟨x, hx, rfl⟩ hTx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hTx
    have hxx : q x x < 0 := hN x hx hx0
    have hpx : q p x = 0 := by rw [hq.eq p x]; exact hxp x hx
    have hexp : q (T x) (T x) = q x x + (t * q n x) ^ 2 * q p p := by
      simp only [hT, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hxp x hx, hpx]
      ring
    rw [hexp]
    -- `(t q (n, x))² q (p, p) ≤ t² q (p, p) (-q (n, n)) (-q (x, x)) < -q (x, x)`.
    have h₁ : (t * q n x) ^ 2 * q p p ≤ t ^ 2 * (q p p * -q n n) * -q x x := by
      have := mul_le_mul_of_nonneg_left (hcs hx) (mul_nonneg (sq_nonneg t) hpp)
      nlinarith
    have h₂ : t ^ 2 * (q p p * -q n n) < 1 := by
      have : 0 ≤ q p p * -q n n := mul_nonneg hpp (by linarith)
      nlinarith
    nlinarith

/-- If the negative spectral subspace `N` of `q` relative to `g` is neither `0` nor everything,
shearing it towards a nonzero vector of the complementary nonnegative spectral subspace gives
another subspace of dimension the negative index of inertia on which `q` is negative definite. -/
private theorem exists_ne_relativeSpectralSubspace_Iio (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hq : q.IsSymm) (hN : g.relativeSpectralSubspace q (Iio 0) ≠ ⊥)
    (hN' : g.relativeSpectralSubspace q (Iio 0) ≠ ⊤) :
    ∃ W : Submodule ℝ V, W ≠ g.relativeSpectralSubspace q (Iio 0) ∧
      (∀ v ∈ W, v ≠ 0 → q v v < 0) ∧ finrank ℝ W = sigNeg q.toQuadraticMap := by
  set N := g.relativeSpectralSubspace q (Iio 0)
  set P := g.relativeSpectralSubspace q (Ici 0)
  have hNP : IsCompl N P := by
    simpa [N, P, compl_Iio] using isCompl_relativeSpectralSubspace_compl hg hpos hq (Ω := Iio 0)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show P ≠ ⊥ from fun hP ↦
    hN' (by rw [← hNP.sup_eq_top, hP, sup_bot_eq]))
  -- `q` vanishes between `N` and `P`, and is nonnegative on `P`.
  have hpp : 0 ≤ q p p := by
    have h := apply_self_le_mul_apply_self_of_mem_relativeSpectralSubspace hg hpos hq.neg 0
      (Ω := -Ici 0) (by simp) (by simpa [relativeSpectralSubspace_neg] using hp)
    simpa using h
  obtain ⟨W, hW, hWneg, hWr⟩ := exists_ne_negDef_finrank_eq hq
    (fun v hv hv0 ↦ apply_self_neg_of_mem_relativeSpectralSubspace_Iio hg hpos hq hv hv0) hn hn0
    (fun hpN ↦ hp0 (Submodule.disjoint_def.mp hNP.disjoint p hpN hp))
    (fun x hx ↦ (apply_eq_zero_of_mem_relativeSpectralSubspace hg hq (Iio_disjoint_Ici le_rfl) hx
      hp).2) hpp
  exact ⟨W, hW, hWneg, hWr.trans (finrank_relativeSpectralSubspace_Iio hg hpos hq)⟩

/-- **The negative spectral subspace depends on the positive definite form.** For a symmetric
bilinear form `q` on a finite-dimensional real space and a positive definite symmetric `g`, some
other positive definite symmetric `g'` has a different negative spectral subspace of `q` exactly
when the negative index of inertia of `q` is neither `0` nor the dimension of the space. In the
two excluded cases the negative spectral subspace is `0`, respectively the whole space, for every
`g`. -/
theorem exists_relativeSpectralSubspace_Iio_ne_iff (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hq : q.IsSymm) :
    (∃ g' : LinearMap.BilinForm ℝ V, g'.IsSymm ∧ (∀ v, v ≠ 0 → 0 < g' v v) ∧
        g'.relativeSpectralSubspace q (Iio 0) ≠ g.relativeSpectralSubspace q (Iio 0)) ↔
      sigNeg q.toQuadraticMap ≠ 0 ∧ sigNeg q.toQuadraticMap ≠ finrank ℝ V := by
  have hN := finrank_relativeSpectralSubspace_Iio hg hpos hq
  constructor
  · rintro ⟨g', hg', hpos', hne⟩
    have hN' := finrank_relativeSpectralSubspace_Iio hg' hpos' hq
    refine ⟨fun h ↦ hne ?_, fun h ↦ hne ?_⟩
    · rw [Submodule.finrank_eq_zero.mp (hN'.trans h), Submodule.finrank_eq_zero.mp (hN.trans h)]
    · rw [Submodule.eq_top_of_finrank_eq (hN'.trans h), Submodule.eq_top_of_finrank_eq (hN.trans h)]
  · rintro ⟨h₀, h₁⟩
    obtain ⟨W, hW, hWneg, hWr⟩ := exists_ne_relativeSpectralSubspace_Iio hg hpos hq
      (fun h ↦ h₀ (by rw [← hN, h, finrank_bot]))
      (fun h ↦ h₁ (by rw [← hN, h, finrank_top]))
    obtain ⟨g', hg', hpos', rfl⟩ := (exists_relativeSpectralSubspace_Iio_eq_iff hq).mpr ⟨hWneg, hWr⟩
    exact ⟨g', hg', hpos', hW⟩

/-- **The positive spectral subspace depends on the positive definite form.** For a symmetric
bilinear form `q` on a finite-dimensional real space and a positive definite symmetric `g`, some
other positive definite symmetric `g'` has a different positive spectral subspace of `q` exactly
when the positive index of inertia of `q` is neither `0` nor the dimension of the space. -/
theorem exists_relativeSpectralSubspace_Ioi_ne_iff (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hq : q.IsSymm) :
    (∃ g' : LinearMap.BilinForm ℝ V, g'.IsSymm ∧ (∀ v, v ≠ 0 → 0 < g' v v) ∧
        g'.relativeSpectralSubspace q (Ioi 0) ≠ g.relativeSpectralSubspace q (Ioi 0)) ↔
      sigPos q.toQuadraticMap ≠ 0 ∧ sigPos q.toQuadraticMap ≠ finrank ℝ V := by
  have h := exists_relativeSpectralSubspace_Iio_ne_iff hg hpos hq.neg
  simp only [relativeSpectralSubspace_neg, neg_Iio, neg_zero] at h
  simpa using h

end Realization

end LinearMap.BilinForm

namespace LinearMap.IsSelfAdjoint

open LinearMap.BilinForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {g : LinearMap.BilinForm ℝ V} {f : Module.End ℝ V}

/-- **Self-adjoint endomorphisms are diagonalizable.** On a finite-dimensional real space, the
eigenspaces of an endomorphism self-adjoint for a positive definite bilinear form span the space.
The form need not be symmetric. -/
theorem iSup_eigenspace_eq_top (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hf : g.IsSelfAdjoint f) :
    ⨆ μ : ℝ, f.eigenspace μ = ⊤ := by
  -- Pass to the symmetrization `s`, for which `f` is still self-adjoint.
  set s := g + g.flip
  have hs : s.IsSymm := ⟨fun v w ↦ by simp [s, add_comm]⟩
  have hspos (v) (hv : v ≠ 0) : 0 < s v v := by
    simpa [s] using add_pos (hpos v hv) (hpos v hv)
  have hfs (v w : V) : s (f v) w = s v (f w) := by
    simp [s, hf v w, hf w v]
  have hsep : s.SeparatingLeft :=
    separatingLeft_of_anisotropic (QuadraticMap.PosDef.anisotropic hspos)
  have hq : (s.compLeft f).IsSymm := ⟨fun v w ↦ by
    simp only [LinearMap.BilinForm.compLeft_apply, hfs, hs.eq v]⟩
  simpa [relativeSpectralSubspace_def, relativeEigenspace_compLeft hsep] using
    relativeSpectralSubspace_univ hs hspos hq

end LinearMap.IsSelfAdjoint

/-! ### Pullbacks along continuous linear equivalences -/

namespace ContinuousLinearEquiv

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Pulling a form and a metric back along a linear equivalence `e` pulls back their relative
spectral subspaces: these are carried by `e` to the relative spectral subspaces of the original
pair. -/
@[simp]
theorem map_relativeSpectralSubspace_bilinearComp (e : W ≃L[𝕜] V) (q h : V →L[𝕜] V →L[𝕜] 𝕜)
    (Ω : Set 𝕜) :
    ((h.bilinearComp (e : W →L[𝕜] V) (e : W →L[𝕜] V)).toBilinForm.relativeSpectralSubspace
      (q.bilinearComp (e : W →L[𝕜] V) (e : W →L[𝕜] V)).toBilinForm Ω).map
        (e.toLinearEquiv : W →ₗ[𝕜] V) =
      h.toBilinForm.relativeSpectralSubspace q.toBilinForm Ω := by
  have hc (B : V →L[𝕜] V →L[𝕜] 𝕜) : (B.bilinearComp (e : W →L[𝕜] V) (e : W →L[𝕜] V)).toBilinForm =
      B.toBilinForm.compl₁₂ (e.toLinearEquiv : W →ₗ[𝕜] V) (e.toLinearEquiv : W →ₗ[𝕜] V) := by
    ext u v
    simp
  rw [hc, hc]
  exact LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂ e.toLinearEquiv

/-- A vector lies in a relative spectral subspace of a pulled-back pair exactly when its image
lies in the corresponding relative spectral subspace of the original pair. -/
@[simp]
theorem mem_relativeSpectralSubspace_bilinearComp_iff (e : W ≃L[𝕜] V) {q h : V →L[𝕜] V →L[𝕜] 𝕜}
    {Ω : Set 𝕜} {u : W} :
    u ∈ (h.bilinearComp (e : W →L[𝕜] V) (e : W →L[𝕜] V)).toBilinForm.relativeSpectralSubspace
        (q.bilinearComp (e : W →L[𝕜] V) (e : W →L[𝕜] V)).toBilinForm Ω ↔
      e u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm Ω := by
  rw [← e.map_relativeSpectralSubspace_bilinearComp q h Ω, Submodule.mem_map]
  refine ⟨fun hu ↦ ⟨u, hu, rfl⟩, fun ⟨w, hw, hwu⟩ ↦ ?_⟩
  rwa [← e.injective hwu]

end ContinuousLinearEquiv
