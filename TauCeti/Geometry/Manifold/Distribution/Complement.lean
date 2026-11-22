/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiff.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Complementary distributions

Every smooth distribution `D` of rank `k` on a manifold `M` modelled on a finite-dimensional real
space, with `M` Hausdorff and σ-compact, has a smooth complement: a distribution `D'` of rank
`dim M - k`, of the same regularity, with `T_x M = D x ⊕ D' x` at every point
(`TauCeti.IsContMDiffDistribution.exists_isCompl`).

The complement is the orthogonal complement of `D` for a smooth Riemannian metric `g` on `M`,
which exists by `TauCeti.nonempty_contMDiffRiemannianMetric`. To see that it is smooth near a
point `x₀`, take a local frame `X₁, …, X_k` of `D` near `x₀` and read the tangent spaces in the
trivialization `e` of the tangent bundle at `x₀`. At `y`, the orthogonal complement of `D y` is
then the kernel of the operator

`u ↦ (g_y (X₁ y, e⁻¹ u), …, g_y (X_k y, e⁻¹ u))`

from the model space to `ℝᵏ`, which is smooth in `y`. Its kernels have constant dimension
`dim M - k`, so they have smooth local bases (`ContMDiffOn.exists_contMDiffOn_basis_ker`), and
these give a local frame of the complement.

Such complements are used to split the tangent bundle along a distribution, for instance to model
the dual of the kernel bundle of a presymplectic form as an annihilator subbundle of the cotangent
bundle.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 10 (orthogonal complements of subbundles) and Chapter 13 (existence of
  Riemannian metrics).
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The orthogonal complement of a subspace of a tangent space for an inner product `g`, given as
a continuous bilinear form. -/
private def orthogonalAt (g : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (D : Π x : M, Submodule ℝ (TangentSpace I x)) (x : M) : Submodule ℝ (TangentSpace I x) :=
  LinearMap.BilinForm.orthogonal (g x).toLinearMap₁₂ (D x)

private theorem mem_orthogonalAt_iff
    {g : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} {x : M} {v : TangentSpace I x} :
    v ∈ orthogonalAt g D x ↔ ∀ u ∈ D x, g x u v = 0 := by
  simp [orthogonalAt, LinearMap.BilinForm.mem_orthogonal_iff]

/-- A vector is orthogonal to the span of a family exactly when it is orthogonal to each member. -/
private theorem mem_orthogonalAt_iff_of_span_eq
    {g : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} {x : M} {ι : Type*} {X : ι → TangentSpace I x}
    (hX : Submodule.span ℝ (range X) = D x) {v : TangentSpace I x} :
    v ∈ orthogonalAt g D x ↔ ∀ i, g x (X i) v = 0 := by
  rw [mem_orthogonalAt_iff, ← hX]
  refine ⟨fun h i ↦ h _ (Submodule.subset_span (mem_range_self i)), fun h u hu ↦ ?_⟩
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact h i
  | zero => simp
  | add u w _ _ hu hw => simp [hu, hw]
  | smul c u _ hu => simp [hu]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- For a positive definite symmetric `g`, the orthogonal complement of a subspace is a
complement. -/
private theorem isCompl_orthogonalAt
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (D : Π x : M, Submodule ℝ (TangentSpace I x)) (x : M) :
    IsCompl (D x) (orthogonalAt g.inner D x) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hrefl : (LinearMap.BilinForm.restrict (g.inner x).toLinearMap₁₂ (D x)).IsRefl :=
    fun u v h ↦ (g.symm x _ _).trans h
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (fun u v h ↦ (g.symm x _ _).trans h)
    ((LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr fun u hu ↦ ?_)
  by_contra hne
  have hu0 : (u : TangentSpace I x) ≠ 0 := fun h ↦ hne (Subtype.ext h)
  exact (g.pos x u hu0).ne' (by simpa using hu u)

/-- The finite-dimensional orthogonal complement has the complementary dimension. -/
private theorem finrank_orthogonalAt
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} {k : ℕ} {x : M} (hk : finrank ℝ (D x) = k) :
    finrank ℝ (orthogonalAt g.inner D x) = finrank ℝ E - k := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (D x) (orthogonalAt g.inner D x)
  rw [(isCompl_orthogonalAt g D x).sup_eq_top, (isCompl_orthogonalAt g D x).inf_eq_bot,
    finrank_top, finrank_bot, hk] at h
  change finrank ℝ (orthogonalAt g.inner D x) = finrank ℝ (TangentSpace I x) - k
  omega

variable {n : ℕ∞ω} [ENat.LEInfty n] {k : ℕ}

/-- The operator `u ↦ (g_y (X₁ y, e⁻¹ u), …, g_y (X_k y, e⁻¹ u))` from the model space, read in the
tangent trivialization `e` at `x₀`. When the `X i y` span `D y`, its kernel is the orthogonal
complement of `D y` read in `e`. -/
private def orthogonalCoord (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : Fin k → Π y : M, TangentSpace I y) (x₀ y : M) : E →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    (g.inner y (X i y)).comp ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y)

/-- The coordinate operators are `C^n` where the vector fields are. -/
private theorem contMDiffOn_orthogonalCoord
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {X : Fin k → Π y : M, TangentSpace I y}
    {U : Set M} (hX : ∀ i, CMDiff[U] n (T% (X i))) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] (Fin k → ℝ)) n (orthogonalCoord g X x₀)
      (U ∩ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hn : n ≤ ∞ := ENat.LEInfty.out
  have : IsManifold I (n + 1) M := IsManifold.of_le (n := ∞) (by simpa using hn)
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let e := trivializationAt E (TangentSpace I) x₀
  intro y hy
  refine contMDiffWithinAt_clm_apply.mpr fun u ↦ contMDiffWithinAt_pi_module_iff.mpr fun i ↦ ?_
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x (g.inner x))
      (U ∩ e.baseSet) :=
    (g.contMDiff.of_le (by simpa using hn)).contMDiffOn
  have hXi := (hX i).mono (inter_subset_left : U ∩ e.baseSet ⊆ U)
  have hs := (Manifold.contMDiffOn_symm_baseSet (I := I) (n := n) u).mono
    (inter_subset_right : U ∩ e.baseSet ⊆ e.baseSet)
  exact ((hg y hy).clm_bundle_apply₂_trivial (hXi y hy) (hs y hy)).congr
    (fun z hz ↦ by simp [orthogonalCoord, e, e.symmL_apply hz.2])
    (by simp [orthogonalCoord, e, e.symmL_apply hy.2])

omit [FiniteDimensional ℝ E] in
/-- Where the `X i y` span `D y`, the kernel of the coordinate operator is the orthogonal
complement of `D y` read in the trivialization. -/
private theorem ker_orthogonalCoord
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} {X : Fin k → Π y : M, TangentSpace I y}
    {x₀ y : M} (hX : Submodule.span ℝ (range (X · y)) = D y)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (orthogonalCoord g X x₀ y).ker = (orthogonalAt g.inner D y).comap
      (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ y hy).symm :
        E →ₗ[ℝ] TangentSpace I y) := by
  let e := trivializationAt E (TangentSpace I) x₀
  have hs : ⇑(e.symmL ℝ y) = ⇑(e.continuousLinearEquivAt ℝ y hy).symm :=
    (e.symm_continuousLinearEquivAt_eq hy).symm
  ext u
  simp only [LinearMap.mem_ker, Submodule.mem_comap, mem_orthogonalAt_iff_of_span_eq hX]
  simp [orthogonalCoord, e, funext_iff, hs]

/-- **Complementary distributions.** On a Hausdorff σ-compact manifold modelled on a
finite-dimensional real space, every `C^n` distribution `D` of rank `k` has a `C^n` complementary
distribution of rank `dim M - k`: a `C^n` distribution `D'` with `D x` and `D' x` complementary
subspaces of `T_x M` at every point `x`. -/
theorem IsContMDiffDistribution.exists_isCompl [T2Space M] [SigmaCompactSpace M]
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hD : IsContMDiffDistribution I n k D) :
    ∃ D' : Π x : M, Submodule ℝ (TangentSpace I x),
      IsContMDiffDistribution I n (finrank ℝ E - k) D' ∧ ∀ x, IsCompl (D x) (D' x) := by
  -- `∞ + 1` is definitionally `∞` in `WithTop ℕ∞`, so the smooth structure is reused as is.
  have : IsManifold I (∞ + 1) M := ‹IsManifold I ∞ M›
  let : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  -- The complement is the orthogonal complement for `g`. Near `x₀`, take a local frame `X` of
  -- `D` on `U` and the tangent trivialization `e` at `x₀`.
  refine ⟨orthogonalAt g.inner D, isContMDiffDistribution_iff.mpr fun x₀ ↦ ?_,
    isCompl_orthogonalAt g D⟩
  obtain ⟨U, hU, hx₀U, X, hX⟩ := isContMDiffDistribution_iff.mp hD x₀
  let e := trivializationAt E (TangentSpace I) x₀
  have hkA (y : M) (hy : y ∈ U ∩ e.baseSet) :
      finrank ℝ (orthogonalCoord g X x₀ y).ker = finrank ℝ E - k := by
    rw [ker_orthogonalCoord g (hX.span_eq hy.1) hy.2, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.finrank_map_eq,
      finrank_orthogonalAt g (by simpa using hX.isSubbundleFrameOn.finrank_eq hy.1)]
  -- Smooth bases of the kernels of the coordinate operators, transported to the tangent spaces.
  obtain ⟨W, hW, hx₀W, hWV, v, hv, hvker⟩ :=
    (contMDiffOn_orthogonalCoord (n := n) g hX.contMDiffOn x₀).exists_contMDiffOn_basis_ker
      (hU.inter e.open_baseSet) hkA ⟨hx₀U, mem_baseSet_trivializationAt E _ x₀⟩
  let L (y : M) (hy : y ∈ W) := e.continuousLinearEquivAt ℝ y (hWV hy).2
  have hsymm {y : M} (hy : y ∈ W) : e.symm y = ⇑(L y hy).symm := by
    funext u
    rw [e.symm_continuousLinearEquivAt_eq (hWV hy).2, e.symmL_apply (hWV hy).2]
  refine ⟨W, hW, hx₀W, fun i y ↦ e.symm y (v i y), ⟨fun i y hy ↦ ?_, fun {y} hy ↦ ?_,
    fun {y} hy ↦ ?_⟩⟩
  · -- In `e`, the coordinates of the frame are the smooth maps `v i`.
    refine (Trivialization.contMDiffWithinAt_section_iff (e := e) W (hWV hy).2).2 ?_
    exact (hv i y hy).congr (fun z hz ↦ by simp only [e.apply_mk_symm (hWV hz).2])
      (by simp only [e.apply_mk_symm (hWV hy).2])
  · rw [hsymm hy]
    exact (hvker y hy).1.map' _ (L y hy).symm.ker
  · -- Transport the span of the coordinate basis along `(L y).symm`.
    have h := congrArg (Submodule.map ((L y hy).symm : E →ₗ[ℝ] TangentSpace I y))
      ((hvker y hy).2.trans (ker_orthogonalCoord g (hX.span_eq (hWV hy).1) (hWV hy).2))
    rw [Submodule.map_comap_eq_of_surjective (L y hy).symm.surjective,
      Submodule.map_span, ← range_comp] at h
    rw [← h, hsymm hy]
    rfl

end TauCeti
