/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenspace
import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Rellich

/-!
# The eigenfunction expansion of the Laplacian on a closed manifold

Let `M` be a closed manifold with a Riemannian metric, its Riemannian volume `dV`, the Sobolev
space `H¹(M)` (`TauCeti.Manifold.SobolevH1`) and the weak eigenspaces
(`TauCeti.Manifold.SobolevH1.weakEigenspace`) of the nonnegative Laplacian `Δ⁺ = -div grad`. This
file proves the spectral theorem for `Δ⁺`: `L²(M)` has a Hilbert basis of eigenfunctions, the
eigenvalues are nonnegative, only finitely many basis vectors have eigenvalue below any bound, and
the multiplicity of each eigenvalue in the basis is the dimension of its eigenspace.

* **Existence** (`TauCeti.Manifold.SobolevH1.exists_hilbertBasis_mem_weakEigenspace`): there is a
  Hilbert basis of `L²(M)` each of whose vectors is the value in `L²(M)` of a weak eigenfunction
  in `H¹(M)`. For a smooth metric the eigenfunctions are smooth functions `u` with `Δu = -μ u`,
  where `Δ = div grad`
  (`TauCeti.Manifold.SobolevH1.exists_hilbertBasis_smoothLaplaceBeltrami_eq_neg_smul`), and the
  eigenspaces of `Δ` on smooth functions have the same dimensions
  (`TauCeti.Manifold.SobolevH1.finrank_eigenspace_smoothLaplaceBeltrami_eq_ncard`).
* **Properties of every such basis.** Its eigenvalues are nonnegative
  (`TauCeti.Manifold.SobolevH1.nonneg_of_mem_weakEigenspace_of_toLp_ne_zero`) and only finitely
  many of them lie below any bound (`TauCeti.Manifold.SobolevH1.finite_setOf_le_of_orthonormal`).
  The values of the weak `ν`-eigenspace are spanned by the basis vectors of eigenvalue `ν`
  (`TauCeti.Manifold.SobolevH1.map_toLp_weakEigenspace_eq_span`), so the weak eigenspaces are
  finite dimensional (`TauCeti.Manifold.SobolevH1.finiteDimensional_weakEigenspace`) and the
  dimension of each is the number of basis vectors with that eigenvalue
  (`TauCeti.Manifold.SobolevH1.finrank_weakEigenspace_eq_ncard`). So a weak eigenspace is nonzero
  exactly when its eigenvalue occurs in the basis, as `0` does for the constants: `Δ⁺` has pure
  point spectrum with finite multiplicities.

## The argument

The `H¹` inner product is the shifted energy form `D(w, v) + ⟪w, v⟫_{L²}`, which is coercive on
`H¹(M)`. By the Rellich–Kondrachov theorem (`TauCeti.Manifold.SobolevH1.isCompactOperator_toLp`)
the value map `J : H¹(M) → L²(M)` is compact, and its range is dense
(`TauCeti.Manifold.SobolevH1.denseRange_toLp`). So the variational spectral theorem
(`IsCoercive.exists_hilbertBasis_forall_apply_eq_smul_inner`) gives a Hilbert basis of `L²(M)`
of values `J u` of solutions of `⟪u, v⟫_{H¹} = κ ⟪J u, J v⟫_{L²}`, that is of weak eigenfunctions
with eigenvalue `μ = κ - 1`. For a smooth metric, weak eigenfunctions are smooth
(`TauCeti.Manifold.SobolevH1.weakEigenspaceEquiv`). Weak eigenfunctions of distinct eigenvalues
are orthogonal in `L²(M)` (`TauCeti.Manifold.SobolevH1.inner_toLp_eq_zero_of_mem_weakEigenspace`),
since `D` is symmetric, so the basis expansion of the value of a weak `ν`-eigenfunction only
involves the basis vectors of eigenvalue `ν`.

These are the properties of the variational eigenspaces of an abstract compact form pair
(`TauCeti.CompactFormPair.formEigenspace`), whose inclusion is assumed injective. They are proved
here directly for the weak eigenspaces, where the value map is injective on each eigenspace
because `‖w‖²_{H¹} = (μ + 1) ‖w‖²_{L²}` there (`norm_sq_eq_of_mem_weakEigenspace`), so that they
hold for a continuous metric, for which injectivity of `toLp` on all of `H¹(M)` is not available.

## References

* I. Chavel, *Eigenvalues in Riemannian Geometry*, Academic Press, 1984, Chapter I (the
  discrete spectrum of the Laplacian of a closed manifold).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.5.1, Theorem 1 (the same variational
  argument for symmetric elliptic operators on a bounded domain).
-/

public section

open Bundle MeasureTheory Module Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

section Continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-! ### Orthogonality and the shifted energy form -/

/-- **Weak eigenfunctions of distinct eigenvalues are orthogonal in `L²(M)`.** -/
theorem inner_toLp_eq_zero_of_mem_weakEigenspace {μ μ' : ℝ} {w w' : SobolevH1 I M}
    (hw : w ∈ weakEigenspace I M μ) (hw' : w' ∈ weakEigenspace I M μ') (hμ : μ ≠ μ') :
    ⟪toLp w, toLp w'⟫_ℝ = 0 := by
  have h := mem_weakEigenspace_iff.1 hw w'
  have h' := mem_weakEigenspace_iff.1 hw' w
  rw [dirichletForm_comm, real_inner_comm (toLp w)] at h'
  have h₀ : (μ - μ') * ⟪toLp w, toLp w'⟫_ℝ = 0 := by linear_combination h.symm.trans h'
  exact (mul_eq_zero.1 h₀).resolve_left (sub_ne_zero.2 hμ)

/-- A weak `μ`-eigenfunction is a variational eigenfunction of the `H¹` inner product, with
eigenvalue `μ + 1`. -/
private theorem innerSL_apply_eq_of_mem_weakEigenspace {μ : ℝ} {w : SobolevH1 I M}
    (hw : w ∈ weakEigenspace I M μ) (v : SobolevH1 I M) :
    innerSL ℝ w v = (μ + 1) * ⟪toLp w, toLp v⟫_ℝ := by
  have h := mem_weakEigenspace_iff.1 hw v
  rw [dirichletForm_apply] at h
  rw [innerSL_apply_apply]
  linear_combination h

/-- The `H¹` norm of a weak `μ`-eigenfunction `w` is determined by its `L²` norm:
`‖w‖²_{H¹} = (μ + 1) ‖w‖²_{L²}`. -/
theorem norm_sq_eq_of_mem_weakEigenspace {μ : ℝ} {w : SobolevH1 I M}
    (hw : w ∈ weakEigenspace I M μ) : ‖w‖ ^ 2 = (μ + 1) * ‖toLp w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← innerSL_apply_apply,
    innerSL_apply_eq_of_mem_weakEigenspace hw]

/-- The value map is injective on each weak eigenspace, whatever the regularity of the metric. -/
theorem toLp_domRestrict_weakEigenspace_injective (μ : ℝ) :
    Function.Injective
      ((toLp : SobolevH1 I M →L[ℝ] _).toLinearMap.domRestrict (weakEigenspace I M μ)) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ Subtype.ext ?_
  have h := norm_sq_eq_of_mem_weakEigenspace w.property
  rw [LinearMap.domRestrict_apply, ContinuousLinearMap.coe_coe] at hw
  rw [hw] at h
  simpa using h

/-! ### Orthonormal families of weak eigenfunctions -/

section Orthonormal

variable {ι : Type*} {u : ι → SobolevH1 I M} {μ : ι → ℝ}

variable [I.Boundaryless]

/-- **Finitely many eigenvalues below any bound.** In an orthonormal family of weak
eigenfunctions, only finitely many members have eigenvalue at most `C`. This is the
Rellich–Kondrachov theorem: the family is bounded in `H¹(M)` below any eigenvalue bound. -/
theorem finite_setOf_le_of_orthonormal (hu : Orthonormal ℝ (toLp ∘ u))
    (hμ : ∀ i, u i ∈ weakEigenspace I M (μ i)) (C : ℝ) : {i | μ i ≤ C}.Finite := by
  have h := isCoercive_innerSL.finite_setOf_le_of_orthonormal isCompactOperator_toLp hu
    (κ := fun i ↦ μ i + 1)
    (fun i ↦ by linarith [nonneg_of_mem_weakEigenspace_of_toLp_ne_zero (hμ i) (hu.ne_zero i)])
    (fun _ ↦ rfl)
    (fun i ↦ innerSL_apply_eq_of_mem_weakEigenspace (hμ i)) (C + 1)
  simpa only [add_le_add_iff_right] using h

/-- Only finitely many members of an orthonormal family of weak eigenfunctions have a given
eigenvalue. -/
private theorem finite_setOf_eq_of_orthonormal (hu : Orthonormal ℝ (toLp ∘ u))
    (hμ : ∀ i, u i ∈ weakEigenspace I M (μ i)) (ν : ℝ) : {i | μ i = ν}.Finite :=
  (finite_setOf_le_of_orthonormal hu hμ ν).subset fun _ hi ↦ le_of_eq hi

end Orthonormal

/-! ### Hilbert bases of weak eigenfunctions -/

section HilbertBasis

variable [I.Boundaryless] {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 (riemannianVolume I M)))
  {u : ι → SobolevH1 I M} {μ : ι → ℝ}

omit [I.Boundaryless] in
/-- Functions in `H¹(M)` whose values form a Hilbert basis of `L²(M)` have orthonormal values. -/
private theorem orthonormal_toLp_of_hilbertBasis (hu : ∀ i, toLp (u i) = b i) :
    Orthonormal ℝ (toLp ∘ u) := by
  simpa only [Function.comp_def, hu] using b.orthonormal

/-- **The weak eigenspaces in an eigenbasis.** If a Hilbert basis `b` of `L²(M)` consists of the
values of weak eigenfunctions `uᵢ` with eigenvalues `μᵢ`, then the values of the weak
`ν`-eigenspace are spanned by the `bᵢ` with `μᵢ = ν`. -/
theorem map_toLp_weakEigenspace_eq_span (hu : ∀ i, toLp (u i) = b i)
    (hμ : ∀ i, u i ∈ weakEigenspace I M (μ i)) (ν : ℝ) :
    (weakEigenspace I M ν).map (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap =
      Submodule.span ℝ (b '' {i | μ i = ν}) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨w, hw, rfl⟩
    have hS := finite_setOf_eq_of_orthonormal (orthonormal_toLp_of_hilbertBasis b hu) hμ ν
    -- The basis coefficients of `toLp w` vanish off the eigenvalue `ν`.
    have hzero : ∀ i ∉ hS.toFinset, b.repr (toLp w) i • b i = 0 := fun i hi ↦ by
      rw [Finite.mem_toFinset, mem_ofPred_eq] at hi
      rw [b.repr_apply_apply, ← hu i,
        inner_toLp_eq_zero_of_mem_weakEigenspace (hμ i) hw hi, zero_smul]
    rw [ContinuousLinearMap.coe_coe,
      ← (hasSum_sum_of_ne_finset_zero hzero).unique (b.hasSum_repr (toLp w))]
    exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, hS.mem_toFinset.1 hi, rfl⟩)
  · rintro _ ⟨i, rfl, rfl⟩
    exact ⟨u i, hμ i, hu i⟩

/-- **Multiplicities in an eigenbasis.** If a Hilbert basis `b` of `L²(M)` consists of the values
of weak eigenfunctions `uᵢ` with eigenvalues `μᵢ`, then the dimension of the weak `ν`-eigenspace
is the number of indices `i` with `μᵢ = ν`. -/
theorem finrank_weakEigenspace_eq_ncard (hu : ∀ i, toLp (u i) = b i)
    (hμ : ∀ i, u i ∈ weakEigenspace I M (μ i)) (ν : ℝ) :
    finrank ℝ (weakEigenspace I M ν) = {i | μ i = ν}.ncard := by
  have hb := b.orthonormal.linearIndependent
  rw [(LinearEquiv.ofInjective _ (toLp_domRestrict_weakEigenspace_injective ν)).finrank_eq,
    LinearMap.range_domRestrict, map_toLp_weakEigenspace_eq_span b hu hμ,
    finrank_span_set_eq_ncard (hb.linearIndepOn _).id_image]
  exact ncard_image_of_injective _ hb.injective

end HilbertBasis

/-! ### Existence of an eigenbasis -/

section Existence

variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **The spectral theorem for the Laplacian on a closed manifold.** `L²(M)` has a Hilbert basis
`b` each of whose vectors `x` is the value of a weak eigenfunction `u x ∈ H¹(M)` of `Δ⁺`, with
eigenvalue `μ x`. Every such basis has nonnegative eigenvalues
(`nonneg_of_mem_weakEigenspace_of_toLp_ne_zero`), only
finitely many of them below any bound (`finite_setOf_le_of_orthonormal`), and the values of each
weak eigenspace are spanned by its basis vectors (`map_toLp_weakEigenspace_eq_span`). As in
`exists_hilbertBasis`, `L²(M)` is not assumed separable and the basis is indexed by a set of
vectors of `L²(M)`. -/
theorem exists_hilbertBasis_mem_weakEigenspace :
    ∃ (s : Set (Lp ℝ 2 (riemannianVolume I M)))
      (b : HilbertBasis s ℝ (Lp ℝ 2 (riemannianVolume I M))) (μ : s → ℝ) (u : s → SobolevH1 I M),
      ⇑b = ((↑) : s → Lp ℝ 2 (riemannianVolume I M)) ∧ (∀ x, toLp (u x) = x) ∧
        ∀ x, u x ∈ weakEigenspace I M (μ x) := by
  obtain ⟨s, b, κ, u, hb, -, -, hJu, heq, -⟩ :=
    isCoercive_innerSL.exists_hilbertBasis_forall_apply_eq_smul_inner
      (isCompactOperator_toLp (I := I) (M := M)) denseRange_toLp fun v w ↦ real_inner_comm w v
  refine ⟨s, b, fun x ↦ κ x - 1, u, hb, hJu, fun x ↦ mem_weakEigenspace_iff.2 fun v ↦ ?_⟩
  have h := heq x v
  rw [innerSL_apply_apply] at h
  rw [dirichletForm_apply]
  linear_combination h

/-- The weak eigenspaces of `Δ⁺` are finite dimensional. -/
instance finiteDimensional_weakEigenspace (ν : ℝ) :
    FiniteDimensional ℝ (weakEigenspace I M ν) := by
  obtain ⟨s, b, μ, u, hb, hu, hμ⟩ := exists_hilbertBasis_mem_weakEigenspace (I := I) (M := M)
  have hu' (x : s) : toLp (u x) = b x := by rw [hu, hb]
  have hspan := FiniteDimensional.span_of_finite ℝ
    ((finite_setOf_eq_of_orthonormal (orthonormal_toLp_of_hilbertBasis b hu') hμ ν).image b)
  rw [← map_toLp_weakEigenspace_eq_span b hu' hμ, ← LinearMap.range_domRestrict] at hspan
  exact (LinearEquiv.ofInjective _
    (toLp_domRestrict_weakEigenspace_injective ν)).symm.finiteDimensional

end Existence

end Continuous

/-! ### Smooth metrics: smooth eigenfunctions -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] instIsContinuousRiemannianBundleOfContMDiffInfty

/-- **The eigenfunction expansion of the Laplacian on a closed manifold.** For a smooth metric,
`L²(M)` has a Hilbert basis `b` each of whose vectors `x` is the class of a smooth function `u x`
with `Δ (u x) = -μ x • u x`, where `Δ = div grad` is the Laplace–Beltrami operator. The eigenvalues
`μ x` of `-Δ` are nonnegative, and only finitely many of them lie below any bound. The
multiplicity of each eigenvalue is the dimension of its eigenspace
(`finrank_eigenspace_smoothLaplaceBeltrami_eq_ncard`). -/
theorem exists_hilbertBasis_smoothLaplaceBeltrami_eq_neg_smul :
    ∃ (s : Set (Lp ℝ 2 (riemannianVolume I M)))
      (b : HilbertBasis s ℝ (Lp ℝ 2 (riemannianVolume I M))) (μ : s → ℝ) (u : s → C^∞⟮I, M; ℝ⟯),
      ⇑b = ((↑) : s → Lp ℝ 2 (riemannianVolume I M)) ∧ (∀ x, toLp (ofSmooth (u x)) = x) ∧
        (∀ x, smoothLaplaceBeltrami I M (u x) = -μ x • u x) ∧ (∀ x, 0 ≤ μ x) ∧
        ∀ C, {x | μ x ≤ C}.Finite := by
  obtain ⟨s, b, μ, w, hb, hw, hμ⟩ := exists_hilbertBasis_mem_weakEigenspace (I := I) (M := M)
  have hon := orthonormal_toLp_of_hilbertBasis b fun x ↦ by rw [hw, hb]
  let v (x : s) := (weakEigenspaceEquiv I M (μ x)).symm ⟨w x, hμ x⟩
  refine ⟨s, b, μ, fun x ↦ v x, hb, fun x ↦ ?_,
    fun x ↦ Module.End.mem_eigenspace_iff.1 (v x).property,
    fun x ↦ nonneg_of_mem_weakEigenspace_of_toLp_ne_zero (hμ x) (hon.ne_zero x),
    finite_setOf_le_of_orthonormal hon hμ⟩
  rw [ofSmooth_weakEigenspaceEquiv_symm_apply, hw]

/-- **Multiplicities of the eigenvalues of the Laplacian.** If a Hilbert basis `b` of `L²(M)`
consists of the classes of smooth functions `uᵢ` with `Δuᵢ = -μᵢ uᵢ`, then the dimension of the
`(-ν)`-eigenspace of `Δ` on smooth functions is the number of indices `i` with `μᵢ = ν`. -/
theorem finrank_eigenspace_smoothLaplaceBeltrami_eq_ncard {ι : Type*}
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (riemannianVolume I M))) {u : ι → C^∞⟮I, M; ℝ⟯} {μ : ι → ℝ}
    (hu : ∀ i, toLp (ofSmooth (u i)) = b i)
    (hμ : ∀ i, smoothLaplaceBeltrami I M (u i) = -μ i • u i) (ν : ℝ) :
    finrank ℝ (Module.End.eigenspace (smoothLaplaceBeltrami I M) (-ν)) =
      {i | μ i = ν}.ncard := by
  rw [(weakEigenspaceEquiv I M ν).finrank_eq]
  refine finrank_weakEigenspace_eq_ncard b hu (fun i ↦ ?_) ν
  rw [← coe_weakEigenspaceEquiv_apply (μ i) ⟨u i, Module.End.mem_eigenspace_iff.2 (hμ i)⟩]
  exact Submodule.coe_mem _

/-- The eigenspaces of the Laplace–Beltrami operator on the smooth functions of a closed manifold
are finite dimensional. -/
instance finiteDimensional_eigenspace_smoothLaplaceBeltrami (ν : ℝ) :
    FiniteDimensional ℝ (Module.End.eigenspace (smoothLaplaceBeltrami I M) ν) := by
  rw [← neg_neg ν]
  exact (weakEigenspaceEquiv I M (-ν)).symm.finiteDimensional

end Smooth

end TauCeti.Manifold.SobolevH1
