/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Riemannian
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# Existence of formal adjoints

Let `V` and `W` be smooth real vector bundles of finite rank with smooth fibre metrics over a
boundaryless manifold `M`, and let `μ` be a measure on `M`. A formal adjoint of a linear operator
`P : Γ(V) → Γ(W)` is an operator `Q : Γ(W) → Γ(V)` with `∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ` whenever `s`
or `t` has compact support (`LinearMap.IsFormalAdjoint`). This file proves that every differential
operator of order at most `m`, in Grothendieck's sense (`TauCeti.differentialOperators`), has a
formal adjoint of order at most `m`, as soon as differentiation along smooth vector fields has
formal transposes of order at most one with respect to `μ`
(`LinearMap.exists_isFormalAdjoint_of_forall_vectorFieldDerivation`). The divergence theorem
supplies these transposes for the Riemannian volume, so with respect to it every differential
operator between such bundles has a formal adjoint, again a differential operator of the same order
(`LinearMap.isFormalAdjoint_formalAdjoint_riemannianVolume_of_mem_differentialOperators`,
`LinearMap.formalAdjoint_riemannianVolume_mem_differentialOperators`). The hypothesis on `μ` also
holds for weighted densities `e^φ dV`
(`LinearMap.isFormalTranspose_vectorFieldDerivation_withDensity_exp`).

## The argument

Formal adjoints glue (`LinearMap.exists_isFormalAdjoint_of_forall_exists_nhds`), exactly as formal
transposes of operators on functions do (`LinearMap.exists_isFormalTranspose_of_forall_exists_nhds`,
whose proof the gluing step follows): if near every point `x` an operator `Q_x` of order at most `m`
is a formal adjoint of `P` for test sections supported near `x`, then for a smooth partition of
unity `ρ_i` subordinate to these neighbourhoods, with compact supports, `t ↦ ∑ᶠ i, Q_i (ρ_i t)` is a
formal adjoint of `P` of order at most `m`.

The local adjoints reduce to operators on functions. Near `x`, orthonormal local frames of `V` and
`W` (`TauCeti.exists_isLocalFrameOn_orthonormal`), cut off by a bump function, give global smooth
sections `e a` of `V` and `f b` of `W` which form orthonormal bases of the fibres over a
neighbourhood `N` of `x`. For `t` supported in `N`, since `P` is local,

`⟪P s, t⟫ = ∑ a b, D a b ⟪s, e a⟫ * ⟪t, f b⟫`,   `D a b g = ⟪P (g • e a), f b⟫`,

and each `D a b` is a differential operator of order at most `m` on `C^∞(M)`. It has a formal
transpose `D' a b` (`LinearMap.exists_isFormalTranspose_of_forall_vectorFieldDerivation`), and
`t ↦ ∑ a b, D' a b ⟪t, f b⟫ • e a` is a formal adjoint of `P` for test sections supported in `N`.

## References

* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (the adjoint of a differential operator between vector bundles).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions and differential operators on manifolds).
-/

public section

noncomputable section

open Bundle MeasureTheory Filter Set TauCeti
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

/-! ### Gluing local formal adjoints -/

section Glue

section Partition

variable {ι : Type*} (ρ : SmoothPartitionOfUnity ι I M univ)
  (Q : ι → Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) (hQ : ∀ i t, (Q i t).tsupport ⊆ t.tsupport)

include hQ in
/-- The pieces `Q i (ρ i • t)` of a glued operator are supported in the supports of the functions
of the partition of unity, so they form a locally finite family. -/
private theorem locallyFinite_glue (t : Cₛ^∞⟮I; F', W⟯) :
    LocallyFinite fun i ↦ {y : M | Q i (ρ i • t) y ≠ 0} :=
  ρ.locallyFinite.closure.subset fun i y hy ↦
    ((hQ i _).trans ((ContMDiffSection.tsupport_smul_function_subset _ t).trans
      inter_subset_left)) (by rw [ContMDiffSection.tsupport_def]; exact subset_closure hy)

/-- The operator `t ↦ ∑ᶠ i, Q i (ρ i • t)` glued from the operators `Q i` along a smooth
partition of unity `ρ`. -/
private def glue : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ where
  toFun t := ⟨fun y ↦ ∑ᶠ i, Q i (ρ i • t) y,
    ContMDiff.finsum_section_of_locallyFinite (locallyFinite_glue ρ Q hQ t)
      fun i ↦ (Q i (ρ i • t)).contMDiff⟩
  map_add' t₁ t₂ := by
    ext y
    simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coeFn_mk]
    rw [← finsum_add_distrib ((locallyFinite_glue ρ Q hQ t₁).point_finite y)
      ((locallyFinite_glue ρ Q hQ t₂).point_finite y)]
    exact finsum_congr fun i ↦ by rw [smul_add (ρ i) t₁ t₂, map_add]; rfl
  map_smul' c t := by
    ext y
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coeFn_mk,
      RingHom.id_apply]
    rw [smul_finsum]
    exact finsum_congr fun i ↦ by rw [← smul_comm c (ρ i) t, map_smul]; rfl

private theorem glue_apply (t : Cₛ^∞⟮I; F', W⟯) (y : M) :
    glue ρ Q hQ t y = ∑ᶠ i, Q i (ρ i • t) y :=
  rfl

/-- Gluing operators of order at most `m` gives an operator of order at most `m`: if `t` lies in
`I_x ^ (m + 1) Γ(W)`, so does each `ρ i • t`, and every piece vanishes at `x`. -/
private theorem glue_mem_differentialOperators [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I] {m : ℕ}
    (hQm : ∀ i, Q i ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m) :
    glue ρ Q hQ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m := by
  refine mem_differentialOperators_section_iff_forall_apply_eq_zero.2 fun x t ht ↦ ?_
  rw [glue_apply]
  exact finsum_eq_zero_of_forall_eq_zero fun i ↦
    mem_differentialOperators_section_iff_forall_apply_eq_zero.1 (hQm i) x _
      (Submodule.smul_mem _ _ ht)

variable [MeasurableSpace M] {μ : Measure M}

/-- The glued operator is a formal adjoint of `P` as soon as each `Q i` is one for test sections
supported in the compact support of `ρ i`. -/
private theorem isFormalAdjoint_glue [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]
    [IsContinuousRiemannianBundle F V] [IsContinuousRiemannianBundle F' W]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} (hP : ∀ s, (P s).tsupport ⊆ s.tsupport)
    (hρ : ∀ i, HasCompactSupport (ρ i))
    (hPQ : ∀ i s (t : Cₛ^∞⟮I; F', W⟯), t.tsupport ⊆ tsupport (ρ i) →
      ∫ y, ⟪P s y, t y⟫ ∂μ = ∫ y, ⟪s y, Q i t y⟫ ∂μ) :
    P.IsFormalAdjoint (glue ρ Q hQ) μ := by
  refine isFormalAdjoint_iff.2 fun s t hst ↦ ?_
  -- Only the finitely many pieces whose support meets the compact support `K` of `s` or of `t`
  -- contribute to either integral.
  obtain ⟨K, hK, hstK⟩ : ∃ K, IsCompact K ∧ (s.tsupport ⊆ K ∨ t.tsupport ⊆ K) :=
    hst.elim (fun hs ↦ ⟨_, hs, .inl subset_rfl⟩) fun ht ↦ ⟨_, ht, .inr subset_rfl⟩
  set S := (ρ.locallyFinite.closure.finite_nonempty_inter_compact hK).toFinset
  have hS {i : ι} {y : M} (hρy : y ∈ tsupport (ρ i)) (hs : y ∈ s.tsupport)
      (ht : y ∈ t.tsupport) : i ∈ S := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨y, hρy, hstK.elim (· hs) (· ht)⟩
  have hρt (i : ι) : (ρ i • t).tsupport ⊆ tsupport (ρ i) ∩ t.tsupport :=
    ContMDiffSection.tsupport_smul_function_subset _ t
  have hcs (i : ι) : IsCompact (ρ i • t).tsupport :=
    (hρ i).of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
      ((hρt i).trans inter_subset_left)
  have hleft (y : M) : ⟪P s y, t y⟫ = ∑ i ∈ S, ⟪P s y, (ρ i • t) y⟫ := by
    by_cases hPs : P s y = 0
    · simp [hPs]
    have hy := hP s (Not.imp_symm (ContMDiffSection.eq_zero_of_notMem_tsupport _) hPs)
    have h1 : t y = ∑ i ∈ S, (ρ i • t) y := by
      have h : t y = ∑ᶠ i, (ρ i • t) y := by
        simp_rw [ContMDiffSection.smul_apply]
        rw [← finsum_smul, ρ.sum_eq_one (mem_univ y), one_smul]
      rw [h]
      refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
      rw [Function.mem_support, ContMDiffSection.smul_apply] at hi
      exact hS (subset_tsupport _ (left_ne_zero_of_smul hi)) hy
        (Not.imp_symm (ContMDiffSection.eq_zero_of_notMem_tsupport _) (right_ne_zero_of_smul hi))
    rw [h1, inner_sum]
  have hright (y : M) : ⟪s y, glue ρ Q hQ t y⟫ = ∑ i ∈ S, ⟪s y, Q i (ρ i • t) y⟫ := by
    by_cases hs : s y = 0
    · simp [hs]
    rw [glue_apply, finsum_eq_sum_of_support_subset (s := S) _ fun i hi ↦ ?_, inner_sum]
    have hy := (hQ i _).trans (hρt i)
      (Not.imp_symm (ContMDiffSection.eq_zero_of_notMem_tsupport _) hi)
    exact hS hy.1 (Not.imp_symm (ContMDiffSection.eq_zero_of_notMem_tsupport _) hs) hy.2
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ fun i _ ↦ integrable_inner_apply_left hP (.inr (hcs i)),
    integral_finsetSum _ fun i _ ↦ integrable_inner_apply_right (hQ i) (.inr (hcs i))]
  exact Finset.sum_congr rfl fun i _ ↦ hPQ i s _ ((hρt i).trans inter_subset_left)

end Partition

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [MeasurableSpace M]
  {μ : Measure M}

/-- **Formal adjoints glue.** Let `P : Γ(V) → Γ(W)` be an operator between smooth sections of
bundles with continuous fibre metrics which does not enlarge supports, with `V` of finite rank. If
near every point `P` has a formal adjoint of order at most `m` for compactly supported test
sections supported in a neighbourhood of that point, then `P` has a formal adjoint of order at most
`m` on all of `M`. It is glued from the local adjoints along a smooth partition of unity. -/
theorem exists_isFormalAdjoint_of_forall_exists_nhds [SigmaCompactSpace M]
    [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I] [IsContinuousRiemannianBundle F V]
    [IsContinuousRiemannianBundle F' W] {m : ℕ}
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} (hP : ∀ s, (P s).tsupport ⊆ s.tsupport)
    (h : ∀ x, ∃ U ∈ 𝓝 x,
      ∃ Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m,
        ∀ s (t : Cₛ^∞⟮I; F', W⟯), IsCompact t.tsupport → t.tsupport ⊆ U →
          ∫ y, ⟪P s y, t y⟫ ∂μ = ∫ y, ⟪s y, Q t y⟫ ∂μ) :
    ∃ Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m,
      P.IsFormalAdjoint Q μ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose U hU Q hQm hPQ using h
  -- Shrink each neighbourhood to a compact one, and take a partition of unity subordinate to
  -- their interiors, so that every function of the partition has compact support.
  choose K hKx hKU hK using fun x ↦ local_compact_nhds (hU x)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun x ↦ interior (K x)) (fun _ ↦ isOpen_interior)
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hKx x)⟩)
  have hρK (x : M) : tsupport (ρ x) ⊆ K x := (hρ x).trans interior_subset
  have hQs (x : M) (t : Cₛ^∞⟮I; F', W⟯) : (Q x t).tsupport ⊆ t.tsupport :=
    tsupport_differentialOperators_section_apply_subset (hQm x) t
  refine ⟨glue ρ Q hQs, glue_mem_differentialOperators ρ Q hQs hQm,
    isFormalAdjoint_glue ρ Q hQs hP (fun x ↦ (hK x).of_isClosed_subset (isClosed_tsupport _)
      (hρK x)) fun x s t ht ↦ hPQ x s t ?_ ((ht.trans (hρK x)).trans (hKU x))⟩
  exact (hK x).of_isClosed_subset (ContMDiffSection.isClosed_tsupport _) (ht.trans (hρK x))

end Glue

/-! ### Formal adjoints in orthonormal frames -/

section Frame

/-- Multiplication of smooth functions by a fixed section, `g ↦ g • σ`, an operator of order zero
from functions to sections. -/
private def smulSection (σ : Cₛ^∞⟮I; F, V⟯) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
  (LinearMap.toSpanSingleton C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ σ).restrictScalars ℝ

private theorem smulSection_apply (σ : Cₛ^∞⟮I; F, V⟯) (g : C^∞⟮I, M; ℝ⟯) (y : M) :
    smulSection σ g y = g y • σ y := by
  simp [smulSection]

/-- Pairing with a fixed section, `t ↦ ⟪t, τ⟫`, an operator of order zero from sections to
functions. -/
private def innerSection [IsContMDiffRiemannianBundle I ∞ F V] (τ : Cₛ^∞⟮I; F, V⟯) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  LinearMap.restrictScalars ℝ (S := C^∞⟮I, M; ℝ⟯)
    { toFun t := ⟨fun y ↦ ⟪t y, τ y⟫, t.contMDiff.inner_bundle τ.contMDiff⟩
      map_add' t₁ t₂ := by ext y; exact inner_add_left _ _ _
      map_smul' g t := by
        ext y
        simp only [ContMDiffSection.smul_apply, real_inner_smul_left]
        rfl }

private theorem innerSection_apply [IsContMDiffRiemannianBundle I ∞ F V] (τ t : Cₛ^∞⟮I; F, V⟯)
    (y : M) : innerSection τ t y = ⟪t y, τ y⟫ :=
  rfl

private theorem smulSection_mem_differentialOperators_zero (σ : Cₛ^∞⟮I; F, V⟯) :
    smulSection σ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ 0 :=
  LinearMap.restrictScalars_mem_differentialOperators_zero _

private theorem innerSection_mem_differentialOperators_zero [IsContMDiffRiemannianBundle I ∞ F V]
    (τ : Cₛ^∞⟮I; F, V⟯) :
    innerSection τ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ C^∞⟮I, M; ℝ⟯ 0 :=
  LinearMap.restrictScalars_mem_differentialOperators_zero _

/-- The scalar coefficient operators `g ↦ ⟪P (g • σ), τ⟫` of an operator `P` of order at most `m`
have order at most `m`. -/
private theorem innerSection_comp_comp_smulSection_mem [IsContMDiffRiemannianBundle I ∞ F' W]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {m : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (σ : Cₛ^∞⟮I; F, V⟯) (τ : Cₛ^∞⟮I; F', W⟯) :
    innerSection τ ∘ₗ P ∘ₗ smulSection σ ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  simpa using comp_mem_differentialOperators (innerSection_mem_differentialOperators_zero τ)
    (comp_mem_differentialOperators hP (smulSection_mem_differentialOperators_zero σ))

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- Near every point of a smooth Riemannian vector bundle of finite rank there are global smooth
sections which form an orthonormal basis of every fibre over a neighbourhood of the point:
orthonormal local frames cut off by a bump function. -/
private theorem exists_nhds_orthonormal_sections [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] (x : M) :
    ∃ N ∈ 𝓝 x, IsOpen N ∧ ∃ e : Fin (Module.finrank ℝ F) → Cₛ^∞⟮I; F, V⟯,
      ∀ y ∈ N, Orthonormal ℝ (e · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (e · y)) := by
  obtain ⟨U, hU, hxU, u, hu, huo⟩ :=
    exists_isLocalFrameOn_orthonormal (I := I) (n := ∞) (F := F) (V := V) x
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 (hU.mem_nhds hxU)
  refine ⟨interior {y | χ y = 1}, interior_mem_nhds.2 χ.eventuallyEq_one, isOpen_interior,
    fun a ↦ ⟨(χ : M → ℝ) • u a, ContMDiffOn.smul_section_of_tsupport χ.contMDiff.contMDiffOn
      hU hχ (hu.contMDiffOn a)⟩, fun y hy ↦ ?_⟩
  have hχy : χ y = 1 := interior_subset hy
  have hyU : y ∈ U :=
    hχ (subset_tsupport _ (by rw [Function.mem_support, hχy]; exact one_ne_zero))
  simp only [ContMDiffSection.coeFn_mk, Pi.smul_apply', hχy, one_smul]
  exact ⟨huo y hyU, hu.generating hyU⟩

variable [IsContMDiffRiemannianBundle I ∞ F V] [IsContMDiffRiemannianBundle I ∞ F' W]
  {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {m : ℕ} {N : Set M}
  {e : Fin (Module.finrank ℝ F) → Cₛ^∞⟮I; F, V⟯} {f : Fin (Module.finrank ℝ F') → Cₛ^∞⟮I; F', W⟯}

/-- Let the sections `e a` of `V` and `f b` of `W` form orthonormal bases of the fibres over an
open set `N`. For a section `t` supported in `N`, the pointwise pairing `⟪P s, t⟫` is
`∑ a b, D a b ⟪s, e a⟫ * ⟪t, f b⟫` for the scalar operators `D a b g = ⟪P (g • e a), f b⟫`: near a
point of `N`, `s = ∑ a, ⟪s, e a⟫ • e a`, and `P` is local. -/
private theorem inner_apply_eq_sum
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (hN : IsOpen N) (he : ∀ y ∈ N, Orthonormal ℝ (e · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (e · y)))
    (hf : ∀ y ∈ N, Orthonormal ℝ (f · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (f · y)))
    (s : Cₛ^∞⟮I; F, V⟯) {t : Cₛ^∞⟮I; F', W⟯} (htN : t.tsupport ⊆ N) (y : M) :
    ⟪P s y, t y⟫ = ∑ a, ∑ b, (innerSection (f b) ∘ₗ P ∘ₗ smulSection (e a))
      (innerSection (e a) s) y * innerSection (f b) t y := by
  by_cases hy : y ∈ N
  swap
  · have hty : t y = 0 := t.eq_zero_of_notMem_tsupport fun h ↦ hy (htN h)
    simp [innerSection_apply, hty]
  have hs : ∀ᶠ z in 𝓝 y, (s - ∑ a, smulSection (e a) (innerSection (e a) s)) z = 0 := by
    filter_upwards [hN.mem_nhds hy] with z hz
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero, ContMDiffSection.coe_sum,
      Finset.sum_apply]
    conv_lhs => rw [← (OrthonormalBasis.mk (he z hz).1 (he z hz).2).sum_repr' (s z)]
    simp [smulSection_apply, innerSection_apply, real_inner_comm]
  have hPs : P s y = ∑ a, P (smulSection (e a) (innerSection (e a) s)) y := by
    have h0 := differentialOperators_section_apply_eq_zero_of_eventuallyEq hP hs
    rwa [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero, map_sum,
      ContMDiffSection.coe_sum, Finset.sum_apply] at h0
  rw [← (OrthonormalBasis.mk (hf y hy).1 (hf y hy).2).sum_inner_mul_inner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Finset.sum_mul, OrthonormalBasis.coe_mk, hPs, sum_inner]
  simp [innerSection_apply, real_inner_comm]

variable [MeasurableSpace M] {μ : Measure M}

/-- **The local formal adjoint.** Let the sections `e a` of `V` and `f b` of `W` form orthonormal
bases of the fibres over an open set `N`, and let `D' a b` be formal transposes of the scalar
operators `D a b g = ⟪P (g • e a), f b⟫`. Then `t ↦ ∑ a b, D' a b ⟪t, f b⟫ • e a` is a formal
adjoint of `P` for compactly supported test sections supported in `N`. -/
private theorem integral_inner_eq_sum [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (hN : IsOpen N) (he : ∀ y ∈ N, Orthonormal ℝ (e · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (e · y)))
    (hf : ∀ y ∈ N, Orthonormal ℝ (f · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (f · y)))
    {D' : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F') →
      C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD'm : ∀ a b, D' a b ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (hD'T : ∀ a b, (innerSection (f b) ∘ₗ P ∘ₗ smulSection (e a)).IsFormalTranspose (D' a b) μ)
    (s : Cₛ^∞⟮I; F, V⟯) {t : Cₛ^∞⟮I; F', W⟯} (ht : IsCompact t.tsupport) (htN : t.tsupport ⊆ N) :
    ∫ y, ⟪P s y, t y⟫ ∂μ =
      ∫ y, ⟪s y, (∑ a, ∑ b, smulSection (e a) ∘ₗ D' a b ∘ₗ innerSection (f b)) t y⟫ ∂μ := by
  have hh b : HasCompactSupport (innerSection (f b) t) :=
    ContMDiffSection.hasCompactSupport_inner (.inl ht)
  have hright (y : M) :
      ⟪s y, (∑ a, ∑ b, smulSection (e a) ∘ₗ D' a b ∘ₗ innerSection (f b)) t y⟫ =
        ∑ a, ∑ b, innerSection (e a) s y * D' a b (innerSection (f b) t) y := by
    simp only [LinearMap.sum_apply, ContMDiffSection.coe_sum, Finset.sum_apply, inner_sum,
      LinearMap.comp_apply, smulSection_apply, inner_smul_right, innerSection_apply]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  have hint₁ a b : Integrable (fun y ↦ (innerSection (f b) ∘ₗ P ∘ₗ smulSection (e a))
      (innerSection (e a) s) y * innerSection (f b) t y) μ :=
    ContMDiffMap.integrable_apply_mul_of_tsupport_subset
      (tsupport_differentialOperators_apply_subset
        (innerSection_comp_comp_smulSection_mem hP (e a) (f b))) (.inr (hh b))
  have hint₂ a b : Integrable
      (fun y ↦ innerSection (e a) s y * D' a b (innerSection (f b) t) y) μ :=
    ContMDiffMap.integrable_mul_apply_of_tsupport_subset
      (tsupport_differentialOperators_apply_subset (hD'm a b)) (.inr (hh b))
  rw [integral_congr_ae (.of_forall (inner_apply_eq_sum hP hN he hf s htN)),
    integral_congr_ae (.of_forall hright),
    integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint₁ a b,
    integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint₂ a b]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_finsetSum _ fun b _ ↦ hint₁ a b, integral_finsetSum _ fun b _ ↦ hint₂ a b]
  exact Finset.sum_congr rfl fun b _ ↦ (hD'T a b).integral_mul_eq (.inr (hh b))

/-- **The local step.** If every differential operator of order at most `m` on `C^∞(M)` has a
formal transpose of order at most `m`, then every differential operator `P : Γ(V) → Γ(W)` of order
at most `m` between bundles of finite rank has a formal adjoint of order at most `m` for test
sections supported near any given point. -/
private theorem exists_nhds_integral_inner_eq [OpensMeasurableSpace M]
    [IsFiniteMeasureOnCompacts μ] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
    [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
    (hT : ∀ D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
      ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
        D.IsFormalTranspose D' μ)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) (x : M) :
    ∃ U ∈ 𝓝 x,
      ∃ Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m,
        ∀ s (t : Cₛ^∞⟮I; F', W⟯), IsCompact t.tsupport → t.tsupport ⊆ U →
          ∫ y, ⟪P s y, t y⟫ ∂μ = ∫ y, ⟪s y, Q t y⟫ ∂μ := by
  obtain ⟨N₁, hN₁, hN₁o, e, he⟩ := exists_nhds_orthonormal_sections (I := I) (F := F) (V := V) x
  obtain ⟨N₂, hN₂, hN₂o, f, hf⟩ := exists_nhds_orthonormal_sections (I := I) (F := F') (V := W) x
  choose D' hD'm hD'T using fun a b ↦
    hT _ (innerSection_comp_comp_smulSection_mem hP (e a) (f b))
  refine ⟨N₁ ∩ N₂, inter_mem hN₁ hN₂, _, sum_mem fun a _ ↦ sum_mem fun b _ ↦ ?_,
    fun s t ht htN ↦ integral_inner_eq_sum hP (hN₁o.inter hN₂o) (fun y hy ↦ he y hy.1)
      (fun y hy ↦ hf y hy.2) hD'm hD'T s ht htN⟩
  simpa using comp_mem_differentialOperators (smulSection_mem_differentialOperators_zero _)
    (comp_mem_differentialOperators (hD'm a b) (innerSection_mem_differentialOperators_zero _))

end Frame

/-! ### Existence -/

section Existence

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] [FiniteDimensional ℝ F']
  [ContMDiffVectorBundle ∞ F' W I] [IsContMDiffRiemannianBundle I ∞ F' W]
  {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {m : ℕ}

/-- **Existence of formal adjoints.** Let `V` and `W` be smooth vector bundles of finite rank with
smooth fibre metrics over a boundaryless manifold, and let `μ` be a measure for which
differentiation along every smooth vector field has a formal transpose of order at most one. Then
every differential operator `P : Γ(V) → Γ(W)` of order at most `m` has a formal adjoint of order at
most `m` with respect to `μ`. -/
theorem exists_isFormalAdjoint_of_forall_vectorFieldDerivation [BoundarylessManifold I M]
    [SigmaCompactSpace M] [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M}
    [IsFiniteMeasureOnCompacts μ]
    (hX : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 1,
        (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    ∃ Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m,
      P.IsFormalAdjoint Q μ :=
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F')
    (V := W)
  exists_isFormalAdjoint_of_forall_exists_nhds
    (tsupport_differentialOperators_section_apply_subset hP) (exists_nhds_integral_inner_eq
      (fun _ hD ↦ exists_isFormalTranspose_of_forall_vectorFieldDerivation hX hD) hP)

/-! ### The Riemannian volume -/

section RiemannianVolume

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- With respect to the Riemannian volume, a differential operator of order at most `m` has a
formal adjoint of order at most `m`. -/
private theorem exists_isFormalAdjoint_riemannianVolume
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    ∃ Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m,
      P.IsFormalAdjoint Q (riemannianVolume I M) :=
  exists_isFormalAdjoint_of_forall_vectorFieldDerivation (fun _ ↦
    ⟨_, formalTranspose_riemannianVolume_mem_differentialOperators
        (Derivation.mem_differentialOperators_one _),
      isFormalTranspose_formalTranspose_riemannianVolume_of_mem_differentialOperators
        (Derivation.mem_differentialOperators_one _)⟩) hP

/-- **Formal adjoints of differential operators.** With respect to the Riemannian volume, every
differential operator between smooth Riemannian vector bundles of finite rank has a formal
adjoint. -/
theorem isFormalAdjoint_formalAdjoint_riemannianVolume_of_mem_differentialOperators
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    P.IsFormalAdjoint (P.formalAdjoint (riemannianVolume I M)) (riemannianVolume I M) :=
  let ⟨_, _, h⟩ := exists_isFormalAdjoint_riemannianVolume hP
  h.isFormalAdjoint_formalAdjoint

/-- With respect to the Riemannian volume, the formal adjoint of a differential operator of order
at most `m` between smooth Riemannian vector bundles of finite rank has order at most `m`. -/
theorem formalAdjoint_riemannianVolume_mem_differentialOperators
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    P.formalAdjoint (riemannianVolume I M) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m := by
  obtain ⟨Q, hQ, h⟩ := exists_isFormalAdjoint_riemannianVolume hP
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  rwa [h.formalAdjoint_eq]

end RiemannianVolume

end Existence

end LinearMap
