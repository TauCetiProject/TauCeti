/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConstantRank.Basic
public import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Level manifolds of constant-rank maps

A level of a constant-rank map from a boundaryless finite-dimensional manifold to a boundaryless
Banach manifold is an embedded manifold, with its subspace topology and tangent space equal to
the derivative kernel. It is
enough that the rank be constant on an open neighbourhood of the entire level. Neither ambient
manifold needs to be Hausdorff or second-countable, and the level may be empty.

The constant-rank coordinates give local regular equations with values in the image of the
derivative. The resulting regular-level manifolds glue by their immersion universal property.
The construction uses `TauCeti.regularLevelChartedSpace` and
`TauCeti.chartedSpaceOfIsOpenEmbedding`, following the embedded-patch gluing argument of
`TauCeti.exists_isManifold_transverseFiberProduct_isSmoothEmbedding`.

`constantRankFiberChartedSpace` is a named, non-instance atlas. Its manifold, embedding and
tangent-image properties are given below. The embedding supplies the smooth universal property
through `Manifold.IsSmoothEmbedding.contMDiff_iff_comp`: a map into the fibre is smooth exactly
when its composite with the inclusion is smooth.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer (2013),
  Theorems 4.12 and 5.12 (constant rank and constant-rank level sets).
-/

public section

open Set Function Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {U : Set M} {x : M} {c : N} {r : ℕ}

/-- Near a point of locally constant rank, the level has regular equations with values in a
finite-dimensional vector space of dimension equal to the rank. This does not require that
`f` itself be a submersion. -/
theorem exists_regular_eq_of_constantRank
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n)
    (hrank : ∀ y ∈ U, mfderivRank I J f y ≤ mfderivRank I J f x) :
    ∃ (V : TopologicalSpace.Opens M) (_ : x ∈ V) (_ : (V : Set M) ⊆ U)
      (L : Submodule 𝕜 F) (q : V → L),
      FiniteDimensional 𝕜 L ∧ finrank 𝕜 L = mfderivRank I J f x ∧
      ContMDiff I 𝓘(𝕜, L) n q ∧ IsRegularValue I 𝓘(𝕜, L) q 0 ∧
      ∀ y : V, q y = 0 ↔ f y = f x := by
  obtain ⟨φ, hxφ, hφU, -, hφ, hφi, heq⟩ :=
    hf.exists_openPartialHomeomorph_apply_eq_iff_mem_ker hU hx hn hrank
  let Φ : PartialDiffeomorph I 𝓘(𝕜, E) M E n :=
    { φ with contMDiffOn_toFun := hφ, contMDiffOn_invFun := hφi }
  let V : TopologicalSpace.Opens M := ⟨φ.source, φ.open_source⟩
  let D := (tangentSpaceCastModel J (f x)).toContinuousLinearMap.comp
    ((mfderiv I J f x).comp (tangentSpaceCastModel I x).symm.toContinuousLinearMap)
  let L := D.range
  let Q : E →L[𝕜] L := D.rangeRestrict
  let q : V → L := fun y ↦ Q (φ y)
  have hcoord : ContMDiff I 𝓘(𝕜, E) n (fun y : V ↦ φ y) :=
    hφ.comp_contMDiff contMDiff_subtype_val fun y ↦ y.2
  have hreg (y : V) : IsRegularPoint I 𝓘(𝕜, L) q y := by
    have hQ : IsRegularPoint 𝓘(𝕜, E) 𝓘(𝕜, L) Q (φ y) := by
      rw [isRegularPoint_iff_surjective_fderiv, Q.fderiv]
      exact D.toLinearMap.surjective_rangeRestrict
    have hΦ : IsRegularPoint I 𝓘(𝕜, E) (fun y : V ↦ φ y) y := by
      have hloc := IsLocalDiffeomorphAt.comp (K := 𝓘(𝕜, E))
        (hg := Φ.isLocalDiffeomorphAt I 𝓘(𝕜, E) n y.2)
        (hf := isLocalDiffeomorph_subtype_val (I := I) (n := n) y)
      exact isRegularPoint_iff.2
        (hloc.isInvertible_mfderiv (ne_of_gt (zero_lt_one.trans_le hn))).surjective
    exact hQ.comp (g := fun y : V ↦ φ y) hΦ
  refine ⟨V, hxφ, hφU, L, q, inferInstance, ?_, Q.contMDiff.comp hcoord,
    isRegularValue_iff.2 (fun y _ ↦ hreg y), fun y ↦ ?_⟩
  · rw [mfderivRank_def]
    exact LinearMap.finrank_range_comp_comp _ (mfderiv I J f x).toLinearMap _
      (tangentSpaceCastModel J (f x)).injective (tangentSpaceCastModel I x).symm.surjective
  · rw [heq y y.2]
    simp only [q, Q, Subtype.ext_iff, ZeroMemClass.coe_zero,
      ContinuousLinearMap.rangeRestrict, ContinuousLinearMap.coe_codRestrict_apply,
      D, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearMap.mem_ker]
    exact (tangentSpaceCastModel J (f x)).map_eq_zero_iff

private theorem exists_levelPatch_of_constantRank
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hrank : ∀ y ∈ U, mfderivRank I J f y = r)
    (z : {x : M // f x = c}) (hz : z.1 ∈ U) :
    ∃ (V : TopologicalSpace.Opens M) (_ : z.1 ∈ V)
      (a : ChartedSpace (Fin (finrank 𝕜 E - r) → 𝕜)
        {y : {x : M // f x = c} // y.1 ∈ V}),
      letI := a
      IsManifold 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) n
        {y : {x : M // f x = c} // y.1 ∈ V} ∧
      Manifold.IsSmoothEmbedding 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) I n
        (fun y : {y : {x : M // f x = c} // y.1 ∈ V} ↦ y.1.1) := by
  obtain ⟨V, hzV, -, L, q, hfin, hdim, hq, hreg, heq⟩ :=
    exists_regular_eq_of_constantRank hf hU hz hn (fun y hy ↦ by rw [hrank y hy, hrank z hz])
  let := hfin
  have heq' (y : V) : q y = 0 ↔ f y = c := by rw [heq, z.2]
  have hdim' : finrank 𝕜 E - finrank 𝕜 L = finrank 𝕜 E - r := by rw [hdim, hrank z hz]
  let P := {y : {x : M // f x = c} // y.1 ∈ V}
  let e : P ≃ₜ {y : V // q y = 0} :=
    { toFun y := ⟨⟨y.1.1, y.2⟩, (heq' _).2 y.1.2⟩
      invFun y := ⟨⟨y.1, (heq' _).1 y.2⟩, y.1.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val :
        Continuous (fun y : P ↦ y.1.1)).subtype_mk _ |>.subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        |>.subtype_mk _ }
  let K := 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜)
  let := regularLevelChartedSpace (fun y _ ↦ (hq y).of_le hn) hreg hdim'
  have := isManifold_regularLevel hn (fun y _ ↦ hq y) hreg hdim'
  let := e.pullbackChartedSpace (H := Fin (finrank 𝕜 E - r) → 𝕜)
  have := e.pullback_isManifold K n
  have hi := isImmersionOfComplement_comp_diffeomorph (e.pullbackDiffeomorph K n)
    (isImmersionOfComplement_coe_regularLevel hn (fun y _ ↦ hq y) hreg hdim')
  rw [Homeomorph.coe_pullbackDiffeomorph] at hi
  have hi' := isImmersionOfComplement_isLocalDiffeomorphAt_comp
    (fun y : P ↦ isLocalDiffeomorph_subtype_val (I := I) (n := n) (U := V) (e y).1) hi
  refine ⟨V, hzV, inferInstance, inferInstance, hi'.isImmersion, ?_⟩
  exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

/-- **The constant-rank level theorem.** If a map has rank `r` on an open neighbourhood of its
entire fibre, that fibre, with its subspace topology, admits an embedded `C^n` manifold structure
of dimension `dim M - r`, whose tangent image is `ker df`. Empty fibres are allowed. No
Hausdorffness or countability is needed, and the target model may be infinite-dimensional. -/
theorem exists_constantRankFiber_smoothEmbedding
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hlevel : ∀ x, f x = c → x ∈ U) (hrank : ∀ y ∈ U, mfderivRank I J f y = r) :
    ∃ a : ChartedSpace (Fin (finrank 𝕜 E - r) → 𝕜) {x : M // f x = c},
      letI := a
      IsManifold 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) n {x : M // f x = c} ∧
      Manifold.IsSmoothEmbedding 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) I n
        (Subtype.val : {x : M // f x = c} → M) ∧
      ∀ z : {x : M // f x = c},
        (mfderiv 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) I Subtype.val z).range =
          (mfderiv I J f z.1).ker := by
  classical
  let P := {x : M // f x = c}
  let K := 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜)
  have hlocal (z : P) := exists_levelPatch_of_constantRank hf hU hn hrank z (hlevel z z.2)
  choose V hV a hman hemb using hlocal
  let W (z : P) : TopologicalSpace.Opens P :=
    ⟨{y | y.1 ∈ V z}, (V z).isOpen.preimage continuous_subtype_val⟩
  let (z : P) : ChartedSpace (Fin (finrank 𝕜 E - r) → 𝕜) (W z) := a z
  have (z : P) : IsManifold K n (W z) := hman z
  let ι (z : P) : W z → P := Subtype.val
  have hopen (z : P) : IsOpenEmbedding (ι z) := (W z).isOpen.isOpenEmbedding_subtypeVal
  have hcover (z : P) : ∃ a q, ι a q = z := ⟨z, ⟨z, hV z⟩, rfl⟩
  have hdeck := exists_contMDiffAt_transition_of_isImmersion hopen
    (g := (Subtype.val : P → M)) (fun z ↦ (hemb z).isImmersion)
  let := chartedSpaceOfIsOpenEmbedding (H := Fin (finrank 𝕜 E - r) → 𝕜) hopen hcover
  have := isManifold_chartedSpaceOfIsOpenEmbedding hopen hcover hdeck
  have hinc : Manifold.IsImmersion K I n (Subtype.val : P → M) := by
    apply isImmersion_iff_forall_isImmersionAt.2
    intro z
    obtain ⟨a, q, rfl⟩ := hcover z
    exact (isImmersionAt_comp_isLocalDiffeomorphAt_iff
      (isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding hopen hcover hdeck a q)).1
      ((hemb a).isImmersion.isImmersionAt q)
  refine ⟨inferInstance, inferInstance, ⟨hinc, Topology.IsEmbedding.subtypeVal⟩, fun z ↦ ?_⟩
  -- Inclusion into the kernel follows by differentiating the level equation. Injectivity
  -- of the inclusion derivative and rank-nullity give equality of dimensions.
  apply Submodule.eq_of_le_of_finrank_eq
    (range_mfderiv_le_ker_mfderiv_of_eventually_eq (.of_forall fun y : P ↦ y.2))
  rw [LinearMap.finrank_range_of_inj (hinc.mfderiv_injective
    (ne_of_gt (zero_lt_one.trans_le hn)) z), finrank_tangentSpace, finrank_fin_fun]
  have hdim := finrank_ker_mfderiv_add_mfderivRank (I := I) (J := J) (f := f) (x := z.1)
  rw [hrank z.1 (hlevel z z.2)] at hdim
  omega

/-- A fixed atlas on a constant-rank fibre, retaining its subspace topology. It is not a global
instance. Use `isManifold_constantRankFiber`, `isSmoothEmbedding_coe_constantRankFiber` and
`range_mfderiv_coe_constantRankFiber` for its geometric properties. -/
@[instance_reducible]
noncomputable def constantRankFiberChartedSpace
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hlevel : ∀ x, f x = c → x ∈ U) (hrank : ∀ y ∈ U, mfderivRank I J f y = r) :
    ChartedSpace (Fin (finrank 𝕜 E - r) → 𝕜) {x : M // f x = c} :=
  (exists_constantRankFiber_smoothEmbedding hf hU hn hlevel hrank).choose

/-- The constant-rank fibre with its chosen atlas is a `C^n` manifold. -/
theorem isManifold_constantRankFiber
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hlevel : ∀ x, f x = c → x ∈ U) (hrank : ∀ y ∈ U, mfderivRank I J f y = r) :
    letI := constantRankFiberChartedSpace hf hU hn hlevel hrank
    IsManifold 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) n {x : M // f x = c} :=
  (exists_constantRankFiber_smoothEmbedding hf hU hn hlevel hrank).choose_spec.1

/-- The inclusion of a constant-rank fibre with its chosen atlas is a smooth embedding. In
particular, the ambient smoothness of a map into the fibre implies its intrinsic smoothness. -/
theorem isSmoothEmbedding_coe_constantRankFiber
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hlevel : ∀ x, f x = c → x ∈ U) (hrank : ∀ y ∈ U, mfderivRank I J f y = r) :
    letI := constantRankFiberChartedSpace hf hU hn hlevel hrank
    Manifold.IsSmoothEmbedding 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) I n
      (Subtype.val : {x : M // f x = c} → M) :=
  (exists_constantRankFiber_smoothEmbedding hf hU hn hlevel hrank).choose_spec.2.1

/-- The tangent image of a constant-rank fibre is the kernel of the ambient derivative. -/
theorem range_mfderiv_coe_constantRankFiber
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hn : 1 ≤ n)
    (hlevel : ∀ x, f x = c → x ∈ U) (hrank : ∀ y ∈ U, mfderivRank I J f y = r) :
    letI := constantRankFiberChartedSpace hf hU hn hlevel hrank
    ∀ z : {x : M // f x = c},
      (mfderiv 𝓘(𝕜, Fin (finrank 𝕜 E - r) → 𝕜) I Subtype.val z).range =
        (mfderiv I J f z.1).ker :=
  (exists_constantRankFiber_smoothEmbedding hf hU hn hlevel hrank).choose_spec.2.2

end TauCeti
