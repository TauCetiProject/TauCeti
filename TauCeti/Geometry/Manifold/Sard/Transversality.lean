/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.Sard.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.LinearAlgebra.Submodule.FiberProduct

/-!
# Parametric transversality

Let `M`, `S`, `N` and `Z` be manifolds without boundary, let `F : M × S → N` be a smooth family
of maps `F (·, s) : M → N` parametrized by `S`, and let `g : Z → N` be a smooth map that is a
topological embedding. If `F` is transverse to `g`, then for all parameters `s` outside a null set
of `S` (`TauCeti.IsNullSet`), the slice `F (·, s)` is transverse to `g`; in particular such
parameters are dense. This is the parametric transversality theorem, in the boundaryless case.
Transversality of maps `f : X → N` and `g : Z → N` is written, as for the transverse fibre
products of `TauCeti.transverseFiberProductChartedSpace`, as the equation
`range (df) ⊔ range (dg) = ⊤` at every pair of points with `f x = g z`.

The bad parameters are critical values of the projection to `S` of the transverse fibre product
`{((x, s), z) // F (x, s) = g z}`: at a point of the fibre product, the slice `F (·, s)` is
transverse to `g` exactly when the point is a regular point of this projection
(`TauCeti.isRegularPoint_snd_fst_transverseFiberProduct_iff`). Sard's theorem for the projection,
whose source has dimension `dim M + dim S + dim Z - dim N`, then shows that the bad parameters are
null. No relation between this dimension and `dim S` is needed, so the unequal-dimensional Sard
theorem `ContMDiff.isNullSet_image_criticalPoints` is used, with regularity `k > dim M + dim Z -
dim N`, `k ≥ 1`.

Since `g` is an embedding, the fibre product is a subspace of `M × S`. The source `M` is assumed
Lindelöf, and no countability assumption is put on `S` or `Z`: nullity in `S` is local, and over
a chart domain of `S` the fibre product is second countable. An injective immersion `g` does not
suffice: for the discrete line `Z = ℝ_δ` with the identity map to `N = ℝ`, the point `M` and
`F (x, s) = s`, the family `F` is a submersion, but no slice is transverse to `g`. Neither can the
Lindelöf hypothesis on `M` be dropped: for the discrete line `M = ℝ_δ`, `S = N = ℝ`, the point `Z`
mapping to `0` and `F (m, s) = s - m`, every parameter is bad.

All four manifolds `M`, `S`, `N` and `Z` are assumed boundaryless. Lee's version of the theorem
also allows `M` to have boundary; that case is not covered here.

For maps between normed spaces, the corresponding statement is
`TauCeti.addHaar_setOf_not_isRegularIncidenceParameter_eq_zero`.

## Main results

* `TauCeti.isRegularPoint_snd_fst_transverseFiberProduct_iff`: a point of the fibre product is a
  regular point of its projection to `S` exactly when the slice through it is transverse.
* `ContMDiff.isNullSet_setOf_exists_not_transverse`: the parameters whose slice is not transverse
  to `g` form a null set.
* `ContMDiff.dense_setOf_forall_transverse`: the parameters whose slice is transverse to `g` are
  dense.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.35 (the parametric transversality theorem).
-/

public section

open Function Module Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {EM HM M ES HS S EN HN N EZ HZ Z : Type*}
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IM : ModelWithCorners ℝ EM HM} {IS : ModelWithCorners ℝ ES HS}
  {IN : ModelWithCorners ℝ EN HN} {IZ : ModelWithCorners ℝ EZ HZ}
  [TopologicalSpace M] [ChartedSpace HM M] [TopologicalSpace S] [ChartedSpace HS S]
  [TopologicalSpace N] [ChartedSpace HN N] [TopologicalSpace Z] [ChartedSpace HZ Z]
  [IM.Boundaryless] [IS.Boundaryless] [IN.Boundaryless] [IZ.Boundaryless]
  [FiniteDimensional ℝ EM] [FiniteDimensional ℝ ES] [FiniteDimensional ℝ EN]
  [FiniteDimensional ℝ EZ]
  {n : ℕ∞ω} [IsManifold IM n M] [IsManifold IS n S] [IsManifold IN n N] [IsManifold IZ n Z]
  {F : M × S → N} {g : Z → N}

/-- **Slices of a transverse family.** Let `F : M × S → N` be transverse to `g : Z → N`. A point
`((x, s), z)` of their transverse fibre product is a regular point of the projection to `S`
exactly when the slice `F (·, s)` is transverse to `g` at `(x, z)`. -/
theorem isRegularPoint_snd_fst_transverseFiberProduct_iff (hn : 1 ≤ n)
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g)
    (htrans : ∀ p : (M × S) × Z, F p.1 = g p.2 →
      (mfderiv (IM.prod IS) IN F p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (F p.1)).toContinuousLinearMap).comp
          (mfderiv IZ IN g p.2)).range = ⊤)
    (p : {p : (M × S) × Z // F p.1 = g p.2}) :
    letI := transverseFiberProductChartedSpace hn hF hg htrans
    IsRegularPoint 𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) IS
        (fun q : {p : (M × S) × Z // F p.1 = g p.2} ↦ q.val.1.2) p ↔
      (mfderiv IM IN (fun x ↦ F (x, p.val.1.2)) p.val.1.1).range ⊔
        (((tangentSpaceCast IN (g p.val.2) (F (p.val.1.1, p.val.1.2))).toContinuousLinearMap).comp
          (mfderiv IZ IN g p.val.2)).range = ⊤ := by
  let := transverseFiberProductChartedSpace hn hF hg htrans
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  obtain ⟨⟨⟨x, s⟩, z⟩, hp⟩ := p
  -- The projection to `S` is the second component of the projection to `M × S`.
  have hd : mfderiv 𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) IS
      (fun q : {p : (M × S) × Z // F p.1 = g p.2} ↦ q.val.1.2) ⟨((x, s), z), hp⟩ =
      (ContinuousLinearMap.snd ℝ (TangentSpace IM x) (TangentSpace IS s)).comp
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) (IM.prod IS)
          (fun q : {p : (M × S) × Z // F p.1 = g p.2} ↦ q.val.1) ⟨((x, s), z), hp⟩) := by
    have hfst := ((isSmoothEmbedding_coe_transverseFiberProduct hn hF hg htrans).contMDiff.fst
      ⟨((x, s), z), hp⟩).mdifferentiableAt hn0
    have h := mfderiv_comp (⟨((x, s), z), hp⟩ : {p : (M × S) × Z // F p.1 = g p.2})
      mdifferentiableAt_snd hfst
    simp only [Function.comp_def, mfderiv_snd] at h
    exact h
  -- The differential of the slice is the differential of `F` on the first factor.
  have hslice : mfderiv IM IN (fun x' ↦ F (x', s)) x = (mfderiv (IM.prod IS) IN F (x, s)).comp
      (ContinuousLinearMap.inl ℝ (TangentSpace IM x) (TangentSpace IS s)) := by
    have h := mfderiv_comp x ((hF (x, s)).mdifferentiableAt hn0)
      (mdifferentiableAt_id.prodMk (mdifferentiableAt_const (c := s)))
    simp only [Function.comp_def, id_eq, mfderiv_prod_left] at h
    exact h
  have hrange := range_mfderiv_fst_transverseFiberProduct hn hF hg htrans ⟨((x, s), z), hp⟩
  -- Both conditions are transversality conditions of the iterated linear fibre product of
  -- `dg`, `dF`, the second projection `T M × T S → T S` and `0`, in its two groupings.
  -- `A` is `dF` with its source written as a product, so that it composes with `snd`.
  let A : TangentSpace IM x × TangentSpace IS s →L[ℝ] TangentSpace IN (F (x, s)) :=
    mfderiv (IM.prod IS) IN F (x, s)
  have key := LinearMap.map_comap_range_sup_range_eq_top_iff (R := ℝ)
    (a := (((tangentSpaceCast IN (g z) (F (x, s))).toContinuousLinearMap).comp
      (mfderiv IZ IN g z) : TangentSpace IZ z →ₗ[ℝ] TangentSpace IN (F (x, s))))
    (b := (A : TangentSpace IM x × TangentSpace IS s →ₗ[ℝ] TangentSpace IN (F (x, s))))
    (c := LinearMap.snd ℝ (TangentSpace IM x) (TangentSpace IS s))
    (d := (0 : TangentSpace IS s →ₗ[ℝ] TangentSpace IS s))
    (by rw [sup_comm]; exact htrans ((x, s), z) hp) (by rw [Submodule.range_snd, top_sup_eq])
  rw [LinearMap.range_zero, sup_bot_eq, Submodule.comap_bot, LinearMap.ker_snd,
    ← LinearMap.range_comp, sup_comm] at key
  dsimp only at hrange ⊢
  rw [isRegularPoint_iff, hd, hslice]
  refine Iff.trans ?_ key
  -- The tangent image of the projection to `M × S` is `dF⁻¹(range dg)`.
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.range_eq_top]
  exact Eq.congr_left ((LinearMap.range_comp _ _).trans (congrArg _ hrange))

/-- **The parametric transversality theorem.** Let `M`, `S`, `N` and `Z` be manifolds without
boundary, and let `F : M × S → N` be a `C^n` family of maps, transverse to a `C^n` map
`g : Z → N` that is a topological embedding, where `M` is Lindelöf and
`n > dim M + dim Z - dim N`, `n ≥ 1`. Then the parameters `s` for which the slice `F (·, s)`
is not transverse to `g` form a null set of `S`. -/
theorem _root_.ContMDiff.isNullSet_setOf_exists_not_transverse [LindelofSpace M]
    [MeasurableSpace ES] [BorelSpace ES]
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g) (hgi : IsEmbedding g)
    (hk : ((finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n)
    (htrans : ∀ p : (M × S) × Z, F p.1 = g p.2 →
      (mfderiv (IM.prod IS) IN F p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (F p.1)).toContinuousLinearMap).comp
          (mfderiv IZ IN g p.2)).range = ⊤) :
    IsNullSet IS {s | ∃ p : M × Z, F (p.1, s) = g p.2 ∧
      (mfderiv IM IN (fun x ↦ F (x, s)) p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (F (p.1, s))).toContinuousLinearMap).comp
          (mfderiv IZ IN g p.2)).range ≠ ⊤} := by
  have hn : 1 ≤ n := le_trans (by exact_mod_cast Nat.le_add_left 1 _) hk
  let := transverseFiberProductChartedSpace hn hF hg htrans
  have := isManifold_transverseFiberProduct hn hF hg htrans
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hF hg htrans
  have := IM.secondCountableTopology
  have := IS.secondCountableTopology
  have := ChartedSpace.secondCountable_of_lindelof HM M
  -- Since `g` is an embedding, the fibre product is a subspace of `M × S`.
  have hP : IsEmbedding fun p : {p : (M × S) × Z // F p.1 = g p.2} ↦ p.val.1 :=
    IsEmbedding.subtypeVal.comp (TopCat.pullbackHomeoPreimage F hF.continuous g hgi).isEmbedding
  rw [isNullSet_iff_forall_exists_nhds]
  rintro s₀ -
  refine ⟨(chartAt HS s₀).source, chart_source_mem_nhds HS s₀, ?_⟩
  -- Over the chart domain `U` at `s₀`, the fibre product is second countable.
  have : SecondCountableTopology (chartAt HS s₀).source :=
    (chartAt HS s₀).secondCountableTopology_source
  let V : Opens {p : (M × S) × Z // F p.1 = g p.2} :=
    ⟨{p | p.val.1.2 ∈ (chartAt HS s₀).source}, (chartAt HS s₀).open_source.preimage
      (continuous_snd.comp hP.continuous)⟩
  have : SecondCountableTopology V := by
    have hV : IsEmbedding fun q : V ↦ ((q.val.val.1.1, ⟨q.val.val.1.2, q.property⟩) :
        M × (chartAt HS s₀).source) :=
      IsEmbedding.of_comp (by fun_prop) (continuous_id.prodMap continuous_subtypeVal)
        (hP.comp IsEmbedding.subtypeVal)
    exact hV.secondCountableTopology
  -- Sard's theorem for the projection of this open piece of the fibre product to `S`.
  have hπ : ContMDiff _ IS n fun q : V ↦ q.val.val.1.2 :=
    hemb.contMDiff.fst.snd.comp contMDiff_subtypeVal
  have hdim : ((finrank ℝ (Fin (finrank ℝ (EM × ES) + finrank ℝ EZ - finrank ℝ EN) → ℝ) -
      finrank ℝ ES + 1 : ℕ) : ℕ∞ω) ≤ n := by
    refine le_trans (le_of_eq ?_) hk
    simp only [finrank_fin_fun, finrank_prod]
    congr 1
    omega
  have hnull := hπ.isNullSet_image_criticalPoints hdim
  refine hnull.mono ?_
  rintro s ⟨⟨⟨x, z⟩, hxz, hnt⟩, hsU⟩
  refine ⟨⟨⟨((x, s), z), hxz⟩, hsU⟩, fun hreg ↦ hnt ?_, rfl⟩
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hreg' := IsRegularPoint.of_comp (g := Subtype.val)
    (f := fun q : {p : (M × S) × Z // F p.1 = g p.2} ↦ q.val.1.2) hreg
    ((hemb.contMDiff.fst.snd _).mdifferentiableAt hn0)
    ((contMDiff_subtypeVal _).mdifferentiableAt hn0)
  exact (isRegularPoint_snd_fst_transverseFiberProduct_iff hn hF hg htrans
    ⟨((x, s), z), hxz⟩).1 hreg'

/-- **Generic slices are transverse.** Let `M`, `S`, `N` and `Z` be manifolds without boundary,
and let `F : M × S → N` be a `C^n` family of maps, transverse to a `C^n` map `g : Z → N` that
is a topological embedding, where `M` is Lindelöf and `n > dim M + dim Z - dim N`, `n ≥ 1`.
Then the parameters `s` for which the slice `F (·, s)` is transverse to `g` are dense in `S`. -/
theorem _root_.ContMDiff.dense_setOf_forall_transverse [LindelofSpace M]
    (hF : ContMDiff (IM.prod IS) IN n F) (hg : ContMDiff IZ IN n g) (hgi : IsEmbedding g)
    (hk : ((finrank ℝ EM + finrank ℝ EZ - finrank ℝ EN + 1 : ℕ) : ℕ∞ω) ≤ n)
    (htrans : ∀ p : (M × S) × Z, F p.1 = g p.2 →
      (mfderiv (IM.prod IS) IN F p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (F p.1)).toContinuousLinearMap).comp
          (mfderiv IZ IN g p.2)).range = ⊤) :
    Dense {s | ∀ p : M × Z, F (p.1, s) = g p.2 →
      (mfderiv IM IN (fun x ↦ F (x, s)) p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (F (p.1, s))).toContinuousLinearMap).comp
          (mfderiv IZ IN g p.2)).range = ⊤} := by
  borelize ES
  convert (hF.isNullSet_setOf_exists_not_transverse hg hgi hk htrans).dense_compl using 1
  ext s
  simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and, not_not]

end TauCeti
