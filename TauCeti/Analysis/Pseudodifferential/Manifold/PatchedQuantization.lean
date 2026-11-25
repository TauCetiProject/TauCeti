/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization

/-!
# Patched quantization on a manifold

Locally finite sums of chart quantizations are how pseudodifferential operators on a manifold are
built from local symbols (Hörmander III, §18.1; Melrose, §5.3): with a locally finite atlas, a
partition of unity `φᵢ` and cutoffs `ψᵢ` equal to `1` near the supports of the `φᵢ`, the operator
`∑ᵢ φᵢ Op(aᵢ) ψᵢ` is the patched quantization of the local symbols `aᵢ`. Each summand is a
classical pseudodifferential operator
(`OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`); this file
shows that the locally finite sum is one too.

## Main results

* `TauCeti.exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum`: a locally finite sum
  `∑ᵢ Pᵢ` of classical pseudodifferential operators of order `m` is one, provided each `Pᵢ` has
  outputs supported in a compact set `Sᵢ` and only sees its input near `Sᵢ`, with `(Sᵢ)` locally
  finite. Near a compact set only finitely many `Pᵢ` matter.
* `TauCeti.exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum_chartQuantization`:
  the **patched quantization** `∑ᵢ φᵢ Op(aᵢ) ψᵢ` of classical symbols of order `m` in charts `eᵢ`,
  for cutoffs whose supports form a locally finite family on `M`, is a classical
  pseudodifferential operator of order `m`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem
  18.1.17 and Definition 18.1.20.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology

/-! ### Locally finite sums -/

namespace TauCeti

variable {n : ℕ} {m : ℝ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {ι : Type*}
  {P : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {S : ι → Set M}

omit [T2Space M] in
/-- At a point of a compact set `K`, a locally finite sum of operators with outputs supported in
the sets `Sᵢ` is the finite sum over the indices with `Sᵢ` meeting `K`. -/
private theorem finsum_apply_eq_sum (hS : LocallyFinite S)
    (hsupp : ∀ i f, tsupport (P i f) ⊆ S i) {K : Set M} (hK : IsCompact K)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {x : M} (hx : x ∈ K) :
    ∑ᶠ i, P i f x = ∑ i ∈ (hS.finite_nonempty_inter_compact hK).toFinset, P i f x :=
  finsum_eq_sum_of_support_subset _ fun i hi ↦
    (hS.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨x, hsupp i f (subset_tsupport _ hi), hx⟩

/-- A locally finite sum of operators `Pᵢ` with outputs supported in compact sets `Sᵢ`, each only
seeing its input near `Sᵢ`, is properly supported. -/
private theorem isProperlySupported_of_apply_eq_finsum (hS : LocallyFinite S)
    (hSc : ∀ i, IsCompact (S i)) (hsupp : ∀ i f, tsupport (P i f) ⊆ S i)
    (hloc : ∀ i f, (∀ᶠ y in 𝓝ˢ (S i), f y = 0) → P i f = 0)
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hQ : ∀ f x, Q f x = ∑ᶠ i, P i f x) :
    IsProperlySupported Q := by
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  -- Only the finitely many `Pᵢ` with `Sᵢ` meeting `K` see functions supported in `K` or act at
  -- points of `K`, so `K'` is the union of their sets `Sᵢ`.
  set I := (hS.finite_nonempty_inter_compact hK).toFinset
  refine ⟨⋃ i ∈ I, S i, I.isCompact_biUnion fun i _ ↦ hSc i, fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · refine closure_minimal (fun x hx ↦ ?_)
      (I.finite_toSet.isClosed_biUnion fun i _ ↦ (hSc i).isClosed)
    obtain ⟨i, hi⟩ : ∃ i, P i f x ≠ 0 := by
      by_contra! h
      exact hx (by rw [hQ, finsum_eq_zero_of_forall_eq_zero h])
    -- `f` vanishes off `K`, so `Pᵢ f = 0` unless `Sᵢ` meets `K`.
    have hiI : i ∈ I := by
      by_contra hiI
      refine hi ?_
      rw [hloc i f ?_, ContMDiffMap.coe_zero, Pi.zero_apply]
      refine Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhdsSet.2 fun y hy hyK ↦
        hiI ((hS.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨y, hy, hyK⟩)) fun y hy ↦ ?_
      exact image_eq_zero_of_notMem_tsupport fun h ↦ hy (hf h)
    exact mem_biUnion hiI (hsupp i f (subset_tsupport _ hi))
  · rw [hQ, finsum_apply_eq_sum hS hsupp hK f hx]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [hloc i f (hf.filter_mono (nhdsSet_mono (subset_biUnion_of_mem hi))),
      ContMDiffMap.coe_zero, Pi.zero_apply]

/-- **Locally finite sums of pseudodifferential operators.** Let `Pᵢ` be classical
pseudodifferential operators of order `m` on `M`, and `Sᵢ` compact sets forming a locally finite
family, such that the outputs of `Pᵢ` are supported in `Sᵢ` and `Pᵢ f = 0` whenever `f` vanishes
near `Sᵢ`. Then the locally finite sum `f ↦ ∑ᵢ Pᵢ f` is a classical pseudodifferential operator of
order `m`. -/
theorem exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum (hS : LocallyFinite S)
    (hSc : ∀ i, IsCompact (S i)) (hP : ∀ i, P i ∈ classicalPseudodifferentialOperators m)
    (hsupp : ∀ i f, tsupport (P i f) ⊆ S i)
    (hloc : ∀ i f, (∀ᶠ y in 𝓝ˢ (S i), f y = 0) → P i f = 0) :
    ∃ Q ∈ classicalPseudodifferentialOperators m, ∀ f x, Q f x = ∑ᶠ i, P i f x := by
  classical
  have hpt (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      (Function.support fun i ↦ P i f x).Finite :=
    (hS.point_finite x).subset fun i hi ↦ hsupp i f (subset_tsupport _ hi)
  -- The sum of the outputs, a smooth function since the supports are locally finite.
  let F (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    ⟨fun x ↦ ∑ᶠ i, P i f x, contMDiff_finsum (fun i ↦ (P i f).contMDiff)
      (hS.subset fun i ↦ (subset_tsupport _).trans (hsupp i f))⟩
  have hF (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      F f x = ∑ᶠ i, P i f x :=
    congrFun (ContMDiffMap.coeFn_mk _ _) x
  let Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    { toFun := F
      map_add' f g := by
        ext x
        simp only [hF, map_add, ContMDiffMap.coe_add, Pi.add_apply]
        exact finsum_add_distrib (hpt f x) (hpt g x)
      map_smul' c f := by
        ext x
        simp only [hF, map_smul, ContMDiffMap.complex_smul_apply, RingHom.id_apply, ← smul_eq_mul]
        exact (smul_finsum' c (hpt f x)).symm }
  have hQ (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      Q f x = ∑ᶠ i, P i f x :=
    hF f x
  refine ⟨Q, mem_classicalPseudodifferentialOperators_iff.2
    ⟨isProperlySupported_of_apply_eq_finsum hS hSc hsupp hloc hQ, fun e he φ ψ ↦ ?_⟩, hQ⟩
  · -- In a chart, only the finitely many `Pᵢ` with `Sᵢ` meeting `e⁻¹(supp φ)` contribute.
    have hK := e.isCompact_symm_image_tsupport φ
    set I := (hS.finite_nonempty_inter_compact hK).toFinset
    choose a ha using fun i ↦ (mem_classicalPseudodifferentialOperators_iff.1 (hP i)).2 e he φ ψ
    refine ⟨∑ i ∈ I, a i, fun u x ↦ ?_⟩
    rw [ClassicalSymbol.toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left]
    simp only [ha, OpenPartialHomeomorph.complexChartCompression_apply, ← Finset.smul_sum, hQ]
    by_cases hx : φ x = 0
    · simp [hx]
    rw [finsum_apply_eq_sum hS hsupp hK _ ⟨x, subset_tsupport _ hx, rfl⟩]

/-- **Patched quantization.** For charts `eᵢ` of the maximal atlas, classical symbols `aᵢ` of order
`m` and cutoffs `φᵢ`, `ψᵢ` with compact supports in the chart targets, such that the chart preimages
`eᵢ⁻¹(supp φᵢ ∪ supp ψᵢ)` form a locally finite family, the operator
`f ↦ ∑ᵢ (φᵢ · Op(aᵢ) (ψᵢ · (f ∘ eᵢ⁻¹))) ∘ eᵢ` is a classical pseudodifferential operator of order
`m` on `M`. -/
theorem exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum_chartQuantization
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (a : ι → ClassicalSymbol n ℂ ℂ m) (φ ψ : (i : ι) → 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i))) :
    ∃ Q ∈ classicalPseudodifferentialOperators m, ∀ f x,
      Q f x = ∑ᶠ i, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) f x :=
  exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum hS
    (fun i ↦ image_union (e i).symm _ _ ▸
      ((e i).isCompact_symm_image_tsupport (φ i)).union ((e i).isCompact_symm_image_tsupport (ψ i)))
    (fun i ↦
      (e i).chartQuantization_mem_classicalPseudodifferentialOperators (he i) (φ i) (ψ i) (a i))
    (fun i f ↦ ((e i).tsupport_chartQuantization_subset (he i) _ _ _ f).trans
      (image_mono subset_union_left))
    fun i _ hf ↦ (e i).chartQuantization_eq_zero (he i) _ _ _ fun p hp ↦
      hf.self_of_nhdsSet p (image_mono subset_union_right hp)

end TauCeti
