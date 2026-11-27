/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Complex.Order

/-!
# Finite partitions of test functions

On a finite-dimensional Hausdorff σ-compact manifold `G`, Mathlib's smooth partitions of unity
give, for a compact set `K` covered by finitely many open sets `U i`, nonnegative test functions
`χ i` supported in `U i` that sum to one on `K`. Multiplying by them splits a test function
whose support closure is covered by the `U i` into a finite sum of test functions supported in
the `U i`; with charts as the `U i`, this reduces statements about test functions on `G` to
test functions supported in chart domains.

## Main results

* `TauCeti.LieTestFunction.exists_sum_eq_one_of_isCompact`: a finite smooth partition of a
  compact set by nonnegative test functions subordinate to an open cover.
* `TauCeti.LieTestFunction.exists_sum_eq_of_tsupport_subset_iUnion`: a test function is a finite
  sum of test functions supported in the members of a finite open cover of its support closure.
-/

public section

open Function Set
open scoped ContDiff Manifold ComplexOrder

namespace TauCeti

namespace LieTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [IsManifold I ∞ G] [T2Space G]
  [SigmaCompactSpace G] {ι : Type*} [Fintype ι]

/-- A compact set `K` covered by finitely many open sets `U i` has a smooth partition of unity by
nonnegative test functions `χ i` with `tsupport (χ i) ⊆ U i` and `∑ i, χ i = 1` on `K`. -/
theorem exists_sum_eq_one_of_isCompact {K : Set G} (hK : IsCompact K) (U : ι → Set G)
    (hU : ∀ i, IsOpen (U i)) (hKU : K ⊆ ⋃ i, U i) :
    ∃ χ : ι → LieTestFunction I G, (∀ i x, 0 ≤ χ i x) ∧ (∀ i, tsupport (χ i) ⊆ U i) ∧
      ∀ x ∈ K, ∑ i, χ i x = 1 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace H G
  obtain ⟨V, hVo, hKV, hVc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hK.isClosed
    (fun i ↦ U i ∩ V) (fun i ↦ (hU i).inter hVo) fun x hx ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hKU hx)
      exact mem_iUnion.2 ⟨i, hi, hKV hx⟩
  have hsupp (i : ι) : tsupport (fun x ↦ (f i x : ℂ)) ⊆ U i ∩ V :=
    (tsupport_comp_subset Complex.ofReal_zero (f i)).trans (hf i)
  refine ⟨fun i ↦ ⟨fun x ↦ (f i x : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp (f i).contMDiff,
    hVc.of_isClosed_subset (isClosed_tsupport _)
      ((hsupp i).trans (inter_subset_right.trans subset_closure))⟩,
    fun i x ↦ Complex.zero_le_real.2 (f.nonneg i x),
    fun i ↦ (hsupp i).trans inter_subset_left, fun x hx ↦ ?_⟩
  -- `χ i x` is `(f i x : ℂ)` by `coe_mk`; `simp only [coe_mk]` cannot rewrite under `∑ i`, as
  -- the proof fields of `χ i` depend on the summation index.
  have hsum : ∑ i, (f i x : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype, f.sum_eq_one hx, Complex.ofReal_one]
  exact hsum

/-- A test function `a` whose support closure is covered by finitely many open sets `U i` is a sum
of test functions `b i` with `tsupport (b i) ⊆ U i`. -/
theorem exists_sum_eq_of_tsupport_subset_iUnion (a : LieTestFunction I G) (U : ι → Set G)
    (hU : ∀ i, IsOpen (U i)) (ha : tsupport a ⊆ ⋃ i, U i) :
    ∃ b : ι → LieTestFunction I G, (∀ i, tsupport (b i) ⊆ U i) ∧ ∑ i, b i = a := by
  obtain ⟨χ, -, hχU, hχ⟩ := exists_sum_eq_one_of_isCompact (I := I) a.hasCompactSupport U hU ha
  refine ⟨fun i ↦ ⟨fun x ↦ χ i x * a x,
    contDiff_mul.contMDiff.comp ((χ i).contMDiff.prodMk_space a.contMDiff),
    a.hasCompactSupport.mul_left⟩, fun i ↦ (tsupport_mul_subset_left).trans (hχU i), ?_⟩
  ext x
  simp only [_root_.sum_apply, coe_mk, ← Finset.sum_mul]
  by_cases hx : x ∈ tsupport a
  · rw [hχ x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

end LieTestFunction

end TauCeti
