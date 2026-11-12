/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The preferred charts of the total space of a fibre bundle

For a fibre bundle `V` with model fibre `F` over a manifold `B` modelled on `IB`, the total space
carries the charts `(trivializationAt F V b) ≫ (chartAt HB b × id)`, modelled on
`IB.prod 𝓘(𝕜, F)`. Over the base set of the trivialization at their base point these charts are
computed explicitly (`Bundle.mem_extChartAt_source_iff`, `Bundle.extChartAt_apply_of_mem_baseSet`,
`Bundle.extChartAt_symm_apply_of_mem_baseSet` and
`Bundle.extChartAt_symm_apply_extChartAt_of_mem_baseSet`). For a vector bundle, the preferred
chart at a zero vector sends the zero vectors over that base set to the zero fibre coordinate
(`Bundle.extChartAt_zeroSection_of_mem_baseSet`, `Bundle.extChartAt_zeroSection_self`).
-/

public section

open Bundle Set
open scoped Manifold

namespace Bundle

variable {𝕜 B F EB HB : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F V]

/-- A point of the total space lies in the source of the preferred chart at `p` exactly when its
base point lies in the base set of the trivialization at `p.proj` and in the source of the chart of
the base at `p.proj`. -/
theorem mem_extChartAt_source_iff (p x : TotalSpace F V) :
    x ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) p).source ↔
      x.proj ∈ (trivializationAt F V p.proj).baseSet ∧ x.proj ∈ (extChartAt IB p.proj).source := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_source, mem_inter_iff, mem_preimage, PartialEquiv.prod_source,
    PartialEquiv.refl_source, mem_prod, mem_univ, and_true, Trivialization.mem_source]
  refine and_congr_right fun h ↦ ?_
  simp [Trivialization.coe_fst' _ h]

/-- In the preferred chart at `p`, a point over the base set of the trivialization at `p.proj` has
coordinates its base point in the chart of the base and its fibre coordinate in that
trivialization. -/
theorem extChartAt_apply_of_mem_baseSet (p : TotalSpace F V) {x : TotalSpace F V}
    (hx : x.proj ∈ (trivializationAt F V p.proj).baseSet) :
    extChartAt (IB.prod 𝓘(𝕜, F)) p x =
      (extChartAt IB p.proj x.proj, (trivializationAt F V p.proj x).2) := by
  rw [FiberBundle.extChartAt]
  simp [Trivialization.coe_fst' _ hx]

/-- The inverse of the preferred chart at `p` sends `(y, w)`, with `y` over the base set of the
trivialization at `p.proj`, to the vector over `(extChartAt IB p.proj).symm y` with fibre
coordinate `w` in that trivialization. -/
theorem extChartAt_symm_apply_of_mem_baseSet [∀ x, Nonempty (V x)] (p : TotalSpace F V) {y : EB}
    (hy : (extChartAt IB p.proj).symm y ∈ (trivializationAt F V p.proj).baseSet) (w : F) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) p).symm (y, w) =
      ⟨(extChartAt IB p.proj).symm y,
        (trivializationAt F V p.proj).symm ((extChartAt IB p.proj).symm y) w⟩ := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.coe_trans,
    PartialEquiv.prod_symm, PartialEquiv.refl_symm, Function.comp_apply, PartialEquiv.prod_coe,
    PartialEquiv.refl_coe, id_eq]
  rw [OpenPartialHomeomorph.coe_toPartialEquiv_symm, Trivialization.mk_symm _ hy w]

/-- The inverse of the preferred chart at `p` sends `(y, w)`, with `y` the coordinate of a base
point `b` in the base set of the trivialization at `p.proj` and in the source of the chart of the
base at `p.proj`, to the vector over `b` with fibre coordinate `w` in that trivialization. -/
theorem extChartAt_symm_apply_extChartAt_of_mem_baseSet [∀ x, Nonempty (V x)] (p : TotalSpace F V)
    {b : B} (hb : b ∈ (trivializationAt F V p.proj).baseSet)
    (hb' : b ∈ (extChartAt IB p.proj).source) (w : F) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) p).symm (extChartAt IB p.proj b, w) =
      ⟨b, (trivializationAt F V p.proj).symm b w⟩ := by
  have h := (extChartAt IB p.proj).left_inv hb'
  rw [extChartAt_symm_apply_of_mem_baseSet p (h.symm ▸ hb), h]

section ZeroSection

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- In the preferred chart of a vector bundle at the zero vector `0_a`, a zero vector `0_b` over the
base set of the trivialization at `a` has coordinates `b` in the chart of the base and `0`. -/
theorem extChartAt_zeroSection_of_mem_baseSet (a : B) {b : B}
    (hb : b ∈ (trivializationAt F V a).baseSet) :
    extChartAt (IB.prod 𝓘(𝕜, F)) (zeroSection F V a) (zeroSection F V b) =
      (extChartAt IB a b, 0) := by
  rw [extChartAt_apply_of_mem_baseSet _ hb, zeroSection_proj, zeroSection_proj,
    (trivializationAt F V a).zeroSection 𝕜 hb]

/-- The preferred chart of a vector bundle at the zero vector `0_a` sends `0_a` to the coordinate
of `a` in the chart of the base and `0`. -/
theorem extChartAt_zeroSection_self (a : B) :
    extChartAt (IB.prod 𝓘(𝕜, F)) (zeroSection F V a) (zeroSection F V a) =
      (extChartAt IB a a, 0) :=
  extChartAt_zeroSection_of_mem_baseSet a (mem_baseSet_trivializationAt F V a)

end ZeroSection

end Bundle
