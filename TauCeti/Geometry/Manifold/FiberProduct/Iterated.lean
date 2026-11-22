/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
import TauCeti.LinearAlgebra.Submodule.FiberProduct

/-!
# Transversality of iterated fibre products

Let `f : X → B`, `g : Y → B`, `h : Y → C` and `k : Z → C` be smooth maps, with `f` and `g`
transverse and `h` and `k` transverse. Then `X ×_B Y` and `Y ×_C Z` are manifolds
(`TauCeti.transverseFiberProductChartedSpace`), and the matching triples `(x, y, z)`, with
`f x = g y` and `h y = k z`, can be grouped in two ways:

* as `(X ×_B Y) ×_C Z`, the fibre product of `(x, y) ↦ h y` and `k`;
* as `X ×_B (Y ×_C Z)`, the fibre product of `f` and `(y, z) ↦ g y`.

This file shows that the first of these fibre products is transverse exactly when the second is
(`TauCeti.transverse_fiberProduct_assoc_iff`). Both conditions say that
`(u, v, w) ↦ (df u - dg v, dh v - dk w)` is onto `T_b B × T_c C` at every matching triple. The
differential of the projection `X ×_B Y → Y` has range `dg⁻¹(range df)`
(`TauCeti.range_mfderiv_snd_transverseFiberProduct`), so the differential of `(x, y) ↦ h y` has
range `dh (dg⁻¹(range df))`; likewise the differential of `(y, z) ↦ g y` on `Y ×_C Z` has range
`dg (dh⁻¹(range dk))` (`TauCeti.range_mfderiv_fst_transverseFiberProduct`). So the comparison is
the linear statement `LinearMap.map_comap_range_sup_range_eq_top_iff`.

When both groupings are transverse, both iterated fibre products are manifolds, and the
associator `TauCeti.fiberProductAssocDiffeomorph` identifies them. This is the setting of the
associativity of transverse composition of correspondences.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Theorem 6.30
  (transverse preimages).
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {EX HX X EY HY Y EZ HZ Z EB HB B EC HC C : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ] [TopologicalSpace HZ]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC] [TopologicalSpace HC]
  {IX : ModelWithCorners ℝ EX HX} {IY : ModelWithCorners ℝ EY HY}
  {IZ : ModelWithCorners ℝ EZ HZ} {IB : ModelWithCorners ℝ EB HB}
  {IC : ModelWithCorners ℝ EC HC}
  [IX.Boundaryless] [IY.Boundaryless] [IZ.Boundaryless] [IB.Boundaryless] [IC.Boundaryless]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace Z] [ChartedSpace HZ Z] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace C] [ChartedSpace HC C]
  {n : ℕ∞ω} [IsManifold IX n X] [IsManifold IY n Y] [IsManifold IZ n Z]
  [IsManifold IB n B] [IsManifold IC n C]
  {f : X → B} {g : Y → B} {h : Y → C} {k : Z → C}

/-- The model of the transverse fibre product `X ×_B Y`. -/
local notation "KXY" => 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EB) → ℝ)

/-- The model of the transverse fibre product `Y ×_C Z`. -/
local notation "KYZ" => 𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EZ - finrank ℝ EC) → ℝ)

/-- **The transversality of an iterated fibre product does not depend on the grouping.** Let
`f : X → B` and `g : Y → B` be transverse, and let `h : Y → C` and `k : Z → C` be transverse.
Then `(x, y) ↦ h y` on the fibre product `X ×_B Y` is transverse to `k` exactly when `f` is
transverse to `(y, z) ↦ g y` on the fibre product `Y ×_C Z`. -/
theorem transverse_fiberProduct_assoc_iff (hn : 1 ≤ n) (hf : ContMDiff IX IB n f)
    (hg : ContMDiff IY IB n g) (hh : ContMDiff IY IC n h) (hk : ContMDiff IZ IC n k)
    (hfg : ∀ p : X × Y, f p.1 = g p.2 →
      (mfderiv IX IB f p.1).range ⊔
        (((tangentSpaceCast IB (g p.2) (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IB g p.2)).range = ⊤)
    (hhk : ∀ p : Y × Z, h p.1 = k p.2 →
      (mfderiv IY IC h p.1).range ⊔
        (((tangentSpaceCast IC (k p.2) (h p.1)).toContinuousLinearMap).comp
          (mfderiv IZ IC k p.2)).range = ⊤) :
    letI := transverseFiberProductChartedSpace hn hf hg hfg
    letI := transverseFiberProductChartedSpace hn hh hk hhk
    (∀ p : {p : X × Y // f p.1 = g p.2} × Z, h p.1.val.2 = k p.2 →
      (mfderiv KXY IC (fun q : {p : X × Y // f p.1 = g p.2} ↦ h q.val.2) p.1).range ⊔
        (((tangentSpaceCast IC (k p.2) (h p.1.val.2)).toContinuousLinearMap).comp
          (mfderiv IZ IC k p.2)).range = ⊤) ↔
    (∀ p : X × {p : Y × Z // h p.1 = k p.2}, f p.1 = g p.2.val.1 →
      (mfderiv IX IB f p.1).range ⊔
        (((tangentSpaceCast IB (g p.2.val.1) (f p.1)).toContinuousLinearMap).comp
          (mfderiv KYZ IB (fun q : {p : Y × Z // h p.1 = k p.2} ↦ g q.val.1) p.2)).range = ⊤) := by
  let := transverseFiberProductChartedSpace hn hf hg hfg
  let := transverseFiberProductChartedSpace hn hh hk hhk
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  -- At a matching triple `(x, y, z)`, both conditions are the two sides of the linear statement
  -- for `a = df`, `b = dg`, `c = dh` and `d = dk`.
  have key (x : X) (y : Y) (z : Z) (hxy : f x = g y) (hyz : h y = k z) :
      (mfderiv KXY IC (fun q : {p : X × Y // f p.1 = g p.2} ↦ h q.val.2) ⟨(x, y), hxy⟩).range ⊔
          (((tangentSpaceCast IC (k z) (h y)).toContinuousLinearMap).comp
            (mfderiv IZ IC k z)).range = ⊤ ↔
        (mfderiv IX IB f x).range ⊔
          (((tangentSpaceCast IB (g y) (f x)).toContinuousLinearMap).comp
            (mfderiv KYZ IB (fun q : {p : Y × Z // h p.1 = k p.2} ↦ g q.val.1)
              ⟨(y, z), hyz⟩)).range = ⊤ := by
    -- The two outer maps factor through the projections of the inner fibre products.
    have hXY : mfderiv KXY IC (fun q : {p : X × Y // f p.1 = g p.2} ↦ h q.val.2) ⟨(x, y), hxy⟩ =
        (mfderiv IY IC h y).comp
          (mfderiv KXY IY (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) ⟨(x, y), hxy⟩) :=
      mfderiv_comp _ (hh.mdifferentiable hn0 y)
        ((isSmoothEmbedding_coe_transverseFiberProduct hn hf hg hfg).contMDiff.mdifferentiable
          hn0 _).snd
    have hYZ : mfderiv KYZ IB (fun q : {p : Y × Z // h p.1 = k p.2} ↦ g q.val.1) ⟨(y, z), hyz⟩ =
        (mfderiv IY IB g y).comp
          (mfderiv KYZ IY (fun q : {p : Y × Z // h p.1 = k p.2} ↦ q.val.1) ⟨(y, z), hyz⟩) :=
      mfderiv_comp _ (hg.mdifferentiable hn0 y)
        ((isSmoothEmbedding_coe_transverseFiberProduct hn hh hk hhk).contMDiff.mdifferentiable
          hn0 _).fst
    rw [hXY, ContinuousLinearMap.toLinearMap_comp _
        (mfderiv KXY IY (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) ⟨(x, y), hxy⟩),
      LinearMap.range_comp, range_mfderiv_snd_transverseFiberProduct hn hf hg hfg, hYZ,
      ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.toLinearMap_comp _
        (mfderiv KYZ IY (fun q : {p : Y × Z // h p.1 = k p.2} ↦ q.val.1) ⟨(y, z), hyz⟩),
      LinearMap.range_comp, range_mfderiv_fst_transverseFiberProduct hn hh hk hhk]
    exact LinearMap.map_comap_range_sup_range_eq_top_iff (hfg (x, y) hxy) (hhk (y, z) hyz)
  constructor
  · rintro hL ⟨x, ⟨⟨y, z⟩, hyz⟩⟩ hxy
    exact (key x y z hxy hyz).1 (hL (⟨(x, y), hxy⟩, z) hyz)
  · rintro hR ⟨⟨⟨x, y⟩, hxy⟩, z⟩ hyz
    exact (key x y z hxy hyz).2 (hR (x, ⟨(y, z), hyz⟩) hxy)

end TauCeti
