/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.Submersion.Split

import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Submersions and immersions under transverse base change

Any `C^n` submersion (`1 ≤ n`) is transverse to every map in either factor
(`TauCeti.transverse_of_isSubmersion_right`, `TauCeti.transverse_of_isSubmersion_left`), and so is
any map whose differential is surjective at the relevant point
(`TauCeti.transverse_of_surjective_mfderiv_right`).

For transverse maps `f : X → N` and `g : Y → N`, the projections from the equal-value
subtype have tangent images `df⁻¹(range dg)` and `dg⁻¹(range df)`, respectively.
Consequently the projection to `X` is a submersion when `g` is a submersion, and the
projection to `Y` is a submersion when `f` is. Likewise the projection to `X` has injective
differential wherever `g` does, so it is an immersion when `g` is
(`TauCeti.isImmersion_fst_transverseFiberProduct`), and symmetrically for the projection to `Y`
(`TauCeti.isImmersion_snd_transverseFiberProduct`). These results use the previously constructed
transverse fibre-product atlas and its inherited topology, including for an empty fibre
product. No Hausdorff or countability assumptions are needed.

The tangent-image formulas also apply when neither map is a submersion. In them the
explicit `tangentSpaceCast` identifies the two target tangent spaces at a pair with
`f x = g y`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages) and Theorem 4.12 (submersion normal form).
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti

section Transversality

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EX HX X EY HY Y EN HN N : Type*}
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IX : ModelWithCorners 𝕜 EX HX} {IY : ModelWithCorners 𝕜 EY HY}
  {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω}

/-- Every map `f : X → N` is transverse to a map `g : Y → N` in the second factor at a pair `p`
where the differential of `g` is surjective. -/
theorem transverse_of_surjective_mfderiv_right (f : X → N) {g : Y → N} (p : X × Y)
    (hg : Surjective (mfderiv IY IN g p.2)) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  have hr : (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
      (mfderiv IY IN g p.2)).range = ⊤ :=
    LinearMap.range_eq_top.2 ((tangentSpaceCast IN (g p.2) (f p.1)).surjective.comp hg)
  rw [hr, sup_top_eq]

/-- Every map `f : X → N` is transverse to a `C^n` submersion `g : Y → N` (`1 ≤ n`) in the
second factor. -/
theorem transverse_of_isSubmersion_right {f : X → N} {g : Y → N}
    (hn : 1 ≤ n) (hg : Manifold.IsSubmersion IY IN n g) (p : X × Y) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ :=
  transverse_of_surjective_mfderiv_right f p
    (hg.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.2)

/-- Every `C^n` submersion `f : X → N` (`1 ≤ n`) is transverse to any map `g : Y → N` in the
first factor. -/
theorem transverse_of_isSubmersion_left {f : X → N} {g : Y → N}
    (hn : 1 ≤ n) (hf : Manifold.IsSubmersion IX IN n f) (p : X × Y) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  rw [LinearMap.range_eq_top.2 (hf.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.1),
    top_sup_eq]

end Transversality

section BaseChange

variable {EX HX X EY HY Y EN HN N : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IX : ModelWithCorners ℝ EX HX} {IY : ModelWithCorners ℝ EY HY}
  {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} [IsManifold IX n X] [IsManifold IY n Y] [IsManifold IN n N]
  [IX.Boundaryless] [IY.Boundaryless] [IN.Boundaryless]
  [FiniteDimensional ℝ EX] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EN]
  {f : X → N} {g : Y → N}
  (hn : 1 ≤ n) (hf : ContMDiff IX IN n f) (hg : ContMDiff IY IN n g)
  (htrans : ∀ p : X × Y, f p.1 = g p.2 →
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤)

/-- The image of the first projection's differential consists exactly of vectors whose
image under `df` lies in the image of `dg`, after identifying the target tangent spaces. -/
theorem range_mfderiv_fst_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ p : {p : X × Y // f p.1 = g p.2},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX
        (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.1) p).range =
      ((((tangentSpaceCast IN (g p.val.2) (f p.val.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.val.2)).range).comap (mfderiv IX IN f p.val.1).toLinearMap := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold IX 1 X := .of_le hn
  have : IsManifold IY 1 Y := .of_le hn
  have hi := isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans
  intro p
  have hd := mfderiv_comp p mdifferentiableAt_fst
    (hi.contMDiff p |>.mdifferentiableAt hn0)
  simp only [Function.comp_def, mfderiv_fst] at hd
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    have hu := (mem_range_mfderiv_coe_transverseFiberProduct_iff hn hf hg htrans p
      (mfderiv _ _ Subtype.val p u)).1 ⟨u, rfl⟩
    rw [hd]
    exact ⟨(mfderiv _ (IX.prod IY) Subtype.val p u).2, hu.symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨u, hu⟩ := (mem_range_mfderiv_coe_transverseFiberProduct_iff
      hn hf hg htrans p (v, w)).2 hw.symm
    refine ⟨u, ?_⟩
    rw [hd]
    exact congrArg Prod.fst hu

/-- The image of the second projection's differential consists exactly of vectors whose
image under `dg` (transported to the other target tangent space) lies in the image of `df`. -/
theorem range_mfderiv_snd_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ p : {p : X × Y // f p.1 = g p.2},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY
        (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) p).range =
      (mfderiv IX IN f p.val.1).range.comap
        (((tangentSpaceCast IN (g p.val.2) (f p.val.1)).toContinuousLinearMap).comp
          (mfderiv IY IN g p.val.2)).toLinearMap := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold IX 1 X := .of_le hn
  have : IsManifold IY 1 Y := .of_le hn
  have hi := isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans
  intro p
  have hd := mfderiv_comp p mdifferentiableAt_snd
    (hi.contMDiff p |>.mdifferentiableAt hn0)
  simp only [Function.comp_def, mfderiv_snd] at hd
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    have hu := (mem_range_mfderiv_coe_transverseFiberProduct_iff hn hf hg htrans p
      (mfderiv _ _ Subtype.val p u)).1 ⟨u, rfl⟩
    rw [hd]
    exact ⟨(mfderiv _ (IX.prod IY) Subtype.val p u).1, hu⟩
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := (mem_range_mfderiv_coe_transverseFiberProduct_iff
      hn hf hg htrans p (v, w)).2 hv
    refine ⟨u, ?_⟩
    rw [hd]
    exact congrArg Prod.snd hu

/-- Base change preserves submersions: the first projection of the transverse fibre product
is a submersion if the map from the second factor is a submersion. -/
theorem isSubmersion_fst_transverseFiberProduct (hgs : Manifold.IsSubmersion IY IN n g) :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX n
      (fun p : {p : X × Y // f p.1 = g p.2} ↦ p.val.1) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have := isManifold_transverseFiberProduct hn hf hg htrans
  have hp := (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff.fst
  apply (hp.isSubmersionOfComplement_of_surjective_mfderiv hn ?_).isSubmersion
  intro p
  apply LinearMap.range_eq_top.mp
  rw [range_mfderiv_fst_transverseFiberProduct hn hf hg htrans]
  have hs := (tangentSpaceCast IN (g p.val.2) (f p.val.1)).surjective.comp
    (hgs.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.val.2)
  have hr : (((tangentSpaceCast IN (g p.val.2) (f p.val.1)).toContinuousLinearMap).comp
      (mfderiv IY IN g p.val.2)).range = ⊤ := LinearMap.range_eq_top.2 hs
  rw [hr, Submodule.comap_top]

/-- Base change preserves submersions: the second projection of the transverse fibre product
is a submersion if the map from the first factor is a submersion. -/
theorem isSubmersion_snd_transverseFiberProduct (hfs : Manifold.IsSubmersion IX IN n f) :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY n
      (fun p : {p : X × Y // f p.1 = g p.2} ↦ p.val.2) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have := isManifold_transverseFiberProduct hn hf hg htrans
  have hp := (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff.snd
  apply (hp.isSubmersionOfComplement_of_surjective_mfderiv hn ?_).isSubmersion
  intro p
  apply LinearMap.range_eq_top.mp
  rw [range_mfderiv_snd_transverseFiberProduct hn hf hg htrans,
    LinearMap.range_eq_top.2
      (hfs.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.val.1), Submodule.comap_top]

/-- Base change preserves injectivity of differentials: the differential of the first projection
of the transverse fibre product at `p` is injective if the differential of `g` at `p.2` is. -/
theorem injective_mfderiv_fst_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ p : {p : X × Y // f p.1 = g p.2}, Injective (mfderiv IY IN g p.val.2) →
      Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX
        (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.1) p) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  intro p hgi
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦
    eq_zero_of_mfderiv_transverseFiberProduct hn hf hg htrans p ξ hξ ?_
  have hfg :=
    mfderiv_comp_mfderiv_fst_eq_mfderiv_comp_mfderiv_snd_transverseFiberProduct hn hf hg htrans p ξ
  rw [hξ, map_zero, eq_comm, map_eq_zero_iff _ (tangentSpaceCast IN _ _).injective] at hfg
  exact (injective_iff_map_eq_zero _).1 hgi _ hfg

/-- Base change preserves immersions: the first projection of the transverse fibre product is an
immersion if `g` has injective differential at the second component of every point of the fibre
product, for instance if `g` is an immersion. -/
theorem isImmersion_fst_transverseFiberProduct
    (hgi : ∀ p : {p : X × Y // f p.1 = g p.2}, Injective (mfderiv IY IN g p.val.2)) :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    Manifold.IsImmersion
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX n
      (fun p : {p : X × Y // f p.1 = g p.2} ↦ p.val.1) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have := isManifold_transverseFiberProduct hn hf hg htrans
  exact (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff.fst
    |>.isImmersion_of_injective_mfderiv hn
      fun p ↦ injective_mfderiv_fst_transverseFiberProduct hn hf hg htrans p (hgi p)

/-- Base change preserves injectivity of differentials: the differential of the second projection
of the transverse fibre product at `p` is injective if the differential of `f` at `p.1` is. -/
theorem injective_mfderiv_snd_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ p : {p : X × Y // f p.1 = g p.2}, Injective (mfderiv IX IN f p.val.1) →
      Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY
        (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) p) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  intro p hfi
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦
    eq_zero_of_mfderiv_transverseFiberProduct hn hf hg htrans p ξ ?_ hξ
  have hfg :=
    mfderiv_comp_mfderiv_fst_eq_mfderiv_comp_mfderiv_snd_transverseFiberProduct hn hf hg htrans p ξ
  rw [hξ, map_zero, map_zero] at hfg
  exact (injective_iff_map_eq_zero _).1 hfi _ hfg

/-- Base change preserves immersions: the second projection of the transverse fibre product is an
immersion if `f` has injective differential at the first component of every point of the fibre
product, for instance if `f` is an immersion. -/
theorem isImmersion_snd_transverseFiberProduct
    (hfi : ∀ p : {p : X × Y // f p.1 = g p.2}, Injective (mfderiv IX IN f p.val.1)) :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    Manifold.IsImmersion
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY n
      (fun p : {p : X × Y // f p.1 = g p.2} ↦ p.val.2) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have := isManifold_transverseFiberProduct hn hf hg htrans
  exact (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff.snd
    |>.isImmersion_of_injective_mfderiv hn
      fun p ↦ injective_mfderiv_snd_transverseFiberProduct hn hf hg htrans p (hfi p)

end BaseChange

end TauCeti
