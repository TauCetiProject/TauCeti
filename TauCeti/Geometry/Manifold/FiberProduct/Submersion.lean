/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Submersions under transverse base change

For transverse maps `f : X → N` and `g : Y → N`, the projections from the equal-value
subtype have tangent images `df⁻¹(range dg)` and `dg⁻¹(range df)`, respectively.
Consequently the projection to `X` is a submersion when `g` is a submersion, and the
projection to `Y` is a submersion when `f` is. These results use the previously constructed
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
        (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.1.1) p).range =
      ((((tangentSpaceCast IN (g p.1.2) (f p.1.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.1.2)).range).comap (mfderiv IX IN f p.1.1).toLinearMap := by
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
        (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.1.2) p).range =
      (mfderiv IX IN f p.1.1).range.comap
        (((tangentSpaceCast IN (g p.1.2) (f p.1.1)).toContinuousLinearMap).comp
          (mfderiv IY IN g p.1.2)).toLinearMap := by
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
      (fun p : {p : X × Y // f p.1 = g p.2} ↦ p.1.1) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have := isManifold_transverseFiberProduct hn hf hg htrans
  have hp := (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff.fst
  apply (hp.isSubmersionOfComplement_of_surjective_mfderiv hn ?_).isSubmersion
  intro p
  apply LinearMap.range_eq_top.mp
  rw [range_mfderiv_fst_transverseFiberProduct hn hf hg htrans]
  have hs := (tangentSpaceCast IN (g p.1.2) (f p.1.1)).surjective.comp
    (hgs.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.1.2)
  have hr : (((tangentSpaceCast IN (g p.1.2) (f p.1.1)).toContinuousLinearMap).comp
      (mfderiv IY IN g p.1.2)).range = ⊤ := LinearMap.range_eq_top.2 hs
  rw [hr, Submodule.comap_top]

/-- Base change preserves submersions: the second projection of the transverse fibre product
is a submersion if the map from the first factor is a submersion. -/
theorem isSubmersion_snd_transverseFiberProduct (hfs : Manifold.IsSubmersion IX IN n f) :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY n
      (fun p : {p : X × Y // f p.1 = g p.2} ↦ p.1.2) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  have := isManifold_transverseFiberProduct hn hf hg htrans
  have hp := (isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff.snd
  apply (hp.isSubmersionOfComplement_of_surjective_mfderiv hn ?_).isSubmersion
  intro p
  apply LinearMap.range_eq_top.mp
  rw [range_mfderiv_snd_transverseFiberProduct hn hf hg htrans,
    LinearMap.range_eq_top.2
      (hfs.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.1.1), Submodule.comap_top]

end TauCeti
