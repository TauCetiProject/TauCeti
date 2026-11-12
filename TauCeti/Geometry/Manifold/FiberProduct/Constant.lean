/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel

/-!
# Fibre products with a constant map

The fibre product of `f : X → N` with the constant map `Y → N` at a regular value `c`
is canonically diffeomorphic to `{x : X // f x = c} × Y`. The comparison uses the existing
transverse fibre-product atlas and the preferred regular-fibre atlas, so these two constructions
agree as smooth manifolds, as well as topological spaces. Both maps preserve the ambient pair.

Regularity is required only along the fibre over `c`; `f` need not be a submersion elsewhere.
No separation, countability or nonemptiness assumptions are needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer (2013),
  Corollary 5.14 (regular level sets) and Theorem 6.30 (transverse preimages).
-/

public section

open Function Module
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
  {f : X → N} {c : N}

/-- The transverse fibre product with a constant map at a regular value is the product of
that regular fibre with the domain of the constant map. The map sends `(x,y)` to `(⟨x,h⟩,y)`
and uses the independently constructed fibre-product and regular-fibre atlases. -/
noncomputable def fiberProductConstDiffeomorph (hn : 1 ≤ n) (hf : ContMDiff IX IN n f)
    (hreg : IsRegularValue IX IN f c) :
    letI := regularFiberChartedSpace hn hf BoundarylessManifold.isInteriorPoint hreg
    letI := transverseFiberProductChartedSpace (IY := IY) (g := fun _ : Y ↦ c) hn hf contMDiff_const
      (fun p hp ↦ by
        rw [LinearMap.range_eq_top.mpr (isRegularPoint_iff.mp (hreg.isRegularPoint hp)),
          top_sup_eq])
    {p : X × Y // f p.1 = c} ≃ₘ^n⟮
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EX - finrank ℝ EN) → ℝ).prod IY⟯
      {x : X // f x = c} × Y := by
  have htrans (p : X × Y) (hp : f p.1 = c) :
      (mfderiv IX IN f p.1).range ⊔
        (((tangentSpaceCast IN c (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IN (fun _ : Y ↦ c) p.2)).range = ⊤ := by
    rw [LinearMap.range_eq_top.mpr (isRegularPoint_iff.mp (hreg.isRegularPoint hp)), top_sup_eq]
  letI := regularFiberChartedSpace hn hf BoundarylessManifold.isInteriorPoint hreg
  letI := transverseFiberProductChartedSpace (IY := IY) hn hf contMDiff_const htrans
  haveI := isManifold_regularFiber hn hf BoundarylessManifold.isInteriorPoint hreg
  haveI := isManifold_transverseFiberProduct (IY := IY) hn hf contMDiff_const htrans
  have hP := (isSmoothEmbedding_coe_transverseFiberProduct (IY := IY) hn hf contMDiff_const htrans)
  have hF := (isSmoothEmbedding_coe_regularFiber hn hf
    BoundarylessManifold.isInteriorPoint hreg)
  let e : {p : X × Y // f p.1 = c} ≃ {x : X // f x = c} × Y :=
    Equiv.prodSubtypeFstEquivSubtypeProd (α := X) (β := Y) (p := fun x ↦ f x = c)
  refine { e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply ContMDiff.prodMk
    · exact hF.contMDiff_iff_comp.2 (contMDiff_fst.comp hP.contMDiff)
    · exact contMDiff_snd.comp hP.contMDiff
  · exact hP.contMDiff_iff_comp.2
      ((hF.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)

/-- The constant-map comparison preserves both entries of the ambient pair. -/
@[simp]
theorem fiberProductConstDiffeomorph_apply (hn : 1 ≤ n) (hf : ContMDiff IX IN n f)
    (hreg : IsRegularValue IX IN f c) (p : {p : X × Y // f p.1 = c}) :
    fiberProductConstDiffeomorph (IY := IY) hn hf hreg p = (⟨p.1.1, p.2⟩, p.1.2) :=
  (rfl)

/-- The inverse constant-map comparison sends a point of the regular fibre and a point of `Y`
to their ambient pair. -/
@[simp]
theorem fiberProductConstDiffeomorph_symm_apply (hn : 1 ≤ n) (hf : ContMDiff IX IN n f)
    (hreg : IsRegularValue IX IN f c) (p : {x : X // f x = c} × Y) :
    letI := regularFiberChartedSpace hn hf BoundarylessManifold.isInteriorPoint hreg
    letI := transverseFiberProductChartedSpace (IY := IY) (g := fun _ : Y ↦ c) hn hf contMDiff_const
      (fun p hp ↦ by
        rw [LinearMap.range_eq_top.mpr (isRegularPoint_iff.mp (hreg.isRegularPoint hp)),
          top_sup_eq])
    (fiberProductConstDiffeomorph (IY := IY) hn hf hreg).symm p = ⟨(p.1.1, p.2), p.1.2⟩ :=
  (rfl)

end TauCeti
