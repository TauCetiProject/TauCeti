/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Local equations for transverse fibre products

For maps `f : X → N` and `g : Y → N`, coordinates `φ` on their common target give the
local equation `φ(f x) - φ(g y) = 0`. On the preimage of the coordinate domain this equation
cuts out exactly the fibre product. At a pair with `f x = g y`, its derivative is the
invertible coordinate derivative applied to `df u - dg v`.

Consequently the equation is regular exactly when the two derivative ranges span the target
tangent space. Its kernel is the space of pairs with equal images under the two derivatives,
with dimension `dim X + dim Y - dim N` in finite dimension.
These are the local equations and tangent spaces used in the regular-level construction of a
transverse fibre product. The equal target tangent spaces are identified explicitly by
`tangentSpaceCast`; no identification of tangent spaces at distinct points is used.
No separation or countability hypotheses on the manifolds are needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages), applied to the diagonal in `N × N`.
-/

public section

open Function Set
open scoped Manifold ContDiff

namespace PartialDiffeomorph

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

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The difference of target coordinates, whose zero set locally defines a fibre product.
Only on the preimage of `φ.source` in both factors does its vanishing characterize equality. -/
def fiberProductEquation (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n)
    (f : X → N) (g : Y → N) (p : X × Y) : EN :=
  φ (f p.1) - φ (g p.2)

omit [TopologicalSpace X] [TopologicalSpace Y] in
@[simp]
theorem fiberProductEquation_apply (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n)
    (f : X → N) (g : Y → N) (p : X × Y) :
    φ.fiberProductEquation f g p = φ (f p.1) - φ (g p.2) := (rfl)

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The equation cuts out exactly the fibre product on the coordinate domain. -/
theorem fiberProductEquation_eq_zero_iff (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n)
    {f : X → N} {g : Y → N} {p : X × Y}
    (hx : f p.1 ∈ φ.source) (hy : g p.2 ∈ φ.source) :
    φ.fiberProductEquation f g p = 0 ↔ f p.1 = g p.2 := by
  simp only [fiberProductEquation_apply, sub_eq_zero]
  exact ⟨fun h ↦ φ.injOn hx hy h, congrArg φ⟩

/-- Smooth maps give a smooth defining equation throughout the coordinate domain. -/
theorem contMDiffOn_fiberProductEquation (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n)
    {f : X → N} {g : Y → N} (hf : ContMDiff IX IN n f) (hg : ContMDiff IY IN n g) :
    ContMDiffOn (IX.prod IY) 𝓘(𝕜, EN) n (φ.fiberProductEquation f g)
      ((f ⁻¹' φ.source) ×ˢ (g ⁻¹' φ.source)) := by
  let U := (f ⁻¹' φ.source) ×ˢ (g ⁻¹' φ.source)
  exact (φ.contMDiffOn.comp ((hf.comp (contMDiff_fst (J := IY))).contMDiffOn (s := U))
    (fun _ hp ↦ hp.1)).sub
      (φ.contMDiffOn.comp ((hg.comp (contMDiff_snd (I := IX))).contMDiffOn (s := U))
        (fun _ hp ↦ hp.2))

/-- At a pair in the fibre product, the vector-valued derivative of its local equation is
the coordinate derivative applied to the difference of the map derivatives. -/
theorem mvfderiv_fiberProductEquation_apply
    (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n) (hn : n ≠ 0)
    {f : X → N} {g : Y → N} {p : X × Y}
    (hf : MDifferentiableAt IX IN f p.1) (hg : MDifferentiableAt IY IN g p.2)
    (hfg : f p.1 = g p.2) (hx : f p.1 ∈ φ.source)
    (v : TangentSpace (IX.prod IY) p) :
    mvfderiv (IX.prod IY) (φ.fiberProductEquation f g) p v =
      mvfderiv IN φ (f p.1)
        (mfderiv IX IN f p.1 v.1 -
          tangentSpaceCast IN (g p.2) (f p.1) (mfderiv IY IN g p.2 v.2)) := by
  have hφ := (φ.isLocalDiffeomorphAt IN 𝓘(𝕜, EN) n hx).mdifferentiableAt hn
  have hψ : MDifferentiableAt IN 𝓘(𝕜, EN) φ (g p.2) := hfg ▸ hφ
  have hsub := mvfderiv_sub
    ((hφ.comp p.1 hf).comp p mdifferentiableAt_fst)
    ((hψ.comp p.2 hg).comp p mdifferentiableAt_snd)
  have hDg : ∀ w : TangentSpace IN (g p.2),
      mvfderiv IN φ (g p.2) w =
        mvfderiv IN φ (f p.1) (tangentSpaceCast IN (g p.2) (f p.1) w) := by
    rw [hfg]
    intro w
    rfl
  -- The equation is the pointwise subtraction of the two coordinate composites.
  have hEq : φ.fiberProductEquation f g =
      (φ ∘ f) ∘ Prod.fst - (φ ∘ g) ∘ Prod.snd := rfl
  have hfst : mfderiv (IX.prod IY) IX Prod.fst p v = v.1 :=
    DFunLike.congr_fun mfderiv_fst v
  have hsnd : mfderiv (IX.prod IY) IY Prod.snd p v = v.2 :=
    DFunLike.congr_fun mfderiv_snd v
  rw [hEq, hsub]
  simp only [sub_apply,
    mvfderiv_comp_apply p (hφ.comp p.1 hf) mdifferentiableAt_fst v,
    mvfderiv_comp_apply p (hψ.comp p.2 hg) mdifferentiableAt_snd v,
    hfst, hsnd, mvfderiv_comp_apply p.1 hφ hf v.1,
    mvfderiv_comp_apply p.2 hψ hg v.2, hDg, map_sub]

/-- The tangent kernel of the defining equation consists of pairs of vectors with equal
images under the two map derivatives. This description is independent of target coordinates. -/
theorem mem_ker_mvfderiv_fiberProductEquation_iff
    (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n) (hn : n ≠ 0)
    {f : X → N} {g : Y → N} {p : X × Y}
    (hf : MDifferentiableAt IX IN f p.1) (hg : MDifferentiableAt IY IN g p.2)
    (hfg : f p.1 = g p.2) (hx : f p.1 ∈ φ.source)
    (v : TangentSpace (IX.prod IY) p) :
    v ∈ (mvfderiv (IX.prod IY) (φ.fiberProductEquation f g) p).ker ↔
      mfderiv IX IN f p.1 v.1 =
        tangentSpaceCast IN (g p.2) (f p.1) (mfderiv IY IN g p.2 v.2) := by
  have hi : Injective (mvfderiv IN φ (f p.1)) :=
    (NormedSpace.fromTangentSpace (φ (f p.1))).injective.comp
      ((φ.isLocalDiffeomorphAt IN 𝓘(𝕜, EN) n hx).isInvertible_mfderiv hn).injective
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    φ.mvfderiv_fiberProductEquation_apply hn hf hg hfg hx]
  exact (hi.eq_iff' (map_zero _)).trans sub_eq_zero

/-- Transversality is exactly regularity of the local fibre-product equation. The range of
`dg` is transported to the equal tangent space at `f p.1` before taking the supremum. -/
theorem surjective_mvfderiv_fiberProductEquation_iff
    (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n) (hn : n ≠ 0)
    {f : X → N} {g : Y → N} {p : X × Y}
    (hf : MDifferentiableAt IX IN f p.1) (hg : MDifferentiableAt IY IN g p.2)
    (hfg : f p.1 = g p.2) (hx : f p.1 ∈ φ.source) :
    Surjective (mvfderiv (IX.prod IY) (φ.fiberProductEquation f g) p) ↔
      (mfderiv IX IN f p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IN g p.2)).range = ⊤ := by
  let Df := mfderiv IX IN f p.1
  let Dg := ((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
    (mfderiv IY IN g p.2)
  have hφ := (φ.isLocalDiffeomorphAt IN 𝓘(𝕜, EN) n hx).isInvertible_mfderiv hn
  have hbij : Bijective (mvfderiv IN φ (f p.1)) :=
    (NormedSpace.fromTangentSpace (φ (f p.1))).bijective.comp hφ.bijective
  have hD (v : TangentSpace (IX.prod IY) p) :
      mvfderiv (IX.prod IY) (φ.fiberProductEquation f g) p v =
        mvfderiv IN φ (f p.1) (Df v.1 - Dg v.2) :=
    φ.mvfderiv_fiberProductEquation_apply hn hf hg hfg hx v
  constructor
  · intro h
    apply top_unique
    intro w _
    obtain ⟨v, hv⟩ := h (mvfderiv IN φ (f p.1) w)
    have hw : Df v.1 - Dg v.2 = w := hbij.injective ((hD v).symm.trans hv)
    rw [← hw]
    exact Submodule.sub_mem_sup (LinearMap.mem_range_self _ v.1)
      (LinearMap.mem_range_self _ v.2)
  · intro h w
    obtain ⟨z, rfl⟩ := hbij.surjective w
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h ▸ (Submodule.mem_top : z ∈ ⊤))
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    have hab' : Df u + Dg v = z := hab
    refine ⟨(u, -v), ?_⟩
    exact (hD (u, -v)).trans (congrArg (mvfderiv IN φ (f p.1))
      (by simpa only [map_neg, sub_neg_eq_add] using hab'))

/-- At a transverse pair, the kernel of the defining equation has the expected dimension.
Surjectivity forces the target dimension not to exceed the sum of the source dimensions. -/
theorem finrank_ker_mvfderiv_fiberProductEquation
    [FiniteDimensional 𝕜 EX] [FiniteDimensional 𝕜 EY]
    (φ : PartialDiffeomorph IN 𝓘(𝕜, EN) N EN n) (hn : n ≠ 0)
    {f : X → N} {g : Y → N} {p : X × Y}
    (hf : MDifferentiableAt IX IN f p.1) (hg : MDifferentiableAt IY IN g p.2)
    (hfg : f p.1 = g p.2) (hx : f p.1 ∈ φ.source)
    (htrans : (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤) :
    Module.finrank 𝕜 (mvfderiv (IX.prod IY) (φ.fiberProductEquation f g) p).ker =
      Module.finrank 𝕜 EX + Module.finrank 𝕜 EY - Module.finrank 𝕜 EN := by
  have hs := (φ.surjective_mvfderiv_fiberProductEquation_iff hn hf hg hfg hx).2 htrans
  have hd := LinearMap.finrank_range_add_finrank_ker
    (mvfderiv (IX.prod IY) (φ.fiberProductEquation f g) p).toLinearMap
  rw [LinearMap.range_eq_top.2 hs, finrank_top, TauCeti.finrank_tangentSpace,
    Module.finrank_prod] at hd
  omega

end PartialDiffeomorph
