/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Fibre products with an identity map

Base change along an identity map does not change a manifold: the fibre product of
`f : X → N` with `id : N → N` is diffeomorphic to `X` by its first projection, with inverse
`x ↦ (x, f x)`. There is also the comparison with the identity in the first factor.
Both comparisons use the already constructed transverse fibre-product atlas and the inherited
subspace topology, not a new graph atlas.

In particular, setting `f = id` identifies the fibre product of two identity maps with the
original manifold, by either projection. These comparisons supply the unit identifications
for smooth base change. No separation, countability or nonemptiness assumptions are needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages).
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H X F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n X] [IsManifold J n N] {f : X → N}

/-- Base change of `f` along the identity is diffeomorphic to its domain by the first
projection. The inverse is the graph map `x ↦ (x, f x)`. The fibre product carries its
chosen transverse atlas. -/
noncomputable def transverseFiberProductIdRightDiffeomorph (hn : 1 ≤ n)
    (hf : ContMDiff I J n f) :
    letI := transverseFiberProductChartedSpace hn hf (contMDiff_id (I := J))
      (by intro p _; simp [mfderiv_id])
    {p : X × N // f p.1 = id p.2} ≃ₘ^n⟮
      𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F - finrank ℝ F) → ℝ), I⟯ X := by
  letI := transverseFiberProductChartedSpace hn hf (contMDiff_id (I := J))
    (by intro p _; simp [mfderiv_id])
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hf (contMDiff_id (I := J))
    (by intro p _; simp [mfderiv_id])
  refine
    { toFun := fun p ↦ p.1.1
      invFun := fun x ↦ ⟨(x, f x), rfl⟩
      left_inv := ?_
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_fst.comp hemb.isImmersion.contMDiff
      contMDiff_invFun := ?_ }
  · intro p
    apply Subtype.ext
    exact Prod.ext rfl p.2
  · exact hemb.contMDiff_iff_comp.2 (contMDiff_id.prodMk hf)

/-- The identity-base-change comparison is the first projection. -/
@[simp]
theorem transverseFiberProductIdRightDiffeomorph_apply (hn : 1 ≤ n)
    (hf : ContMDiff I J n f) (p : {p : X × N // f p.1 = id p.2}) :
    transverseFiberProductIdRightDiffeomorph hn hf p = p.1.1 :=
  (rfl)

/-- The inverse identity-base-change comparison is the graph map. -/
@[simp]
theorem transverseFiberProductIdRightDiffeomorph_symm_apply (hn : 1 ≤ n)
    (hf : ContMDiff I J n f) (x : X) :
    letI := transverseFiberProductChartedSpace hn hf (contMDiff_id (I := J))
      (by intro p _; simp [mfderiv_id])
    (transverseFiberProductIdRightDiffeomorph hn hf).symm x = ⟨(x, f x), rfl⟩ :=
  (rfl)

/-- With the identity in the first factor, the second projection identifies the transverse
fibre product with the domain of `f`. Its inverse is `x ↦ (f x, x)`. -/
noncomputable def transverseFiberProductIdLeftDiffeomorph (hn : 1 ≤ n)
    (hf : ContMDiff I J n f) :
    letI := transverseFiberProductChartedSpace hn (contMDiff_id (I := J)) hf
      (by intro p _; simp [mfderiv_id])
    {p : N × X // id p.1 = f p.2} ≃ₘ^n⟮
      𝓘(ℝ, Fin (finrank ℝ F + finrank ℝ E - finrank ℝ F) → ℝ), I⟯ X := by
  letI := transverseFiberProductChartedSpace hn (contMDiff_id (I := J)) hf
    (by intro p _; simp [mfderiv_id])
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn (contMDiff_id (I := J)) hf
    (by intro p _; simp [mfderiv_id])
  refine
    { toFun := fun p ↦ p.1.2
      invFun := fun x ↦ ⟨(f x, x), rfl⟩
      left_inv := ?_
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_snd.comp hemb.isImmersion.contMDiff
      contMDiff_invFun := ?_ }
  · intro p
    apply Subtype.ext
    exact Prod.ext p.2.symm rfl
  · exact hemb.contMDiff_iff_comp.2 (hf.prodMk contMDiff_id)

/-- The comparison with the identity in the first factor is the second projection. -/
@[simp]
theorem transverseFiberProductIdLeftDiffeomorph_apply (hn : 1 ≤ n)
    (hf : ContMDiff I J n f) (p : {p : N × X // id p.1 = f p.2}) :
    transverseFiberProductIdLeftDiffeomorph hn hf p = p.1.2 :=
  (rfl)

/-- The inverse comparison with the identity in the first factor inserts the value of `f`. -/
@[simp]
theorem transverseFiberProductIdLeftDiffeomorph_symm_apply (hn : 1 ≤ n)
    (hf : ContMDiff I J n f) (x : X) :
    letI := transverseFiberProductChartedSpace hn (contMDiff_id (I := J)) hf
      (by intro p _; simp [mfderiv_id])
    (transverseFiberProductIdLeftDiffeomorph hn hf).symm x = ⟨(f x, x), rfl⟩ :=
  (rfl)

end TauCeti
