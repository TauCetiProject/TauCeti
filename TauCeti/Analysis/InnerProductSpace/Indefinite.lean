/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Linearization of changes of indefinite quadratic coordinates

A local change of coordinates fixing the origin and preserving
`Q(u,v) = -‖u‖² + ‖v‖²` has a derivative preserving the same quadratic form.
Its negative column `u ↦ (A u, B u)` consequently satisfies
`‖A u‖² - ‖B u‖² = ‖u‖²`; we call such a column an *isometric negative
column*, meaning that it pulls `Q` back to `-‖u‖²`, not that it preserves the
product norm. In particular `A` expands norms and, in finite
dimension, is invertible. The image of the negative coordinate plane is the graph
of `B ∘ A⁻¹`, which strictly decreases the norm of every nonzero vector.

These facts permit comparison of the negative disks of two Morse coordinate systems:
the invertible negative block has a polar part, while contracting the positive
coordinate of the linearized disk never increases `Q`. Only the negative column's
quadratic identity is needed for the linear statements; an ambient linear isomorphism
is not assumed. The calculus statement supplies that identity for local transitions.
Zero-dimensional factors are allowed.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Function Filter Topology

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (L : E →L[ℝ] E × F)
  (hL : ∀ u, ‖(L u).1‖ ^ 2 - ‖(L u).2‖ ^ 2 = ‖u‖ ^ 2)

include hL

/-- The first block of an isometric negative column expands norms. -/
theorem norm_le_norm_fst_of_norm_sq_sub (u : E) : ‖u‖ ≤ ‖(L u).1‖ := by
  have := hL u
  nlinarith [sq_nonneg ‖(L u).2‖, norm_nonneg u, norm_nonneg (L u).1]

/-- Away from zero, the positive block of an isometric negative column has strictly
smaller norm than its negative block. -/
theorem norm_snd_lt_norm_fst_of_norm_sq_sub {u : E} (hu : u ≠ 0) :
    ‖(L u).2‖ < ‖(L u).1‖ := by
  have := hL u
  have := norm_pos_iff.mpr hu
  nlinarith [norm_nonneg (L u).1, norm_nonneg (L u).2]

/-- In finite dimension, the negative block of an isometric negative column is invertible. -/
theorem isInvertible_fst_of_norm_sq_sub [FiniteDimensional ℝ E] :
    ((fst ℝ E F).comp L).IsInvertible := by
  obtain ⟨G, hCG, hGC, -⟩ := LinearMap.exists_comp_eq_id_of_mul_norm_le
    (C := ((fst ℝ E F).comp L).toLinearMap) (c := 1) one_pos
    (fun u ↦ by simpa using L.norm_le_norm_fst_of_norm_sq_sub hL u)
  let e : E ≃ₗ[ℝ] E :=
    LinearEquiv.ofLinearMap ((fst ℝ E F).comp L).toLinearMap G hCG hGC
  exact ⟨e.toContinuousLinearEquiv, by ext; simp [e]⟩

/-- For any inverse of the negative block, its norm is at most one. -/
theorem norm_symm_le_one_of_norm_sq_sub (e : E ≃L[ℝ] E)
    (he : ∀ u, e u = (L u).1) : ‖(e.symm : E →L[ℝ] E)‖ ≤ 1 := by
  refine (e.symm : E →L[ℝ] E).opNorm_le_bound (by norm_num) fun u ↦ ?_
  simpa only [ContinuousLinearEquiv.coe_coe, one_mul, ← he, e.apply_symm_apply] using
    L.norm_le_norm_fst_of_norm_sq_sub hL (e.symm u)

/-- The graph map of an isometric negative column strictly decreases nonzero norms. -/
theorem norm_snd_symm_lt_of_norm_sq_sub (e : E ≃L[ℝ] E)
    (he : ∀ u, e u = (L u).1) {u : E} (hu : u ≠ 0) :
    ‖(L (e.symm u)).2‖ < ‖u‖ := by
  have hv : e.symm u ≠ 0 := by
    intro hv
    apply hu
    rw [← e.apply_symm_apply u, hv, map_zero]
  simpa only [← he, e.apply_symm_apply] using
    L.norm_snd_lt_norm_fst_of_norm_sq_sub hL hv

/-- Contracting the positive component of an isometric negative column keeps the
quadratic value at or below its original negative value. -/
theorem neg_norm_fst_sq_add_norm_smul_snd_sq_le_of_norm_sq_sub
    {t : ℝ} (ht : |t| ≤ 1) (u : E) :
    -‖(L u).1‖ ^ 2 + ‖t • (L u).2‖ ^ 2 ≤ -‖u‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  have hs : |t| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
  nlinarith [hL u, sq_nonneg ‖(L u).2‖]

end ContinuousLinearMap

namespace DifferentiableAt

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {T : E × F → E × F}

/-- The derivative of a local change of indefinite quadratic coordinates at the origin
preserves the same quadratic form. The normal-form identity is needed only near zero. -/
theorem norm_sq_sub_fderiv (hT : DifferentiableAt ℝ T 0) (hT0 : T 0 = 0)
    (hQ : ∀ᶠ z in 𝓝 0, ‖(T z).1‖ ^ 2 - ‖(T z).2‖ ^ 2 = ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2)
    (z : E × F) :
    ‖(fderiv ℝ T 0 z).1‖ ^ 2 - ‖(fderiv ℝ T 0 z).2‖ ^ 2 =
      ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 := by
  let p := ContinuousLinearMap.fst ℝ E F
  let q := ContinuousLinearMap.snd ℝ E F
  let B : (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp p p - (innerSL ℝ).bilinearComp q q
  have hB (v : E × F) : B v v = ‖v.1‖ ^ 2 - ‖v.2‖ ^ 2 := by
    simp [B, p, q]
  have h := ContinuousLinearMap.apply_self_fderiv_eq_of_eventuallyEq B B hT hT0
    (hQ.mono fun z hz ↦ by simpa only [hB] using hz) z
  simpa only [hB] using h

/-- The negative block of a local indefinite-quadratic coordinate change is invertible.
Finite dimensionality is required only for the negative factor. -/
theorem isInvertible_fst_fderiv_inl [FiniteDimensional ℝ E]
    (hT : DifferentiableAt ℝ T 0) (hT0 : T 0 = 0)
    (hQ : ∀ᶠ z in 𝓝 0, ‖(T z).1‖ ^ 2 - ‖(T z).2‖ ^ 2 = ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2) :
    ((ContinuousLinearMap.fst ℝ E F).comp
      ((fderiv ℝ T 0).comp (ContinuousLinearMap.inl ℝ E F))).IsInvertible := by
  apply ContinuousLinearMap.isInvertible_fst_of_norm_sq_sub
  intro u
  simpa using hT.norm_sq_sub_fderiv hT0 hQ (u, 0)

end DifferentiableAt
