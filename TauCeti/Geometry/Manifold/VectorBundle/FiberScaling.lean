/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Fibre scaling on a vector bundle

Fibre scaling `H : V × [0, 1] → V`, `(v, t) ↦ t • v` (`TauCeti.vectorBundleFiberScaling`), is a
homotopy from the retraction `v ↦ 0_(π v)` of a real vector bundle onto its zero section to the
identity. It fixes the zero section at all times and is smooth on the cylinder `V × [0, 1]`
(`TauCeti.contMDiff_vectorBundleFiberScaling`). Since it is constant in time along the zero
section, its derivative kills the time direction there
(`TauCeti.mfderiv_vectorBundleFiberScaling_zeroSection_time`).

The time is the last factor, as in the cylinder `M × [0, 1]` of the homotopy operator on
differential forms.
-/

public section

noncomputable section

open Set Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module ℝ (V b)]

variable (FV V) in
/-- **Fibre scaling** `(v, t) ↦ t • v` on the total space of a vector bundle, a homotopy from the
retraction `v ↦ 0_(π v)` onto the zero section to the identity. This is the whole-bundle radial
contraction `TauCeti.IsTubularNeighborhood.radialContraction`, with the time last as in the
cylinder `V × [0, 1]` of `TauCeti.homotopyOperator`. -/
def vectorBundleFiberScaling (p : TotalSpace FV V × Icc (0 : ℝ) 1) : TotalSpace FV V :=
  ⟨p.1.proj, (p.2 : ℝ) • p.1.2⟩

/-- Fibre scaling multiplies the vector by the time and keeps its base point. -/
@[simp]
theorem vectorBundleFiberScaling_apply (v : TotalSpace FV V) (t : Icc (0 : ℝ) 1) :
    vectorBundleFiberScaling FV V (v, t) = ⟨v.proj, (t : ℝ) • v.2⟩ :=
  (rfl)

/-- At time one, fibre scaling is the identity. -/
theorem vectorBundleFiberScaling_one (v : TotalSpace FV V) :
    vectorBundleFiberScaling FV V (v, 1) = v := by
  simp

/-- At time zero, fibre scaling is the retraction onto the zero section. -/
theorem vectorBundleFiberScaling_zero (v : TotalSpace FV V) :
    vectorBundleFiberScaling FV V (v, 0) = zeroSection FV V v.proj := by
  simp [zeroSection]

/-- Fibre scaling fixes the zero section at all times. -/
theorem vectorBundleFiberScaling_zeroSection (b : B) (t : Icc (0 : ℝ) 1) :
    vectorBundleFiberScaling FV V (zeroSection FV V b, t) = zeroSection FV V b := by
  simp [zeroSection]

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  [VectorBundle ℝ FV V]

/-- Fibre scaling is smooth on the cylinder `V × [0, 1]`. Only the vector bundle structure is
used: the total space need not be a smooth manifold. -/
theorem contMDiff_vectorBundleFiberScaling {n : ℕ∞ω} :
    ContMDiff ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV)) n
      (vectorBundleFiberScaling FV V) :=
  (contMDiff_subtypeVal_Icc.comp contMDiff_snd).smul_totalSpace contMDiff_fst

/-- Along the zero section, fibre scaling has zero derivative in the time direction: it maps
`∂ₜ = (0, 1)` to `0`. -/
theorem mfderiv_vectorBundleFiberScaling_zeroSection_time (b : B) (t : Icc (0 : ℝ) 1)
    (τ : EuclideanSpace ℝ (Fin 1)) :
    mfderiv ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) (zeroSection FV V b, t) ((0 : EB × FV), τ) = 0 := by
  rw [mfderiv_prod_eq_add_apply (v := ((0 : EB × FV), τ))
    ((contMDiff_vectorBundleFiberScaling (n := 1) _).mdifferentiableAt one_ne_zero)]
  have hconst : (fun z : Icc (0 : ℝ) 1 ↦ vectorBundleFiberScaling FV V (zeroSection FV V b, z)) =
      fun _ ↦ zeroSection FV V b :=
    funext fun z ↦ vectorBundleFiberScaling_zeroSection b z
  rw [hconst, mfderiv_const]
  exact (add_zero _).trans (ContinuousLinearMap.map_zero _)

end TauCeti
