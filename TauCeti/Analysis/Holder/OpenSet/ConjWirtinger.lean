/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Holder.OpenSet.Comp.Left

/-!
# The Cauchy–Riemann operator on the Hölder space `C^{1,α}(Ω)`

Let `Ω` be an open subset of `ℂ` and `F` a complex normed space. The conjugate Wirtinger
derivative `∂u/∂(conj z) = (∂ₛu + i ∂ₜu) / 2` is a fixed real-linear function of the first
derivative. Applied to the Hölder derivative field of an element `u ∈ C^{1,α}(Ω, F)`, it gives a
bounded `α`-Hölder function on `Ω`. This file packages the Cauchy–Riemann operator as a continuous
linear map `C^{1,α}(Ω, F) → C^{0,α}(Ω, F)`, the second space being the bounded `α`-Hölder
functions on the subtype `Ω`, and identifies it with `TauCeti.conjWirtingerDeriv` of any function
on `ℂ` agreeing with `u` near the evaluation point. It is the principal part of the linearized
Cauchy–Riemann operators of holomorphic curves, in the Hölder setting of the Schauder theory.

## Main declarations

* `TauCeti.CkHolderSpaceOn.conjWirtingerDerivL`: the operator
  `C^{1,α}(Ω, F) →L[ℝ] C^{0,α}(Ω, F)`, `u ↦ ∂u/∂(conj z)`.
* `TauCeti.CkHolderSpaceOn.conjWirtingerDerivL_apply`: it equals `∂/∂(conj z)` of a representative
  of the germ at the evaluation point.
* `TauCeti.CkHolderSpaceOn.conjWirtingerDerivL_compLeftL`: it commutes with postcomposition by a
  complex-linear map, for instance with the coordinate projections of `ℂⁿ`.
-/

public noncomputable section

open Filter TopologicalSpace
open scoped NNReal Topology

namespace TauCeti.CkHolderSpaceOn

variable {α : ℝ≥0} {Ω : Opens ℂ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (α Ω F) in
/-- The Cauchy–Riemann operator `u ↦ ∂u/∂(conj z)` as a continuous linear map from
`C^{1,α}(Ω, F)` to the bounded `α`-Hölder functions on `Ω`. It takes the complex-antilinear part
of the first derivative field and evaluates it at `1`. -/
def conjWirtingerDerivL : CkHolderSpaceOn 1 α Ω F →L[ℝ] HolderSpace α Ω F :=
  HolderSpace.compLeftL (ContinuousLinearMap.apply ℝ F (1 : ℂ) ∘L
    ContinuousLinearMap.complexAntilinearPartL ∘L
      (continuousMultilinearCurryFin1 ℝ ℂ F).toContinuousLinearEquiv.toContinuousLinearMap) ∘L
    iteratedFDerivHolderL

/-- The Cauchy–Riemann operator on `C^{1,α}(Ω)` agrees on `Ω` with the conjugate Wirtinger
derivative of the extension by zero. -/
theorem conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_extend (u : CkHolderSpaceOn 1 α Ω F)
    (z : Ω) : conjWirtingerDerivL α Ω F u z = conjWirtingerDeriv u.extend z 1 := by
  have h : u.iteratedFDeriv 1 z = _root_.iteratedFDeriv ℝ 1 u.extend z :=
    (u.iteratedFDeriv_extend 1 z).symm
  simp [conjWirtingerDerivL, h, conjWirtingerDeriv_apply_eq_complexAntilinearPartL]

/-- The Cauchy–Riemann operator on `C^{1,α}(Ω)` is determined by the germ at the evaluation
point. -/
theorem conjWirtingerDerivL_apply (u : CkHolderSpaceOn 1 α Ω F) (z : Ω) {g : ℂ → F}
    (hg : u.extend =ᶠ[𝓝 (z : ℂ)] g) :
    conjWirtingerDerivL α Ω F u z = conjWirtingerDeriv g z 1 := by
  rw [conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_extend, hg.conjWirtingerDeriv_eq]

/-- The Cauchy–Riemann operator on `C^{1,α}(Ω)` commutes with postcomposition by a continuous
complex-linear map `L`: `∂(L ∘ u)/∂(conj z) = L ∘ ∂u/∂(conj z)`. -/
theorem conjWirtingerDerivL_compLeftL {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : F →L[ℂ] G) (u : CkHolderSpaceOn 1 α Ω F) :
    conjWirtingerDerivL α Ω G (compLeftL (L.restrictScalars ℝ) u) =
      HolderSpace.compLeftL (L.restrictScalars ℝ) (conjWirtingerDerivL α Ω F u) := by
  ext z
  rw [conjWirtingerDerivL_apply _ z (extend_compLeftL_eventuallyEq _ u z.property),
    HolderSpace.compLeftL_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [L.conjWirtingerDeriv_comp_left
      ((u.contDiffOn_extend.contDiffAt (Ω.isOpen.mem_nhds z.property)).differentiableAt
        one_ne_zero),
    conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_extend, ContinuousLinearMap.comp_apply]

end TauCeti.CkHolderSpaceOn
