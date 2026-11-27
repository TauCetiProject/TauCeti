/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.IteratedFDeriv
public import TauCeti.Analysis.Holder.OpenSet.Comp.Left
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.DiffContOnCl
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Holder.Bilinear
import TauCeti.Analysis.Holder.OpenSet.Zero

/-!
# The Cauchy–Riemann operator and its conjugate on the Hölder space `C^{1,α}(Ω)`

Let `Ω` be an open subset of `ℂ` and `F` a complex normed space. The conjugate Wirtinger
derivative `∂u/∂(conj z) = (∂ₛu + i ∂ₜu) / 2` is a fixed real-linear function of the first
derivative. Applied to the Hölder derivative field of an element `u ∈ C^{1,α}(Ω, F)`, it gives a
bounded `α`-Hölder function on `Ω`. This file packages the Cauchy–Riemann operator as a continuous
linear map `C^{1,α}(Ω, F) → C^{0,α}(Ω, F)`, the second space being the bounded `α`-Hölder
functions on the subtype `Ω`, and identifies it with `TauCeti.conjWirtingerDeriv` of any function
on `ℂ` agreeing with `u` near the evaluation point. It is the principal part of the linearized
Cauchy–Riemann operators of holomorphic curves, in the Hölder setting of the Schauder theory.
The Wirtinger derivative `∂u/∂z = (∂ₛu - i ∂ₜu) / 2`, the complex-linear part of the first
derivative, is packaged in the same way. On a convex open set and for `α ≤ 1`, the perturbation
`u ↦ A ∂u/∂z + B u` by coefficients `A`, `B ∈ C^{0,α}(Ω, F →L[ℝ] F)` is a continuous linear map
`C^{1,α}(Ω, F) → C^{0,α}(Ω, F)` of norm at most `‖A‖ + 3 ‖B‖`, which depends continuously and
linearly on `(A, B)`; adding it to
`∂u/∂(conj z)` gives the operators `∂u/∂(conj z) + A ∂u/∂z + B u` of the linear theory of
holomorphic curves.

## Main declarations

* `TauCeti.CkHolderSpaceOn.conjWirtingerDerivL`: the operator
  `C^{1,α}(Ω, F) →L[ℝ] C^{0,α}(Ω, F)`, `u ↦ ∂u/∂(conj z)`.
* `TauCeti.CkHolderSpaceOn.conjWirtingerDerivL_apply`: it equals `∂/∂(conj z)` of a representative
  of the germ at the evaluation point; in particular
  (`TauCeti.CkHolderSpaceOn.conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_closureExtend`) of the
  extension to the closure.
* `TauCeti.CkHolderSpaceOn.diffContOnCl_closureExtend_of_conjWirtingerDerivL_eq_zero`: on a convex
  open set, an element of the kernel extends to a function holomorphic on `Ω` and continuous on its
  closure.
* `TauCeti.CkHolderSpaceOn.conjWirtingerDerivL_compLeftL`: it commutes with postcomposition by a
  complex-linear map, for instance with the coordinate projections of `ℂⁿ`.
* `TauCeti.CkHolderSpaceOn.wirtingerDerivL`: the operator
  `C^{1,α}(Ω, F) →L[ℝ] C^{0,α}(Ω, F)`, `u ↦ ∂u/∂z`, with
  `TauCeti.CkHolderSpaceOn.wirtingerDerivL_apply`.
* `TauCeti.CkHolderSpaceOn.wirtingerPerturbationL`: the perturbation `u ↦ A ∂u/∂z + B u`, with
  the norm bound `TauCeti.CkHolderSpaceOn.norm_wirtingerPerturbationL_le` and its smooth
  dependence on the coefficients `TauCeti.CkHolderSpaceOn.contDiff_wirtingerPerturbationL`.
-/

public noncomputable section

open Filter TopologicalSpace ContinuousLinearMap
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

/-- The Cauchy–Riemann operator on `C^{1,α}(Ω)` agrees on `Ω` with the conjugate Wirtinger
derivative of the extension to the closure. -/
theorem conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_closureExtend
    (u : CkHolderSpaceOn 1 α Ω F) (z : Ω) :
    conjWirtingerDerivL α Ω F u z = conjWirtingerDeriv u.closureExtend z 1 :=
  conjWirtingerDerivL_apply u z (u.closureExtend_eventuallyEq_extend z.property).symm

/-- **Elements of the kernel are holomorphic.** On a convex open set `Ω`, an element of
`C^{1,α}(Ω, F)` with complete values and vanishing Cauchy–Riemann derivative extends to a function
holomorphic on `Ω` and continuous on the closure of `Ω`. -/
theorem diffContOnCl_closureExtend_of_conjWirtingerDerivL_eq_zero [CompleteSpace F]
    (hΩ : Convex ℝ (Ω : Set ℂ)) {u : CkHolderSpaceOn 1 α Ω F}
    (hu : conjWirtingerDerivL α Ω F u = 0) : DiffContOnCl ℂ u.closureExtend Ω := by
  refine ⟨fun z hz ↦ ?_, u.continuousOn_closureExtend hΩ⟩
  have hd : DifferentiableAt ℝ u.closureExtend z :=
    u.differentiableOn_closureExtend.differentiableAt (Ω.isOpen.mem_nhds hz)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hd).2 ?_
    ).differentiableWithinAt
  rw [← conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_closureExtend u ⟨z, hz⟩, hu,
    HolderSpace.zero_apply]

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
  rw [L.conjWirtingerDeriv_comp_left (u.differentiableAt_extend z.property),
    conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_extend, ContinuousLinearMap.comp_apply]

variable (α Ω F) in
/-- The Wirtinger derivative `u ↦ ∂u/∂z` as a continuous linear map from `C^{1,α}(Ω, F)` to the
bounded `α`-Hölder functions on `Ω`. It takes the complex-linear part of the first derivative
field and evaluates it at `1` (`TauCeti.wirtingerOne`). -/
def wirtingerDerivL : CkHolderSpaceOn 1 α Ω F →L[ℝ] HolderSpace α Ω F :=
  HolderSpace.compLeftL (wirtingerOne ∘L
      (continuousMultilinearCurryFin1 ℝ ℂ F).toLinearIsometry.toContinuousLinearMap) ∘L
    iteratedFDerivHolderL

/-- The operator `∂/∂z` on `C^{1,α}(Ω)` agrees on `Ω` with the Wirtinger derivative of the
extension by zero. -/
theorem wirtingerDerivL_apply_eq_wirtingerDeriv_extend (u : CkHolderSpaceOn 1 α Ω F) (z : Ω) :
    wirtingerDerivL α Ω F u z = wirtingerDeriv u.extend z 1 := by
  have h : u.iteratedFDeriv 1 z = _root_.iteratedFDeriv ℝ 1 u.extend z :=
    (u.iteratedFDeriv_extend 1 z).symm
  simp [wirtingerDerivL, h, wirtingerDeriv_apply]

/-- The operator `∂/∂z` on `C^{1,α}(Ω)` is determined by the germ at the evaluation point. -/
theorem wirtingerDerivL_apply (u : CkHolderSpaceOn 1 α Ω F) (z : Ω) {g : ℂ → F}
    (hg : u.extend =ᶠ[𝓝 (z : ℂ)] g) :
    wirtingerDerivL α Ω F u z = wirtingerDeriv g z 1 := by
  rw [wirtingerDerivL_apply_eq_wirtingerDeriv_extend, hg.wirtingerDeriv_eq]

/-- The operator `∂/∂z` on `C^{1,α}(Ω)` has operator norm at most one. -/
theorem norm_wirtingerDerivL_le : ‖wirtingerDerivL α Ω F‖ ≤ 1 := by
  have hg : ‖wirtingerOne ∘L
      (continuousMultilinearCurryFin1 ℝ ℂ F).toLinearIsometry.toContinuousLinearMap‖ ≤ 1 :=
    (opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul norm_wirtingerOne_le
        (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _) zero_le_one)
  exact (opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul ((HolderSpace.norm_compLeftL_le _).trans hg)
      norm_iteratedFDerivHolderL_le_one (norm_nonneg _) zero_le_one)

section perturbation

variable (hconv : Convex ℝ (Ω : Set ℂ)) (hα : α ≤ 1)

variable (Ω F) in
/-- The perturbation `u ↦ A ∂u/∂z + B u` of the Cauchy–Riemann operator by the coefficients
`A, B ∈ C^{0,α}(Ω, F →L[ℝ] F)`, on a convex open set `Ω` and for `α ≤ 1`, as a continuous linear
map `C^{1,α}(Ω, F) → C^{0,α}(Ω, F)`. Convexity and `α ≤ 1` make an element of `C^{1,α}(Ω)` an
`α`-Hölder function on `Ω` (`TauCeti.CkHolderSpaceOn.inclusionSuccL`). -/
def wirtingerPerturbationL (A B : HolderSpace α Ω (F →L[ℝ] F)) :
    CkHolderSpaceOn 1 α Ω F →L[ℝ] HolderSpace α Ω F :=
  (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ A ∘L wirtingerDerivL α Ω F +
    (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ B ∘L
      (zeroEquivHolderSpace.toLinearIsometry.toContinuousLinearMap ∘L
        inclusionSuccL (k := 0) hconv hα)

/-- The values of the perturbation `u ↦ A ∂u/∂z + B u`. -/
@[simp]
theorem wirtingerPerturbationL_apply (A B : HolderSpace α Ω (F →L[ℝ] F))
    (u : CkHolderSpaceOn 1 α Ω F) (z : Ω) :
    wirtingerPerturbationL Ω F hconv hα A B u z =
      A z (wirtingerDerivL α Ω F u z) + B z (u z) := by
  simp [wirtingerPerturbationL]

/-- Without coefficients there is no perturbation. -/
@[simp]
theorem wirtingerPerturbationL_zero_zero : wirtingerPerturbationL Ω F hconv hα 0 0 = 0 := by
  ext u z
  simp

/-- The perturbation `u ↦ A ∂u/∂z + B u` has operator norm at most `‖A‖ + 3 ‖B‖`. -/
theorem norm_wirtingerPerturbationL_le (A B : HolderSpace α Ω (F →L[ℝ] F)) :
    ‖wirtingerPerturbationL Ω F hconv hα A B‖ ≤ ‖A‖ + 3 * ‖B‖ := by
  have hA : ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ A‖ ≤ ‖A‖ :=
    opNorm_le_bound _ (norm_nonneg _) fun g ↦ norm_id_compHolder₂_apply_le A g
  have hB : ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ B‖ ≤ ‖B‖ :=
    opNorm_le_bound _ (norm_nonneg _) fun g ↦ norm_id_compHolder₂_apply_le B g
  have hI : ‖zeroEquivHolderSpace.toLinearIsometry.toContinuousLinearMap ∘L
      inclusionSuccL (k := 0) (F := F) hconv hα‖ ≤ 3 :=
    (opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_inclusionSuccL_le hconv hα) (norm_nonneg _) zero_le_one)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul hA norm_wirtingerDerivL_le (norm_nonneg _) (norm_nonneg _))
  · exact (opNorm_comp_le _ _).trans (by
      simpa [mul_comm] using mul_le_mul hB hI (norm_nonneg _) (norm_nonneg _))

/-- The perturbation `u ↦ A ∂u/∂z + B u` depends continuously and linearly on `(A, B)`, so it is
a `C^n` function of the coefficients for every `n`. -/
theorem contDiff_wirtingerPerturbationL {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : HolderSpace α Ω (F →L[ℝ] F) × HolderSpace α Ω (F →L[ℝ] F) ↦
      wirtingerPerturbationL Ω F hconv hα p.1 p.2 :=
  ContDiff.add
    (((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂.contDiff.comp contDiff_fst).clm_comp
      contDiff_const)
    (((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂.contDiff.comp contDiff_snd).clm_comp
      contDiff_const)

end perturbation

end TauCeti.CkHolderSpaceOn
