/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Basic
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
import TauCeti.Analysis.InnerProductSpace.Laplacian.Contraction
import TauCeti.Analysis.Normed.Module.Multilinear.Curry
import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Derivative
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Inclusion

/-!
# The Duhamel heat potential in the parabolic Hölder spaces of every order

For `0 < α < 1`, `T > 0` and a forcing `f ∈ C_{par,b}^{k+α}(E × [0, T])` of any order `k`
(`TauCeti.ParabolicCkHolderSpace`), the Duhamel heat potential

`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`

belongs to `C_{par,b}^{k+2+α}(E × [0, T])`, and `f ↦ w` is a bounded linear map
`TauCeti.ParabolicCkHolderSpace.heatDuhamelPotentialL`. At order `k = 0` it is the order-two
Duhamel operator `TauCeti.heatDuhamelPotentialL`
(`TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace_heatDuhamelPotentialL`). It solves the
heat equation `∂ₜw = Δw + f` with zero initial value: it is the forcing part of the solution
operator of the Cauchy problem for the heat equation at every order of differentiability, gaining
two orders over the forcing.

The fields of `w` are computed from the order-two theory.

* **Spatial derivatives.** For `j ≤ k` the spatial derivative `D_x^j w` is the Duhamel potential
  of `D_x^j f` (`TauCeti.hasFDerivAt_heatDuhamelPotential`), and the order-two theory applied to
  the forcing `D_x^k f ∈ C_b^{α,α/2}` gives the two further derivatives `D_x^(k+1) w` and the
  parabolically `α`-Hölder `D_x^(k+2) w`, with `(1 + α) / 2`-Hölder time slices of `D_x^(k+1) w`.
* **Time derivatives.** Differentiating `∂ₜw = Δw + f` in time and space gives
  `∂ₜ^r D_x^m w = D^m Δ^r w + ∑_{i < r} D^m Δ^(r-1-i) ∂ₜ^i f`
  (`TauCeti.ParabolicCkHolderSpace.mixedDerivL_heatDuhamelPotentialL`). The derivatives of
  iterated Laplacians are contractions of higher derivatives
  (`ContDiff.iteratedFDeriv_iterate_laplacian`), so `D^m Δ^r w` is a contraction of
  `D_x^(m + 2r) w`, and `D^m Δ^(r-1-i) ∂ₜ^i f` one of the field `∂ₜ^i D_x^(m+2(r-1-i)) f` of `f`,
  of order `2r + m - 2`. Contractions are continuous linear, so the boundedness and the Hölder
  conditions of the fields of `w` at the two top orders `k + 2` and `k + 1` come from those of
  `D_x^(k+2) w`, `D_x^(k+1) w` and of the fields of `f` at the orders `k` and `k - 1`.

The map is continuous by the closed graph theorem: the value `w(t, x)` is bounded by `t` times the
supremum of `f`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.heatDuhamelPotentialL`: the Duhamel potential as a continuous
  linear map `C_{par,b}^{k+α}(E × [0, T]) → C_{par,b}^{k+2+α}(E × [0, T])`.
* `TauCeti.ParabolicCkHolderSpace.heatDuhamelPotentialL_apply`: its values.
* `TauCeti.ParabolicCkHolderSpace.heatDuhamelPotentialL_apply_slabMk_zero`: its zero initial value.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL_heatDuhamelPotentialL`: its fields.
* `TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace_heatDuhamelPotentialL`: agreement
  with the order-two Duhamel operator.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (parabolic Hölder spaces of higher order).
-/

public section

noncomputable section

namespace TauCeti

namespace ParabolicCkHolderSpace

open InnerProductSpace Laplacian Set Filter Topology ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α T : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {hT : (0 : ℝ) < T}

variable (E F) in
/-- Shortcut instance for gradients of `n`-multilinear fields. Without it and the following
shortcuts, instance search for the normed structure of these iterated operator spaces exceeds the
default synthesis depth. They are local, and no public statement mentions them. -/
local instance instNormedAddCommGroupGradient (n : ℕ) :
    NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] F) :=
  inferInstance

variable (E F) in
/-- Shortcut instance for scalar operations on gradients of `n`-multilinear fields. -/
local instance instNormedSpaceGradient (n : ℕ) : NormedSpace ℝ (E →L[ℝ] E [×n]→L[ℝ] F) :=
  inferInstance

variable (E F) in
/-- Shortcut instance for Hessians of `n`-multilinear fields. -/
local instance instNormedAddCommGroupHessian (n : ℕ) :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E [×n]→L[ℝ] F) :=
  inferInstance

variable (E F) in
/-- Shortcut instance for scalar operations on Hessians of `n`-multilinear fields. -/
local instance instNormedSpaceHessian (n : ℕ) :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E [×n]→L[ℝ] F) :=
  inferInstance

section Fields

variable (hα₀ : 0 < α) (hα₁ : α < 1) (f : ParabolicCkHolderSpace k α E F hT)

/-! ### The potentials of the spatial derivatives of the forcing -/

/-- The field `D_x^j f`, `j ≤ k`, as a bounded parabolically `α`-Hölder forcing, and zero for
`j > k`. -/
private def forcing (j : ℕ) : HolderSpace α (slab (E := E) 0 T) (E [×j]→L[ℝ] F) :=
  if h : j ≤ k then
    HolderSpace.ofBoundedContinuousFunction (mixedDerivL 0 j f)
      (memHolder_mixedDerivL_of_le hα₁.le f (by omega))
  else 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem forcing_apply {j : ℕ} (h : j ≤ k) (p : slab (E := E) 0 T) :
    forcing hα₁ f j p = mixedDerivL 0 j f p := by
  rw [forcing, dite_eq_left h, HolderSpace.ofBoundedContinuousFunction_apply]

/-- The Duhamel potential of `D_x^j f`, in the order-two space. -/
private def potential (j : ℕ) : ParabolicC2HolderSpace α E (E [×j]→L[ℝ] F) hT :=
  TauCeti.heatDuhamelPotentialL hα₀ hα₁ hT (forcing hα₁ f j)

private theorem potential_apply (j : ℕ) (p : slab (E := E) 0 T) :
    potential hα₀ hα₁ f j p = heatDuhamelPotential
      (fun s x ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f j) x s)
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space :=
  TauCeti.heatDuhamelPotentialL_apply _ p

/-- Below the top order, the spatial derivative of the potential of `D_x^j f` is the potential of
`D_x^(j+1) f`, curried on the left. -/
private theorem hasFDerivAt_potential {j : ℕ} (h : j < k) (t : Icc (0 : ℝ) T) (x : E) :
    HasFDerivAt (fun y ↦ potential hα₀ hα₁ f j (slabMk y t))
      (potential hα₀ hα₁ f (j + 1) (slabMk x t)).curryLeft x := by
  let L : (E [×(j + 1)]→L[ℝ] F) ≃L[ℝ] (E →L[ℝ] E [×j]→L[ℝ] F) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).toContinuousLinearEquiv
  have hd : ∀ (s : ℝ) (y : E), HasFDerivAt
      (fun x ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f j) x s)
      (L (ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f (j + 1)) y s)) y := by
    intro s y
    simp only [L, ParabolicC2HolderSpace.timeExtension_def, forcing_apply hα₁ f h.le,
      forcing_apply hα₁ f (Nat.succ_le_of_lt h), LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      continuousMultilinearCurryLeftEquiv_eq_curryLeft]
    exact f.hasFDerivAt_mixedDerivL (by omega) _ y
  have hc : ∀ s : ℝ, Continuous fun y ↦
      L (ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f (j + 1)) y s) :=
    fun s ↦ L.continuous.comp ((ParabolicC2HolderSpace.continuous_timeExtension T.coe_nonneg
      (forcing hα₁ f (j + 1)).continuous).comp (continuous_const.prodMk continuous_id))
  have hw := hasFDerivAt_heatDuhamelPotential
    (f := fun s x ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f j) x s)
    (f' := fun s y ↦
      L (ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f (j + 1)) y s))
    (ParabolicC2HolderSpace.continuous_timeExtension T.coe_nonneg
      (forcing hα₁ f j).continuous).stronglyMeasurable
    ((L.continuous.comp (ParabolicC2HolderSpace.continuous_timeExtension T.coe_nonneg
      (forcing hα₁ f (j + 1)).continuous)).stronglyMeasurable)
    (fun s _ y ↦ ParabolicC2HolderSpace.norm_timeExtension_holderSpace_le T.coe_nonneg _ s y)
    (fun s _ y ↦ by
      rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
      exact ParabolicC2HolderSpace.norm_timeExtension_holderSpace_le T.coe_nonneg _ s y)
    (fun s _ y ↦ hd s y) (fun s _ ↦ hc s) t.property.1 x
  have hcomm := heatDuhamelPotential_comp_continuousLinearEquiv L
    (fun s y ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f (j + 1)) y s)
    t x
  rw [hcomm] at hw
  simp only [potential_apply, space_slabMk, time_slabMk]
  exact hw

/-- The Duhamel potential `w(t, ·)` of `f` on the time slice `t`. -/
private def slice (t : Icc (0 : ℝ) T) (y : E) : F :=
  (potential hα₀ hα₁ f 0 (slabMk y t)).curry0

/-- Up to order `k`, the spatial derivatives of `w(t, ·)` are the potentials of the spatial
derivatives of `f`. -/
private theorem hasFTaylorSeriesUpTo_slice (t : Icc (0 : ℝ) T) :
    HasFTaylorSeriesUpTo k (slice hα₀ hα₁ f t) fun y j ↦ potential hα₀ hα₁ f j (slabMk y t) where
  zero_eq _ := rfl
  fderiv j hj x := hasFDerivAt_potential hα₀ hα₁ f (by exact_mod_cast hj) t x
  cont j _ := (ParabolicC2HolderSpace.valueL (potential hα₀ hα₁ f j)).continuous.comp
    (continuous_slabMk.comp (continuous_id.prodMk continuous_const))

private theorem iteratedFDeriv_slice_of_le {n : ℕ} (h : n ≤ k) (t : Icc (0 : ℝ) T) (y : E) :
    iteratedFDeriv ℝ n (slice hα₀ hα₁ f t) y = potential hα₀ hα₁ f n (slabMk y t) :=
  ((hasFTaylorSeriesUpTo_slice hα₀ hα₁ f t).eq_iteratedFDeriv (by exact_mod_cast h) y).symm

variable (k E F) in
/-- The currying of the derivative of order `k + 1`. -/
private abbrev curryOne : (E →L[ℝ] E [×k]→L[ℝ] F) ≃ₗᵢ[ℝ] E [×(k + 1)]→L[ℝ] F :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F).symm

variable (k E F) in
/-- The currying of the derivative of order `k + 2`. -/
private def curryTwo : (E →L[ℝ] E →L[ℝ] E [×k]→L[ℝ] F) →L[ℝ] E [×(k + 2)]→L[ℝ] F :=
  ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 2) ↦ E) F).symm :
      (E →L[ℝ] E [×(k + 1)]→L[ℝ] F) →L[ℝ] E [×(k + 2)]→L[ℝ] F).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E [×k]→L[ℝ] F) (E [×(k + 1)]→L[ℝ] F)
      (curryOne k E F : (E →L[ℝ] E [×k]→L[ℝ] F) →L[ℝ] _))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem curryTwo_apply (A : E →L[ℝ] E →L[ℝ] E [×k]→L[ℝ] F) :
    curryTwo k E F A = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 2) ↦ E) F).symm
      ((curryOne k E F : (E →L[ℝ] E [×k]→L[ℝ] F) →L[ℝ] _).comp A) :=
  (rfl)

/-- The derivative of order `k + 1` of `w(t, ·)` is the gradient of the potential of `D_x^k f`. -/
private theorem iteratedFDeriv_slice_succ (t : Icc (0 : ℝ) T) (y : E) :
    iteratedFDeriv ℝ (k + 1) (slice hα₀ hα₁ f t) y =
      curryOne k E F
        (ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) (slabMk y t)) := by
  have h : iteratedFDeriv ℝ k (slice hα₀ hα₁ f t) = fun y ↦ potential hα₀ hα₁ f k (slabMk y t) :=
    funext (iteratedFDeriv_slice_of_le hα₀ hα₁ f le_rfl t)
  rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, h,
    ParabolicC2HolderSpace.fderiv_eq]

/-- The derivative of order `k + 2` of `w(t, ·)` is the Hessian of the potential of `D_x^k f`. -/
private theorem iteratedFDeriv_slice_succ_succ (t : Icc (0 : ℝ) T) (y : E) :
    iteratedFDeriv ℝ (k + 2) (slice hα₀ hα₁ f t) y =
      curryTwo k E F (ParabolicC2HolderSpace.spatialSecondFDerivL (potential hα₀ hα₁ f k)
        (slabMk y t)) := by
  have h : iteratedFDeriv ℝ (k + 1) (slice hα₀ hα₁ f t) = fun y ↦
      curryOne k E F (ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) (slabMk y t)) :=
    funext (iteratedFDeriv_slice_succ hα₀ hα₁ f t)
  have hd : HasFDerivAt (fun y ↦ curryOne k E F
      (ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) (slabMk y t)))
      ((curryOne k E F : (E →L[ℝ] E [×k]→L[ℝ] F) →L[ℝ] _).comp
        (ParabolicC2HolderSpace.spatialSecondFDerivL (potential hα₀ hα₁ f k) (slabMk y t))) y :=
    (curryOne k E F).toContinuousLinearEquiv.hasFDerivAt.comp y
      ((potential hα₀ hα₁ f k).hasSpatialSecondFDerivAt t y)
  rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, h, hd.fderiv, curryTwo_apply]

private theorem continuous_slice_iteratedFDeriv {n : ℕ} (h : n ≤ k + 2) (t : Icc (0 : ℝ) T) :
    Continuous (iteratedFDeriv ℝ n (slice hα₀ hα₁ f t)) := by
  have hs : Continuous fun y : E ↦ slabMk y t :=
    continuous_slabMk.comp (continuous_id.prodMk continuous_const)
  rcases (show n ≤ k ∨ n = k + 1 ∨ n = k + 2 by omega) with hn | rfl | rfl
  · rw [funext (iteratedFDeriv_slice_of_le hα₀ hα₁ f hn t)]
    exact (ParabolicC2HolderSpace.valueL (potential hα₀ hα₁ f n)).continuous.comp hs
  · rw [funext (iteratedFDeriv_slice_succ hα₀ hα₁ f t)]
    exact (curryOne k E F).continuous.comp
      ((ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k)).continuous.comp hs)
  · rw [funext (iteratedFDeriv_slice_succ_succ hα₀ hα₁ f t)]
    exact (curryTwo k E F).continuous.comp
      ((ParabolicC2HolderSpace.spatialSecondFDerivL (potential hα₀ hα₁ f k)).continuous.comp hs)

private theorem differentiable_slice_iteratedFDeriv {n : ℕ} (h : n < k + 2)
    (t : Icc (0 : ℝ) T) : Differentiable ℝ (iteratedFDeriv ℝ n (slice hα₀ hα₁ f t)) := by
  intro y
  rcases (show n ≤ k ∨ n = k + 1 by omega) with hn | rfl
  · rw [funext (iteratedFDeriv_slice_of_le hα₀ hα₁ f hn t)]
    exact ((potential hα₀ hα₁ f n).hasSpatialFDerivAt t y).differentiableAt
  · rw [funext (iteratedFDeriv_slice_succ hα₀ hα₁ f t)]
    exact ((curryOne k E F).toContinuousLinearEquiv.hasFDerivAt.comp y
      ((potential hα₀ hα₁ f k).hasSpatialSecondFDerivAt t y)).differentiableAt

/-- Every slice `w(t, ·)` is of class `C^(k+2)`. -/
private theorem contDiff_slice (t : Icc (0 : ℝ) T) :
    ContDiff ℝ (k + 2 : ℕ) (slice hα₀ hα₁ f t) :=
  contDiff_iff_continuous_differentiable.2
    ⟨fun n hn ↦ continuous_slice_iteratedFDeriv hα₀ hα₁ f (by exact_mod_cast hn) t,
      fun n hn ↦ differentiable_slice_iteratedFDeriv hα₀ hα₁ f (by exact_mod_cast hn) t⟩

/-! ### The fields -/

/-- The spatial derivative `D_x^n w(x, t)` of the potential. -/
private def derivField (n : ℕ) (p : slab (E := E) 0 T) : E [×n]→L[ℝ] F :=
  iteratedFDeriv ℝ n (slice hα₀ hα₁ f (slabTime p)) (p : ParabolicSpaceTime E).space

private theorem derivField_slabMk (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    derivField hα₀ hα₁ f n (slabMk x t) = iteratedFDeriv ℝ n (slice hα₀ hα₁ f t) x := by
  rw [derivField, slabTime_slabMk, space_slabMk]

/-- The spatial derivatives of the potential up to order `k + 2` form bounded continuous fields. -/
private theorem exists_coe_eq_derivField {n : ℕ} (h : n ≤ k + 2) :
    ∃ g : slab (E := E) 0 T →ᵇ (E [×n]→L[ℝ] F), ⇑g = derivField hα₀ hα₁ f n := by
  rcases (show n ≤ k ∨ n = k + 1 ∨ n = k + 2 by omega) with hn | rfl | rfl
  · refine ⟨ParabolicC2HolderSpace.valueL (potential hα₀ hα₁ f n), funext fun p ↦ ?_⟩
    rw [← slabMk_space_slabTime p, derivField_slabMk, iteratedFDeriv_slice_of_le hα₀ hα₁ f hn,
      ParabolicC2HolderSpace.valueL_apply]
  · refine ⟨(curryOne k E F : _ →L[ℝ] _).compLeftContinuousBounded _
      (ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k)), funext fun p ↦ ?_⟩
    rw [← slabMk_space_slabTime p, derivField_slabMk, iteratedFDeriv_slice_succ,
      ContinuousLinearMap.compLeftContinuousBounded_apply, LinearIsometryEquiv.coe_coe'']
  · refine ⟨(curryTwo k E F).compLeftContinuousBounded _
      (ParabolicC2HolderSpace.spatialSecondFDerivL
        (potential hα₀ hα₁ f k)).toBoundedContinuousFunction, funext fun p ↦ ?_⟩
    rw [← slabMk_space_slabTime p, derivField_slabMk, iteratedFDeriv_slice_succ_succ,
      ContinuousLinearMap.compLeftContinuousBounded_apply,
      HolderSpace.toBoundedContinuousFunction_apply]

/-- The spatial derivative `D_x^n w` of the potential as a bounded continuous field, for
`n ≤ k + 2`, and zero otherwise. -/
private def derivFieldBCF (n : ℕ) : slab (E := E) 0 T →ᵇ (E [×n]→L[ℝ] F) :=
  if h : n ≤ k + 2 then (exists_coe_eq_derivField hα₀ hα₁ f h).choose else 0

private theorem derivFieldBCF_apply {n : ℕ} (h : n ≤ k + 2) (p : slab (E := E) 0 T) :
    derivFieldBCF hα₀ hα₁ f n p = derivField hα₀ hα₁ f n p := by
  rw [derivFieldBCF, dite_eq_left h]
  exact congrFun (exists_coe_eq_derivField hα₀ hα₁ f h).choose_spec p

/-- The term `D^m Δ^r w` of the field `∂ₜ^r D_x^m w`, as the `r`-fold contraction of `D_x^(m+2r) w`.
-/
private def heatField (r m : ℕ) : slab (E := E) 0 T →ᵇ (E [×m]→L[ℝ] F) :=
  (iteratedTraceLastTwoL E F r m).compLeftContinuousBounded _
    (derivFieldBCF hα₀ hα₁ f (m + 2 * r))

/-- The term `D^m Δ^a ∂ₜ^i f` of a field of the potential, as the `a`-fold contraction of the field
`∂ₜ^i D_x^(m+2a) f` of `f`. -/
private def forcingField (m i a : ℕ) : slab (E := E) 0 T →ᵇ (E [×m]→L[ℝ] F) :=
  (iteratedTraceLastTwoL E F a m).compLeftContinuousBounded _ (mixedDerivL i (m + 2 * a) f)

/-- The field `∂ₜ^r D_x^m w = D^m Δ^r w + ∑_{i < r} D^m Δ^(r-1-i) ∂ₜ^i f` of the potential. -/
private def field (r m : ℕ) : slab (E := E) 0 T →ᵇ (E [×m]→L[ℝ] F) :=
  heatField hα₀ hα₁ f r m + ∑ i ∈ Finset.range r, forcingField f m i (r - 1 - i)

private theorem field_apply (r m : ℕ) (p : slab (E := E) 0 T) :
    field hα₀ hα₁ f r m p =
      heatField hα₀ hα₁ f r m p + ∑ i ∈ Finset.range r, forcingField f m i (r - 1 - i) p := by
  simp only [field, FunLike.coe_add, FunLike.coe_sum, Pi.add_apply, Finset.sum_apply]

private theorem heatField_slabMk {r m : ℕ} (h : m + 2 * r ≤ k + 2) (x : E)
    (t : Icc (0 : ℝ) T) :
    heatField hα₀ hα₁ f r m (slabMk x t) = iteratedFDeriv ℝ m (Δ^[r] (slice hα₀ hα₁ f t)) x := by
  rw [heatField, ContinuousLinearMap.compLeftContinuousBounded_apply,
    derivFieldBCF_apply hα₀ hα₁ f h, derivField_slabMk,
    ContDiff.iteratedFDeriv_iterate_laplacian
      ((contDiff_slice hα₀ hα₁ f t).of_le (by exact_mod_cast h))]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem forcingField_slabMk {m i a : ℕ} (h : 2 * i + (m + 2 * a) ≤ k) (x : E)
    (t : Icc (0 : ℝ) T) :
    forcingField f m i a (slabMk x t) =
      iteratedFDeriv ℝ m (Δ^[a] fun y ↦ (mixedDerivL i 0 f (slabMk y t)).curry0) x := by
  rw [forcingField, ContinuousLinearMap.compLeftContinuousBounded_apply,
    ContDiff.iteratedFDeriv_iterate_laplacian
      ((f.hasFTaylorSeriesUpTo_mixedDerivL i t).contDiff.of_le
        (Nat.cast_le.2 (by omega : m + 2 * a ≤ k - 2 * i))),
    f.iteratedFDeriv_mixedDerivL_zero h]

/-! ### Spatial derivatives of the fields -/

private theorem hasFDerivAt_heatField {r m : ℕ} (h : m + 2 * r + 1 ≤ k + 2) (t : Icc (0 : ℝ) T)
    (x : E) : HasFDerivAt (fun y ↦ heatField hα₀ hα₁ f r m (slabMk y t))
      (heatField hα₀ hα₁ f r (m + 1) (slabMk x t)).curryLeft x := by
  rw [funext fun y ↦ heatField_slabMk hα₀ hα₁ f (by omega) y t,
    heatField_slabMk hα₀ hα₁ f (by omega : m + 1 + 2 * r ≤ k + 2)]
  exact ((contDiff_slice hα₀ hα₁ f t).iterate_laplacian (m := (m + 1 : ℕ))
    (by norm_cast; omega)).hasFDerivAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m) x

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem hasFDerivAt_forcingField {m i a : ℕ} (h : 2 * i + (m + 2 * a) + 1 ≤ k)
    (t : Icc (0 : ℝ) T) (x : E) : HasFDerivAt (fun y ↦ forcingField f m i a (slabMk y t))
      (forcingField f (m + 1) i a (slabMk x t)).curryLeft x := by
  rw [funext fun y ↦ forcingField_slabMk f (by omega) y t,
    forcingField_slabMk f (by omega : 2 * i + (m + 1 + 2 * a) ≤ k)]
  exact ((f.hasFTaylorSeriesUpTo_mixedDerivL i t).contDiff.iterate_laplacian (m := (m + 1 : ℕ))
    (by norm_cast; exact Nat.cast_le.2 (by omega))).hasFDerivAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self m) x

private theorem hasFDerivAt_field {r m : ℕ} (h : 2 * r + m + 1 ≤ k + 2) (t : Icc (0 : ℝ) T)
    (x : E) : HasFDerivAt (fun y ↦ field hα₀ hα₁ f r m (slabMk y t))
      (field hα₀ hα₁ f r (m + 1) (slabMk x t)).curryLeft x := by
  simp only [field_apply]
  have hcurry : (heatField hα₀ hα₁ f r (m + 1) (slabMk x t) +
      ∑ i ∈ Finset.range r, forcingField f (m + 1) i (r - 1 - i) (slabMk x t)).curryLeft =
      (heatField hα₀ hα₁ f r (m + 1) (slabMk x t)).curryLeft +
        ∑ i ∈ Finset.range r, (forcingField f (m + 1) i (r - 1 - i) (slabMk x t)).curryLeft :=
    by
      ext h v
      simp only [ContinuousMultilinearMap.curryLeft_apply, add_apply, sum_apply]
  rw [hcurry]
  refine (hasFDerivAt_heatField hα₀ hα₁ f (r := r) (m := m) (by omega) t x).add
    (HasFDerivAt.fun_sum fun i hi ↦
      hasFDerivAt_forcingField (m := m) (i := i) (a := r - 1 - i) f ?_ t x)
  have := Finset.mem_range.1 hi
  omega

/-! ### Time derivatives of the fields -/

/-- Below the top two orders, the time derivative of `D_x^n w` is
`Δ D_x^n w + D_x^n f`, with `Δ D_x^n w` the contraction of `D_x^(n+2) w`. -/
private theorem hasDerivWithinAt_derivFieldBCF {n : ℕ} (h : n ≤ k) (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hT.le (derivFieldBCF hα₀ hα₁ f n) x)
      (traceLastTwoL E F n (derivFieldBCF hα₀ hα₁ f (n + 2) (slabMk x t)) +
        mixedDerivL 0 n f (slabMk x t)) (Icc 0 T) t := by
  have hfield : ⇑(derivFieldBCF hα₀ hα₁ f n) = potential hα₀ hα₁ f n := funext fun p ↦ by
    rw [derivFieldBCF_apply hα₀ hα₁ f (by omega), ← slabMk_space_slabTime p, derivField_slabMk,
      iteratedFDeriv_slice_of_le hα₀ hα₁ f h]
  have hΔ : Δ (fun y ↦ potential hα₀ hα₁ f n (slabMk y t)) x =
      traceLastTwoL E F n (derivFieldBCF hα₀ hα₁ f (n + 2) (slabMk x t)) := by
    rw [← funext (iteratedFDeriv_slice_of_le hα₀ hα₁ f h t), derivFieldBCF_apply hα₀ hα₁ f
      (by omega), derivField_slabMk, ContDiff.laplacian_iteratedFDeriv_eq_traceLastTwoL
      ((contDiff_slice hα₀ hα₁ f t).of_le (by exact_mod_cast (by omega : n + 2 ≤ k + 2)))]
  have hd := (potential hα₀ hα₁ f n).hasTimeDerivWithinAt x t
  rw [potential, TauCeti.timeDerivL_heatDuhamelPotentialL_eq_laplacian_add, ← potential,
    slabTime_slabMk, space_slabMk, hΔ, forcing_apply hα₁ f h] at hd
  rw [hfield]
  exact hd

private theorem hasDerivWithinAt_heatField {r m : ℕ} (h : m + 2 * r ≤ k) (x : E)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hT.le (heatField hα₀ hα₁ f r m) x)
      (heatField hα₀ hα₁ f (r + 1) m (slabMk x t) + forcingField f m 0 r (slabMk x t))
      (Icc 0 T) t := by
  have hext : ParabolicC2HolderSpace.timeExtension hT.le (heatField hα₀ hα₁ f r m) x =
      iteratedTraceLastTwoL E F r m ∘
        ParabolicC2HolderSpace.timeExtension hT.le (derivFieldBCF hα₀ hα₁ f (m + 2 * r)) x := by
    funext s
    simp only [ParabolicC2HolderSpace.timeExtension_def, heatField,
      ContinuousLinearMap.compLeftContinuousBounded_apply, Function.comp_apply]
  have hd := (iteratedTraceLastTwoL E F r m).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (hasDerivWithinAt_derivFieldBCF hα₀ hα₁ f h x t)
  rw [hext]
  convert hd using 1
  rw [map_add, heatField, forcingField, ContinuousLinearMap.compLeftContinuousBounded_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply, iteratedTraceLastTwoL_succ,
    ContinuousLinearMap.comp_apply]
  -- The orders `m + 2 * (r + 1)` and `m + 2 * r + 2` agree by computation.
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem hasDerivWithinAt_forcingField {m i a : ℕ} (h : 2 * i + (m + 2 * a) + 2 ≤ k)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hT.le (forcingField f m i a) x)
      (forcingField f m (i + 1) a (slabMk x t)) (Icc 0 T) t := by
  have hext : ParabolicC2HolderSpace.timeExtension hT.le (forcingField f m i a) x =
      iteratedTraceLastTwoL E F a m ∘
        ParabolicC2HolderSpace.timeExtension hT.le (mixedDerivL i (m + 2 * a) f) x := by
    funext s
    simp only [ParabolicC2HolderSpace.timeExtension_def, forcingField,
      ContinuousLinearMap.compLeftContinuousBounded_apply, Function.comp_apply]
  rw [hext]
  exact (iteratedTraceLastTwoL E F a m).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (f.hasDerivWithinAt_mixedDerivL h x t)

private theorem hasDerivWithinAt_field {r m : ℕ} (h : 2 * r + m + 2 ≤ k + 2) (x : E)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hT.le (field hα₀ hα₁ f r m) x)
      (field hα₀ hα₁ f (r + 1) m (slabMk x t)) (Icc 0 T) t := by
  have hsum : field hα₀ hα₁ f (r + 1) m (slabMk x t) =
      heatField hα₀ hα₁ f (r + 1) m (slabMk x t) + forcingField f m 0 r (slabMk x t) +
        ∑ i ∈ Finset.range r, forcingField f m (i + 1) (r - 1 - i) (slabMk x t) := by
    simp only [field_apply, Finset.sum_range_succ', add_assoc]
    rw [add_comm (∑ i ∈ Finset.range r, _)]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show r + 1 - 1 - (i + 1) = r - 1 - i by omega]
  have hext : ParabolicC2HolderSpace.timeExtension hT.le (field hα₀ hα₁ f r m) x =
      ParabolicC2HolderSpace.timeExtension hT.le (heatField hα₀ hα₁ f r m) x +
        ∑ i ∈ Finset.range r,
          ParabolicC2HolderSpace.timeExtension hT.le (forcingField f m i (r - 1 - i)) x := by
    funext s
    simp only [ParabolicC2HolderSpace.timeExtension_def, field_apply, Pi.add_apply,
      Finset.sum_apply]
  rw [hext, hsum]
  refine (hasDerivWithinAt_heatField hα₀ hα₁ f (r := r) (m := m) (by omega) x t).add
    (HasDerivWithinAt.sum fun i hi ↦
      hasDerivWithinAt_forcingField (m := m) (i := i) (a := r - 1 - i) f ?_ x t)
  have := Finset.mem_range.1 hi
  omega

/-! ### The Hölder conditions at the two top orders -/

/-- The time slices of `D_x^(k+1) w`, the gradient of the potential of `D_x^k f`, are uniformly
`(1 + α) / 2`-Hölder. -/
private theorem exists_holderWith_derivFieldBCF {n : ℕ} (hn : n = k + 1) :
    ∃ C, ∀ x : E, HolderWith C ((1 + α) / 2)
      fun t : Icc (0 : ℝ) T ↦ derivFieldBCF hα₀ hα₁ f n (slabMk x t) := by
  subst hn
  refine ⟨(timeEHolderNorm ((1 + α) / 2)
      (ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) : _ → _)).toNNReal,
    fun x ↦ ?_⟩
  have hgrad : HolderWith
      (timeEHolderNorm ((1 + α) / 2)
        (ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) : _ → _)).toNNReal
      ((1 + α) / 2) fun t : Icc (0 : ℝ) T ↦
        ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) (slabMk x t) := by
    intro t s
    rw [ENNReal.coe_toNNReal (potential hα₀ hα₁ f k).timeEHolderNorm_spatialFDeriv_lt_top.ne]
    exact timeEHolderNorm_le_iff.1 le_rfl x t s
  have heq : (fun t : Icc (0 : ℝ) T ↦ derivFieldBCF hα₀ hα₁ f (k + 1) (slabMk x t)) =
      curryOne k E F ∘ fun t ↦
        ParabolicC2HolderSpace.spatialFDerivL (potential hα₀ hα₁ f k) (slabMk x t) := by
    funext t
    rw [Function.comp_apply, derivFieldBCF_apply hα₀ hα₁ f (by omega), derivField_slabMk,
      iteratedFDeriv_slice_succ]
  rw [heq]
  exact (curryOne k E F).isometry.comp_holderWith hgrad

/-- `D_x^(k+2) w`, the Hessian of the potential of `D_x^k f`, is parabolically `α`-Hölder. -/
private theorem memHolder_derivFieldBCF {n : ℕ} (hn : n = k + 2) :
    MemHolder α (derivFieldBCF hα₀ hα₁ f n : slab (E := E) 0 T → E [×n]→L[ℝ] F) := by
  subst hn
  have heq : ⇑(derivFieldBCF hα₀ hα₁ f (k + 2)) = HolderSpace.compLeftL (curryTwo k E F)
      (ParabolicC2HolderSpace.spatialSecondFDerivL (potential hα₀ hα₁ f k)) := funext fun p ↦ by
    rw [derivFieldBCF_apply hα₀ hα₁ f le_rfl, ← slabMk_space_slabTime p, derivField_slabMk,
      iteratedFDeriv_slice_succ_succ, HolderSpace.compLeftL_apply]
  have hm := (HolderSpace.compLeftL (curryTwo k E F)
    (ParabolicC2HolderSpace.spatialSecondFDerivL (potential hα₀ hα₁ f k))).memHolder
  rwa [HolderSpace.coe_toBoundedContinuousFunction, ← heq] at hm

/-- At the order `k + 1`, the time slices of the fields are uniformly `(1 + α) / 2`-Hölder. -/
private theorem exists_holderWith_field {r m : ℕ} (h : 2 * r + m + 1 = k + 2) :
    ∃ C, ∀ x : E, HolderWith C ((1 + α) / 2)
      fun t : Icc (0 : ℝ) T ↦ field hα₀ hα₁ f r m (slabMk x t) := by
  obtain ⟨C, hC⟩ := exists_holderWith_derivFieldBCF hα₀ hα₁ f (n := m + 2 * r) (by omega)
  -- The time slices of the fields `∂ₜ^i D_x^(m+2a) f` of order `k - 1`.
  have hforce : ∀ i a, 2 * i + (m + 2 * a) + 1 = k → ∀ x : E,
      HolderWith ‖timeSliceL i (m + 2 * a) f‖₊ ((1 + α) / 2)
        fun t : Icc (0 : ℝ) T ↦ mixedDerivL i (m + 2 * a) f (slabMk x t) := fun i a hk x ↦ by
    have hslice := (timeSliceL i (m + 2 * a) f x).holderWith_nnnorm.mono
      (show ‖timeSliceL i (m + 2 * a) f x‖₊ ≤ ‖timeSliceL i (m + 2 * a) f‖₊ from
        lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)
    rwa [coe_timeSliceL f hk x] at hslice
  refine ⟨‖iteratedTraceLastTwoL E F r m‖₊ * C + ∑ i ∈ Finset.range r,
    ‖iteratedTraceLastTwoL E F (r - 1 - i) m‖₊ * ‖timeSliceL i (m + 2 * (r - 1 - i)) f‖₊,
    fun x ↦ ?_⟩
  simp only [field_apply, heatField, forcingField,
    ContinuousLinearMap.compLeftContinuousBounded_apply]
  refine HolderWith.add (ContinuousLinearMap.holderWith_comp _ (hC x))
    (HolderWith.sum fun i hi ↦ ?_)
  have := Finset.mem_range.1 hi
  exact ContinuousLinearMap.holderWith_comp _ (hforce i (r - 1 - i) (by omega) x)

/-- At the order `k + 2`, the fields are parabolically `α`-Hölder. -/
private theorem memHolder_field {r m : ℕ} (h : 2 * r + m = k + 2) :
    MemHolder α (field hα₀ hα₁ f r m : slab (E := E) 0 T → E [×m]→L[ℝ] F) := by
  have hheat := (memHolder_derivFieldBCF hα₀ hα₁ f (n := m + 2 * r) (by omega)).holderWith
  have hforce : ∀ i ∈ Finset.range r, HolderWith (‖iteratedTraceLastTwoL E F (r - 1 - i) m‖₊ *
      nnHolderNorm α (mixedDerivL i (m + 2 * (r - 1 - i)) f : slab (E := E) 0 T → _)) α
      fun p ↦ iteratedTraceLastTwoL E F (r - 1 - i) m (mixedDerivL i (m + 2 * (r - 1 - i)) f p) :=
    fun i hi ↦ by
      have := Finset.mem_range.1 hi
      exact ContinuousLinearMap.holderWith_comp _ (f.memHolder_mixedDerivL (by omega)).holderWith
  have hfun : ⇑(field hα₀ hα₁ f r m) =
      (fun p ↦ iteratedTraceLastTwoL E F r m (derivFieldBCF hα₀ hα₁ f (m + 2 * r) p)) +
        fun p ↦ ∑ i ∈ Finset.range r,
          iteratedTraceLastTwoL E F (r - 1 - i) m (mixedDerivL i (m + 2 * (r - 1 - i)) f p) := by
    funext p
    simp only [field_apply, heatField, forcingField, Pi.add_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply]
  rw [hfun]
  have hheat' : HolderWith (‖iteratedTraceLastTwoL E F r m‖₊ *
      nnHolderNorm α (derivFieldBCF hα₀ hα₁ f (m + 2 * r) : slab (E := E) 0 T → _)) α
      fun p ↦ iteratedTraceLastTwoL E F r m (derivFieldBCF hα₀ hα₁ f (m + 2 * r) p) :=
    ContinuousLinearMap.holderWith_comp _ hheat
  exact ⟨_, hheat'.add (HolderWith.sum hforce)⟩

/-! ### The potential in the space of order `k + 2` -/

/-- The Duhamel potential of `f`, as an element of the space of order `k + 2`. -/
private def potentialK : ParabolicCkHolderSpace (k + 2) α E F hT :=
  mk (field hα₀ hα₁ f) (fun _ _ h t x ↦ hasFDerivAt_field hα₀ hα₁ f h t x)
    (fun _ _ h x t ↦ hasDerivWithinAt_field hα₀ hα₁ f h x t)
    (fun _ _ h ↦ exists_holderWith_field hα₀ hα₁ f h)
    (fun _ _ h ↦ memHolder_field hα₀ hα₁ f h)

private theorem potentialK_apply (p : slab (E := E) 0 T) :
    potentialK hα₀ hα₁ f p = (potential hα₀ hα₁ f 0 p).curry0 := by
  simp [potentialK, field_apply, heatField, derivFieldBCF_apply hα₀ hα₁ f (by omega : 0 ≤ k + 2),
    derivField, slice]

private theorem potentialK_apply_eq_heatDuhamelPotential (p : slab (E := E) 0 T) :
    potentialK hα₀ hα₁ f p = heatDuhamelPotential
      (fun s x ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  have hf : (fun s x ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg f x s) =
      fun s x ↦ (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv
        (ParabolicC2HolderSpace.timeExtension T.coe_nonneg (forcing hα₁ f 0) x s) := by
    funext s x
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      continuousMultilinearCurryFin0_apply, ParabolicC2HolderSpace.timeExtension_def,
      forcing_apply hα₁ f (Nat.zero_le k), mixedDerivL_zero_zero_apply]
  rw [potentialK_apply, potential_apply, hf, heatDuhamelPotential_comp_continuousLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, continuousMultilinearCurryFin0_apply,
    ContinuousMultilinearMap.curry0_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem forcing_add (g : ParabolicCkHolderSpace k α E F hT) (j : ℕ) :
    forcing hα₁ (f + g) j = forcing hα₁ f j + forcing hα₁ g j := by
  by_cases h : j ≤ k
  · refine HolderSpace.ext fun p ↦ ?_
    rw [HolderSpace.add_apply, forcing_apply hα₁ _ h, forcing_apply hα₁ _ h,
      forcing_apply hα₁ _ h, map_add, add_apply]
  · simp only [forcing, dite_eq_right h, add_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem forcing_smul (c : ℝ) (j : ℕ) :
    forcing hα₁ (c • f) j = c • forcing hα₁ f j := by
  by_cases h : j ≤ k
  · refine HolderSpace.ext fun p ↦ ?_
    rw [HolderSpace.smul_apply, forcing_apply hα₁ _ h, forcing_apply hα₁ _ h, map_smul,
      smul_apply]
  · simp only [forcing, dite_eq_right h, smul_zero]

end Fields

/-- The Duhamel potential, as a linear map into the space of order `k + 2`. -/
private def potentialLinear (hα₀ : 0 < α) (hα₁ : α < 1) :
    ParabolicCkHolderSpace k α E F hT →ₗ[ℝ] ParabolicCkHolderSpace (k + 2) α E F hT where
  toFun := potentialK hα₀ hα₁
  map_add' f g := ext fun p ↦ by
    simp only [coe_add, Pi.add_apply, potentialK_apply, potential, forcing_add, map_add,
      ContinuousMultilinearMap.curry0_apply, add_apply]
  map_smul' c f := ext fun p ↦ by
    simp only [coe_smul, Pi.smul_apply, potentialK_apply, potential, forcing_smul, map_smul,
      RingHom.id_apply, ContinuousMultilinearMap.curry0_apply, smul_apply]

/-- The value of the potential at time `t` is at most `t` times the supremum of the forcing. -/
private theorem norm_potentialK_apply_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : ParabolicCkHolderSpace k α E F hT)
    (p : slab (E := E) 0 T) : ‖potentialK hα₀ hα₁ f p‖ ≤ ‖f‖ * T := by
  have hp := (slabTime p).property
  rw [coe_slabTime] at hp
  rw [potentialK_apply_eq_heatDuhamelPotential]
  refine (norm_heatDuhamelPotential_le hp.1
    (MeasureTheory.ae_of_all _ fun s ↦ MeasureTheory.ae_of_all _ fun y ↦ ?_) _).trans
    (mul_le_mul_of_nonneg_left hp.2 (norm_nonneg f))
  rw [ParabolicC2HolderSpace.timeExtension_def]
  exact f.norm_apply_le _

/-- **Closed graph.** If `fₙ → f` and the potentials of `fₙ` converge to `w`, then `w` is the
potential of `f`: the values converge pointwise to both. -/
private theorem eq_potentialK_of_tendsto (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ℕ → ParabolicCkHolderSpace k α E F hT)
    (f : ParabolicCkHolderSpace k α E F hT) (w : ParabolicCkHolderSpace (k + 2) α E F hT)
    (hu : Tendsto u atTop (𝓝 f)) (hw : Tendsto (potentialLinear hα₀ hα₁ ∘ u) atTop (𝓝 w)) :
    w = potentialLinear hα₀ hα₁ f := by
  ext p
  have h₁ : Tendsto (fun n ↦ potentialLinear hα₀ hα₁ (u n) p) atTop (𝓝 (w p)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_iff_norm_sub_tendsto_zero.1 hw)
    rw [← Pi.sub_apply, ← coe_sub]
    exact norm_apply_le _ p
  have h₂ : Tendsto (fun n ↦ potentialLinear hα₀ hα₁ (u n) p) atTop
      (𝓝 (potentialLinear hα₀ hα₁ f p)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (by simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 hu).mul_const (T : ℝ)))
    rw [← Pi.sub_apply, ← coe_sub, ← map_sub]
    exact norm_potentialK_apply_le hα₀ hα₁ _ p
  exact tendsto_nhds_unique h₁ h₂

/-- **The Duhamel heat potential in `C_{par,b}^{k+2+α}`.** For `0 < α < 1` and `T > 0`, the
Duhamel potential `w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` of a forcing
`f ∈ C_{par,b}^{k+α}(E × [0, T])` of any order `k`, extended constantly in time outside the slab,
as a continuous linear map into `C_{par,b}^{k+2+α}(E × [0, T])`. Its values are given by
`TauCeti.ParabolicCkHolderSpace.heatDuhamelPotentialL_apply` and its fields, which make it a
solution of `∂ₜw = Δw + f`, by
`TauCeti.ParabolicCkHolderSpace.mixedDerivL_heatDuhamelPotentialL`. -/
def heatDuhamelPotentialL (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T) :
    ParabolicCkHolderSpace k α E F hT →L[ℝ] ParabolicCkHolderSpace (k + 2) α E F hT :=
  ContinuousLinearMap.ofSeqClosedGraph (g := potentialLinear hα₀ hα₁)
    fun u f w hu hw ↦ eq_potentialK_of_tendsto hα₀ hα₁ u f w hu hw

variable {hα₀ : 0 < α} {hα₁ : α < 1}

private theorem heatDuhamelPotentialL_eq_potentialK (f : ParabolicCkHolderSpace k α E F hT) :
    heatDuhamelPotentialL hα₀ hα₁ hT f = potentialK hα₀ hα₁ f := by
  simp only [heatDuhamelPotentialL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, potentialLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The value of the Duhamel potential at a point of the slab. -/
@[simp]
theorem heatDuhamelPotentialL_apply (f : ParabolicCkHolderSpace k α E F hT)
    (p : slab (E := E) 0 T) :
    heatDuhamelPotentialL hα₀ hα₁ hT f p = heatDuhamelPotential
      (fun s x ↦ ParabolicC2HolderSpace.timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatDuhamelPotentialL_eq_potentialK, potentialK_apply_eq_heatDuhamelPotential]

/-- **Zero initial value.** The Duhamel potential vanishes at the initial time `t = 0`. It is not
a simp lemma because `simp` proves it from `heatDuhamelPotentialL_apply`. -/
theorem heatDuhamelPotentialL_apply_slabMk_zero (f : ParabolicCkHolderSpace k α E F hT) (x : E) :
    heatDuhamelPotentialL hα₀ hα₁ hT f (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) = 0 := by
  simp

/-- **The fields of the Duhamel potential.** For `2 r + m ≤ k + 2`, the field `∂ₜ^r D_x^m w` of
the Duhamel potential `w` of `f` is
`D^m Δ^r w + ∑_{i < r} D^m Δ^(r-1-i) ∂ₜ^i f`, the time derivatives `∂ₜ^i f` taken within `[0, T]`.
In particular `∂ₜw = Δw + f`. -/
theorem mixedDerivL_heatDuhamelPotentialL (f : ParabolicCkHolderSpace k α E F hT) {r m : ℕ}
    (h : 2 * r + m ≤ k + 2) (x : E) (t : Icc (0 : ℝ) T) :
    mixedDerivL r m (heatDuhamelPotentialL hα₀ hα₁ hT f) (slabMk x t) =
      iteratedFDeriv ℝ m (Δ^[r] fun y ↦ heatDuhamelPotentialL hα₀ hα₁ hT f (slabMk y t)) x +
        ∑ i ∈ Finset.range r, iteratedFDeriv ℝ m (Δ^[r - 1 - i] fun y ↦
          iteratedDerivWithin i (ParabolicC2HolderSpace.timeExtension hT.le f y) (Icc 0 T) t)
          x := by
  have hw : (fun y ↦ heatDuhamelPotentialL hα₀ hα₁ hT f (slabMk y t)) = slice hα₀ hα₁ f t :=
    funext fun y ↦ by rw [heatDuhamelPotentialL_eq_potentialK, potentialK_apply, slice]
  rw [hw, heatDuhamelPotentialL_eq_potentialK, potentialK, mixedDerivL_mk _ _ _ _ h, field_apply,
    heatField_slabMk hα₀ hα₁ f (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have := Finset.mem_range.1 hi
  rw [forcingField_slabMk f (by omega)]
  congr 2
  funext y
  rw [curry0_mixedDerivL_slabMk f (by omega)]

/-- At order `k = 0` the Duhamel potential is the order-two Duhamel operator
`TauCeti.heatDuhamelPotentialL` on `C_b^{α,α/2}`. -/
theorem equivParabolicC2HolderSpace_heatDuhamelPotentialL
    (f : ParabolicCkHolderSpace 0 α E F hT) :
    equivParabolicC2HolderSpace (heatDuhamelPotentialL hα₀ hα₁ hT f) =
      TauCeti.heatDuhamelPotentialL hα₀ hα₁ hT (equivHolderSpace f) := by
  refine ParabolicC2HolderSpace.ext fun p ↦ ?_
  rw [equivParabolicC2HolderSpace_apply, heatDuhamelPotentialL_apply,
    TauCeti.heatDuhamelPotentialL_apply]
  congr 1
  funext s x
  simp only [ParabolicC2HolderSpace.timeExtension_def, equivHolderSpace_apply]


end ParabolicCkHolderSpace

end TauCeti
