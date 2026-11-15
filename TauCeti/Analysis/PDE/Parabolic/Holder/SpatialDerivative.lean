/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Spatial differentiation in the parabolic Hölder scale

Spatial differentiation `u ↦ D_x u` maps `C_{par,b}^{k+1+α}` to `C_{par,b}^{k+α}` on a
nondegenerate closed slab `E × [a, b]`, where the derivative takes values in `E →L[ℝ] F`, and it
does not increase the norm. In the parabolic scaling one spatial derivative lowers the order by
one, while one time derivative lowers it by two.

The mixed derivative fields of `D_x u` are those of `u` with one more spatial derivative, read
through right currying: `D_t^r D_x^m (D_x u)` is `(D_t^r D_x^(m+1) u).curryRight`, the original
spatial direction being the last argument. Right currying
`E [×(m+1)]→L[ℝ] F ≃ E [×m]→L[ℝ] (E →L[ℝ] F)` is a linear isometry, so the top-order parabolic
Hölder fields and the uniform temporal Hölder slices one order below the top carry over with the
same norms, and the index shift `(r, m) ↦ (r, m + 1)` from the pairs of order at most `k` to those
of order at most `k + 1` is injective. Spatial differentiation is how estimates at order `k + 1`
are reduced to estimates at order `k` in higher-order parabolic regularity: differentiating an
equation in space gives an equation of the same type for `D_x u`.

## Main declarations

All declarations are in the `TauCeti.ParabolicCkHolderSpace` namespace.

* `spatialFDeriv`: spatial differentiation
  `C_{par,b}^{k+1+α}(E × [a, b], F) → C_{par,b}^{k+α}(E × [a, b], E →L[ℝ] F)`.
* `mixedDerivL_spatialFDeriv`, `mixedDerivHolderL_spatialFDeriv_apply` and
  `timeSliceL_spatialFDeriv_apply`: the derivative data of `D_x u` in terms of those of `u`.
* `hasFDerivAt_spatialFDeriv` and `spatialFDeriv_slabMk`: `D_x u (x, t)` is the Fréchet
  derivative of `y ↦ u (y, t)` at `x`.
* `norm_spatialFDeriv_le` and `isBoundedLinearMap_spatialFDeriv`: spatial differentiation is a
  bounded linear map of norm at most one.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 3 (parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped ENNReal NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-! ### Shifting the fields through a family of linear isometries

The construction is carried out for a family of linear isometries
`c m : E [×(m+1)]→L[ℝ] F → E [×m]→L[ℝ] G` compatible with left currying, and specialised to right
currying below. Keeping the codomain `G` a variable keeps the instance terms of the shifted fields
syntactically those of the carrier, which keeps unification with its API cheap. -/

section Shift

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {c : ∀ m : ℕ, (E [×(m + 1)]→L[ℝ] F) →ₗᵢ[ℝ] E [×m]→L[ℝ] G}

/-- The shifted fields: `c m` applied to the fields of `u` with one more spatial derivative. -/
private def shiftField (c : ∀ m : ℕ, (E [×(m + 1)]→L[ℝ] F) →ₗᵢ[ℝ] E [×m]→L[ℝ] G)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] G) :=
  (mixedDerivL r (m + 1) f).comp (c m) (c m).lipschitzWith

private theorem shiftField_apply (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) : shiftField c f r m p = c m (mixedDerivL r (m + 1) f p) :=
  (rfl)

/-- The shifted fields satisfy the spatial derivative identities. -/
private theorem hasFDerivAt_shiftField
    (hc : ∀ m (A : E [×(m + 2)]→L[ℝ] F),
      (c (m + 1) A).curryLeft = (c m).toContinuousLinearMap.comp A.curryLeft)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) (h : 2 * r + m + 1 ≤ k)
    (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ shiftField c f r m (slabMk y t))
      (shiftField c f r (m + 1) (slabMk x t)).curryLeft x := by
  have H := (c m).toContinuousLinearMap.hasFDerivAt.comp x
    (hasFDerivAt_mixedDerivL f (r := r) (m := m + 1) (by omega) t x)
  rw [← hc] at H
  exact H

/-- The shifted fields satisfy the time derivative identities. -/
private theorem hasDerivWithinAt_shiftField (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (shiftField c f r m) x)
      (shiftField c f (r + 1) m (slabMk x t)) (Icc a b) t := by
  have H := HasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (c m).toContinuousLinearMap.hasFDerivAt
    (hasDerivWithinAt_mixedDerivL f (r := r) (m := m + 1) (by omega) x t)
  simpa only [ParabolicC2HolderSpace.timeExtension_def, Function.comp_def, shiftField_apply,
    LinearIsometry.coe_toContinuousLinearMap] using H

/-- Postcomposition with a linear isometry preserves Hölder continuity with the same constant. -/
private theorem holderWith_linearIsometry_comp {X : Type*} [PseudoEMetricSpace X] {m : ℕ}
    {C r : ℝ≥0} {g : X → E [×(m + 1)]→L[ℝ] F} (hg : HolderWith C r g) :
    HolderWith C r fun x ↦ c m (g x) :=
  fun x y ↦ by
    rw [LinearIsometry.edist_map]
    exact hg x y

/-- The shifted fields one order below the top have uniformly Hölder time slices. -/
private theorem exists_holderWith_shiftField (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (h : 2 * r + m + 1 = k) :
    ∃ C, ∀ x : E, HolderWith C ((1 + α) / 2) fun t : Icc a b ↦
      shiftField c f r m (slabMk x t) := by
  refine ⟨‖timeSliceL r (m + 1) f‖₊, fun x ↦ ?_⟩
  have hnorm : ‖timeSliceL r (m + 1) f x‖₊ ≤ ‖timeSliceL r (m + 1) f‖₊ := by
    exact_mod_cast lp.norm_apply_le_norm ENNReal.top_ne_zero (timeSliceL r (m + 1) f) x
  have H := holderWith_linearIsometry_comp (c := c)
    ((timeSliceL r (m + 1) f x).holderWith_nnnorm.mono hnorm)
  simpa only [timeSliceL_apply f (r := r) (m := m + 1) (by omega), shiftField_apply] using H

/-- The shifted fields of top order are parabolically Hölder. -/
private theorem memHolder_shiftField (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ)
    (h : 2 * r + m = k) :
    MemHolder α (shiftField c f r m : slab (E := E) a b → E [×m]→L[ℝ] G) := by
  obtain ⟨C, hC⟩ := memHolder_mixedDerivL f (r := r) (m := m + 1) (by omega)
  exact (holderWith_linearIsometry_comp (c := c) hC).memHolder

/-- The element of order `k` with the shifted fields. -/
private def shift (c : ∀ m : ℕ, (E [×(m + 1)]→L[ℝ] F) →ₗᵢ[ℝ] E [×m]→L[ℝ] G)
    (hc : ∀ m (A : E [×(m + 2)]→L[ℝ] F),
      (c (m + 1) A).curryLeft = (c m).toContinuousLinearMap.comp A.curryLeft)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) : ParabolicCkHolderSpace k α E G hab :=
  mk (shiftField c f) (hasFDerivAt_shiftField hc f) (hasDerivWithinAt_shiftField f)
    (exists_holderWith_shiftField f) (memHolder_shiftField f)

variable (hc : ∀ m (A : E [×(m + 2)]→L[ℝ] F),
  (c (m + 1) A).curryLeft = (c m).toContinuousLinearMap.comp A.curryLeft)

private theorem mixedDerivL_shift_apply (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivL r m (shift c hc f) p = c m (mixedDerivL r (m + 1) f p) := by
  by_cases h : 2 * r + m ≤ k
  · rw [shift, mixedDerivL_mk _ _ _ _ h, shiftField_apply]
  · rw [mixedDerivL_of_lt (by omega), mixedDerivL_of_lt (by omega)]
    simp only [zero_apply, map_zero]

private theorem mixedDerivHolderL_shift (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) : mixedDerivHolderL r m (shift c hc f) =
      HolderSpace.compLeftL (c m).toContinuousLinearMap (mixedDerivHolderL r (m + 1) f) := by
  by_cases h : 2 * r + m = k
  · refine HolderSpace.ext fun p ↦ ?_
    have H := congrArg (fun g ↦ g p)
      (toBoundedContinuousFunction_mixedDerivHolderL (shift c hc f) h)
    have H' := congrArg (fun g ↦ g p)
      (toBoundedContinuousFunction_mixedDerivHolderL f (r := r) (m := m + 1) (by omega))
    simp only [HolderSpace.toBoundedContinuousFunction_apply] at H H'
    rw [H, HolderSpace.compLeftL_apply, H', mixedDerivL_shift_apply]
    rfl
  · rw [mixedDerivHolderL_of_ne h, mixedDerivHolderL_of_ne (by omega), zero_apply, zero_apply,
      map_zero]

private theorem timeSliceL_shift (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ)
    (x : E) : timeSliceL r m (shift c hc f) x =
      HolderSpace.compLeftL (c m).toContinuousLinearMap (timeSliceL r (m + 1) f x) := by
  by_cases h : 2 * r + m + 1 = k
  · refine HolderSpace.ext fun t ↦ ?_
    rw [timeSliceL_apply _ h, HolderSpace.compLeftL_apply,
      timeSliceL_apply f (r := r) (m := m + 1) (by omega), mixedDerivL_shift_apply]
    rfl
  · rw [timeSliceL_of_ne h, timeSliceL_of_ne (by omega), zero_apply, zero_apply, lp.coeFn_zero,
      lp.coeFn_zero, Pi.zero_apply, Pi.zero_apply, map_zero]

private theorem norm_shift_le (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖shift c hc f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq]
  apply Finset.sum_le_sum_of_injOn (fun p : ℕ × ℕ ↦ (p.1, p.2 + 1))
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (by omega)
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    simp only [mem_parabolicDerivPairs] at hq ⊢
    omega
  · rintro ⟨r, m⟩ _
    refine add_le_add ?_ (add_le_add ?_ ?_)
    · -- The fields: `c m` preserves norms pointwise.
      refine (BoundedContinuousFunction.norm_le (norm_nonneg (mixedDerivL r (m + 1) f))).2
        fun p ↦ ?_
      rw [mixedDerivL_shift_apply, LinearIsometry.norm_map]
      exact (mixedDerivL r (m + 1) f).norm_coe_le_norm p
    · -- The time slices: `c m` preserves each bounded Hölder norm.
      refine lp.norm_le_of_forall_le (norm_nonneg _) fun x ↦ ?_
      rw [timeSliceL_shift, HolderSpace.norm_compLeftL_linearIsometry]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ x
    · rw [mixedDerivHolderL_shift, HolderSpace.norm_compLeftL_linearIsometry]
  · intro p _ _
    positivity

end Shift

/-! ### Right currying -/

variable (E F) in
/-- Right currying `E [×(m+1)]→L[ℝ] F → E [×m]→L[ℝ] (E →L[ℝ] F)` as a linear isometry,
`A ↦ A.curryRight`. -/
private def curryRightLI (m : ℕ) : (E [×(m + 1)]→L[ℝ] F) →ₗᵢ[ℝ] E [×m]→L[ℝ] (E →L[ℝ] F) :=
  (continuousMultilinearCurryRightEquiv' ℝ m E F).toLinearIsometry

private theorem curryRightLI_apply {m : ℕ} (A : E [×(m + 1)]→L[ℝ] F) :
    curryRightLI E F m A = A.curryRight :=
  (rfl)

/-- Right currying turns the left currying of an `(m + 2)`-multilinear map into the left currying
of its right currying: both send `h₀`, `v` and `h` to `A (h₀, v, h)`. -/
private theorem curryRightLI_curryLeft (m : ℕ) (A : E [×(m + 2)]→L[ℝ] F) :
    (curryRightLI E F (m + 1) A).curryLeft =
      (curryRightLI E F m).toContinuousLinearMap.comp A.curryLeft := by
  ext h₀ v h
  simp only [ContinuousMultilinearMap.curryLeft_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, curryRightLI_apply,
    ContinuousMultilinearMap.curryRight_apply, Fin.cons_snoc_eq_snoc_cons]

/-- Spatial differentiation `u ↦ D_x u` from `C_{par,b}^{k+1+α}` to `C_{par,b}^{k+α}` on the same
closed slab, with values in `E →L[ℝ] F`: the mixed derivative fields of `D_x u` are the right
curryings of those of `u` with one more spatial derivative (`mixedDerivL_spatialFDeriv`), and its
value at `(x, t)` is the Fréchet derivative of `y ↦ u (y, t)` at `x` (`spatialFDeriv_slabMk`). It
is a bounded linear map of norm at most one (`isBoundedLinearMap_spatialFDeriv`). -/
def spatialFDeriv (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E (E →L[ℝ] F) hab :=
  shift (curryRightLI E F) curryRightLI_curryLeft f

/-- The mixed derivative fields of `D_x u` are the right curryings of the fields of `u` with one
more spatial derivative: the spatial direction of `D_x` is the last argument. -/
@[simp]
theorem mixedDerivL_spatialFDeriv (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) :
    mixedDerivL r m (spatialFDeriv f) p = (mixedDerivL r (m + 1) f p).curryRight := by
  rw [spatialFDeriv, mixedDerivL_shift_apply, curryRightLI_apply]

/-- The top-order parabolic Hölder fields of `D_x u` are the right curryings of those of `u`. -/
@[simp]
theorem mixedDerivHolderL_spatialFDeriv_apply (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivHolderL r m (spatialFDeriv f) p = (mixedDerivHolderL r (m + 1) f p).curryRight := by
  rw [spatialFDeriv, mixedDerivHolderL_shift, HolderSpace.compLeftL_apply,
    LinearIsometry.coe_toContinuousLinearMap, curryRightLI_apply]

/-- The uniform temporal Hölder slices of `D_x u` are the right curryings of those of `u`. -/
@[simp]
theorem timeSliceL_spatialFDeriv_apply (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) (t : Icc a b) :
    timeSliceL r m (spatialFDeriv f) x t = (timeSliceL r (m + 1) f x t).curryRight := by
  rw [spatialFDeriv, timeSliceL_shift, HolderSpace.compLeftL_apply,
    LinearIsometry.coe_toContinuousLinearMap, curryRightLI_apply]

/-- The value of `D_x u` is the recorded first spatial derivative of `u`, read as a linear map. -/
@[simp]
theorem spatialFDeriv_apply (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) :
    spatialFDeriv f p = continuousMultilinearCurryFin1 ℝ E F (mixedDerivL 0 1 f p) := by
  ext h
  rw [← mixedDerivL_zero_zero_apply (spatialFDeriv f) p 0, mixedDerivL_spatialFDeriv,
    ContinuousMultilinearMap.curryRight_apply, continuousMultilinearCurryFin1_apply]

/-- On every time slice, `y ↦ u (y, t)` is Fréchet differentiable with derivative
`D_x u (x, t)`. -/
theorem hasFDerivAt_spatialFDeriv (f : ParabolicCkHolderSpace (k + 1) α E F hab) (t : Icc a b)
    (x : E) : HasFDerivAt (fun y ↦ f (slabMk y t)) (spatialFDeriv f (slabMk x t)) x := by
  have H := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.hasFDerivAt.comp x
    (hasFDerivAt_mixedDerivL f (r := 0) (m := 0) (by omega) t x)
  convert H using 1
  · funext y
    simp only [Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      continuousMultilinearCurryFin0_apply, mixedDerivL_zero_zero_apply]
  · ext h
    rw [spatialFDeriv_apply, continuousMultilinearCurryFin1_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    exact funext fun i ↦ by fin_cases i; rfl

/-- The value of `D_x u` at `(x, t)` is the Fréchet derivative of `y ↦ u (y, t)` at `x`. -/
theorem spatialFDeriv_slabMk (f : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E)
    (t : Icc a b) : spatialFDeriv f (slabMk x t) = fderiv ℝ (fun y ↦ f (slabMk y t)) x :=
  (hasFDerivAt_spatialFDeriv f t x).fderiv.symm

/-- Spatial differentiation does not increase the full parabolic Hölder norm. -/
theorem norm_spatialFDeriv_le (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖spatialFDeriv f‖ ≤ ‖f‖ := by
  rw [spatialFDeriv]
  exact norm_shift_le _ f

/-- Spatial differentiation is additive. -/
@[simp]
theorem spatialFDeriv_add (f g : ParabolicCkHolderSpace (k + 1) α E F hab) :
    spatialFDeriv (f + g) = spatialFDeriv f + spatialFDeriv g :=
  ext fun p ↦ by
    simp only [spatialFDeriv_apply, coe_add, Pi.add_apply, map_add, FunLike.coe_add]

/-- Spatial differentiation is homogeneous. -/
@[simp]
theorem spatialFDeriv_smul (c : ℝ) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    spatialFDeriv (c • f) = c • spatialFDeriv f :=
  ext fun p ↦ by
    simp only [spatialFDeriv_apply, coe_smul, Pi.smul_apply, map_smul, FunLike.coe_smul]

/-- Spatial differentiation is a bounded linear map, with bound one (`norm_spatialFDeriv_le`);
`IsBoundedLinearMap.toContinuousLinearMap` bundles it. -/
theorem isBoundedLinearMap_spatialFDeriv :
    IsBoundedLinearMap ℝ (spatialFDeriv : ParabolicCkHolderSpace (k + 1) α E F hab →
      ParabolicCkHolderSpace k α E (E →L[ℝ] F) hab) :=
  IsLinearMap.with_bound ⟨spatialFDeriv_add, spatialFDeriv_smul⟩ 1 fun f ↦ by
    rw [one_mul]
    exact norm_spatialFDeriv_le f

end TauCeti.ParabolicCkHolderSpace
