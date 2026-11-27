/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Operator
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Maps of time alone in the parabolic Hölder spaces of every order

Let `α ≤ 1`, `k : ℕ`, and let `g : ℝ → F` be of class `C^{⌊k/2⌋+1}`. The map `(x, t) ↦ g t` on a
nondegenerate closed time slab `E × [a, b]` lies in the bounded parabolic Hölder space
`C_{par,b}^{k+α}` (`TauCeti.ParabolicCkHolderSpace.compSlabTime`). Its mixed derivatives are
`D_t^r D_x^0 = g⁽ʳ⁾` and `D_t^r D_x^(m+1) = 0`, and its norm is at most `9 (k + 1)² M` whenever
`M` bounds `g, g', …, g⁽⌊k/2⌋⁺¹⁾` on `[a, b]`
(`TauCeti.ParabolicCkHolderSpace.norm_compSlabTime_le`), independently of the length of the slab.
In the parabolic scaling one time derivative counts as two spatial ones, which is why `⌊k/2⌋ + 1`
derivatives of `g` suffice: the top-order field `g^(k/2)` (for even `k`) and the time slices of
`g^((k-1)/2)` (for odd `k`) are Lipschitz in time, hence Hölder for the parabolic distance.

This is the counterpart of the time-independent lift `TauCeti.CkHolderSpace.compSlabSpaceL`. Its
main use is localization in time: multiplying a solution of a parabolic equation by a cutoff
`χ(t)` vanishing near the initial time removes the initial values, and the equation for the
product only changes by the term `χ' u`
(`ParabolicCkHolderSpace.parabolicOperatorL_compParabolicCkHolder₂_lsmul_compSlabTime_apply`):

`P (χ u) = χ P u + χ' u`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.compSlabTime`: the map `(x, t) ↦ g t` in `C_{par,b}^{k+α}`, with
  its values `compSlabTime_apply`, fields `mixedDerivL_zero_compSlabTime_apply` and
  `mixedDerivL_succ_compSlabTime`, and time derivative `timeDerivL_compSlabTime`.
* `TauCeti.ParabolicCkHolderSpace.norm_compSlabTime_le`: its norm bound.
* `ParabolicCkHolderSpace.parabolicOperatorL_compParabolicCkHolder₂_lsmul_compSlabTime_apply`:
  the parabolic operator applied to the product of a map of time with a map of order `k + 2`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (time localization for parabolic estimates).
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b} {g : ℝ → F}

/-! ### The fields -/

/-- The time coordinate on the slab `E × [a, b]`, as a continuous map. -/
private def slabTimeC : C(slab (E := E) a b, Icc a b) :=
  ⟨slabTime, continuous_slabTime⟩

/-- The fields `D_t^r D_x^m` of the map `(x, t) ↦ g t`: the derivative `g⁽ʳ⁾(t)`, read as a
`0`-multilinear map, when `m = 0` and `2 r ≤ k`, and zero otherwise. -/
private def timeField (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g) :
    (r m : ℕ) → slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | r, 0 =>
    if h : 2 * r ≤ k then
      (BoundedContinuousFunction.mkOfCompact ⟨fun t : Icc a b ↦
        (continuousMultilinearCurryFin0 ℝ E F).symm (iteratedDeriv r g t),
        (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp
          ((hg.continuous_iteratedDeriv r (by exact_mod_cast (by omega : r ≤ k / 2 + 1))).comp
            continuous_subtypeVal)⟩).compContinuous slabTimeC
    else 0
  | _, _ + 1 => 0

private theorem timeField_zero_apply (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g) {r : ℕ} (hr : 2 * r ≤ k)
    (p : slab (E := E) a b) :
    timeField hg r 0 p = (continuousMultilinearCurryFin0 ℝ E F).symm
      (iteratedDeriv r g (p : ParabolicSpaceTime E).time) := by
  simp only [timeField, dite_eq_left hr, BoundedContinuousFunction.compContinuous_apply,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk, slabTimeC, coe_slabTime]

private theorem timeField_succ (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g) (r m : ℕ) :
    timeField (E := E) (a := a) (b := b) hg r (m + 1) = 0 :=
  rfl

/-- Every field of `(x, t) ↦ g t` is constant in space. -/
private theorem timeField_slabMk (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g) (r m : ℕ) (x y : E)
    (t : Icc a b) : timeField hg r m (slabMk x t) = timeField hg r m (slabMk y t) := by
  rcases m with _ | m
  · by_cases hr : 2 * r ≤ k
    · rw [timeField_zero_apply hg hr, timeField_zero_apply hg hr, time_slabMk, time_slabMk]
    · simp only [timeField, dite_eq_right hr, FunLike.coe_zero, Pi.zero_apply]
  · rw [timeField_succ, FunLike.coe_zero, Pi.zero_apply, Pi.zero_apply]

/-- The field `g⁽ʳ⁾` is bounded by any bound of `g⁽ʳ⁾` on `[a, b]`. -/
private theorem norm_timeField_le (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g) {M : ℝ≥0}
    (hM : ∀ r ≤ k / 2 + 1, ∀ t ∈ Icc a b, ‖iteratedDeriv r g t‖ ≤ M) (r m : ℕ) :
    ‖timeField (E := E) (a := a) (b := b) hg r m‖ ≤ M := by
  refine (BoundedContinuousFunction.norm_le M.coe_nonneg).2 fun p ↦ ?_
  rcases m with _ | m
  · by_cases hr : 2 * r ≤ k
    · rw [timeField_zero_apply hg hr, LinearIsometryEquiv.norm_map]
      exact hM r (by omega) _ (mem_slab.1 p.property)
    · simp [timeField, dite_eq_right hr]
  · simp [timeField_succ]

/-- With `M` bounding `g, …, g^(⌊k/2⌋+1)` on `[a, b]`, the time slices of the field `g⁽ʳ⁾`,
`2 r < k`, are `(1 + α) / 2`-Hölder with constant `3 M`, for `α ≤ 1`. -/
private theorem holderWith_timeField_slabMk (hα : α ≤ 1) (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g)
    {M : ℝ≥0} (hM : ∀ r ≤ k / 2 + 1, ∀ t ∈ Icc a b, ‖iteratedDeriv r g t‖ ≤ M) {r m : ℕ}
    (hr : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (3 * M) ((1 + α) / 2) fun t : Icc a b ↦ timeField hg r m (slabMk x t) := by
  rcases m with _ | m
  · have hβ : (1 + α) / 2 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      calc 1 + α ≤ 1 + 1 := by gcongr
        _ = 2 := one_add_one_eq_two
    have hH := hg.holderOnWith_iteratedDeriv (by exact_mod_cast (by omega : r < k / 2 + 1))
      (convex_Icc a b) hβ fun t ht ↦ ⟨hM r (by omega) t ht, hM (r + 1) (by omega) t ht⟩
    have h := (continuousMultilinearCurryFin0 ℝ E F).symm.lipschitzWith.comp_holderWith
      hH.holderWith
    rw [one_mul] at h
    convert h using 1
    funext t
    rw [timeField_zero_apply hg (by omega), time_slabMk, Function.comp_apply,
      Set.domRestrict_apply]
  · simp only [timeField_succ, FunLike.coe_zero, Pi.zero_apply]
    exact HolderWith.const

/-- With `M` bounding `g, …, g^(⌊k/2⌋+1)` on `[a, b]`, the field `g⁽ʳ⁾`, `2 r ≤ k`, is
parabolically `α`-Hölder with constant `3 M`. -/
private theorem holderWith_timeField (hα : α ≤ 1) (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g)
    {M : ℝ≥0} (hM : ∀ r ≤ k / 2 + 1, ∀ t ∈ Icc a b, ‖iteratedDeriv r g t‖ ≤ M) {r m : ℕ}
    (hr : 2 * r + m ≤ k) :
    HolderWith (3 * M) α (timeField (E := E) (a := a) (b := b) hg r m) := by
  rcases m with _ | m
  · have hH := hg.holderOnWith_iteratedDeriv (by exact_mod_cast (by omega : r < k / 2 + 1))
      (convex_Icc a b) (β := α / 2) (by rw [div_le_one (by norm_num)]; exact hα.trans one_le_two)
      fun t ht ↦ ⟨hM r (by omega) t ht, hM (r + 1) (by omega) t ht⟩
    have h := (continuousMultilinearCurryFin0 ℝ E F).symm.lipschitzWith.comp_holderWith
      (hH.comp_parabolicTime_slab (E := E))
    rw [one_mul] at h
    convert h using 1
    funext p
    rw [timeField_zero_apply hg (by omega), Function.comp_apply]
  · rw [timeField_succ]
    exact HolderWith.zero

/-! ### The map of time alone -/

/-- **Maps of time alone.** For `α ≤ 1` and `g : ℝ → F` of class `C^{⌊k/2⌋+1}`, the map
`(x, t) ↦ g t` on the slab `E × [a, b]`, as an element of the bounded parabolic Hölder space
`C_{par,b}^{k+α}`. Its fields are `D_t^r D_x^0 = g⁽ʳ⁾` (`mixedDerivL_zero_compSlabTime_apply`) and
`D_t^r D_x^(m+1) = 0` (`mixedDerivL_succ_compSlabTime`). -/
def compSlabTime (hα : α ≤ 1) (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (timeField hg)
    (fun r m _ t x ↦ by
      have hconst : (fun y ↦ timeField hg r m (slabMk y t)) =
          fun _ ↦ timeField hg r m (slabMk x t) :=
        funext fun y ↦ timeField_slabMk hg r m y x t
      rw [hconst, timeField_succ, FunLike.coe_zero, Pi.zero_apply]
      convert hasFDerivAt_const (timeField hg r m (slabMk x t)) x using 1
      ext
      simp)
    (fun r m h x t ↦ by
      rcases m with _ | m
      · have hd : HasDerivAt (fun s ↦ (continuousMultilinearCurryFin0 ℝ E F).symm
            (iteratedDeriv r g s)) ((continuousMultilinearCurryFin0 ℝ E F).symm
              (iteratedDeriv (r + 1) g t)) t := by
          exact (continuousMultilinearCurryFin0 ℝ E F).symm.hasFDerivAt.comp_hasDerivAt _
            (hg.hasDerivAt_iteratedDeriv (by exact_mod_cast (by omega : r < k / 2 + 1)) t)
        refine (hd.hasDerivWithinAt.congr_of_mem (fun s hs ↦ ?_) t.property).congr_deriv ?_
        · simp only [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le hs]
          rw [timeField_zero_apply hg (by omega), time_slabMk]
        · rw [timeField_zero_apply hg (by omega), time_slabMk]
      · have hconst : ParabolicC2HolderSpace.timeExtension hab.le (timeField hg r (m + 1)) x =
            fun _ ↦ 0 := by
          simp [timeField_succ, ParabolicC2HolderSpace.timeExtension_def]
        rw [hconst, timeField_succ, FunLike.coe_zero, Pi.zero_apply]
        exact hasDerivWithinAt_const _ _ _)
    (fun r m h ↦ by
      obtain ⟨M, hM⟩ :=
        hg.exists_norm_iteratedDeriv_le_of_isCompact (isCompact_Icc (a := a) (b := b))
      exact ⟨3 * M, holderWith_timeField_slabMk hα hg hM (by omega)⟩)
    (fun r m h ↦ by
      obtain ⟨M, hM⟩ :=
        hg.exists_norm_iteratedDeriv_le_of_isCompact (isCompact_Icc (a := a) (b := b))
      exact (holderWith_timeField hα hg hM h.le).memHolder)

variable (hα : α ≤ 1) (hg : ContDiff ℝ (k / 2 + 1 : ℕ) g)

private theorem mixedDerivL_compSlabTime {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (compSlabTime (E := E) (hab := hab) hα hg) = timeField hg r m :=
  mixedDerivL_mk _ _ _ _ h

/-- The map of time alone takes the value `g t` at `(x, t)`. -/
@[simp]
theorem compSlabTime_apply (p : slab (E := E) a b) :
    compSlabTime (hab := hab) hα hg p = g (p : ParabolicSpaceTime E).time := by
  rw [compSlabTime, mk_apply, timeField_zero_apply hg (by omega)]
  simp

/-- The purely temporal fields `D_t^r` of the map of time alone are the derivatives `g⁽ʳ⁾`, read
as `0`-multilinear maps, for `2 r ≤ k`. -/
@[simp]
theorem mixedDerivL_zero_compSlabTime_apply {r : ℕ} (hr : 2 * r ≤ k) (p : slab (E := E) a b) :
    mixedDerivL r 0 (compSlabTime (hab := hab) hα hg) p =
      (continuousMultilinearCurryFin0 ℝ E F).symm
        (iteratedDeriv r g (p : ParabolicSpaceTime E).time) := by
  rw [mixedDerivL_compSlabTime hα hg (by omega), timeField_zero_apply hg hr]

/-- The map of time alone has no spatial derivatives: every field `D_t^r D_x^(m+1)` vanishes. -/
@[simp]
theorem mixedDerivL_succ_compSlabTime (r m : ℕ) :
    mixedDerivL r (m + 1) (compSlabTime (E := E) (hab := hab) hα hg) = 0 := by
  by_cases h : 2 * r + (m + 1) ≤ k
  · rw [mixedDerivL_compSlabTime hα hg h, timeField_succ]
  · rw [mixedDerivL_of_lt (by omega), zero_apply]

/-- The map of time alone has vanishing spatial derivative. -/
@[simp]
theorem spatialFDerivL_compSlabTime {k : ℕ} (hg : ContDiff ℝ ((k + 1) / 2 + 1 : ℕ) g) :
    spatialFDerivL k α E F hab (compSlabTime hα hg) = 0 :=
  ext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp [spatialFDerivL_apply]

/-- The time derivative of the map `(x, t) ↦ g t` is the map `(x, t) ↦ g' t`. -/
@[simp]
theorem timeDerivL_compSlabTime {k : ℕ} (hg : ContDiff ℝ ((k + 2) / 2 + 1 : ℕ) g) :
    timeDerivL k α E F hab (compSlabTime hα hg) =
      compSlabTime hα
        (hg.of_le (by exact_mod_cast (by omega : k / 2 + 1 + 1 ≤ (k + 2) / 2 + 1))).deriv' := by
  ext p
  rw [timeDerivL_apply, mixedDerivL_zero_compSlabTime_apply hα hg (by omega), compSlabTime_apply]
  simp [iteratedDeriv_one]

/-- **The norm of a map of time alone.** If `M` bounds `g, g', …, g⁽⌊k/2⌋⁺¹⁾` on `[a, b]`, then
the norm of `(x, t) ↦ g t` in `C_{par,b}^{k+α}(E × [a, b])` is at most `9 (k + 1)² M`, whatever
the length of `[a, b]`. -/
theorem norm_compSlabTime_le {M : ℝ≥0}
    (hM : ∀ r ≤ k / 2 + 1, ∀ t ∈ Icc a b, ‖iteratedDeriv r g t‖ ≤ M) :
    ‖compSlabTime (E := E) (hab := hab) hα hg‖ ≤ 9 * (k + 1) ^ 2 * M := by
  set u := compSlabTime (E := E) (hab := hab) hα hg
  -- Each pair `(r, m)` contributes at most `M + 4 M + 4 M`.
  have hpair : ∀ p ∈ parabolicDerivPairs k, ‖mixedDerivL p.1 p.2 u‖ +
      (‖timeSliceL p.1 p.2 u‖ + ‖mixedDerivHolderL p.1 p.2 u‖) ≤ 9 * M := by
    intro ⟨r, m⟩ hp
    have hp' := mem_parabolicDerivPairs.1 hp
    have hD : mixedDerivL r m u = timeField hg r m := mixedDerivL_compSlabTime hα hg hp'
    have hDM : ‖mixedDerivL r m u‖ ≤ M := hD ▸ norm_timeField_le hg hM r m
    have hS : ‖timeSliceL r m u‖ ≤ 4 * M := by
      by_cases hs : 2 * r + m + 1 = k
      · refine (norm_timeSliceL_le_of_holderWith u hs (C := 3 * M) fun x ↦ ?_).trans ?_
        · rw [hD]
          exact holderWith_timeField_slabMk hα hg hM hs.le x
        · push_cast
          linarith
      · rw [timeSliceL_of_ne hs, zero_apply, norm_zero]
        positivity
    have hH : ‖mixedDerivHolderL r m u‖ ≤ 4 * M := by
      by_cases hh : 2 * r + m = k
      · have hcoe : ⇑(mixedDerivHolderL r m u) = timeField hg r m := by
          rw [← HolderSpace.coe_toBoundedContinuousFunction,
            toBoundedContinuousFunction_mixedDerivHolderL u hh, hD]
        have h := HolderSpace.norm_le_of_norm_le_of_holderWith M.coe_nonneg
          (fun p ↦ by
            rw [hcoe]
            exact ((timeField hg r m).norm_coe_le_norm p).trans (norm_timeField_le hg hM r m))
          (hcoe ▸ holderWith_timeField hα hg hM hh.le)
        push_cast at h
        linarith
      · rw [mixedDerivHolderL_of_ne hh, zero_apply, norm_zero]
        positivity
    linarith
  rw [norm_eq]
  refine (Finset.sum_le_sum hpair).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((parabolicDerivPairs k).card : ℝ) ≤ (k + 1) ^ 2 := by
    exact_mod_cast card_parabolicDerivPairs_le k
  nlinarith [M.coe_nonneg]

/-- The norms of the maps `(x, t) ↦ g t` on all the slabs `E × [a, b]` inside a fixed slab
`E × [a₀, b₀]` are bounded by one constant. -/
theorem exists_norm_compSlabTime_le (a₀ b₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ} (hab : a < b), a₀ ≤ a → b ≤ b₀ →
      ‖compSlabTime (E := E) (hab := hab) hα hg‖ ≤ C := by
  obtain ⟨M, hM⟩ :=
    hg.exists_norm_iteratedDeriv_le_of_isCompact (isCompact_Icc (a := a₀) (b := b₀))
  exact ⟨9 * (k + 1) ^ 2 * M, by positivity, fun hab ha hb ↦ norm_compSlabTime_le hα hg
    fun r hr t ht ↦ hM r hr t ⟨ha.trans ht.1, ht.2.trans hb⟩⟩

/-! ### Multiplication by a map of time -/

-- Reuse the operator module's Hessian shortcuts for instance search in coefficient types.
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

variable {hα} in
/-- **The parabolic operator on a product with a map of time.** For `χ : ℝ → ℝ` of class
`C^{⌊k/2⌋+2}` and `u ∈ C_{par,b}^{(k+2)+α}`, the product of `u` with the map `(x, t) ↦ χ t`
satisfies `P (χ u) = χ P u + χ' u`: at `(x, t)`,

`P (χ u) (x, t) = χ t • P u (x, t) + χ' t • u (x, t)`,

for every operator `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u`. -/
theorem parabolicOperatorL_compParabolicCkHolder₂_lsmul_compSlabTime_apply
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((k + 2) / 2 + 1 : ℕ) χ) (u : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) :
    parabolicOperatorL hα A B C
        ((ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα (compSlabTime hα hχ) u) p =
      χ (p : ParabolicSpaceTime E).time • parabolicOperatorL hα A B C u p +
        deriv χ (p : ParabolicSpaceTime E).time • u p := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  set w := (ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα
    (compSlabTime (E := E) (hab := hab) hα hχ) u
  have hw : ∀ y (s : Icc a b), w (slabMk y s) = χ s • u (slabMk y s) := fun y s ↦ by
    simp [w, time_slabMk]
  -- In space, `χ` is the constant `χ t`.
  have hslice : (fun y ↦ w (slabMk y t)) = χ t • fun y ↦ u (slabMk y t) :=
    funext fun y ↦ by rw [hw, Pi.smul_apply]
  -- In time, the product rule within `[a, b]`.
  have hu : HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le u x)
      (derivWithin (ParabolicC2HolderSpace.timeExtension hab.le u x) (Icc a b) t) (Icc a b) t := by
    rw [← timeDerivL_slabMk, timeDerivL_apply]
    have h := (continuousMultilinearCurryFin0 ℝ E F).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
      (hasDerivWithinAt_mixedDerivL u (r := 0) (m := 0) (by omega) x t)
    refine (h.congr_of_mem (fun s hs ↦ ?_) t.property).congr_deriv ?_
    · simp [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le hs]
    · simp only [zero_add, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, continuousMultilinearCurryFin0_apply,
        Matrix.zero_empty]
  have hχd : HasDerivWithinAt χ (deriv χ t) (Icc a b) t :=
    ((hχ.differentiable (by norm_num)) t).hasDerivAt.hasDerivWithinAt
  have hwt : derivWithin (ParabolicC2HolderSpace.timeExtension hab.le w x) (Icc a b) t =
      χ t • derivWithin (ParabolicC2HolderSpace.timeExtension hab.le u x) (Icc a b) t +
        deriv χ t • u (slabMk x t) := by
    have h := ((hχd.smul hu).congr_of_mem (f₁ := ParabolicC2HolderSpace.timeExtension hab.le w x)
      (fun s hs ↦ ?_) t.property).derivWithin (uniqueDiffOn_Icc hab t t.property)
    · rwa [ParabolicC2HolderSpace.timeExtension_of_mem] at h
    · simp only [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le hs, hw,
        Pi.smul_apply']
  rw [parabolicOperatorL_slabMk, parabolicOperatorL_slabMk, hwt, hslice,
    fderiv_const_smul_field, fderiv_const_smul_field, hw, time_slabMk]
  simp only [Pi.smul_apply, map_smul, smul_sub, smul_add]
  abel

end TauCeti.ParabolicCkHolderSpace
