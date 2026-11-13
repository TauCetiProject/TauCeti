/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The additive circle and the complex unit circle

For a nonzero real period `T`, Mathlib's `AddCircle.homeomorphCircle` identifies `AddCircle T`
with the complex unit circle `Circle`. This file records where that identification sends the
distinguished points: `0 : AddCircle T` is the point `1 : Circle`, so the inverse homeomorphism
carries `1` back to `0`; more generally it carries `exp (2πix / T)` back to the class of `x`.
In the other direction, `AddCircle.toCircle` sends the class of `t` to
`cos (2πt / T) + i sin (2πt / T)`, and the only points it sends to the real points `±1` of `Circle`
are `0` and the half period `T / 2`.
Applied to both factors, it identifies the torus `S¹ × S¹` with the standard torus
`UnitAddTorus (Fin 2) = ℝ² / ℤ²`. Applied coordinatewise, it identifies the standard torus
`UnitAddTorus ι` with the product of circles `ι → Circle` as topological groups.
Finally, a continuous family of maps of `AddCircle T` starting at the identity and without fixed
points at small positive times moves, at some small time, every point forward by a small continuous
amount, and the short secants `(q τ, q (τ + w))` of a loop `q` stay near the diagonal.

## Main definitions

* `TauCeti.circleProdHomeomorphUnitAddTorus` — the homeomorphism `S¹ × S¹ ≃ₜ ℝ² / ℤ²`.
* `TauCeti.unitAddTorusEquivPiCircle` — the isomorphism of topological groups
  `UnitAddTorus ι ≃ₜ+ Additive (ι → Circle)`.

## Main results

* `AddCircle.homeomorphCircle_symm_one` — the inverse circle homeomorphism sends `1` to `0` for
  every nonzero real period.
* `AddCircle.homeomorphCircle_symm_exp` — it sends `exp (2πix / T)` to the class of `x`.
* `AddCircle.re_toCircle_coe`, `AddCircle.im_toCircle_coe` — the real and imaginary parts of
  `AddCircle.toCircle` at the class of `t` are `cos (2πt / T)` and `sin (2πt / T)`.
* `AddCircle.toCircle_half_period`, `AddCircle.coe_half_period_ne_zero` — the half period is sent
  to `-1`, so it is not `0`.
* `AddCircle.im_toCircle_eq_zero_iff` — `0` and the half period are the only points at which
  `AddCircle.toCircle` is real.
* `AddCircle.exists_forall_eq_add_pos` — a continuous family of maps of the circle, the identity
  at time `0` and without fixed points at small positive times, moves every point forward by a
  small continuous amount at some arbitrarily small nonzero time.
* `ContinuousMap.secant_ne_zero` — a short forward secant of an injective loop is nonzero
  when its defining function has no zeros off the diagonal.
* `ContinuousMap.exists_pos_forall_secant_mem` — the short secants `(q τ, q (τ + w))` of a loop
  `q` lie in any given open neighborhood of the diagonal.
* `TauCeti.circleProdHomeomorphUnitAddTorus_apply`,
  `TauCeti.circleProdHomeomorphUnitAddTorus_symm_apply` — the torus homeomorphism and its inverse
  act factorwise through `AddCircle.homeomorphCircle`.
* `TauCeti.circleProdHomeomorphUnitAddTorus_exp` — the torus homeomorphism sends
  `(exp (2πia), exp (2πib))` to the class of `(a, b)`.
* `TauCeti.toMul_unitAddTorusEquivPiCircle_apply`,
  `TauCeti.unitAddTorusEquivPiCircle_symm_apply` — the torus isomorphism and its inverse act
  coordinatewise through `AddCircle.homeomorphCircle`.
-/

public section

namespace AddCircle

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `1 : Circle` to `0`. -/
@[simp]
theorem homeomorphCircle_symm_one {T : ℝ} (hT : T ≠ 0) :
    (AddCircle.homeomorphCircle hT).symm 1 = 0 := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `exp (2πix / T)` to the
class of `x`. -/
@[simp]
theorem homeomorphCircle_symm_exp {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    (AddCircle.homeomorphCircle hT).symm (Circle.exp (2 * Real.pi / T * x)) = x := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]

/-- The real part of `AddCircle.toCircle` at the class of `t` is `cos (2πt / T)`. -/
@[simp]
theorem re_toCircle_coe (T t : ℝ) :
    (toCircle (t : AddCircle T) : ℂ).re = Real.cos (2 * Real.pi / T * t) := by
  rw [toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

/-- The imaginary part of `AddCircle.toCircle` at the class of `t` is `sin (2πt / T)`. -/
@[simp]
theorem im_toCircle_coe (T t : ℝ) :
    (toCircle (t : AddCircle T) : ℂ).im = Real.sin (2 * Real.pi / T * t) := by
  rw [toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

/-- The half period `T / 2` of `AddCircle T` is sent to `-1` by `AddCircle.toCircle`. -/
@[simp]
theorem toCircle_half_period {T : ℝ} (hT : T ≠ 0) : toCircle ((T / 2 : ℝ) : AddCircle T) = -1 := by
  have hangle : 2 * Real.pi / T * (T / 2) = Real.pi := by field_simp
  ext1
  rw [toCircle_apply_mk, Circle.coe_exp, Circle.coe_neg, Circle.coe_one, hangle]
  exact Complex.exp_pi_mul_I

/-- For a nonzero period `T`, the half period `T / 2` is a nonzero point of `AddCircle T`. -/
theorem coe_half_period_ne_zero {T : ℝ} (hT : T ≠ 0) : ((T / 2 : ℝ) : AddCircle T) ≠ 0 :=
  fun h ↦ by
    have := congrArg (fun x ↦ (toCircle x : ℂ).re) h
    norm_num [hT] at this

/-- **The real points of the circle.** For a nonzero period `T`, the value of `AddCircle.toCircle`
at `x` is real exactly when `x` is `0` or the half period `T / 2`; these are sent to `1` and `-1`.
-/
theorem im_toCircle_eq_zero_iff {T : ℝ} (hT : T ≠ 0) {x : AddCircle T} :
    (toCircle x : ℂ).im = 0 ↔ x = 0 ∨ x = ((T / 2 : ℝ) : AddCircle T) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- A unit complex number with vanishing imaginary part is `1` or `-1`.
    have hsq : ((toCircle x : ℂ).re - 1) * ((toCircle x : ℂ).re + 1) = 0 := by
      have := Circle.normSq_coe (toCircle x)
      rw [Complex.normSq_apply, h] at this
      linear_combination this
    -- Such a point of the circle is determined by its real part.
    have heq (w : Circle) (hw : (w : ℂ).im = 0) (hre : (toCircle x : ℂ).re = (w : ℂ).re) :
        toCircle x = w :=
      Circle.ext (Complex.ext hre (h.trans hw.symm))
    rcases mul_eq_zero.1 hsq with hre | hre
    · left
      refine injective_toCircle hT ?_
      rw [toCircle_zero]
      exact heq 1 (by simp) (by simp [sub_eq_zero.1 hre])
    · right
      refine injective_toCircle hT ?_
      rw [toCircle_half_period hT]
      exact heq (-1) (by simp) (by simp [eq_neg_of_add_eq_zero_left hre])
  · rintro (rfl | rfl) <;> simp [hT]

section Displacement

open Set Filter
open scoped Topology

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **Maps moving the circle forward.** A continuous family `ψ (θ, ·)` of maps of `AddCircle T`,
equal to the identity at `θ = 0`, with `ψ (-θ, ·)` a right inverse of `ψ (θ, ·)`, and without fixed
points for small `θ > 0`, moves every point forward by a continuous amount `d τ ∈ (0, δ)` at some
time `c ≠ 0` satisfying any property `P` holding near `0`. For small `θ` the displacement
`ψ (θ, τ) - τ` lifts continuously to a small real number, which never vanishes and hence, the circle
being connected, has constant sign; if it is negative, the time `-θ` moves points forward. -/
theorem exists_forall_eq_add_pos (ψ : ℝ × AddCircle T → AddCircle T)
    (hψ : Continuous ψ) (hψ0 : ∀ τ, ψ (0, τ) = τ) (hψinv : ∀ θ τ, ψ (θ, ψ (-θ, τ)) = τ)
    (hψne : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ τ, ψ (θ, τ) ≠ τ) {δ : ℝ} (hδ : 0 < δ)
    {P : ℝ → Prop} (hP : ∀ᶠ θ in 𝓝 (0 : ℝ), P θ) :
    ∃ c : ℝ, c ≠ 0 ∧ P c ∧ ∃ d : AddCircle T → ℝ, Continuous d ∧
      ∀ τ, d τ ∈ Ioo 0 δ ∧ ψ (c, τ) = τ + d τ := by
  wlog hδT : δ ≤ T / 2 generalizing δ
  · obtain ⟨c, hc0, hcP, d, hdc, hd⟩ := this (half_pos hT.out) le_rfl
    exact ⟨c, hc0, hcP, d, hdc, fun τ ↦
      ⟨⟨(hd τ).1.1, (hd τ).1.2.trans (not_le.1 hδT)⟩, (hd τ).2⟩⟩
  let N : Set (AddCircle T) := (↑) '' Ioo (-δ) δ
  have hnear : ∀ᶠ c in 𝓝 (0 : ℝ), ∀ τ ∈ (univ : Set (AddCircle T)), ψ (c, τ) - τ ∈ N :=
    isCompact_univ.eventually_forall_of_forall_eventually fun τ _ ↦
      ((by fun_prop : Continuous fun cτ : ℝ × AddCircle T ↦ ψ cτ - cτ.2)
        |>.continuousAt.preimage_mem_nhds <| (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).mem_nhds
          ⟨0, ⟨neg_lt_zero.2 hδ, hδ⟩, by simp [hψ0]⟩)
  have hPneg : ∀ᶠ θ in 𝓝 (0 : ℝ), P (-θ) :=
    (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).eventually hP
  obtain ⟨θ, hθ0, ⟨hθP, hθPneg, hθnear⟩, hθne⟩ := (eventually_mem_nhdsWithin.and <|
    ((hP.and (hPneg.and hnear)).filter_mono nhdsWithin_le_nhds).and hψne).exists
  have hIco {w : ℝ} (hw : w ∈ Ioo (-δ) δ) : w ∈ Ico (-(T / 2)) (-(T / 2) + T) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  let d : AddCircle T → ℝ := fun τ ↦ AddCircle.equivIco T (-(T / 2)) (ψ (θ, τ) - τ)
  have hd (τ : AddCircle T) : d τ ∈ Ioo (-δ) δ ∧ ψ (θ, τ) = τ + d τ := by
    obtain ⟨w, hw, hwψ⟩ := hθnear τ (mem_univ τ)
    have hdw : d τ = w := by simp only [d, ← hwψ, AddCircle.equivIco_coe_eq (hIco hw)]
    exact ⟨hdw ▸ hw, by rw [hdw, hwψ, add_sub_cancel]⟩
  have hdc : Continuous d := continuous_iff_continuousAt.2 fun τ ↦ by
    obtain ⟨w, hw, hwψ⟩ := hθnear τ (mem_univ τ)
    refine continuous_subtype_val.continuousAt.comp <|
      (AddCircle.continuousAt_equivIco T _ fun h ↦ ?_).comp (by fun_prop)
    rw [← hwψ, AddCircle.coe_eq_coe_iff_of_mem_Ico (hIco hw)
      ⟨le_rfl, by linarith [hT.out]⟩] at h
    linarith [hw.1]
  have hdne (τ : AddCircle T) : d τ ≠ 0 := fun h ↦ hθne τ (by simp [(hd τ).2, h])
  have hsign {a b : AddCircle T} (ha : d a < 0) : d b < 0 := not_le.1 fun hb ↦
    let ⟨τ, hτ⟩ := intermediate_value_univ a b hdc ⟨ha.le, hb⟩
    hdne τ hτ
  by_cases hpos : ∀ τ, 0 < d τ
  · exact ⟨θ, hθ0.ne', hθP, d, hdc, fun τ ↦ ⟨⟨hpos τ, (hd τ).1.2⟩, (hd τ).2⟩⟩
  obtain ⟨a, ha⟩ := not_forall.1 hpos
  have hneg (τ : AddCircle T) : d τ < 0 := hsign ((not_lt.1 ha).lt_of_ne (hdne a))
  refine ⟨-θ, neg_ne_zero.2 hθ0.ne', hθPneg, fun τ ↦ -d (ψ (-θ, τ)),
    (hdc.comp (by fun_prop)).neg, fun τ ↦ ⟨⟨neg_pos.2 (hneg _), ?_⟩, ?_⟩⟩
  · linarith [(hd (ψ (-θ, τ))).1.1]
  · have h := (hd (ψ (-θ, τ))).2
    rw [hψinv] at h
    rw [AddCircle.coe_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h.symm

end Displacement

end AddCircle

namespace ContinuousMap

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {T : ℝ} [Fact (0 < T)]

/-- **Short secants of a loop.** The pairs `(q τ, q (τ + w))` of points of a loop `q` in `X`,
parametrized by `AddCircle T`, with a short step `w`, lie in any given open neighborhood `U` of the
diagonal, uniformly in `τ`. -/
theorem exists_pos_forall_secant_mem (q : C(AddCircle T, X)) {U : Set (X × X)}
    (hU : IsOpen U) (hdiag : ∀ x, (x, x) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, |w| < δ → ∀ τ : AddCircle T, (q τ, q (τ + w)) ∈ U := by
  have hnear : ∀ᶠ w : ℝ in 𝓝 0, ∀ τ ∈ (univ : Set (AddCircle T)), (q τ, q (τ + w)) ∈ U :=
    isCompact_univ.eventually_forall_of_forall_eventually fun τ _ ↦
      ((by fun_prop : Continuous fun z : ℝ × AddCircle T ↦ (q z.2, q (z.2 + z.1)))
        |>.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hdiag (q τ))))
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp hnear
  exact ⟨δ, hδ, fun w hw τ ↦ hsub (by rwa [Real.dist_eq, sub_zero]) τ (mem_univ τ)⟩

/-- A secant of an injective loop with a step in `(0, 1)` is nonzero if `S` has no zeros
off the diagonal in the neighborhood containing the pair. -/
theorem secant_ne_zero (q : C(AddCircle (1 : ℝ), X)) (hq : Function.Injective q)
    {S : C(X × X, ℂ)} {U : Set (X × X)} (hzero : ∀ x y, (x, y) ∈ U → S (x, y) = 0 → x = y)
    {w : ℝ} (hw : w ∈ Ioo 0 1) {τ : AddCircle (1 : ℝ)} (hU : (q τ, q (τ + w)) ∈ U) :
    S (q τ, q (τ + w)) ≠ 0 := by
  intro h
  have hw0 : ((w : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    simpa using (hq (hzero _ _ hU h)).symm
  exact hw.1.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hw.1.le, hw.2⟩).1 hw0)

end ContinuousMap

namespace TauCeti

/-- The torus `S¹ × S¹` is homeomorphic to the standard torus `UnitAddTorus (Fin 2) = ℝ² / ℤ²`,
each circle factor being identified with `ℝ / ℤ` by `AddCircle.homeomorphCircle`. -/
noncomputable def circleProdHomeomorphUnitAddTorus : Circle × Circle ≃ₜ UnitAddTorus (Fin 2) :=
  ((AddCircle.homeomorphCircle one_ne_zero).symm.prodCongr
    (AddCircle.homeomorphCircle one_ne_zero).symm).trans Homeomorph.finTwoArrow.symm

/-- The identification of `S¹ × S¹` with `ℝ² / ℤ²` reads each circle factor through
`AddCircle.homeomorphCircle.symm`. -/
@[simp]
theorem circleProdHomeomorphUnitAddTorus_apply (z : Circle × Circle) :
    circleProdHomeomorphUnitAddTorus z =
      ![(AddCircle.homeomorphCircle one_ne_zero).symm z.1,
        (AddCircle.homeomorphCircle one_ne_zero).symm z.2] := by
  ext i
  fin_cases i <;> rfl

/-- The inverse identification of `ℝ² / ℤ²` with `S¹ × S¹` sends the coordinates of a point to the
circle by `AddCircle.toCircle`. -/
@[simp]
theorem circleProdHomeomorphUnitAddTorus_symm_apply (x : UnitAddTorus (Fin 2)) :
    circleProdHomeomorphUnitAddTorus.symm x =
      (AddCircle.toCircle (x 0), AddCircle.toCircle (x 1)) := by
  simp [circleProdHomeomorphUnitAddTorus, AddCircle.homeomorphCircle_apply]

/-- The identification of `S¹ × S¹` with `ℝ² / ℤ²` sends `(exp (2πia), exp (2πib))` to the class
of `(a, b)`. -/
theorem circleProdHomeomorphUnitAddTorus_exp (a b : ℝ) :
    circleProdHomeomorphUnitAddTorus
        (Circle.exp (2 * Real.pi * a), Circle.exp (2 * Real.pi * b)) =
      ![(a : UnitAddCircle), (b : UnitAddCircle)] := by
  have h (x : ℝ) : (AddCircle.homeomorphCircle one_ne_zero).symm (Circle.exp (2 * Real.pi * x)) =
      (x : UnitAddCircle) := by
    simpa using AddCircle.homeomorphCircle_symm_exp one_ne_zero x
  ext i
  fin_cases i <;> simp [circleProdHomeomorphUnitAddTorus, h]

/-- The standard torus `UnitAddTorus ι = (ℝ / ℤ)^ι` is isomorphic as a topological group to the
product `ι → Circle` of unit circles, each coordinate being identified with `Circle` by
`AddCircle.homeomorphCircle`. The group `ι → Circle` is multiplicative, so it appears as
`Additive (ι → Circle)`. -/
noncomputable def unitAddTorusEquivPiCircle {ι : Type*} : UnitAddTorus ι ≃ₜ+ Additive (ι → Circle)
    where
  toEquiv := (Homeomorph.piCongrRight fun _ : ι ↦
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).toEquiv.trans Additive.ofMul
  map_add' x y := by
    ext i
    simp [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
  continuous_toFun := continuous_ofMul.comp (Homeomorph.piCongrRight fun _ : ι ↦
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous
  continuous_invFun := (Homeomorph.piCongrRight fun _ : ι ↦
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous.comp continuous_toMul

/-- The torus isomorphism `TauCeti.unitAddTorusEquivPiCircle` sends each coordinate to the circle
by `AddCircle.toCircle`. -/
@[simp]
theorem toMul_unitAddTorusEquivPiCircle_apply {ι : Type*} (x : UnitAddTorus ι) (i : ι) :
    (unitAddTorusEquivPiCircle x).toMul i = AddCircle.toCircle (x i) := by
  simp [unitAddTorusEquivPiCircle, AddCircle.homeomorphCircle_apply]

/-- The inverse of the torus isomorphism `TauCeti.unitAddTorusEquivPiCircle` reads each coordinate
through `AddCircle.homeomorphCircle.symm`. -/
@[simp]
theorem unitAddTorusEquivPiCircle_symm_apply {ι : Type*} (z : ι → Circle) (i : ι) :
    unitAddTorusEquivPiCircle.symm (Additive.ofMul z) i =
      (AddCircle.homeomorphCircle one_ne_zero).symm (z i) := by
  rw [Homeomorph.eq_symm_apply, AddCircle.homeomorphCircle_apply,
    ← toMul_unitAddTorusEquivPiCircle_apply, ContinuousAddEquiv.apply_symm_apply, toMul_ofMul]

end TauCeti
