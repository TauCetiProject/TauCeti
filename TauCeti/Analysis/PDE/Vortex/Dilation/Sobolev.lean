/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Dilations on the affine Sobolev field space

Pulling a field back by the dilation `z ↦ t • z` (`TauCeti.Vortex.dilateField`) acts on the
affine Sobolev field space `A_m^s` of framed plane vortex fields.

* Nonzero dilations preserve the Sobolev fields of every real order
  (`TauCeti.Vortex.dilateField_mem_sobolevFields_iff`).
* A positive dilation fixes the reference field off a disc, since the winding phase is homogeneous
  of degree `0` and the angular form `dθ` is invariant under dilations
  (`TauCeti.Vortex.hasCompactSupport_dilateField_referenceField_sub`), so it maps `A_m^s` onto
  itself (`TauCeti.Vortex.dilateField_mem_framedFieldSpace_iff`), as the bijection
  `TauCeti.Vortex.dilateFramedField`.
* For `t ≠ 0`, pullback of a gauge, `u ↦ u (t ·)`, preserves the Sobolev gauge groups `G_s` of
  every order `s > 1` (`TauCeti.Vortex.comp_smul_mem_sobolevGaugeGroup_iff`), as the automorphism
  `TauCeti.Vortex.dilateSobolevGauge`. Since pulling back a gauge transform is the gauge transform
  by the pulled-back gauge (`TauCeti.Vortex.dilateField_gaugeTransform`), a nonzero dilation maps
  `G_s` gauge orbits onto `G_s` gauge orbits
  (`TauCeti.Vortex.exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff`).
  For `k > 1` and `t > 0` it intertwines the actions of `G_(k+1)` on `A_m^k`
  (`TauCeti.Vortex.dilateFramedField_smul`), so it maps `G_(k+1)` orbits onto `G_(k+1)` orbits
  (`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_dilateFramedField_eq_iff`).

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex Filter Topology TemperedDistribution

namespace TauCeti.Vortex

variable {t : ℝ} {m : ℕ}

/-- Nonzero dilations preserve the Sobolev fields of every real order. -/
theorem dilateField_mem_sobolevFields (ht : t ≠ 0) {s : ℝ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields s) :
    dilateField t y ∈ sobolevFields s := by
  have h (j : Fin 4) : (fun z ↦ y (t • z) j) ∈ realSobolevFunctions ℂ s 2 :=
    comp_continuousLinearEquiv_mem_realSobolevFunctions (by norm_num) (by norm_num)
      (.smulLeft (Units.mk0 t ht)) (mem_sobolevFields.1 hy j)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 0)
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 1)
  · simpa [dilateField_apply] using h 2
  · simpa [dilateField_apply] using h 3

/-- A field lies in `H^s` exactly when its pullback by a nonzero dilation does. -/
@[simp]
theorem dilateField_mem_sobolevFields_iff (ht : t ≠ 0) {s : ℝ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t y ∈ sobolevFields s ↔ y ∈ sobolevFields s := by
  refine ⟨fun h ↦ ?_, dilateField_mem_sobolevFields ht⟩
  simpa [inv_mul_cancel₀ ht] using dilateField_mem_sobolevFields (inv_ne_zero ht) h

/-- A positive dilation fixes the reference field off a disc: the winding phase is homogeneous of
degree `0` and the angular form `dθ` is invariant. So the two differ by a compactly supported
field. -/
theorem hasCompactSupport_dilateField_referenceField_sub (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) : HasCompactSupport (dilateField t (referenceField f m) - referenceField f m) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
  have hr := f.rOut_pos
  have hst := div_nonneg (Real.sqrt_nonneg f.rOut) ht.le
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop
    (√f.rOut + √f.rOut / t + 1)] with z hz
  have hsq {s : ℝ} (hs : √f.rOut ≤ s) : f.rOut ≤ s ^ 2 :=
    (Real.sq_sqrt hr.le).symm.le.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2)
  have h₁ : f.rOut ≤ ‖z‖ ^ 2 := hsq (by linarith [Real.sqrt_nonneg f.rOut])
  have h₂ : f.rOut ≤ ‖t • z‖ ^ 2 := hsq (by
    rw [norm_smul, Real.norm_of_nonneg ht.le, ← div_le_iff₀' ht]
    linarith [Real.sqrt_nonneg f.rOut])
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith [Real.sqrt_nonneg f.rOut])
  simp only [Pi.sub_apply, Pi.zero_apply, dilateField_apply, referenceField_eq_of_rOut_le f m h₁,
    referenceField_eq_of_rOut_le f m h₂, smul_div_norm_smul ht, sub_eq_zero]
  ext i
  fin_cases i <;> simp [abs_of_pos ht] <;> field_simp

/-- **Dilation of the affine field space.** A positive dilation maps `A_m^s` into itself, for
every real order `s`. -/
theorem dilateField_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {s : ℝ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s) :
    dilateField t x ∈ framedFieldSpace f m s := by
  rw [mem_framedFieldSpace] at hx ⊢
  have href := mem_sobolevFields_of_hasCompactSupport
    (y := dilateField t (referenceField f m) - referenceField f m)
    ((contDiff_dilateField (contDiff_referenceField f m) t).sub (contDiff_referenceField f m))
    (hasCompactSupport_dilateField_referenceField_sub f m ht) s
  have hsplit : dilateField t x - referenceField f m = dilateField t (x - referenceField f m) +
      (dilateField t (referenceField f m) - referenceField f m) := by
    rw [dilateField_sub]
    abel
  rw [hsplit]
  exact add_mem (dilateField_mem_sobolevFields ht.ne' hx) href

/-- A field lies in `A_m^s` exactly when its pullback by a positive dilation does. -/
@[simp]
theorem dilateField_mem_framedFieldSpace_iff {f : ContDiffBump (0 : ℝ)} {s : ℝ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t x ∈ framedFieldSpace f m s ↔ x ∈ framedFieldSpace f m s := by
  refine ⟨fun h ↦ ?_, dilateField_mem_framedFieldSpace ht⟩
  simpa [inv_mul_cancel₀ ht.ne'] using dilateField_mem_framedFieldSpace (inv_pos.2 ht) h

/-- **Dilation of `A_m^s`**: for `t > 0`, pullback by `z ↦ t • z` as a bijection of the affine
field space `A_m^s`, with inverse the pullback by `z ↦ t⁻¹ • z`. -/
def dilateFramedField {f : ContDiffBump (0 : ℝ)} {s : ℝ} (ht : 0 < t) :
    framedFieldSpace f m s ≃ framedFieldSpace f m s where
  toFun x := ⟨dilateField t x, dilateField_mem_framedFieldSpace ht x.property⟩
  invFun x := ⟨dilateField t⁻¹ x, dilateField_mem_framedFieldSpace (inv_pos.2 ht) x.property⟩
  left_inv x := Subtype.ext (by simp [inv_mul_cancel₀ ht.ne'])
  right_inv x := Subtype.ext (by simp [mul_inv_cancel₀ ht.ne'])

@[simp]
theorem coe_dilateFramedField {f : ContDiffBump (0 : ℝ)} {s : ℝ} (ht : 0 < t)
    (x : framedFieldSpace f m s) :
    (dilateFramedField ht x : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField t x :=
  (rfl)

@[simp]
theorem coe_dilateFramedField_symm {f : ContDiffBump (0 : ℝ)} {s : ℝ} (ht : 0 < t)
    (x : framedFieldSpace f m s) :
    ((dilateFramedField ht).symm x : ℂ → EuclideanSpace ℝ (Fin 4)) = dilateField t⁻¹ x :=
  (rfl)

/-! ### The Sobolev gauge groups -/

/-- Pullback by a nonzero dilation preserves the Sobolev gauge group `G_s` of each order
`s > 1`. -/
theorem comp_smul_mem_sobolevGaugeGroup (ht : t ≠ 0) {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) : (fun z ↦ u (t • z)) ∈ sobolevGaugeGroup hs := by
  obtain ⟨hc, h₁, h₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  exact (mem_sobolevGaugeGroup hs _).2 ⟨hc.comp (continuous_const_smul t),
    comp_continuousLinearEquiv_mem_realSobolevFunctions (by norm_num) (by norm_num)
      (.smulLeft (Units.mk0 t ht)) h₁,
    comp_continuousLinearEquiv_mem_realSobolevFunctions (by norm_num) (by norm_num)
      (.smulLeft (Units.mk0 t ht)) h₂⟩

/-- A gauge lies in the Sobolev gauge group `G_s`, `s > 1`, exactly when its pullback by a nonzero
dilation does. -/
theorem comp_smul_mem_sobolevGaugeGroup_iff (ht : t ≠ 0) {s : ℝ} {hs : 1 < s} {u : ℂ → Circle} :
    (fun z ↦ u (t • z)) ∈ sobolevGaugeGroup hs ↔ u ∈ sobolevGaugeGroup hs := by
  refine ⟨fun h ↦ ?_, comp_smul_mem_sobolevGaugeGroup ht⟩
  simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using
    comp_smul_mem_sobolevGaugeGroup (inv_ne_zero ht) h

/-- **Dilation of Sobolev gauges**: the automorphism `u ↦ u (t • ·)` of the Sobolev gauge group
`G_s`, for `t ≠ 0`. -/
def dilateSobolevGauge {s : ℝ} {hs : 1 < s} (ht : t ≠ 0) :
    sobolevGaugeGroup hs ≃* sobolevGaugeGroup hs where
  toFun u := ⟨fun w ↦ u.val (t • w), comp_smul_mem_sobolevGaugeGroup ht u.property⟩
  invFun u := ⟨fun w ↦ u.val (t⁻¹ • w),
    comp_smul_mem_sobolevGaugeGroup (inv_ne_zero ht) u.property⟩
  left_inv u := by
    ext w
    simp [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 ht)]
  right_inv u := by
    ext w
    simp [inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.2 ht)]
  map_mul' _ _ := rfl

@[simp]
theorem coe_dilateSobolevGauge_apply {s : ℝ} {hs : 1 < s} (ht : t ≠ 0)
    (u : sobolevGaugeGroup hs) (w : ℂ) :
    (dilateSobolevGauge ht u : ℂ → Circle) w = (u : ℂ → Circle) (t • w) :=
  (rfl)

@[simp]
theorem coe_dilateSobolevGauge_symm_apply {s : ℝ} {hs : 1 < s} (ht : t ≠ 0)
    (u : sobolevGaugeGroup hs) (w : ℂ) :
    ((dilateSobolevGauge ht).symm u : ℂ → Circle) w = (u : ℂ → Circle) (t⁻¹ • w) :=
  (rfl)

/-- **Dilation preserves Sobolev gauge orbits.** For `t ≠ 0` and `s > 1`, the fields `x` and `y`
are related by a gauge transformation in `G_s` exactly when their pullbacks by `z ↦ t z` are. -/
theorem exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff (ht : t ≠ 0) {s : ℝ}
    {hs : 1 < s} {x y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    (∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u (dilateField t y) = dilateField t x) ↔
      ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u y = x := by
  -- Pulling back a relating gauge by `t` relates the pulled-back fields; pulling back by `t⁻¹`
  -- undoes the dilation.
  have key {r : ℝ} (hr : r ≠ 0) {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
      (h : ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u y = x) :
      ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u (dilateField r y) = dilateField r x := by
    obtain ⟨u, hu, rfl⟩ := h
    exact ⟨_, comp_smul_mem_sobolevGaugeGroup hr hu, (dilateField_gaugeTransform r u y).symm⟩
  refine ⟨fun h ↦ ?_, key ht⟩
  simpa [inv_mul_cancel₀ ht] using key (inv_ne_zero ht) h

/-- **Dilation intertwines the actions of `G_(k+1)` on `A_m^k`**: for `k > 1` and `t > 0`,
pulling back `u • x` gives the pulled-back gauge acting on the pulled-back field. -/
theorem dilateFramedField_smul {k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}
    {f : ContDiffBump (0 : ℝ)} (ht : 0 < t) (u : sobolevGaugeGroup hs)
    (x : framedFieldSpace f m k) :
    dilateFramedField ht (u • x) = dilateSobolevGauge ht.ne' u • dilateFramedField ht x := by
  ext1
  rw [coe_dilateFramedField, coe_sobolevGaugeGroup_smul, coe_sobolevGaugeGroup_smul,
    coe_dilateFramedField, funext (coe_dilateSobolevGauge_apply ht.ne' u),
    dilateField_gaugeTransform]

/-- **Dilation preserves `G_(k+1)` orbits in `A_m^k`.** For `k > 1` and `t > 0`, two framed fields
of `A_m^k` lie in the same `G_(k+1)` orbit exactly when their pullbacks by `z ↦ t z` do. -/
theorem exists_sobolevGaugeGroup_smul_dilateFramedField_eq_iff {k : ℕ} [Fact (1 < k)]
    {hs : 1 < (k : ℝ) + 1} {f : ContDiffBump (0 : ℝ)} (ht : 0 < t)
    {x y : framedFieldSpace f m k} :
    (∃ u : sobolevGaugeGroup hs, u • dilateFramedField ht y = dilateFramedField ht x) ↔
      ∃ u : sobolevGaugeGroup hs, u • y = x := by
  rw [(dilateSobolevGauge ht.ne').surjective.exists]
  exact exists_congr fun u ↦ by
    rw [← dilateFramedField_smul, (dilateFramedField ht).injective.eq_iff]

end TauCeti.Vortex
