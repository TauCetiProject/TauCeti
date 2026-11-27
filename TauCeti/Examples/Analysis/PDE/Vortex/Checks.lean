/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Flux.Basic
public import TauCeti.Analysis.PDE.Vortex.Index
public import TauCeti.Analysis.PDE.Vortex.Moduli.Symmetry
public import TauCeti.Analysis.PDE.Vortex.Moduli.Topology
public import TauCeti.Topology.Sym.Basic

/-!
# Normalization checks for framed plane vortices

The plane vortex equations `∂bar_a α = 0`, `*iF_a = (1 - |α|²) / 8` on the trivial line over `ℂ`
are written in the real coordinates `x = (b₁, b₂, p, q)`, `a = i (b₁ ds + b₂ dt)`,
`α = 2 (p + i q)` (`TauCeti.Vortex.equation`). This file tests that normalization, and the
framed gauge group and zero divisors built on it, on explicit fields, and contrasts each value
with the one a competing convention would give.

* **Flux.** A framed degree-`m` vortex has `∫ (1 - |α|²) = 16 π m`. The equation with curvature
  coefficient `1/4` in place of `1/8`, coupling `2`, gives `8 π m` instead
  (`integral_one_sub_sq_norm_sectionValue_eq_div`). The vacuum `(0, 1)`, the framed degree-`0`
  vortex `TauCeti.Vortex.vacuumField_mem_framedVortexSubMulAction`, has `|α| ≡ 1` and empty zero
  divisor (`isZeroMultiplicity_sectionValue_vacuumField`).
* **The vacuum operator.** On constant fields the gauge-fixed operator at the vacuum is its
  zeroth-order part `(b₁, b₂, p, q) ↦ (q, p, -b₂, b₁) / 2`, one half of an orthogonal map, so
  `|L₀ x| = |x| / 2` (`gaugeFixedOperator_vacuumField_const`,
  `norm_gaugeFixedOperator_vacuumField_const`). At `m = 0` the index `2m` is `0`: the Sobolev
  realization at the vacuum is bijective (`bijective_sobolevGaugeFixedOperator_vacuumField`).
  At `m = 1` the kernel is spanned by the two covariant translations of the vortex, the
  translations corrected by a gauge direction; that is already
  `TauCeti.Vortex.range_covariantTranslationLinearMap`.
* **The moduli space.** For `m = 0` the symmetric product is a point and every framed degree-`0`
  vortex is gauge equivalent to the vacuum (`exists_framedGaugeGroup_smul_vacuumField_eq`). The
  framed gauge group has no base-point condition: its values at `0` exhaust the circle
  (`exists_mem_framedGaugeGroup_apply_zero_eq`), and two gauge transforms of the vacuum are
  related by a gauge with `u(0) = 1` only when they agree at `0`
  (`exists_smul_smul_vacuumField_eq_and_apply_zero_eq_one_iff`); the based quotient would carry
  a free action of that circle. For `m = 1` the moduli space is homeomorphic to `ℂ`, and the
  vortex with zero divisor `{z₀}` is the translate by `z₀` of the vortex centred at `0`
  (`framedVortexModuliHomeomorphOne`, `exists_framedGaugeGroup_smul_translateFramedVortex_eq`).
* **Zero divisors record oriented order.** The section `w ↦ conj w` has no zero divisor at
  all (`not_isZeroMultiplicity_conj`), although `|conj w| = |w|`: a definition of the order of
  vanishing by the growth of `|α|` would give it order `1`.
* **Flat scaling.** In the coordinate `w = √(2r) y` the coefficient `r/4` becomes `1/8`
  (`TauCeti.Vortex.equation_dilateField_inv_sqrt_eq_zero_iff`); the coordinate `w = √r y` gives
  the coupling-`2` equation, with coefficient `1/4`
  (`coupledEquation_two_dilateField_inv_sqrt_eq_zero_iff`, `coupledEquation_two_apply_zero`),
  whose vortices have the flux `8 π m` above.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Proposition 4.1.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Examples.PlaneVortex

open Complex Filter _root_.MeasureTheory Real TauCeti.Vortex TopologicalSpace
open scoped Topology

local notation "μ⊤" =>
  _root_.MeasureTheory.Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The vacuum -/

/-- The section of the vacuum has empty zero divisor. -/
theorem isZeroMultiplicity_sectionValue_vacuumField :
    IsZeroMultiplicity (sectionValue vacuumField) 0 := isZeroMultiplicity_iff.2 fun _ ↦
  ⟨fun _ ↦ 1, continuousAt_const, one_ne_zero, Eventually.of_forall fun _ ↦ by simp⟩

/-! ### The flux -/

/-- **The flux at coupling `c`.** A smooth framed degree-`m` vortex of the equation
`*iF_a = c (1 - |α|²) / 8`, `c > 0`, has `∫ (1 - |α|²) = 16 π m / c`. At `c = 1` this is the
flux identity `∫ (1 - |α|²) = 16 π m` of the normalized equation
(`TauCeti.Vortex.integral_one_sub_sq_norm_sectionValue_eq_mul_card`); the coefficient `1/4`,
coupling `2`, gives `8 π m` (`integral_one_sub_sq_norm_sectionValue_eq_eight_mul`). -/
theorem integral_one_sub_sq_norm_sectionValue_eq_div {c : ℝ} (hc : 0 < c) {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction c m) :
    ∫ z, (1 - ‖sectionValue x z‖ ^ 2) = 16 * π * m / c := by
  -- Dilate by `t = c^(-1/2)` to the normalized equation, where the flux identity holds.
  set t : ℝ := (√c)⁻¹ with ht_def
  have ht : 0 < t := by positivity
  have ht2 : t ^ 2 = c⁻¹ := by rw [ht_def, inv_pow, Real.sq_sqrt hc.le]
  have htc : t ^ 2 * c = 1 := by rw [ht2, inv_mul_cancel₀ hc.ne']
  have hy := dilateField_mem_framedVortexSubMulAction ht hx
  rw [htc] at hy
  obtain ⟨hs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hy
  simp only [coupledEquation_one] at hsol
  have hflux := integral_one_sub_sq_norm_sectionValue_eq_mul_card (hs.of_le (by simp)) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfr)
    (isZeroMultiplicity_sectionValue_framedVortexDivisor ⟨_, hy⟩)
  simp only [sectionValue_dilateField, Sym.card_coe] at hflux
  have hcomp := Measure.integral_comp_smul volume (fun z ↦ 1 - ‖sectionValue x z‖ ^ 2) t
  rw [Complex.finrank_real_complex, ht2, inv_inv, abs_of_pos hc, smul_eq_mul] at hcomp
  rw [hcomp] at hflux
  rw [eq_div_iff hc.ne', ← hflux, mul_comm]

/-- **The coefficient `1/4` gives flux `8 π m`.** A smooth framed degree-`m` vortex of
`*iF_a = (1 - |α|²) / 4` has `∫ (1 - |α|²) = 8 π m`, not the value `16 π m` of the normalized
equation. -/
theorem integral_one_sub_sq_norm_sectionValue_eq_eight_mul {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction 2 m) :
    ∫ z, (1 - ‖sectionValue x z‖ ^ 2) = 8 * π * m := by
  rw [integral_one_sub_sq_norm_sectionValue_eq_div two_pos hx]
  ring

/-! ### The vacuum operator -/

/-- **The vacuum operator on constant fields** is its zeroth-order part
`(b₁, b₂, p, q) ↦ (q, p, -b₂, b₁) / 2`. The entry `b₁ / 2` of the last row `H₂` is the one that
makes the adjoint carry `+H₂ / 2` in its first row (`TauCeti.Vortex.vacuumAdjoint_apply_zero`). -/
theorem gaugeFixedOperator_vacuumField_const (v : EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedOperator vacuumField (fun _ ↦ v) z = !₂[v 3 / 2, v 2 / 2, -v 1 / 2, v 0 / 2] := by
  ext i
  fin_cases i <;>
    simp [gaugeFixedOperator_apply_zero, gaugeFixedOperator_apply_one,
      gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three, gaugeAdjoint_def,
      linearizedEquation_apply_zero, linearizedEquation_apply_one, linearizedEquation_apply_two,
      vacuumField_apply] <;> ring

/-- **The vacuum gap is `1/2`.** On constant fields the vacuum operator is one half of an
orthogonal map: `|L₀ v| = |v| / 2`. -/
theorem norm_gaugeFixedOperator_vacuumField_const (v : EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ‖gaugeFixedOperator vacuumField (fun _ ↦ v) z‖ = ‖v‖ / 2 := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [gaugeFixedOperator_vacuumField_const, EuclideanSpace.norm_sq_eq, div_pow,
    EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_four]
  ring

/-- **Index `0` at the vacuum.** The Sobolev realization `H¹ → L²` of the gauge-fixed operator at
the vacuum, the framed degree-`0` vortex, is bijective. -/
theorem bijective_sobolevGaugeFixedOperator_vacuumField {a : Lp (EuclideanSpace ℝ (Fin 4)) ⊤ μ⊤}
    (ha : a =ᵐ[μ⊤] vacuumField) : Function.Bijective (sobolevGaugeFixedOperator a) := by
  refine bijective_sobolevGaugeFixedOperator contDiff_vacuumField (fun i n _ ↦ ?_)
    equation_vacuumField
    (by rw [show sectionValue vacuumField = 1 from funext sectionValue_vacuumField]
        exact tendsto_const_nhds) ha
  -- The coordinates of the vacuum are constant.
  refine ⟨‖iteratedFDeriv ℝ n (fun _ : ℂ ↦ vacuumField 0 i) 0‖, fun z ↦ le_of_eq ?_⟩
  rw [show (fun z ↦ vacuumField z i) = fun _ ↦ vacuumField 0 i by simp [vacuumField_apply]]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [iteratedFDeriv_const_of_ne hn]

/-! ### The moduli space -/

/-- **The degree-`0` moduli space is the orbit of the vacuum.** At every positive coupling, every
smooth framed degree-`0` vortex is gauge equivalent to the vacuum, matching the one-point
symmetric product `Sym ℂ 0`. -/
theorem exists_framedGaugeGroup_smul_vacuumField_eq {c : ℝ} (hc : 0 < c)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction c 0) :
    ∃ u : framedGaugeGroup, u • vacuumField = x := by
  obtain ⟨u, hu⟩ := (framedVortexDivisor_eq_framedVortexDivisor_iff hc (x := ⟨x, hx⟩)
    (y := ⟨vacuumField, vacuumField_mem_framedVortexSubMulAction c⟩)).1 (Subsingleton.elim _ _)
  exact ⟨u, congrArg Subtype.val hu⟩

/-- **The framed gauge group has no base-point condition.** For every unit complex number `c`
there is a smooth gauge tending to one at infinity with value `c` at the origin. -/
theorem exists_mem_framedGaugeGroup_apply_zero_eq (c : Circle) :
    ∃ u ∈ framedGaugeGroup, u 0 = c := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective c
  -- A bump `φ` equal to `1` near the origin, and the gauge `exp (i θ φ)`.
  let φ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun z ↦ Circle.exp (θ * φ z), (mem_framedGaugeGroup _).2 ⟨?_, ?_⟩, ?_⟩
  · simp only [Circle.coe_exp]
    exact Complex.contDiff_exp.comp
      ((ofRealCLM.contDiff.comp (contDiff_const.mul φ.contDiff)).mul contDiff_const)
  · have h0 : (fun z ↦ Circle.exp (θ * φ z)) =ᶠ[cocompact ℂ] fun _ ↦ 1 := by
      filter_upwards [φ.hasCompactSupport.isCompact.compl_mem_cocompact] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, Circle.exp_zero]
    exact tendsto_const_nhds.congr' h0.symm
  · simp [φ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]

/-- **Based gauges see the value at the origin.** Two gauge transforms `u • (0, 1)` and
`v • (0, 1)` of the vacuum are related by a framed gauge `w` with `w(0) = 1` exactly when
`u(0) = v(0)`. With a base-point condition the circle of values at `0`
(`exists_mem_framedGaugeGroup_apply_zero_eq`) would act freely on the degree-`0` moduli space,
which would no longer be the point `Sym ℂ 0`. -/
theorem exists_smul_smul_vacuumField_eq_and_apply_zero_eq_one_iff (u v : framedGaugeGroup) :
    (∃ w : framedGaugeGroup, w • u • vacuumField = v • vacuumField ∧ (w : ℂ → Circle) 0 = 1) ↔
      (u : ℂ → Circle) 0 = (v : ℂ → Circle) 0 := by
  constructor
  · rintro ⟨w, hw, hw0⟩
    have h := congrArg (fun y ↦ sectionValue y 0) hw
    simp only [framedGaugeGroup_smul, sectionValue_gaugeTransform, sectionValue_vacuumField,
      mul_one, hw0, Circle.coe_one, one_mul] at h
    exact Circle.ext h
  · intro h
    refine ⟨v * u⁻¹, by rw [smul_smul, inv_mul_cancel_right], ?_⟩
    simp [h]

/-- **The degree-`1` moduli space is `ℂ`.** The zero divisor identifies the orbit space of the
smooth framed gauge group on the smooth framed degree-`1` vortices with `ℂ`, through
`Sym ℂ 1 ≃ₜ ℂ`. -/
def framedVortexModuliHomeomorphOne :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortices 1 1) ≃ₜ ℂ :=
  (framedVortexModuliHomeomorph one_pos 1).trans Sym.oneHomeomorph.symm

/-- The orbit of a framed degree-`1` vortex goes to the zero of its section. -/
theorem framedVortexModuliHomeomorphOne_mk (x : framedVortices 1 1) :
    Sym.oneEquiv (framedVortexModuliHomeomorphOne (Quotient.mk'' x)) =
      framedVortexDivisor ((framedVortexEquiv 1 1).symm x) := by
  simp [framedVortexModuliHomeomorphOne]

/-- **A degree-`1` vortex is a translate of the centred one.** If `y` is a framed degree-`1`
vortex with zero divisor `{0}`, then a framed degree-`1` vortex `x` has zero divisor `{z₀}`
exactly when it is the translate of `y` by `z₀`, `z ↦ y (z - z₀)`, up to framed gauge. -/
theorem exists_framedGaugeGroup_smul_translateFramedVortex_eq {x y : framedVortexSubMulAction 1 1}
    (hy : framedVortexDivisor y = Sym.oneEquiv 0) (z₀ : ℂ) :
    (∃ g : framedGaugeGroup, g • translateFramedVortex (-z₀) y = x) ↔
      framedVortexDivisor x = Sym.oneEquiv z₀ := by
  rw [exists_framedGaugeGroup_smul_translateFramedVortex_eq_iff, hy]
  congr!
  exact Sym.coe_injective (by simp)

/-! ### Zero divisors record the oriented order of vanishing -/

/-- **The section `w ↦ conj w` has no zero divisor.** At the origin no factorization
`conj w = wⁿ v(w)` with `v` continuous and nonzero at `0` exists: for `n = 0` it would force
`v(0) = 0`; for `n = 1`, `v` would be `1` on the real axis and `-1` on the imaginary axis; for
`n ≥ 2`, `w^(n-1) v(w) = 1` on the real axis would tend to `0`. -/
theorem not_isZeroMultiplicity_conj (n : ℂ → ℕ) : ¬IsZeroMultiplicity (starRingEnd ℂ) n := by
  intro h
  obtain ⟨v, hv, hv0, hev⟩ := isZeroMultiplicity_iff.1 h 0
  simp only [sub_zero] at hev
  -- Restrictions of `v` to the punctured real and imaginary axes near `0`.
  have hline (u : ℂ) :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, starRingEnd ℂ (t * u) = (t * u) ^ n 0 * v (t * u) ∧ (t : ℂ) ≠ 0 :=
    (((continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp)).eventually hev).filter_mono
      nhdsWithin_le_nhds |>.and (eventually_mem_nhdsWithin.mono fun t ht ↦ ofReal_ne_zero.2 ht)
  have hlim (u : ℂ) : Tendsto (fun t : ℝ ↦ v (t * u)) (𝓝[≠] 0) (𝓝 (v 0)) :=
    (hv.tendsto.comp ((continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp))).mono_left
      nhdsWithin_le_nhds
  rcases Nat.lt_or_ge (n 0) 2 with hn | hn
  · interval_cases hn0 : n 0
    · -- `n = 0`: the factorization at `0` itself gives `v 0 = 0`.
      exact hv0 (by simpa [hn0] using hev.self_of_nhds.symm)
    · -- `n = 1`: `v = 1` on the real axis and `v = -1` on the imaginary axis.
      have h₁ : Tendsto (fun t : ℝ ↦ v (t * 1)) (𝓝[≠] 0) (𝓝 1) :=
        tendsto_const_nhds.congr' <| (hline 1).mono fun t ⟨ht, ht0⟩ ↦ by
          simp only [pow_one, mul_one, conj_ofReal] at ht ⊢
          exact ((mul_eq_left₀ ht0).1 ht.symm).symm
      have h₂ : Tendsto (fun t : ℝ ↦ v (t * I)) (𝓝[≠] 0) (𝓝 (-1)) :=
        tendsto_const_nhds.congr' <| (hline I).mono fun t ⟨ht, ht0⟩ ↦ by
          rw [pow_one, map_mul, conj_ofReal, conj_I] at ht
          beta_reduce
          refine mul_left_cancel₀ (mul_ne_zero ht0 I_ne_zero) ?_
          rw [← ht]
          ring
      have e₁ := tendsto_nhds_unique (hlim 1) h₁
      have e₂ := tendsto_nhds_unique (hlim I) h₂
      rw [e₁] at e₂
      norm_num at e₂
  · -- `n ≥ 2`: `t^(n-1) v(t) = 1` for real `t ≠ 0`, while its limit at `0` is `0`.
    have h₁ : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (n 0 - 1) * v (t * 1)) (𝓝[≠] 0) (𝓝 1) :=
      tendsto_const_nhds.congr' <| (hline 1).mono fun t ⟨ht, ht0⟩ ↦ by
        rw [mul_one, conj_ofReal] at ht
        beta_reduce
        rw [mul_one]
        have hpow : (t : ℂ) ^ n 0 = t * t ^ (n 0 - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega)]
        rw [hpow, mul_assoc] at ht
        exact ((mul_eq_left₀ ht0).1 ht.symm).symm
    have h₀ : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (n 0 - 1) * v (t * 1)) (𝓝[≠] 0) (𝓝 0) := by
      have hp : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (n 0 - 1)) (𝓝[≠] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (n 0 - 1)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (n 0 - 1) : ℂ)) :=
          (continuous_ofReal.pow _).tendsto 0
        rw [ofReal_zero, zero_pow (by omega)] at this
        exact this.mono_left nhdsWithin_le_nhds
      simpa using hp.mul (hlim 1)
    exact one_ne_zero (tendsto_nhds_unique h₁ h₀)

/-! ### The flat scaling -/

/-- **The coupling-`2` equation has coefficient `1/4`.** Its curvature row is
`*iF_a - (1 - |α|²) / 4`. -/
theorem coupledEquation_two_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledEquation 2 x z 0 = fderiv ℝ (fun w ↦ x w 0) z I - fderiv ℝ (fun w ↦ x w 1) z 1 -
      (1 - ‖sectionValue x z‖ ^ 2) / 4 := by
  rw [coupledEquation_apply_zero, sq_norm_sectionValue]
  ring

/-- **The coordinate `w = √r y` gives coefficient `1/4`.** A field solves the equation
`*iF_a = (r/4) (1 - |α|²)`, of coupling `2 r`, exactly when its pullback to the coordinate
`w = √r y` solves the coupling-`2` equation `*iF_a = (1 - |α|²) / 4`, not the normalized plane
vortex equation of the coordinate `w = √(2r) y`
(`TauCeti.Vortex.equation_dilateField_inv_sqrt_eq_zero_iff`). -/
theorem coupledEquation_two_dilateField_inv_sqrt_eq_zero_iff {r : ℝ} (hr : 0 < r)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    coupledEquation 2 (dilateField (√r)⁻¹ x) = 0 ↔ coupledEquation (2 * r) x = 0 := by
  have hc : (√r)⁻¹ ^ 2 * (2 * r) = 2 := by
    rw [inv_pow, Real.sq_sqrt hr.le]
    field_simp
  simpa only [hc] using
    coupledEquation_dilateField_eq_zero_iff (2 * r) (t := (√r)⁻¹) (inv_ne_zero (by positivity)) x

end TauCeti.Examples.PlaneVortex
