/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Theta functions of level `k` with characteristics

Fix `k : ℕ`, `τ` in the upper half-plane and real characteristics `α, β`. The entire functions
`s : ℂ → ℂ` with the automorphy law
`s (z + 1) = e^{2πiα} s z` and `s (z + τ) = e^{2πiβ - πikτ - 2πikz} s z`
are the holomorphic sections, pulled back to the universal cover `ℂ`, of the degree-`k` line bundle
on the complex torus `ℂ / (ℤ + τℤ)` with characteristics `(α, β)`. They form the complex vector
space `TauCeti.thetaSections k τ α β`. For `k > 0` and `im τ > 0` it has dimension `k`
(`TauCeti.finrank_thetaSections`), whatever the characteristics; this is the Kähler quantization of
the torus `ℝ² / ℤ²` with symplectic form `2πℏk dq ∧ dp`.

An explicit basis consists of the theta functions with characteristics
`θ_r(z) = e^{2πi(r + α)z} θ(kz + (r + α)τ - β, kτ)` for `0 ≤ r < k`
(`TauCeti.characteristicTheta`), where `θ = jacobiTheta₂` is Mathlib's two-variable Jacobi theta
function. The coordinates of a section `s` in this basis are the Fourier coefficients
`c_r(s) = ∫₀¹ e^{-2πi(r + α)x} s(x) dx` of the `1`-periodic function `x ↦ e^{-2πiαx} s(x)`
(`TauCeti.thetaSectionsBasis_repr_apply`).

The proof is the classical Fourier-series argument. Moving the line of integration from `ℝ` to
`ℝ + τ` (Cauchy's theorem) turns the second automorphy law into the recursion
`c_m(s) = e^{2πiβ - πikτ - 2πi(m + α)τ} c_(m+k)(s)`, so the coefficients `c_0, …, c_(k-1)`
determine all the others. A continuous periodic function with vanishing Fourier coefficients is
zero, and an entire function vanishing on `[0, 1]` is zero, so `s ↦ (c_0(s), …, c_(k-1)(s))` is
injective. Integrating the theta series termwise gives `c_m(θ_r) = δ_{mr}`, so it is also
surjective; the termwise integration is `TauCeti.integral_cexp_mul_jacobiTheta₂_mul_add`.

## Main definitions

* `TauCeti.thetaSections k τ α β`: the entire functions with the automorphy law above.
* `TauCeti.characteristicTheta k τ α β r`: the theta function `θ_r` with characteristics.
* `TauCeti.thetaSectionsBasis`: for `k > 0` and `im τ > 0`, the basis `(θ_r)_{0 ≤ r < k}` of
  `thetaSections k τ α β`.

## Main results

* `TauCeti.characteristicTheta_mem_thetaSections`: each `θ_r` is a section.
* `TauCeti.thetaSectionsBasis_apply`, `TauCeti.thetaSectionsBasis_repr_apply`: the basis vectors
  are the `θ_r`, and the coordinates are the Fourier coefficients `c_r`.
* `TauCeti.finrank_thetaSections`: for `k > 0` and `im τ > 0`, `thetaSections k τ α β` has
  dimension `k`.

## References

* D. Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapters I and II.
-/

public section

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace TauCeti

/-- The holomorphic sections of the level-`k` theta line with characteristics `(α, β)` on the
complex torus `ℂ / (ℤ + τℤ)`, pulled back to the universal cover `ℂ`: the entire functions `s`
with `s (z + 1) = e^{2πiα} s z` and `s (z + τ) = e^{2πiβ - πikτ - 2πikz} s z` for all `z`. -/
def thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {s | Differentiable ℂ s ∧ (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
    ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z}
  add_mem' := by
    rintro f g ⟨hf, hf1, hfτ⟩ ⟨hg, hg1, hgτ⟩
    exact ⟨hf.add hg, fun z ↦ by simp [hf1, hg1, mul_add], fun z ↦ by simp [hfτ, hgτ, mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, fun z ↦ by simp, fun z ↦ by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hfτ⟩
    exact ⟨hf.const_smul c, fun z ↦ by simp [hf1]; ring, fun z ↦ by simp [hfτ]; ring⟩

variable {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}

/-- Membership in `thetaSections k τ α β`: being entire with the two automorphy laws. -/
theorem mem_thetaSections_iff : s ∈ thetaSections k τ α β ↔ Differentiable ℂ s ∧
    (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
    ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z :=
  Iff.rfl

/-- The theta function of level `k` with characteristics `(α, β)` and index `r`:
`θ_r(z) = e^{2πi(r + α)z} θ(kz + (r + α)τ - β, kτ)`, where `θ = jacobiTheta₂`. Its Fourier series is
`∑_n e^{πikn²τ + 2πin((r + α)τ - β)} e^{2πi(r + kn + α)z}`, supported on the frequencies `≡ r`
modulo `k`. -/
noncomputable def characteristicTheta (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ)

/-- Unfolding `TauCeti.characteristicTheta`. -/
theorem characteristicTheta_apply (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r z =
      cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) :=
  (rfl)

/-- Each theta function with characteristics is a section of the level-`k` theta line. -/
theorem characteristicTheta_mem_thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) :
    characteristicTheta k τ α β r ∈ thetaSections k τ α β := by
  refine ⟨?_, fun z ↦ ?_, fun z ↦ ?_⟩
  · by_cases hτ : 0 < (k * τ).im
    · intro z
      exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ cexp (2 * π * I * (r + α) * z)) z).mul
        ((differentiableAt_jacobiTheta₂_fst _ hτ).comp z (by fun_prop))
    · have h0 : characteristicTheta k τ α β r = 0 := funext fun z ↦ by
        simp [characteristicTheta_apply, jacobiTheta₂_undef _ (not_lt.1 hτ)]
      rw [h0]
      exact differentiable_const 0
  · have hθ : jacobiTheta₂ (k * (z + 1) + (r + α) * τ - β) (k * τ) =
        jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) := by
      have hper : Function.Periodic (jacobiTheta₂ · (k * τ)) 1 :=
        fun w ↦ jacobiTheta₂_add_left w (k * τ)
      convert hper.nat_mul k (k * z + (r + α) * τ - β) using 2
      ring
    rw [characteristicTheta_apply, characteristicTheta_apply, hθ, ← mul_assoc, ← exp_add,
      show 2 * π * I * (r + α) * (z + 1) =
        2 * π * I * α + 2 * π * I * (r + α) * z + r * (2 * π * I) by ring,
      exp_add _ (r * (2 * π * I)), exp_int_mul_two_pi_mul_I, mul_one]
  · have hθ : jacobiTheta₂ (k * (z + τ) + (r + α) * τ - β) (k * τ) =
        cexp (-π * I * (k * τ + 2 * (k * z + (r + α) * τ - β))) *
          jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) := by
      rw [← jacobiTheta₂_add_left']
      ring_nf
    rw [characteristicTheta_apply, characteristicTheta_apply, hθ, ← mul_assoc, ← mul_assoc,
      ← exp_add, ← exp_add]
    ring_nf

/-! ### Fourier coefficients of a section -/

/-- The Fourier coefficient `c_m(s) = ∫₀¹ e^{-2πi(m + α)x} s(x) dx`. -/
private noncomputable def thetaCoeff (α : ℝ) (m : ℤ) (s : ℂ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cexp (-(2 * π * I * (m + α) * x)) * s x

private lemma intervalIntegrable_thetaCoeff (hs : Differentiable ℂ s) (α : ℝ) (m : ℤ) :
    IntervalIntegrable (fun x : ℝ ↦ cexp (-(2 * π * I * (m + α) * x)) * s x) volume 0 1 :=
  ((by fun_prop : Continuous fun x : ℝ ↦ cexp (-(2 * π * I * (m + α) * x))).mul
    (hs.continuous.comp continuous_ofReal)).intervalIntegrable 0 1

/-- Moving the line of integration from `ℝ` to `ℝ + τ` turns the second automorphy law into a
recursion `c_m = e^{2πiβ - πikτ - 2πi(m + α)τ} c_(m+k)` for the Fourier coefficients. -/
private lemma thetaCoeff_eq_mul_thetaCoeff_add (hs : s ∈ thetaSections k τ α β) (m : ℤ) :
    thetaCoeff α m s =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * (m + α) * τ) * thetaCoeff α (m + k) s := by
  obtain ⟨hd, h1, hτ⟩ := hs
  set h : ℂ → ℂ := fun z ↦ cexp (-(2 * π * I * (m + α) * z)) * s z with h_def
  have hper : Function.Periodic h ((1 : ℝ) : ℂ) := fun z ↦ by
    simp only [h_def, ofReal_one, h1, ← mul_assoc, ← exp_add]
    rw [show -(2 * π * I * (m + α) * (z + 1)) + 2 * π * I * α =
      -(2 * π * I * (m + α) * z) + (-m : ℤ) * (2 * π * I) by push_cast; ring,
      exp_add _ ((-m : ℤ) * (2 * π * I)), exp_int_mul_two_pi_mul_I, mul_one]
  have key := hper.intervalIntegral_comp_add_eq_of_differentiable
    ((by fun_prop : Differentiable ℂ fun z : ℂ ↦ cexp (-(2 * π * I * (m + α) * z))).mul hd) τ
  rw [thetaCoeff, thetaCoeff, ← intervalIntegral.integral_const_mul, ← key]
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  simp only [h_def, hτ, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- If the coefficients `c_0, …, c_(k-1)` of a section vanish, then all of them do. -/
private lemma thetaCoeff_eq_zero_of_forall_lt (hs : s ∈ thetaSections k τ α β) (hk : 0 < k)
    (h : ∀ m : ℤ, 0 ≤ m → m < k → thetaCoeff α m s = 0) (m : ℤ) : thetaCoeff α m s = 0 := by
  have step (m : ℤ) : thetaCoeff α m s = 0 ↔ thetaCoeff α (m + k) s = 0 := by
    rw [thetaCoeff_eq_mul_thetaCoeff_add hs m, mul_eq_zero, or_iff_right (exp_ne_zero _)]
  have hq (q : ℤ) : ∀ r : ℤ, 0 ≤ r → r < k → thetaCoeff α (r + k * q) s = 0 := by
    induction q using Int.induction_on with
    | zero => simpa using h
    | succ q ih =>
      intro r hr0 hrk
      have := (step (r + k * q)).1 (ih r hr0 hrk)
      rwa [show r + k * q + k = r + k * (q + 1) by ring] at this
    | pred q ih =>
      intro r hr0 hrk
      refine (step _).2 ?_
      rw [show r + k * (-(q : ℤ) - 1) + k = r + k * -(q : ℤ) by ring]
      exact ih r hr0 hrk
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  rw [← Int.emod_add_mul_ediv m k]
  exact hq _ _ (Int.emod_nonneg m hk'.ne') (Int.emod_lt_of_pos m hk')

/-- A section whose coefficients `c_0, …, c_(k-1)` vanish is zero: all its Fourier coefficients
vanish, so it vanishes on `[0, 1]`, hence everywhere by the identity theorem. -/
private lemma eq_zero_of_thetaCoeff_eq_zero (hs : s ∈ thetaSections k τ α β) (hk : 0 < k)
    (h : ∀ m : ℤ, 0 ≤ m → m < k → thetaCoeff α m s = 0) : s = 0 := by
  have hd := hs.1
  set g : ℝ → ℂ := fun x ↦ cexp (-(2 * π * I * α * x)) * s x with g_def
  have hgc : Continuous g :=
    (by fun_prop : Continuous fun x : ℝ ↦ cexp (-(2 * π * I * α * x))).mul
      (hd.continuous.comp continuous_ofReal)
  have hcoeff (m : ℤ) : fourierCoeffOn zero_lt_one g m = thetaCoeff α m s := by
    rw [fourierCoeffOn_eq_integral, thetaCoeff, sub_zero, div_one, one_smul]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp only [fourier_coe_apply, g_def, smul_eq_mul, ← mul_assoc, ← exp_add]
    congr 2
    push_cast
    ring
  have hIcc : EqOn g 0 (Icc 0 1) :=
    eqOn_Icc_of_fourierCoeffOn_eq zero_lt_one hgc.continuousOn continuousOn_const fun n ↦ by
      rw [hcoeff, thetaCoeff_eq_zero_of_forall_lt hs hk h, fourierCoeffOn_eq_integral]
      simp
  have hzero {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : s x = 0 := by
    simpa [g_def, exp_ne_zero] using hIcc hx
  have hT : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] (1 / 2)) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht ↦ mt (fun h ↦ ofReal_injective h) ht)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] (1 / 2 : ℝ), s (t : ℂ) = 0 :=
    (eventually_of_mem (Icc_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)) fun t ht ↦ hzero ht).filter_mono nhdsWithin_le_nhds
  have hA : AnalyticOnNhd ℂ s univ := fun w _ ↦ hd.analyticAt w
  funext z
  exact hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ _)
    (hT.frequently hev.frequently) (mem_univ z)

/-- The Fourier coefficients of the theta functions with characteristics: for `0 ≤ m, r < k`,
`c_m(θ_r) = δ_{mr}`. -/
private lemma thetaCoeff_characteristicTheta (hk : 0 < k) (hτ : 0 < τ.im) {m r : ℤ} (hm0 : 0 ≤ m)
    (hmk : m < k) (hr0 : 0 ≤ r) (hrk : r < k) :
    thetaCoeff α m (characteristicTheta k τ α β r) = if m = r then 1 else 0 := by
  have hkτ : 0 < ((k : ℂ) * τ).im := by simpa using mul_pos (Nat.cast_pos.2 hk) hτ
  rw [thetaCoeff, intervalIntegral.integral_congr (g := fun x : ℝ ↦
      cexp (2 * π * I * (r - m : ℤ) * x) *
        jacobiTheta₂ (((k : ℤ) : ℂ) * x + ((r + α) * τ - β)) (k * τ))
      fun x _ ↦ by
        simp only [characteristicTheta_apply, ← mul_assoc, ← exp_add, add_sub_assoc]
        congr 2
        push_cast
        ring,
    integral_cexp_mul_jacobiTheta₂_mul_add (by exact_mod_cast hk.ne') _ _ hkτ]
  by_cases hmr : m = r
  · simp [hmr, jacobiTheta₂_term]
  · have hdvd : ¬(k : ℤ) ∣ r - m := fun h ↦ hmr <| by
      have := Int.eq_zero_of_abs_lt_dvd h (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
      omega
    simp [hmr, hdvd]

/-- The coefficient map `s ↦ (c_0(s), …, c_(k-1)(s))` on sections. -/
private noncomputable def thetaCoeffMap (k : ℕ) (τ : ℂ) (α β : ℝ) :
    thetaSections k τ α β →ₗ[ℂ] (Fin k → ℂ) where
  toFun s r := thetaCoeff α (r : ℕ) s
  map_add' s t := funext fun r ↦ by
    simp only [Pi.add_apply, thetaCoeff]
    rw [← intervalIntegral.integral_add (intervalIntegrable_thetaCoeff s.property.1 α _)
      (intervalIntegrable_thetaCoeff t.property.1 α _)]
    congr 1 with x
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c s := funext fun r ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, thetaCoeff, RingHom.id_apply,
      ← intervalIntegral.integral_const_mul]
    congr 1 with x
    ring

private lemma thetaCoeffMap_characteristicTheta (hk : 0 < k) (hτ : 0 < τ.im) (r : Fin k) :
    thetaCoeffMap k τ α β ⟨_, characteristicTheta_mem_thetaSections k τ α β (r : ℕ)⟩ =
      Pi.single r 1 := by
  funext m
  rw [thetaCoeffMap, LinearMap.coe_mk, AddHom.coe_mk, thetaCoeff_characteristicTheta hk hτ
    (by omega) (by exact_mod_cast m.isLt) (by omega) (by exact_mod_cast r.isLt), Pi.single_apply]
  simp [Fin.ext_iff]

private lemma thetaCoeffMap_bijective (hk : 0 < k) (hτ : 0 < τ.im) :
    Function.Bijective (thetaCoeffMap k τ α β) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ Subtype.ext ?_, fun v ↦ ?_⟩
  · refine eq_zero_of_thetaCoeff_eq_zero s.property hk fun m hm0 hmk ↦ ?_
    have := congr_fun hs ⟨m.toNat, by omega⟩
    simpa [thetaCoeffMap, Int.toNat_of_nonneg hm0] using this
  · refine ⟨∑ r, v r • ⟨_, characteristicTheta_mem_thetaSections k τ α β (r : ℕ)⟩, ?_⟩
    simp only [map_sum, map_smul, thetaCoeffMap_characteristicTheta hk hτ]
    ext m
    simp [Pi.single_apply]

/-- The basis of the level-`k` theta sections given by the theta functions with characteristics
`θ_r`, `0 ≤ r < k` (`TauCeti.thetaSectionsBasis_apply`). The coordinate of a section `s` along
`θ_r` is its Fourier coefficient `∫₀¹ e^{-2πi(r + α)x} s(x) dx`
(`TauCeti.thetaSectionsBasis_repr_apply`). -/
noncomputable def thetaSectionsBasis (hk : 0 < k) (hτ : 0 < τ.im) (α β : ℝ) :
    Module.Basis (Fin k) ℂ (thetaSections k τ α β) :=
  .ofEquivFun (.ofBijective _ (thetaCoeffMap_bijective (α := α) (β := β) hk hτ))

/-- The basis vectors of `TauCeti.thetaSectionsBasis` are the theta functions with
characteristics. -/
@[simp]
theorem thetaSectionsBasis_apply (hk : 0 < k) (hτ : 0 < τ.im) (r : Fin k) :
    (thetaSectionsBasis hk hτ α β r : ℂ → ℂ) = characteristicTheta k τ α β (r : ℕ) := by
  have h : (LinearEquiv.ofBijective _ (thetaCoeffMap_bijective (α := α) (β := β) hk hτ)).symm
      (Pi.single r 1) = ⟨_, characteristicTheta_mem_thetaSections k τ α β (r : ℕ)⟩ :=
    (LinearEquiv.symm_apply_eq _).2 (thetaCoeffMap_characteristicTheta hk hτ r).symm
  rw [thetaSectionsBasis, Module.Basis.coe_ofEquivFun]
  exact congrArg Subtype.val h

/-- The coordinates of a section in `TauCeti.thetaSectionsBasis` are its Fourier coefficients
`c_r(s) = ∫₀¹ e^{-2πi(r + α)x} s(x) dx`. -/
theorem thetaSectionsBasis_repr_apply (hk : 0 < k) (hτ : 0 < τ.im) (s : thetaSections k τ α β)
    (r : Fin k) :
    (thetaSectionsBasis hk hτ α β).repr s r =
      ∫ x in (0 : ℝ)..1, cexp (-(2 * π * I * ((r : ℕ) + α) * x)) * (s : ℂ → ℂ) x := by
  rw [thetaSectionsBasis, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.ofBijective_apply]
  simp [thetaCoeffMap, thetaCoeff]

/-- **Kähler quantization of the degree-`k` torus.** For `k > 0` and `τ` in the upper half-plane,
the level-`k` theta line on `ℂ / (ℤ + τℤ)` has exactly `k` linearly independent holomorphic
sections, whatever the characteristics `(α, β)`. -/
theorem finrank_thetaSections (hk : 0 < k) (hτ : 0 < τ.im) (α β : ℝ) :
    Module.finrank ℂ (thetaSections k τ α β) = k := by
  simp [Module.finrank_eq_card_basis (thetaSectionsBasis hk hτ α β)]

end TauCeti
