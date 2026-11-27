/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.PoincareSeries
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Multiples without base points, and the canonical multiplier

Let `D = (B, χ)` be an Appell–Humbert datum for a full lattice `L` in a finite-dimensional complex
normed space `V`, with Riemann form `E` (`TauCeti.AppellHumbertData`).

**Base points.** If `E` is positive, then for every `n ≥ 2` the theta functions of the multiple
`n D = (n B, χⁿ)` have no common zero
(`TauCeti.AppellHumbertData.IsPositive.exists_mem_thetaSpace_nsmul_apply_ne_zero`). Write
`n = m + 1` and take a nonzero theta function `f` of `D`. For every `a ∈ V` the product of the
twisted translates of `f ^ m` by `a` and of `f` by `-m a` is a theta function of `n D`: the twists
of the semicharacters, `exp (± 2πi m E (a, ·))`, cancel. At a common zero `z` this product, up to a
nowhere vanishing factor `f (z + a) ^ m f (z - m a)`, vanishes for every `a`; this is a product of
two entire functions of `a`, neither identically zero.

**The canonical multiplier.** Let `b` be a complex linear endomorphism of `V` that is an "adjoint
half" for the Riemann form `E_B` of a form `B`, `E_B (b u, w) + E_B (u, b w) = E_B (u, w)`, with
`E_B (b l, m)` an integer for `l, m ∈ L`. Then `χ_b (x) = exp (πi E_B (x, b x))` is a semicharacter
for `B`, and `(B, χ_b)` is an Appell–Humbert datum
(`TauCeti.AppellHumbertData.ofCanonicalSemichar`). The twisted translations normalised by it,
`N_x = χ_b (x)⁻¹ U_x` (`TauCeti.AppellHumbertData.normalizedTranslate`), satisfy the Heisenberg law
`N_x N_y = exp (2πi E_B (y, b x)) N_(x + y)`
(`TauCeti.AppellHumbertData.normalizedTranslate_normalizedTranslate`), and the theta functions of
`(B, χ_b)` are the entire functions fixed by every `N_l`, `l ∈ L`
(`TauCeti.AppellHumbertData.mem_thetaSpace_ofCanonicalSemichar_iff`).

The Riemann form here is `E = Im H` (`TauCeti.AppellHumbertData.riemannForm`), the negative of the
form `Im (B (u, v) - B (v, u)) / 2π` of the roadmap; so the roadmap's `exp (πi E_B (b x, x))` is
`exp (πi E (x, b x))` here, and its phase `exp (2πi E_B (b x, y))` is `exp (2πi E (y, b x))`.

## Provenance

Adapted from `New.ThetaTori.eq_zero_of_differentiable_of_mul_eq_zero`,
`New.IsAppellHumbert.exists_mem_thetaSpace_nsmul_apply_ne_zero`,
`New.ThetaTori.canonicalMultiplier`, `New.ThetaTori.normalizedShift`,
`New.ThetaTori.mem_thetaSpace_iff_normalizedShift`,
`New.ThetaTori.isAppellHumbert_canonicalMultiplier` and
`New.IsAppellHumbert.normalizedShift_normalizedShift` (file
`src/Lib/Shimura/ComplexTheta/DimensionFormula.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).
The phases are restated for the Riemann form `E = Im H`, and the semicharacter is a map
`L → U(1)` rather than a function on `V` of modulus one on `L`.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Section 3.1 (canonical factors) and Section 4.5 (base-point freeness of `L^n`, `n ≥ 2`).
* D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research, 1970, §17.
-/

public section

open Complex Set Filter
open scoped Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

/-! ### Multiples without base points -/

/-- On a finite-dimensional complex space, if the product of two entire functions vanishes and the
first does not, the second does. -/
private theorem eq_zero_of_mul_eq_zero_of_differentiable [FiniteDimensional ℂ V] {f g : V → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (h : f * g = 0) (hf_ne : f ≠ 0) :
    g = 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hf_ne
  have h_near : g =ᶠ[nhds z] 0 := by
    filter_upwards [(hf z).continuousAt.eventually_ne hz] with w hw
    exact (mul_eq_zero.mp (congrFun h w)).resolve_left hw
  exact AnalyticOnNhd.eq_of_eventuallyEq
    (fun w _ ↦ hg.differentiableOn.analyticAt_of_finiteDimensional univ_mem) analyticOnNhd_const
    h_near

variable {D : AppellHumbertData L}

/-- The twists of the semicharacters of `m D` by `a` and of `D` by `-m a` cancel. -/
private theorem riemannChar_nsmul_mul_riemannChar_neg (m : ℕ) (a : V) :
    (m • D).riemannChar a * D.riemannChar (-(m • a)) = 1 := by
  ext l
  have h0 : (m • D).riemannForm a l + D.riemannForm (-(m • a)) l = 0 := by
    rw [riemannForm_nsmul]
    simp
  rw [mul_apply, riemannChar_apply, riemannChar_apply, ← Circle.exp_add, ← mul_add, h0, mul_zero,
    Circle.exp_zero, one_apply]

/-- **Multiples without base points.** For an Appell–Humbert datum `D` with positive Riemann form
and `n ≥ 2`, the theta functions of `n D` have no common zero: for every `z` some theta function of
`n D` does not vanish at `z`. -/
theorem IsPositive.exists_mem_thetaSpace_nsmul_apply_ne_zero [FiniteDimensional ℂ V]
    [DiscreteTopology L] [IsZLattice ℝ L] (hD : D.IsPositive) {n : ℕ} (hn : 2 ≤ n) (z : V) :
    ∃ f ∈ (n • D).thetaSpace, f z ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  obtain ⟨f, hf, hf_ne⟩ := hD.exists_mem_thetaSpace_ne_zero
  have hf_diff := differentiable_of_mem_thetaSpace hf
  by_contra! h_zero
  -- For each `a`, the product of the translates of `f ^ m` by `a` and of `f` by `-m a`.
  have h_mem (a : V) : (m • D).twistedTranslate a (f ^ m) * D.twistedTranslate (-(m • a)) f ∈
      ((m + 1) • D).thetaSpace := by
    have h := mul_mem_thetaSpace_add
      (twistedTranslate_mem_thetaSpace (pow_mem_thetaSpace_nsmul hf m) a)
      (twistedTranslate_mem_thetaSpace hf (-(m • a)))
    refine (mem_thetaSpace_iff _).mpr ⟨differentiable_of_mem_thetaSpace h, fun l z ↦ ?_⟩
    have hχ := congrArg (fun ψ : AddChar L Circle ↦ (ψ l : ℂ))
      (riemannChar_nsmul_mul_riemannChar_neg (D := D) m a)
    simp only [mul_apply, Circle.coe_mul, one_apply, Circle.coe_one] at hχ
    rw [apply_add_of_mem_thetaSpace h, factor_add, factor_add, factor_add, factor_nsmul,
      factor_nsmul, factor_ofAddChar, factor_ofAddChar, pow_succ]
    linear_combination (D.factor l z ^ m * D.factor l z *
      ((m • D).twistedTranslate a (f ^ m) * D.twistedTranslate (-(m • a)) f) z) * hχ
  -- At `z` the product is `f (z + a) ^ m * f (z - m a)` times a nonzero exponential.
  set F₁ : V → ℂ := fun a ↦ f (z + a) ^ m
  set F₂ : V → ℂ := fun a ↦ f (z - (m : ℂ) • a)
  have hF₁ : Differentiable ℂ F₁ := by fun_prop
  have hF₂ : Differentiable ℂ F₂ := by fun_prop
  have h_mul : F₁ * F₂ = 0 := by
    funext a
    have := h_zero _ (h_mem a)
    simp only [Pi.mul_apply, twistedTranslate_apply, Pi.pow_apply, mul_eq_zero, exp_ne_zero,
      false_or] at this
    simp only [F₁, F₂, Pi.mul_apply, Pi.zero_apply, Nat.cast_smul_eq_nsmul, sub_eq_add_neg]
    rcases this with h | h <;> simp [h]
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hf_ne
  have hw' : f w ≠ 0 := hw
  have h_left : F₁ ≠ 0 :=
    Function.ne_iff.mpr ⟨w - z, by simpa [F₁] using pow_ne_zero m hw'⟩
  -- So `F₂ = 0`, but `a ↦ z - m a` is surjective, so `f` would vanish at `w`.
  have h_right := eq_zero_of_mul_eq_zero_of_differentiable hF₁ hF₂ h_mul h_left
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have := congrFun h_right ((m : ℂ)⁻¹ • (z - w))
  simp only [F₂, smul_smul, mul_inv_cancel₀ hm', one_smul, sub_sub_cancel, Pi.zero_apply] at this
  exact hw' this

/-! ### The canonical multiplier and normalised translations -/

/-- The **Appell–Humbert datum of the canonical multiplier.** Let `B` be a form with symmetric real
part and Riemann form `E_B (u, v) = Im (B (v, u) - B (u, v)) / 2π`, and `b` a complex linear
endomorphism of `V` with `E_B (b u, w) + E_B (u, b w) = E_B (u, w)` and `E_B (b l, m) ∈ ℤ` for
`l, m ∈ L`. Then `χ_b (l) = exp (πi E_B (l, b l))` is a semicharacter for `B`, and `(B, χ_b)` is an
Appell–Humbert datum. -/
noncomputable def ofCanonicalSemichar (B : V →L[ℝ] V →L[ℂ] ℂ)
    (hB : ∀ u v, (B u v).re = (B v u).re) (b : V →L[ℂ] V)
    (hadj : ∀ u w, (B w (b u) - B (b u) w).im / (2 * π) + (B (b w) u - B u (b w)).im / (2 * π) =
      (B w u - B u w).im / (2 * π))
    (hint : ∀ l m : L, ∃ k : ℤ, (B m (b l) - B (b l) m).im / (2 * π) = k) :
    AppellHumbertData L where
  form := B
  re_form_comm := hB
  semichar l := Circle.exp (π * ((B (b l) l - B l (b l)).im / (2 * π)))
  semichar_add_eq_circleExp_mul_mul l m := by
    -- With `E = E_B`, `E (l + m, b (l + m)) = E (l, b l) + E (m, b m) + E (l, m) - 2 E (b l, m)`.
    set E : V → V → ℝ := fun u v ↦ (B v u - B u v).im / (2 * π)
    obtain ⟨k, hk⟩ := hint l m
    have hE_add_left (u u' v : V) : E (u + u') v = E u v + E u' v := by
      simp only [E, map_add, _root_.add_apply, sub_im, add_im]
      ring
    have hE_add_right (u v v' : V) : E u (v + v') = E u v + E u v' := by
      simp only [E, map_add, _root_.add_apply, sub_im, add_im]
      ring
    have hE_swap (u v : V) : E v u = -E u v := by
      simp only [E, ← neg_div, ← neg_im, neg_sub]
    have h_quad : E (l + m) (b (l + m)) =
        E l (b l) + E m (b m) + E l m - 2 * k := by
      have h1 := hadj l m
      change E (b l) m + E l (b m) = E l m at h1
      simp only [map_add, hE_add_left, hE_add_right]
      rw [hE_swap (b l) m]
      change E (b l) m = k at hk
      linarith
    have h_im : (B m l - B l m).im / 2 = π * E l m := by
      simp only [E]
      field_simp
    change Circle.exp (π * E (l + m) (b (l + m))) =
      Circle.exp ((B m l - B l m).im / 2) * Circle.exp (π * E l (b l)) *
        Circle.exp (π * E m (b m))
    rw [h_im, h_quad, ← Circle.exp_add, ← Circle.exp_add,
      show π * (E l (b l) + E m (b m) + E l m - 2 * k) =
        π * E l m + π * E l (b l) + π * E m (b m) + -(2 * π * k) by ring, Circle.exp_add,
      Circle.exp_neg, Circle.exp_two_pi_mul_int, inv_one, mul_one]

variable (D) in
/-- The **normalised translation** `N_x = χ_b (x)⁻¹ U_x` by `x ∈ V`: the twisted translation
divided by the canonical multiplier `χ_b (x) = exp (πi E (x, b x))` of a complex linear map `b`. -/
noncomputable def normalizedTranslate (b : V →L[ℂ] V) (x : V) : (V → ℂ) →ₗ[ℂ] V → ℂ :=
  (Circle.exp (π * D.riemannForm x (b x)) : ℂ)⁻¹ • D.twistedTranslate x

/-- The defining formula of the normalised translation. -/
theorem normalizedTranslate_apply (b : V →L[ℂ] V) (x : V) (f : V → ℂ) :
    D.normalizedTranslate b x f = (Circle.exp (π * D.riemannForm x (b x)) : ℂ)⁻¹ •
      D.twistedTranslate x f := (rfl)

/-- **The Heisenberg law of the normalised translations**: if
`E (b u, w) + E (u, b w) = E (u, w)`, then `N_x N_y = exp (2πi E (y, b x)) N_(x + y)`. -/
theorem normalizedTranslate_normalizedTranslate {b : V →L[ℂ] V}
    (hadj : ∀ u w, D.riemannForm (b u) w + D.riemannForm u (b w) = D.riemannForm u w)
    (x y : V) (f : V → ℂ) :
    D.normalizedTranslate b x (D.normalizedTranslate b y f) =
      (Circle.exp (2 * π * D.riemannForm y (b x)) : ℂ) • D.normalizedTranslate b (x + y) f := by
  -- The multipliers at `x`, `y` and `x + y` contribute `exp (πi (E (x, b y) + E (y, b x)))`.
  have h_exp : D.riemannForm (x + y) (b (x + y)) = D.riemannForm x (b x) +
      D.riemannForm y (b y) + 2 * D.riemannForm x (b y) - D.riemannForm x y := by
    have h1 := hadj x y
    simp only [map_add, LinearMap.add_apply]
    rw [D.riemannForm_swap (b x) y]
    linarith
  have h_phase : D.riemannForm y (b x) = D.riemannForm x (b y) - D.riemannForm x y := by
    have h1 := hadj x y
    rw [D.riemannForm_swap (b x) y]
    linarith
  simp only [normalizedTranslate_apply, map_smul, smul_smul,
    D.twistedTranslate_twistedTranslate x y f]
  congr 1
  rw [h_exp, h_phase]
  simp only [Circle.coe_exp, ← exp_neg, ← exp_add]
  congr 1
  push_cast
  ring

/-- The theta functions of `(B, χ_b)` are the entire functions fixed by the normalised
translations `N_l`, `l ∈ L`. -/
theorem mem_thetaSpace_ofCanonicalSemichar_iff (B : V →L[ℝ] V →L[ℂ] ℂ)
    (hB : ∀ u v, (B u v).re = (B v u).re) (b : V →L[ℂ] V)
    (hadj : ∀ u w, (B w (b u) - B (b u) w).im / (2 * π) + (B (b w) u - B u (b w)).im / (2 * π) =
      (B w u - B u w).im / (2 * π))
    (hint : ∀ l m : L, ∃ k : ℤ, (B m (b l) - B (b l) m).im / (2 * π) = k) {f : V → ℂ} :
    f ∈ (ofCanonicalSemichar B hB b hadj hint).thetaSpace ↔ Differentiable ℂ f ∧
      ∀ l : L, (ofCanonicalSemichar B hB b hadj hint).normalizedTranslate b l f = f := by
  set D' := ofCanonicalSemichar B hB b hadj hint
  have hsc (l : L) : (D'.semichar l : ℂ) = Circle.exp (π * D'.riemannForm l (b l)) := by
    rw [riemannForm_apply]
    rfl
  rw [mem_thetaSpace_iff]
  refine and_congr_right fun _ ↦ ⟨fun h l ↦ funext fun z ↦ ?_, fun h l z ↦ ?_⟩
  · rw [normalizedTranslate_apply, Pi.smul_apply, twistedTranslate_apply, h l z, factor_def,
      smul_eq_mul, exp_neg, ← hsc]
    have he := exp_ne_zero (D'.form l z + D'.form l l / 2)
    have hc := Circle.coe_ne_zero (D'.semichar l)
    generalize exp (D'.form l z + D'.form l l / 2) = e at he ⊢
    field_simp
  · have h' := congrFun (h l) z
    rw [normalizedTranslate_apply, Pi.smul_apply, twistedTranslate_apply, smul_eq_mul, exp_neg,
      ← hsc] at h'
    rw [factor_def]
    have he := exp_ne_zero (D'.form l z + D'.form l l / 2)
    have hc := Circle.coe_ne_zero (D'.semichar l)
    generalize exp (D'.form l z + D'.form l l / 2) = e at he h' ⊢
    field_simp at h'
    linear_combination h'

end TauCeti.AppellHumbertData
