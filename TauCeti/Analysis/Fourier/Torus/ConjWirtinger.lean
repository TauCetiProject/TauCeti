/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Fourier.Torus.Smooth
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# The Cauchy-Riemann operator on the square torus

The square torus `ℂ / (ℤ + iℤ)` is `UnitAddTorus (Fin 2)`, with real coordinates `(s, t)` lifting
to `z = s + i t`. On functions on it, the Cauchy-Riemann operator is
`∂bar = (∂_s + i ∂_t) / 2`. This file shows that `∂bar` maps smooth functions to smooth functions
and multiplies the `n`-th Fourier coefficient by `π i (n₀ + i n₁)`. This multiplier vanishes only
at `n = 0`, and has norm at least `1` elsewhere, so dividing rapidly decreasing coefficients by it
keeps them rapidly decreasing. Hence:

* the kernel of `∂bar` on smooth functions consists of the constant functions;
* its range consists of the smooth functions with mean zero (zeroth Fourier coefficient zero), so
  its cokernel is a copy of `ℂ`, spanned by the class of the constant function `1`; this class is
  detected by integrating against the antiholomorphic `(0, 1)`-forms `c d(conj z)`;
* kernel and cokernel both have complex dimension `1`, so real dimension `2`, and the index of
  `∂bar` on functions on the torus is `0 = 1 · χ(T²) + 2 · 0`.

## Main definitions

* `UnitAddTorus.conjWirtingerDeriv f`: the Cauchy-Riemann operator
  `∂bar f = (∂_s f + i ∂_t f) / 2` on `UnitAddTorus (Fin 2)`.
* `TauCeti.UnitAddTorus.conjWirtingerDerivₗ`: `∂bar` as a complex-linear map on smooth functions.
* `TauCeti.UnitAddTorus.kerConjWirtingerDerivEquiv`: the kernel of `∂bar` on smooth functions
  is a copy of `ℂ`.

## Main results

* `UnitAddTorus.mFourierCoeff_conjWirtingerDeriv`: the Fourier multiplier
  `π i (n₀ + i n₁)` of `∂bar`.
* `conjWirtingerDeriv_eq_zero_iff`: a smooth function is in the kernel of
  `∂bar` if and only if it is constant.
* `UnitAddTorus.exists_conjWirtingerDeriv_eq_iff`: a smooth function is `∂bar` of a smooth
  function if and only if its mean vanishes.
* `TauCeti.UnitAddTorus.ker_conjWirtingerDerivₗ`, `TauCeti.UnitAddTorus.range_conjWirtingerDerivₗ`
  and `TauCeti.UnitAddTorus.cokernelConjWirtingerDerivEquiv`: the kernel, range and cokernel of
  `∂bar` on smooth functions.
* `TauCeti.UnitAddTorus.finrank_ker_conjWirtingerDerivₗ` and
  `TauCeti.UnitAddTorus.finrank_cokernel_conjWirtingerDerivₗ`: complex dimension `1` for kernel
  and cokernel.
* `TauCeti.UnitAddTorus.finrank_real_ker_conjWirtingerDerivₗ`,
  `TauCeti.UnitAddTorus.finrank_real_cokernel_conjWirtingerDerivₗ` and
  `TauCeti.UnitAddTorus.finrank_ker_sub_finrank_cokernel_conjWirtingerDerivₗ`: real dimension `2`
  for kernel and cokernel, and index `0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  American Mathematical Society Colloquium Publications 52, 2012, Appendix C.1 (the Riemann-Roch
  theorem for the Cauchy-Riemann operator on a closed Riemann surface).
-/

public section

noncomputable section

open Complex Filter Topology
open scoped Real ContDiff

namespace TauCeti.UnitAddTorus

/-! ### The Fourier multiplier of the Cauchy-Riemann operator -/

/-- The Fourier multiplier `π i (n₀ + i n₁)` of `∂bar` vanishes only at `n = 0`. -/
theorem conjWirtingerMultiplier_ne_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    (π * I * (n 0 + I * n 1) : ℂ) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero) fun h ↦ hn ?_
  have h0 := congrArg re h
  have h1 := congrArg im h
  simp only [add_re, intCast_re, mul_re, I_re, intCast_im, zero_mul, I_im, one_mul, zero_sub,
    zero_re, add_im, mul_im, zero_im] at h0 h1
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- For `n ≠ 0`, the Fourier multiplier of `∂bar` has norm at least `1`. -/
private theorem one_le_norm_conjWirtingerMultiplier {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    1 ≤ ‖(π * I * (n 0 + I * n 1) : ℂ)‖ := by
  have hz : (n 0 + I * n 1 : ℂ) ≠ 0 := by
    intro h
    exact conjWirtingerMultiplier_ne_zero hn (by rw [h, mul_zero])
  have h1 : 1 ≤ ‖(n 0 + I * n 1 : ℂ)‖ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hn
    have hi' : (1 : ℝ) ≤ |(n i : ℝ)| := by
      exact_mod_cast Int.one_le_abs hi
    fin_cases i
    · refine hi'.trans ((le_of_eq ?_).trans (abs_re_le_norm _))
      simp
    · refine hi'.trans ((le_of_eq ?_).trans (abs_im_le_norm _))
      simp
  rw [norm_mul, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  nlinarith [Real.two_le_pi]

end TauCeti.UnitAddTorus

namespace UnitAddTorus

open TauCeti.UnitAddTorus

/-! ### The Cauchy-Riemann operator -/

/-- The **Cauchy-Riemann operator** `∂bar f = (∂_s f + i ∂_t f) / 2` on functions on the square
torus `UnitAddTorus (Fin 2) = ℂ / (ℤ + iℤ)`, whose real coordinates `(s, t)` lift to
`z = s + i t`. -/
def conjWirtingerDeriv (f : UnitAddTorus (Fin 2) → ℂ) : UnitAddTorus (Fin 2) → ℂ :=
  (2 : ℂ)⁻¹ • (lineDeriv f (Pi.single 0 1) + I • lineDeriv f (Pi.single 1 1))

/-- `∂bar` on the torus is the planar Cauchy-Riemann operator `TauCeti.conjWirtingerDeriv · · 1`
applied to the lift `w ↦ f (Re w, Im w)` of `f` to `ℂ`. -/
theorem conjWirtingerDeriv_coe {f : UnitAddTorus (Fin 2) → ℂ} (hf : f ∈ smoothFunctions (Fin 2))
    (z : ℂ) :
    conjWirtingerDeriv f (fun i ↦ (![z.re, z.im] i : UnitAddCircle)) =
      TauCeti.conjWirtingerDeriv (fun w : ℂ ↦ f fun i ↦ (![w.re, w.im] i : UnitAddCircle)) z 1 := by
  set F := fun y : Fin 2 → ℝ ↦ f fun i ↦ (y i : UnitAddCircle)
  have hF := mem_smoothFunctions.1 hf
  -- The real coordinates `w ↦ (Re w, Im w)` as a continuous real-linear map.
  set φ : ℂ →L[ℝ] Fin 2 → ℝ := ContinuousLinearMap.pi ![reCLM, imCLM]
  have hφ (w : ℂ) : φ w = ![w.re, w.im] := by
    funext i
    fin_cases i <;> simp [φ]
  have hG : (fun w : ℂ ↦ f fun i ↦ (![w.re, w.im] i : UnitAddCircle)) = F ∘ φ := by
    funext w
    simp only [Function.comp_apply, hφ, F]
  have hD (v : ℂ) : fderiv ℝ (F ∘ φ) z v = fderiv ℝ F (φ z) (φ v) := by
    rw [fderiv_comp z (hF.differentiable (by simp) _) φ.differentiableAt, φ.fderiv]
    rfl
  have h1 : φ 1 = Pi.single 0 1 := by
    rw [hφ]
    funext i
    fin_cases i <;> simp
  have hI : φ I = Pi.single 1 1 := by
    rw [hφ]
    funext i
    fin_cases i <;> simp
  rw [hG, TauCeti.conjWirtingerDeriv_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one, hD,
    hD, h1, hI, ← hφ,
    conjWirtingerDeriv, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    lineDeriv_coe _ _ (hF.differentiable (by simp) _),
    lineDeriv_coe _ _ (hF.differentiable (by simp) _)]

/-- `∂bar` maps smooth functions to smooth functions. -/
theorem conjWirtingerDeriv_mem_smoothFunctions {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : f ∈ smoothFunctions (Fin 2)) : conjWirtingerDeriv f ∈ smoothFunctions (Fin 2) := by
  rw [conjWirtingerDeriv]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (lineDeriv_mem_smoothFunctions hf _)
    (Submodule.smul_mem _ _ (lineDeriv_mem_smoothFunctions hf _)))

/-- **The Fourier multiplier of `∂bar`.** On a smooth function, `∂bar` multiplies the `n`-th Fourier
coefficient by `π i (n₀ + i n₁)`. -/
theorem mFourierCoeff_conjWirtingerDeriv {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : f ∈ smoothFunctions (Fin 2)) (n : Fin 2 → ℤ) :
    mFourierCoeff (conjWirtingerDeriv f) n = π * I * (n 0 + I * n 1) * mFourierCoeff f n := by
  have hint (w : Fin 2 → ℝ) : MeasureTheory.Integrable (lineDeriv f w) :=
    integrable_of_mem_smoothFunctions (lineDeriv_mem_smoothFunctions hf w)
  rw [conjWirtingerDeriv, mFourierCoeff_smul, mFourierCoeff_add (hint _) ((hint _).smul I),
    mFourierCoeff_smul, mFourierCoeff_lineDeriv hf, mFourierCoeff_lineDeriv hf]
  simp only [Fin.sum_univ_two, Pi.single_apply, smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, ofReal_one, ofReal_zero, mul_one,
    mul_zero, zero_add]
  ring

/-! ### Kernel and range -/

/-- **The kernel of `∂bar`.** A smooth function on the torus satisfies `∂bar f = 0` if and only if
it is constant. -/
theorem conjWirtingerDeriv_eq_zero_iff {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : f ∈ smoothFunctions (Fin 2)) : conjWirtingerDeriv f = 0 ↔ ∃ c : ℂ, f = fun _ ↦ c := by
  constructor
  · intro h
    refine ⟨mFourierCoeff f 0, ?_⟩
    have hc : (fun _ : UnitAddTorus (Fin 2) ↦ mFourierCoeff f 0) =
        mFourierCoeff f 0 • ⇑(mFourier (0 : Fin 2 → ℤ)) := by
      funext z
      simp [mFourier_zero]
    rw [hc]
    refine eq_of_mFourierCoeff_eq hf
      (Submodule.smul_mem _ _ (mFourier_mem_smoothFunctions 0)) fun n ↦ ?_
    rw [mFourierCoeff_smul, mFourierCoeff_mFourier, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp
    · have h' := mFourierCoeff_conjWirtingerDeriv hf n
      rw [h] at h'
      have h0 : mFourierCoeff (0 : UnitAddTorus (Fin 2) → ℂ) n = 0 := by
        simpa using mFourierCoeff_smul (0 : ℂ) (0 : UnitAddTorus (Fin 2) → ℂ) n
      rw [h0, eq_comm, mul_eq_zero] at h'
      simp [hn, h'.resolve_left (conjWirtingerMultiplier_ne_zero hn)]
  · rintro ⟨c, rfl⟩
    funext z
    simp [conjWirtingerDeriv]

/-- **The range of `∂bar`.** A smooth function `g` on the torus is `∂bar f` for some smooth function
`f` if and only if its mean `mFourierCoeff g 0` vanishes. -/
theorem exists_conjWirtingerDeriv_eq_iff {g : UnitAddTorus (Fin 2) → ℂ}
    (hg : g ∈ smoothFunctions (Fin 2)) :
    (∃ f ∈ smoothFunctions (Fin 2), conjWirtingerDeriv f = g) ↔ mFourierCoeff g 0 = 0 := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    simp [mFourierCoeff_conjWirtingerDeriv hf]
  · intro hg0
    -- Divide the coefficients of `g` by the multiplier; at `n = 0` this gives `0`.
    set c : (Fin 2 → ℤ) → ℂ := fun n ↦ mFourierCoeff g n / (π * I * (n 0 + I * n 1))
    have hcle (n : Fin 2 → ℤ) : ‖c n‖ ≤ ‖mFourierCoeff g n‖ := by
      by_cases hn : n = 0
      · subst hn
        simp [c]
      · rw [norm_div]
        exact div_le_self (norm_nonneg _) (one_le_norm_conjWirtingerMultiplier hn)
    have hc (k : ℕ) : Summable fun n ↦ ‖c n‖ * ‖n‖ ^ k := by
      refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
        (summable_norm_mFourierCoeff_mul_pow hg zero_le_one k)
      rw [one_mul]
      exact mul_le_mul (hcle n) (pow_le_pow_left₀ (norm_nonneg _) (by linarith) k)
        (by positivity) (norm_nonneg _)
    have hc1 : Summable fun n ↦ ‖c n‖ := by simpa using hc 0
    refine ⟨fun z ↦ ∑' n, c n • mFourier n z, tsum_smul_mFourier_mem_smoothFunctions hc, ?_⟩
    refine eq_of_mFourierCoeff_eq
      (conjWirtingerDeriv_mem_smoothFunctions (tsum_smul_mFourier_mem_smoothFunctions hc)) hg
      fun n ↦ ?_
    rw [mFourierCoeff_conjWirtingerDeriv (tsum_smul_mFourier_mem_smoothFunctions hc),
      mFourierCoeff_tsum_smul_mFourier hc1]
    by_cases hn : n = 0
    · subst hn
      simp [hg0]
    · exact mul_div_cancel₀ _ (conjWirtingerMultiplier_ne_zero hn)

/-- `∂bar` is additive on smooth functions. -/
theorem conjWirtingerDeriv_add {f g : UnitAddTorus (Fin 2) → ℂ} (hf : f ∈ smoothFunctions (Fin 2))
    (hg : g ∈ smoothFunctions (Fin 2)) :
    conjWirtingerDeriv (f + g) = conjWirtingerDeriv f + conjWirtingerDeriv g := by
  have hfg := Submodule.add_mem _ hf hg
  have hint {h : UnitAddTorus (Fin 2) → ℂ} (hh : h ∈ smoothFunctions (Fin 2)) :=
    integrable_of_mem_smoothFunctions (conjWirtingerDeriv_mem_smoothFunctions hh)
  refine eq_of_mFourierCoeff_eq (conjWirtingerDeriv_mem_smoothFunctions hfg)
    (Submodule.add_mem _ (conjWirtingerDeriv_mem_smoothFunctions hf)
      (conjWirtingerDeriv_mem_smoothFunctions hg)) fun n ↦ ?_
  rw [mFourierCoeff_conjWirtingerDeriv hfg, mFourierCoeff_add (hint hf) (hint hg),
    mFourierCoeff_conjWirtingerDeriv hf, mFourierCoeff_conjWirtingerDeriv hg,
    mFourierCoeff_add (integrable_of_mem_smoothFunctions hf)
      (integrable_of_mem_smoothFunctions hg), mul_add]

/-- `∂bar` commutes with multiplication by complex scalars on smooth functions. -/
theorem conjWirtingerDeriv_smul {f : UnitAddTorus (Fin 2) → ℂ} (hf : f ∈ smoothFunctions (Fin 2))
    (c : ℂ) : conjWirtingerDeriv (c • f) = c • conjWirtingerDeriv f := by
  have hcf := Submodule.smul_mem _ c hf
  refine eq_of_mFourierCoeff_eq (conjWirtingerDeriv_mem_smoothFunctions hcf)
    (Submodule.smul_mem _ c (conjWirtingerDeriv_mem_smoothFunctions hf)) fun n ↦ ?_
  rw [mFourierCoeff_conjWirtingerDeriv hcf, mFourierCoeff_smul, mFourierCoeff_smul,
    mFourierCoeff_conjWirtingerDeriv hf, smul_eq_mul, smul_eq_mul]
  ring

end UnitAddTorus

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

/-! ### `∂bar` as a linear map on smooth functions -/

/-- The Cauchy-Riemann operator `∂bar` as a complex-linear map on the smooth functions on the square
torus. -/
def conjWirtingerDerivₗ : smoothFunctions (Fin 2) →ₗ[ℂ] smoothFunctions (Fin 2) where
  toFun f := ⟨UnitAddTorus.conjWirtingerDeriv f, conjWirtingerDeriv_mem_smoothFunctions f.2⟩
  map_add' f g := Subtype.ext (UnitAddTorus.conjWirtingerDeriv_add f.2 g.2)
  map_smul' c f := Subtype.ext (conjWirtingerDeriv_smul f.2 c)

@[simp]
theorem coe_conjWirtingerDerivₗ_apply (f : smoothFunctions (Fin 2)) :
    (conjWirtingerDerivₗ f : UnitAddTorus (Fin 2) → ℂ) = UnitAddTorus.conjWirtingerDeriv f :=
  (rfl)

/-- The kernel of `∂bar` on smooth functions is the line of constant functions, spanned by the
constant function `1 = mFourier 0`. -/
theorem ker_conjWirtingerDerivₗ :
    LinearMap.ker conjWirtingerDerivₗ = ℂ ∙ mFourierSmooth (0 : Fin 2 → ℤ) := by
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  have h0 : ⇑(mFourier (0 : Fin 2 → ℤ)) = 1 := by simp [mFourier_zero]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (conjWirtingerDeriv_eq_zero_iff f.2).1 (congrArg Subtype.val h)
    refine ⟨c, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, coe_mFourierSmooth, h0, hc]
    funext z
    simp
  · rintro ⟨c, rfl⟩
    refine Subtype.ext ((conjWirtingerDeriv_eq_zero_iff (c • mFourierSmooth 0).2).2 ⟨c, ?_⟩)
    rw [Submodule.coe_smul, coe_mFourierSmooth, h0]
    funext z
    simp

/-- The range of `∂bar` on smooth functions is the hyperplane of functions with mean zero. -/
theorem range_conjWirtingerDerivₗ :
    LinearMap.range conjWirtingerDerivₗ = LinearMap.ker (mFourierCoeffₗ (0 : Fin 2 → ℤ)) := by
  ext g
  rw [LinearMap.mem_range, LinearMap.mem_ker, mFourierCoeffₗ_apply,
    ← exists_conjWirtingerDeriv_eq_iff g.2]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, f.2, rfl⟩
  · rintro ⟨f, hf, hfg⟩
    exact ⟨⟨f, hf⟩, Subtype.ext hfg⟩

/-- **The cokernel of `∂bar`.** The cokernel of `∂bar` on smooth functions on the torus is
identified with `ℂ` by taking the mean. -/
def cokernelConjWirtingerDerivEquiv :
    (smoothFunctions (Fin 2) ⧸ LinearMap.range conjWirtingerDerivₗ) ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ range_conjWirtingerDerivₗ).trans
    ((mFourierCoeffₗ 0).quotKerEquivOfSurjective fun c ↦
      ⟨c • mFourierSmooth 0, by
        rw [map_smul, mFourierCoeffₗ_zero_mFourierSmooth_zero, smul_eq_mul, mul_one]⟩)

/-- The class of a smooth function `f` in the cokernel of `∂bar` corresponds to the mean of `f`. -/
@[simp]
theorem cokernelConjWirtingerDerivEquiv_mk (f : smoothFunctions (Fin 2)) :
    cokernelConjWirtingerDerivEquiv (Submodule.Quotient.mk f) =
      mFourierCoeff (f : UnitAddTorus (Fin 2) → ℂ) 0 := by
  rw [cokernelConjWirtingerDerivEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    ← mFourierCoeffₗ_apply]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ f

/-- The cokernel of `∂bar` is spanned by the class of the constant function `1`. -/
theorem cokernelConjWirtingerDerivEquiv_mk_mFourierSmooth_zero :
    cokernelConjWirtingerDerivEquiv (Submodule.Quotient.mk (mFourierSmooth 0)) = 1 := by
  rw [cokernelConjWirtingerDerivEquiv_mk, ← mFourierCoeffₗ_apply,
    mFourierCoeffₗ_zero_mFourierSmooth_zero]

/-! ### Dimensions and the index -/

/-- The kernel of `∂bar` on smooth functions is a copy of `ℂ`: the constant function `c` corresponds
to `c`. -/
def kerConjWirtingerDerivEquiv : LinearMap.ker conjWirtingerDerivₗ ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofEq _ _ ker_conjWirtingerDerivₗ).trans
    (LinearEquiv.toSpanNonzeroSingleton ℂ _ _ mFourierSmooth_zero_ne_zero).symm

/-- The scalar `c` corresponds to the constant function `c = c • mFourier 0` in the kernel of
`∂bar`. -/
@[simp]
theorem coe_kerConjWirtingerDerivEquiv_symm_apply (c : ℂ) :
    (kerConjWirtingerDerivEquiv.symm c : smoothFunctions (Fin 2)) = c • mFourierSmooth 0 := by
  rw [kerConjWirtingerDerivEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply, LinearEquiv.toSpanNonzeroSingleton_apply]

/-- A function in the kernel of `∂bar`, a constant, corresponds to its mean. -/
@[simp]
theorem kerConjWirtingerDerivEquiv_apply (f : LinearMap.ker conjWirtingerDerivₗ) :
    kerConjWirtingerDerivEquiv f = mFourierCoeff (f : UnitAddTorus (Fin 2) → ℂ) 0 := by
  conv_rhs => rw [← kerConjWirtingerDerivEquiv.symm_apply_apply f]
  rw [← mFourierCoeffₗ_apply, coe_kerConjWirtingerDerivEquiv_symm_apply, map_smul,
    mFourierCoeffₗ_zero_mFourierSmooth_zero, smul_eq_mul, mul_one]

/-- The kernel of `∂bar` on smooth functions, the constants, has complex dimension `1`. -/
theorem finrank_ker_conjWirtingerDerivₗ :
    Module.finrank ℂ (LinearMap.ker conjWirtingerDerivₗ) = 1 := by
  rw [kerConjWirtingerDerivEquiv.finrank_eq, Module.finrank_self]

/-- The cokernel of `∂bar` on smooth functions on the torus has complex dimension `1`. -/
theorem finrank_cokernel_conjWirtingerDerivₗ :
    Module.finrank ℂ (smoothFunctions (Fin 2) ⧸ LinearMap.range conjWirtingerDerivₗ) = 1 := by
  rw [cokernelConjWirtingerDerivEquiv.finrank_eq, Module.finrank_self]

/-- The kernel of `∂bar` on smooth functions on the torus, the constants, has real dimension `2`. -/
theorem finrank_real_ker_conjWirtingerDerivₗ :
    Module.finrank ℝ (LinearMap.ker conjWirtingerDerivₗ) = 2 := by
  rw [(kerConjWirtingerDerivEquiv.restrictScalars ℝ).finrank_eq, finrank_real_complex]

/-- The cokernel of `∂bar` on smooth functions on the torus has real dimension `2`. -/
theorem finrank_real_cokernel_conjWirtingerDerivₗ :
    Module.finrank ℝ (smoothFunctions (Fin 2) ⧸ LinearMap.range conjWirtingerDerivₗ) = 2 := by
  rw [(cokernelConjWirtingerDerivEquiv.restrictScalars ℝ).finrank_eq, finrank_real_complex]

/-- **The index of `∂bar` on the torus.** On smooth functions on the torus, `∂bar` has index
`dim ker ∂bar - dim coker ∂bar = 0`, which is `n χ(T²) + 2 c₁ = 1 · 0 + 2 · 0` for the trivial line
bundle. -/
theorem finrank_ker_sub_finrank_cokernel_conjWirtingerDerivₗ :
    (Module.finrank ℝ (LinearMap.ker conjWirtingerDerivₗ) : ℤ) -
      Module.finrank ℝ (smoothFunctions (Fin 2) ⧸ LinearMap.range conjWirtingerDerivₗ) = 0 := by
  rw [finrank_real_ker_conjWirtingerDerivₗ, finrank_real_cokernel_conjWirtingerDerivₗ, sub_self]

end TauCeti.UnitAddTorus
