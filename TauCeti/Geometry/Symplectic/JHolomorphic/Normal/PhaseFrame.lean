/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.TwistedKernel
import Mathlib.Algebra.CharP.Two
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The twisted normal operators of a torus in a phase frame

Let `C = ℂ ⧸ Λ` be an embedded pseudoholomorphic torus, with normal Cauchy–Riemann operator
`D v = ∂bar v + ν v + μ conj v` in a `Λ`-periodic unitary frame of its normal line. Taubes's labels
of `C` are read off from `D` twisted by each of the four real flat sign lines `χ : Λ → ZMod 2` of
the torus, acting on the maps `v : ℂ → ℂ` with `v (z + ω) = (-1) ^ χ ω v z`
(`TauCeti.signTwisted`); its kernel is `TauCeti.signTwisted ℝ Λ.subtype χ ⊓
TauCeti.cauchyRiemannKernel ν μ`. This file shows that each twisted operator is, in a suitable
unitary frame, an operator of the same form on `Λ`-periodic maps, that is on sections of the
trivial line over the torus.

**Change of frame.** Writing a section as `v = e w` for a nowhere vanishing real-differentiable
function `e`, the Leibniz rule `∂bar (e w) = e ∂bar w + w ∂bar e` gives

`D (e w) = e (∂bar w + (ν + ∂bar e / e) w + (μ conj e / e) conj w)`.

So `e w` solves `D` exactly when `w` solves the operator with coefficients `ν + ∂bar e / e` and
`μ conj e / e` (`TauCeti.mul_mem_cauchyRiemannKernel_iff`); this is the law
`g ν' - ∂bar g = (ν ∘ φ) g conj φ'`, `g μ' = (μ ∘ φ) conj g conj φ'` of
`TauCeti.isJHolomorphicOn_prodMk_mul_normalModelStructure_iff` with `φ = id`, read on solutions
rather than on the normal model structure. If `e` is twisted by `χ`, multiplication by `e`
carries maps twisted by `χ'` to maps twisted by `χ + χ'` (`TauCeti.mul_mem_signTwisted`), and
restricts to a linear equivalence between the two twisted kernels
(`TauCeti.twistedKernelFrameEquiv`).

**The phase of a sign character.** For a real linear form `c` on `ℂ`, the phase
`e_c (z) = exp (2π i c z)` (`TauCeti.linearPhase`) has modulus one,
`∂bar e_c = π i (c 1 + i c i) e_c` and `conj e_c / e_c = e_(-2c)`. It is twisted by `χ` when
`exp (2π i c ω) = (-1) ^ χ ω` on the lattice (`TauCeti.linearPhase_mem_signTwisted`), and then
`e_(-2c)` is `Λ`-periodic (`TauCeti.linearPhase_neg_two_smul_periodic`). Such a form `c` is a lift
of the sign character, read as the unitary character `ω ↦ (-1) ^ χ ω`, to a real linear form; for
a full lattice one is obtained by prescribing `c bᵢ = χ(bᵢ) / 2` on a `ℤ`-basis `bᵢ`, which is an
`ℝ`-basis of `ℂ`.

**The twisted operators as periodic operators.** Consequently, for such a lift `c`, the kernel of
`D` twisted by `χ` is isomorphic, by multiplication by `e_c`, to the kernel on `Λ`-periodic maps of
the operator `∂bar + (ν + κ) + μ ρ conj` with the constant `κ = π i (c 1 + i c i)` and the smooth
`Λ`-periodic function `ρ = e_(-2c)` of modulus one (`TauCeti.phaseKernelEquiv`). For `Λ`-periodic
(and smooth) `ν` and `μ` the new coefficients are again `Λ`-periodic (and smooth), so the twisted
operator becomes a real Cauchy–Riemann operator of the form `∂bar + ν' + μ' conj` on the trivial
line `C × ℂ`, and it has no kernel exactly when this periodic operator has none
(`TauCeti.signTwisted_inf_cauchyRiemannKernel_eq_bot_iff`). The frame preserves the
complex-linear reference: `μ' = μ ρ` vanishes exactly when `μ` does. On the trivial line of a closed
surface, `∂bar` plus a zeroth-order term is the setting of the Fredholm realizations
`TauCeti.IsRealCauchyRiemannOperator.isFredholm_perturbedSobolevL`; the realizations on the torus
itself are not constructed here.

The flat real line of `χ` is the line bundle with transition functions `±1`; as a complex line it
is trivial, and `e_c` is a unitary trivialization of it which is not flat. This is why the
coefficient `ν` changes by the constant `κ`, the `(0,1)`-part of the connection form `e_c⁻¹ de_c`
of the frame.

## Main definitions

* `TauCeti.frameMulEquiv e he`: multiplication by a nowhere vanishing function, as a real linear
  automorphism of the maps `ℂ → ℂ`.
* `TauCeti.twistedKernelFrameEquiv`: the change of frame on twisted kernels.
* `TauCeti.linearPhase c`: the phase `z ↦ exp (2π i c z)` of a real linear form `c`.
* `TauCeti.phaseKernelEquiv`: a twisted kernel in the phase frame of its sign character.

## Main results

* `TauCeti.mul_mem_cauchyRiemannKernel_iff`: the coefficients of `D` in a new frame.
* `TauCeti.map_frameMulEquiv_signTwisted_inf_cauchyRiemannKernel`: multiplication by a twisted
  frame identifies the twisted kernels.
* `TauCeti.linearPhase_mem_signTwisted`, `TauCeti.linearPhase_neg_two_smul_periodic`,
  `TauCeti.conjWirtingerDeriv_linearPhase`: the phase of a lift of a sign character, its twisting
  and its connection form.
* `TauCeti.signTwisted_inf_cauchyRiemannKernel_eq_bot_iff`: a twisted operator is nondegenerate
  exactly when its periodic operator in the phase frame is.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 (real Cauchy–Riemann operators and changes of trivialization).
-/

public section

open Complex ComplexConjugate
open scoped Real

noncomputable section

namespace TauCeti

/-! ### Change of frame -/

section Frame

variable {ν μ : ℂ → ℂ} {e w : ℂ → ℂ}

/-- Multiplication by a nowhere vanishing function `e : ℂ → ℂ`, a change of frame (trivialization)
of the normal line, as a real linear automorphism of the maps `ℂ → ℂ`. -/
def frameMulEquiv (e : ℂ → ℂ) (he : ∀ z, e z ≠ 0) : (ℂ → ℂ) ≃ₗ[ℝ] (ℂ → ℂ) :=
  (LinearEquiv.smulOfUnit ⟨e, e⁻¹, funext fun z ↦ mul_inv_cancel₀ (he z),
    funext fun z ↦ inv_mul_cancel₀ (he z)⟩).restrictScalars ℝ

@[simp]
theorem frameMulEquiv_apply (he : ∀ z, e z ≠ 0) (w : ℂ → ℂ) :
    frameMulEquiv e he w = e * w :=
  (rfl)

@[simp]
theorem frameMulEquiv_symm_apply (he : ∀ z, e z ≠ 0) (v : ℂ → ℂ) :
    (frameMulEquiv e he).symm v = e⁻¹ * v :=
  (rfl)

/-- **The normal operator in a new frame.** For a nowhere vanishing real-differentiable `e`, the
product `e w` solves `∂bar v + ν v + μ conj v = 0` exactly when `w` solves the operator with
coefficients `ν + ∂bar e / e` and `μ conj e / e`. -/
theorem mul_mem_cauchyRiemannKernel_iff (he : Differentiable ℝ e) (he₀ : ∀ z, e z ≠ 0) :
    e * w ∈ cauchyRiemannKernel ν μ ↔
      w ∈ cauchyRiemannKernel (fun z ↦ ν z + conjWirtingerDeriv e z 1 / e z)
        (fun z ↦ μ z * conj (e z) / e z) := by
  have hdiff : Differentiable ℝ (e * w) ↔ Differentiable ℝ w := by
    refine ⟨fun h ↦ ?_, he.mul⟩
    have hinv : Differentiable ℝ e⁻¹ := he.inv he₀
    convert hinv.mul h using 1
    ext z
    simp [← mul_assoc, inv_mul_cancel₀ (he₀ z)]
  rw [mem_cauchyRiemannKernel, mem_cauchyRiemannKernel, hdiff]
  refine and_congr_right fun hw ↦ forall_congr' fun z ↦ ?_
  have hd : conjWirtingerDeriv (e * w) z 1 =
      e z * conjWirtingerDeriv w z 1 + w z * conjWirtingerDeriv e z 1 := by
    rw [Pi.mul_def, conjWirtingerDeriv_fun_mul (he z) (hw z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hez := he₀ z
  rw [hd, Pi.mul_apply, map_mul]
  constructor <;> intro h
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h

variable {G : Type*} [AddCommGroup G] {j : G →+ ℂ} {χ χ' : G →+ ZMod 2}

/-- **Multiplication by a twisted frame identifies twisted kernels.** If `e` is real
differentiable, vanishes nowhere and is twisted by `χ`, multiplication by `e` carries the
solutions twisted by `χ'` of the operator with coefficients `ν + ∂bar e / e` and `μ conj e / e`
onto the solutions twisted by `χ + χ'` of `∂bar + ν + μ conj`. -/
theorem map_frameMulEquiv_signTwisted_inf_cauchyRiemannKernel (he : Differentiable ℝ e)
    (he₀ : ∀ z, e z ≠ 0) (heχ : e ∈ signTwisted ℝ j χ) :
    (signTwisted ℝ j χ' ⊓ cauchyRiemannKernel (fun z ↦ ν z + conjWirtingerDeriv e z 1 / e z)
        (fun z ↦ μ z * conj (e z) / e z)).map (frameMulEquiv e he₀ : (ℂ → ℂ) →ₗ[ℝ] (ℂ → ℂ)) =
      signTwisted ℝ j (χ + χ') ⊓ cauchyRiemannKernel ν μ := by
  ext v
  rw [Submodule.mem_map_equiv, Submodule.mem_inf, Submodule.mem_inf, frameMulEquiv_symm_apply,
    ← mul_mem_cauchyRiemannKernel_iff he he₀]
  have hv : e * (e⁻¹ * v) = v := by
    ext z
    simp [← mul_assoc, mul_inv_cancel₀ (he₀ z)]
  rw [hv]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [hv] using mul_mem_signTwisted heχ h
  · have h' := mul_mem_signTwisted (inv_mem_signTwisted heχ) h
    have hχ : χ + (χ + χ') = χ' := by
      ext g
      simp only [AddMonoidHom.add_apply, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rwa [hχ] at h'

/-- **The change of frame on twisted kernels.** For a real-differentiable, nowhere vanishing `e`
twisted by `χ`, multiplication by `e` is a linear equivalence from the kernel twisted by `χ'` of
the operator with coefficients `ν + ∂bar e / e` and `μ conj e / e` onto the kernel twisted by
`χ + χ'` of `∂bar + ν + μ conj`. -/
def twistedKernelFrameEquiv (he : Differentiable ℝ e) (he₀ : ∀ z, e z ≠ 0)
    (heχ : e ∈ signTwisted ℝ j χ) :
    ↥(signTwisted ℝ j χ' ⊓ cauchyRiemannKernel (fun z ↦ ν z + conjWirtingerDeriv e z 1 / e z)
        (fun z ↦ μ z * conj (e z) / e z)) ≃ₗ[ℝ]
      ↥(signTwisted ℝ j (χ + χ') ⊓ cauchyRiemannKernel ν μ) :=
  (frameMulEquiv e he₀).ofSubmodules _ _
    (map_frameMulEquiv_signTwisted_inf_cauchyRiemannKernel he he₀ heχ)

@[simp]
theorem coe_twistedKernelFrameEquiv_apply (he : Differentiable ℝ e) (he₀ : ∀ z, e z ≠ 0)
    (heχ : e ∈ signTwisted ℝ j χ)
    (w : ↥(signTwisted ℝ j χ' ⊓ cauchyRiemannKernel (fun z ↦ ν z + conjWirtingerDeriv e z 1 / e z)
        (fun z ↦ μ z * conj (e z) / e z))) :
    (twistedKernelFrameEquiv he he₀ heχ w : ℂ → ℂ) = e * w :=
  (rfl)

@[simp]
theorem coe_twistedKernelFrameEquiv_symm_apply (he : Differentiable ℝ e) (he₀ : ∀ z, e z ≠ 0)
    (heχ : e ∈ signTwisted ℝ j χ) (v : ↥(signTwisted ℝ j (χ + χ') ⊓ cauchyRiemannKernel ν μ)) :
    ((twistedKernelFrameEquiv (χ' := χ') he he₀ heχ).symm v : ℂ → ℂ) = e⁻¹ * v :=
  (rfl)

end Frame

/-! ### The phase of a sign character -/

section Phase

/-- The **linear phase** `z ↦ exp (2π i c z)` of a real linear form `c` on `ℂ`. When
`exp (2π i c ω) = (-1) ^ χ ω` on a lattice, it is a unitary frame of the flat real line of the sign
character `χ` (`TauCeti.linearPhase_mem_signTwisted`). -/
def linearPhase (c : ℂ →L[ℝ] ℝ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * c z)

variable (c : ℂ →L[ℝ] ℝ)

theorem linearPhase_apply (z : ℂ) : linearPhase c z = cexp (2 * π * I * c z) :=
  (rfl)

@[simp]
theorem linearPhase_ne_zero (z : ℂ) : linearPhase c z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem norm_linearPhase (z : ℂ) : ‖linearPhase c z‖ = 1 := by
  rw [linearPhase_apply, Complex.norm_exp]
  simp

/-- The phase turns sums into products. -/
theorem linearPhase_add (z w : ℂ) : linearPhase c (z + w) = linearPhase c z * linearPhase c w := by
  simp only [linearPhase_apply, map_add, ofReal_add, mul_add, Complex.exp_add]

/-- The conjugate of the phase, divided by the phase, is the phase of `-2 c`. -/
theorem conj_linearPhase_div (z : ℂ) :
    conj (linearPhase c z) / linearPhase c z = linearPhase (-2 • c) z := by
  rw [div_eq_iff (linearPhase_ne_zero c z)]
  simp only [linearPhase_apply]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, smul_apply, map_ofNat]
  push_cast
  ring

/-- The derivative of the phase: `d e_c = 2π i e_c c`. -/
theorem hasFDerivAt_linearPhase (z : ℂ) :
    HasFDerivAt (linearPhase c)
      (linearPhase c z • ((2 * π * I) • (ofRealCLM.comp c).restrictScalars ℝ)) z := by
  have h : HasFDerivAt (fun y : ℂ ↦ 2 * π * I * (c y : ℂ))
      ((2 * π * I) • (ofRealCLM.comp c).restrictScalars ℝ) z :=
    ((ofRealCLM.comp c).restrictScalars ℝ).hasFDerivAt.const_smul (2 * π * I)
  exact h.cexp

theorem fderiv_linearPhase (z : ℂ) :
    fderiv ℝ (linearPhase c) z =
      linearPhase c z • ((2 * π * I) • (ofRealCLM.comp c).restrictScalars ℝ) :=
  (hasFDerivAt_linearPhase c z).fderiv

theorem differentiable_linearPhase : Differentiable ℝ (linearPhase c) :=
  fun z ↦ (hasFDerivAt_linearPhase c z).differentiableAt

theorem contDiff_linearPhase {n : WithTop ℕ∞} : ContDiff ℝ n (linearPhase c) :=
  (contDiff_const.mul (ofRealCLM.contDiff.comp c.contDiff)).cexp

/-- **The connection form of the phase frame.** `∂bar e_c = π i (c 1 + i c i) e_c`. -/
theorem conjWirtingerDeriv_linearPhase (z : ℂ) :
    conjWirtingerDeriv (linearPhase c) z 1 = π * I * (c 1 + I * c I) * linearPhase c z := by
  rw [conjWirtingerDeriv_apply, fderiv_linearPhase]
  simp only [smul_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul, mul_one]
  ring

variable {G : Type*} [AddCommGroup G] {j : G →+ ℂ} {χ : G →+ ZMod 2}

/-- **The phase is a frame of the twisted line.** If `exp (2π i c (j g)) = (-1) ^ χ g` for every
`g`, the phase of `c` is twisted by `χ` along `j`. -/
theorem linearPhase_mem_signTwisted
    (hc : ∀ g, cexp (2 * π * I * c (j g)) = ((hilbertSign (χ g) : ℤ) : ℂ)) :
    linearPhase c ∈ signTwisted ℝ j χ := by
  rw [mem_signTwisted]
  intro g z
  rw [linearPhase_add, linearPhase_apply c (j g), hc g, Units.smul_def, zsmul_eq_mul, mul_comm]

/-- Under the same hypothesis the phase of `-2 c` is periodic along `j`. -/
theorem linearPhase_neg_two_smul_periodic
    (hc : ∀ g, cexp (2 * π * I * c (j g)) = ((hilbertSign (χ g) : ℤ) : ℂ)) (g : G) :
    Function.Periodic (linearPhase (-2 • c)) (j g) := by
  intro z
  rw [linearPhase_add, ← conj_linearPhase_div c (j g), linearPhase_apply c (j g), hc g]
  rcases Int.units_eq_one_or (hilbertSign (χ g)) with h | h <;> simp [h]

/-- **A twisted kernel in the phase frame.** If `exp (2π i c (j g)) = (-1) ^ χ g` for every `g`,
multiplication by the phase `e_c` is a linear equivalence from the kernel on maps periodic along
`j` of `∂bar + (ν + κ) + μ e_(-2c) conj`, with the constant `κ = π i (c 1 + i c i)`, onto the
kernel of `∂bar + ν + μ conj` on maps twisted by `χ`. -/
def phaseKernelEquiv
    (hc : ∀ g, cexp (2 * π * I * c (j g)) = ((hilbertSign (χ g) : ℤ) : ℂ)) (ν μ : ℂ → ℂ) :
    ↥(signTwisted ℝ j 0 ⊓ cauchyRiemannKernel (fun z ↦ ν z + π * I * (c 1 + I * c I))
        (fun z ↦ μ z * linearPhase (-2 • c) z)) ≃ₗ[ℝ]
      ↥(signTwisted ℝ j χ ⊓ cauchyRiemannKernel ν μ) :=
  (LinearEquiv.ofEq _ _ (by
      congr 2 <;> ext z
      · rw [conjWirtingerDeriv_linearPhase, mul_div_cancel_right₀ _ (linearPhase_ne_zero c z)]
      · rw [mul_div_assoc, conj_linearPhase_div])).trans
    ((twistedKernelFrameEquiv (χ' := 0) (differentiable_linearPhase c) (linearPhase_ne_zero c)
      (linearPhase_mem_signTwisted c hc)).trans (LinearEquiv.ofEq _ _ (by rw [add_zero])))

@[simp]
theorem coe_phaseKernelEquiv_apply
    (hc : ∀ g, cexp (2 * π * I * c (j g)) = ((hilbertSign (χ g) : ℤ) : ℂ)) (ν μ : ℂ → ℂ)
    (w : ↥(signTwisted ℝ j 0 ⊓ cauchyRiemannKernel (fun z ↦ ν z + π * I * (c 1 + I * c I))
        (fun z ↦ μ z * linearPhase (-2 • c) z))) :
    (phaseKernelEquiv c hc ν μ w : ℂ → ℂ) = linearPhase c * w :=
  (rfl)

@[simp]
theorem coe_phaseKernelEquiv_symm_apply
    (hc : ∀ g, cexp (2 * π * I * c (j g)) = ((hilbertSign (χ g) : ℤ) : ℂ)) (ν μ : ℂ → ℂ)
    (v : ↥(signTwisted ℝ j χ ⊓ cauchyRiemannKernel ν μ)) :
    ((phaseKernelEquiv c hc ν μ).symm v : ℂ → ℂ) = (linearPhase c)⁻¹ * v :=
  (rfl)

/-- **Nondegeneracy of a twisted operator is that of a periodic operator.** If
`exp (2π i c (j g)) = (-1) ^ χ g` for every `g`, then `∂bar + ν + μ conj` has no nonzero solution
twisted by `χ` exactly when `∂bar + (ν + κ) + μ e_(-2c) conj`, with `κ = π i (c 1 + i c i)`, has
no nonzero solution periodic along `j`. -/
theorem signTwisted_inf_cauchyRiemannKernel_eq_bot_iff
    (hc : ∀ g, cexp (2 * π * I * c (j g)) = ((hilbertSign (χ g) : ℤ) : ℂ)) (ν μ : ℂ → ℂ) :
    signTwisted ℝ j χ ⊓ cauchyRiemannKernel ν μ = ⊥ ↔
      signTwisted ℝ j 0 ⊓ cauchyRiemannKernel (fun z ↦ ν z + π * I * (c 1 + I * c I))
        (fun z ↦ μ z * linearPhase (-2 • c) z) = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact ⟨fun _ ↦ (phaseKernelEquiv c hc ν μ).toEquiv.subsingleton,
    fun _ ↦ (phaseKernelEquiv c hc ν μ).symm.toEquiv.subsingleton⟩

end Phase

end TauCeti
