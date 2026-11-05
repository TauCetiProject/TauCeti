/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Deformation
public import TauCeti.Analysis.Complex.Wirtinger.Similarity

/-!
# Isolated zeros and local multiplicities of plane vortex sections

For the section `α = 2(p + i q)`, the two holomorphicity rows of the plane vortex equation
give `bar∂ α = (b₂ - i b₁) α / 2`. The scalar similarity principle therefore factors
every nontrivial section locally as `(w - z)^n v(w)`, with `v` of class `Cᵏ` at `z` and
nonzero there, for `Cᵏ` connection coefficients (`k ≥ 1`).
In particular the zeros are isolated. If `|α| → 1` at infinity, the zero set is finite.
These conclusions supply the local zero multiplicities and finiteness needed to associate
an effective divisor to a framed plane vortex; no prescribed-divisor existence or flux
identity is asserted here.

Two such sections with the same multiplicity function differ by a nowhere-vanishing `Cᵏ`
factor (`TauCeti.Vortex.exists_contDiff_sectionValue_eq_mul`). Since the exponent of a local
factorization is unique (`TauCeti.eq_of_eventually_sub_pow_mul_eq`), the factor at a zero is the
quotient of the two similarity-principle factors there.

Only the holomorphicity rows are used. The curvature equation is unnecessary, and the
section components need only be real differentiable when the connection is `Cᵏ`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TauCeti.Vortex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The two holomorphicity rows give the scalar Cauchy–Riemann equation for `α = 2(p + i q)`. -/
theorem conjWirtingerDeriv_apply_one_section_eq_mul {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    conjWirtingerDeriv (fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3)) z 1 =
      ((x z 1 : ℂ) - I * x z 0) / 2 * (2 * ((x z 2 : ℂ) + I * x z 3)) := by
  have hP := Complex.ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt
  have hQ := Complex.ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt
  have hA := (hP.fun_add (hQ.const_mul I)).const_mul (2 : ℂ)
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hA
  rw [conjWirtingerDeriv_apply, hA.fderiv]
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  apply Complex.ext <;>
    simp [smul_eq_mul, Complex.ofRealCLM_apply] <;> linarith

section LocalFactor

variable {k : ℕ∞} (hn : 1 ≤ k) (hb₁ : ContDiff ℝ k (fun w ↦ x w 0))
  (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
  (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
  (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)

include hb₁ hb₂ hp hq hhol

private theorem section_scalar_equation :
    ContDiff ℝ k (fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2) ∧
      Differentiable ℝ (fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3)) ∧
      ∀ w, conjWirtingerDeriv (fun y ↦ 2 * ((x y 2 : ℂ) + I * x y 3)) w 1 =
        ((x w 1 : ℂ) - I * x w 0) / 2 * (2 * ((x w 2 : ℂ) + I * x w 3)) := by
  refine ⟨?_, ?_, fun w ↦
    conjWirtingerDeriv_apply_one_section_eq_mul (hp w) (hq w) (hhol w).1 (hhol w).2⟩
  · exact ((Complex.ofRealCLM.contDiff.comp hb₂).sub
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hb₁))).div_const 2
  · fun_prop

include hn

/-- A nontrivial plane vortex section factors locally as a nonnegative integral power
times a factor `Cᵏ` at `z` and nonzero there, including at repeated zeros. -/
theorem exists_contDiffAt_section_eq_pow_mul
    (hne : ∃ w, (x w 2 : ℂ) + I * x w 3 ≠ 0) (z : ℂ) :
    ∃ (n : ℕ) (v : ℂ → ℂ), ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, 2 * ((x w 2 : ℂ) + I * x w 3) = (w - z) ^ n * v w := by
  obtain ⟨ha, hα, heq⟩ := section_scalar_equation hb₁ hb₂ hp hq hhol
  have hneα : ∃ w ∈ (univ : Set ℂ), 2 * ((x w 2 : ℂ) + I * x w 3) ≠ 0 := by
    simpa only [mem_univ, true_and, mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] using hne
  exact exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul hn isOpen_univ
    ha.contDiffOn hα.differentiableOn (fun w _ ↦ heq w) (mem_univ z)
    (not_eventually_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul hn isOpen_univ
      isPreconnected_univ ha.contDiffOn hα.differentiableOn (fun w _ ↦ heq w) hneα (mem_univ z))

/-- A plane vortex section approaching unit modulus has finitely many zeros. -/
theorem finite_setOfPred_section_eq_zero
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    {w | (x w 2 : ℂ) + I * x w 3 = 0}.Finite := by
  let α := fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3)
  obtain ⟨ha, hα, heq⟩ := section_scalar_equation hb₁ hb₂ hp hq hhol
  have htail : ∀ᶠ w in cocompact ℂ, α w ≠ 0 := by
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w hw
    intro hz
    have hr : x w 2 = 0 := by simpa [α] using congrArg Complex.re hz
    have hi : x w 3 = 0 := by simpa [α] using congrArg Complex.im hz
    simp [hr, hi] at hw
  simpa [α] using finite_setOfPred_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul hn ha hα heq htail

end LocalFactor

/-! ### Sections with the same zero multiplicities -/

section Quotient

variable {k : ℕ∞} {y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The section in the form used by `exists_contDiffAt_section_eq_pow_mul`. -/
private theorem sectionValue_eq_two_mul (x : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) :
    sectionValue x w = 2 * ((x w 2 : ℂ) + I * x w 3) := by
  rw [sectionValue_apply, mul_comm I]

/-- A local factorization of a vortex section with a factor only continuous at `z` can be
replaced by one with the same exponent and a `Cᵏ` factor. -/
private theorem exists_contDiffAt_sectionValue_eq_pow_mul (hk : 1 ≤ k)
    (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {z : ℂ} {n : ℕ}
    (hn : ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n * v w) :
    ∃ V : ℂ → ℂ, ContDiffAt ℝ k V z ∧ V z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n * V w := by
  obtain ⟨v, hv, hv₀, hfac⟩ := hn
  -- The factorization makes the section nonzero at points near `z` other than `z`.
  have hne : ∃ w, (x w 2 : ℂ) + I * x w 3 ≠ 0 := by
    obtain ⟨w, ⟨hw, hvw⟩, hwz⟩ :=
      (((hfac.and (hv.eventually_ne hv₀)).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin (s := {z}ᶜ))).exists
    refine ⟨w, fun h0 ↦ mul_ne_zero
      (pow_ne_zero n (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hwz))) hvw ?_⟩
    rw [← hw, sectionValue_eq_two_mul, h0, mul_zero]
  obtain ⟨m, V, hV, hV₀, hfacV⟩ := exists_contDiffAt_section_eq_pow_mul hk hb₁ hb₂ hp hq hhol hne z
  obtain rfl : m = n := eq_of_eventually_sub_pow_mul_eq hV.continuousAt hV₀ hv hv₀ <| by
    filter_upwards [hfac, hfacV] with w hw hwV
    rw [← hwV, ← hw, sectionValue_eq_two_mul]
  exact ⟨V, hV, hV₀, by simpa only [sectionValue_eq_two_mul] using hfacV⟩

/-- **Vortex sections with the same zero multiplicities differ by a nowhere-vanishing `Cᵏ`
factor.** Let `x` and `y` be fields with `Cᵏ` connections (`k ≥ 1`) and differentiable sections
satisfying the holomorphicity rows `∂bar_a α = 0` of the vortex equation. If `n` is a
multiplicity function for both sections, meaning that each of them factors near every `z` as
`(w - z) ^ n z * v w` with `v` continuous and nonzero at `z`, then `α_x = h α_y` for a
nowhere-vanishing `Cᵏ` function `h`. -/
theorem exists_contDiff_sectionValue_eq_mul (hk : 1 ≤ k)
    (hxb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hxb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hxp : Differentiable ℝ (fun w ↦ x w 2)) (hxq : Differentiable ℝ (fun w ↦ x w 3))
    (hxhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hyb₁ : ContDiff ℝ k (fun w ↦ y w 0)) (hyb₂ : ContDiff ℝ k (fun w ↦ y w 1))
    (hyp : Differentiable ℝ (fun w ↦ y w 2)) (hyq : Differentiable ℝ (fun w ↦ y w 3))
    (hyhol : ∀ w, equation y w 1 = 0 ∧ equation y w 2 = 0) {n : ℂ → ℕ}
    (hnx : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w)
    (hny : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue y w = (w - z) ^ n z * v w) :
    ∃ h : ℂ → ℂ, ContDiff ℝ k h ∧ (∀ z, h z ≠ 0) ∧
      ∀ z, sectionValue x z = h z * sectionValue y z := by
  choose V hV hV₀ hfacV using fun z ↦
    exists_contDiffAt_sectionValue_eq_pow_mul hk hxb₁ hxb₂ hxp hxq hxhol (hnx z)
  choose W hW hW₀ hfacW using fun z ↦
    exists_contDiffAt_sectionValue_eq_pow_mul hk hyb₁ hyb₂ hyp hyq hyhol (hny z)
  -- Off the zeros of `α_y` take the quotient of the sections; at a zero `z` take the quotient of
  -- the two factors at `z`.
  let h : ℂ → ℂ := fun w ↦
    if sectionValue y w = 0 then V w w / W w w else sectionValue x w / sectionValue y w
  -- Near each `z`, `h` is the quotient of the two factors at `z`.
  have hloc (z : ℂ) : h =ᶠ[𝓝 z] fun w ↦ V z w / W z w := by
    filter_upwards [hfacV z, hfacW z, (hW z).continuousAt.eventually_ne (hW₀ z)]
      with w hwV hwW hW0
    by_cases hs : sectionValue y w = 0
    · -- The only zero of `α_y` near `z` is `z` itself.
      obtain rfl : w = z := by
        by_contra hwz
        rw [hwW] at hs
        exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hwz)) hW0 hs
      simp only [h, hs, ↓reduceIte]
    · have hpow : (w - z) ^ n z ≠ 0 := fun h0 ↦ hs (by rw [hwW, h0, zero_mul])
      simp only [h, hs, ↓reduceIte]
      rw [hwV, hwW, mul_div_mul_left _ _ hpow]
  have hq (z : ℂ) : ContDiffAt ℝ k (fun w ↦ V z w / W z w) z := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using (hV z).mul ((hW z).inv (hW₀ z))
  refine ⟨h, contDiff_iff_contDiffAt.2 fun z ↦ (hq z).congr_of_eventuallyEq (hloc z),
    fun z ↦ ?_, fun z ↦ ?_⟩
  · rw [(hloc z).self_of_nhds]
    exact div_ne_zero (hV₀ z) (hW₀ z)
  · rw [(hloc z).self_of_nhds, (hfacV z).self_of_nhds, (hfacW z).self_of_nhds]
    rw [div_mul_eq_mul_div, eq_div_iff (hW₀ z)]
    ring

end Quotient

end TauCeti.Vortex
