/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The energy of continuation cylinders

Floer continuation maps, and the cylinders inserted when the end Hamiltonians of a pair of pants
are changed, count solutions `u : ℝ × [0, 1] → V` of the Floer equation

`∂_s u + J_{(s, t)} (∂_t u - X_{H_{(s, t)}}(u)) = 0`

for an `s`-dependent family of Hamiltonians `H_{(s, t)}`, that is, for the perturbation one-form
`K = H_{(s, t)} dt`, with domain-dependent almost complex structures `J_{(s, t)}`. Its curvature
is `R_K = ∂_s H`, so, unlike for a cylindrical perturbation, the energy is no longer the change of
action. This file proves the energy and action bounds of continuation cylinders in a symplectic
vector space for the standard interpolation between two Hamiltonians.

For a map `u` whose loops `t ↦ u(s, t)` are closed, the energy over `[a, b] × [0, 1]` is

`E = A_{H(b, ·)}(u(b, ·)) - A_{H(a, ·)}(u(a, ·)) - ∫∫ (∂_s H)(s, t, u(s, t))`

(`SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral`, in
`TauCeti.Geometry.Symplectic.Floer.Action`), where `A_H` is the Hamiltonian action
`TauCeti.SymplecticForm.hamiltonianAction`. Over the whole cylinder, for a solution with tame `J`
whose loop actions converge at the two ends, the energy is the difference of the limiting actions
minus the integral of `∂_s H` along `u`
(`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral`).

More generally, for the linear homotopy `H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` with a
monotone `C¹` profile `β`, if `H₀ - H₁ ≤ B` along `u`, then the energy over `[a, b] × [0, 1]` is at
most the change of action plus `(β(b) - β(a)) ∫₀¹ B`
(`SymplecticForm.integral_floerEnergyDensity_linearHomotopy_le`), so the action drops by at most
`(β(b) - β(a)) ∫₀¹ B` along a solution with tame `J`
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy`). For a profile with
values in `[0, 1]` and `B ≥ 0` this is at most `∫₀¹ B`, uniformly over stretched profiles
`β(s / λ)`.

The standard interpolation from `H₀` to `H₁` is the *continuation homotopy*
`H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` (`TauCeti.Floer.continuationHomotopy`), with `β` the
smooth transition function from `0` on `s ≤ 0` to `1` on `s ≥ 1`. Its curvature is
`β'(s) (H₁ - H₀)(t)`, so, since `β' ≥ 0` has total integral one, its integrated curvature along
any map is at most `∫₀¹ h` whenever `|H₁ - H₀| ≤ h`, however long the cylinder
(`SymplecticForm.integral_abs_hamiltonianCurvature_continuationHomotopy_le`). If only
`H₀ - H₁ ≤ h`, then the energy is at most the change of action plus `∫₀¹ h`
(`SymplecticForm.integral_floerEnergyDensity_continuationHomotopy_le`). As the energy of a
solution is nonnegative, the action at the end `s → -∞` of a continuation cylinder exceeds the
action at the end `s → ∞` by at most `∫₀¹ h`: if `A_{H₀}(u(s, ·)) → A₁` as `s → -∞` and
`A_{H₁}(u(s, ·)) → A₂` as `s → ∞`, then

`A₁ ≤ A₂ + ∫₀¹ h`

(`SymplecticForm.le_add_integral_of_tendsto_hamiltonianAction_continuationHomotopy`). When
`H₀ - H₁` is bounded above, taking `h(t) = sup_x (H₀ - H₁)(t, x)` gives the action shift
`∫₀¹ sup_x (H₀ - H₁) dt`, the bound by which continuation maps move the action filtration.

These are statements for a symplectic vector space target and maps of the strip whose loops are
closed; manifold targets, capped orbits, and the existence, compactness and counting of
continuation cylinders are not treated here.

## Main definitions

* `TauCeti.Floer.continuationHomotopy H₀ H₁`: the interpolation `H₀ + β(s) (H₁ - H₀)`.

## Main results

* `TauCeti.Floer.fderiv_linearHomotopy_stdComplexLineReal`: the `s`-derivative of the linear
  homotopy with profile `β` is `β'(s) (H₁ - H₀)`.
* `SymplecticForm.integral_floerEnergyDensity_linearHomotopy_le`,
  `SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy`: the energy bound
  and the action shift of a linear homotopy with a monotone profile over a rectangle.
* `TauCeti.Floer.fderiv_continuationHomotopy_stdComplexLineReal`,
  `SymplecticForm.hamiltonianCurvature_continuationHomotopy`: the `s`-derivative and the curvature
  of the continuation homotopy are `β'(s) (H₁ - H₀)`.
* `SymplecticForm.integral_abs_hamiltonianCurvature_continuationHomotopy_le`: its integrated
  curvature is at most `∫₀¹ h` for `|H₁ - H₀| ≤ h`, uniformly in the rectangle.
* `SymplecticForm.integral_floerEnergyDensity_continuationHomotopy_le`,
  `SymplecticForm.lintegral_floerEnergyDensity_continuationHomotopy_le`: the energy is at most the
  change of action plus `∫₀¹ h` for `H₀ - H₁ ≤ h`, over a rectangle and over the whole cylinder.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_continuationHomotopy`,
  `SymplecticForm.le_add_integral_of_tendsto_hamiltonianAction_continuationHomotopy`: the action
  shift of a continuation cylinder, over a rectangle and between the limiting actions.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Function MeasureTheory Set Filter Topology Real

namespace TauCeti

namespace Floer

variable {V : Type*} {H₀ H₁ : ℝ → V → ℝ}

/-- The **continuation homotopy** `H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` from `H₀` to `H₁`,
where `β = Real.smoothTransition` increases from `0` on `s ≤ 0` to `1` on `s ≥ 1`. As the
Hamiltonian of the perturbation `K = H_{(s, t)} dt` of the cylinder, it equals `H₀` for `s ≤ 0`
and `H₁` for `s ≥ 1`. -/
noncomputable def continuationHomotopy (H₀ H₁ : ℝ → V → ℝ) (z : ℝ × ℝ) (x : V) : ℝ :=
  H₀ z.2 x + smoothTransition z.1 * (H₁ z.2 x - H₀ z.2 x)

theorem continuationHomotopy_def (z : ℝ × ℝ) (x : V) :
    continuationHomotopy H₀ H₁ z x = H₀ z.2 x + smoothTransition z.1 * (H₁ z.2 x - H₀ z.2 x) :=
  (rfl)

/-- The continuation homotopy is `H₀` for `s ≤ 0`. -/
@[simp]
theorem continuationHomotopy_of_nonpos {z : ℝ × ℝ} (hz : z.1 ≤ 0) (x : V) :
    continuationHomotopy H₀ H₁ z x = H₀ z.2 x := by
  simp [continuationHomotopy_def, smoothTransition.zero_of_nonpos hz]

/-- The continuation homotopy is `H₁` for `s ≥ 1`. -/
@[simp]
theorem continuationHomotopy_of_one_le {z : ℝ × ℝ} (hz : 1 ≤ z.1) (x : V) :
    continuationHomotopy H₀ H₁ z x = H₁ z.2 x := by
  simp [continuationHomotopy_def, smoothTransition.one_of_one_le hz]

/-- The continuation homotopy of two `Cⁿ` time-dependent Hamiltonians is `Cⁿ`. -/
theorem contDiff_uncurry_continuationHomotopy [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ∞}
    (hH₀ : ContDiff ℝ n (uncurry H₀)) (hH₁ : ContDiff ℝ n (uncurry H₁)) :
    ContDiff ℝ n (uncurry (continuationHomotopy H₀ H₁)) := by
  have hp : ContDiff ℝ n fun p : (ℝ × ℝ) × V ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  exact (hH₀.comp hp).add ((smoothTransition.contDiff.comp (contDiff_fst.comp contDiff_fst)).mul
    ((hH₁.comp hp).sub (hH₀.comp hp)))

/-- The `s`-derivative of the linear homotopy `H₀ + β(s) (H₁ - H₀)` with profile `β`, its
derivative along the direction `1` of the domain, is `β'(s) (H₁ - H₀)(t)`. -/
theorem fderiv_linearHomotopy_stdComplexLineReal {β : ℝ → ℝ} {z : ℝ × ℝ} {x : V}
    (hβ : DifferentiableAt ℝ β z.1) (hH₀ : DifferentiableAt ℝ (fun t ↦ H₀ t x) z.2)
    (hH₁ : DifferentiableAt ℝ (fun t ↦ H₁ t x) z.2) :
    fderiv ℝ (fun w : ℝ × ℝ ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) z stdComplexLineReal =
      deriv β z.1 * (H₁ z.2 x - H₀ z.2 x) := by
  rw [stdComplexLineReal_eq, ← (hasDerivAt_slice_left (s := z.1) (b := z.2)
    (u := fun w : ℝ × ℝ ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x))
    ((hH₀.comp z differentiableAt_snd).add ((hβ.comp z differentiableAt_fst).mul
      ((hH₁.comp z differentiableAt_snd).sub (hH₀.comp z differentiableAt_snd))))).deriv]
  dsimp only
  rw [deriv_const_add, deriv_mul_const hβ]

/-- The `s`-derivative of the continuation homotopy, its derivative along the direction `1` of
the domain, is `β'(s) (H₁ - H₀)(t)`. -/
theorem fderiv_continuationHomotopy_stdComplexLineReal {z : ℝ × ℝ} {x : V}
    (hH₀ : DifferentiableAt ℝ (fun t ↦ H₀ t x) z.2)
    (hH₁ : DifferentiableAt ℝ (fun t ↦ H₁ t x) z.2) :
    fderiv ℝ (fun w ↦ continuationHomotopy H₀ H₁ w x) z stdComplexLineReal =
      deriv smoothTransition z.1 * (H₁ z.2 x - H₀ z.2 x) :=
  fderiv_linearHomotopy_stdComplexLineReal
    ((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero z.1) hH₀ hH₁

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H₀ H₁ : ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)} {a b : ℝ}

section ContinuationHomotopy

/-- **The curvature of the continuation homotopy.** The perturbation `K = H_{(s, t)} dt` of the
continuation homotopy `H = H₀ + β(s) (H₁ - H₀)` has curvature `β'(s) (H₁ - H₀)(t)`. -/
theorem hamiltonianCurvature_continuationHomotopy (ω : SymplecticForm V) {z : ℝ × ℝ} {x : V}
    (hH₀ : DifferentiableAt ℝ (fun t ↦ H₀ t x) z.2)
    (hH₁ : DifferentiableAt ℝ (fun t ↦ H₁ t x) z.2) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) z x =
      deriv smoothTransition z.1 * (H₁ z.2 x - H₀ z.2 x) := by
  rw [hamiltonianCurvature_zero_left, fderiv_continuationHomotopy_stdComplexLineReal hH₀ hH₁]

/-- **Uniform curvature bound for the continuation homotopy.** Let `h` bound `|H₁ - H₀|` on
`[c, d]`, uniformly on the target. Over any rectangle `[a, b] × [c, d]`, the integrated curvature of
the continuation homotopy along any map `u` is at most `∫_c^d h`, independently of `a` and `b`. -/
theorem integral_abs_hamiltonianCurvature_continuationHomotopy_le (ω : SymplecticForm V)
    {c d : ℝ} (hH₀ : ∀ t ∈ Icc c d, ∀ x, DifferentiableAt ℝ (fun t ↦ H₀ t x) t)
    (hH₁ : ∀ t ∈ Icc c d, ∀ x, DifferentiableAt ℝ (fun t ↦ H₁ t x) t) (u : ℝ × ℝ → V)
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc c d, ∀ x, |H₁ t x - H₀ t x| ≤ h t)
    (hhi : IntegrableOn h (Icc c d)) :
    ∫ z in Icc a b ×ˢ Icc c d,
        |ω.hamiltonianCurvature (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) z (u z)| ≤
      ∫ t in Icc c d, h t := by
  set f : ℝ × ℝ → ℝ := fun z ↦
    |ω.hamiltonianCurvature (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) z (u z)|
  have hβ'0 (s : ℝ) : 0 ≤ deriv smoothTransition s := smoothTransition.monotone.deriv_nonneg
  have hh0 : 0 ≤ ∫ t in Icc c d, h t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ (abs_nonneg _).trans (hh t ht 0)
  by_cases hfi : IntegrableOn f (Icc a b ×ˢ Icc c d)
  swap
  · rw [integral_undef hfi]
    exact hh0
  -- The pointwise bound `|R_K(z, u z)| ≤ β'(s) h(t)`.
  have hfg (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc c d) :
      f z ≤ deriv smoothTransition z.1 * h z.2 := by
    simp only [f, ω.hamiltonianCurvature_continuationHomotopy (hH₀ z.2 hz.2 _) (hH₁ z.2 hz.2 _),
      abs_mul, abs_of_nonneg (hβ'0 z.1)]
    exact mul_le_mul_of_nonneg_left (hh z.2 hz.2 (u z)) (hβ'0 z.1)
  -- The bound integrates to `(∫ β') (∫ h) ≤ ∫ h` over the rectangle.
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℝ
  have hgi : IntegrableOn (fun z : ℝ × ℝ ↦ deriv smoothTransition z.1 * h z.2)
      (Icc a b ×ˢ Icc c d) := by
    rw [IntegrableOn, hvol, ← Measure.prod_restrict]
    exact (smoothTransition.integrable_deriv.integrableOn (s := Icc a b)).mul_prod hhi
  calc ∫ z in Icc a b ×ˢ Icc c d, f z
      ≤ ∫ z in Icc a b ×ˢ Icc c d, deriv smoothTransition z.1 * h z.2 :=
        setIntegral_mono_on hfi hgi (measurableSet_Icc.prod measurableSet_Icc) hfg
    _ = (∫ s in Icc a b, deriv smoothTransition s) * ∫ t in Icc c d, h t := by
        rw [hvol]
        exact setIntegral_prod_mul _ h _ _
    _ ≤ 1 * ∫ t in Icc c d, h t :=
        mul_le_mul_of_nonneg_right (smoothTransition.setIntegral_deriv_le_one _) hh0
    _ = ∫ t in Icc c d, h t := one_mul _

/-- **The energy bound of a linear homotopy over a rectangle.** Let `H₀` and `H₁` be `C¹`
time-dependent Hamiltonians, let `β` be a monotone `C¹` profile, and let `u` be `C²` on an open
neighbourhood `U` of `[a, b] × [0, 1]`, with `u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. If
`H₀ - H₁ ≤ B` along `u` for a function `B` integrable on `[0, 1]`, then for the linear homotopy
`H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` the Floer energy of `u` over the rectangle is at most
`A_{H(b, ·)}(u(b, ·)) - A_{H(a, ·)}(u(a, ·)) + (β(b) - β(a)) ∫₀¹ B`. -/
theorem integral_floerEnergyDensity_linearHomotopy_le (ω : SymplecticForm V)
    (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁)) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) (hβm : Monotone β) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    {B : ℝ → ℝ} (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w x ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) u z ≤
      ω.hamiltonianAction (fun t x ↦ H₀ t x + β b * (H₁ t x - H₀ t x)) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (fun t x ↦ H₀ t x + β a * (H₁ t x - H₀ t x)) (fun t ↦ u (a, t)) +
        (β b - β a) * ∫ t in Icc 0 1, B t := by
  have hH : ContDiff ℝ 1 (uncurry fun (w : ℝ × ℝ) x ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) :=
    (contDiff_uncurry_cylindrical hH₀).add ((hβ.comp (contDiff_fst.comp contDiff_fst)).mul
      ((contDiff_uncurry_cylindrical hH₁).sub (contDiff_uncurry_cylindrical hH₀)))
  rw [ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral hH hU hu hab hRU hper]
  -- It remains to bound `-∫ ∂_s H(u) = ∫ β'(s) (H₀ - H₁)(t, u)` by `(∫ β') (∫ B)`.
  have hβ' : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  have hd {G : ℝ → V → ℝ} (hG : ContDiff ℝ 1 (uncurry G)) (t : ℝ) (x : V) :
      DifferentiableAt ℝ (fun t ↦ G t x) t :=
    (hG.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero t
  have hcurv (z : ℝ × ℝ) : fderiv ℝ (fun w : ℝ × ℝ ↦
      H₀ w.2 (u z) + β w.1 * (H₁ w.2 (u z) - H₀ w.2 (u z))) z stdComplexLineReal =
      deriv β z.1 * (H₁ z.2 (u z) - H₀ z.2 (u z)) :=
    fderiv_linearHomotopy_stdComplexLineReal (hβ.differentiable one_ne_zero z.1) (hd hH₀ _ _)
      (hd hH₁ _ _)
  simp only [hcurv]
  have hR : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hfi : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * (H₁ z.2 (u z) - H₀ z.2 (u z)))
      (Icc a b ×ˢ Icc 0 1) := by
    have hp : ContinuousOn (fun z : ℝ × ℝ ↦ (z.2, u z)) U :=
      continuous_snd.continuousOn.prodMk hu.continuousOn
    exact (((hβ'.comp continuous_fst).continuousOn.mul
      ((hH₁.continuous.comp_continuousOn hp).sub (hH₀.continuous.comp_continuousOn hp))).mono
        hRU).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℝ
  have hgi : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * B z.2) (Icc a b ×ˢ Icc 0 1) := by
    rw [IntegrableOn, hvol, ← Measure.prod_restrict]
    exact hβ'.continuousOn.integrableOn_Icc.mul_prod hB
  have hle : ∫ z in Icc a b ×ˢ Icc 0 1, -(deriv β z.1 * B z.2) ≤
      ∫ z in Icc a b ×ˢ Icc 0 1, deriv β z.1 * (H₁ z.2 (u z) - H₀ z.2 (u z)) :=
    setIntegral_mono_on hgi.neg hfi hR fun z hz ↦ by
      have := mul_le_mul_of_nonneg_left (hHB z hz) (hβm.deriv_nonneg (x := z.1))
      linarith
  have hftc : ∫ s in Icc a b, deriv β s = β b - β a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hβ.differentiable one_ne_zero x)
        (hβ'.intervalIntegrable _ _)]
  rw [integral_neg, hvol, setIntegral_prod_mul (deriv β) B, ← hvol, hftc] at hle
  linarith

/-- **The action shift of a linear homotopy over a rectangle.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_linearHomotopy_le`, if `u` solves the Floer
equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` for the linear homotopy on the rectangle, with
almost complex structures `J_z` tamed by `ω`, then the action of the loop at `s = a` for
`H(a, ·)` is at most the action of the loop at `s = b` for `H(b, ·)` plus `(β(b) - β(a)) ∫₀¹ B`.
When `β` takes values in `[0, 1]` and `B ≥ 0`, the error term is at most `∫₀¹ B`, whatever the
profile `β`; in particular it does not depend on how far the homotopy is stretched. -/
theorem hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁)) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) (hβm : Monotone β) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag -
        ω.hamiltonianVectorField (fun x ↦ H₀ z.2 x + β z.1 * (H₁ z.2 x - H₀ z.2 x)) (u z)) = 0)
    {B : ℝ → ℝ} (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    ω.hamiltonianAction (fun t x ↦ H₀ t x + β a * (H₁ t x - H₀ t x)) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (fun t x ↦ H₀ t x + β b * (H₁ t x - H₀ t x)) (fun t ↦ u (b, t)) +
        (β b - β a) * ∫ t in Icc 0 1, B t := by
  have h := ω.integral_floerEnergyDensity_linearHomotopy_le hH₀ hH₁ hβ hβm hU hu hab hRU hper hB
    hHB
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_zero_left_nonneg
      (Kt := fun w x ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) (hJ z hz) (hfloer z hz)
  linarith

/-- **The energy bound of a continuation cylinder over a rectangle.** Let `H₀` and `H₁` be `C¹`
time-dependent Hamiltonians with `H₀ - H₁ ≤ h` on `[0, 1]`, uniformly on the target, and let `u` be
`C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with `a ≤ 0`, `1 ≤ b` and
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. For the continuation homotopy, the Floer energy of `u` over
the rectangle is at most `A_{H₁}(u(b, ·)) - A_{H₀}(u(a, ·)) + ∫₀¹ h`. -/
theorem integral_floerEnergyDensity_continuationHomotopy_le (ω : SymplecticForm V)
    (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (ha : a ≤ 0) (hb : 1 ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) {h : ℝ → ℝ}
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t) (hhi : IntegrableOn h (Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) u z ≤
      ω.hamiltonianAction H₁ (fun t ↦ u (b, t)) - ω.hamiltonianAction H₀ (fun t ↦ u (a, t)) +
        ∫ t in Icc 0 1, h t := by
  have h := ω.integral_floerEnergyDensity_linearHomotopy_le hH₀ hH₁
    (smoothTransition.contDiff (n := 1)) smoothTransition.monotone hU hu
    (ha.trans (zero_le_one.trans hb)) hRU hper hhi fun z hz ↦ hh z.2 hz.2 (u z)
  -- At the two ends the homotopy is `H₀` and `H₁`.
  rw [smoothTransition.zero_of_nonpos ha, smoothTransition.one_of_one_le hb] at h
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel, sub_zero] at h
  exact h

/-- **The action shift of a continuation cylinder over a rectangle.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_continuationHomotopy_le`, if `u` solves the
Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` for the continuation homotopy on the
rectangle, with almost complex structures `J_z` tamed by `ω`, then
`A_{H₀}(u(a, ·)) ≤ A_{H₁}(u(b, ·)) + ∫₀¹ h`. -/
theorem hamiltonianAction_le_hamiltonianAction_add_of_continuationHomotopy
    (ω : SymplecticForm V) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z)) (hH₀ : ContDiff ℝ 1 (uncurry H₀))
    (hH₁ : ContDiff ℝ 1 (uncurry H₁)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (ha : a ≤ 0)
    (hb : 1 ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0)
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t)
    (hhi : IntegrableOn h (Icc 0 1)) :
    ω.hamiltonianAction H₀ (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction H₁ (fun t ↦ u (b, t)) + ∫ t in Icc 0 1, h t := by
  have h := ω.integral_floerEnergyDensity_continuationHomotopy_le hH₀ hH₁ hU hu ha hb hRU hper hh
    hhi
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_zero_left_nonneg (hJ z hz) (hfloer z hz)
  linarith

/-- **The energy bound of a continuation cylinder.** Let `H₀` and `H₁` be `C¹` time-dependent
Hamiltonians with `H₀ - H₁ ≤ h` on `[0, 1]`, uniformly on the target, and let `u` be `C²` on an
open neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)` for all `s`, solving the Floer
equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` there for the continuation homotopy, with almost
complex structures `J_z` tamed by `ω`. If `A_{H₀}(u(s, ·))` tends to `A₁` as `s → -∞` and
`A_{H₁}(u(s, ·))` tends to `A₂` as `s → ∞`, then the energy of `u` is at most
`A₂ - A₁ + ∫₀¹ h`. -/
theorem lintegral_floerEnergyDensity_continuationHomotopy_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0)
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t)
    (hhi : IntegrableOn h (Icc 0 1)) {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction H₀ (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction H₁ (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) u z) ≤
      ENNReal.ofReal (A₂ - A₁ + ∫ t in Icc 0 1, h t) := by
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hcont := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0)
    (Kt := continuationHomotopy H₀ H₁) hU (hu.of_le one_le_two) contDiffOn_const
    (contDiff_uncurry_continuationHomotopy hH₀ hH₁).contDiffOn
  -- On each rectangle `[-n, n] × [0, 1]` with `n ≥ 1`, the energy obeys the bound.
  have hE : ∀ᶠ n : ℕ in atTop, ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) u z) ≤
      ENNReal.ofReal (ω.hamiltonianAction H₁ (fun t ↦ u (n, t)) -
        ω.hamiltonianAction H₀ (fun t ↦ u (-n, t)) + ∫ t in Icc 0 1, h t) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal
        ((hcont.mono ((hRsub n).trans hRU)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))
        (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
          fun z hz ↦ ω.floerEnergyDensity_zero_left_nonneg (hJ z (hRsub n hz))
            (hfloer z (hRsub n hz)))]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact ENNReal.ofReal_le_ofReal (ω.integral_floerEnergyDensity_continuationHomotopy_le hH₀ hH₁
      hU hu (neg_nonpos.2 (zero_le_one.trans hn')) hn' ((hRsub n).trans hRU) (fun s _ ↦ hper s)
      hh hhi)
  refine le_of_tendsto_of_tendsto (tendsto_setLIntegral_Icc_neg_prod volume (Icc (0 : ℝ) 1) _) ?_ hE
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (((htop.comp tendsto_natCast_atTop_atTop).sub
      (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))).add_const _)

/-- **The action shift of a continuation cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_continuationHomotopy_le`, the limiting actions
satisfy `A₁ ≤ A₂ + ∫₀¹ h`: along a continuation cylinder from `H₀` at `s → -∞` to `H₁` at
`s → ∞`, the action at the end `s → -∞` exceeds the action at the end `s → ∞` by at most
`∫₀¹ h`. -/
theorem le_add_integral_of_tendsto_hamiltonianAction_continuationHomotopy (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0)
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t)
    (hhi : IntegrableOn h (Icc 0 1)) {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction H₀ (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction H₁ (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    A₁ ≤ A₂ + ∫ t in Icc 0 1, h t := by
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  refine le_of_tendsto_of_tendsto
    (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
    ((htop.comp tendsto_natCast_atTop_atTop).add_const _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ω.hamiltonianAction_le_hamiltonianAction_add_of_continuationHomotopy
    (fun z hz ↦ hJ z (hRsub n hz)) hH₀ hH₁ hU hu (neg_nonpos.2 (zero_le_one.trans hn')) hn'
    ((hRsub n).trans hRU) (fun s _ ↦ hper s) (fun z hz ↦ hfloer z (hRsub n hz)) hh hhi

end ContinuationHomotopy

end SymplecticForm

end TauCeti
