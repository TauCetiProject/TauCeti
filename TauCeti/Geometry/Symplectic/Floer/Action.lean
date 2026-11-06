/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.Basic
public import TauCeti.Geometry.Symplectic.Floer.Energy
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# The Hamiltonian action and the energy of cylindrical Floer solutions

Let `(V, ω)` be a symplectic vector space and `H : ℝ → V → ℝ` a time-dependent Hamiltonian. For
a loop `x : [0, 1] → V` with `x 1 = x 0`, the symplectic area of the loop is
`a(x) = ½ ∫₀¹ ω(x(t), x'(t)) dt` (`TauCeti.SymplecticForm.loopArea`, in
`TauCeti.Geometry.Symplectic.Area.Basic`). It is the symplectic area
`∫ D^* ω` of the cone `D(r, t) = r x(t)` bounding the loop
(`SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`). The Hamiltonian action of the
loop capped by this disc is

`A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt`

(`TauCeti.SymplecticForm.hamiltonianAction`), the convention `A_H(x, D) = ∫ D^* ω + ∫ H dt` of
capped Floer theory with positive ends as inputs.

On a region of the domain where the Hamiltonian perturbation is cylindrical, `K = H_t dt`, such as
a strip-like end or a neck of a punctured Floer domain, the curvature of `K` vanishes and the
boundary terms of the Floer energy identity combine into actions. For a map `u` on
`[a, b] × [0, 1]` whose bottom and top sides agree, so that each `t ↦ u(s, t)` is a loop:

* the symplectic area of `u` is `a(u(b, ·)) - a(u(a, ·))`
  (`SymplecticForm.integral_symplecticForm_fderiv_eq_loopArea_sub`), by Green's formula for the
  primitive `λₓ(v) = ½ ω(x, v)` (`SymplecticForm.integral_fderiv_apply_prod_Icc`);
* the Floer energy of `u` is `A_H(u(b, ·)) - A_H(u(a, ·))`
  (`SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`), by the energy identity
  `TauCeti.SymplecticForm.integral_floerEnergyDensity`.

For a solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with `J` tamed by `ω`,
the energy density is nonnegative, so the action increases along the cylinder
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction`), and the energy of a Floer solution on
the whole cylinder `ℝ × [0, 1]` is the difference of the limiting actions at its two ends
(`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`), by exhausting the
cylinder with rectangles (`TauCeti.tendsto_setLIntegral_Icc_neg_prod`). These are the
end and neck terms of the energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants.

For an `s`-dependent family of Hamiltonians `H_{(s, t)}`, the perturbation `K = H_{(s, t)} dt` of a
continuation cylinder has curvature `∂_s H`, and the energy of `u` over `[a, b] × [0, 1]` is

`E = A_{H(b, ·)}(u(b, ·)) - A_{H(a, ·)}(u(a, ·)) - ∫∫ (∂_s H)(s, t, u(s, t))`

(`SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral`). Over the
whole cylinder, for a solution with tame `J` whose loop actions converge at the two ends, the
energy is the difference of the limiting actions minus the integral of `∂_s H` along `u`
(`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral`).
The cylindrical statements above are the special case of an `s`-independent family.

For a solution with tame `J`, the action therefore drops by at most the integral of `∂_s H` along
`u` (`SymplecticForm.hamiltonianAction_le_hamiltonianAction_sub_integral`), and it does not drop
for a monotone homotopy (`SymplecticForm.hamiltonianAction_le_hamiltonianAction_of_monotone`). For
the linear homotopy `H_{(s, t)} = H⁰_t + β(s) (H¹_t - H⁰_t)` with monotone `C¹` profile `β`, it
drops by at most `(β(b) - β(a)) ∫₀¹ B` whenever `H⁰_t - H¹_t ≤ B(t)` along `u`
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy`). This is at most
`∫₀¹ B` for every profile with values in `[0, 1]`, so it is uniform over stretched homotopies
`β(s / λ)`.

## Main definitions

* `TauCeti.SymplecticForm.hamiltonianAction`: the Hamiltonian action of a loop.

## Main results

* `SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`: the energy of a map over
  `[a, b] × [0, 1]` for a cylindrical perturbation is the change of action.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction`: the action increases along Floer
  solutions.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`: the energy of a
  Floer solution on the whole cylinder is the difference of its limiting actions.
* `SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral`: the energy
  identity of a continuation cylinder over a rectangle.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction_sub_integral`: the action estimate along
  a continuation cylinder over a rectangle.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction_of_monotone` and
  `SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy`: the action along
  continuation cylinders of monotone and of linear homotopies.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral`: the
  energy identity of a continuation cylinder over the whole cylinder.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1 and the
  chapter on Floer homology, on the action functional and the energy identity.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 1 and 3.
-/

public section

open Function MeasureTheory Set Filter Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Action

/-- The Hamiltonian action `A_H(x) = ½ ∫₀¹ ω(x, x') dt + ∫₀¹ H(t, x(t)) dt` of a loop `x`, for a
time-dependent Hamiltonian `H`. It is the action `∫ D^* ω + ∫ H dt` of the loop capped by the
cone `D(r, t) = r x(t)`, with the sign convention in which the action increases along Floer
solutions, so that positive ends are inputs. -/
noncomputable def hamiltonianAction (ω : SymplecticForm V) (H : ℝ → V → ℝ) (x : ℝ → V) : ℝ :=
  ω.loopArea x + ∫ t in (0 : ℝ)..1, H t (x t)

theorem hamiltonianAction_def (ω : SymplecticForm V) (H : ℝ → V → ℝ) (x : ℝ → V) :
    ω.hamiltonianAction H x = ω.loopArea x + ∫ t in (0 : ℝ)..1, H t (x t) :=
  (rfl)

/-- The action of a constant loop is the time average of the Hamiltonian at that point. -/
@[simp]
theorem hamiltonianAction_const (ω : SymplecticForm V) (H : ℝ → V → ℝ) (v : V) :
    ω.hamiltonianAction H (fun _ ↦ v) = ∫ t in (0 : ℝ)..1, H t v := by
  simp [hamiltonianAction_def]

end Action

section Homotopy

variable [FiniteDimensional ℝ V] {H : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)}
  {a b : ℝ}

/-- **The energy identity of a continuation cylinder.** Let `H_{(s, t)}` be a `C¹` family of
Hamiltonians and let `u` be `C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. For the perturbation `K = H_{(s, t)} dt`, the Floer energy of
`u` over the rectangle is the action of the loop at `s = b` for `H(b, ·)`, minus the action of the
loop at `s = a` for `H(a, ·)`, minus the integral of `∂_s H` along `u`. -/
theorem integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral (ω : SymplecticForm V)
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) H u z =
      ω.hamiltonianAction (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have h := ω.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := H) hU
    (hu.of_le one_le_two) contDiffOn_const hH.contDiffOn (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩)
    (hR ▸ hRU)
  simp only [hamiltonianCurvature_zero_left, intervalIntegral.integral_zero, ← hR] at h
  rw [h, ω.integral_symplecticForm_fderiv_eq_loopArea_sub hab
      (fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hRU hz))) hper,
    hamiltonianAction_def, hamiltonianAction_def]
  ring

/-- **The action estimate along a continuation cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral`, if `u`
solves the Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` on the rectangle for almost
complex structures `J_z` tamed by `ω`, then the action of the loop at `s = a` is at most the
action of the loop at `s = b` minus the integral of `∂_s H` along `u`. -/
theorem hamiltonianAction_le_hamiltonianAction_sub_integral (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z) (u z)) = 0) :
    ω.hamiltonianAction (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal := by
  have h := ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral hH hU hu hab hRU
    hper
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_zero_left_nonneg (hJ z hz) (hfloer z hz)
  linarith

/-- **The action increases along continuation cylinders of monotone homotopies.** Under the
hypotheses of `TauCeti.SymplecticForm.hamiltonianAction_le_hamiltonianAction_sub_integral`, if
every `s ↦ H_{(s, t)}(x)` is monotone, then the action of the loop at `s = a` for `H(a, ·)` is at
most that of the loop at `s = b` for `H(b, ·)`. -/
theorem hamiltonianAction_le_hamiltonianAction_of_monotone (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    (hH : ContDiff ℝ 1 (uncurry H)) (hmono : ∀ t x, Monotone fun s ↦ H (s, t) x) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z) (u z)) = 0) :
    ω.hamiltonianAction (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) := by
  have h := ω.hamiltonianAction_le_hamiltonianAction_sub_integral hJ hH hU hu hab hRU hper hfloer
  -- `∂_s H` is the derivative of the monotone functions `s ↦ H_{(s, t)}(x)`.
  have hderiv (z : ℝ × ℝ) (x : V) :
      fderiv ℝ (fun w ↦ H w x) z stdComplexLineReal = deriv (fun s ↦ H (s, z.2) x) z.1 :=
    (ω.hamiltonianCurvature_zero_left H z x).symm.trans <| ω.hamiltonianCurvature_homotopy <|
      (hH.differentiable one_ne_zero (z, x)).comp (f := fun w : ℝ × ℝ ↦ (w, x)) z
        (differentiableAt_id.prodMk (differentiableAt_const _))
  have hnonneg : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ by
      rw [hderiv]
      exact (hmono z.2 (u z)).deriv_nonneg
  linarith

/-- **The action estimate for a linear homotopy.** Let `H⁰` and `H¹` be `C¹` time-dependent
Hamiltonians, let `β` be a monotone `C¹` function, and let `H_{(s, t)} = H⁰_t + β(s) (H¹_t - H⁰_t)`.
Under the hypotheses of
`TauCeti.SymplecticForm.hamiltonianAction_le_hamiltonianAction_sub_integral`, if
`H⁰_t - H¹_t ≤ B(t)` along `u` for a function `B` integrable on `[0, 1]`, then the action of the
loop at `s = a` for `H(a, ·)` is at most the action of the loop at `s = b` for `H(b, ·)` plus
`(β(b) - β(a)) ∫₀¹ B`. When `β` takes values in `[0, 1]` and `B ≥ 0`, the error term is at most
`∫₀¹ B`, whatever the profile `β`; in particular it does not depend on how far the homotopy is
stretched. -/
theorem hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    {H₀ H₁ : ℝ → V → ℝ} (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β) (hβm : Monotone β) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag -
        ω.hamiltonianVectorField (fun x ↦ H₀ z.2 x + β z.1 * (H₁ z.2 x - H₀ z.2 x)) (u z)) = 0)
    {B : ℝ → ℝ} (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    ω.hamiltonianAction (fun t x ↦ H₀ t x + β a * (H₁ t x - H₀ t x)) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (fun t x ↦ H₀ t x + β b * (H₁ t x - H₀ t x)) (fun t ↦ u (b, t)) +
        (β b - β a) * ∫ t in (0 : ℝ)..1, B t := by
  have hR : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hH : ContDiff ℝ 1 (uncurry fun (w : ℝ × ℝ) x ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) :=
    (contDiff_uncurry_cylindrical hH₀).add ((hβ.comp (contDiff_fst.comp contDiff_fst)).mul
      ((contDiff_uncurry_cylindrical hH₁).sub (contDiff_uncurry_cylindrical hH₀)))
  have hβ' : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  -- `∂_s H = β'(s) (H¹_t - H⁰_t)`, so `-∂_s H ≤ β'(s) B(t)` along `u`.
  have hderiv (z : ℝ × ℝ) (x : V) :
      fderiv ℝ (fun w : ℝ × ℝ ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) z stdComplexLineReal =
        deriv β z.1 * (H₁ z.2 x - H₀ z.2 x) := by
    rw [← ω.hamiltonianCurvature_zero_left (fun w x ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)),
      ω.hamiltonianCurvature_homotopy ((hH.differentiable one_ne_zero (z, x)).comp
        (f := fun w : ℝ × ℝ ↦ (w, x)) z (differentiableAt_id.prodMk (differentiableAt_const _)))]
    dsimp only
    rw [deriv_const_add, deriv_mul_const (hβ.differentiable one_ne_zero z.1)]
  have h := ω.hamiltonianAction_le_hamiltonianAction_sub_integral hJ hH hU hu hab hRU hper hfloer
  simp only [hderiv] at h
  have hcurv : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * (H₁ z.2 (u z) - H₀ z.2 (u z)))
      (Icc a b ×ˢ Icc 0 1) := by
    have hp : ContinuousOn (fun z : ℝ × ℝ ↦ (z.2, u z)) U :=
      continuous_snd.continuousOn.prodMk hu.continuousOn
    exact (((hβ'.comp continuous_fst).continuousOn.mul
      ((hH₁.continuous.comp_continuousOn hp).sub (hH₀.continuous.comp_continuousOn hp))).mono
        hRU).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hg : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * B z.2) (Icc a b ×ˢ Icc 0 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Integrable.mul_prod hβ'.continuousOn.integrableOn_Icc hB
  have hle := setIntegral_mono_on hcurv.neg hg hR fun z hz ↦ by
    rw [Pi.neg_apply, ← mul_neg, neg_sub]
    exact mul_le_mul_of_nonneg_left (hHB z hz) hβm.deriv_nonneg
  have hint : ∫ z in Icc a b ×ˢ Icc 0 1, deriv β z.1 * B z.2 =
      (β b - β a) * ∫ t in (0 : ℝ)..1, B t := by
    rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_Icc_eq_integral_Ioc,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hβ.differentiable one_ne_zero x)
        (hβ'.intervalIntegrable _ _)]
  simp only [Pi.neg_apply, integral_neg] at hle
  linarith

/-- **The energy of a continuation cylinder.** Let `H_{(s, t)}` be a `C¹` family of Hamiltonians
and let `u` be `C²` on an open neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)` for all
`s`, solving the Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` there for almost complex
structures `J_z` tamed by `ω`. Suppose that `∂_s H` is integrable along `u` and that the actions
`A_{H(s, ·)}(u(s, ·))` tend to `A₁` as `s → -∞` and to `A₂` as `s → ∞`. Then the energy of `u` is
`A₂ - A₁` minus the integral of `∂_s H` along `u`. -/
theorem lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral
    (ω : SymplecticForm V) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z)) (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z) (u z)) = 0)
    (hint : IntegrableOn (fun z ↦ fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal)
      ((univ : Set ℝ) ×ˢ Icc 0 1))
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction (fun t ↦ H (s, t)) (fun t ↦ u (s, t))) atBot
      (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction (fun t ↦ H (s, t)) (fun t ↦ u (s, t))) atTop
      (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) H u z) =
      ENNReal.ofReal (A₂ - A₁ -
        ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal) := by
  set f : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal
  set A : ℝ → ℝ := fun s ↦ ω.hamiltonianAction (fun t ↦ H (s, t)) (fun t ↦ u (s, t))
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hcont := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := H) hU
    (hu.of_le one_le_two) contDiffOn_const hH.contDiffOn
  -- On each rectangle `[-n, n] × [0, 1]` the energy identity holds, with nonnegative density.
  have hE (n : ℕ) : ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) H u z) =
      ENNReal.ofReal (A n - A (-n) - ∫ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1, f z) := by
    rw [← ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral hH hU hu
        (neg_le_self n.cast_nonneg) ((hRsub n).trans hRU) fun s _ ↦ hper s,
      ofReal_integral_eq_lintegral_ofReal
        ((hcont.mono ((hRsub n).trans hRU)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))
        (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
          fun z hz ↦ ω.floerEnergyDensity_zero_left_nonneg (hJ z (hRsub n hz))
            (hfloer z (hRsub n hz)))]
  -- The integrals of `∂_s H` along `u` over the rectangles converge to the one over the strip.
  have hf : Tendsto (fun n : ℕ ↦ ∫ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1, f z) atTop
      (𝓝 (∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, f z)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume) (f := f)
      (fun _ ↦ measurableSet_Icc.prod measurableSet_Icc) (monotone_Icc_neg_prod (Icc 0 1))
      (by rwa [iUnion_Icc_neg_prod])
    rwa [iUnion_Icc_neg_prod] at h
  refine tendsto_nhds_unique (tendsto_setLIntegral_Icc_neg_prod volume (Icc (0 : ℝ) 1) _) ?_
  simp only [hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (((htop.comp tendsto_natCast_atTop_atTop).sub
      (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))).sub hf)

end Homotopy

section Energy

variable [FiniteDimensional ℝ V] {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)} {a b : ℝ}

/-- **The energy identity for a cylindrical perturbation.** Let `H` be a `C¹` time-dependent
Hamiltonian and let `u` be `C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. For the cylindrical perturbation `K = H_t dt`, the Floer
energy of `u` over the rectangle is the action of the loop at `s = b` minus the action of the loop
at `s = a`. -/
theorem integral_floerEnergyDensity_eq_hamiltonianAction_sub (ω : SymplecticForm V)
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.hamiltonianAction H (fun t ↦ u (b, t)) - ω.hamiltonianAction H (fun t ↦ u (a, t)) := by
  -- A cylindrical family does not depend on `s`.
  have h0 (z : ℝ × ℝ) (x : V) : fderiv ℝ (fun w : ℝ × ℝ ↦ H w.2 x) z stdComplexLineReal = 0 :=
    (ω.hamiltonianCurvature_zero_left _ z x).symm.trans (ω.hamiltonianCurvature_cylindrical H z x)
  simpa [h0] using ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral
    (H := fun w ↦ H w.2) (contDiff_uncurry_cylindrical hH) hU hu hab hRU hper

/-- The Floer energy density of a solution of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt` is
nonnegative when `J` is tamed by `ω`. -/
theorem floerEnergyDensity_cylindrical_nonneg (ω : SymplecticForm V) {J : AlmostComplexStructure V}
    (hJ : ω.Tames J) {z : ℝ × ℝ}
    (hfloer : fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z :=
  ω.floerEnergyDensity_zero_left_nonneg hJ hfloer

/-- **The action increases along Floer solutions.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`, if `u` solves the
Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the rectangle for an almost complex
structure `J` tamed by `ω`, then the action of the loop at `s = a` is at most that of the loop at
`s = b`. -/
theorem hamiltonianAction_le_hamiltonianAction (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J) (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ω.hamiltonianAction H (fun t ↦ u (a, t)) ≤ ω.hamiltonianAction H (fun t ↦ u (b, t)) :=
  ω.hamiltonianAction_le_hamiltonianAction_of_monotone (H := fun w ↦ H w.2) (J := fun _ ↦ J)
    (fun _ _ ↦ hJ) (contDiff_uncurry_cylindrical hH) (fun _ _ _ _ _ ↦ le_rfl) hU hu hab hRU
    hper hfloer

/-- **The energy of a Floer cylinder.** Let `H` be a `C¹` time-dependent Hamiltonian and let `u`
be `C²` on an open neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)` for all `s`,
solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` there for an almost complex
structure `J` tamed by `ω`. If the actions of the loops `t ↦ u(s, t)` tend to `A₁` as `s → -∞`
and to `A₂` as `s → ∞`, then the energy of `u` is `A₂ - A₁`. -/
theorem lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J) (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (A₂ - A₁) := by
  have h0 (z : ℝ × ℝ) (x : V) : fderiv ℝ (fun w : ℝ × ℝ ↦ H w.2 x) z stdComplexLineReal = 0 :=
    (ω.hamiltonianCurvature_zero_left _ z x).symm.trans (ω.hamiltonianCurvature_cylindrical H z x)
  simpa [h0] using ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral
    (H := fun w ↦ H w.2) (J := fun _ ↦ J) (fun _ _ ↦ hJ) (contDiff_uncurry_cylindrical hH) hU hu
    hRU hper hfloer (by simp [h0]) hbot htop

end Energy

end TauCeti.SymplecticForm
