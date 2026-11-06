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
# The Hamiltonian action and the energy of Floer and continuation cylinders

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

Continuation maps between Floer complexes count solutions of the Floer equation
`∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` for the perturbation `K = H_s(t) dt` of a homotopy `H_s`
of Hamiltonians, and on a region of a punctured Floer domain where `K = H_t dt` is cylindrical,
such as a strip-like end or a neck, `H_s = H` does not depend on `s`. The curvature of
`K = H_s(t) dt` is `∂_s H_s(t)` (`SymplecticForm.hamiltonianCurvature_homotopy`), and the
boundary terms of the Floer energy identity combine into actions. For a map `u` on
`[a, b] × [0, 1]` whose bottom and top sides agree, so that each `t ↦ u(s, t)` is a loop:

* the symplectic area of `u` is `a(u(b, ·)) - a(u(a, ·))`
  (`SymplecticForm.integral_symplecticForm_fderiv_eq_loopArea_sub`), by Green's formula for the
  primitive `λₓ(v) = ½ ω(x, v)` (`SymplecticForm.integral_fderiv_apply_prod_Icc`);
* the Floer energy of `u` is
  `A_{H_b}(u(b, ·)) - A_{H_a}(u(a, ·)) - ∫_{[a, b] × [0, 1]} ∂_s H_s(t, u(s, t)) ds dt`
  (`SymplecticForm.integral_floerEnergyDensity_homotopy`), by the energy identity
  `TauCeti.SymplecticForm.integral_floerEnergyDensity`; for a cylindrical perturbation it is
  `A_H(u(b, ·)) - A_H(u(a, ·))`
  (`SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`).

For a solution with `J` tamed by `ω` the energy density is nonnegative, so the action changes
along the cylinder by at most the integral of a bound for `-∂_s H_s`
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_homotopy`). It increases for a
monotone homotopy (`SymplecticForm.hamiltonianAction_le_hamiltonianAction_of_monotone`), and in
particular along Floer solutions of a cylindrical perturbation
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction`). For the linear homotopy
`H_s = H⁰ + β(s) (H¹ - H⁰)` with monotone `β`, the action changes by at most
`(β(b) - β(a)) ∫₀¹ B` whenever `H⁰_t - H¹_t ≤ B(t)` along the solution
(`SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy`). This bound does
not depend on the profile `β`, so it is uniform over stretched homotopies `β(s / λ)`.

On the whole cylinder `ℝ × [0, 1]`, the energy of a solution is the difference of the limiting
actions at its two ends minus the integral of the curvature
(`SymplecticForm.lintegral_floerEnergyDensity_homotopy_eq_of_tendsto`), and for a cylindrical
perturbation it is the difference of the limiting actions
(`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`). Both follow by
exhausting the cylinder with rectangles (`TauCeti.tendsto_setLIntegral_Icc_neg_prod`). These are
the energy identities of the continuation maps, and the end and neck terms of the energy identity
`E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants.

## Main definitions

* `TauCeti.SymplecticForm.hamiltonianAction`: the Hamiltonian action of a loop.

## Main results

* `SymplecticForm.integral_floerEnergyDensity_homotopy`: the energy of a map over
  `[a, b] × [0, 1]` for the perturbation of a homotopy of Hamiltonians is the change of action
  minus the integrated curvature;
  `SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub` is the cylindrical case.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_homotopy`,
  `SymplecticForm.hamiltonianAction_le_hamiltonianAction_of_monotone`,
  `SymplecticForm.hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy` and
  `SymplecticForm.hamiltonianAction_le_hamiltonianAction`: action bounds along continuation and
  Floer solutions.
* `SymplecticForm.lintegral_floerEnergyDensity_homotopy_eq_of_tendsto` and
  `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`: the energy of a
  continuation or Floer solution on the whole cylinder.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1 and the
  chapter on Floer homology, on the action functional and the energy identity.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
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

section Energy

variable [FiniteDimensional ℝ V] {Hs : ℝ → ℝ → V → ℝ} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}
  {U : Set (ℝ × ℝ)} {a b : ℝ}

/-- Along a map `u` continuous on an open set `U`, the curvature of the perturbation `K = H_s dt`
of a `C¹` homotopy of Hamiltonians is `∂_s H_s(t, u(s, t))`, and this is continuous on `U`. -/
private theorem hamiltonianCurvature_homotopy_comp (ω : SymplecticForm V)
    (hH : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ Hs w.1 w.2)) (hU : IsOpen U)
    (hu : ContinuousOn u U) :
    (∀ z, ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w ↦ Hs w.1 w.2) z (u z) =
        deriv (fun s ↦ Hs s z.2 (u z)) z.1) ∧
      ContinuousOn (fun z ↦ deriv (fun s ↦ Hs s z.2 (u z)) z.1) U := by
  have h (z : ℝ × ℝ) : ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w ↦ Hs w.1 w.2) z (u z) =
      deriv (fun s ↦ Hs s z.2 (u z)) z.1 :=
    ω.hamiltonianCurvature_homotopy (H := Hs) <|
      (hH.differentiable one_ne_zero (z, u z)).comp (f := fun w : ℝ × ℝ ↦ (w, u z)) z
        (differentiableAt_id.prodMk (differentiableAt_const _))
  exact ⟨h, (ω.continuousOn_hamiltonianCurvature_comp hU hu contDiffOn_const
    hH.contDiffOn).congr fun z _ ↦ (h z).symm⟩

/-- **The energy identity for a homotopy of Hamiltonians.** Let `H_s` be a `C¹` family of
time-dependent Hamiltonians and let `u` be `C²` on an open neighbourhood `U` of
`[a, b] × [0, 1]`, with `u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. For the perturbation
`K = H_s(t) dt`, the Floer energy of `u` over the rectangle is the action of the loop at `s = b`
for `H_b`, minus the action of the loop at `s = a` for `H_a`, minus the integral of the curvature
`∂_s H_s` along `u`. -/
theorem integral_floerEnergyDensity_homotopy (ω : SymplecticForm V)
    (hH : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ Hs w.1 w.2)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ Hs w.1 w.2) u z =
      ω.hamiltonianAction (Hs b) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (Hs a) (fun t ↦ u (a, t)) -
          ∫ z in Icc a b ×ˢ Icc 0 1, deriv (fun s ↦ Hs s z.2 (u z)) z.1 := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := (Icc_prod_Icc _ _ _ _)
  have h := ω.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ Hs w.1 w.2) hU
    (hu.of_le one_le_two) contDiffOn_const hH.contDiffOn
    (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩) (hR ▸ hRU)
  simp only [(ω.hamiltonianCurvature_homotopy_comp hH hU hu.continuousOn).1,
    intervalIntegral.integral_zero, ← hR] at h
  rw [h, ω.integral_symplecticForm_fderiv_eq_loopArea_sub hab
      (fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hRU hz))) hper,
    hamiltonianAction_def, hamiltonianAction_def]
  ring

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
  simpa using ω.integral_floerEnergyDensity_homotopy (Hs := fun _ ↦ H)
    (contDiff_uncurry_cylindrical hH) hU hu hab hRU hper

/-- The Floer energy density of a solution of the Floer equation
`∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` for the perturbation `K = H_s(t) dt` of a homotopy of
Hamiltonians is nonnegative when `J` is tamed by `ω`. -/
theorem floerEnergyDensity_homotopy_nonneg (ω : SymplecticForm V) {J : AlmostComplexStructure V}
    (hJ : ω.Tames J) {z : ℝ × ℝ}
    (hfloer : fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Hs z.1 z.2) (u z)) = 0) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ Hs w.1 w.2) u z :=
  ω.floerEnergyDensity_nonneg hJ <|
    (ω.isComplexLinearMap_perturbedFDeriv_iff J _ _ u z).2 (by simpa using hfloer)

/-- The Floer energy density of a solution of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt` is
nonnegative when `J` is tamed by `ω`. -/
theorem floerEnergyDensity_cylindrical_nonneg (ω : SymplecticForm V) {J : AlmostComplexStructure V}
    (hJ : ω.Tames J) {z : ℝ × ℝ}
    (hfloer : fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z :=
  ω.floerEnergyDensity_homotopy_nonneg (Hs := fun _ ↦ H) hJ hfloer

/-- **The action along a continuation solution.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_homotopy`, let `u` solve the Floer equation
`∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` on the rectangle for an almost complex structure `J`
tamed by `ω`. If `g` is an integrable bound for `-∂_s H_s` along `u`, then the action of the loop
at `s = a` for `H_a` is at most the action of the loop at `s = b` for `H_b` plus the integral of
`g`. -/
theorem hamiltonianAction_le_hamiltonianAction_add_of_homotopy (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J)
    (hH : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ Hs w.1 w.2)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Hs z.1 z.2) (u z)) = 0)
    {g : ℝ × ℝ → ℝ} (hg : IntegrableOn g (Icc a b ×ˢ Icc 0 1))
    (hHg : ∀ z ∈ Icc a b ×ˢ Icc 0 1, -deriv (fun s ↦ Hs s z.2 (u z)) z.1 ≤ g z) :
    ω.hamiltonianAction (Hs a) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (Hs b) (fun t ↦ u (b, t)) + ∫ z in Icc a b ×ˢ Icc 0 1, g z := by
  have hmeas : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have h := ω.integral_floerEnergyDensity_homotopy hH hU hu hab hRU hper
  have hnonneg := setIntegral_nonneg (μ := volume) hmeas
    fun z hz ↦ ω.floerEnergyDensity_homotopy_nonneg hJ (hfloer z hz)
  have hcurv : IntegrableOn (fun z ↦ deriv (fun s ↦ Hs s z.2 (u z)) z.1) (Icc a b ×ˢ Icc 0 1) :=
    ((ω.hamiltonianCurvature_homotopy_comp hH hU hu.continuousOn).2.mono hRU).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hle := setIntegral_mono_on hcurv.neg hg hmeas hHg
  simp only [Pi.neg_apply, integral_neg] at hle
  linarith

/-- **The action increases along continuation solutions for monotone homotopies.** Under the
hypotheses of `TauCeti.SymplecticForm.integral_floerEnergyDensity_homotopy`, if `u` solves the
Floer equation `∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` on the rectangle for an almost complex
structure `J` tamed by `ω`, and every `s ↦ H_s(t, x)` is monotone, then the action of the loop at
`s = a` for `H_a` is at most that of the loop at `s = b` for `H_b`. -/
theorem hamiltonianAction_le_hamiltonianAction_of_monotone (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J)
    (hH : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ Hs w.1 w.2))
    (hmono : ∀ t x, Monotone fun s ↦ Hs s t x) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Hs z.1 z.2) (u z)) = 0) :
    ω.hamiltonianAction (Hs a) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (Hs b) (fun t ↦ u (b, t)) := by
  simpa using ω.hamiltonianAction_le_hamiltonianAction_add_of_homotopy hJ hH hU hu hab hRU hper
    hfloer integrableOn_zero fun z _ ↦ neg_nonpos.2 (hmono z.2 (u z)).deriv_nonneg

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
  ω.hamiltonianAction_le_hamiltonianAction_of_monotone (Hs := fun _ ↦ H) hJ
    (contDiff_uncurry_cylindrical hH) (fun _ _ ↦ monotone_const) hU hu hab hRU hper hfloer

/-- **The action estimate for a linear homotopy.** Let `H⁰` and `H¹` be `C¹` time-dependent
Hamiltonians, let `β` be a monotone `C¹` function, and let `H_s = H⁰ + β(s) (H¹ - H⁰)`. Under the
hypotheses of `TauCeti.SymplecticForm.integral_floerEnergyDensity_homotopy`, let `u` solve the
Floer equation `∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` on the rectangle for an almost complex
structure `J` tamed by `ω`. If `H⁰_t - H¹_t ≤ B(t)` along `u`, for a function `B` integrable on
`[0, 1]`, then the action of the loop at `s = a` for `H_a` is at most the action of the loop at
`s = b` for `H_b` plus `(β(b) - β(a)) ∫₀¹ B`. When `β` takes values in `[0, 1]` and `B ≥ 0`, the
error term is at most `∫₀¹ B`, whatever the profile `β`; in particular it does not depend on how
far the homotopy is stretched. -/
theorem hamiltonianAction_le_hamiltonianAction_add_of_linearHomotopy (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J) {H₀ H₁ : ℝ → V → ℝ}
    (hH₀ : ContDiff ℝ 1 (uncurry H₀)) (hH₁ : ContDiff ℝ 1 (uncurry H₁)) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) (hβm : Monotone β) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag -
        ω.hamiltonianVectorField (fun x ↦ H₀ z.2 x + β z.1 * (H₁ z.2 x - H₀ z.2 x)) (u z)) = 0)
    {B : ℝ → ℝ} (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    ω.hamiltonianAction (fun t x ↦ H₀ t x + β a * (H₁ t x - H₀ t x)) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (fun t x ↦ H₀ t x + β b * (H₁ t x - H₀ t x)) (fun t ↦ u (b, t)) +
        (β b - β a) * ∫ t in (0 : ℝ)..1, B t := by
  have hH : ContDiff ℝ 1 (uncurry fun (w : ℝ × ℝ) x ↦ H₀ w.2 x + β w.1 * (H₁ w.2 x - H₀ w.2 x)) :=
    (contDiff_uncurry_cylindrical hH₀).add ((hβ.comp (contDiff_fst.comp contDiff_fst)).mul
      ((contDiff_uncurry_cylindrical hH₁).sub (contDiff_uncurry_cylindrical hH₀)))
  have hβ' : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  -- The curvature is `β'(s) (H¹_t - H⁰_t)`, so `-∂_s H_s ≤ β'(s) B(t)`.
  have hderiv (s t : ℝ) (x : V) :
      deriv (fun s ↦ H₀ t x + β s * (H₁ t x - H₀ t x)) s = deriv β s * (H₁ t x - H₀ t x) := by
    rw [deriv_const_add, deriv_mul_const (hβ.differentiable one_ne_zero s)]
  have hg : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * B z.2) (Icc a b ×ˢ Icc 0 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Integrable.mul_prod hβ'.continuousOn.integrableOn_Icc hB
  have h := ω.hamiltonianAction_le_hamiltonianAction_add_of_homotopy
    (Hs := fun s t x ↦ H₀ t x + β s * (H₁ t x - H₀ t x)) hJ hH hU hu hab hRU hper hfloer hg
    fun z hz ↦ by
      rw [hderiv, ← mul_neg, neg_sub]
      exact mul_le_mul_of_nonneg_left (hHB z hz) hβm.deriv_nonneg
  rwa [Measure.volume_eq_prod, setIntegral_prod_mul, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hβ.differentiable one_ne_zero x)
      (hβ'.intervalIntegrable _ _)] at h

/-- **The energy of a continuation cylinder.** Let `H_s` be a `C¹` family of time-dependent
Hamiltonians and let `u` be `C²` on an open neighbourhood `U` of `ℝ × [0, 1]`, with
`u(s, 1) = u(s, 0)` for all `s`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` there for an almost complex structure `J` tamed by `ω`.
Suppose that the curvature `∂_s H_s` is integrable along `u` over the cylinder, and that the
actions for `H_s` of the loops `t ↦ u(s, t)` tend to `A₁` as `s → -∞` and to `A₂` as `s → ∞`.
Then the energy of `u` is `A₂ - A₁` minus the integral of the curvature along `u`. -/
theorem lintegral_floerEnergyDensity_homotopy_eq_of_tendsto (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hJ : ω.Tames J)
    (hH : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ Hs w.1 w.2)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Hs z.1 z.2) (u z)) = 0)
    (hcurv : IntegrableOn (fun z ↦ deriv (fun s ↦ Hs s z.2 (u z)) z.1)
      ((univ : Set ℝ) ×ˢ Icc 0 1))
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction (Hs s) (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction (Hs s) (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ Hs w.1 w.2) u z) =
      ENNReal.ofReal (A₂ - A₁ -
        ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, deriv (fun s ↦ Hs s z.2 (u z)) z.1) := by
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hmeas (n : ℕ) : MeasurableSet (Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hcont := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ Hs w.1 w.2) hU (hu.of_le one_le_two) contDiffOn_const hH.contDiffOn
  -- On each rectangle `[-n, n] × [0, 1]` the energy is given by the energy identity.
  have hE (n : ℕ) : ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ Hs w.1 w.2) u z) =
        ENNReal.ofReal (ω.hamiltonianAction (Hs n) (fun t ↦ u (n, t)) -
          ω.hamiltonianAction (Hs (-n)) (fun t ↦ u (-n, t)) -
            ∫ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1, deriv (fun s ↦ Hs s z.2 (u z)) z.1) := by
    rw [← ω.integral_floerEnergyDensity_homotopy hH hU hu (neg_le_self n.cast_nonneg)
        ((hRsub n).trans hRU) fun s _ ↦ hper s,
      ofReal_integral_eq_lintegral_ofReal
        ((hcont.mono ((hRsub n).trans hRU)).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))
        (ae_restrict_of_forall_mem (hmeas n)
          fun z hz ↦ ω.floerEnergyDensity_homotopy_nonneg hJ (hfloer z (hRsub n hz)))]
  -- The rectangles exhaust the cylinder, for the energy and for the curvature integral.
  refine tendsto_nhds_unique tendsto_setLIntegral_Icc_neg_prod ?_
  simp only [hE]
  refine (ENNReal.continuous_ofReal.tendsto _).comp (((htop.comp tendsto_natCast_atTop_atTop).sub
    (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))).sub ?_)
  rw [← iUnion_Icc_neg_prod] at hcurv ⊢
  exact tendsto_setIntegral_of_monotone hmeas monotone_Icc_neg_prod hcurv

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
  simpa using ω.lintegral_floerEnergyDensity_homotopy_eq_of_tendsto (Hs := fun _ ↦ H) hJ
    (contDiff_uncurry_cylindrical hH) hU hu hRU hper hfloer (by simp) hbot htop

end Energy

end TauCeti.SymplecticForm
