/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.Basic
public import TauCeti.Geometry.Symplectic.Floer.Energy
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

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

For a solution with tame `J`, the action therefore drops by at most the integral of `-∂_s H` along
`u` (`SymplecticForm.hamiltonianAction_le_hamiltonianAction_sub_integral`), and it does not drop
for a monotone homotopy (`SymplecticForm.hamiltonianAction_le_hamiltonianAction_of_monotone`).

A `1`-periodic orbit `x` of `X_{H_t}` is a critical point of the action, so for a loop `γ` the
difference `A_H(γ) - A_H(x)` has no term linear in `ξ = γ - x`: it is
`∫₀¹ (½ ω(ξ, ξ') + H_t(γ) - H_t(x) - dH_t(x) ξ) dt`
(`SymplecticForm.hamiltonianAction_sub_hamiltonianAction_eq_integral`).

## Main definitions

* `TauCeti.SymplecticForm.hamiltonianAction`: the Hamiltonian action of a loop.

## Main results

* `integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral_hamiltonianCurvature`:
  the energy of a map over `[a, b] × [0, 1]`, for a perturbation which is `H_a dt` and `H_b dt` on
  the two boundary circles, is the change of action minus the integrated curvature.
* `SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`: the energy of a map over
  `[a, b] × [0, 1]` for a cylindrical perturbation is the change of action.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction`: the action increases along Floer
  solutions.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`: the energy of a
  Floer solution on the whole cylinder is the difference of its limiting actions.
* `SymplecticForm.tendsto_hamiltonianAction`: the action is continuous for uniform `C¹`
  convergence of loops.
* `SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral`: the energy
  identity of a continuation cylinder over a rectangle.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction_sub_integral`: the action estimate along
  a continuation cylinder over a rectangle.
* `SymplecticForm.hamiltonianAction_le_hamiltonianAction_of_monotone`: the action does not drop
  along a continuation cylinder of a monotone homotopy.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral`: the
  energy identity of a continuation cylinder over the whole cylinder.
* `SymplecticForm.hamiltonianAction_sub_hamiltonianAction_eq_integral`: the expansion of the
  action at an orbit, without linear term.

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

section Curvature

variable [FiniteDimensional ℝ V] {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)} {a b : ℝ}

/-- **The energy identity between two loops.** Let `u` be `C²` and the perturbation components
`K_s` and `K_t` be `C¹` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` and `K_s(s, 1) = K_s(s, 0)` for `s ∈ [a, b]`, so that the bottom and top sides
of the rectangle are glued into a cylinder. If on the two boundary circles the `dt`-component of
`K` is a time-dependent Hamiltonian, `K_t(a, t) = H_a(t)` and `K_t(b, t) = H_b(t)`, then the Floer
energy of `u` over the rectangle is the change of action minus the integrated curvature:

`∫ E = A_{H_b}(u(b, ·)) - A_{H_a}(u(a, ·)) - ∫ R_K(u)`.

No condition is imposed on `K_s` along the two boundary circles or on `K` in the interior. -/
theorem integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral_hamiltonianCurvature
    (ω : SymplecticForm V) {Ks Kt : ℝ × ℝ → V → ℝ} {Ha Hb : ℝ → V → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ)) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hKper : ∀ s ∈ Icc a b, Ks (s, 1) = Ks (s, 0)) (hKa : ∀ t ∈ Icc (0 : ℝ) 1, Kt (a, t) = Ha t)
    (hKb : ∀ t ∈ Icc (0 : ℝ) 1, Kt (b, t) = Hb t) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u z =
      ω.hamiltonianAction Hb (fun t ↦ u (b, t)) - ω.hamiltonianAction Ha (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature Ks Kt z (u z) := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := (Icc_prod_Icc _ _ _ _)
  have h := ω.integral_floerEnergyDensity hU (hu.of_le one_le_two) hKs hKt
    (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩) (hR ▸ hRU)
  rw [← hR] at h
  -- The `ds` terms along the bottom and top sides cancel, since both sides are the same loop.
  have hbot : ∫ s in a..b, Ks (s, 0) (u (s, 0)) = ∫ s in a..b, Ks (s, 1) (u (s, 1)) :=
    intervalIntegral.integral_congr fun s hs ↦ by
      rw [uIcc_of_le hab] at hs
      rw [hKper s hs, hper s hs]
  -- The `dt` terms along the two ends are the Hamiltonian terms of the actions.
  have hend (c : ℝ) (H : ℝ → V → ℝ) (hc : ∀ t ∈ Icc (0 : ℝ) 1, Kt (c, t) = H t) :
      ∫ t in (0 : ℝ)..1, Kt (c, t) (u (c, t)) = ∫ t in (0 : ℝ)..1, H t (u (c, t)) :=
    intervalIntegral.integral_congr fun t ht ↦ by
      rw [uIcc_of_le zero_le_one] at ht
      rw [hc t ht]
  rw [h, hbot, hend a Ha hKa, hend b Hb hKb, ω.integral_symplecticForm_fderiv_eq_loopArea_sub hab
      (fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hRU hz))) hper,
    hamiltonianAction_def, hamiltonianAction_def]
  ring

end Curvature

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
  simpa only [hamiltonianCurvature_zero_left] using
    ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral_hamiltonianCurvature
      (Ks := fun _ _ ↦ 0) (Kt := H) (Ha := fun t ↦ H (a, t)) (Hb := fun t ↦ H (b, t)) hU hu
      contDiffOn_const hH.contDiffOn hab hRU hper (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

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
  have hnonneg : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ by
      rw [stdComplexLineReal_eq, fderiv_apply_mk_one_zero (u := fun w ↦ H w (u z))
        ((hH.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero z)]
      exact (hmono z.2 (u z)).deriv_nonneg
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
  exact setLIntegral_univ_prod_eq_ofReal_of_tendsto_sub_integral measurableSet_Icc hint hE hbot htop

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
  simpa only [fderiv_cylindrical_apply_stdComplexLineReal, integral_zero, sub_zero] using
    ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral
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
Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the rectangle for almost complex
structures `J z` tamed by `ω`, which may depend on the domain point, then the action of the loop at
`s = a` is at most that of the loop at `s = b`. -/
theorem hamiltonianAction_le_hamiltonianAction (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ω.hamiltonianAction H (fun t ↦ u (a, t)) ≤ ω.hamiltonianAction H (fun t ↦ u (b, t)) :=
  ω.hamiltonianAction_le_hamiltonianAction_of_monotone (H := fun w ↦ H w.2) hJ
    (contDiff_uncurry_cylindrical hH) (fun _ _ _ _ _ ↦ le_rfl) hU hu hab hRU hper hfloer

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
  simpa only [fderiv_cylindrical_apply_stdComplexLineReal, integral_zero, sub_zero] using
    ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral
      (H := fun w ↦ H w.2) (J := fun _ ↦ J) (fun _ _ ↦ hJ) (contDiff_uncurry_cylindrical hH) hU hu
      hRU hper hfloer
      (by simp only [fderiv_cylindrical_apply_stdComplexLineReal]; exact integrableOn_zero) hbot
      htop

end Energy

section Expansion

variable [FiniteDimensional ℝ V] {H : ℝ → V → ℝ} {x : ℝ → V}

open intervalIntegral in
/-- **The action near a critical loop.** Let `x` be an orbit of the Hamiltonian vector field of a
`C¹` Hamiltonian `H` with `x 1 = x 0`, and let `γ` be a loop with continuous derivative `γ'` and
`γ 1 = γ 0`. Since `x` is a critical point of the action, the action difference has no term linear
in `ξ = γ - x`:
`A_H(γ) - A_H(x) = ∫₀¹ (½ ω(ξ, ξ') + H_t(γ) - H_t(x) - dH_t(x) ξ) dt`. -/
theorem hamiltonianAction_sub_hamiltonianAction_eq_integral (ω : SymplecticForm V)
    (hH : ContDiff ℝ 1 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    {γ γ' : ℝ → V} (hγ' : Continuous γ') (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ1 : γ 1 = γ 0) :
    ω.hamiltonianAction H γ - ω.hamiltonianAction H x =
      ∫ t in (0 : ℝ)..1, ((1 / 2 : ℝ) *
        ω (γ t - x t) (γ' t - ω.hamiltonianVectorField (H t) (x t)) +
        (H t (γ t) - H t (x t) - fderiv ℝ (H t) (x t) (γ t - x t))) := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  set ξ : ℝ → V := fun t ↦ γ t - x t with hξdef
  set ξ' : ℝ → V := fun t ↦ γ' t - X t (x t) with hξ'def
  simp only [← ω.apply_hamiltonianVectorField]
  have hXc : Continuous (uncurry X) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hXcomp {p : ℝ → V} (hp : Continuous p) : Continuous fun t ↦ X t (p t) :=
    hXc.comp (continuous_id.prodMk hp)
  have hHcomp {p : ℝ → V} (hp : Continuous p) : Continuous fun t ↦ H t (p t) :=
    hH.continuous.comp (continuous_id.prodMk hp)
  have hξc : Continuous ξ := hγc.sub hxc
  have hξ'c : Continuous ξ' := hγ'.sub (hXcomp hxc)
  -- The derivative of `ω(x, ξ)` integrates to zero over a period.
  have i₆ : IntervalIntegrable (fun t ↦ ω (X t (x t)) (ξ t) + ω (x t) (ξ' t)) volume 0 1 :=
    ((ω.continuous_apply_comp (hXcomp hxc) hξc).add
      (ω.continuous_apply_comp hxc hξ'c)).intervalIntegrable _ _
  have hφ : ∫ t in (0 : ℝ)..1, (ω (X t (x t)) (ξ t) + ω (x t) (ξ' t)) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt (f := fun t ↦ ω (x t) (ξ t))
      (fun t _ ↦ ω.hasDerivAt_apply_comp (hx t) ((hγ t).sub (hx t))) i₆]
    simp [hξdef, hγ1, hx1]
  -- Pointwise, the action density differs from the claimed integrand by half that derivative.
  have hpt (t : ℝ) : (1 / 2 : ℝ) * ω (γ t) (γ' t) + H t (γ t) -
      ((1 / 2 : ℝ) * ω (x t) (X t (x t)) + H t (x t)) =
      ((1 / 2 : ℝ) * ω (ξ t) (ξ' t) + (H t (γ t) - H t (x t) - ω (X t (x t)) (ξ t))) +
        (1 / 2 : ℝ) * (ω (X t (x t)) (ξ t) + ω (x t) (ξ' t)) := by
    have hγt : γ t = x t + ξ t := by simp [hξdef]
    have hγ't : γ' t = X t (x t) + ξ' t := by simp [hξ'def]
    have hskew : ω (ξ t) (X t (x t)) = -ω (X t (x t)) (ξ t) := (ω.neg_eq _ _).symm
    simp only [hγt, hγ't, map_add, LinearMap.add_apply] at hskew ⊢
    linear_combination (1 / 2 : ℝ) * hskew
  have hdγ : deriv γ = γ' := funext fun t ↦ (hγ t).deriv
  have hdx : deriv x = fun t ↦ X t (x t) := funext fun t ↦ (hx t).deriv
  have i₁ := (ω.continuous_apply_comp hγc hγ').intervalIntegrable (μ := volume) 0 1
  have i₂ := (hHcomp hγc).intervalIntegrable (μ := volume) 0 1
  have i₃ := (ω.continuous_apply_comp hxc (hXcomp hxc)).intervalIntegrable (μ := volume) 0 1
  have i₄ := (hHcomp hxc).intervalIntegrable (μ := volume) 0 1
  have i₅ : IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) * ω (ξ t) (ξ' t) +
      (H t (γ t) - H t (x t) - ω (X t (x t)) (ξ t))) volume 0 1 :=
    ((continuous_const.mul (ω.continuous_apply_comp hξc hξ'c)).add
      (((hHcomp hγc).sub (hHcomp hxc)).sub
        (ω.continuous_apply_comp (hXcomp hxc) hξc))).intervalIntegrable _ _
  have h := integral_congr (μ := volume) (a := 0) (b := 1) fun t _ ↦ hpt t
  rw [integral_sub ((i₁.const_mul _).add i₂) ((i₃.const_mul _).add i₄), integral_add i₅
    (i₆.const_mul _), integral_add (i₁.const_mul _) i₂, integral_add (i₃.const_mul _) i₄,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hφ] at h
  rw [hamiltonianAction_def, hamiltonianAction_def, loopArea_def, loopArea_def, hdγ, hdx]
  linear_combination h

end Expansion

section Continuity

variable [FiniteDimensional ℝ V] {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
  {H : ℝ → V → ℝ} {x : ι → ℝ → V} {x₀ : ℝ → V}

/-- **The action is continuous for uniform `C¹` convergence of loops.** Let `H` be a continuous
time-dependent Hamiltonian. If the loops `x i` and their derivatives are eventually continuous on
`[0, 1]` and converge uniformly there to `x₀` and to the derivative of `x₀`, then the actions of the
`x i` converge to the action of `x₀`. -/
theorem tendsto_hamiltonianAction (ω : SymplecticForm V) (hH : Continuous (uncurry H))
    (hx : ∀ᶠ i in l, ContinuousOn (x i) (Icc 0 1))
    (hdx : ∀ᶠ i in l, ContinuousOn (deriv (x i)) (Icc 0 1))
    (hlim : TendstoUniformlyOn x x₀ l (Icc 0 1))
    (hdlim : TendstoUniformlyOn (fun i ↦ deriv (x i)) (deriv x₀) l (Icc 0 1)) :
    Tendsto (fun i ↦ ω.hamiltonianAction H (x i)) l (𝓝 (ω.hamiltonianAction H x₀)) := by
  -- The pairs `(x(t), x'(t))` converge uniformly on `[0, 1]`, so the integrands of the symplectic
  -- area and of the Hamiltonian term, continuous functions of `t` and of the pair, converge.
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hx hdx hlim hdlim
  have hP := hlim.prodMk_same hdlim
  have hPc : ∀ᶠ i in l, ContinuousOn (fun t ↦ (x i t, deriv (x i) t)) (uIcc 0 1) :=
    (hx.and hdx).mono fun i hi ↦ hi.1.prodMk hi.2
  have hg1 : Continuous (uncurry fun (_ : ℝ) (p : V × V) ↦ ω p.1 p.2) :=
    ω.continuous_apply_comp continuous_snd.fst continuous_snd.snd
  have hg2 : Continuous (uncurry fun t (p : V × V) ↦ H t p.1) :=
    hH.comp (continuous_fst.prodMk continuous_snd.fst)
  simpa only [hamiltonianAction_def, loopArea_def] using
    (tendsto_const_nhds.mul (hP.tendsto_intervalIntegral_comp hg1 hPc)).add
      (hP.tendsto_intervalIntegral_comp hg2 hPc)

end Continuity

end TauCeti.SymplecticForm
