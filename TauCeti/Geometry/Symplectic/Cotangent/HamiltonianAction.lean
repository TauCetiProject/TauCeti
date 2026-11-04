/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Action
public import TauCeti.Geometry.Symplectic.Floer.Action
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The Hamiltonian action of two exact graphs and the energy of Floer strips

In the linear cotangent space `V × V'` let `L₀ = graph dh₀` and `L₁ = graph dh₁` be two exact
graphs, and let `H : ℝ → V × V' → ℝ` be a time-dependent Hamiltonian. The **Hamiltonian action**
of a path `γ : [0, 1] → V × V'` from `L₀` to `L₁` is

`A_H(γ) = ∫₀¹ γ^*λ + h₀(π γ(0)) - h₁(π γ(1)) - ∫₀¹ H(t, γ(t)) dt`

(`TauCeti.cotangentHamiltonianAction`): the action `TauCeti.cotangentAction` of the pair of graphs
minus the time integral of `H` along the path. The symplectic form is `ω = -dλ`
(`TauCeti.strongDualCotangentSymplecticForm`), and the Hamiltonian vector field is fixed by
`ω(X_H, ·) = dH` (`TauCeti.SymplecticForm.hamiltonianVectorField`). The paths `t ↦ u(s, t)` of a
strip `u : ℝ × [0, 1] → V × V'` with `u(s, 0) ∈ L₀` and `u(s, 1) ∈ L₁` are paths from `L₀` to
`L₁`, and the Floer equation for strips is

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`.

The Floer energy density `ω(∂_s u, ∂_t u - X_{H_t}(u))` of the perturbation `K = H_t dt`
(`TauCeti.SymplecticForm.floerEnergyDensity`) is nonnegative along a solution when `J` is tamed by
`ω`. The energy identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` writes its integral
over a rectangle as the symplectic area, plus the boundary integral of `K(u)`, minus the integral
of the curvature `∂_s H`. Along the two horizontal sides `dt = 0`, so only the two vertical sides
contribute, and the symplectic area is the drop of the unperturbed action
(`TauCeti.integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub`). Together:

* for an `s`-dependent Hamiltonian `H(s, t, x)`, the energy over `[a, b] × [0, 1]` is
  `A_{H(a, ·)}(u(a, ·)) - A_{H(b, ·)}(u(b, ·)) - ∫ (∂_s H)(s, t, u(s, t))`
  (`TauCeti.integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub_sub_integral`), the
  energy identity of a continuation strip;
* for an `s`-independent Hamiltonian the energy is the drop of the action
  (`TauCeti.integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub`), so the action
  decreases along Floer strips (`TauCeti.cotangentHamiltonianAction_le_cotangentHamiltonianAction`),
  and the energy of a Floer strip on all of `ℝ × [0, 1]` is the difference of the limits of the
  actions at its two ends
  (`TauCeti.lintegral_floerEnergyDensity_eq_of_tendsto_cotangentHamiltonianAction`).

The generators of the Floer complex of the pair are the Hamiltonian chords from `L₀` to `L₁`. When
the paths `t ↦ u(s, t)` converge uniformly, together with the base components of their
derivatives, to chords `x₀` and `x₁` as `s → -∞` and `s → ∞`, the limiting actions are `A_H(x₀)`
and `A_H(x₁)` (`TauCeti.tendsto_cotangentHamiltonianAction_of_tendstoUniformlyOn`), so the energy
of the strip is `A_H(x₀) - A_H(x₁)`
(`TauCeti.lintegral_floerEnergyDensity_eq_of_tendstoUniformlyOn`). For `H = 0`
these are the statements of `TauCeti.Geometry.Symplectic.Cotangent.Action` for holomorphic strips.

## Main declarations

* `TauCeti.cotangentHamiltonianAction`: the Hamiltonian action of a path from `graph dh₀` to
  `graph dh₁`.
* `TauCeti.integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub_sub_integral`: the energy
  identity for an `s`-dependent Hamiltonian over a rectangle.
* `TauCeti.integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub`: the energy identity for
  an `s`-independent Hamiltonian over a rectangle.
* `TauCeti.cotangentHamiltonianAction_le_cotangentHamiltonianAction_sub_integral` and
  `TauCeti.cotangentHamiltonianAction_le_cotangentHamiltonianAction`: the action estimates along
  continuation strips and Floer strips.
* `TauCeti.lintegral_floerEnergyDensity_eq_of_tendsto_cotangentHamiltonianAction`: the energy of a
  whole Floer strip is the difference of its limiting actions.
* `TauCeti.tendsto_cotangentHamiltonianAction_of_tendstoUniformlyOn` and
  `TauCeti.lintegral_floerEnergyDensity_eq_of_tendstoUniformlyOn`: the limiting actions are the
  actions of the limiting paths, and the energy of the strip is their difference.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  §2 (the action functional of a pair of exact Lagrangians and the energy of connecting strips).
* D. Auroux, *A beginner's introduction to Fukaya categories*, arXiv:1301.7056, §1.2 (Hamiltonian
  perturbations of the Floer equation for exact Lagrangians, and the energy of strips).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 8.1
  (Hamiltonian perturbations, their curvature and the energy identity).
-/

public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Set Filter Topology
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Action

/-- The **Hamiltonian action** of a path `γ` in the linear cotangent space `V × V'` from the graph
of `dh₀` to the graph of `dh₁`, for a time-dependent Hamiltonian `H`: the action
`TauCeti.cotangentAction h₀ h₁ γ` of the pair of graphs minus `∫₀¹ H(t, γ(t)) dt`. With this sign
the action decreases along solutions of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`.
-/
def cotangentHamiltonianAction (h₀ h₁ : V → ℝ) (H : ℝ → V × StrongDual ℝ V → ℝ)
    (γ : ℝ → V × StrongDual ℝ V) : ℝ :=
  cotangentAction h₀ h₁ γ - ∫ t in (0 : ℝ)..1, H t (γ t)

lemma cotangentHamiltonianAction_def (h₀ h₁ : V → ℝ) (H : ℝ → V × StrongDual ℝ V → ℝ)
    (γ : ℝ → V × StrongDual ℝ V) :
    cotangentHamiltonianAction h₀ h₁ H γ = cotangentAction h₀ h₁ γ - ∫ t in (0 : ℝ)..1, H t (γ t) :=
  (rfl)

/-- Without Hamiltonian, the Hamiltonian action is the action of the pair of graphs. -/
@[simp]
lemma cotangentHamiltonianAction_zero (h₀ h₁ : V → ℝ) (γ : ℝ → V × StrongDual ℝ V) :
    cotangentHamiltonianAction h₀ h₁ (fun _ _ ↦ 0) γ = cotangentAction h₀ h₁ γ := by
  simp [cotangentHamiltonianAction_def]

/-- The Hamiltonian action of a constant path is `h₀ - h₁` at its base point minus the time
average of the Hamiltonian at the point. -/
@[simp]
lemma cotangentHamiltonianAction_const (h₀ h₁ : V → ℝ) (H : ℝ → V × StrongDual ℝ V → ℝ)
    (x : V × StrongDual ℝ V) :
    cotangentHamiltonianAction h₀ h₁ H (fun _ ↦ x) =
      h₀ x.1 - h₁ x.1 - ∫ t in (0 : ℝ)..1, H t x := by
  simp [cotangentHamiltonianAction_def]

/-- **The action converges to the action of a limiting path.** Suppose paths in the linear
cotangent space, continuous on `[0, 1]` and with continuous base components of their derivatives
there, converge uniformly on `[0, 1]` to a path `x`, and that the base components of their
derivatives converge uniformly on `[0, 1]` to that of `x`. If `H` is jointly continuous and the
endpoint potentials are continuous at the base points of `x 0` and `x 1`, then the Hamiltonian
actions of the paths converge to that of `x`. -/
theorem tendsto_cotangentHamiltonianAction_of_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {γ : ι → ℝ → V × StrongDual ℝ V}
    {x : ℝ → V × StrongDual ℝ V} {h₀ h₁ : V → ℝ} {H : ℝ → V × StrongDual ℝ V → ℝ}
    (hH : Continuous (uncurry H)) (hγc : ∀ᶠ i in l, ContinuousOn (γ i) [[0, 1]])
    (hγc' : ∀ᶠ i in l, ContinuousOn (fun t ↦ (deriv (γ i) t).1) [[0, 1]])
    (hγ : TendstoUniformlyOn γ x l [[0, 1]])
    (hγ' : TendstoUniformlyOn (fun i t ↦ (deriv (γ i) t).1) (fun t ↦ (deriv x t).1) l [[0, 1]])
    (hh₀ : ContinuousAt h₀ (x 0).1) (hh₁ : ContinuousAt h₁ (x 1).1) :
    Tendsto (fun i ↦ cotangentHamiltonianAction h₀ h₁ H (γ i)) l
      (𝓝 (cotangentHamiltonianAction h₀ h₁ H x)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hx : ContinuousOn x [[0, 1]] := hγ.continuousOn hγc.frequently
  have hx' : ContinuousOn (fun t ↦ (deriv x t).1) [[0, 1]] := hγ'.continuousOn hγc'.frequently
  -- The Liouville integrands converge uniformly: they evaluate the covectors of the paths on the
  -- base components of their derivatives, and these pairs converge uniformly (`prodMk` converges
  -- along `l ×ˢ l`, which we pull back along the diagonal).
  have hpair : TendstoUniformlyOn (fun i t ↦ ((γ i t).2, (deriv (γ i) t).1))
      (fun t ↦ ((x t).2, (deriv x t).1)) l [[0, 1]] := fun _ hu ↦
    tendsto_diag.eventually (((uniformContinuous_snd.comp_tendstoUniformlyOn hγ).prodMk hγ') _ hu)
  have hlio : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, (γ i t).2 (deriv (γ i) t).1) l
      (𝓝 (∫ t in (0 : ℝ)..1, (x t).2 (deriv x t).1)) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (hγc.and hγc' |>.mono fun i hi ↦ hi.1.snd.clm_apply hi.2)
      ((isCompact_uIcc.image_of_continuousOn (hx.snd.prodMk hx')).comp_tendstoUniformlyOn
        (g := fun p : StrongDual ℝ V × V ↦ p.1 p.2)
        (fun _ _ ↦ isBoundedBilinearMap_apply.continuous.continuousAt) hpair)
  -- The Hamiltonian integrands converge uniformly, as `H` is continuous.
  have hid : TendstoUniformlyOn (fun (_ : ι) (t : ℝ) ↦ t) id l [[0, 1]] :=
    fun _ hu ↦ .of_forall fun _ _ _ ↦ refl_mem_uniformity hu
  have hgraph : TendstoUniformlyOn (fun i t ↦ (t, γ i t)) (fun t ↦ (t, x t)) l [[0, 1]] :=
    fun _ hu ↦ tendsto_diag.eventually ((hid.prodMk hγ) _ hu)
  have hHint : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, H t (γ i t)) l
      (𝓝 (∫ t in (0 : ℝ)..1, H t (x t))) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (hγc.mono fun i hi ↦ hH.comp_continuousOn (continuousOn_id.prodMk hi))
      ((isCompact_uIcc.image_of_continuousOn (continuousOn_id.prodMk hx)).comp_tendstoUniformlyOn
        (fun _ _ ↦ hH.continuousAt) hgraph)
  have hstart : Tendsto (fun i ↦ h₀ (γ i 0).1) l (𝓝 (h₀ (x 0).1)) :=
    hh₀.tendsto.comp (continuousAt_fst.tendsto.comp (hγ.tendsto_at (by simp)))
  have hend : Tendsto (fun i ↦ h₁ (γ i 1).1) l (𝓝 (h₁ (x 1).1)) :=
    hh₁.tendsto.comp (continuousAt_fst.tendsto.comp (hγ.tendsto_at (by simp)))
  simpa only [cotangentHamiltonianAction_def, cotangentAction_def] using
    ((hlio.add hstart).sub hend).sub hHint

end Action

section Energy

variable [FiniteDimensional ℝ V] {u : ℝ × ℝ → V × StrongDual ℝ V} {h₀ h₁ : V → ℝ}
  {U : Set (ℝ × ℝ)} {a b : ℝ}

/-- **The energy identity for a continuation strip.** Let `H(s, t, x)` be a `C¹` Hamiltonian
depending on both strip coordinates, and let `u` be `C²` on an open neighbourhood `U` of
`[a, b] × [0, 1]`, with its bottom side `t = 0` in the graph of `dh₀` and its top side `t = 1` in
the graph of `dh₁`. For the perturbation `K = H_{s,t} dt`, the Floer energy of `u` over the
rectangle is the Hamiltonian action of `t ↦ u(a, t)` for `H(a, ·)`, minus that of `t ↦ u(b, t)`
for `H(b, ·)`, minus the integral of `∂_s H` along `u`. -/
theorem integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub_sub_integral
    {H : ℝ × ℝ → V × StrongDual ℝ V → ℝ} (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) H u z =
      cotangentHamiltonianAction h₀ h₁ (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) -
        cotangentHamiltonianAction h₀ h₁ (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have h := strongDualCotangentSymplecticForm.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0)
    (Kt := H) hU (hu.of_le one_le_two) contDiffOn_const hH.contDiffOn
    (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩) (hR ▸ hRU)
  simp only [SymplecticForm.hamiltonianCurvature_zero_left, intervalIntegral.integral_zero,
    ← hR] at h
  rw [h, integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub hab
      (fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hRU hz))) hh₀ hh₁ hu₀ hu₁,
    cotangentHamiltonianAction_def, cotangentHamiltonianAction_def]
  ring

/-- **The energy identity for a Floer strip over a rectangle.** Let `H` be a `C¹` time-dependent
Hamiltonian and let `u` be `C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with its bottom
side in the graph of `dh₀` and its top side in the graph of `dh₁`. For the perturbation
`K = H_t dt`, the Floer energy of `u` over the rectangle is the Hamiltonian action of
`t ↦ u(a, t)` minus that of `t ↦ u(b, t)`. -/
theorem integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub
    {H : ℝ → V × StrongDual ℝ V → ℝ} (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (a, t)) -
        cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (b, t)) := by
  -- An `s`-independent Hamiltonian has vanishing `∂_s H`, the curvature of `K = H_t dt`.
  have hcurv (z : ℝ × ℝ) (x : V × StrongDual ℝ V) :
      fderiv ℝ (fun w : ℝ × ℝ ↦ H w.2 x) z stdComplexLineReal = 0 := by
    simpa only [SymplecticForm.hamiltonianCurvature_zero_left] using
      strongDualCotangentSymplecticForm.hamiltonianCurvature_cylindrical H z x
  simpa only [hcurv, integral_zero, sub_zero] using
    integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub_sub_integral (H := fun w ↦ H w.2)
      (SymplecticForm.contDiff_uncurry_cylindrical hH) hU hu hab hRU hh₀ hh₁ hu₀ hu₁

variable {J : AlmostComplexStructure (V × StrongDual ℝ V)}

/-- **The action estimate along a continuation strip.** Under the hypotheses of
`TauCeti.integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub_sub_integral`, if `u` solves
the Floer equation `∂_s u + J (∂_t u - X_{H_{s,t}}(u)) = 0` on the rectangle for an almost
complex structure `J` tamed by `ω`, then the Hamiltonian action of `t ↦ u(b, t)` for `H(b, ·)` is
at most that of `t ↦ u(a, t)` for `H(a, ·)` minus the integral of `∂_s H` along `u`. In particular
the action decreases along a continuation strip for a Hamiltonian that increases in `s`. -/
theorem cotangentHamiltonianAction_le_cotangentHamiltonianAction_sub_integral
    (hJ : strongDualCotangentSymplecticForm.Tames J) {H : ℝ × ℝ → V × StrongDual ℝ V → ℝ}
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1)
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag -
        strongDualCotangentSymplecticForm.hamiltonianVectorField (H z) (u z)) = 0) :
    cotangentHamiltonianAction h₀ h₁ (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) ≤
      cotangentHamiltonianAction h₀ h₁ (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal := by
  have h := integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub_sub_integral hH hU hu hab
    hRU hh₀ hh₁ hu₀ hu₁
  have hnonneg : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1,
      strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) H u z :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
      SymplecticForm.floerEnergyDensity_nonneg _ hJ <|
        (SymplecticForm.isComplexLinearMap_perturbedFDeriv_iff _ J (fun _ _ ↦ 0) H u z).2
          (by simpa using hfloer z hz)
  linarith

/-- **The action decreases along Floer strips.** Under the hypotheses of
`TauCeti.integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub`, if `u` solves the Floer
equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the rectangle for an almost complex structure `J`
tamed by `ω`, then the Hamiltonian action of `t ↦ u(b, t)` is at most that of `t ↦ u(a, t)`. -/
theorem cotangentHamiltonianAction_le_cotangentHamiltonianAction
    (hJ : strongDualCotangentSymplecticForm.Tames J) {H : ℝ → V × StrongDual ℝ V → ℝ}
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hab : a ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1)
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag -
        strongDualCotangentSymplecticForm.hamiltonianVectorField (H z.2) (u z)) = 0) :
    cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (b, t)) ≤
      cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (a, t)) := by
  have h := integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub hH hU hu hab hRU
    hh₀ hh₁ hu₀ hu₁
  have hnonneg : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1,
      strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
      SymplecticForm.floerEnergyDensity_cylindrical_nonneg _ hJ (hfloer z hz)
  linarith

/-- **The energy of a Floer strip.** Let `H` be a `C¹` time-dependent Hamiltonian and let `u` be
`C²` on an open neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 0)` in the graph of `dh₀` and
`u(s, 1)` in the graph of `dh₁`, solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`
there for an almost complex structure `J` tamed by `ω`. If the Hamiltonian actions of the paths
`t ↦ u(s, t)` tend to `A₁` as `s → -∞` and to `A₂` as `s → ∞`, then the energy of `u` is
`A₁ - A₂`. -/
theorem lintegral_floerEnergyDensity_eq_of_tendsto_cotangentHamiltonianAction
    (hJ : strongDualCotangentSymplecticForm.Tames J) {H : ℝ → V × StrongDual ℝ V → ℝ}
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hh₀ : ∀ s, DifferentiableAt ℝ h₀ (u (s, 0)).1) (hh₁ : ∀ s, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1)
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag -
        strongDualCotangentSymplecticForm.hamiltonianVectorField (H z.2) (u z)) = 0)
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (s, t))) atTop
      (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal
        (strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (A₁ - A₂) := by
  -- Exhaust the strip by the rectangles `[-n, n] × [0, 1]`, on which `-A_H` increases by the
  -- energy.
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hdens : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, 0 ≤
      strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z :=
    fun z hz ↦ SymplecticForm.floerEnergyDensity_cylindrical_nonneg _ hJ (hfloer z hz)
  have hcont := strongDualCotangentSymplecticForm.continuousOn_floerEnergyDensity
    (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) hU (hu.of_le one_le_two) contDiffOn_const
    (SymplecticForm.contDiff_uncurry_cylindrical hH).contDiffOn
  rw [← neg_sub_neg]
  refine setLIntegral_univ_prod_eq_ofReal_of_tendsto (F := fun s ↦
    -cotangentHamiltonianAction h₀ h₁ H (fun t ↦ u (s, t))) (fun n ↦ ?_) hbot.neg htop.neg
  rw [neg_sub_neg, ← integral_floerEnergyDensity_eq_cotangentHamiltonianAction_sub hH hU hu
      (neg_le_self n.cast_nonneg) ((hRsub n).trans hRU) (fun s _ ↦ hh₀ s) (fun s _ ↦ hh₁ s)
      (fun s _ ↦ hu₀ s) (fun s _ ↦ hu₁ s),
    ofReal_integral_eq_lintegral_ofReal
      ((hcont.mono ((hRsub n).trans hRU)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
        fun z hz ↦ hdens z (hRsub n hz))]

/-- **The energy of a Floer strip is the difference of the actions of its ends.** Suppose a Floer
strip as in `TauCeti.lintegral_floerEnergyDensity_eq_of_tendsto_cotangentHamiltonianAction`
converges, as the strip coordinate tends to `-∞` and `+∞`, uniformly on `[0, 1]` to paths `x₀`
and `x₁`, with the base components of its path derivatives converging uniformly on `[0, 1]` to
those of `x₀` and `x₁`. If the endpoint potentials are continuous at the endpoints of `x₀` and
`x₁`, then the energy of the strip is `A_H(x₀) - A_H(x₁)`.

In Floer applications `x₀` and `x₁` are Hamiltonian chords from the graph of `dh₀` to the graph
of `dh₁`; the statement does not need this. -/
theorem lintegral_floerEnergyDensity_eq_of_tendstoUniformlyOn
    (hJ : strongDualCotangentSymplecticForm.Tames J) {H : ℝ → V × StrongDual ℝ V → ℝ}
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hh₀ : ∀ s, DifferentiableAt ℝ h₀ (u (s, 0)).1) (hh₁ : ∀ s, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1)
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J (fderiv ℝ u z stdComplexLineImag -
        strongDualCotangentSymplecticForm.hamiltonianVectorField (H z.2) (u z)) = 0)
    {x₀ x₁ : ℝ → V × StrongDual ℝ V}
    (hbot : TendstoUniformlyOn (fun s t ↦ u (s, t)) x₀ atBot [[0, 1]])
    (hbot' : TendstoUniformlyOn (fun s t ↦ (deriv (fun t ↦ u (s, t)) t).1)
      (fun t ↦ (deriv x₀ t).1) atBot [[0, 1]])
    (htop : TendstoUniformlyOn (fun s t ↦ u (s, t)) x₁ atTop [[0, 1]])
    (htop' : TendstoUniformlyOn (fun s t ↦ (deriv (fun t ↦ u (s, t)) t).1)
      (fun t ↦ (deriv x₁ t).1) atTop [[0, 1]])
    (hh₀bot : ContinuousAt h₀ (x₀ 0).1) (hh₁bot : ContinuousAt h₁ (x₀ 1).1)
    (hh₀top : ContinuousAt h₀ (x₁ 0).1) (hh₁top : ContinuousAt h₁ (x₁ 1).1) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal
        (strongDualCotangentSymplecticForm.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (cotangentHamiltonianAction h₀ h₁ H x₀ -
        cotangentHamiltonianAction h₀ h₁ H x₁) := by
  have h01 : [[(0 : ℝ), 1]] = Icc 0 1 := uIcc_of_le zero_le_one
  have hmem {s t : ℝ} (ht : t ∈ [[(0 : ℝ), 1]]) : ((s, t) : ℝ × ℝ) ∈ U :=
    hRU ⟨mem_univ s, h01 ▸ ht⟩
  -- Along each path `t ↦ u(s, t)` the derivative is `∂_t u`, which is continuous.
  have hderiv (s : ℝ) {t : ℝ} (ht : t ∈ [[(0 : ℝ), 1]]) :
      deriv (fun t ↦ u (s, t)) t = fderiv ℝ u (s, t) stdComplexLineImag := by
    have hv : HasDerivAt (fun t ↦ ((s, t) : ℝ × ℝ)) stdComplexLineImag t :=
      stdComplexLineImag_eq ▸ hasDerivAt_prodMk_right s t
    exact (((hu.differentiableOn two_ne_zero _ (hmem ht)).differentiableAt
      (hU.mem_nhds (hmem ht))).hasFDerivAt.comp_hasDerivAt t hv).deriv
  have hpath (s : ℝ) : ContinuousOn (fun t ↦ u (s, t)) [[0, 1]] :=
    hu.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun _ ht ↦ hmem ht
  have hpath' (s : ℝ) : ContinuousOn (fun t ↦ (deriv (fun t ↦ u (s, t)) t).1) [[0, 1]] := by
    refine ContinuousOn.congr (f := fun t ↦ (fderiv ℝ u (s, t) stdComplexLineImag).1) ?_
      fun t ht ↦ by rw [hderiv s ht]
    exact (((hu.continuousOn_fderiv_of_isOpen hU one_le_two).comp
      (continuousOn_const.prodMk continuousOn_id) fun _ ht ↦ hmem ht).clm_apply
        continuousOn_const).fst
  have hHc : Continuous (uncurry H) := hH.continuous
  exact lintegral_floerEnergyDensity_eq_of_tendsto_cotangentHamiltonianAction hJ hH hU hu hRU
    hh₀ hh₁ hu₀ hu₁ hfloer
    (tendsto_cotangentHamiltonianAction_of_tendstoUniformlyOn hHc (.of_forall hpath)
      (.of_forall hpath') hbot hbot' hh₀bot hh₁bot)
    (tendsto_cotangentHamiltonianAction_of_tendstoUniformlyOn hHc (.of_forall hpath)
      (.of_forall hpath') htop htop' hh₀top hh₁top)

end Energy

end TauCeti
