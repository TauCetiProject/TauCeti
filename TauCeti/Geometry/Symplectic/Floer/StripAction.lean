/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# The energy of Floer strips between exact Lagrangians and the action of their paths

Let `ω = dα` be a nondegenerate exact two-form on a finite-dimensional manifold `M`, such as the
symplectic form of a Liouville domain or of its completion, and let `i₀ : N₀ → M` and
`i₁ : N₁ → M` be maps with `i₀^* α = d f₀` and `i₁^* α = d f₁`, for instance exact Lagrangian
maps with primitives `f₀` and `f₁`. A path `γ : [0, 1] → M` from `L₀ = i₀(N₀)` to `L₁ = i₁(N₁)`,
with `γ(0) = i₀(y₀)` and `γ(1) = i₁(y₁)`, has the **action**

`A_H(γ) = -∫_γ α - ∫₀¹ H(t, γ(t)) dt + f₁(y₁) - f₀(y₀)`

for a time-dependent Hamiltonian `H` (`TauCeti.lagrangianPathAction`). The points `y₀` and `y₁`
over the endpoints are part of the data, so that immersed Lagrangians are allowed. Classically,
the critical points of this functional are the Hamiltonian chords from `L₀` to `L₁`, the
generators of the Floer complex of the pair. In the convention of
`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap`, where `ω = -dθ` and `i^* θ = dh`,
take `α = -θ` and `f = -h`.

A Floer strip is a map `u : ℝ × [0, 1] → M` with `u(s, 0) ∈ L₀` and `u(s, 1) ∈ L₁`, solving
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with the convention `ι_{X_H} ω = dH`. Its paths
`γ_s = u(s, ·)` run from `L₀` to `L₁`. The manifold energy identity
(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`) writes the energy of `u`
over a rectangle `[a, b] × [0, 1]` as the symplectic area plus Hamiltonian boundary terms. By
Stokes' formula the area is the integral of `α` around the boundary of the rectangle. Along the
two horizontal sides `u` stays in a Lagrangian on which `α` is exact, so these sides contribute
only the values of `f₀` and `f₁` at the corners
(`TauCeti.pathIntegral_comp_eq_sub_of_mpullback_eq`). Together:

* for an `s`-dependent family of Hamiltonians `H(s, t, x)`, the energy over `[a, b] × [0, 1]` is
  `A_{H(a, ·)}(γ_a) - A_{H(b, ·)}(γ_b) - ∫ (∂_s H)(s, t, u(s, t))`, the energy identity of a
  continuation strip;
* for an `s`-independent Hamiltonian the energy is `A_H(γ_a) - A_H(γ_b)`, so the action
  decreases along Floer strips, and the energy of a Floer strip on all of `ℝ × [0, 1]` is the
  difference of the limits of the actions at its two ends.

The map `u` is assumed `C²` on all of `ℝ × ℝ`, as in the integration by parts behind Stokes'
formula; only its values on the strip enter the statements. The boundary conditions are required
only along the rectangle in question, through `C¹` lifts `c₀` and `c₁` of the boundary paths to
`N₀` and `N₁`. These are the manifold versions of the statements of
`TauCeti.Geometry.Symplectic.Cotangent.HamiltonianAction` for two exact graphs in a linear
cotangent space.

## Main declarations

* `TauCeti.lagrangianPathAction`: the action of a path between two exact Lagrangians.

In the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.integral_floerEnergyDensity_eq_lagrangianPathAction_sub_sub_integral`: the
  energy identity of a continuation strip over a rectangle.
* `IsNondegenerate.integral_floerEnergyDensity_eq_lagrangianPathAction_sub`: the energy identity
  of a Floer strip over a rectangle.
* `IsNondegenerate.lagrangianPathAction_le_lagrangianPathAction_sub_integral` and
  `IsNondegenerate.lagrangianPathAction_le_lagrangianPathAction`: the action estimates along
  continuation strips and Floer strips.
* `IsNondegenerate.lintegral_floerEnergyDensity_eq_of_tendsto_lagrangianPathAction_sub_integral`
  and `IsNondegenerate.lintegral_floerEnergyDensity_eq_of_tendsto_lagrangianPathAction`: the
  energy of a whole continuation strip and of a whole Floer strip.

## References

* D. Auroux, *A beginner's introduction to Fukaya categories*, arXiv:1301.7056, §1.2 (the action
  of chords between exact Lagrangians and the energy of strips).
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Section 8 (action and energy for exact Lagrangian Floer theory).
* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol. 14
  (2010), Section 7 (energy of strips with Lagrangian boundary in Liouville domains).
-/

public noncomputable section

open Set MeasureTheory Function Filter
open scoped Manifold Interval Topology

namespace TauCeti

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] {N₀ N₁ : Type*}

/-! ### The action of a path between exact Lagrangians -/

/-- The **action** of a path `γ` from `L₀` to `L₁`, for a primitive `α` of the symplectic form,
primitives `f₀` and `f₁` of `α` along the two Lagrangians, a time-dependent Hamiltonian `H` and
points `y₀` and `y₁` of the Lagrangians over the endpoints `γ 0` and `γ 1`:

`A_H(γ) = -∫_γ α - ∫₀¹ H(t, γ(t)) dt + f₁(y₁) - f₀(y₀)`.

With this sign the action decreases along solutions of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for `ω = dα` and `ι_{X_H} ω = dH`. -/
def lagrangianPathAction (α : RoughForm I M ℝ 1) (f₀ : N₀ → ℝ) (f₁ : N₁ → ℝ) (H : ℝ → M → ℝ)
    (γ : ℝ → M) (y₀ : N₀) (y₁ : N₁) : ℝ :=
  -pathIntegral α γ 0 1 - (∫ t in 0..1, H t (γ t)) + f₁ y₁ - f₀ y₀

theorem lagrangianPathAction_def (α : RoughForm I M ℝ 1) (f₀ : N₀ → ℝ) (f₁ : N₁ → ℝ)
    (H : ℝ → M → ℝ) (γ : ℝ → M) (y₀ : N₀) (y₁ : N₁) :
    lagrangianPathAction α f₀ f₁ H γ y₀ y₁ =
      -pathIntegral α γ 0 1 - (∫ t in 0..1, H t (γ t)) + f₁ y₁ - f₀ y₀ :=
  (rfl)

/-- Without Hamiltonian, the action of a path is minus the line integral of `α` plus the
difference of the primitives at its endpoints. -/
@[simp]
theorem lagrangianPathAction_zero (α : RoughForm I M ℝ 1) (f₀ : N₀ → ℝ) (f₁ : N₁ → ℝ)
    (γ : ℝ → M) (y₀ : N₀) (y₁ : N₁) :
    lagrangianPathAction α f₀ f₁ (fun _ _ ↦ 0) γ y₀ y₁ = -pathIntegral α γ 0 1 + f₁ y₁ - f₀ y₀ := by
  simp [lagrangianPathAction_def]

/-- The action of a constant path, at a point `x = i₀(y₀) = i₁(y₁)` of `L₀ ∩ L₁`, is
`f₁(y₁) - f₀(y₀)` minus the time average of the Hamiltonian at `x`. -/
@[simp]
theorem lagrangianPathAction_const (α : RoughForm I M ℝ 1) (f₀ : N₀ → ℝ) (f₁ : N₁ → ℝ)
    (H : ℝ → M → ℝ) (x : M) (y₀ : N₀) (y₁ : N₁) :
    lagrangianPathAction α f₀ f₁ H (fun _ ↦ x) y₀ y₁ = f₁ y₁ - f₀ y₀ - ∫ t in 0..1, H t x := by
  simp only [lagrangianPathAction_def, pathIntegral_const_curve]
  ring

end TauCeti

/-! ### The energy of strips with exact Lagrangian boundary -/

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E]
  {E₀ H₀ N₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace N₀] [ChartedSpace H₀ N₀]
  {E₁ H₁ N₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {u : ℝ × ℝ → M}
  {i₀ : N₀ → M} {f₀ : N₀ → ℝ} {c₀ : ℝ → N₀} {i₁ : N₁ → M} {f₁ : N₁ → ℝ} {c₁ : ℝ → N₁}

omit [FiniteDimensional ℝ E] in
/-- Along a horizontal side of a rectangle on which `u` stays in a map with exact pullback of `α`,
the line integral of `α` is the change of the primitive. -/
private theorem pathIntegral_side_eq_sub {t : ℝ} (hi : MDifferentiable I₀ I i₀)
    (hf : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ s ∈ Icc a b, u (s, t) = i₀ (c₀ s)) :
    pathIntegral α.1 (fun s ↦ u (s, t)) a b = f₀ (c₀ b) - f₀ (c₀ a) := by
  rw [pathIntegral_congr_of_eqOn_uIoo (γ' := i₀ ∘ c₀) fun s hs ↦
      hu s (Ioo_subset_Icc_self (by rwa [uIoo_of_le hab] at hs)),
    pathIntegral_comp_eq_sub_of_mpullback_eq hi hf hL hc]

/-- **The energy identity of a continuation strip.** Let `ω = dα` be a nondegenerate exact
two-form on a finite-dimensional manifold, `H` a `C¹` family of Hamiltonians `H(s, t, x)`, and `u`
a `C²` map whose sides `s ↦ u(s, 0)` and `s ↦ u(s, 1)`, for `s ∈ [a, b]`, are `i₀ ∘ c₀` and
`i₁ ∘ c₁` for `C¹` curves `c₀` and `c₁`, where `i₀^* α = d f₀` and `i₁^* α = d f₁`. For the
perturbation `K = H_{(s, t)} dt`, the Floer energy of `u` over `[a, b] × [0, 1]` is the action of
the path at `s = a` for `H(a, ·)`, minus the action of the path at `s = b` for `H(b, ·)`, minus
the integral of `∂_s H` along `u`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_lagrangianPathAction_sub_sub_integral
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.1 = ω.1) {H : ℝ × ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.1 = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) {a b : ℝ} (hab : a ≤ b)
    (hu₀ : ∀ s ∈ Icc a b, u (s, 0) = i₀ (c₀ s)) (hu₁ : ∀ s ∈ Icc a b, u (s, 1) = i₁ (c₁ s)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) H u z =
      lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) (c₀ a) (c₁ a) -
        lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) (c₀ b) (c₁ b) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have hab' : ((a, 0) : ℝ × ℝ) ≤ (b, 1) := Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩
  have hu₁' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u := hu.of_le one_le_two
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  -- The manifold energy identity: area, plus the vertical Hamiltonian terms, minus `∂_s H`.
  have h := hω.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := H) isOpen_univ
    hu₁'.contMDiffOn contMDiffOn_const hH.contMDiffOn hab' (subset_univ _)
    ((hω.continuous_floerEnergyDensity_zero_left hH hu₁').continuousOn.integrableOn_compact
      isCompact_Icc)
    ((continuous_hamiltonianCurvature_zero_left_comp hH hu₁').continuousOn.integrableOn_compact
      isCompact_Icc)
  simp only [hamiltonianCurvature_zero_left, intervalIntegral.integral_zero, sub_zero] at h
  -- By Stokes' formula the area is the integral of `α` around the rectangle, and the two
  -- horizontal sides, in the Lagrangians, contribute the changes of the primitives.
  rw [hR, h, ← hR]
  have harea : ∫ z in Icc a b ×ˢ Icc 0 1, SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) =
      (pathIntegral α.1 (fun t ↦ u (b, t)) 0 1 - pathIntegral α.1 (fun t ↦ u (a, t)) 0 1) -
        ((f₁ (c₁ b) - f₁ (c₁ a)) - (f₀ (c₀ b) - f₀ (c₀ a))) := by
    have hS := hω₀.setIntegral_eq_rectangleIntegral hu₁' hab'
    rw [← hα, rectangleIntegral_mextDeriv (α.isSmoothForm.of_le (by simp)) hu,
      pathIntegral_side_eq_sub hi₀ hf₀ hL₀ hc₀ hab hu₀,
      pathIntegral_side_eq_sub hi₁ hf₁ hL₁ hc₁ hab hu₁, hα] at hS
    rw [hR, ← hS]
    simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  rw [harea, lagrangianPathAction_def, lagrangianPathAction_def]
  ring

/-- **The energy identity of a Floer strip.** Let `ω = dα` be a nondegenerate exact two-form on a
finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian, and `u` a `C²` map whose sides
`s ↦ u(s, 0)` and `s ↦ u(s, 1)`, for `s ∈ [a, b]`, are `i₀ ∘ c₀` and `i₁ ∘ c₁` for `C¹` curves
`c₀` and `c₁`, where `i₀^* α = d f₀` and `i₁^* α = d f₁`. For the perturbation `K = H_t dt`, the
Floer energy of `u` over `[a, b] × [0, 1]` is `A_H(γ_a) - A_H(γ_b)`, for the paths
`γ_s = u(s, ·)` and their action `TauCeti.lagrangianPathAction`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_lagrangianPathAction_sub
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.1 = ω.1) {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.1 = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) {a b : ℝ} (hab : a ≤ b)
    (hu₀ : ∀ s ∈ Icc a b, u (s, 0) = i₀ (c₀ s)) (hu₁ : ∀ s ∈ Icc a b, u (s, 1) = i₁ (c₁ s)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      lagrangianPathAction α.1 f₀ f₁ H (fun t ↦ u (a, t)) (c₀ a) (c₁ a) -
        lagrangianPathAction α.1 f₀ f₁ H (fun t ↦ u (b, t)) (c₀ b) (c₁ b) := by
  have hH' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
    hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  -- A Hamiltonian independent of `s` has no `s`-derivative.
  have hcurv (z : ℝ × ℝ) : fderiv ℝ (fun w : ℝ × ℝ ↦ H w.2 (u z)) z stdComplexLineReal = 0 := by
    rw [← hamiltonianCurvature_zero_left ω]
    exact hamiltonianCurvature_cylindrical ω H z (u z)
  simpa [hcurv] using
    hω.integral_floerEnergyDensity_eq_lagrangianPathAction_sub_sub_integral hα hH' hu hi₀ hf₀ hL₀
      hc₀ hi₁ hf₁ hL₁ hc₁ hab hu₀ hu₁

/-- **The action estimate along a continuation strip.** Under the hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_eq_lagrangianPathAction_sub_sub_integral`, if `u`
solves the Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` on `[a, b] × [0, 1]` for
almost complex structures `J_z` on `T_{u z} M` tamed by `ω`, then the action of the path at
`s = b` for `H(b, ·)` is at most the action of the path at `s = a` for `H(a, ·)` minus the
integral of `∂_s H` along `u`. -/
theorem IsNondegenerate.lagrangianPathAction_le_lagrangianPathAction_sub_integral
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.1 = ω.1) {H : ℝ × ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.1 = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) {a b : ℝ} (hab : a ≤ b)
    (hu₀ : ∀ s ∈ Icc a b, u (s, 0) = i₀ (c₀ s)) (hu₁ : ∀ s ∈ Icc a b, u (s, 1) = i₁ (c₁ s))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z) (u z)) = 0) :
    lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (b, t)) (fun t ↦ u (b, t)) (c₀ b) (c₁ b) ≤
      lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (a, t)) (fun t ↦ u (a, t)) (c₀ a) (c₁ a) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal := by
  have h := hω.integral_floerEnergyDensity_eq_lagrangianPathAction_sub_sub_integral hα hH hu hi₀
    hf₀ hL₀ hc₀ hi₁ hf₁ hL₁ hc₁ hab hu₀ hu₁
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (hJ z hz) (hfloer z hz)
  linarith

/-- **The action decreases along Floer strips.** Under the hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_eq_lagrangianPathAction_sub`, if `u` solves the
Floer equation `∂_s u + J_z (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for almost complex
structures `J_z` on `T_{u z} M` tamed by `ω`, then the action of the path at `s = b` is at most
that of the path at `s = a`. -/
theorem IsNondegenerate.lagrangianPathAction_le_lagrangianPathAction
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.1 = ω.1) {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.1 = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) {a b : ℝ} (hab : a ≤ b)
    (hu₀ : ∀ s ∈ Icc a b, u (s, 0) = i₀ (c₀ s)) (hu₁ : ∀ s ∈ Icc a b, u (s, 1) = i₁ (c₁ s))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    lagrangianPathAction α.1 f₀ f₁ H (fun t ↦ u (b, t)) (c₀ b) (c₁ b) ≤
      lagrangianPathAction α.1 f₀ f₁ H (fun t ↦ u (a, t)) (c₀ a) (c₁ a) := by
  have h := hω.integral_floerEnergyDensity_eq_lagrangianPathAction_sub hα hH hu hi₀ hf₀ hL₀ hc₀
    hi₁ hf₁ hL₁ hc₁ hab hu₀ hu₁
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := fun w ↦ H w.2) (hJ z hz)
      (hfloer z hz)
  linarith

/-- **The energy of a continuation strip.** Let `ω = dα` be a nondegenerate exact two-form on a
finite-dimensional manifold, `H` a `C¹` family of Hamiltonians `H(s, t, x)`, and `u` a `C²` map
whose sides `s ↦ u(s, 0)` and `s ↦ u(s, 1)` are `i₀ ∘ c₀` and `i₁ ∘ c₁` for `C¹` curves `c₀` and
`c₁`, where `i₀^* α = d f₀` and `i₁^* α = d f₁`. Suppose that `u` solves the Floer equation
`∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` on `ℝ × [0, 1]` for almost complex structures `J_z` tamed by
`ω`, that `∂_s H` is integrable along `u`, and that the actions `A_{H(s, ·)}(u(s, ·))` tend to `A₁`
as `s → -∞` and to `A₂` as `s → ∞`. Then the energy of `u` is `A₁ - A₂` minus the integral of
`∂_s H` along `u`. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_eq_of_tendsto_lagrangianPathAction_sub_integral
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.1 = ω.1) {H : ℝ × ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.1 = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) (hu₀ : ∀ s, u (s, 0) = i₀ (c₀ s))
    (hu₁ : ∀ s, u (s, 1) = i₁ (c₁ s)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z) (u z)) = 0)
    (hint : IntegrableOn (fun z ↦ fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal)
      ((univ : Set ℝ) ×ˢ Icc 0 1))
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (s, t))
      (fun t ↦ u (s, t)) (c₀ s) (c₁ s)) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (s, t))
      (fun t ↦ u (s, t)) (c₀ s) (c₁ s)) atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) H u z) =
      ENNReal.ofReal (A₁ - A₂ -
        ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal) := by
  set f : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ (fun w ↦ H w (u z)) z stdComplexLineReal
  set A : ℝ → ℝ := fun s ↦ lagrangianPathAction α.1 f₀ f₁ (fun t ↦ H (s, t)) (fun t ↦ u (s, t))
    (c₀ s) (c₁ s)
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hcont := hω.continuous_floerEnergyDensity_zero_left hH (hu.of_le one_le_two)
  -- On each rectangle `[-n, n] × [0, 1]` the energy identity holds, with nonnegative density.
  have hE (n : ℕ) : ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) H u z) =
      ENNReal.ofReal (A (-n) - A n - ∫ z in Icc (-(n : ℝ)) n ×ˢ Icc 0 1, f z) := by
    rw [← hω.integral_floerEnergyDensity_eq_lagrangianPathAction_sub_sub_integral hα hH hu hi₀ hf₀
        hL₀ hc₀ hi₁ hf₁ hL₁ hc₁ (neg_le_self n.cast_nonneg) (fun s _ ↦ hu₀ s) fun s _ ↦ hu₁ s,
      ofReal_integral_eq_lintegral_ofReal
        (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
        (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
          fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (hJ z (hRsub n hz))
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
    (((hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)).sub
      (htop.comp tendsto_natCast_atTop_atTop)).sub hf)

/-- **The energy of a Floer strip.** Let `ω = dα` be a nondegenerate exact two-form on a
finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian, and `u` a `C²` map whose
sides `s ↦ u(s, 0)` and `s ↦ u(s, 1)` are `i₀ ∘ c₀` and `i₁ ∘ c₁` for `C¹` curves `c₀` and `c₁`,
where `i₀^* α = d f₀` and `i₁^* α = d f₁`. Suppose that `u` solves the Floer equation
`∂_s u + J_z (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]` for almost complex structures `J_z` tamed by
`ω`. If the actions `A_H(u(s, ·))` tend to `A₁` as `s → -∞` and to `A₂` as `s → ∞`, then the
energy of `u` is `A₁ - A₂`. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_eq_of_tendsto_lagrangianPathAction
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.1 = ω.1) {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.1 = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.1 = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) (hu₀ : ∀ s, u (s, 0) = i₀ (c₀ s))
    (hu₁ : ∀ s, u (s, 1) = i₁ (c₁ s)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ lagrangianPathAction α.1 f₀ f₁ H (fun t ↦ u (s, t)) (c₀ s) (c₁ s))
      atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ lagrangianPathAction α.1 f₀ f₁ H (fun t ↦ u (s, t)) (c₀ s) (c₁ s))
      atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (A₁ - A₂) := by
  have hRsub (n : ℕ) : Icc (-(n : ℝ)) n ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hH' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
    hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hcont := hω.continuous_floerEnergyDensity_zero_left hH' (hu.of_le one_le_two)
  -- Exhaust the strip by the rectangles `[-n, n] × [0, 1]`, on which the energy is the drop of
  -- the action. The action is negated so that the exhaustion lemma applies to an increasing
  -- quantity.
  refine (setLIntegral_univ_prod_eq_ofReal_of_tendsto (F := fun s ↦ -lagrangianPathAction α.1 f₀
    f₁ H (fun t ↦ u (s, t)) (c₀ s) (c₁ s)) (fun n ↦ ?_) hbot.neg htop.neg).trans
    (by rw [neg_sub_neg])
  rw [neg_sub_neg, ← hω.integral_floerEnergyDensity_eq_lagrangianPathAction_sub hα hH hu hi₀ hf₀
      hL₀ hc₀ hi₁ hf₁ hL₁ hc₁ (neg_le_self n.cast_nonneg) (fun s _ ↦ hu₀ s) fun s _ ↦ hu₁ s,
    ofReal_integral_eq_lintegral_ofReal
      (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
        fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := fun w ↦ H w.2)
          (hJ z (hRsub n hz)) (hfloer z (hRsub n hz)))]

end TauCeti.SmoothTwoForm
