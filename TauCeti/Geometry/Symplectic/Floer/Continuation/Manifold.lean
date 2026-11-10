/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylinderAction

/-!
# Continuation cylinders in a manifold and the capped action

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as the symplectic
form of a closed symplectic manifold, and let `H₀`, `H₁ : ℝ → M → ℝ` be `C¹` time-dependent
Hamiltonians. A continuation cylinder from `H₀` to `H₁` solves the Floer equation
`∂_s u + J (∂_t u - X_{H_{(s, t)}}(u)) = 0` for the linear homotopy
`H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` (`TauCeti.Floer.linearHomotopy`) with a monotone
`C¹` profile `β`, for instance the continuation homotopy (`TauCeti.Floer.continuationHomotopy`),
whose profile increases from `0` on `s ≤ 0` to `1` on `s ≥ 1`. Its curvature is
`R_K = ∂_s H = β'(s) (H₁ - H₀)(t)` (`TauCeti.SmoothTwoForm.hamiltonianCurvature_zero_left` and
`TauCeti.Floer.fderiv_linearHomotopy_stdComplexLineReal`).

The energy identity for a family of Hamiltonians on a manifold target
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub_sub_integral`)
measures the Floer energy of `u` over `[a, b] × [0, 1]`, corrected by the integrated curvature,
against the capped action
`A_H(γ, v) = ∫ v^* ω - ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cylinderAction`). Write `γ_a = u(a, ·)` and
`γ_b = u(b, ·)`, let `v` be a map with `v(0, ·) = γ_b`, and let `w # v` be the map with
`(w # v)(0, ·) = γ_a` obtained by gluing `u|_{[a, b]}` to `v`. When `u` is a cylinder of loops
and `v` is a cap of `γ_b`, `w # v` is a cap of `γ_a` and both actions below are capped actions.
If `H₀ - H₁ ≤ B` along `u`, then

`E(u) ≤ A_{H(a, ·)}(γ_a, w # v) - A_{H(b, ·)}(γ_b, v) + (β(b) - β(a)) ∫₀¹ B`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_linearHomotopy_le`). Since the
energy of a solution with almost complex structures tamed by `ω` is nonnegative, the capped action
increases by at most `(β(b) - β(a)) ∫₀¹ B` from the end `s = a` to the end `s = b`
(`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_linearHomotopy`).
For the continuation homotopy with `a ≤ 0` and `1 ≤ b`, the end Hamiltonians are `H₀` and `H₁`
and, if `H₀ - H₁ ≤ h` on the whole target,

`A_{H₁}(γ_b, v) ≤ A_{H₀}(γ_a, w # v) + ∫₀¹ h`

(`SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_continuationHomotopy`).
Taking `h(t) = sup_x (H₀ - H₁)(t, x)`, this is the shift `∫₀¹ sup (H₀ - H₁) dt` of the action
filtration of capped generators under continuation, with the caps carried along the cylinder.
No weak exactness or closedness of `ω` is used, so the statements apply to the closed monotone
targets of capped Floer theory, such as `ℂPⁿ`. The corresponding statements for a symplectic
vector space target, without caps, are in `TauCeti.Geometry.Symplectic.Floer.Continuation`, and
those for the contractible action of a weakly exact form are in
`TauCeti.Geometry.Symplectic.Floer.CylinderAction`.

The existence, compactness and counting of continuation cylinders are not treated here.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_linearHomotopy_le`: the
  energy bound of a linear homotopy in terms of capped actions.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_linearHomotopy`:
  the capped action shift along a solution.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_continuationHomotopy_le`,
  `SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_continuationHomotopy`:
  the same for continuation cylinders from `H₀` to `H₁`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progr. Math. 133 (1995), 483–524, on continuation maps of capped Floer complexes.
-/

public section

open Function MeasureTheory Set Real
open scoped Manifold

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H₀ H₁ : ℝ → M → ℝ} {u v : ℝ × ℝ → M}
  {a b : ℝ}

variable [FiniteDimensional ℝ E]

/-- **The energy bound of a linear homotopy, with caps.** Let `ω` be a nondegenerate two-form on a
finite-dimensional manifold, `H₀` and `H₁` `C¹` time-dependent Hamiltonians, `β` a monotone `C¹`
profile, `u` a `C¹` map and `v` a `C¹` map with `v (0, ·) = u (b, ·)`. If `H₀ - H₁ ≤ B` along `u`
on `[a, b] × [0, 1]` for a function `B` integrable on `[0, 1]`, then for the linear homotopy
`H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` the Floer energy of `u` over the rectangle is at most
`A_{H(a, ·)}(γ_a, w # v) - A_{H(b, ·)}(γ_b, v) + (β(b) - β(a)) ∫₀¹ B`, where `γ_a = u(a, ·)`,
`γ_b = u(b, ·)`, `A` is the capped action `TauCeti.cylinderAction`, and `w # v` glues `u`, rescaled
from `[a, b]` to `[0, 1]`, to `v`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_linearHomotopy_le (hω : ω.IsNondegenerate)
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hab : a ≤ b)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t)) {B : ℝ → ℝ}
    (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (linearHomotopy β H₀ H₁) u z ≤
      cylinderAction ω.1 (fun t ↦ linearHomotopy β H₀ H₁ (a, t))
          (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) -
        cylinderAction ω.1 (fun t ↦ linearHomotopy β H₀ H₁ (b, t)) v +
        (β b - β a) * ∫ t in Icc 0 1, B t := by
  rw [hω.integral_floerEnergyDensity_eq_cylinderAction_sub_sub_integral
    (contMDiff_uncurry_linearHomotopy hβ hH₀ hH₁) hu hab hv hv₀]
  linarith [neg_setIntegral_fderiv_linearHomotopy_le hH₀ hH₁ hβ hβm hu.continuous hab hB hHB]

/-- **The capped action shift of a linear homotopy.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_linearHomotopy_le`, if `u`
solves the Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` for the linear homotopy on
`[a, b] × [0, 1]`, with almost complex structures `J z` on `T_{u z} M` tamed by `ω`, then the
action of `γ_b = u(b, ·)` for `H(b, ·)` measured against `v` is at most the action of
`γ_a = u(a, ·)` for `H(a, ·)` measured against the glued map `w # v`, plus
`(β(b) - β(a)) ∫₀¹ B`. When `v` is a cap of `γ_b`, both actions are capped actions. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_of_linearHomotopy
    (hω : ω.IsNondegenerate) (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hab : a ≤ b)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (linearHomotopy β H₀ H₁ z) (u z)) = 0)
    {B : ℝ → ℝ} (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    cylinderAction ω.1 (fun t ↦ linearHomotopy β H₀ H₁ (b, t)) v ≤
      cylinderAction ω.1 (fun t ↦ linearHomotopy β H₀ H₁ (a, t))
          (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        (β b - β a) * ∫ t in Icc 0 1, B t := by
  have h := hω.integral_floerEnergyDensity_linearHomotopy_le hH₀ hH₁ hβ hβm hu hab hv hv₀ hB hHB
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := linearHomotopy β H₀ H₁) (hJ z hz)
      (hfloer z hz)
  linarith

/-- **The energy bound of a continuation cylinder, with caps.** Let `ω` be a nondegenerate
two-form on a finite-dimensional manifold, `H₀` and `H₁` `C¹` time-dependent Hamiltonians with
`H₀ - H₁ ≤ h` on `[0, 1]`, uniformly on the target, `u` a `C¹` map, and `v` a `C¹` map with
`v (0, ·) = u (b, ·)`, where `a ≤ 0` and `1 ≤ b`. For the continuation homotopy from `H₀` to `H₁`,
the Floer energy of `u` over `[a, b] × [0, 1]` is at most
`A_{H₀}(γ_a, w # v) - A_{H₁}(γ_b, v) + ∫₀¹ h`, for the capped action `TauCeti.cylinderAction`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_continuationHomotopy_le
    (hω : ω.IsNondegenerate) (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (ha : a ≤ 0) (hb : 1 ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = u (b, t)) {h : ℝ → ℝ}
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t) (hhi : IntegrableOn h (Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        ω.floerEnergyDensity (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) u z ≤
      cylinderAction ω.1 H₀ (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) -
        cylinderAction ω.1 H₁ v + ∫ t in Icc 0 1, h t := by
  have hE := hω.integral_floerEnergyDensity_linearHomotopy_le hH₀ hH₁
    (smoothTransition.contDiff (n := 1)) smoothTransition.monotone hu
    (ha.trans (zero_le_one.trans hb)) hv hv₀ hhi fun z hz ↦ hh z.2 hz.2 (u z)
  rwa [← continuationHomotopy_eq_linearHomotopy, continuationHomotopy_eq_left_of_nonpos ha,
    continuationHomotopy_eq_right_of_one_le hb, smoothTransition.zero_of_nonpos ha,
    smoothTransition.one_of_one_le hb, sub_zero, one_mul] at hE

/-- **The capped action shift of a continuation cylinder.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_continuationHomotopy_le`, if
`u` solves the Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` for the continuation homotopy
on `[a, b] × [0, 1]`, with almost complex structures `J z` on `T_{u z} M` tamed by `ω`, then
`A_{H₁}(γ_b, v) ≤ A_{H₀}(γ_a, w # v) + ∫₀¹ h`: the capped action at the `H₁` end exceeds the
capped action at the `H₀` end, with the cap carried along the cylinder, by at most `∫₀¹ h`. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_of_continuationHomotopy
    (hω : ω.IsNondegenerate) (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (ha : a ≤ 0) (hb : 1 ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0)
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t)
    (hhi : IntegrableOn h (Icc 0 1)) :
    cylinderAction ω.1 H₁ v ≤
      cylinderAction ω.1 H₀ (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        ∫ t in Icc 0 1, h t := by
  have hE := hω.integral_floerEnergyDensity_continuationHomotopy_le hH₀ hH₁ hu ha hb hv hv₀ hh hhi
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := continuationHomotopy H₀ H₁)
      (hJ z hz) (hfloer z hz)
  linarith

end SmoothTwoForm

end TauCeti
