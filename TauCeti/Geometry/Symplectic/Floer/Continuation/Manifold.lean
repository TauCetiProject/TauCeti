/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation
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
`R_K = ∂_s H = β'(s) (H₁ - H₀)(t)` (`TauCeti.SmoothTwoForm.hamiltonianCurvature_linearHomotopy`).

The energy identity for a family of Hamiltonians on a manifold target
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_zero_left_eq_cylinderAction_sub`)
measures the Floer energy of `u` over `[a, b] × [0, 1]` against the capped action
`A_H(γ, v) = ∫ v^* ω - ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cylinderAction`). Write `γ_a = u(a, ·)` and
`γ_b = u(b, ·)`, let `v` be a map with `v(0, ·) = γ_b` (a cap of `γ_b`), and let `w # v` be the
cap of `γ_a` obtained by gluing `u|_{[a, b]}` to `v`. If `H₀ - H₁ ≤ B` along `u`, then

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
vector space target, without caps, are in `TauCeti.Geometry.Symplectic.Floer.Continuation`.

The existence, compactness and counting of continuation cylinders are not treated here.

## Main results

* `TauCeti.Floer.contMDiff_uncurry_linearHomotopy`: the linear homotopy of `C^n` Hamiltonians
  on a manifold with a `C^n` profile is `C^n`.
* `TauCeti.SmoothTwoForm.hamiltonianCurvature_linearHomotopy`: its curvature is
  `β'(s) (H₁ - H₀)(t)`.
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

namespace Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] {H₀ H₁ : ℝ → M → ℝ}

/-- The linear homotopy of two `Cⁿ` time-dependent Hamiltonians on a manifold with a `Cⁿ` profile
is `Cⁿ`. -/
theorem contMDiff_uncurry_linearHomotopy {n : ℕ∞} {β : ℝ → ℝ} (hβ : ContDiff ℝ n β)
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H₁)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n (uncurry (linearHomotopy β H₀ H₁)) := by
  have hp : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod I) n
      fun p : (ℝ × ℝ) × M ↦ (p.1.2, p.2) :=
    (contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hβ' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n fun p : (ℝ × ℝ) × M ↦ β p.1.1 :=
    (hβ.comp contDiff_fst).contMDiff.comp contMDiff_fst
  have h := (hH₀.comp hp).add (hβ'.smul ((hH₁.comp hp).sub (hH₀.comp hp)))
  exact h.congr fun p ↦ (linearHomotopy_def β p.1 p.2).trans (by simp only [smul_eq_mul]; rfl)

/-- The continuation homotopy of two `Cⁿ` time-dependent Hamiltonians on a manifold is `Cⁿ`. -/
theorem contMDiff_uncurry_continuationHomotopy {n : ℕ∞}
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H₁)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n (uncurry (continuationHomotopy H₀ H₁)) := by
  rw [continuationHomotopy_eq_linearHomotopy]
  exact contMDiff_uncurry_linearHomotopy smoothTransition.contDiff hH₀ hH₁

end Floer

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H₀ H₁ : ℝ → M → ℝ} {u v : ℝ × ℝ → M}
  {a b : ℝ}

/-- **The curvature of a linear homotopy.** The perturbation `K = H_{(s, t)} dt` of the linear
homotopy `H = H₀ + β(s) (H₁ - H₀)` has curvature `β'(s) (H₁ - H₀)(t)`. -/
theorem hamiltonianCurvature_linearHomotopy (ω : SmoothTwoForm I M) {β : ℝ → ℝ} {z : ℝ × ℝ}
    {x : M} (hβ : DifferentiableAt ℝ β z.1) (hH₀ : DifferentiableAt ℝ (fun t ↦ H₀ t x) z.2)
    (hH₁ : DifferentiableAt ℝ (fun t ↦ H₁ t x) z.2) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (linearHomotopy β H₀ H₁) z x =
      deriv β z.1 * (H₁ z.2 x - H₀ z.2 x) := by
  rw [hamiltonianCurvature_zero_left, fderiv_linearHomotopy_stdComplexLineReal hβ hH₀ hH₁]

/-- **The curvature of the continuation homotopy.** The perturbation `K = H_{(s, t)} dt` of the
continuation homotopy has curvature `β'(s) (H₁ - H₀)(t)` for the profile
`β = Real.smoothTransition`. -/
theorem hamiltonianCurvature_continuationHomotopy (ω : SmoothTwoForm I M) {z : ℝ × ℝ} {x : M}
    (hH₀ : DifferentiableAt ℝ (fun t ↦ H₀ t x) z.2)
    (hH₁ : DifferentiableAt ℝ (fun t ↦ H₁ t x) z.2) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) z x =
      deriv smoothTransition z.1 * (H₁ z.2 x - H₀ z.2 x) := by
  rw [hamiltonianCurvature_zero_left, fderiv_continuationHomotopy_stdComplexLineReal hH₀ hH₁]

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
  have hK := contMDiff_uncurry_linearHomotopy hβ hH₀ hH₁
  rw [hω.integral_floerEnergyDensity_zero_left_eq_cylinderAction_sub hK hu hab hv hv₀]
  -- It remains to bound `-∫ ∂_s H(u) = ∫ β'(s) (H₀ - H₁)(t, u)` by `(β(b) - β(a)) ∫ B`.
  have hfi : IntegrableOn
      (fun z ↦ ω.hamiltonianCurvature (fun _ _ ↦ 0) (linearHomotopy β H₀ H₁) z (u z))
      (Icc a b ×ˢ Icc 0 1) :=
    (continuous_hamiltonianCurvature_zero_left_comp hK hu).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hd {G : ℝ → M → ℝ} (hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (x : M) :
      Differentiable ℝ fun t ↦ G t x :=
    (contMDiff_iff_contDiff.mp (hG.comp (contMDiff_id.prodMk contMDiff_const))).differentiable
      one_ne_zero
  have hle := neg_mul_setIntegral_le_setIntegral hβ hab hB hfi fun z hz ↦ by
    rw [ω.hamiltonianCurvature_linearHomotopy (hβ.differentiable one_ne_zero z.1) (hd hH₀ _ _)
      (hd hH₁ _ _)]
    have := mul_le_mul_of_nonneg_left (hHB z hz) (hβm.deriv_nonneg (x := z.1))
    linarith
  linarith

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
  -- At the two ends the homotopy is `H₀` and `H₁`.
  have hA : (fun t ↦ continuationHomotopy H₀ H₁ (a, t)) = H₀ :=
    funext fun t ↦ funext (continuationHomotopy_of_nonpos (z := (a, t)) ha)
  have hB : (fun t ↦ continuationHomotopy H₀ H₁ (b, t)) = H₁ :=
    funext fun t ↦ funext (continuationHomotopy_of_one_le (z := (b, t)) hb)
  rwa [← continuationHomotopy_eq_linearHomotopy, hA, hB, smoothTransition.zero_of_nonpos ha,
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
