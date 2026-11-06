/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The first variation of the action functional on contractible loops

Let `ω` be a continuous weakly exact two-form on a manifold `M` (`TauCeti.IsWeaklyExact`, the
area half of symplectic asphericity) and `H : ℝ → M → ℝ` a `C¹` time-dependent Hamiltonian. The
action of a loop `γ` with a cap is `A_H(γ) = ∫ u^* ω - ∫₀¹ H(t, γ(t)) dt`
(`TauCeti.contractibleLoopAction`), the cap `u` running from `γ` to its centre.

A **variation of loops** is a `C²` map `Γ : ℝ × ℝ → M`, `1`-periodic in its second coordinate
`t`; its loops are `γ_s = Γ(s, ·)`, and its variation field along `γ_s` is `∂_s Γ(s, ·)`. This
file computes the derivative of `s ↦ A_H(γ_s)`, the **first variation formula**

`d/ds A_H(γ_s) = ∫₀¹ (ω(∂_t Γ, ∂_s Γ) - dH_t(∂_s Γ)) dt`

(`TauCeti.IsWeaklyExact.hasDerivAt_contractibleLoopAction`), as soon as one loop of the family
has a cap. For a nondegenerate form on a finite-dimensional manifold, with the convention
`ι_{X_H} ω = dH` for Hamiltonian vector fields, this reads

`d/ds A_H(γ_s) = ∫₀¹ ω(∂_t Γ - X_{H_t}(Γ), ∂_s Γ) dt`

(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`). In particular the
`1`-periodic orbits of `X_H` are critical points of the action functional: the derivative vanishes
along every variation through such an orbit
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_zero`). This is the
variational principle behind Hamiltonian Floer theory, whose generators are the `1`-periodic
orbits.

The area term is handled globally, not only to first order: the cap area of `γ_b` is the cap
area of `γ_a` minus the integral of `ω` over the rectangle `[a, b] × [0, 1]` of the variation
(`TauCeti.IsWeaklyExact.capArea_eq_sub_rectangleIntegral`), because the restriction of the
variation to `[b, a]` is a cylinder from `γ_b` to `γ_a`. The fundamental theorem of calculus
then differentiates the area term, and differentiation under the integral sign the Hamiltonian
term (`TauCeti.hasDerivAt_intervalIntegral_apply_comp`).

## Main results

* `TauCeti.IsWeaklyExact.capArea_eq_sub_rectangleIntegral`: the change of the cap area along a
  variation of loops.
* `TauCeti.IsWeaklyExact.hasDerivAt_capArea`: the first variation of the cap area.
* `TauCeti.IsWeaklyExact.hasDerivAt_contractibleLoopAction`: the first variation formula for the
  action of contractible loops.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`: the first variation
  formula in terms of the Hamiltonian vector field.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_zero`: `1`-periodic
  orbits are critical points of the action.

## References

* H. Hofer and E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (the action functional on loops and its critical points).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the first variation of the symplectic action).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
-/

public section

noncomputable section

open Function
open scoped Manifold Interval

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The Hamiltonian term -/

section Hamiltonian

variable {H : ℝ → M → ℝ} {Γ : ℝ × ℝ → M}

/-- The function `(s, t) ↦ H t (Γ (s, t))` is `C¹`. -/
private theorem contDiff_apply_comp (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 Γ) : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ H w.2 (Γ w) :=
  contMDiff_iff_contDiff.mp (hH.comp (contDiff_snd.contMDiff.prodMk hΓ))

/-- The partial derivative in `s` of `(s, t) ↦ H t (Γ (s, t))` is the differential of `H t`
applied to the partial derivative `∂_s Γ`. -/
private theorem fderiv_apply_comp_apply_one_zero
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 Γ)
    (z : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ ↦ H w.2 (Γ w)) z (1, 0) =
      mvfderiv I (H z.2) (Γ z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ z (1, 0)) := by
  obtain ⟨s, t⟩ := z
  have hG := contDiff_apply_comp hH hΓ
  -- Along the line `s ↦ (s, t)`, the function is `H t` composed with the curve `s ↦ Γ (s, t)`.
  have hl : HasDerivAt (fun r : ℝ ↦ (r, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  have h₁ : HasDerivAt ((fun w : ℝ × ℝ ↦ H w.2 (Γ w)) ∘ fun r ↦ (r, t))
      (fderiv ℝ (fun w : ℝ × ℝ ↦ H w.2 (Γ w)) (s, t) (1, 0)) s :=
    ((hG.differentiable one_ne_zero (s, t)).hasFDerivAt).comp_hasDerivAt s hl
  have hHt : MDifferentiableAt I 𝓘(ℝ) (H t) (Γ (s, t)) :=
    ((hH.comp (contMDiff_const.prodMk contMDiff_id) :
      ContMDiff I 𝓘(ℝ) 1 (H t)) (Γ (s, t))).mdifferentiableAt one_ne_zero
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r ↦ Γ (r, t)) s :=
    ((hΓ.comp (contDiff_id.prodMk contDiff_const).contMDiff :
      ContMDiff 𝓘(ℝ, ℝ) I 1 fun r ↦ Γ (r, t)) s).mdifferentiableAt one_ne_zero
  have h₂ := Manifold.hasDerivAt_comp_curve hHt (Manifold.hasMFDerivAt_curveVelocity hcurve)
  rw [Manifold.curveVelocity_eq_mfderiv_fst (f := fun a b ↦ Γ (a, b))
    ((hΓ (s, t)).mdifferentiableAt one_ne_zero)] at h₂
  exact h₁.unique h₂

/-- **Differentiation of the Hamiltonian term along a family of curves.** For a `C¹`
time-dependent function `H` and a `C¹` map `Γ` of the plane, the derivative of
`s ↦ ∫_a^b H(t, Γ(s, t)) dt` is the integral of `dH_t(∂_s Γ)`. -/
theorem hasDerivAt_intervalIntegral_apply_comp
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 Γ)
    (a b s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, H t (Γ (s, t)))
      (∫ t in a..b, mvfderiv I (H t) (Γ (s₀, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)))
      s₀ := by
  have hG := contDiff_apply_comp hH hΓ
  have h := (hasDerivAt_intervalIntegral_of_contDiffOn isOpen_univ hG.contDiffOn
    (x₀ := s₀) (a := a) (b := b) (Set.subset_univ _)).2
  simpa only [fderiv_apply_comp_apply_one_zero hH hΓ] using h

/-- The integrand `dH_t(∂_s Γ)` of the variation of the Hamiltonian term is continuous. -/
private theorem continuous_mvfderiv_apply_comp
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 Γ) :
    Continuous fun z : ℝ × ℝ ↦ mvfderiv I (H z.2) (Γ z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ z (1, 0)) := by
  have hG := contDiff_apply_comp hH hΓ
  exact ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).congr
    (fderiv_apply_comp_apply_one_zero hH hΓ)

end Hamiltonian

/-! ### The area term -/

section Area

variable [IsManifold I 1 M] {φ : RoughForm I M F 2} {Γ : ℝ × ℝ → M}

omit [IsManifold I 1 M] in
/-- The restriction of a `C²` family of loops `Γ` to the parameters between `b` and `a`,
reparametrized affinely by `[0, 1]`, is a cylinder from the loop at `b` to the loop at `a`. -/
private theorem isLoopCylinder_comp_prodMap (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 Γ)
    (hper : ∀ z : ℝ × ℝ, Γ (z.1, z.2 + 1) = Γ z) (a b : ℝ) :
    IsLoopCylinder I (Γ ∘ Prod.map (fun s ↦ b + s * (a - b)) id) (fun t ↦ Γ (b, t))
      (fun t ↦ Γ (a, t)) where
  contMDiff := hΓ.comp
    (((contDiff_const.add (contDiff_id.mul contDiff_const)).prodMap contDiff_id).contMDiff)
  apply_add_one z := hper (b + z.1 * (a - b), z.2)
  apply_zero t := by simp
  apply_one t := by simp

/-- **The cap area along a variation of loops.** Let `Γ` be a `C²` family of loops, `1`-periodic
in its second coordinate, whose loop at the parameter `a` has a cap. For a continuous weakly exact
form `φ`, the cap area of the loop at any parameter `b` is that of the loop at `a`, minus the
integral of `φ` over `Γ` on the rectangle `[a, b] × [0, 1]`. -/
theorem IsWeaklyExact.capArea_eq_sub_rectangleIntegral (hφ : IsSmoothForm I 0 φ)
    (hw : IsWeaklyExact φ) (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 Γ)
    (hper : ∀ z : ℝ × ℝ, Γ (z.1, z.2 + 1) = Γ z) {a : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ Γ (a, t)) (b : ℝ) :
    capArea φ (fun t ↦ Γ (b, t)) =
      capArea φ (fun t ↦ Γ (a, t)) - rectangleIntegral φ Γ (a, 0) (b, 1) := by
  obtain ⟨u, hu⟩ := hcap
  rw [hw.capArea_eq_rectangleIntegral_add hφ (isLoopCylinder_comp_prodMap hΓ hper a b) hu,
    rectangleIntegral_comp_prodMap hφ (hΓ.of_le one_le_two) (σ' := fun _ ↦ a - b)
      (fun s _ ↦ by simpa using ((hasDerivAt_id s).mul_const (a - b)).const_add b)
      continuousOn_const]
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel]
  rw [rectangleIntegral_symm_fst]
  abel

/-- **The first variation of the cap area.** Let `Γ` be a `C²` family of loops, `1`-periodic in
its second coordinate, whose loop at `s₀` has a cap. For a continuous weakly exact form `φ`, the
derivative at `s₀` of the cap area of the loops `Γ(s, ·)` is `∫₀¹ φ(∂_t Γ, ∂_s Γ) dt`. -/
theorem IsWeaklyExact.hasDerivAt_capArea [CompleteSpace F] (hφ : IsSmoothForm I 0 φ)
    (hw : IsWeaklyExact φ)
    (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 Γ) (hper : ∀ z : ℝ × ℝ, Γ (z.1, z.2 + 1) = Γ z) {s₀ : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ Γ (s₀, t)) :
    HasDerivAt (fun s ↦ capArea φ fun t ↦ Γ (s, t))
      (∫ t in 0..1, φ (Γ (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)]) s₀ := by
  -- The area integrand `φ(∂_s Γ, ∂_t Γ)`, integrated in `t`, is continuous in `s`.
  set g : ℝ → F := fun s ↦ ∫ t in 0..1, φ (Γ (s, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s, t) (1, 0),
    mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s, t) (0, 1)] with hg_def
  have hg : Continuous g :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hφ.continuous_apply_mfderiv (hΓ.of_le one_le_two)) 0 1
  have hfun : (fun s ↦ capArea φ fun t ↦ Γ (s, t)) =
      fun s ↦ capArea φ (fun t ↦ Γ (s₀, t)) - ∫ r in s₀..s, g r := by
    funext s
    rw [hw.capArea_eq_sub_rectangleIntegral hφ hΓ hper hcap s, rectangleIntegral_eq]
  have hswap (t : ℝ) : φ (Γ (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)] =
      -φ (Γ (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1)] := by
    simpa using (φ (Γ (s₀, t))).map_swap ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1)] (i := 0) (j := 1) Fin.zero_ne_one
  rw [hfun, intervalIntegral.integral_congr fun t _ ↦ hswap t, intervalIntegral.integral_neg,
    ← zero_sub]
  exact (hasDerivAt_const s₀ _).sub (hg.integral_hasStrictDerivAt s₀ s₀).hasDerivAt

end Area

/-! ### The first variation of the action -/

section Action

variable [IsManifold I 1 M] {ω : RoughForm I M ℝ 2} {H : ℝ → M → ℝ} {Γ : ℝ × ℝ → M}

/-- **The first variation formula** for the action of contractible loops. Let `ω` be a continuous
weakly exact two-form, `H` a `C¹` time-dependent Hamiltonian and `Γ` a `C²` family of loops,
`1`-periodic in its second coordinate, whose loop at `s₀` has a cap. The derivative at `s₀` of the
action of the loops `Γ(s, ·)` is

`∫₀¹ (ω(∂_t Γ, ∂_s Γ) - dH_t(∂_s Γ)) dt`. -/
theorem IsWeaklyExact.hasDerivAt_contractibleLoopAction (hω : IsSmoothForm I 0 ω)
    (hw : IsWeaklyExact ω) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 Γ) (hper : ∀ z : ℝ × ℝ, Γ (z.1, z.2 + 1) = Γ z) {s₀ : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ Γ (s₀, t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction ω H fun t ↦ Γ (s, t))
      (∫ t in 0..1, (ω (Γ (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)] -
          mvfderiv I (H t) (Γ (s₀, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)))) s₀ := by
  -- Both integrands are continuous in `t`.
  have harea : Continuous fun t ↦ ω (Γ (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)] := by
    have h := (hω.continuous_apply_mfderiv (hΓ.of_le one_le_two)).comp
      (continuous_const.prodMk continuous_id : Continuous fun t : ℝ ↦ (s₀, t))
    refine h.neg.congr fun t ↦ ?_
    simpa using ((ω (Γ (s₀, t))).map_swap ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1)] (i := 0) (j := 1) Fin.zero_ne_one).symm
  have hham : Continuous fun t ↦
      mvfderiv I (H t) (Γ (s₀, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)) :=
    (continuous_mvfderiv_apply_comp hH (hΓ.of_le one_le_two)).comp
      (continuous_const.prodMk continuous_id : Continuous fun t : ℝ ↦ (s₀, t))
  have hfun : (fun s ↦ contractibleLoopAction ω H fun t ↦ Γ (s, t)) =
      fun s ↦ (capArea ω fun t ↦ Γ (s, t)) - ∫ t in 0..1, H t (Γ (s, t)) :=
    funext fun s ↦ contractibleLoopAction_def ω H _
  rw [hfun, intervalIntegral.integral_sub (harea.intervalIntegrable 0 1)
    (hham.intervalIntegrable 0 1)]
  exact (hw.hasDerivAt_capArea hω hΓ hper hcap).sub
    (hasDerivAt_intervalIntegral_apply_comp hH (hΓ.of_le one_le_two) 0 1 s₀)

end Action

namespace SmoothTwoForm

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {Γ : ℝ × ℝ → M}

/-- **The first variation formula with the Hamiltonian vector field.** Let `ω` be a nondegenerate
weakly exact two-form on a finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian
and `Γ` a `C²` family of loops, `1`-periodic in its second coordinate, whose loop at `s₀` has a
cap. The derivative at `s₀` of the action of the loops `Γ(s, ·)` is

`∫₀¹ ω(∂_t Γ - X_{H_t}(Γ), ∂_s Γ) dt`,

for the Hamiltonian vector fields `X_{H_t}` of the convention `ι_{X_{H_t}} ω = dH_t`. -/
theorem IsNondegenerate.hasDerivAt_contractibleLoopAction (hnd : ω.IsNondegenerate)
    (hw : IsWeaklyExact ω.1) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 Γ) (hper : ∀ z : ℝ × ℝ, Γ (z.1, z.2 + 1) = Γ z) {s₀ : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ Γ (s₀, t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction ω.1 H fun t ↦ Γ (s, t))
      (∫ t in 0..1, ω.1 (Γ (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1) - ω.hamiltonianVectorField (H t) (Γ (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (1, 0)]) s₀ := by
  have hω : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  refine (hw.hasDerivAt_contractibleLoopAction hω hH hΓ hper hcap).congr_deriv
    (intervalIntegral.integral_congr fun t _ ↦ ?_)
  simp only [← SmoothBundleForm.eval₂_apply, sub_eq_add_neg, SmoothBundleForm.eval₂_add_left,
    SmoothBundleForm.eval₂_neg_left, hnd.eval₂_hamiltonianVectorField]

/-- **One-periodic orbits are critical points of the action.** Let `ω` be a nondegenerate weakly
exact two-form on a finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian and `Γ` a
`C²` family of loops, `1`-periodic in its second coordinate, whose loop at `s₀` has a cap and is a
`1`-periodic orbit of the Hamiltonian vector field `X_{H_t}`. Then the action of the loops
`Γ(s, ·)` has derivative `0` at `s₀`. -/
theorem IsNondegenerate.hasDerivAt_contractibleLoopAction_zero (hnd : ω.IsNondegenerate)
    (hw : IsWeaklyExact ω.1) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hΓ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 Γ) (hper : ∀ z : ℝ × ℝ, Γ (z.1, z.2 + 1) = Γ z) {s₀ : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ Γ (s₀, t))
    (horbit : (fun t ↦ Γ (s₀, t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1) :
    HasDerivAt (fun s ↦ contractibleLoopAction ω.1 H fun t ↦ Γ (s, t)) 0 s₀ := by
  refine (hnd.hasDerivAt_contractibleLoopAction hw hH hΓ hper hcap).congr_deriv
    ((intervalIntegral.integral_congr fun t _ ↦ ?_).trans intervalIntegral.integral_zero)
  -- Along an orbit, the velocity `∂_t Γ` is the Hamiltonian vector field.
  have hvel : mfderiv 𝓘(ℝ, ℝ × ℝ) I Γ (s₀, t) (0, 1) =
      ω.hamiltonianVectorField (H t) (Γ (s₀, t)) := by
    rw [← Manifold.curveVelocity_eq_mfderiv_snd (f := fun a b ↦ Γ (a, b))
      ((hΓ (s₀, t)).mdifferentiableAt two_ne_zero), ← Manifold.curveVelocityWithin_univ]
    exact Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
      ((mem_periodicSolutions.mp horbit).1 t).hasMFDerivWithinAt uniqueDiffWithinAt_univ
  rw [hvel, sub_self]
  exact (ω.1 _).map_coord_zero 0 rfl

end SmoothTwoForm

end TauCeti
