/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import TauCeti.Geometry.Manifold.MFDeriv.IntervalIntegral

/-!
# The first variation of the action functional on contractible loops

Let `ω` be a continuous weakly exact two-form on a manifold `M` and `H : ℝ → M → ℝ` a
time-dependent Hamiltonian, jointly `C¹` on `ℝ × M`. A **variation** of loops is a `C²` map
`u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, read as the family of loops
`γ_s = u(s, ·)`. If the loop `γ_{s₀}` has a cap, the action `A_H(γ_s)` of
`TauCeti.contractibleLoopAction` is differentiable in `s` at `s₀`, with derivative

`d/ds A_H(γ_s) = ∫₀¹ ω(∂_t u, ∂_s u) - d(H t)(∂_s u) dt`

(`TauCeti.IsWeaklyExact.hasDerivAt_contractibleLoopAction`). This is the **first variation
formula** of the action functional. For a weakly exact smooth two-form `σ` and a Hamiltonian
vector field `X t` of `H t`, that is `ι_{X t} σ = d(H t)`, it takes the form

`d/ds A_H(γ_s) = ∫₀¹ σ(γ_s' - X_t(γ_s), ∂_s u) dt`

(`TauCeti.SmoothTwoForm.hasDerivAt_contractibleLoopAction_of_isHamiltonianVectorField`). In
particular the `1`-periodic orbits of `X`, the loops with `γ' = X_t(γ)`, are critical points of the
action functional: every variation through such a loop has derivative `0` there
(`TauCeti.SmoothTwoForm.hasDerivAt_contractibleLoopAction_of_mem_periodicSolutions`). These are the
generators of the Hamiltonian Floer complex, and the sign conventions are those of
`TauCeti.contractibleLoopAction` and `TauCeti.SmoothTwoForm.IsHamiltonianVectorField`. The
converse, that for a nondegenerate form every critical loop is a `1`-periodic orbit, needs
variations with a prescribed variation field and is not proved here.

The proof joins the loops `γ_a` and `γ_b` of the variation by the cylinder
`(σ, t) ↦ u(a + σ (b - a), t)` (`TauCeti.isLoopCylinder_comp_prodMap_lineMap`). Gluing it to a cap
of `γ_a` caps `γ_b`, and the cap areas differ by the integral of `ω` over `u` on the rectangle
`[a, b] × [0, 1]` (`TauCeti.IsWeaklyExact.capArea_eq_sub_rectangleIntegral`). Its derivative in
`b` is the integral of `ω(∂_s u, ∂_t u)` along the loop `γ_b`
(`TauCeti.hasDerivAt_rectangleIntegral`), and the Hamiltonian term is differentiated under the
integral sign (`TauCeti.Manifold.hasDerivAt_intervalIntegral_comp`).

## Main results

* `TauCeti.isLoopCylinder_comp_prodMap_lineMap`: two loops of a variation are joined by a
  cylinder.
* `TauCeti.IsWeaklyExact.capArea_eq_sub_rectangleIntegral`: the cap areas along a variation.
* `TauCeti.IsWeaklyExact.hasDerivAt_contractibleLoopAction`: the first variation formula.
* `TauCeti.SmoothTwoForm.hasDerivAt_contractibleLoopAction_of_isHamiltonianVectorField`: the first
  variation formula in terms of a Hamiltonian vector field.
* `TauCeti.SmoothTwoForm.hasDerivAt_contractibleLoopAction_of_mem_periodicSolutions`: the
  `1`-periodic orbits are critical points of the action functional.

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

open scoped Manifold Interval

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Cylinders between the loops of a variation -/

variable (I) in
/-- Two loops `u(a, ·)` and `u(b, ·)` of a `C²` family of loops `u` are joined by the cylinder
`(σ, t) ↦ u(a + σ (b - a), t)`. -/
theorem isLoopCylinder_comp_prodMap_lineMap {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) (a b : ℝ) :
    IsLoopCylinder I (u ∘ Prod.map (AffineMap.lineMap a b) id) (fun t ↦ u (a, t))
      fun t ↦ u (b, t) where
  contMDiff := by
    have hl : (AffineMap.lineMap a b : ℝ → ℝ) = fun c ↦ c * (b - a) + a :=
      funext (AffineMap.lineMap_apply_ring' a b)
    refine hu.comp (ContDiff.contMDiff ?_)
    rw [hl]
    fun_prop
  apply_add_one z := hper (AffineMap.lineMap a b z.1, z.2)
  apply_zero t := by simp
  apply_one t := by simp

section Continuous

variable [IsManifold I 1 M] {ω : RoughForm I M ℝ 2} {u : ℝ × ℝ → M}

/-- **The cap areas along a variation.** For a continuous weakly exact form `ω` and a `C²` family
of loops `u` whose loop `u(a, ·)` has a cap, the cap area of `u(b, ·)` is that of `u(a, ·)` minus
the integral of `ω` over `u` on the rectangle `[a, b] × [0, 1]`. The loop `u(b, ·)` is capped by
gluing the cylinder `TauCeti.isLoopCylinder_comp_prodMap_lineMap` to the cap of `u(a, ·)`. -/
theorem IsWeaklyExact.capArea_eq_sub_rectangleIntegral (hω : IsSmoothForm I 0 ω)
    (hw : IsWeaklyExact ω) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (a, t)) :
    capArea ω (fun t ↦ u (b, t)) =
      capArea ω (fun t ↦ u (a, t)) - rectangleIntegral ω u (a, 0) (b, 1) := by
  rw [hw.capArea_eq_rectangleIntegral_add hω
      (isLoopCylinder_comp_prodMap_lineMap I hu hper b a) hv,
    rectangleIntegral_comp_prodMap hω (hu.of_le one_le_two)
      (fun _ _ ↦ AffineMap.hasDerivAt_lineMap) continuousOn_const]
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  rw [rectangleIntegral_symm_fst]
  ring

end Continuous

/-! ### The first variation formula -/

section FirstVariation

variable [IsManifold I 1 M] {ω : RoughForm I M ℝ 2} {u : ℝ × ℝ → M} {Ham : ℝ → M → ℝ}

/-- **The first variation formula of the action functional.** Let `ω` be a continuous weakly
exact two-form, `H` a Hamiltonian that is jointly `C¹` on `ℝ × M`, and `u` a `C²` family of loops
whose loop `u(s₀, ·)` has a cap. Then the action of the loops `u(s, ·)` is differentiable at
`s₀`, with derivative `∫₀¹ ω(∂_t u, ∂_s u) - d(H t)(∂_s u) dt` along the loop `u(s₀, ·)`. -/
theorem IsWeaklyExact.hasDerivAt_contractibleLoopAction (hω : IsSmoothForm I 0 ω)
    (hw : IsWeaklyExact ω) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (Function.uncurry Ham))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {s₀ : ℝ}
    {v : ℝ × ℝ → M} (hv : IsCap I v fun t ↦ u (s₀, t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction ω Ham fun t ↦ u (s, t))
      (∫ t in 0..1, (ω (u (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0)] -
        mvfderiv I (Ham t) (u (s₀, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0)))) s₀ := by
  have hu₁ := hu.of_le one_le_two
  have hA := (hasDerivAt_rectangleIntegral hω hu₁ (s₀, 0) 1 s₀).neg.sub
    (Manifold.hasDerivAt_intervalIntegral_comp hH hu₁ 0 1 s₀)
  have hfun : (fun s ↦ contractibleLoopAction ω Ham fun t ↦ u (s, t)) =
      fun s ↦ capArea ω (fun t ↦ u (s₀, t)) +
        (-rectangleIntegral ω u (s₀, 0) (s, 1) - ∫ t in 0..1, Ham t (u (s, t))) := by
    funext s
    rw [contractibleLoopAction_def,
      hw.capArea_eq_sub_rectangleIntegral hω hu hper (b := s) hv]
    ring
  rw [hfun]
  refine (hA.const_add _).congr_deriv ?_
  -- Both integrands are continuous along the loop, so the integrals combine.
  have hline : Continuous fun t : ℝ ↦ (s₀, t) := continuous_const.prodMk continuous_id
  have hint₁ : IntervalIntegrable (fun t ↦ -ω (u (s₀, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1)])
      MeasureTheory.volume 0 1 :=
    ((hω.continuous_apply_mfderiv hu₁).comp hline).intervalIntegrable 0 1 |>.neg
  have hint₂ : IntervalIntegrable (fun t ↦ mvfderiv I (Ham t) (u (s₀, t))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0))) MeasureTheory.volume 0 1 :=
    ((Manifold.continuous_mvfderiv_apply_mfderiv hH hu₁).comp hline).intervalIntegrable 0 1
  dsimp only
  rw [← intervalIntegral.integral_neg]
  refine (intervalIntegral.integral_sub hint₁ hint₂).symm.trans ?_
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [sub_left_inj]
  simpa using ((ω (u (s₀, t))).map_swap ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0),
    mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1)] (i := 0) (j := 1) Fin.zero_ne_one).symm

end FirstVariation

/-! ### The first variation in terms of the Hamiltonian vector field -/

namespace SmoothTwoForm

variable [IsManifold I (⊤ : ℕ∞) M] {σ : SmoothTwoForm I M} {Ham : ℝ → M → ℝ}
  {X : ℝ → (x : M) → TangentSpace I x} {u : ℝ × ℝ → M}

/-- **The first variation formula, with the Hamiltonian vector field.** If `X t` is a Hamiltonian
vector field of `H t` for a weakly exact smooth two-form `σ`, `ι_{X t} σ = d(H t)`, then along a
`C²` family of loops `u` whose loop `γ = u(s₀, ·)` has a cap, the derivative of the action at
`s₀` is `∫₀¹ σ(γ' - X_t(γ), ∂_s u) dt`. -/
theorem hasDerivAt_contractibleLoopAction_of_isHamiltonianVectorField (hw : IsWeaklyExact σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (Function.uncurry Ham))
    (hX : ∀ t, σ.IsHamiltonianVectorField (Ham t) (X t)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {s₀ : ℝ} {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (s₀, t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.1 Ham fun t ↦ u (s, t))
      (∫ t in 0..1, σ.eval₂ (u (s₀, t))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1) - X t (u (s₀, t)))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0))) s₀ := by
  refine (hw.hasDerivAt_contractibleLoopAction (σ.isSmoothForm.of_le (by simp)) hH hu hper
    hv).congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  have h₁ := isHamiltonianVectorField_iff.mp (hX t) (u (s₀, t))
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0))
  have h₂ := (σ.bilinFormAt (u (s₀, t))).map_sub₂ (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1))
    (X t (u (s₀, t))) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0))
  simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply] at h₁ h₂ ⊢
  rw [h₂, h₁]

/-- **The `1`-periodic orbits are critical points of the action functional.** If `X t` is a
Hamiltonian vector field of `H t` for a weakly exact smooth two-form `σ` and the loop
`u(s₀, ·)` of a `C²` family of loops `u` is a `1`-periodic solution of `X` with a cap, then the
derivative of the action along the family vanishes at `s₀`. -/
theorem hasDerivAt_contractibleLoopAction_of_mem_periodicSolutions (hw : IsWeaklyExact σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (Function.uncurry Ham))
    (hX : ∀ t, σ.IsHamiltonianVectorField (Ham t) (X t)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {s₀ : ℝ}
    (hγ : (fun t ↦ u (s₀, t)) ∈ periodicSolutions X 1) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (s₀, t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.1 Ham fun t ↦ u (s, t)) 0 s₀ := by
  refine (hasDerivAt_contractibleLoopAction_of_isHamiltonianVectorField hw hH hX hu hper
    hv).congr_deriv ?_
  -- Along the orbit, `∂_t u = X_t(u)`, so the integrand vanishes.
  have hder (t : ℝ) : mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1) = X t (u (s₀, t)) :=
    (Manifold.curveVelocity_eq_mfderiv_snd (f := fun s t ↦ u (s, t))
      ((hu (s₀, t)).mdifferentiableAt two_ne_zero)).symm.trans <| by
      rw [← Manifold.curveVelocityWithin_univ]
      exact Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
        ((mem_periodicSolutions.mp hγ).1 t).hasMFDerivWithinAt uniqueDiffWithinAt_univ
  refine (intervalIntegral.integral_congr fun t _ ↦ ?_).trans intervalIntegral.integral_zero
  rw [hder t, sub_self, ← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply]

end SmoothTwoForm

end TauCeti
