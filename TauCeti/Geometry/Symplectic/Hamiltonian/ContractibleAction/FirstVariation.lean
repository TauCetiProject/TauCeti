/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation

/-!
# The first variation of the action functional and its critical loops

Let `σ` be a continuous weakly exact two-form on a manifold `M` and `H : ℝ → M → ℝ` a
time-dependent Hamiltonian. A **variation through loops** is a `C²` map `w : ℝ × ℝ → M`,
`1`-periodic in its second coordinate `t`; its loops are `γ_s = w (s, ·)`. This file computes the
derivative in `s` of the action `A_H(γ_s)` of `TauCeti.contractibleLoopAction`, when the loops have
caps.

* The cap area changes by the area swept by the variation, so
  `d/ds capArea σ γ_s = -∫₀¹ σ(∂_s w, ∂_t w) dt` (`TauCeti.IsWeaklyExact.hasDerivAt_capArea`).
* Differentiating under the integral sign,
  `d/ds ∫₀¹ H(t, γ_s(t)) dt = ∫₀¹ dH_t(∂_s w) dt` for a jointly `C¹` Hamiltonian
  (`TauCeti.Manifold.hasDerivAt_intervalIntegral_apply_comp`).
* For a nondegenerate `σ` with Hamiltonian vector fields `ι_{X_{H_t}} σ = dH_t`, the two combine
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_sub_intervalIntegral`) into the **first
  variation formula**
  `d/ds A_H(γ_s) = ∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`).

A loop `γ` is a **critical point of the action** (`TauCeti.IsContractibleLoopActionCritical`)
when it is a `C²` loop with a cap and the derivative at `s = 0` of `A_H(γ_s)` vanishes for every
variation through loops starting at `γ`. The first variation formula shows that the
`1`-periodic orbits of `X_H` are critical. Conversely, for a Hamiltonian which is `1`-periodic in
time, if `γ' ≠ X_H(γ)` at some time `t₀`, pushing `γ` near `t₀ + ℤ` in a chart direction `e` with
`σ(γ' - X_H, e) > 0` gives a variation along which the action has a nonzero derivative
(`TauCeti.SmoothTwoForm.IsNondegenerate.mem_periodicSolutions_of_forall_integral_eq_zero`).
Hence, on a manifold without boundary modelled on a finite-dimensional space, the critical loops
are exactly the `1`-periodic orbits of `X_H`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isContractibleLoopActionCritical_iff`). This is the
variational principle behind Hamiltonian Floer theory, whose generators are the `1`-periodic
orbits.

## Main definitions

* `TauCeti.IsContractibleLoopActionCritical σ H γ`: `γ` is a critical point of the contractible
  action functional.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`: the first variation
  formula.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isContractibleLoopActionCritical_iff`: the critical
  points of the action are the `1`-periodic orbits.

The variational argument shared with the action of loops relative to a reference loop is in
`TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation`.

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

open Function Set
open scoped Manifold Interval ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The variation of the cap area -/

section CapArea

variable [IsManifold I 1 M] [CompleteSpace F] {φ : RoughForm I M F 2} {w : ℝ × ℝ → M}

/-- **The first variation of the cap area.** For a continuous weakly exact form `φ` and a `C²`
variation `w` through loops whose loop `w (s₀, ·)` has a cap, the cap area of the loops
`w (s, ·)` has derivative `-∫₀¹ φ(∂_s w, ∂_t w) dt` at `s₀`: moving the loop sweeps out the area
of the variation. -/
theorem IsWeaklyExact.hasDerivAt_capArea (hφ : IsSmoothForm I 0 φ) (hw : IsWeaklyExact φ)
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w) (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z)
    {s₀ : ℝ} (hcap : ∃ u, IsCap I u fun t ↦ w (s₀, t)) :
    HasDerivAt (fun s ↦ capArea φ fun t ↦ w (s, t))
      (-∫ t in 0..1, φ (w (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1)]) s₀ := by
  obtain ⟨u, hu⟩ := hcap
  -- the cap area of `w (s, ·)` is the area swept from `s` to `s₀` plus that of `w (s₀, ·)`
  have heq : (fun s ↦ capArea φ fun t ↦ w (s, t)) = fun s ↦
      rectangleIntegral φ (w ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id) (0, 0) (1, 1) +
        capArea φ fun t ↦ w (s₀, t) :=
    funext fun s ↦
      hw.capArea_eq_rectangleIntegral_add hφ (isLoopCylinder_comp_prodMap hwc hper s s₀) hu
  rw [heq]
  exact (hasDerivAt_rectangleIntegral_comp_prodMap_affine hφ (hwc.of_le one_le_two) s₀ 0
    1).add_const _

end CapArea

/-! ### The first variation formula -/

section FirstVariation

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {w : ℝ × ℝ → M}

/-- **The first variation of the action functional.** Let `σ` be a nondegenerate weakly exact
two-form, `H` a jointly `C¹` time-dependent Hamiltonian and `w` a `C²` variation through loops,
`1`-periodic in `t`, whose loop `w (s₀, ·)` has a cap. Then the action of the loops `w (s, ·)` has
derivative `∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt` at `s₀`, with all terms taken at `(s₀, t)`. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction (h : σ.IsNondegenerate)
    (hw : IsWeaklyExact σ.1) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w) (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z)
    {s₀ : ℝ} (hcap : ∃ u, IsCap I u fun t ↦ w (s₀, t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.1 H fun t ↦ w (s, t))
      (∫ t in 0..1, σ.1 (w (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)]) s₀ := by
  simp only [contractibleLoopAction_def]
  exact h.hasDerivAt_sub_intervalIntegral hH (hwc.of_le one_le_two)
    (hw.hasDerivAt_capArea (σ.isSmoothForm.of_le (by simp)) hwc hper hcap)

end FirstVariation

/-! ### Critical loops of the action -/

/-- A loop `γ` is a **critical point of the contractible action** `A_H` of the two-form `φ` when
it is a `1`-periodic `C²` loop with a cap and, for every `C²` variation `w` through loops starting
at `γ`, the action `A_H(w (s, ·))` has derivative `0` at `s = 0`. -/
structure IsContractibleLoopActionCritical (φ : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ : ℝ → M) :
    Prop where
  /-- A critical loop is `C²`. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ) I 2 γ
  /-- A critical loop is `1`-periodic. -/
  apply_add_one : ∀ t, γ (t + 1) = γ t
  /-- A critical loop has a cap. -/
  exists_isCap : ∃ u, IsCap I u γ
  /-- The action is stationary along every variation through loops. -/
  hasDerivAt : ∀ ⦃w : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w →
    (∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) → (∀ t, w (0, t) = γ t) →
    HasDerivAt (fun s ↦ contractibleLoopAction φ H fun t ↦ w (s, t)) 0 0

section CriticalLoops

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {γ : ℝ → M}

/-- Along a `C²` variation through loops of a loop `γ` with a cap, the action of the loops has
at `s = 0` the derivative given by the first variation formula. -/
private theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_zero
    (h : σ.IsNondegenerate) (hw : IsWeaklyExact σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hcap : ∃ u, IsCap I u γ)
    {w : ℝ × ℝ → M} (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w)
    (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) (h0 : ∀ t, w (0, t) = γ t) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.1 H fun t ↦ w (s, t))
      (∫ t in 0..1, σ.1 (w (0, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)]) 0 :=
  h.hasDerivAt_contractibleLoopAction hw hH hwc hper (funext h0 ▸ hcap)

/-- **The `1`-periodic orbits are critical points of the action.** For a nondegenerate weakly
exact two-form and a jointly `C¹` Hamiltonian, a `C²` loop with a cap which is a `1`-periodic orbit
of `X_H` is a critical point of the contractible action. -/
theorem SmoothTwoForm.IsNondegenerate.isContractibleLoopActionCritical (h : σ.IsNondegenerate)
    (hw : IsWeaklyExact σ.1) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (hcap : ∃ u, IsCap I u γ)
    (horbit : γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1) :
    IsContractibleLoopActionCritical σ.1 H γ where
  contMDiff := hγ
  apply_add_one := (mem_periodicSolutions.mp horbit).2
  exists_isCap := hcap
  hasDerivAt w hwc hper h0 := by
    convert h.hasDerivAt_contractibleLoopAction_zero hw hH hcap hwc hper h0 using 1
    exact (σ.intervalIntegral_apply_sub_hamiltonianVectorField_eq_zero horbit
      (fun t ↦ (hwc (0, t)).mdifferentiableAt two_ne_zero) h0 0 1).symm

/-- **Critical points of the action are `1`-periodic orbits.** Let `σ` be a nondegenerate weakly
exact two-form on a manifold without boundary modelled on a finite-dimensional space, and `H` a
jointly `C¹` Hamiltonian, `1`-periodic in time. Then a critical point of the contractible action
is a `1`-periodic orbit of `X_H`. -/
theorem IsContractibleLoopActionCritical.mem_periodicSolutions [I.Boundaryless]
    (hc : IsContractibleLoopActionCritical σ.1 H γ) (h : σ.IsNondegenerate)
    (hw : IsWeaklyExact σ.1) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hP : ∀ t, H (t + 1) = H t) :
    γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1 :=
  h.mem_periodicSolutions_of_forall_integral_eq_zero hH hP (n := 2) (by norm_num)
    hc.contMDiff hc.apply_add_one fun _ hwc hper h0 ↦
      (h.hasDerivAt_contractibleLoopAction_zero hw hH hc.exists_isCap hwc hper h0).unique
        (hc.hasDerivAt hwc hper h0)

/-- **The critical points of the action are the `1`-periodic orbits.** Let `σ` be a
nondegenerate weakly exact two-form on a manifold without boundary modelled on a
finite-dimensional space, and `H` a jointly `C¹` Hamiltonian, `1`-periodic in time. A `C²` loop
with a cap is a critical point of the contractible action exactly when it is a `1`-periodic orbit
of `X_H`. -/
theorem SmoothTwoForm.IsNondegenerate.isContractibleLoopActionCritical_iff [I.Boundaryless]
    (h : σ.IsNondegenerate) (hw : IsWeaklyExact σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hP : ∀ t, H (t + 1) = H t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (hcap : ∃ u, IsCap I u γ) :
    IsContractibleLoopActionCritical σ.1 H γ ↔
      γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1 :=
  ⟨fun hc ↦ hc.mem_periodicSolutions h hw hH hP, h.isContractibleLoopActionCritical hw hH hγ hcap⟩

end CriticalLoops

end TauCeti
