/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Action.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation

/-!
# The first variation of the action relative to a reference loop and its critical loops

Let `σ` be a nondegenerate two-form on a manifold `M` which vanishes on tori
(`TauCeti.VanishesOnTori`, the area half of symplectic atoroidality), `H : ℝ → M → ℝ` a
time-dependent Hamiltonian and `γ₀` a reference loop. The action of a loop `γ` relative to `γ₀`,

`𝒜_H(γ) = ∫ Γ^* σ - ∫₀¹ H(t, γ(t)) dt`

for a smooth cylinder `Γ` from `γ` to `γ₀` (`TauCeti.SmoothTwoForm.referenceAction`), does not
depend on the cylinder. Choosing one reference loop in each free homotopy class, it is the action
functional on the whole free loop space, not only on contractible loops. This file computes its
derivative along a smooth **variation through loops**, a smooth map `w : ℝ × ℝ → M`,
`1`-periodic in its second coordinate `t`, with loops `γ_s = w (s, ·)`.

If the loop `γ_{s₀}` is joined to `γ₀` by a smooth cylinder `Γ`, so is every loop `γ_s`: run
through the variation from `γ_s` to `γ_{s₀}`, then through `Γ`. The area term of `𝒜_H(γ_s)` is
therefore that of `γ_{s₀}` plus the area swept out by the variation between `s` and `s₀`, and
this gives the **first variation formula**

`d/ds 𝒜_H(γ_s) = ∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt`

(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction`), for Hamiltonian vector
fields `ι_{X_{H_t}} σ = dH_t`. It has the same form as for the action of contractible loops
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`).

A loop `γ` is a **critical point of the action** relative to `γ₀`
(`TauCeti.SmoothTwoForm.IsReferenceActionCritical`) when it is a smooth loop joined to `γ₀` by a
smooth cylinder and the derivative at `s = 0` of `𝒜_H(γ_s)` vanishes for every smooth variation
through loops starting at `γ`. The `1`-periodic orbits of `X_H` are critical, and conversely, for
a Hamiltonian which is `1`-periodic in time on a manifold without boundary modelled on a
finite-dimensional space, every critical loop is a `1`-periodic orbit, by the chart-variation
argument of `TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation`. So the critical loops are
exactly the smooth `1`-periodic orbits of `X_H` joined to `γ₀` by a smooth cylinder
(`TauCeti.SmoothTwoForm.IsNondegenerate.isReferenceActionCritical_iff`). These are the generators,
in the free homotopy class of `γ₀`, of the Floer complex of an atoroidal manifold.

## Main definitions

* `TauCeti.SmoothTwoForm.IsReferenceActionCritical σ H γ₀ γ`: `γ` is a critical point of the
  action relative to `γ₀`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction`: the first variation formula.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isReferenceActionCritical_iff`: the critical points of the
  action relative to `γ₀` are the `1`-periodic orbits joined to `γ₀` by a smooth cylinder.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the action functional on loops in a fixed free homotopy class).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
-/

public section

noncomputable section

open Function Set
open scoped Manifold Interval ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ} {γ₀ γ : ℝ → M} {w : ℝ × ℝ → M}

/-! ### The first variation formula -/

variable [FiniteDimensional ℝ E]

/-- **The first variation of the action relative to a reference loop.** Let `σ` be a nondegenerate
two-form vanishing on tori, `H` a jointly `C¹` time-dependent Hamiltonian and `w` a smooth
variation through loops, `1`-periodic in `t`, whose loop `w (s₀, ·)` is joined to the reference loop
`γ₀` by a smooth cylinder. Then the action of the loops `w (s, ·)` relative to `γ₀` has derivative
`∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt` at `s₀`, with all terms taken at `(s₀, t)`. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction (h : σ.IsNondegenerate)
    (hT : VanishesOnTori σ.1) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w) (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z)
    {s₀ : ℝ} (hcyl : ∃ u, IsSmoothCylinder I (fun t ↦ w (s₀, t)) γ₀ u) :
    HasDerivAt (fun s ↦ σ.referenceAction H γ₀ fun t ↦ w (s, t))
      (∫ t in 0..1, σ.1 (w (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)]) s₀ := by
  obtain ⟨u, hu⟩ := hcyl
  have hσ : IsSmoothForm I 0 σ.1 := σ.isSmoothForm.of_le (by simp)
  have hw1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w := hwc.of_le (by simp)
  -- the area term of the action of `w (s, ·)` is the area swept from `s` to `s₀` plus the area
  -- of `u`
  have heq : (fun s ↦ σ.referenceAction H γ₀ fun t ↦ w (s, t)) = fun s ↦
      (rectangleIntegral σ.1 (w ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id) (0, 0) (1, 1) +
        rectangleIntegral σ.1 u (0, 0) (1, 1)) - ∫ t in 0..1, H t (w (s, t)) := by
    funext s
    -- the loop `w (s, ·)` is joined to `γ₀` through the variation from `s` to `s₀`, then `u`
    have hcyl : IsSmoothCylinder I (fun t ↦ w (s, t)) γ₀
        (rectangleTrans (w ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id) u) :=
      (isSmoothCylinder_comp_prodMap_affine hwc hper s s₀).trans hu fun t ↦ by
        simp [hu.apply_zero]
    rw [referenceAction_eq hT hcyl,
      cylinderAction_rectangleTrans hσ H (hw1.comp (contMDiff_prodMap_affine s s₀))
        (hu.contMDiff.of_le (by simp)) fun t ↦ by simp [hu.apply_zero], cylinderAction_def]
    simp only [comp_apply, Prod.map_apply, mul_zero, add_zero, id_eq]
    ring
  rw [heq]
  exact h.hasDerivAt_sub_intervalIntegral hH hw1
    ((hasDerivAt_rectangleIntegral_comp_prodMap_affine hσ hw1 s₀ 0 1).add_const _)

/-! ### Critical loops of the action -/

variable (σ H γ₀ γ) in
/-- A loop `γ` is a **critical point of the action relative to the reference loop** `γ₀` when it
is a `1`-periodic smooth loop joined to `γ₀` by a smooth cylinder and, for every smooth variation
`w` through loops starting at `γ`, the action `𝒜_H(w (s, ·))` relative to `γ₀` has derivative `0`
at `s = 0`. -/
structure SmoothTwoForm.IsReferenceActionCritical : Prop where
  /-- A critical loop is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ
  /-- A critical loop is `1`-periodic. -/
  apply_add_one : ∀ t, γ (t + 1) = γ t
  /-- A critical loop is joined to the reference loop by a smooth cylinder. -/
  exists_isSmoothCylinder : ∃ u, IsSmoothCylinder I γ γ₀ u
  /-- The action is stationary along every variation through loops. -/
  hasDerivAt : ∀ ⦃w : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w →
    (∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) → (∀ t, w (0, t) = γ t) →
    HasDerivAt (fun s ↦ σ.referenceAction H γ₀ fun t ↦ w (s, t)) 0 0

/-- Along a smooth variation through loops of a loop `γ` joined to `γ₀` by a smooth cylinder, the
action of the loops relative to `γ₀` has at `s = 0` the derivative given by the first variation
formula. -/
private theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction_zero
    (h : σ.IsNondegenerate) (hT : VanishesOnTori σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hcyl : ∃ u, IsSmoothCylinder I γ γ₀ u)
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w) (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z)
    (h0 : ∀ t, w (0, t) = γ t) :
    HasDerivAt (fun s ↦ σ.referenceAction H γ₀ fun t ↦ w (s, t))
      (∫ t in 0..1, σ.1 (w (0, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)]) 0 :=
  h.hasDerivAt_referenceAction hT hH hwc hper (funext h0 ▸ hcyl)

/-- **The `1`-periodic orbits are critical points of the action.** For a nondegenerate two-form
vanishing on tori and a jointly `C¹` Hamiltonian, a smooth loop joined to `γ₀` by a smooth
cylinder which is a `1`-periodic orbit of `X_H` is a critical point of the action relative to
`γ₀`. -/
theorem SmoothTwoForm.IsNondegenerate.isReferenceActionCritical (h : σ.IsNondegenerate)
    (hT : VanishesOnTori σ.1) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hcyl : ∃ u, IsSmoothCylinder I γ γ₀ u)
    (horbit : γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1) :
    σ.IsReferenceActionCritical H γ₀ γ where
  contMDiff := hγ
  apply_add_one := (mem_periodicSolutions.mp horbit).2
  exists_isSmoothCylinder := hcyl
  hasDerivAt w hwc hper h0 := by
    convert h.hasDerivAt_referenceAction_zero hT hH hcyl hwc hper h0 using 1
    exact (σ.intervalIntegral_apply_sub_hamiltonianVectorField_eq_zero horbit
      (fun t ↦ (hwc (0, t)).mdifferentiableAt (by simp)) h0 0 1).symm

/-- **Critical points of the action are `1`-periodic orbits.** Let `σ` be a nondegenerate two-form
vanishing on tori on a manifold without boundary modelled on a finite-dimensional space, and `H` a
jointly `C¹` Hamiltonian, `1`-periodic in time. Then a critical point of the action relative to a
reference loop is a `1`-periodic orbit of `X_H`. -/
theorem SmoothTwoForm.IsReferenceActionCritical.mem_periodicSolutions [I.Boundaryless]
    (hc : σ.IsReferenceActionCritical H γ₀ γ) (h : σ.IsNondegenerate) (hT : VanishesOnTori σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hP : ∀ t, H (t + 1) = H t) :
    γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1 :=
  h.mem_periodicSolutions_of_forall_integral_eq_zero hH hP (n := ⊤) le_top hc.contMDiff
    hc.apply_add_one fun _ hwc hper h0 ↦
      (h.hasDerivAt_referenceAction_zero hT hH hc.exists_isSmoothCylinder hwc hper h0).unique
        (hc.hasDerivAt hwc hper h0)

/-- **The critical points of the action relative to a reference loop are the `1`-periodic
orbits.** Let `σ` be a nondegenerate two-form vanishing on tori on a manifold without boundary
modelled on a finite-dimensional space, and `H` a jointly `C¹` Hamiltonian, `1`-periodic in time.
A smooth loop joined to the reference loop `γ₀` by a smooth cylinder is a critical point of the
action relative to `γ₀` exactly when it is a `1`-periodic orbit of `X_H`. -/
theorem SmoothTwoForm.IsNondegenerate.isReferenceActionCritical_iff [I.Boundaryless]
    (h : σ.IsNondegenerate) (hT : VanishesOnTori σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hP : ∀ t, H (t + 1) = H t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hcyl : ∃ u, IsSmoothCylinder I γ γ₀ u) :
    σ.IsReferenceActionCritical H γ₀ γ ↔
      γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1 :=
  ⟨fun hc ↦ hc.mem_periodicSolutions h hT hH hP, h.isReferenceActionCritical hT hH hγ hcyl⟩

end TauCeti
