/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Flow.Basic

/-!
# Diffeomorphisms intertwine maximal flows

Let `ψ : M → M'` be a `C^n` diffeomorphism, `n ≠ 0`, carrying a vector field `X` on `M` to a
vector field `Y` on `M'`: `dψ_x (X x) = Y (ψ x)` for every `x`. Then `ψ` sends integral curves of
`X` to integral curves of `Y`, and its inverse carries `Y` back to `X`
(`Diffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`). Hence the maximal interval of existence
of `Y` through `ψ x` is that of `X` through `x`
(`Diffeomorph.maximalIntegralCurveInterval_apply`), and `ψ` conjugates the maximal flows:

`ψ (flowOf X t x) = flowOf Y t (ψ x)` (`Diffeomorph.apply_flowOf`).

This holds at every time, inside and outside the flow domain, since outside it both sides take the
junk value of the initial point. The comparison of intervals needs no regularity of the fields;
the identification of the flows uses uniqueness of integral curves of `Y`, so `Y` is `C^1` on a
Hausdorff boundaryless manifold.

## Main results

* `Diffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`: the inverse of a diffeomorphism
  carrying `X` to `Y` carries `Y` to `X`.
* `Diffeomorph.maximalIntegralCurveInterval_apply`, `Diffeomorph.mem_flowDomain_apply_iff`:
  related fields have the same maximal intervals of existence at corresponding points.
* `Diffeomorph.apply_flowOf`: a diffeomorphism carrying `X` to `Y` conjugates their maximal flows.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 9.13 (naturality of flows).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace Diffeomorph

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω} (ψ : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0)
  {X : (x : M) → TangentSpace I x} {Y : (y : M') → TangentSpace I' y}

include hn

/-- If a diffeomorphism carries the vector field `X` to `Y`, its inverse carries `Y` to `X`. -/
theorem mfderiv_symm_apply_eq_of_mfderiv_apply_eq
    (hXY : ∀ x, mfderiv I I' ψ x (X x) = Y (ψ x)) (y : M') :
    mfderiv I' I ψ.symm y (Y y) = X (ψ.symm y) := by
  obtain ⟨x, rfl⟩ := ψ.toEquiv.surjective y
  rw [coe_toEquiv, ← hXY x, ψ.mfderiv_symm_apply_mfderiv_apply hn, ψ.symm_apply_apply]

/-- A diffeomorphism carrying `X` to `Y` sends integral curves of `X` through `x` to integral
curves of `Y` through `ψ x`, so it enlarges no maximal interval of existence. -/
private theorem maximalIntegralCurveInterval_subset
    (hXY : ∀ x, mfderiv I I' ψ x (X x) = Y (ψ x)) (x : M) :
    maximalIntegralCurveInterval X x ⊆ maximalIntegralCurveInterval Y (ψ x) := by
  intro t ht
  obtain ⟨γ, a, b, hγ, hγ0, h0, hta, -⟩ := exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  exact (hγ.map_of_mfderiv_eq (fun s _ ↦ ψ.mdifferentiable hn (γ s)) (fun s _ ↦ hXY (γ s))
    ).subset_maximalIntegralCurveInterval h0 (by rw [comp_apply, hγ0]) hta

/-- **Related vector fields have the same maximal intervals.** If a diffeomorphism `ψ` carries `X`
to `Y`, the maximal interval of existence of `Y` through `ψ x` is that of `X` through `x`. -/
theorem maximalIntegralCurveInterval_apply
    (hXY : ∀ x, mfderiv I I' ψ x (X x) = Y (ψ x)) (x : M) :
    maximalIntegralCurveInterval Y (ψ x) = maximalIntegralCurveInterval X x := by
  refine Subset.antisymm ?_ (ψ.maximalIntegralCurveInterval_subset hn hXY x)
  have h := ψ.symm.maximalIntegralCurveInterval_subset hn
    (ψ.mfderiv_symm_apply_eq_of_mfderiv_apply_eq hn hXY) (ψ x)
  rwa [ψ.symm_apply_apply] at h

/-- If a diffeomorphism `ψ` carries `X` to `Y`, the flow of `Y` is defined at `(t, ψ x)` exactly
when the flow of `X` is defined at `(t, x)`. -/
theorem mem_flowDomain_apply_iff
    (hXY : ∀ x, mfderiv I I' ψ x (X x) = Y (ψ x)) {t : ℝ} {x : M} :
    (t, ψ x) ∈ flowDomain Y ↔ (t, x) ∈ flowDomain X := by
  rw [mem_flowDomain, mem_flowDomain, ψ.maximalIntegralCurveInterval_apply hn hXY]

variable [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M']

/-- **Naturality of flows.** A diffeomorphism `ψ` carrying the vector field `X` to the `C^1` vector
field `Y` conjugates their maximal flows: `ψ (flowOf X t x) = flowOf Y t (ψ x)`. Outside the flow
domain both sides are the junk value `ψ x`. -/
theorem apply_flowOf (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x, mfderiv I I' ψ x (X x) = Y (ψ x)) (t : ℝ) (x : M) :
    ψ (flowOf X t x) = flowOf Y t (ψ x) := by
  rw [TauCeti.flowOf_apply, TauCeti.flowOf_apply]
  by_cases ht : t ∈ maximalIntegralCurveInterval X x
  · obtain ⟨γ, a, b, hγ, hγ0, h0, hta, heq⟩ :=
      exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
    have hψγ := hγ.map_of_mfderiv_eq (fun s _ ↦ ψ.mdifferentiable hn (γ s))
      fun s _ ↦ hXY (γ s)
    rw [heq]
    exact ((hψγ.eqOn_maximalIntegralCurve hY h0 (by rw [comp_apply, hγ0])) hta).symm
  · rw [maximalIntegralCurve_eq_of_not_mem ht, maximalIntegralCurve_eq_of_not_mem
      (by rwa [ψ.maximalIntegralCurveInterval_apply hn hXY])]

end Diffeomorph
