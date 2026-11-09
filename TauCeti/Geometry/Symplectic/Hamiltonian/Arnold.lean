/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.Morse.MinCriticalCount
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# The degenerate Arnold comparison and its autonomous case

Let `σ` be a nondegenerate two-form on a manifold `M` modelled on a finite-dimensional space, and
let `c(M) = TauCeti.minCriticalCount I M` be the least number of critical points of a smooth real
function on `M`, counted in `ℕ∞` and minimized over all smooth functions, Morse or not.
The time-one map of a time-dependent Hamiltonian `H : ℝ → M → ℝ` is
`φ_H = timeDependentFlowOf X_H 0 1`, where `X_H(t, x) = X_{H t}(x)` and `ι_{X_{H t}} σ = d(H t)`.

The **degenerate Arnold comparison** for a map `φ` asserts that if `φ` is the time-one map of a
smooth Hamiltonian isotopy, then `φ` has at least `c(M)` fixed points, each fixed point counted
once and the count taken in `ℕ∞`
(`TauCeti.SmoothTwoForm.DegenerateArnoldCriticalNumberStatement`). On a closed symplectic
manifold this is Arnold's conjecture for possibly degenerate Hamiltonian diffeomorphisms. It is
recorded here as a statement; it is not asserted in general.

The autonomous case is proved directly, without Floer theory. For a time-independent Hamiltonian
`H`, nondegeneracy of `σ` makes the zeros of `X_H` exactly the critical points of `H`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_eq_zero_iff`). By uniqueness of
solutions, the trajectory through such a point is constant, so every critical point of `H` is a
fixed point of every time map of `X_H`. Hence `c(M) ≤ #Crit(H) ≤ #Fix(φ_H)`, where the first
inequality is the definition of `c(M)`; if `H` has infinitely many critical points, `φ_H` has
infinitely many fixed points. More generally, a point that is critical for every `H t` is fixed
by every time map of a time-dependent Hamiltonian.

The inclusion of critical points among fixed points is in general strict: time-one fixed points
need not be equilibria, as for the rotation flows of the harmonic oscillator. So the general
time-dependent comparison does not follow from the autonomous argument.

No compactness is assumed. On a closed manifold the suspension of every `C¹` time-dependent
vector field is complete (`TauCeti.isCompleteVectorField_timeDependentSuspensionField`, applied
to the whole manifold), and `c(M)` is finite (`TauCeti.minCriticalCount_ne_top`).

## Main declarations

* `TauCeti.SmoothTwoForm.DegenerateArnoldCriticalNumberStatement`: the degenerate Arnold
  comparison `c(M) ≤ #Fix(φ)` for time-one maps of smooth Hamiltonian isotopies.

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `timeDependentFlowOf_hamiltonianVectorField_eq_self`: points critical for every `H t` are fixed
  by the time-dependent Hamiltonian flow.
* `criticalPoints_subset_fixedPoints_timeDependentFlowOf`: the critical points of an autonomous
  Hamiltonian are fixed points of each of its time maps.
* `minCriticalCount_le_encard_fixedPoints_timeDependentFlowOf`: the time maps of an autonomous
  Hamiltonian flow have at least `c(M)` fixed points.
* `degenerateArnoldCriticalNumberStatement_timeDependentFlowOf`: the time-one maps of autonomous
  Hamiltonian flows satisfy the degenerate Arnold comparison.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 9.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 11 (the Arnold conjecture and its degenerate form).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {φ : M → M}

/-! ### The degenerate Arnold comparison -/

/-- The **degenerate Arnold comparison** for `φ`: whenever `φ` is the time-one map
`timeDependentFlowOf X_H 0 1` of a smooth time-dependent Hamiltonian `H` whose flow is defined for
all times, `φ` has at least `c(M) = minCriticalCount I M` fixed points, counted in `ℕ∞`.

The completeness hypothesis on the suspension of `X_H` makes `φ` a genuine time-one map, rather
than a junk value of the maximal flow; it holds for every smooth `H` when `σ` is nondegenerate
and `M` is closed. On a closed symplectic manifold this is Arnold's conjecture for possibly
degenerate Hamiltonian diffeomorphisms. The autonomous case is
`TauCeti.SmoothTwoForm.IsNondegenerate.degenerateArnoldCriticalNumberStatement_timeDependentFlowOf`.
-/
def DegenerateArnoldCriticalNumberStatement (σ : SmoothTwoForm I M) (φ : M → M) : Prop :=
  ∀ H : ℝ → M → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ (uncurry H) →
    IsCompleteVectorField
      (timeDependentSuspensionField fun t ↦ σ.hamiltonianVectorField (H t)) →
    timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) 0 1 = φ →
    minCriticalCount I M ≤ (fixedPoints φ).encard

/-- The degenerate Arnold comparison holds for a map with at least `c(M)` fixed points. -/
theorem DegenerateArnoldCriticalNumberStatement.of_minCriticalCount_le_encard_fixedPoints
    (h : minCriticalCount I M ≤ (fixedPoints φ).encard) :
    σ.DegenerateArnoldCriticalNumberStatement φ :=
  fun _ _ _ _ ↦ h

/-- If the degenerate Arnold comparison holds for the time-one map of a smooth time-dependent
Hamiltonian flow defined for all times, that map has at least `c(M)` fixed points. -/
theorem DegenerateArnoldCriticalNumberStatement.minCriticalCount_le_encard_fixedPoints
    {H : ℝ → M → ℝ}
    (h : σ.DegenerateArnoldCriticalNumberStatement
      (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) 0 1))
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ (uncurry H))
    (hcomplete : IsCompleteVectorField
      (timeDependentSuspensionField fun t ↦ σ.hamiltonianVectorField (H t))) :
    minCriticalCount I M ≤
      (fixedPoints (timeDependentFlowOf (fun t ↦ σ.hamiltonianVectorField (H t)) 0 1)).encard :=
  h H hH hcomplete rfl

/-! ### Critical points are fixed points -/

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] (h : σ.IsNondegenerate)
include h

/-- **Common critical points are fixed by a time-dependent Hamiltonian flow.** For a jointly `C²`
time-dependent Hamiltonian `H`, a point that is critical for every `H t` is fixed by the
time-dependent flow of `X_H` from any time `s` to any time `t`. -/
theorem timeDependentFlowOf_hamiltonianVectorField_eq_self {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) {x : M}
    (hx : ∀ u, x ∈ criticalPoints I (H u)) (s t : ℝ) :
    timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s t x = x :=
  timeDependentFlowOf_eq_self_of_forall_eq_zero
    (h.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) hH)
    (fun u ↦ h.hamiltonianVectorField_eq_zero_iff.2 (mem_criticalPoints.1 (hx u))) s t

/-- **The critical points of an autonomous Hamiltonian are fixed points of its flow.** For a `C²`
function `f`, every critical point of `f` is a fixed point of each time map of the Hamiltonian
vector field `X_f`, viewed as a time-independent field. -/
theorem criticalPoints_subset_fixedPoints_timeDependentFlowOf {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (s t : ℝ) :
    criticalPoints I f ⊆
      fixedPoints (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField f) s t) :=
  fun _ hx ↦ h.timeDependentFlowOf_hamiltonianVectorField_eq_self (H := fun _ ↦ f)
    (hf.comp contMDiff_snd) (fun _ ↦ hx) s t

/-- **The autonomous degenerate Arnold comparison.** Each time map of the Hamiltonian flow of a
smooth time-independent Hamiltonian `f` has at least `c(M)` fixed points, counted in `ℕ∞`: there
are at least as many as critical points of `f`, and `f` has at least `c(M)` of those. -/
theorem minCriticalCount_le_encard_fixedPoints_timeDependentFlowOf {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (s t : ℝ) :
    minCriticalCount I M ≤
      (fixedPoints (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField f) s t)).encard :=
  (minCriticalCount_le hf).trans <| by
    rw [totalCriticalCount_def]
    exact encard_le_encard
      (h.criticalPoints_subset_fixedPoints_timeDependentFlowOf (hf.of_le (by simp)) s t)

/-- **Autonomous Hamiltonian diffeomorphisms satisfy the degenerate Arnold comparison.** The
time-one map of the Hamiltonian flow of a smooth time-independent Hamiltonian satisfies
`DegenerateArnoldCriticalNumberStatement`. -/
theorem degenerateArnoldCriticalNumberStatement_timeDependentFlowOf {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    σ.DegenerateArnoldCriticalNumberStatement
      (timeDependentFlowOf (fun _ ↦ σ.hamiltonianVectorField f) 0 1) :=
  .of_minCriticalCount_le_encard_fixedPoints
    (h.minCriticalCount_le_encard_fixedPoints_timeDependentFlowOf hf 0 1)

end IsNondegenerate

end SmoothTwoForm

end TauCeti
