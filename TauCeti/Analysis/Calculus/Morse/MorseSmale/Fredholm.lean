/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.LinearizedTransversality
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic

/-!
# The Morse–Smale condition is surjectivity of the linearized operators

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, and `γ` a trajectory of its negative gradient, `γ' = -∇f(γ)`, running from a
nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at `+∞`. Linearizing
the trajectory equation at `γ` gives the trajectory operator `D_γ ξ = ξ' + Hess f(γ) ξ` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)`. At a single trajectory, `D_γ` is onto exactly when the unstable set
of `p` and the stable set of `q` are transverse at `γ 0`
(`TauCeti.surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff`). This file
quantifies over all trajectories: `f` is Morse–Smale exactly when the linearized operator along
every connecting trajectory is onto. So the regular points of the description of the spaces of
trajectories as intersections of unstable and stable sets, and of Schwarz's description of them as
zero sets of a Fredholm section, coincide.

## Main results

* `TauCeti.isMorseSmale_iff_forall_surjective_trajectoryOperator`: the negative gradient flow is
  Morse–Smale exactly when the linearized operator along every trajectory between nondegenerate
  critical points is onto.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (the linearized operator, its kernel and cokernel through decaying solutions, and
  transversality).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic Geometry and Topology*, IAS/Park City
  Math. Ser. **7**, 1999, Lecture 2 (the linearized operator is onto exactly when the unstable and
  stable manifolds intersect transversally).
-/

public section

open Filter MeasureTheory Topology
open scoped ENNReal Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0}

/-- **Morse–Smale means every linearized operator is onto.** For a `C²` function with globally
Lipschitz gradient, the negative gradient flow is Morse–Smale exactly when, along every negative
gradient trajectory `γ` between nondegenerate critical points, the linearized operator
`ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is onto. -/
theorem isMorseSmale_iff_forall_surjective_trajectoryOperator (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) :
    IsMorseSmale f hf ↔ ∀ ⦃p q : E⦄ ⦃γ : ℝ → E⦄, IsNondegenerateCriticalPoint f p →
      IsNondegenerateCriticalPoint f q → IsIntegralCurve γ (fun _ x ↦ -∇ f x) →
      Tendsto γ atBot (𝓝 p) → Tendsto γ atTop (𝓝 q) →
      ∀ AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)),
        AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
          (fun s ↦ hessianOperator f (γ s)) →
        Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) := by
  constructor
  · intro h p q γ hp hq hγ hbot htop AL hAL
    -- `γ` is the orbit of `γ 0` under the negative gradient flow.
    have hγφ : γ = fun t ↦ negativeGradientFlow f hf t (γ 0) :=
      funext (eq_negativeGradientFlow f hf hγ)
    rw [hγφ] at hbot htop hAL
    exact (surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff hp hq hfs hf
      (Flow.mem_unstableSet.2 hbot) (Flow.mem_stableSet.2 htop) hAL).2
      (h.transverse_at hp hq ⟨Flow.mem_unstableSet.2 hbot, Flow.mem_stableSet.2 htop⟩)
  · intro h
    refine IsMorseSmale.of_forall fun p q y hp hq hy ↦ ?_
    -- Every point of `W^u(p) ∩ W^s(q)` is the value at time `0` of its orbit.
    have hγ := (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
    have hbot := Flow.mem_unstableSet.1 hy.1
    have htop := Flow.mem_stableSet.1 hy.2
    have hmem := hfs.memLp_top_hessianOperator_comp hγ.continuous hbot htop
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
    exact (surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff hp hq hfs hf
      hy.1 hy.2 hmem.coeFn_toLp).1 (h hp hq hγ hbot htop _ hmem.coeFn_toLp)

end TauCeti
