/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.LinearizedTransversality
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic
import TauCeti.Analysis.Calculus.Morse.RegularLevel
import TauCeti.Analysis.Calculus.Morse.Transversality

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

Along the constant trajectory at a nondegenerate critical point `p` the linearized operator is
bijective, so the unstable and stable sets of `p` are transverse at `p`. Together with a count of
dimensions this shows that the Morse–Smale condition only concerns trajectories between distinct
critical points whose indices lie strictly between `0` and `dim E`.

## Main results

* `TauCeti.isMorseSmale_iff_forall_surjective_trajectoryOperator`: the negative gradient flow is
  Morse–Smale exactly when the linearized operator along every trajectory between nondegenerate
  critical points is onto.
* `span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_self` (in the namespace
  `TauCeti.IsNondegenerateCriticalPoint`): the unstable and stable sets of a nondegenerate critical
  point are transverse at that point.
* `TauCeti.IsMorseSmale.of_forall_ne_of_morseIndex_ne`: it suffices to check the Morse–Smale
  condition between distinct critical points of intermediate index.

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

namespace IsNondegenerateCriticalPoint

/-- **Transversality at a critical point.** At a nondegenerate critical point `p` of a `C²` function
with globally Lipschitz gradient, the unstable and stable sets of `p` are transverse at `p`, since
the linearized operator `ξ ↦ ξ' + Hess f(p) ξ` along the constant trajectory at `p` is bijective. -/
theorem span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_self
    {p : E} (hp : IsNondegenerateCriticalPoint f p) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) p) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) p) p) = ⊤ := by
  have hfix : ∀ t, negativeGradientFlow f hf t p = p :=
    (forall_negativeGradientFlow_eq_self_iff f hf p).2 (by simp [gradient, hp.fderiv_eq_zero])
  have hAL := (memLp_top_const (μ := volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
    (hessianOperator f p)).coeFn_toLp
  refine (surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff hp hp hfs hf
    (Flow.self_mem_unstableSet_iff.2 hfix) (Flow.self_mem_stableSet_iff.2 hfix) ?_).1
    (hp.bijective_trajectoryOperator_hessianOperator hAL).surjective
  simpa only [hfix] using hAL

end IsNondegenerateCriticalPoint

/-- **The Morse–Smale condition is only a condition between intermediate indices.** Let `f` be a
`C²` function with globally Lipschitz gradient on a space of dimension `n`. Its negative gradient
flow is Morse–Smale as soon as `W^u(p)` and `W^s(q)` meet transversally for all distinct
nondegenerate critical points `p` and `q` whose indices both differ from `0` and from `n`. All other
pairs are transverse automatically:

* if `p = q`, the only common point is `p`, where `W^u(p)` and `W^s(p)` are transverse
  (`span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_self`);
* if `ind p = n` or `ind q = 0`, the tangent space of `W^u(p)` or of `W^s(q)` is already `E`;
* if `ind p = 0` or `ind q = n` and `p ≠ q`, no trajectory runs from `p` to `q`, since its velocity
  would be a nonzero tangent vector of `W^u(p)` or of `W^s(q)`, whose tangent spaces are then
  zero. -/
theorem IsMorseSmale.of_forall_ne_of_morseIndex_ne (hfs : ContDiff ℝ 2 f)
    {hf : LipschitzWith K (∇ f)}
    (htr : ∀ ⦃p q y : E⦄, IsNondegenerateCriticalPoint f p → IsNondegenerateCriticalPoint f q →
      p ≠ q → morseIndex f p ≠ 0 → morseIndex f p ≠ Module.finrank ℝ E → morseIndex f q ≠ 0 →
      morseIndex f q ≠ Module.finrank ℝ E →
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
        Flow.stableSet (negativeGradientFlow f hf) q →
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤) :
    IsMorseSmale f hf := by
  refine IsMorseSmale.of_forall fun p q y hp hq hy ↦ ?_
  obtain rfl | hpq := eq_or_ne p q
  · obtain rfl :=
      (isNegativeGradient_negativeGradientFlow f hf).eq_of_mem_unstableSet_inter_stableSet
        (fun _ ↦ (hfs.differentiable (by norm_num)).differentiableAt) hfs.continuous.continuousAt hy
    exact hp.span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_self hfs hf
  have hu := hp.finrank_span_tangentConeAt_unstableSet hfs hf hy.1
  have hs := hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf hy.2
  -- The velocity `-∇f y` is a nonzero vector tangent to both `W^u(p)` and `W^s(q)`.
  have hgy : -∇ f y ≠ 0 :=
    neg_ne_zero.2 (Flow.gradient_ne_zero_of_mem_unstableSet_inter_stableSet
      (fun z ↦ (forall_negativeGradientFlow_eq_self_iff f hf z).2) hpq hy)
  have hmemu : -∇ f y ∈
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) :=
    Submodule.subset_span
      (neg_gradient_mem_tangentConeAt_of_isInvariant f hf (Flow.isInvariant_unstableSet _ p) hy.1)
  have hmems : -∇ f y ∈
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) :=
    Submodule.subset_span
      (neg_gradient_mem_tangentConeAt_of_isInvariant f hf (Flow.isInvariant_stableSet _ q) hy.2)
  by_cases hp0 : morseIndex f p = 0
  · rw [Submodule.finrank_eq_zero.1 (hu.trans hp0)] at hmemu
    exact (hgy ((Submodule.mem_bot ℝ).1 hmemu)).elim
  by_cases hpn : morseIndex f p = Module.finrank ℝ E
  · rw [Submodule.eq_top_of_finrank_eq (hu.trans hpn), top_sup_eq]
  by_cases hq0 : morseIndex f q = 0
  · rw [Submodule.eq_top_of_finrank_eq (by omega : Module.finrank ℝ (Submodule.span ℝ
      (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y)) = Module.finrank ℝ E),
      sup_top_eq]
  by_cases hqn : morseIndex f q = Module.finrank ℝ E
  · rw [Submodule.finrank_eq_zero.1 (by omega : Module.finrank ℝ (Submodule.span ℝ
      (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y)) = 0)] at hmems
    exact (hgy ((Submodule.mem_bot ℝ).1 hmems)).elim
  exact htr hp hq hpq hp0 hpn hq0 hqn hy

end TauCeti
