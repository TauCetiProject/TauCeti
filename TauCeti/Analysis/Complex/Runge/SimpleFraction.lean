/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Runge.Rational

/-!
# Runge approximation of simple fractions

If a compact set `K` is filled in a subset `Ω` of the complex plane, every simple fraction with
pole outside `K` is uniformly approximable on `K` by functions holomorphic on `Ω`. Neither `K` nor
`Ω` needs to be connected. This is the simple-fraction form of Runge's theorem used to replace the
rational kernels in finite-rank holomorphic approximation operators.

The proof delegates to `TauCeti.exists_rational_norm_inv_sub_lt` with poles in `Ωᶜ`, converting
filledness into the pole-set condition via `TauCeti.IsFilledIn.not_connectedComponentIn_subset`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
-/

public section

open Set

namespace TauCeti

variable {K Ω : Set ℂ}

/-- **Runge approximation for a simple fraction.** On a compact set filled in `Ω`, a simple
fraction whose pole avoids that compact set is uniformly approximable by functions holomorphic
on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_inv_sub_lt (hfill : IsFilledIn K Ω)
    (_hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε := by
  obtain ⟨p, q, -, hqΩ, hlt⟩ := exists_rational_norm_inv_sub_lt hK
    (fun _ hx => hfill.compl_inter_connectedComponentIn_nonempty hK.isClosed hKΩ hx) ha hε
  refine ⟨fun z => p.eval z / q.eval z, ?_, hlt⟩
  exact p.differentiable.differentiableOn.div q.differentiable.differentiableOn
    fun z hz h0 => (hqΩ z h0).1 hz

end TauCeti
