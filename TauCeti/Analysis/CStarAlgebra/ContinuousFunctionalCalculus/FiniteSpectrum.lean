/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The continuous functional calculus of an element with finite spectrum

If the spectrum of `a` is finite, every scalar function is continuous on it, so `cfc f a` is
the genuine functional calculus of `a` for every `f`. When the spectrum lies in a finite set `s`,
the functional calculus is Lagrange interpolation on the nodes `s`:
`cfc f a = ∑ μ ∈ s, f μ • ℓ_μ(a)`, where `ℓ_μ` is the Lagrange basis polynomial that is `1` at `μ`
and `0` at the other nodes. The elements `ℓ_μ(a)` do not depend on `f`, so every `cfc f a` is a
fixed linear combination of polynomials in `a`, with coefficients the values of `f`.

## Main results

* `TauCeti.cfc_eq_sum_smul_aeval_lagrangeBasis`: if the spectrum of `a` lies in the finite set `s`,
  then `cfc f a = ∑ μ ∈ s, f μ • ℓ_μ(a)` for the Lagrange basis polynomials `ℓ_μ` of `s`.
-/

public section

namespace TauCeti

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- **The functional calculus as Lagrange interpolation.** If the spectrum of `a` lies in the
finite set `s`, then `cfc f a = ∑ μ ∈ s, f μ • ℓ_μ(a)`, where `ℓ_μ = Lagrange.basis s id μ` is
the Lagrange basis polynomial of the nodes `s` that is `1` at `μ` and `0` at the other nodes. -/
theorem cfc_eq_sum_smul_aeval_lagrangeBasis [DecidableEq R] (f : R → R) {a : A} {s : Finset R}
    (hs : spectrum R a ⊆ s) (ha : p a := by cfc_tac) :
    cfc f a = ∑ μ ∈ s, f μ • Polynomial.aeval a (Lagrange.basis s id μ) := by
  rw [cfc_congr (g := (Lagrange.interpolate s id f).eval) fun x hx ↦
      (Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (hs hx)).symm,
    cfc_polynomial _ a ha, Lagrange.interpolate_apply, map_sum]
  simp [Algebra.smul_def]

end TauCeti
