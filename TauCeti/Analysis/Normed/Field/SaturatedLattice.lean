/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.SaturatedModule
public import TauCeti.Topology.Algebra.Valued.Integer

import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Saturated lattices over a nonarchimedean field

Let `K` be a nontrivially normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the
closed unit ball) and maximal ideal `𝓂[K]` (the open unit ball). This file relates the
`𝓂[K]`-saturation of `TauCeti.IsValuationSaturated` to the metric structure of `K`.

Bounded `𝒪[K]`-submodules of `ι → K` are transported along `𝒪[K]`-linear equivalences by
`LinearEquiv.isBounded_image_iff_of_integer`, and saturation by
`TauCeti.isValuationSaturated_congr`.

If the norm of `K` is dense, for instance if its value group is all of `ℝ_{>0}`, the maximal
ideal `𝓂[K]` is not finitely generated, so `𝒪[K]` and every principal lattice `a • 𝒪[K]` in `K`
are `𝓂[K]`-saturated. For a discretely valued field such as `ℚ_p` this fails: `ℤ_p` is not
saturated with respect to its maximal ideal `p ℤ_p`.

## Main results

* `TauCeti.isValuationSaturated_integer`, `TauCeti.isValuationSaturated_integer_span_singleton`:
  for a densely normed field, `𝒪[K]` and every principal lattice `a • 𝒪[K]` in `K` are
  `𝓂[K]`-saturated.
* `TauCeti.not_isValuationSaturated_maximalIdeal_integer`: the open unit ball `𝓂[K]` is not
  `𝓂[K]`-saturated.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 6.14.
-/

public section

open IsLocalRing
open scoped NormedField

namespace TauCeti

/-- Over a nontrivially normed nonarchimedean field, the open unit ball `𝓂[K]` is not saturated
with respect to itself. -/
theorem not_isValuationSaturated_maximalIdeal_integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    ¬ IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K))
      (maximalIdeal (Valued.integer K)) := by
  refine not_isValuationSaturated_ideal_ideal (fun h ↦ ?_) (maximalIdeal.isMaximal _).ne_top
  obtain ⟨x, hx0, hx1⟩ := Valued.integer.exists_norm_lt_one (K := K)
  have hx : x ∈ maximalIdeal (Valued.integer K) := Valued.integer.mem_maximalIdeal_iff.2 hx1
  rw [h, Ideal.mem_bot] at hx
  simp [hx] at hx0

section DenselyNormed

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

/-- Over a densely normed nonarchimedean field `K`, the valuation ring `𝒪[K]` is saturated with
respect to its maximal ideal. -/
theorem isValuationSaturated_integer :
    IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K)) (Valued.integer K) :=
  isValuationSaturated_maximalIdeal_self not_fg_maximalIdeal_integer

/-- Over a densely normed nonarchimedean field `K`, every principal lattice `a • 𝒪[K]` in `K`,
including `a = 0`, is saturated with respect to the maximal ideal of `𝒪[K]`. -/
theorem isValuationSaturated_integer_span_singleton (a : K) :
    IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K))
      (Valued.integer K ∙ a) :=
  isValuationSaturated_span_singleton not_fg_maximalIdeal_integer a

end DenselyNormed

/-- The ring `ℤ_[p]` of `p`-adic integers is not saturated with respect to its maximal ideal
`p ℤ_[p]`, since that ideal is finitely generated. -/
example (p : ℕ) [Fact p.Prime] :
    ¬ IsValuationSaturated ℤ_[p] (maximalIdeal ℤ_[p]) ℤ_[p] := fun h ↦
  isValuationSaturated_maximalIdeal_self_iff.1 h (IsNoetherian.noetherian _)

end TauCeti
