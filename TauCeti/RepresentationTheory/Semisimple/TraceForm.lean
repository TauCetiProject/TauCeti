/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Semisimple
-- Non-public: the image algebra and its semisimple module trace pairing are used only in proofs.
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.Semisimple.Range
import TauCeti.RingTheory.SimpleModule.Subalgebra

/-!
# The trace pairing on the span of a semisimple representation

Let `ρ` be a finite-dimensional semisimple representation of a monoid `G` over a field `k` of
characteristic zero. The trace pairing `(x, y) ↦ tr(x y)` of `End_k(V)` is nondegenerate on the
span of the operators `ρ g`: an element `f` of that span with `tr(f ρ(g)) = 0` for every `g` is
zero (`Representation.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero`).

The span is the image `B` of the monoid algebra `k[G]` in `End_k(V)`, and `V` is a semisimple
`B`-module, so this is `Subalgebra.eq_zero_of_forall_trace_mul_eq_zero`. Consequently every linear
functional on that span is a linear combination of the functionals `x ↦ tr(x ρ(g))`, which is how
the character of `ρ` controls all its matrix coefficients.

Both hypotheses are needed. In characteristic `p` the trivial representation on `k ^ p` is
semisimple, and the identity pairs to zero with every `ρ g`. In characteristic zero the
representation of `ℕ` on `k ^ 2` sending `1` to a unipotent `2 × 2` matrix `1 + N` has span
`k + k N`, and `N` pairs to zero with all of it.

## Main results

* `Representation.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero`: the trace pairing is
  nondegenerate on the span of a semisimple representation in characteristic zero.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **The trace pairing is nondegenerate on the span of a semisimple representation.** Over a field
of characteristic zero, if `ρ` is a finite-dimensional semisimple representation and `f` is a linear
combination of the operators `ρ g` with `tr(f ρ(g)) = 0` for every `g`, then `f = 0`. -/
theorem eq_zero_of_mem_span_of_forall_trace_mul_eq_zero [CharZero k] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsSemisimpleRepresentation] {f : Module.End k V}
    (hf : f ∈ Submodule.span k (Set.range ρ)) (h : ∀ g, LinearMap.trace k V (f * ρ g) = 0) :
    f = 0 := by
  have := ρ.isSemisimpleModule_range_asAlgebraHom
  have hspan : ∀ b ∈ Submodule.span k (Set.range ρ), LinearMap.trace k V (f * b) = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp [mul_add, h₁, h₂]
    | smul c _ _ h₁ => simp [h₁]
  rw [← toSubmodule_range_asAlgebraHom] at hf hspan
  exact ρ.asAlgebraHom.range.eq_zero_of_forall_trace_mul_eq_zero hf hspan

end Representation
