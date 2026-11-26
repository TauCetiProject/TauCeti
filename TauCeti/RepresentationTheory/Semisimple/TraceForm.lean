/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Semisimple
-- Non-public: used only inside proofs.
import TauCeti.LinearAlgebra.Trace.Basic
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

* `Representation.finiteDimensional_of_nondegenerate`: a representation with nondegenerate trace
  pairing on its span is finite-dimensional, in any characteristic.
* `Representation.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero`: the trace pairing is
  nondegenerate on the span of a semisimple representation in characteristic zero.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A representation whose trace pairing is nondegenerate on its span is finite-dimensional: on an
infinite-dimensional space the trace vanishes identically, so the identity would pair to zero with
everything. -/
theorem finiteDimensional_of_nondegenerate (ρ : Representation k G V)
    (hρ : ∀ f ∈ Submodule.span k (Set.range ρ), (∀ g, LinearMap.trace k V (f * ρ g) = 0) → f = 0) :
    FiniteDimensional k V := by
  by_contra hV
  have htr := TauCeti.LinearMap.trace_eq_zero_of_not_finite hV
  have h1 : (1 : Module.End k V) = 0 :=
    hρ 1 (Submodule.subset_span ⟨1, map_one ρ⟩) fun g ↦ by rw [htr, LinearMap.zero_apply]
  have : Subsingleton V := ⟨fun v w ↦ by
    simpa using congr($h1 v).trans congr($h1 w).symm⟩
  exact hV inferInstance

/-- **The trace pairing is nondegenerate on the span of a semisimple representation.** Over a field
of characteristic zero, if `ρ` is a finite-dimensional semisimple representation and `f` is a linear
combination of the operators `ρ g` with `tr(f ρ(g)) = 0` for every `g`, then `f = 0`. -/
theorem eq_zero_of_mem_span_of_forall_trace_mul_eq_zero [CharZero k] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsSemisimpleRepresentation] {f : Module.End k V}
    (hf : f ∈ Submodule.span k (Set.range ρ)) (h : ∀ g, LinearMap.trace k V (f * ρ g) = 0) :
    f = 0 := by
  have := ρ.isSemisimpleModule_range_asAlgebraHom
  have hspan : ∀ b ∈ Submodule.span k (Set.range ρ), LinearMap.trace k V (f * b) = 0 := by
    apply LinearMap.eqOn_span (f := LinearMap.trace k V ∘ₗ LinearMap.mulLeft k f) (g := 0)
    rintro _ ⟨g, rfl⟩
    exact h g
  rw [← toSubmodule_range_asAlgebraHom] at hf hspan
  exact ρ.asAlgebraHom.range.eq_zero_of_forall_trace_mul_eq_zero hf hspan

end Representation
