/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.LinearMap
import TauCeti.LinearAlgebra.Submodule.Compl
import TauCeti.LinearAlgebra.Trace.Exact

/-!
# The trace of an endomorphism exchanging two subspaces

Let `f` be an endomorphism of a finite-dimensional vector space `V` that maps each of two
subspaces `A` and `B` into the other. Then `f` preserves `A ⊓ B`, and when `A ⊔ B = ⊤` the trace of
`f` is the trace of its restriction to `A ⊓ B`: on `V ⧸ (A ⊓ B)`, which is the direct sum of the
images of `A` and `B`, the induced map exchanges the two summands and so has trace `0`
(Mathlib's `LinearMap.trace_eq_zero_of_mapsTo_ne`).

This is the linear algebra behind the trace reduction in Popa and Zagier's proof of the
Eichler–Selberg trace formula: their operator `T̃ₙ` exchanges `A = ker(1 + S)` and
`B = ker(1 + U + U²)` in the space `V_w` of homogeneous polynomials of degree `w`, with
`A + B = V_w`, so its trace on the period polynomials `W_w = A ∩ B` is its trace on `V_w`.

## Main results

* `LinearMap.trace_restrict_inf_eq_trace`: if `f` maps `A` and `B` into each other and
  `A ⊔ B = ⊤`, then the trace of `f` on `A ⊓ B` is the trace of `f`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, Proposition 3.
-/

public section

open Module Submodule

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Trace reduction to an intersection.** If `f` maps the subspaces `A` and `B` into each other
and `A ⊔ B = ⊤` (`Codisjoint A B`), then the trace of `f` is the trace of its restriction to
`A ⊓ B`. -/
theorem trace_restrict_inf_eq_trace {A B : Submodule K V} (hAB : Codisjoint A B) {f : V →ₗ[K] V}
    (hA : ∀ x ∈ A, f x ∈ B) (hB : ∀ x ∈ B, f x ∈ A) :
    trace K (A ⊓ B : Submodule K V) (f.restrict fun x hx ↦ ⟨hB x hx.2, hA x hx.1⟩) =
      trace K V f := by
  set C := A ⊓ B
  have hC : ∀ x ∈ C, f x ∈ C := fun x hx ↦ ⟨hB x hx.2, hA x hx.1⟩
  -- `trace f` is the trace on `C` plus the trace of the induced map on `V ⧸ C`
  rw [trace_eq_add_of_exact C.injective_subtype C.mkQ_surjective (exact_subtype_mkQ C)
    (fN := f.restrict hC) (fQ := C.mapQ C f hC) rfl rfl, left_eq_add]
  -- in `V ⧸ C` the images of `A` and `B` are complementary, and `mapQ` exchanges them
  have hcompl : IsCompl (A.map C.mkQ) (B.map C.mkQ) := isCompl_map_mkQ_iff.2
    ⟨by rw [sup_of_le_right inf_le_left, sup_of_le_right inf_le_right],
      by rw [codisjoint_iff.1 hAB, sup_top_eq]⟩
  refine trace_eq_zero_of_mapsTo_ne (N := ![A.map C.mkQ, B.map C.mkQ])
    ((DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one (Set.ext <| by decide)).2 hcompl)
    (· + 1) (by decide) (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> rintro _ ⟨x, hx, rfl⟩
  exacts [⟨f x, hA x hx, rfl⟩, ⟨f x, hB x hx, rfl⟩]

end LinearMap
