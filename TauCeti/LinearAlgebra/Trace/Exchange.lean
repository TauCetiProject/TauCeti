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
subspaces `A` and `B` into the other. Then `f` preserves `A ⊓ B` and `A ⊔ B`, and its traces on
the two agree. In particular, when `A ⊔ B = ⊤` the trace of `f` is the trace of its restriction to
`A ⊓ B`.

This is the linear algebra behind the trace reduction in Popa and Zagier's proof of the
Eichler–Selberg trace formula: their modified Hecke operator exchanges `A = ker(1 + S)` and
`B = ker(1 + U + U²)` in the space `V_w` of homogeneous polynomials of degree `w`, and over a field
of characteristic zero and for positive even `w` we have `A + B = V_w`, so its trace on the period
polynomials `W_w = A ∩ B` is its trace on `V_w`. This application is
`TauCeti.TraceFormulaMatrixModule.ExchangeRelations.trace_periodActionRestrict_eq_trace`.

## Main results

* `LinearMap.trace_restrict_inf_eq_trace_restrict_sup`: if `f` maps `A` and `B` into each other,
  then the traces of `f` on `A ⊓ B` and on `A ⊔ B` agree.
* `LinearMap.trace_restrict_inf_eq_trace`: if moreover `A ⊔ B = ⊤`, then the trace of `f` on
  `A ⊓ B` is the trace of `f`.

The proofs move traces between restrictions with two general lemmas:
`LinearMap.trace_restrict_congr` (the traces of `f` on equal submodules agree) and
`LinearMap.trace_restrict_restrict` (for `p ≤ q`, restricting `f` to `q` and then to `p`, viewed
inside `q`, has the same trace as restricting `f` to `p`).

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, Proposition 3.
-/

public section

open Module Submodule

namespace LinearMap

/-! ### Traces of restrictions -/

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The traces of the restrictions of `f` to equal submodules agree. -/
theorem trace_restrict_congr {p q : Submodule R M} (hpq : p = q) (f : M →ₗ[R] M)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    trace R p (f.restrict hp) = trace R q (f.restrict hq) := by
  subst hpq
  rfl

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Restriction in two steps.** If `f` preserves the submodules `p ≤ q`, then restricting `f`
to `q` and then to `p`, viewed as the submodule `p.comap q.subtype` of `q`, gives the same trace as
restricting `f` to `p` directly: the two restrictions are conjugate by
`Submodule.comapSubtypeEquivOfLe`. -/
theorem trace_restrict_restrict {p q : Submodule R M} (hpq : p ≤ q) {f : M →ₗ[R] M}
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q)
    (hpq' : ∀ x ∈ p.comap q.subtype, f.restrict hq x ∈ p.comap q.subtype := fun x hx ↦ hp x hx) :
    trace R (p.comap q.subtype) ((f.restrict hq).restrict hpq') = trace R p (f.restrict hp) := by
  have h : (comapSubtypeEquivOfLe hpq).conj ((f.restrict hq).restrict hpq') = f.restrict hp :=
    LinearMap.ext fun x ↦ Subtype.ext <| by simp [LinearEquiv.conj_apply]
  rw [← h, trace_conj']

end CommRing

/-! ### Endomorphisms exchanging two subspaces -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If `f` maps the subspaces `A` and `B` into each other and `A ⊔ B = ⊤` (`Codisjoint A B`), then
the trace of `f` is the trace of its restriction to `A ⊓ B`. -/
theorem trace_restrict_inf_eq_trace {A B : Submodule K V} (hAB : Codisjoint A B) {f : V →ₗ[K] V}
    (hA : ∀ x ∈ A, f x ∈ B) (hB : ∀ x ∈ B, f x ∈ A) :
    trace K (A ⊓ B : Submodule K V) (f.restrict fun x hx ↦ ⟨hB x hx.2, hA x hx.1⟩) =
      trace K V f := by
  set C := A ⊓ B
  have hC : ∀ x ∈ C, f x ∈ C := fun x hx ↦ ⟨hB x hx.2, hA x hx.1⟩
  -- `trace f` is the trace on `C` plus the trace of the induced map on `V ⧸ C`
  rw [trace_eq_add_of_exact C.injective_subtype C.mkQ_surjective (exact_subtype_mkQ C)
    (fN := f.restrict hC) (fQ := C.mapQ C f hC) (by ext; simp) (mapQ_mkQ C C f).symm,
    left_eq_add]
  -- in `V ⧸ C` the images of `A` and `B` are complementary, and `mapQ` exchanges them
  have hcompl : IsCompl (A.map C.mkQ) (B.map C.mkQ) := isCompl_map_mkQ_iff.2
    ⟨by rw [sup_of_le_right inf_le_left, sup_of_le_right inf_le_right],
      by rw [codisjoint_iff.1 hAB, sup_top_eq]⟩
  refine trace_eq_zero_of_mapsTo_ne (N := ![A.map C.mkQ, B.map C.mkQ])
    ((DirectSum.isInternal_submodule_iff_isCompl _ zero_ne_one (Set.ext <| by decide)).2 hcompl)
    (· + 1) (by decide) (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> rintro _ ⟨x, hx, rfl⟩
  exacts [⟨f x, hA x hx, by simp⟩, ⟨f x, hB x hx, by simp⟩]

/-- **Trace reduction to an intersection.** If `f` maps the subspaces `A` and `B` into each other,
then its traces on `A ⊓ B` and on `A ⊔ B` agree. -/
theorem trace_restrict_inf_eq_trace_restrict_sup {A B : Submodule K V} {f : V →ₗ[K] V}
    (hA : ∀ x ∈ A, f x ∈ B) (hB : ∀ x ∈ B, f x ∈ A) :
    trace K (A ⊓ B : Submodule K V) (f.restrict fun x hx ↦ ⟨hB x hx.2, hA x hx.1⟩) =
      trace K (A ⊔ B : Submodule K V) (f.restrict fun _ hx ↦
        (sup_le (fun x hx ↦ mem_sup_right (hA x hx)) (fun x hx ↦ mem_sup_left (hB x hx)) :
          A ⊔ B ≤ (A ⊔ B).comap f) hx) := by
  set U := A ⊔ B
  -- inside `U`, the preimages of `A` and `B` span, so the ambient case applies there
  have hcod : Codisjoint (A.comap U.subtype) (B.comap U.subtype) := by
    rw [codisjoint_iff]
    refine map_injective_of_injective U.injective_subtype ?_
    rw [Submodule.map_sup, map_comap_subtype, map_comap_subtype, map_subtype_top,
      inf_of_le_right le_sup_left, inf_of_le_right le_sup_right]
  rw [← trace_restrict_inf_eq_trace hcod (f := f.restrict _) (fun x hx ↦ hA x hx)
    (fun x hx ↦ hB x hx)]
  -- `A ⊓ B`, seen inside `U`, is `A.comap U.subtype ⊓ B.comap U.subtype`
  exact (trace_restrict_restrict inf_le_sup _ _).symm.trans
    (trace_restrict_congr (comap_inf A B U.subtype) _ _ _)

end LinearMap
