/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic

/-!
# Intersections of polynomial ideals using an auxiliary variable

For generating sets `s` and `t`, adjoining the variable `X none` and using the generators
`X none * rename some f` for `f ∈ s` and `(1 - X none) * rename some g` for `g ∈ t`
reduces intersection to contraction along `rename some`.

The order-independent contraction formula is
`Ideal.span_inf_span_eq_comap_rename_some`. Given a Gröbner basis of this auxiliary ideal,
a remainder of `rename some f` vanishes
exactly when `f` belongs to both original ideals. Thus an ordinary Gröbner membership
certificate in one more variable certifies membership in the intersection, without requiring
an elimination order. This does not construct a Gröbner basis of the intersection itself.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 4, §3,
  computing intersections by elimination.
-/

public section

open MvPolynomial

namespace MonomialOrder

variable {σ R : Type*} [CommRing R] {m : MonomialOrder (Option σ)}
  {G : Set (MvPolynomial (Option σ) R)} {s t : Set (MvPolynomial σ R)}
  {f : MvPolynomial σ R} {r : MvPolynomial (Option σ) R}

/-- A remainder modulo a Gröbner basis of the added-variable ideal vanishes exactly on the
intersection. Only the given remainder, not its existence, is needed, so this equivalence
requires no unit leading coefficients. -/
theorem IsGroebnerBasis.remainder_eq_zero_iff_mem_inf
    (h : m.IsGroebnerBasis G
      (Ideal.span ((fun f ↦ X none * rename some f) '' s ∪
        (fun g ↦ (1 - X none) * rename some g) '' t)))
    (hr : m.IsRemainder (rename some f) G r) :
    r = 0 ↔ f ∈ Ideal.span s ⊓ Ideal.span t := by
  simpa only [Ideal.span_inf_span_eq_comap_rename_some, Ideal.mem_comap] using
    h.remainder_eq_zero_iff_mem hr

end MonomialOrder
