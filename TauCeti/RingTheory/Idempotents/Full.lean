/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Jacobson.Semiperfect
public import TauCeti.RingTheory.TwoSidedIdeal.Span

/-!
# Lifting full idempotents modulo the Jacobson radical

A full idempotent is one generating the entire ring as a two-sided ideal. In a semiperfect
ring, every full idempotent of the radical quotient lifts to a full idempotent of the ring.
Idempotent lifting is supplied by semiperfectness, and any lift retains fullness because
the Jacobson radical cannot contribute to generation of the unit ideal.

This permits a full idempotent selected in a semisimple radical quotient to define a Morita
equivalence with its lifted corner ring. In particular it applies to finite-dimensional
algebras, which are semiperfect. No choice of matrix decomposition or base field is needed.

The construction uses `TauCeti.IsSemiperfectRing.exists_isIdempotentElem_eq` and
`RingHom.twoSidedIdeal_span_image_eq_top_iff`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Sections I.4 and I.6.
-/

public section

namespace TauCeti.IsSemiperfectRing

variable {R : Type*} [Ring R] [IsSemiperfectRing R]

/-- A full idempotent of the radical quotient of a semiperfect ring lifts to a full idempotent
of the ring, with the specified quotient image. -/
theorem exists_isIdempotentElem_full_eq (e : R ⧸ Ring.jacobson R)
    (he : IsIdempotentElem e) (hfull : TwoSidedIdeal.span {e} = ⊤) :
    ∃ f : R, IsIdempotentElem f ∧ Ideal.Quotient.mk (Ring.jacobson R) f = e ∧
      TwoSidedIdeal.span {f} = ⊤ := by
  obtain ⟨f, hf, hfe⟩ := exists_isIdempotentElem_eq e he
  refine ⟨f, hf, hfe, ?_⟩
  apply ((Ideal.Quotient.mk (Ring.jacobson R)).twoSidedIdeal_span_image_eq_top_iff
    Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]) {f}).mp
  simpa [hfe] using hfull

end TauCeti.IsSemiperfectRing
