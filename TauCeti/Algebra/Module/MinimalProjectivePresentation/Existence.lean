/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic
public import TauCeti.Algebra.Module.ProjectiveCover.Existence

/-!
# Existence of minimal projective presentations over a semiprimary ring

`TauCeti/Algebra/Module/MinimalProjectivePresentation/Basic.lean` develops a minimal projective
presentation `P₁ → P₀ → M → 0` as a *given* datum: it is a quotient of every projective
presentation, and it is unique up to isomorphism of the whole diagram, but nothing there produces
one. This file supplies the existence theorem, over the same class of rings that carries projective
covers: over a **semiprimary** ring — Mathlib's `IsSemiprimaryRing`, as a finite-dimensional algebra
is — **every** module has a minimal projective presentation
(`TauCeti.exists_isMinimalProjectivePresentation`), with no finiteness hypothesis on the module.

## The construction

A minimal projective presentation is two projective covers stacked, and
`TauCeti.IsProjectiveCover.isMinimalProjectivePresentation` is the step that stacks them: a cover
`p₀ : P₀ ↠ M`, followed by a cover of the syzygy `ker p₀` pushed back into `P₀` along the inclusion
of the syzygy. So there is nothing to prove beyond applying `TauCeti.exists_isProjectiveCover`
twice, and the only thing worth saying is why the second application is available. Over a
semiperfect ring it would not be, at least not in this generality: semiperfectness guarantees a
projective cover only for the finitely generated modules, so the syzygy would have to be proved
finitely generated before a cover of it could be produced, and that is a noetherian hypothesis on
`P₀`, hence on the ring. A semiprimary ring covers *every* module, so the second step is the first
step again and the presented module may be arbitrary.

Finite generation is therefore not part of the existence statements, and a consumer that needs it
reads it off the presentation they produce: `TauCeti.IsProjectiveCover.finite` makes the middle term
finitely generated as soon as `M` is, with no hypothesis on the ring at all, and
`TauCeti.IsMinimalProjectivePresentation.finite` makes the left-hand source finitely generated as
soon as the middle term is noetherian, noetherianity being what makes the syzygy cut out of the
middle term finitely generated. So `obtain`ing a presentation of a finitely generated module over a
semiprimary noetherian ring, reading off `Module.Finite R P₀` by `h.isProjectiveCover.finite` —
which makes `P₀` noetherian over a noetherian ring — and applying `h.finite` gives a minimal
presentation by finitely generated projectives, which is the form the Auslander-Reiten transpose
consumes, its vanishing criterion asking for a finitely generated left-hand source. A
finite-dimensional algebra is Artinian, hence both semiprimary and noetherian, so a consumer
working over one installs `IsArtinianRing.of_finite` and `IsNoetherianRing.of_finite` and applies
these statements as they stand.

## The shape of the statements

The carriers of the two projective modules are quantified over, together with their module
structures, rather than named. They *could* be named: the covers produced by
`TauCeti.exists_isProjectiveCover` are submodules of free modules on the underlying set of the
module covered, which is how that theorem states its conclusion. But a submodule carries its own
additive structure rather than the one an `[AddCommGroup P]` binder builds, and the cover API is
stated over such binders — a covering module has to be an additive group for minimality to be usable
at all — so a statement naming the submodule would force every consumer to pin instances by hand
before applying a single lemma about covers. Quantifying over the structures hands the consumer
exactly the binders the API is written against. The universe is then forced rather than chosen: the
free module on the underlying set of a module in `Type v` over a ring in `Type u` lives in
`Type (max u v)`.

## Main statements

* `TauCeti.IsProjectiveCover.exists_isMinimalProjectivePresentation`: over a semiprimary ring
  **every projective cover extends to a minimal projective presentation**, by a cover of its
  syzygy.
* `TauCeti.exists_isMinimalProjectivePresentation`: **every module over a semiprimary ring has a
  minimal projective presentation.**

## References

The Auslander-Reiten transpose `Tr` and the translate `τ = D Tr` are read off a minimal projective
presentation of the module, so they are defined at all only where one exists; that is what the
statements here supply, and what makes those constructions unconditional over a finite-dimensional
algebra.

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section I.2.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Section I.5.
-/

public section

namespace TauCeti

universe u v w

section Semiprimary

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **Every projective cover extends to a minimal projective presentation**, over a semiprimary
ring. The left-hand source is a projective cover of the syzygy `ker p₀`, which exists because a
semiprimary ring covers every module, the syzygy among them, and the left-hand map is that cover
followed by the inclusion of the syzygy, as in
`TauCeti.IsProjectiveCover.isMinimalProjectivePresentation`.

By uniqueness of a minimal projective presentation
(`TauCeti.IsMinimalProjectivePresentation.exists_linearEquiv`) the extension is unique up to
isomorphism, so the given cover already determines the whole presentation. -/
theorem IsProjectiveCover.exists_isMinimalProjectivePresentation [IsSemiprimaryRing R]
    {P₀ : Type w} [AddCommGroup P₀] [Module R P₀] {p₀ : P₀ →ₗ[R] M}
    (h₀ : IsProjectiveCover p₀) :
    ∃ (P₁ : Type max u w) (_ : AddCommGroup P₁) (_ : Module R P₁) (p₁ : P₁ →ₗ[R] P₀),
      IsMinimalProjectivePresentation p₁ p₀ := by
  obtain ⟨P₁, h₁⟩ := exists_isProjectiveCover R ↥(LinearMap.ker p₀)
  exact ⟨↥P₁, inferInstance, inferInstance,
    (LinearMap.ker p₀).subtype ∘ₗ (Finsupp.linearCombination R id ∘ₗ P₁.subtype),
    h₀.isMinimalProjectivePresentation h₁⟩

variable (R M) in
/-- **Every module over a semiprimary ring has a minimal projective presentation.**

The middle term is the projective cover of `M` supplied by `TauCeti.exists_isProjectiveCover`, and
the left-hand source is a projective cover of the syzygy that cover cuts out. No finiteness is
assumed of `M`: a semiprimary ring is left perfect, so it covers every module, and the two covers
making up a presentation are available for the same reason. -/
theorem exists_isMinimalProjectivePresentation [IsSemiprimaryRing R] :
    ∃ (P₀ : Type max u v) (_ : AddCommGroup P₀) (_ : Module R P₀) (p₀ : P₀ →ₗ[R] M)
      (P₁ : Type max u v) (_ : AddCommGroup P₁) (_ : Module R P₁) (p₁ : P₁ →ₗ[R] P₀),
      IsMinimalProjectivePresentation p₁ p₀ := by
  obtain ⟨P₀, h₀⟩ := exists_isProjectiveCover R M
  -- The covering module is a submodule, so its additive group structure is pinned by hand here:
  -- read off the submodule, it is not the structure the binders of the cover API build.
  obtain ⟨P₁, _, _, p₁, h⟩ := IsProjectiveCover.exists_isMinimalProjectivePresentation
    (P₀ := ↥P₀) (p₀ := Finsupp.linearCombination R id ∘ₗ P₀.subtype) h₀
  exact ⟨↥P₀, inferInstance, inferInstance, _, P₁, inferInstance, inferInstance, p₁, h⟩

end Semiprimary

end TauCeti
