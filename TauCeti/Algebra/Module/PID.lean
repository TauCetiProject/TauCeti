/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PID
public import TauCeti.RingTheory.KrullSchmidt.DirectSum

/-!
# Indecomposable torsion modules over a principal ideal domain

Mathlib's structure theorem `Module.equiv_directSum_of_isTorsion` decomposes a finitely generated
torsion module over a principal ideal domain `R` as a finite direct sum of cyclic primary modules
`R ⧸ R ∙ p ^ e`, with `p` irreducible. An indecomposable module has room for only one nonzero
summand, so it is itself cyclic primary. This is the form of the structure theorem used to
classify the indecomposable modules over a quotient of `R`: for instance, the finite-dimensional
modules over the truncated polynomial algebra `k[X]/(Xⁿ)` are the `k[X]`-modules killed by `Xⁿ`.

## Main results

* `TauCeti.exists_linearEquiv_quotient_pow_of_isIndecomposableModule`: a finitely generated
  torsion module over a principal ideal domain that is indecomposable is isomorphic to
  `R ⧸ R ∙ p ^ e` for some irreducible `p` and some `e > 0`.
-/

public section

namespace TauCeti

open scoped DirectSum

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- **An indecomposable finitely generated torsion module over a principal ideal domain is cyclic
primary**: it is isomorphic to `R ⧸ R ∙ p ^ e` for an irreducible `p` and a positive exponent
`e`. -/
theorem exists_linearEquiv_quotient_pow_of_isIndecomposableModule [Module.Finite R M]
    (hM : Module.IsTorsion R M) (h : IsIndecomposableModule R M) :
    ∃ p : R, Irreducible p ∧ ∃ e : ℕ, 0 < e ∧ Nonempty (M ≃ₗ[R] R ⧸ R ∙ p ^ e) := by
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_directSum_of_isTorsion hM
  obtain ⟨i, ⟨g⟩⟩ := h.exists_nonempty_linearEquiv_of_directSum f
  refine ⟨p i, hp i, e i, Nat.pos_of_ne_zero fun he ↦ ?_, ⟨g⟩⟩
  -- A zero exponent leaves the quotient of `R` by the unit ideal, which `M` cannot be.
  have := h.nontrivial
  have : Subsingleton (R ⧸ R ∙ p i ^ e i) := by
    rw [he, pow_zero, Submodule.Quotient.subsingleton_iff, ← Ideal.span, Ideal.span_singleton_one]
  exact not_subsingleton M g.toEquiv.subsingleton

end TauCeti
