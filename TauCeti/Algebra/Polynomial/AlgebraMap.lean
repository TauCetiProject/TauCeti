/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Irreducibility under algebra isomorphisms

Irreducibility of a polynomial after extending its coefficients is invariant under an
isomorphism of algebras over the coefficient ring.
-/

public section

namespace TauCeti

open Polynomial

/-- Extending coefficients to isomorphic algebras preserves irreducibility. -/
theorem irreducible_map_iff_of_algEquiv {F K K' : Type*} [CommSemiring F] [Semiring K]
    [Semiring K'] [Algebra F K] [Algebra F K'] (ψ : K ≃ₐ[F] K') (g : F[X]) :
    Irreducible (g.map (algebraMap F K)) ↔ Irreducible (g.map (algebraMap F K')) := by
  have hψ : (ψ.toRingEquiv : K →+* K').comp (algebraMap F K) = algebraMap F K' :=
    RingHom.ext ψ.commutes
  rw [← MulEquiv.irreducible_iff (mapEquiv ψ.toRingEquiv), mapEquiv_apply, Polynomial.map_map,
    hψ]

end TauCeti
