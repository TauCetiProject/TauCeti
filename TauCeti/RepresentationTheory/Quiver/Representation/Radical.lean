/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Multiplicity
public import TauCeti.RepresentationTheory.Quiver.Representation.KrullSchmidt
public import TauCeti.RepresentationTheory.Quiver.Representation.Fitting
public import TauCeti.RepresentationTheory.Quiver.Representation.HomDifferential

/-!
# Dimensions of quiver morphisms modulo the radical

For a pointwise finite-dimensional indecomposable representation `X` and any pointwise
finite-dimensional representation `Y`, the dimensions of `Hom(X, Y) / rad` and
`Hom(Y, X) / rad` agree. Both count the copies of `X` in a Krull–Schmidt decomposition of `Y`,
weighted by the dimension of the residue division algebra of `End(X)`.

In an almost-split sequence, these dimensions compute the incoming and outgoing arrow
multiplicities at the two ends. No algebraic closedness or acyclicity is required.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]
  {X Y : QuiverRep.{u, v, w, t} k Q}

/-- For a finite-dimensional indecomposable `X` and a finite-dimensional `Y`, morphisms in
either direction have the same dimension modulo the radical. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_symm (hX : IsFinDim k Q X)
    (hI : Indecomposable X) (hY : IsFinDim k Q Y) :
    Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Module.finrank k ((Y ⟶ X) ⧸ jacobsonRadicalSubmodule k Y X) := by
  obtain ⟨n, P, hP, hfin, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct Y hY
  have : IsLocalRing (End X) := (indecomposable_iff_isLocalRing_end hX).mp hI
  have : ∀ j, IsLocalRing (End (P j)) :=
    fun j ↦ (indecomposable_iff_isLocalRing_end (hfin j)).mp (hP j)
  have : ∀ j, FiniteDimensional k (P j ⟶ X) :=
    fun j ↦ finiteDimensional_hom (hfin j) hX
  have : ∀ j, FiniteDimensional k (X ⟶ P j) :=
    fun j ↦ finiteDimensional_hom hX (hfin j)
  exact TauCeti.finrank_quotient_jacobsonRadicalSubmodule_symm_of_iso_biproduct k P e

end TauCeti.QuiverRep
