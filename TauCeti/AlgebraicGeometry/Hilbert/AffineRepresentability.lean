/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Hilbert.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Hilbert.Representability

/-!
# Hilbert functors of affine schemes

Every affine scheme over an affine base embeds as a closed subscheme of an affine space,
with no finiteness assumption on the set of coordinates. Its functor of finite locally
free closed subschemes is therefore represented by a closed subscheme of the affine-space
Hilbert scheme.
-/

public section

noncomputable section

universe u

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Hilbert

/-- The Hilbert functor of finite locally free degree-`d` closed subschemes of an affine
scheme over an affine base is representable. -/
theorem isRepresentable_hilbertFunctor_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] (d : ℕ) : (hilbertFunctor f d).IsRepresentable := by
  let i : X ⟶ 𝔸(Γ(X, ⊤); S) := AffineSpace.homOfVector f id
  have : IsClosedImmersion i := .of_surjective_of_isAffine i fun a ↦
    ⟨AffineSpace.coord S a, AffineSpace.homOfVector_appTop_coord f id a⟩
  rw [← AffineSpace.homOfVector_over f id]
  exact isRepresentable_hilbertFunctor_of_isClosedImmersion i _ d
    (isRepresentable_hilbertFunctor_affineSpace _ S d)

end AlgebraicGeometry.Hilbert
