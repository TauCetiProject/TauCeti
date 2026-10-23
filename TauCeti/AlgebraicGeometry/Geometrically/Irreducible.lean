/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# Geometric irreducibility over an algebraically closed field

Over an algebraically closed field `K`, the spectrum of every domain is geometrically irreducible:
for every field `M` over `K`, the fibre product `Spec A ×_K Spec M ≅ Spec (A ⊗[K] M)` is irreducible
because `A ⊗[K] M` is a domain (`TauCeti.isDomain_tensorProduct_of_isAlgClosed`). In particular a
morphism `Spec L ⟶ Spec K` from the spectrum of a field extension is geometrically irreducible.

Such a morphism is also universally open, as is every morphism to the spectrum of a field. Hence,
for a scheme `X` over `K`, the projection `p : X ×_K Spec L ⟶ X` is geometrically irreducible and
open, and Mathlib's `AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv` identifies the
irreducible components of `X ×_K Spec L` with those of `X`: a component `E` of `X` corresponds to
its preimage `p ⁻¹' E`, and a component `E'` of `X ×_K Spec L` to its image `p '' E'`. So the
irreducible components of a geometric fibre do not depend on the chosen algebraically closed
field.

## Main results

* `TauCeti.AlgebraicGeometry.geometricallyIrreducible_Spec_of_isAlgClosed`: over an algebraically
  closed field, a morphism from the spectrum of a domain is geometrically irreducible.

## References

* The Stacks Project, Chapter *Varieties*, Section *Geometrically irreducible schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- Over an algebraically closed field `K`, every morphism `Spec A ⟶ Spec K` from the spectrum of a
domain is geometrically irreducible. -/
instance geometricallyIrreducible_Spec_of_isAlgClosed {K A : Type u} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] {g : Spec (.of A) ⟶ Spec (.of K)} : GeometricallyIrreducible g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  -- The fibre product is `Spec (A ⊗[K] M)`, the spectrum of a domain.
  exact (pullbackSpecIso K A M).inv.homeomorph.irreducibleSpace_iff.mp inferInstance

end AlgebraicGeometry

end TauCeti
