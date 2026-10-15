/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Finite
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.GeometricallyReduced
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The exceptional G₂ endomorphism is an isogeny

The exceptional endomorphism of the short-root G₂ carrier over `𝔽₃` is finite and faithfully
flat. Its Frobenius-square identity gives dominance, and smoothness of the carrier makes its
coordinate algebra geometrically reduced; the finite dominant homomorphism criterion then gives
faithful flatness. The result is stated both on coordinate Hopf algebras and on the carrier group
scheme.

This is the group-scheme isogeny consumed by the Suzuki–Ree construction, separate from the
pointwise bijectivity of the map on the algebraic closure.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* J. S. Milne, *Algebraic Groups* (2017), Propositions 1.65(a) and 1.70.

The coordinate endomorphism, its Frobenius square, finiteness, and prime-spectrum dominance are
established in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.{SpecialIsogeny,Finite}`. The proof
pattern for the corresponding F₄ carrier is in
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Isogeny`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

local notation "𝔽₃" => ZMod 3

/-- The exceptional coordinate endomorphism of the short-root G₂ carrier is an isogeny. -/
theorem isIsogeny_specialIsogenyCoordinateMap :
    CommHopfAlgCat.IsIsogeny specialIsogenyCoordinateMap := by
  have hsmooth : Algebra.Smooth 𝔽₃ carrierAlgebra := algebraSmooth_carrierAlgebra
  let _ : Algebra.IsGeometricallyReduced 𝔽₃ carrierAlgebra :=
    @isGeometricallyReduced_of_smooth 𝔽₃ carrierAlgebra _ _ _ hsmooth
  exact (CommHopfAlgCat.isIsogeny_iff_finite_and_dominant
    specialIsogenyCoordinateMap).2
      ⟨finite_specialIsogenyCoordinateMap,
        comap_specialIsogenyCoordinateMap_involutive.surjective.denseRange⟩

/-- The exceptional endomorphism of the short-root G₂ carrier group scheme is an isogeny. -/
theorem isIsogeny_specialIsogenyHom : GroupScheme.IsIsogeny specialIsogenyHom := by
  rw [specialIsogenyHom_eq_map_specialIsogenyCoordinateMap]
  apply GroupScheme.IsIsogeny.comp
  · exact GroupScheme.isIsogeny_of_isIso _
  · apply GroupScheme.IsIsogeny.comp
    · exact (CommHopfAlgCat.isIsogeny_iff_isIsogeny_hopfSpec_map
        specialIsogenyCoordinateMap).mp isIsogeny_specialIsogenyCoordinateMap
    · exact GroupScheme.isIsogeny_of_isIso _

end

end TauCeti.G2ShortRoot.PrimeField
