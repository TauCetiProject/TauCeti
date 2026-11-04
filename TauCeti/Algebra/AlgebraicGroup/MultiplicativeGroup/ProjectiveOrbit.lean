/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Naturality
import TauCeti.Algebra.Polynomial.Laurent.Power
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Projective orbits under power restriction of the multiplicative group

Restricting a representation of the multiplicative group along `t ↦ tⁿ`, for `n > 0`,
preserves the full images of its projective orbit morphisms over any commutative base ring.
The power morphism is surjective on spectra by integrality and lying over; surjectivity
on rational points is neither assumed nor needed. Restriction uses the existing
`Comodule.Corestrict` construction.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f and §12.c.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§1.8 and 6.7.
-/

public section

open CategoryTheory AlgebraicGeometry LaurentPolynomial TauCeti.Comodule

namespace TauCeti.MultiplicativeGroup

universe u

variable (R : Type u) [CommRing R]

/-- Restriction along a positive power morphism of the multiplicative group preserves
projective orbit images over any commutative base ring, including their nonclosed points. -/
@[simp]
theorem range_projectiveOrbitMap_corestrict_power
    {M : Type u} [AddCommMonoid M] [Module R M] [Comodule R R[T;T⁻¹] M]
    [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} (hn : 0 < n) (m : M) (hm : Module.IsUnimodular R m) :
    (letI : Comodule R R[T;T⁻¹] M := Corestrict
        (AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulRight (n : ℤ))).toCoalgHom
     Set.range (projectiveOrbitMap (H := R[T;T⁻¹]) m hm)) =
      Set.range (projectiveOrbitMap (H := R[T;T⁻¹]) m hm) := by
  have hinj : Function.Injective (AddMonoidAlgebra.mapDomainRingHom R
      (AddMonoidHom.mulRight (n : ℤ))) :=
    AddMonoidAlgebra.mapDomain_injective (mul_left_injective₀ (by exact_mod_cast hn.ne'))
  have hsurj := (LaurentPolynomial.isIntegral_mapDomain_mulRight R hn).comap_surjective hinj
  rw [BialgHom.projectiveOrbitMap_corestrict]
  have hcomp : ⇑(Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom R
          (AddMonoidHom.mulRight (n : ℤ))).toAlgHom.toRingHom) ≫
        projectiveOrbitMap (H := R[T;T⁻¹]) m hm) =
      (projectiveOrbitMap (H := R[T;T⁻¹]) m hm) ∘ PrimeSpectrum.comap
        (AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.mulRight (n : ℤ))) := by
    funext x
    rw [Scheme.Hom.comp_apply, Spec.map_apply]
    rfl
  rw [hcomp]
  exact hsurj.range_comp _

end TauCeti.MultiplicativeGroup
