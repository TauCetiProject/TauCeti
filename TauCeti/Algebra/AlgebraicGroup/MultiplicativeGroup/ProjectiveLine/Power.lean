/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.ProjectiveLine.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.ProjectiveOrbit

/-!
# Power-twisted scaling has the same projective orbits

Restricting a representation of the multiplicative group along `t ↦ tⁿ`, for `n > 0`,
preserves the full images of its projective orbit morphisms. The power morphism is
surjective on spectra by integrality and lying over; surjectivity on rational points
is neither assumed nor needed.

For the scaling representation on two coordinates this gives `t • [u : v] = [tⁿ u : v]`.
Its orbit of `[1 : 1]` is the complement of the two coordinate points, with those two
points as its boundary. In characteristic `p`, take `n = p`: the orbit is unchanged even
though the orbit map can be inseparable. These are statements about all scheme points,
not just closed or rational points. No smoothness assertion about stabilizers follows.

The restriction uses the existing `Comodule.Corestrict` construction rather than a
second diagonal representation.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f and §12.c.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§1.8 and 6.7.
-/

public section

open CategoryTheory AlgebraicGeometry LaurentPolynomial TauCeti.Comodule

namespace TauCeti.MultiplicativeGroup

universe u

variable (R : Type u) [CommRing R]

attribute [local instance] scalingComodule

/-- The restriction of the standard scaling representation along `t ↦ tⁿ` acts by
`(u, v) ↦ (tⁿ u, v)`. This formula also includes the trivial action at `n = 0`. -/
theorem basePointsRepresentation_corestrict_power (n : ℕ) (t : Rˣ) (v : Fin 2 → R) :
    (letI : Comodule R R[T;T⁻¹] (Fin 2 → R) := Corestrict
        (AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulRight (n : ℤ))).toCoalgHom
     basePointsRepresentation (H := R[T;T⁻¹]) (Fin 2 → R) (pointsMulEquiv.symm t) v) =
      ![(t : R) ^ n * v 0, v 1] := by
  rw [basePointsRepresentation_corestrict]
  have hpoint : BialgHom.mapDomain
      (AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulRight (n : ℤ)))
      (pointsMulEquiv.symm t) = (pointsMulEquiv (R := R)).symm (t ^ n) := by
    rw [pointsMulEquiv_symm_apply, BialgHom.mapDomain_apply,
      pointsMulEquiv_symm_apply]
    congr 1
    convert laurentEval_comp_mapDomainAlgHom_mulRight (R := R) t (n : ℤ) using 1
    ext x
    rfl
  rw [hpoint, basePointsRepresentation_pointsMulEquiv_symm]
  simp

section Field

variable (k : Type u) [Field k] {n : ℕ}

/-- Under `t • [u : v] = [tⁿ u : v]`, for `n > 0`, the orbit of `[1 : 1]` is exactly
the complement of the two coordinate points. This includes `n = p` in characteristic `p`. -/
theorem range_projectiveOrbitMap_one_corestrict_power (hn : 0 < n) :
    (letI : Comodule k k[T;T⁻¹] (Fin 2 → k) := Corestrict
        (AddMonoidAlgebra.mapDomainBialgHom k (AddMonoidHom.mulRight (n : ℤ))).toCoalgHom
     Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k))) =
      {projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 0 1) (isUnimodular_single k 0)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])),
        projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 1 1) (isUnimodular_single k 1)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))}ᶜ := by
  rw [range_projectiveOrbitMap_corestrict_power k hn, range_projectiveOrbitMap_one]

/-- The boundary of the power-twisted open orbit is the two coordinate points, in every
characteristic, even when the power vanishes in the field. -/
theorem closure_diff_range_projectiveOrbitMap_one_corestrict_power (hn : 0 < n) :
    (letI : Comodule k k[T;T⁻¹] (Fin 2 → k) := Corestrict
        (AddMonoidAlgebra.mapDomainBialgHom k (AddMonoidHom.mulRight (n : ℤ))).toCoalgHom
     closure (Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k)
         (isUnimodular_one k))) \
       Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k))) =
      {projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 0 1) (isUnimodular_single k 0)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])),
        projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 1 1) (isUnimodular_single k 1)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))} := by
  simp only [range_projectiveOrbitMap_corestrict_power k hn,
    closure_diff_range_projectiveOrbitMap_one]

end Field

end TauCeti.MultiplicativeGroup
