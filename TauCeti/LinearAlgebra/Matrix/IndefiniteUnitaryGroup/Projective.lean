/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup

/-!
# The projective indefinite unitary group `PU(p, q)` and its conjugation representation

The **projective indefinite unitary group** `PU(p, q)` is the quotient of the indefinite unitary
group `U(p, q)` (`TauCeti.Matrix.indefiniteUnitaryGroup`) by its centre. Over a field of
characteristic zero the centre is the group of unit scalars
(`TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`), so `PU(p, q)` is
`U(p, q) / U(1)`. For `p = Fin 1` and `q = Fin n` over `ℂ` this is the group `PU(1, n)` of
holomorphic isometries of complex hyperbolic `n`-space.

Conjugation `X ↦ g X g⁻¹` by a lift `g ∈ U(p, q)` defines the **conjugation representation**
`Ad : PU(p, q) →* Aut(M_{p ⊕ q}(K))` on the matrix algebra; it does not depend on the lift since
scalars act trivially, and it is injective: an element of `U(p, q)` whose conjugation is trivial is
central in the general linear group, hence central in `U(p, q)`
(`TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_comap_center`). It is the
representation through which neat subgroups of `PU(1, n)` are defined, by the eigenvalues of
`Ad(γ)`. The topological statements about `Ad` over `ℝ` and `ℂ` (it is a closed embedding) are in
`TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Projective`.

## Main definitions

* `TauCeti.Matrix.ProjectiveIndefiniteUnitaryGroup p q R`: the quotient `PU(p, q)` of `U(p, q)`
  by its centre.
* `TauCeti.Matrix.ProjectiveIndefiniteUnitaryGroup.innerAut`: the conjugation representation
  `PU(p, q) →* (M_{p ⊕ q}(K) ≃ₐ[K] M_{p ⊕ q}(K))`.

## Main results

* `TauCeti.Matrix.indefiniteUnitaryGroup.ker_innerAut_comp_subtype`: the kernel of conjugation
  restricted to `U(p, q)` is the centre of `U(p, q)`.
* `TauCeti.Matrix.ProjectiveIndefiniteUnitaryGroup.innerAut_injective`: the conjugation
  representation of `PU(p, q)` is faithful.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford Mathematical Monographs, Oxford University
  Press (1999), Chapter 3.
* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. 197 (2023), Section 2, for `PU(1, n)` as the quotient of `U(1, n)` by the unit
  scalars.
-/

public section

open Matrix

namespace TauCeti

namespace Matrix

variable (p q R : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [CommRing R]
  [StarRing R]

/-- The **projective indefinite unitary group** `PU(p, q)`: the quotient of the indefinite unitary
group `U(p, q)` by its centre, which over a field of characteristic zero is the group of unit
scalars (`TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`). For `U(1, n)` over
`ℂ` this is `PU(1, n)`, the holomorphic isometry group of complex hyperbolic `n`-space. -/
abbrev ProjectiveIndefiniteUnitaryGroup :=
  indefiniteUnitaryGroup p q R ⧸ Subgroup.center (indefiniteUnitaryGroup p q R)

variable {p q} {K : Type*} [Field K] [StarRing K] [CharZero K]

/-- Over a field of characteristic zero, the kernel of conjugation `X ↦ g X g⁻¹` restricted to
`U(p, q)` is the centre of `U(p, q)`. -/
theorem indefiniteUnitaryGroup.ker_innerAut_comp_subtype :
    (GeneralLinearGroup.innerAut.comp (indefiniteUnitaryGroup p q K).subtype).ker =
      Subgroup.center (indefiniteUnitaryGroup p q K) := by
  rw [← MonoidHom.comap_ker, GeneralLinearGroup.ker_innerAut,
    indefiniteUnitaryGroup.center_eq_comap_center]

namespace ProjectiveIndefiniteUnitaryGroup

/-- The **conjugation representation** `Ad` of `PU(p, q)` on the matrix algebra: the class of
`g ∈ U(p, q)` acts by the algebra automorphism `X ↦ g X g⁻¹`
(`Matrix.GeneralLinearGroup.innerAut`), which does not depend on the lift `g` because central
elements of `U(p, q)` are scalars. It is injective (`innerAut_injective`). -/
noncomputable def innerAut :
    ProjectiveIndefiniteUnitaryGroup p q K →*
      (Matrix (p ⊕ q) (p ⊕ q) K ≃ₐ[K] Matrix (p ⊕ q) (p ⊕ q) K) :=
  QuotientGroup.lift _ (GeneralLinearGroup.innerAut.comp (indefiniteUnitaryGroup p q K).subtype)
    indefiniteUnitaryGroup.ker_innerAut_comp_subtype.ge

/-- The conjugation representation of `PU(p, q)` on the class of `g ∈ U(p, q)` is conjugation by
`g`. -/
@[simp]
theorem innerAut_mk (g : indefiniteUnitaryGroup p q K) :
    innerAut (g : ProjectiveIndefiniteUnitaryGroup p q K) =
      GeneralLinearGroup.innerAut (g : GL (p ⊕ q) K) := by
  simp [innerAut]

/-- **The conjugation representation of `PU(p, q)` is faithful**: an element of `U(p, q)` acting
trivially by conjugation on the matrix algebra is central in the general linear group, hence
central in `U(p, q)`, hence trivial in `PU(p, q)`. -/
theorem innerAut_injective : Function.Injective (innerAut (p := p) (q := q) (K := K)) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    indefiniteUnitaryGroup.ker_innerAut_comp_subtype.symm

end ProjectiveIndefiniteUnitaryGroup

end Matrix

end TauCeti
