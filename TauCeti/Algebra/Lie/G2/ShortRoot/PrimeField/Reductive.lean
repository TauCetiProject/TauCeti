/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.Connected
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.UnipotentRadical
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Smooth

/-!
# Reductivity of the short-root G₂ carrier over `𝔽₃`

The short-root type-`G₂` carrier over `𝔽₃` is the closed subgroup scheme of `GL₇` generated
by four numbered root subgroups and a rank-two weight torus. It is reductive: smooth,
geometrically connected, and with no nontrivial connected normal smooth unipotent subgroup
after extension to an algebraic closure.

The geometric fibre is identified with the subgroup generated after scalar extension by
`TauCeti.G2ShortRoot.PrimeField.coordinateHopfAlgebraGeneratedIso`. The latter's faithful
simple seven-dimensional standard representation eliminates normal smooth unipotent subgroups,
as proved in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.UnipotentRadical`.

This proves reductivity of the constructed carrier. Identification with the pinned simply
connected group of type `G₂` also requires maximal-torus and root-datum recognition.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapter 19.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

/-- The prime-field short-root type-`G₂` carrier as a finite-type commutative Hopf algebra. -/
abbrev finiteTypeCarrierAlgebra : FiniteTypeCommHopfAlgCat (ZMod 3) :=
  ⟨carrierAlgebra, inferInstanceAs (Algebra.FiniteType (ZMod 3) carrierAlgebra)⟩

-- The scalar-extension and reductivity argument follows the type-`F₄` companion in
-- `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Reductive`. Transport uses
-- `TauCeti.reductiveCommHopfAlgProperty_of_geometricFiber_iso`.
/-- The short-root type-`G₂` carrier over `𝔽₃` is reductive: smooth and geometrically connected,
with trivial geometric unipotent radical. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCarrierAlgebra :
    reductiveCommHopfAlgProperty (ZMod 3) finiteTypeCarrierAlgebra :=
  reductiveCommHopfAlgProperty_of_geometricFiber_iso (ZMod 3) finiteTypeCarrierAlgebra
    (finiteTypeGeneratedCoordinateHopfAlgebra (AlgebraicClosure (ZMod 3)))
    algebraSmooth_carrierAlgebra geometricallyConnectedCommHopfAlgProperty_carrierAlgebra
    (ObjectProperty.isoMk _ (coordinateHopfAlgebraGeneratedIso _))
    (eq_augmentation_of_isNormal_of_smoothUnipotent _)

end

end TauCeti.G2ShortRoot.PrimeField
