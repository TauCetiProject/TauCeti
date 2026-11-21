/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.BaseChange
public import TauCeti.RingTheory.Henselian.FiniteEtale

/-!
# Lifting finite étale schemes over henselian pairs

Every finite étale scheme over `Spec (R/I)` lifts to a finite étale scheme over `Spec R`
when `(R, I)` is henselian. The result concerns the actual pullback functor on schemes,
not a transported functor defined by choosing coordinate algebras. This supplies geometric
lifts of covers of a hypersurface section, including sections of complete local schemes.

We use the finite étale algebra lifting theorem
`CommAlgCat.FiniteEtale.essSurj_baseChange_quotient`, the affine anti-equivalence
`TauCeti.FiniteEtaleScheme.spec`, and
`TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv` to identify the lift's pullback.
Only essential surjectivity is asserted here, not full faithfulness.

## References

* The Stacks Project, Lemma 15.13.2 (09ZL), finite étale algebras over a henselian pair.
* The Stacks Project, Lemma 58.20.7 (0BLM), lifting the cover of the hypersurface section.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

/-- Every finite étale scheme over a henselian quotient lifts to the original affine base.
No Noetherianity, locality or completeness assumption is required. -/
@[stacks 09ZL "essential surjectivity, in terms of finite étale schemes"]
instance essSurj_pullback_quotient (R : Type u) [CommRing R] (I : Ideal R)
    [HenselianRing R I] :
    (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).EssSurj :=
  essSurj_pullback_of_essSurj_baseChange R (R ⧸ I)

end TauCeti.FiniteEtaleScheme
