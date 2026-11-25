/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.SchemeMap

/-!
# Properness of projective orbits descends to larger subgroups

Let `G` be an affine group of finite type over an algebraically closed field and let `P ⊆ Q` be
closed subgroups. If a projective orbit scheme representing `G/P` is proper over the base field,
then every projective orbit scheme representing `G/Q` is proper. The projection `G/P ⟶ G/Q` is
induced by a surjective morphism of the representing orbit schemes
(`CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap`), so universal closedness descends, and the
orbit scheme of `G/Q` is separated and of finite type as a subscheme of projective space.

Applied to a Borel subgroup `P`, whose homogeneous quotient is complete, this shows that `G/Q` is
proper for every closed subgroup `Q` containing a Borel subgroup.

## Main declarations

* `Comodule.isProper_projectiveOrbitToSpec_of_le`: properness of a projective orbit
  representing `G/P` implies properness of any projective orbit representing `G/Q`, for `P ⊆ Q`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.16.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
  {M' : Type u} [AddCommGroup M'] [Module k M'] [Comodule k H M'] [Module.Finite k M']

/-- **Properness of projective orbits descends to larger subgroups.** Let `I` define a closed
subgroup `P` and `J ≤ I` a closed subgroup `Q ⊇ P`. If the projective orbit of `m` represents
`G/P` and is proper over the base field, then any projective orbit of `m'` representing `G/Q` is
proper over the base field. The representing isomorphisms are arbitrary. -/
theorem isProper_projectiveOrbitToSpec_of_le {I J : HopfIdeal k H} (hJI : J ≤ I)
    {m : M} {hm : Module.IsUnimodular k m} {m' : M'} {hm' : Module.IsUnimodular k m'}
    (e : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ projectiveOrbitPointsSheaf (H := H) m hm)
    (e' : CommHopfAlgCat.fppfHomogeneousQuotient H J ≅
      projectiveOrbitPointsSheaf (H := H) m' hm')
    [IsProper (projectiveOrbitToSpec (H := H) m hm)] :
    IsProper (projectiveOrbitToSpec (H := H) m' hm') := by
  -- The structure morphism of `Over.mk f` is `f` itself.
  have : IsProper (Over.mk (projectiveOrbitToSpec (H := H) m hm)).hom :=
    inferInstanceAs (IsProper (projectiveOrbitToSpec (H := H) m hm))
  have : IsSeparated (Over.mk (projectiveOrbitToSpec (H := H) m' hm')).hom :=
    inferInstanceAs (IsSeparated (projectiveOrbitToSpec (H := H) m' hm'))
  have : LocallyOfFiniteType (Over.mk (projectiveOrbitToSpec (H := H) m' hm')).hom :=
    inferInstanceAs (LocallyOfFiniteType (projectiveOrbitToSpec (H := H) m' hm'))
  exact CommHopfAlgCat.isProper_hom_of_le H hJI (e ≪≫ eqToIso (projectiveOrbitPointsSheaf_eq m hm))
    (e' ≪≫ eqToIso (projectiveOrbitPointsSheaf_eq m' hm'))

end TauCeti.Comodule
