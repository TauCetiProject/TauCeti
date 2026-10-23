/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Homogeneous
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance

/-!
# Faithfully flat projective orbit morphisms

For a reduced finite-type affine group over an algebraically closed field, the morphism
onto the projective orbit scheme of a line is flat. Together with its existing surjectivity
and local finite presentation, this makes it an fppf cover, the cover needed to descend
morphisms to the homogeneous space of the line stabilizer.

Generic flatness supplies a dense open subset of the orbit over which the morphism is flat.
Rational group translations preserve the scheme morphism and move any closed orbit point
to any other. Their translates of the flat open cover the Jacobson orbit scheme, so flatness
holds at every stalk, including nonclosed points. No connectedness or characteristic-zero
assumption is needed. Reducedness is used to apply generic flatness to the orbit scheme.

The proof combines `Comodule.exists_projectiveOrbitTranslation_eq_of_mem_closedPoints` and
`Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [_root_.IsReduced H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The surjective morphism from a reduced finite-type affine group onto the projective
orbit scheme of a line is flat. In particular, it is an fppf cover. -/
instance instFlatToProjectiveOrbit (m : M) (hm : Module.IsUnimodular k m) :
    Flat (toProjectiveOrbit (H := H) m hm) := by
  let f := toProjectiveOrbit (H := H) m hm
  let Y := projectiveOrbitScheme (H := H) m hm
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace
    (projectiveOrbitToSpec (H := H) m hm)
  let a (g : WithConv (H →ₐ[k] k)) : Spec (.of H) ≅ Spec (.of H) :=
    Scheme.Spec.mapIso (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv.toCommRingCatIso.op
  -- Mapping the opposite ring isomorphism through Spec gives the morphism induced by
  -- the forward translation algebra homomorphism used in the equivariance identity.
  have a_hom (g : WithConv (H →ₐ[k] k)) : (a g).hom =
      Spec.map (CommRingCat.ofHom
        (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) := rfl
  let b (g : WithConv (H →ₐ[k] k)) : Y ≅ Y := projectiveOrbitTranslation m hm g
  have := Algebra.FiniteType.isNoetherianRing k H
  apply f.flat_of_transitive_closedPoints_of_finiteType a b
    (fun g ↦ by
      rw [a_hom]
      exact (toProjectiveOrbit_projectiveOrbitTranslation_hom m hm g).symm)
  intro y z hy hz
  exact exists_projectiveOrbitTranslation_eq_of_mem_closedPoints m hm hy hz

end TauCeti.Comodule
