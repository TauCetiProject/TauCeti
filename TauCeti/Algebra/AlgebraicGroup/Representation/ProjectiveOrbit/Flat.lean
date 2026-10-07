/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Action
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

The proof combines `Comodule.projectiveOrbitTranslation`, closed-point lifting, and
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
  let b (g : WithConv (H →ₐ[k] k)) : Y ≅ Y := projectiveOrbitTranslation m hm g
  have := Algebra.FiniteType.isNoetherianRing k H
  apply f.flat_of_transitive_closedPoints_of_finiteType a b
    (fun g ↦ (toProjectiveOrbit_projectiveOrbitTranslation_hom m hm g).symm)
  intro y z hy hz
  -- Lift closed orbit points to closed source points, hence to rational group points.
  have : JacobsonSpace (Spec (.of H)) := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx, hxy⟩ := f.continuous.exists_isClosed_singleton_of_mem_range hy
    (Set.mem_range.mpr (f.surjective y))
  obtain ⟨w, hw, hwz⟩ := f.continuous.exists_isClosed_singleton_of_mem_range hz
    (Set.mem_range.mpr (f.surjective z))
  obtain ⟨g, hg⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k) x hx
  obtain ⟨h, hh⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k) w hw
  refine ⟨toConv h * (toConv g)⁻¹, ?_⟩
  apply (projectiveOrbitι (H := H) m hm).isEmbedding.injective
  rw [← hxy, ← hg, ← hwz, ← hh]
  have htranslate := congrArg (fun q : Y ⟶ _ ↦ q (f (AlgHom.kernelPoint g)))
    (projectiveOrbitTranslation_hom_ι m hm (toConv h * (toConv g)⁻¹))
  have hι (p : Spec (.of H)) :
      projectiveOrbitι (H := H) m hm (f p) = projectiveOrbitMap (H := H) m hm p :=
    congrArg (fun q : Spec (.of H) ⟶ _ ↦ q p) (toProjectiveOrbit_projectiveOrbitι m hm)
  have hpoint := projectivePointTranslation_projectiveOrbitMap_kernelPoint
    (toConv h * (toConv g)⁻¹) (toConv g) m hm
  simp only [ofConv_toConv, inv_mul_cancel_right] at hpoint
  simp only [Scheme.Hom.comp_apply, hι] at htranslate
  simpa only [hι] using htranslate.trans hpoint

end TauCeti.Comodule
