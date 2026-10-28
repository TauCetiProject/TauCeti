/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
public import TauCeti.AlgebraicGeometry.Curves.HighDegree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic

/-!
# Restricting high-degree line bundles to effective divisors

On a smooth proper geometrically connected curve, sections of a line bundle `L` can prescribe
arbitrary restrictions along an effective Cartier divisor `D` whenever
`deg L - deg D > 2g - 2`. The degree of `D` is the rank of its finite closed subscheme over the
field, so multiplicities and residue-field degrees are included. In particular the result
applies to doubled points, not only to reduced collections of points.

Restriction is expressed as the tensor of `𝒪_X → i_*𝒪_D` with `L`, preceded by the inverse
right unitor. Its target is `L ⊗ i_*𝒪_D`, the quotient by `L ⊗ 𝓘_D`. The vanishing of
`H¹(X, L ⊗ 𝓘_D)` gives surjectivity. This is the restriction calculation used in separating
points and tangent directions by complete linear systems; no projective embedding or
very-ampleness criterion is asserted here.

## References

* R. Hartshorne, *Algebraic Geometry*, IV, Corollary 3.2 and its proof.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Module (finrank)

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} {k : Type u} [Field k] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyConnected (X ↘ Spec (.of k))]

/-- On a smooth proper geometrically connected curve, sections of `L` prescribe arbitrary
restrictions along an effective Cartier divisor `D` if `deg L - deg D > 2g - 2`.
The rank of `D → Spec k` counts its full scheme structure, including nonreduced points. -/
theorem surjective_tensorRestriction_of_high_degree
    (L : InvertibleSheaf X) (I : X.IdealSheafData) (hI : I.IsEffectiveCartier)
    (s : Spec (.of k))
    (hdeg : 2 * (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) - 2 <
      L.eulerDegree k - (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s) :
    Function.Surjective (Scheme.Modules.Hom.app
      ((ρ_ L.obj).inv ≫ L.obj ◁
        SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) ⊤) := by
  have : ConnectedSpace X :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := X ↘ Spec (.of k))
  have hIdeg := hI.eulerDegree_inv_mk_toInvertibleSheaf k I s
  have hcancel := LineBundleClass.eulerDegree_mul_of_smooth k
    (LineBundleClass.mk hI.toInvertibleSheaf) (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  rw [mul_inv_cancel, LineBundleClass.eulerDegree_one, hIdeg,
    LineBundleClass.eulerDegree_mk] at hcancel
  have htensor := LineBundleClass.eulerDegree_mul_of_smooth k
    (LineBundleClass.mk L) (LineBundleClass.mk hI.toInvertibleSheaf)
  rw [← LineBundleClass.mk_tensorProduct, LineBundleClass.eulerDegree_mk,
    LineBundleClass.eulerDegree_mk, LineBundleClass.eulerDegree_mk] at htensor
  have hvan := subsingleton_cohomology_one_of_smooth_of_two_mul_genus_sub_two_lt_eulerDegree
    (k := k) (tensorProduct L hI.toInvertibleSheaf) (by omega)
  let e := tensorProductObjIso L hI.toInvertibleSheaf ≪≫
    whiskerLeftIso L.obj (eqToIso hI.toInvertibleSheaf_obj)
  have hvan' : Subsingleton (Scheme.Modules.Cohomology (L.obj ⊗ I.sheaf) 1) := by
    have := hvan
    exact (Scheme.Modules.cohomologyBaseLinearEquivOfIso k e 1).surjective.subsingleton
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  let F : _root_.SheafOfModules X.ringCatSheaf := L.obj
  have : L.obj.IsLocallyFree := inferInstanceAs F.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs F.IsFiniteType
  exact I.surjective_tensorRestriction_of_subsingleton_cohomology_one L.obj hvan'

end TauCeti.AlgebraicGeometry.InvertibleSheaf
