/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# The multiplicative group scheme over an arbitrary base

For a scheme `S`, the multiplicative group scheme `𝔾_{m,S} = Spec ℤ[t, t⁻¹] ×_{Spec ℤ} S` is the
base change to `S` of the multiplicative group scheme `𝔾_m = D(ℤ)` over `Spec ℤ`
(`TauCeti.DiagonalizableGroup.multiplicativeGroupScheme`). It is defined here as a group object
in schemes over `S`, using that `Spec ℤ` is terminal, so that every scheme lies over it in a
unique way.

Its functor of points is the functor of units of global sections: for every scheme `T` over
`S`, not necessarily affine, morphisms `T ⟶ 𝔾_{m,S}` over `S` form a group isomorphic to
`Γ(T, 𝒪_T)ˣ`, and restriction along a morphism `T ⟶ T'` over `S` corresponds to the map of
units induced by `Γ(T', 𝒪) ⟶ Γ(T, 𝒪)`. This is the group-scheme counterpart of the sheaf
`AlgebraicGeometry.Scheme.Gm` of units on the big site of `S`. The identification composes the
base-change adjunction (`TauCeti.GroupScheme.baseChangePointMulEquiv`) with the description of
points of `𝔾_m` over `Spec ℤ` on arbitrary test schemes
(`TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsAlgΓMulEquiv`).

## Main declarations

* `TauCeti.GroupScheme.Gm`: the multiplicative group scheme `𝔾_{m,S}` over a scheme `S`.
* `TauCeti.GroupScheme.Gm.pointsMulEquiv`: points of `𝔾_{m,S}` over `S` with values in an
  `S`-scheme `T` are the units of `Γ(T, 𝒪_T)`, as groups.
* `TauCeti.GroupScheme.Gm.pointsMulEquiv_naturality`: this identification is natural in `T`.

## References

* The Stacks Project, Chapter *Groupoid Schemes*, Section 39.5, Example 39.5.1.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti.GroupScheme

universe u

/-- The multiplicative group scheme `𝔾_{m,S}` over a scheme `S`: the base change of the
multiplicative group scheme over `Spec ℤ` along the unique morphism `S ⟶ Spec ℤ`. -/
noncomputable abbrev Gm (S : Scheme.{u}) : Grp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.obj
    (DiagonalizableGroup.multiplicativeGroupScheme (ULift.{u} ℤ))

/-- The multiplicative group scheme is commutative. -/
instance (S : Scheme.{u}) : IsCommMonObj (Gm S).X :=
  inferInstanceAs <| IsCommMonObj <| (Over.pullback (specULiftZIsTerminal.from S)).obj
    (DiagonalizableGroup.multiplicativeGroupScheme (ULift.{u} ℤ)).X

namespace Gm

variable {S : Scheme.{u}}

/-- Points of `𝔾_{m,S}` with values in a scheme `T` over `S` are the units of the global
sections of `T`: morphisms `T ⟶ 𝔾_{m,S}` over `S`, with their pointwise group law, form a group
isomorphic to `Γ(T, 𝒪_T)ˣ`. The scheme `T` need not be affine. -/
noncomputable def pointsMulEquiv (T : Over S) : (T ⟶ (Gm S).X) ≃* Γ(T.left, ⊤)ˣ :=
  (baseChangePointMulEquiv _ _ T).trans
    (DiagonalizableGroup.multiplicativeGroupSchemePointsAlgΓMulEquiv _)

/-- The unit attached to a point of `𝔾_{m,S}` is the unit attached to the corresponding point
of `𝔾_m` over `Spec ℤ`, through the base-change adjunction. -/
theorem pointsMulEquiv_apply (T : Over S) (x : T ⟶ (Gm S).X) :
    pointsMulEquiv T x =
      DiagonalizableGroup.multiplicativeGroupSchemePointsAlgΓMulEquiv _
        (baseChangePointMulEquiv _ _ T x) := (rfl)

/-- The identification of points of `𝔾_{m,S}` with units of global sections is natural in the
test scheme: restricting a point along `f : T ⟶ T'` over `S` maps its unit along
`Γ(T', 𝒪) ⟶ Γ(T, 𝒪)`. -/
theorem pointsMulEquiv_naturality {T T' : Over S} (f : T ⟶ T') (x : T' ⟶ (Gm S).X) :
    pointsMulEquiv T (f ≫ x) =
      Units.map f.left.appTop.hom.toMonoidHom (pointsMulEquiv T' x) := by
  rw [pointsMulEquiv_apply, pointsMulEquiv_apply, baseChangePointMulEquiv_naturality_left,
    DiagonalizableGroup.multiplicativeGroupSchemePointsAlgΓMulEquiv_precomp, Over.map_map_left]

end Gm

end TauCeti.GroupScheme
