/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Coordinates
public import TauCeti.AlgebraicTopology.UniversalCover.Action

/-!
# Local systems are associated to their monodromy on the universal cover

Let `X` be a path-connected, locally path-connected, semilocally simply connected space with a
basepoint `x₀`, and let `k` be a commutative ring. The fundamental group `π₁(X, x₀)` acts on the
universal cover `p : UniversalCover x₀ → X` (`TauCeti.UniversalCover`) by deck transformations,
and `p` is the quotient covering map of this action
(`TauCeti.UniversalCover.isQuotientCoveringMap_projTopHom`). So every representation `A` of
`π₁(X, x₀)` has an associated local system `L_A` on `X`, with fibre `(A ⊗ k[p⁻¹ x])_{π₁}` over `x`
(`IsQuotientCoveringMap.associatedLocalSystem`). This file proves that every local system `L` on
`X` arises in this way, from its monodromy representation on the fibre `L_{x₀}`
(`TauCeti.LocalCoefficientSystem.monodromyFunctor`):

`L_{L_{x₀}} ≅ L`

(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`), naturally in `L`
(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso_hom_naturality`). Conversely the
monodromy representation of `L_A` is `A`
(`TauCeti.UniversalCover.monodromyAssociatedLocalSystemIso`), naturally in `A`. So the associated
local system on the universal cover inverts the monodromy functor up to isomorphism. The
equivalence of local systems with representations of `π₁(X, x₀)` itself, which needs only
path-connectedness, is `TauCeti.LocalCoefficientSystem.ofRepresentationFunctor`.

A point of the universal cover over `x` is a homotopy class `q` of paths from `x₀` to `x`
(`TauCeti.UniversalCover.sheetHom`), and transport back along `q` identifies `L_x` with `L_{x₀}`
(`TauCeti.UniversalCover.sheetCoordinates`). The deck transformation `g` prepends the loop `g⁻¹`
to `q`, which changes these coordinates by the monodromy of `g`, and transport along a path `γ`
reads as the identity in the coordinates of `q` and of `q · γ`, the endpoint of the lift of `γ`
starting at `q` (`TauCeti.UniversalCover.monodromy_mk`). These are the two conditions under which
`IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates` recognizes an associated local
system.

This identification lets homology with coefficients in an arbitrary local system on such a space be
computed from the chains of the universal cover with their deck action: by
`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`, homology with coefficients in `L_A` is
the homology of the coinvariants of the chains upstairs tensored with `A`, as in the equivariant
descent of the Thom isomorphism (`TauCeti.quotientTwistedHomologyThomIso`).

## Main definitions and results

* `TauCeti.UniversalCover.sheetHom`: the path class from `x₀` recorded by a sheet over `x`.
* `TauCeti.UniversalCover.sheetCoordinates`: the identification `L_x ≅ L_{x₀}` given by a sheet.
* `TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`: `L_{L_{x₀}} ≅ L`.
* `TauCeti.UniversalCover.associatedLocalSystemMonodromyIso_hom_naturality`: its naturality in `L`.
* `TauCeti.UniversalCover.monodromyAssociatedLocalSystemIso`: the monodromy of `L_A` at `x₀` is `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (local
  coefficient systems and modules over the group ring of `π₁`).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer (1978), Chapter VI, Section 1
  (bundles of groups and their operator groups).
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti.UniversalCover

variable {X : TopCat.{u}} (x₀ : X)

/-- The universal covering projection `UniversalCover x₀ → X` as a morphism of topological
spaces. -/
abbrev projTopHom : TopCat.of (UniversalCover x₀) ⟶ X :=
  TopCat.ofHom ⟨proj, continuous_proj x₀⟩

/-- The universal covering projection is the quotient covering map of the deck action of the
fundamental group (`TauCeti.UniversalCover.isQuotientCoveringMap`). -/
theorem isQuotientCoveringMap_projTopHom [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    IsQuotientCoveringMap (projTopHom x₀) (FundamentalGroup X x₀) :=
  isQuotientCoveringMap

variable {x₀}

/-! ### Sheets as path classes -/

/-- The homotopy class of paths from `x₀` to `x` recorded by a point of the universal cover over
`x`, as a morphism of the fundamental groupoid. -/
def sheetHom {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as}) :
    FundamentalGroupoid.mk x₀ ⟶ x :=
  e.val.path.cast rfl e.property.symm

/-- The sheet `[q]` over `x` records the path class `q`. -/
@[simp]
theorem sheetHom_mk {x : FundamentalGroupoid X} (q : Path.Homotopic.Quotient x₀ x.as) :
    sheetHom (x := x) ⟨mk x.as q, rfl⟩ = q :=
  Path.Homotopic.Quotient.cast_rfl_rfl q

/-! ### Sheet coordinates of a local system -/

section Coordinates

variable (k : Type u) [CommRing k] (L : LocalCoefficientSystem.{u, u, u} k X)

/-- **The coordinates of a local system in a sheet of the universal cover.** A point `e` of the
universal cover over `x`, a path class `q` from `x₀` to `x`, identifies the fibre `L_x` with the
fibre `L_{x₀}` of the monodromy representation, by transport back along `q`. -/
def sheetCoordinates {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as}) :
    L.obj x ≅ ModuleCat.of k ((LocalCoefficientSystem.monodromyFunctor k X x₀).obj L) :=
  (L.mapIso (asIso (sheetHom e))).symm

/-- The sheet coordinates are transport back along the path class of the sheet. -/
theorem sheetCoordinates_hom {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as}) :
    (sheetCoordinates k L e).hom = L.map (inv (sheetHom e)) := by
  rw [sheetCoordinates, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]

/-- The inverse sheet coordinates are transport along the path class of the sheet. -/
theorem sheetCoordinates_inv {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as}) :
    (sheetCoordinates k L e).inv = L.map (sheetHom e) :=
  (rfl)

end Coordinates

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-! ### Sheets under the deck action and under transport -/

/-- Transporting a sheet along `γ` composes its path class with `γ`. -/
@[simp]
theorem sheetHom_monodromy {x y : FundamentalGroupoid X} (γ : x ⟶ y)
    (e : projTopHom x₀ ⁻¹' {x.as}) :
    sheetHom ((isQuotientCoveringMap_projTopHom x₀).isCoveringMap.monodromy γ e) =
      sheetHom e ≫ γ := by
  obtain ⟨⟨z, q⟩, hz⟩ := e
  obtain rfl : z = x.as := hz
  have h : (isQuotientCoveringMap_projTopHom x₀).isCoveringMap.monodromy γ ⟨mk x.as q, rfl⟩ =
      ⟨mk y.as (q.trans γ), rfl⟩ :=
    Subtype.ext (monodromy_mk (X := X) q γ)
  rw [h, sheetHom_mk, sheetHom_mk, FundamentalGroupoid.comp_eq]

/-- The deck transformation `g` prepends the loop class `g⁻¹` to the path class of a sheet. -/
@[simp]
theorem sheetHom_smul {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as})
    (g : FundamentalGroup X x₀) :
    letI := (isQuotientCoveringMap_projTopHom x₀).mulActionFiber x.as
    sheetHom (g • e) = g⁻¹.asHom ≫ sheetHom e := by
  obtain ⟨⟨z, q⟩, hz⟩ := e
  obtain rfl : z = x.as := hz
  let := (isQuotientCoveringMap_projTopHom x₀).mulActionFiber x.as
  have h : g • (⟨mk x.as q, rfl⟩ : projTopHom x₀ ⁻¹' {x.as}) =
      ⟨mk x.as (g⁻¹.toPath.trans q), rfl⟩ :=
    Subtype.ext (by rw [IsQuotientCoveringMap.coe_mulActionFiber_smul, smul_mk])
  rw [h, sheetHom_mk, sheetHom_mk, FundamentalGroupoid.comp_eq]

variable (k : Type u) [CommRing k] (L : LocalCoefficientSystem.{u, u, u} k X)

/-- Moving the sheet by the deck transformation `g` composes its coordinates with the monodromy
of `g`. -/
theorem sheetCoordinates_hom_smul {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as})
    (g : FundamentalGroup X x₀) :
    letI := (isQuotientCoveringMap_projTopHom x₀).mulActionFiber x.as
    (sheetCoordinates k L (g • e)).hom = (sheetCoordinates k L e).hom ≫
      ModuleCat.ofHom (((LocalCoefficientSystem.monodromyFunctor k X x₀).obj L).ρ g) := by
  have hg : inv g⁻¹.asHom = g.asHom :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← End.mul_asHom, mul_inv_cancel, End.one_asHom])
  rw [sheetCoordinates_hom, sheetCoordinates_hom, sheetHom_smul, IsIso.inv_comp, hg, L.map_comp]
  refine congrArg (_ ≫ ·) ?_
  ext a
  rw [LocalCoefficientSystem.monodromyFunctor_obj_ρ]
  exact (LocalCoefficientSystem.monodromyRepresentation_apply L x₀ g a).symm

/-- Transport along `γ` reads as the identity in the coordinates of a sheet and of its transport
along `γ`. -/
theorem map_comp_sheetCoordinates_hom_monodromy {x y : FundamentalGroupoid X} (γ : x ⟶ y)
    (e : projTopHom x₀ ⁻¹' {x.as}) :
    L.map γ ≫ (sheetCoordinates k L
        ((isQuotientCoveringMap_projTopHom x₀).isCoveringMap.monodromy γ e)).hom =
      (sheetCoordinates k L e).hom := by
  have h : L.map γ ≫ L.map (inv (sheetHom e ≫ γ)) = L.map (inv (sheetHom e)) := by
    rw [← L.map_comp, IsIso.inv_comp, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [sheetCoordinates_hom, sheetCoordinates_hom, sheetHom_monodromy]
  exact h

/-! ### Every local system is associated to its monodromy representation -/

variable (x₀) in
/-- **Every local system is associated to its monodromy representation.** On a path-connected,
locally path-connected, semilocally simply connected space `X`, a local system `L` is isomorphic to
the local system associated, through the universal cover, to the representation of `π₁(X, x₀)` on
its fibre `L_{x₀}` by monodromy. In the coordinates of a sheet it is the identity of `L_{x₀}`
(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso_hom_app_comp`). -/
def associatedLocalSystemMonodromyIso :
    (isQuotientCoveringMap_projTopHom x₀).associatedLocalSystem k
        ((LocalCoefficientSystem.monodromyFunctor k X x₀).obj L) ≅ L :=
  (isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemIsoOfSheetCoordinates k
    (sheetCoordinates k L) (sheetCoordinates_hom_smul k L)
    (map_comp_sheetCoordinates_hom_monodromy k L)

/-- In the coordinates of any sheet `e`, the isomorphism `L_{L_{x₀}} ≅ L` is the identity of
`L_{x₀}`. -/
@[reassoc (attr := simp)]
theorem associatedLocalSystemMonodromyIso_hom_app_comp {x : FundamentalGroupoid X}
    (e : projTopHom x₀ ⁻¹' {x.as}) :
    (associatedLocalSystemMonodromyIso x₀ k L).hom.app x ≫ (sheetCoordinates k L e).hom =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k _ e).hom :=
  IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates_hom_app_comp _ _ _ _ _ e

/-- The isomorphism `L_{L_{x₀}} ≅ L` reads the fibre over `x` in the coordinates of a sheet `e`
and transports the result along the path class of `e`: the class of `a ⊗ r[e]` goes to the
transport of `r • a` along `e`. -/
theorem associatedLocalSystemMonodromyIso_hom_app {x : FundamentalGroupoid X}
    (e : projTopHom x₀ ⁻¹' {x.as}) :
    (associatedLocalSystemMonodromyIso x₀ k L).hom.app x =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k _ e).hom ≫
        (sheetCoordinates k L e).inv :=
  Iso.eq_comp_inv _ |>.2 (associatedLocalSystemMonodromyIso_hom_app_comp k L e)

/-- In the coordinates of any sheet `e`, the isomorphism `L ≅ L_{L_{x₀}}` is the identity of
`L_{x₀}`. -/
@[reassoc (attr := simp)]
theorem sheetCoordinates_inv_comp_associatedLocalSystemMonodromyIso_inv_app
    {x : FundamentalGroupoid X} (e : projTopHom x₀ ⁻¹' {x.as}) :
    (sheetCoordinates k L e).inv ≫ (associatedLocalSystemMonodromyIso x₀ k L).inv.app x =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k _ e).inv :=
  IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates_comp_inv_app _ _ _ _ _ e

/-- The isomorphism `L ≅ L_{L_{x₀}}` transports the fibre over `x` back along the path class of a
sheet `e`, and reads the result as an element of the fibre of `L_{L_{x₀}}` in the coordinates of
`e`. -/
theorem associatedLocalSystemMonodromyIso_inv_app {x : FundamentalGroupoid X}
    (e : projTopHom x₀ ⁻¹' {x.as}) :
    (associatedLocalSystemMonodromyIso x₀ k L).inv.app x =
      (sheetCoordinates k L e).hom ≫
        ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k _ e).inv :=
  Iso.eq_inv_comp _ |>.2
    (sheetCoordinates_inv_comp_associatedLocalSystemMonodromyIso_inv_app k L e)

/-- The isomorphism `L_{L_{x₀}} ≅ L` is natural in the local system `L`. -/
@[reassoc]
theorem associatedLocalSystemMonodromyIso_hom_naturality
    {L L' : LocalCoefficientSystem.{u, u, u} k X} (η : L ⟶ L') :
    (isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemMap k
        ((LocalCoefficientSystem.monodromyFunctor k X x₀).map η) ≫
      (associatedLocalSystemMonodromyIso x₀ k L').hom =
    (associatedLocalSystemMonodromyIso x₀ k L).hom ≫ η := by
  ext x : 2
  obtain ⟨z, hz⟩ := (isQuotientCoveringMap_projTopHom x₀).surjective x.as
  let e : projTopHom x₀ ⁻¹' {x.as} := ⟨z, hz⟩
  rw [NatTrans.comp_app, NatTrans.comp_app, associatedLocalSystemMonodromyIso_hom_app k _ e,
    associatedLocalSystemMonodromyIso_hom_app k _ e, ← Category.assoc,
    IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_naturality, Category.assoc,
    Category.assoc, sheetCoordinates_inv, sheetCoordinates_inv,
    LocalCoefficientSystem.forget₂_map_monodromyFunctor_map]
  -- `η.naturality` closes the goal up to `monodromyFunctor_obj_V`, the source of `η.app x₀` here.
  exact congrArg (_ ≫ ·) (η.naturality (sheetHom e)).symm

/-! ### The monodromy of an associated local system -/

/-- Read in the coordinates of the constant-path sheet, transport in `L_A` around the loop `g`
is `A.ρ g`: the transport of the constant-path sheet along `g` is `g⁻¹ •` that sheet
(`TauCeti.UniversalCover.monodromy_basepointLift`), whose coordinates are those of the
constant-path sheet followed by `A.ρ g⁻¹`. -/
@[reassoc]
theorem map_comp_associatedLocalSystemFiberIso_basepointLift_hom
    (A : Rep.{u} k (FundamentalGroup X x₀)) (g : FundamentalGroup X x₀) :
    ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystem k A).map g.asHom ≫
        ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k A
          (basepointLift x₀)).hom =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k A
          (basepointLift x₀)).hom ≫ ModuleCat.ofHom (A.ρ g) := by
  have h := (isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso_map_hom k A
    g.asHom (basepointLift x₀)
  let := (isQuotientCoveringMap_projTopHom x₀).mulActionFiber x₀
  rw [show (isQuotientCoveringMap_projTopHom x₀).isCoveringMap.monodromy g.asHom
      (basepointLift x₀) = g⁻¹ • basepointLift x₀ from
        Subtype.ext (monodromy_basepointLift x₀ g),
    IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_smul] at h
  conv_rhs => rw [← h]
  ext a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Representation.self_inv_apply]

/-- **The monodromy of an associated local system is the representation.** For a representation
`A` of `π₁(X, x₀)`, the monodromy representation at `x₀` of the local system associated to `A`
through the universal cover is `A`, by the coordinates of the constant-path sheet. -/
def monodromyAssociatedLocalSystemIso (A : Rep.{u} k (FundamentalGroup X x₀)) :
    (LocalCoefficientSystem.monodromyFunctor k X x₀).obj
        ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystem k A) ≅ A :=
  Rep.mkIso (Representation.Equiv.mk
    ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k A
      (basepointLift x₀)).toLinearEquiv fun g ↦ by
        ext a
        have h := congr(($(map_comp_associatedLocalSystemFiberIso_basepointLift_hom k A g)).hom a)
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
          ModuleCat.hom_ofHom] at h
        rw [LinearMap.comp_apply, LinearMap.comp_apply,
          LocalCoefficientSystem.monodromyRepresentation_apply, LinearEquiv.coe_coe,
          Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, h])

/-- The identification of the monodromy of `L_A` with `A` reads the fibre over `x₀` in the
coordinates of the constant-path sheet. -/
theorem monodromyAssociatedLocalSystemIso_hom_apply (A : Rep.{u} k (FundamentalGroup X x₀))
    (a : (isQuotientCoveringMap_projTopHom x₀).associatedLocalSystem k A |>.obj (.mk x₀)) :
    (monodromyAssociatedLocalSystemIso k A).hom a =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k A
        (basepointLift x₀)).hom a :=
  (rfl)

/-- The identification of `A` with the monodromy of `L_A` gives the element of the fibre over `x₀`
with coordinates `a` in the constant-path sheet. -/
theorem monodromyAssociatedLocalSystemIso_inv_apply (A : Rep.{u} k (FundamentalGroup X x₀))
    (a : A) :
    (monodromyAssociatedLocalSystemIso k A).inv a =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k A
        (basepointLift x₀)).inv a :=
  (rfl)

/-- The identification of the monodromy of `L_A` with `A` is natural in the representation. -/
@[reassoc]
theorem monodromyAssociatedLocalSystemIso_hom_naturality
    {A A' : Rep.{u} k (FundamentalGroup X x₀)} (f : A ⟶ A') :
    (LocalCoefficientSystem.monodromyFunctor k X x₀).map
        ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemMap k f) ≫
      (monodromyAssociatedLocalSystemIso k A').hom =
    (monodromyAssociatedLocalSystemIso k A).hom ≫ f := by
  have hB (B : Rep.{u} k (FundamentalGroup X x₀)) :
      (forget₂ (Rep k (FundamentalGroup X x₀)) (ModuleCat k)).map
        (monodromyAssociatedLocalSystemIso k B).hom =
      ((isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso k B
        (basepointLift x₀)).hom := by
    ext a
    exact monodromyAssociatedLocalSystemIso_hom_apply k B a
  apply (forget₂ (Rep k (FundamentalGroup X x₀)) (ModuleCat k)).map_injective
  rw [Functor.map_comp, Functor.map_comp, hB, hB,
    LocalCoefficientSystem.forget₂_map_monodromyFunctor_map]
  exact (isQuotientCoveringMap_projTopHom x₀).associatedLocalSystemFiberIso_hom_naturality k f
    (basepointLift x₀)

end TauCeti.UniversalCover
