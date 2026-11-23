/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem

/-!
# The orientation local system as the local system associated to the sign representation

Let `E → B` be a real vector bundle of rank `card ι`, with orientation double cover `B'`. The units
`ℤˣ = {1, -1}` act on `B'`, with `-1` acting by the deck involution that reverses orientations, and
the projection `B' → B` is the quotient covering map of this action
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_proj`). So every representation of
`ℤˣ` has an associated local system on `B` (`IsQuotientCoveringMap.associatedLocalSystem`). This
file identifies the one associated to the sign representation of `ℤˣ` on a commutative ring `k`
with the orientation local system `o(E)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`):

`L_sign ≅ o(E)`

(`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`). The class of `a ⊗ f`, for a
formal sum `f` of orientations of the fibre `E_b`, goes to `a` times the function `o ↦ f o - f (-o)`
on the orientations of `E_b` (`signLocalSystemObjEquiv_associatedLocalSystemSignIso_hom_app_apply`
in the namespace `TauCeti.VectorBundleOrientationCover`).
This is the case of the orientation double cover of
`IsQuotientCoveringMap.associatedLocalSystemSignIso`.

Chains on `B` twisted by an associated local system are the coinvariants of the chains of the cover
tensored with the representation
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`, and
`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted` for pairs). Through this isomorphism,
chains on `B` twisted by `o(E)` are the coinvariants of the chains of `B'` tensored with the sign
representation, on which `-1` acts by minus the deck involution. This is the form in which an
equivariant chain map on `B'`, or on the total space of the pull-back of `E` to `B'`, computes
homology twisted by `o(E)`.

The covering-space and coinvariant constructions are stated for spaces and coefficient rings in a
single universe with the group `ℤˣ`, so the base, the bundle and `k` live in `Type`.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`: the local system associated
  to the sign representation is the orientation local system.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H (local
  coefficient systems and the orientation double cover).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover of a vector bundle).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti

namespace VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type) [CommRing k]

variable (F E) in
include hι in
/-- The projection of the orientation double cover, as a morphism of topological spaces, is the
quotient covering map of the action of `ℤˣ` (`isQuotientCoveringMap_proj`). -/
theorem isQuotientCoveringMap_ofHom_projection :
    IsQuotientCoveringMap (TopCat.ofHom (projection : C(VectorBundleOrientationCover F E ι, B)))
      ℤˣ :=
  isQuotientCoveringMap_proj hι

variable (F E) in
/-- **The orientation local system is associated to the sign representation.** For a real vector
bundle `E`, the local system on the base associated to the sign representation of `ℤˣ` on `k`
through the orientation double cover is isomorphic to the orientation local system `o(E)`. The
class of `a ⊗ f` goes to `a` times the function `o ↦ f o - f (-o)` on the orientations of the fibre
(`signLocalSystemObjEquiv_associatedLocalSystemSignIso_hom_app_apply`). -/
def associatedLocalSystemSignIso :
    (isQuotientCoveringMap_ofHom_projection F E hι).associatedLocalSystem k
        (Rep.of (Representation.ofDistribMulAction k ℤˣ k)) ≅
      signLocalSystem F E k hι :=
  (isQuotientCoveringMap_ofHom_projection F E hι).associatedLocalSystemSignIso k
    (σ := (deck (F := F) (E := E) (ι := ι) :
      C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))
    (fun p ↦ (neg_one_smul_eq_deck p).symm) ≪≫ (eqToIso (signLocalSystem_def hι)).symm

/-- The isomorphism `associatedLocalSystemSignIso` sends the class of `a ⊗ f`, for a formal sum `f`
of orientations of the fibre over `x`, to `a` times the function `o ↦ f o - f (-o)`. -/
-- Match before simplification unfolds `Rep.coinvariantsTensorMk` on the left-hand side.
@[simp↓]
theorem signLocalSystemObjEquiv_associatedLocalSystemSignIso_hom_app_apply
    (x : FundamentalGroupoid (TopCat.of B)) (a : k)
    (f : TopCat.ofHom (projection : C(VectorBundleOrientationCover F E ι, B)) ⁻¹' {x.as} →₀ k)
    (o : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι))) :
    (signLocalSystemObjEquiv hι x (((associatedLocalSystemSignIso F E hι k).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
          (Rep.of ((isQuotientCoveringMap_ofHom_projection F E hι).fiberRepresentation k x.as))
            a f)) : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → k) o =
      a * (f o - f (Function.fiberMap deck (funext proj_deck) x.as o)) := by
  have hG := isQuotientCoveringMap_ofHom_projection F E hι
  let σ : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι) :=
    deck (F := F) (E := E) (ι := ι)
  have hσ (p : VectorBundleOrientationCover F E ι) : σ p = (-1 : ℤˣ) • p :=
    (neg_one_smul_eq_deck p).symm
  -- By definition, `associatedLocalSystemSignIso` is the isomorphism of `IsQuotientCoveringMap`
  -- followed by the identification of its target with the orientation local system.
  calc _ = (signLocalSystemObjEquiv hι x ((eqToIso (signLocalSystem_def (R := k) hι)).inv.app x
          (((hG.associatedLocalSystemSignIso k hσ).hom.app x).hom
            (Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
              (Rep.of (hG.fiberRepresentation k x.as)) a f))) :
            (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → k) o := rfl
    _ = _ := by
      rw [signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_inv_app,
        IsQuotientCoveringMap.associatedLocalSystemSignIso_hom,
        IsQuotientCoveringMap.associatedLocalSystemSignHom_app_coinvariantsTensorMk, map_smul,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      -- The fibres of `proj` and of the projection as a morphism of spaces are the same sets.
      exact congrArg (a * ·)
        (hG.isCoveringMap.signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply k _ _ x f o)

/-- The inverse of `associatedLocalSystemSignIso` sends a function `g` on the orientations of the
fibre over `x` changing sign under reversal to the class of `g o ⊗ o`, for any orientation `o` of
the fibre. -/
theorem associatedLocalSystemSignIso_inv_app_apply {x : FundamentalGroupoid (TopCat.of B)}
    (o : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)))
    (g : (signLocalSystem F E k hι).obj x) :
    ((associatedLocalSystemSignIso F E hι k).inv.app x).hom g =
      Rep.coinvariantsTensorMk (Rep.of (Representation.ofDistribMulAction k ℤˣ k))
        (Rep.of ((isQuotientCoveringMap_ofHom_projection F E hι).fiberRepresentation k x.as))
        ((signLocalSystemObjEquiv hι x g :
          (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → k) o)
        (Finsupp.single o 1) := by
  have hG := isQuotientCoveringMap_ofHom_projection F E hι
  let σ : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι) :=
    deck (F := F) (E := E) (ι := ι)
  have hσ (p : VectorBundleOrientationCover F E ι) : σ p = (-1 : ℤˣ) • p :=
    (neg_one_smul_eq_deck p).symm
  -- By definition, the inverse of `associatedLocalSystemSignIso` is the identification of the
  -- orientation local system with the sign local system of `deck`, followed by the inverse of the
  -- isomorphism of `IsQuotientCoveringMap`.
  calc _ = ((hG.associatedLocalSystemSignIso k hσ).inv.app x).hom
          ((eqToIso (signLocalSystem_def (R := k) hι)).hom.app x g) := rfl
    _ = _ := by
      rw [IsQuotientCoveringMap.associatedLocalSystemSignIso_inv_app_apply hG k hσ o,
        signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]

end VectorBundleOrientationCover

end TauCeti
