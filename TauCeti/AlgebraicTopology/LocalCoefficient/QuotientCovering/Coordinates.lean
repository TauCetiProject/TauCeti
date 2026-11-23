/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Trivialization

/-!
# Recognizing an associated local system by its sheet coordinates

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G`, in the sense of Mathlib's
`IsQuotientCoveringMap`, let `k` be a commutative ring and `A` a representation of `G`. A choice of
sheet `e` over `x` identifies the fibre `(A ⊗ k[p⁻¹ x])_G` of the associated local system `L_A`
(`IsQuotientCoveringMap.associatedLocalSystem`) with `A`
(`IsQuotientCoveringMap.associatedLocalSystemFiberIso`); moving the sheet to `g • e` multiplies
these coordinates by `A.ρ g`, and transport along a path keeps them when the sheet is transported
too.

These two properties characterize `L_A`. Let `S` be a local system on `B` with, for every point `x`
and every sheet `e` over `x`, an identification `ψ e : S_x ≅ A` such that `ψ (g • e) = A.ρ g ∘ ψ e`
and such that transport along a path `γ` reads in the coordinates `ψ e` and `ψ (γ_* e)` as the
identity, `γ_* e` being the endpoint of the lift of `γ` starting at `e`. Then `L_A ≅ S`, by the
isomorphism which in the coordinates of any sheet is the identity of `A`
(`IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates`): the class of `a ⊗ r[e]` goes
to `(ψ e)⁻¹ (r • a)`. No sheet is distinguished, since the coordinates of different sheets over a
point differ by the action on both sides.

The simplest instance is a trivial representation, whose coordinates do not depend on the sheet:
the local system associated to the trivial representation on a module `M` is the constant system
`M` (`IsQuotientCoveringMap.associatedLocalSystemTrivialIso`). So the homology of the base with
constant coefficients is the homology of the coinvariants of the chains of the cover. The sign
representation of `ℤˣ` and the sign local system of a double cover are another instance, treated in
`TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Sign`.

## Main definitions

* `IsQuotientCoveringMap.associatedLocalSystemIsoOfSheetCoordinates`: the isomorphism of the
  associated local system with a local system carrying compatible sheet coordinates.
* `IsQuotientCoveringMap.associatedLocalSystemTrivialIso`: the local system associated to a trivial
  representation is constant.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] {A : Rep.{u} k G}
  {S : LocalCoefficientSystem.{u, u, u} k B}
  (ψ : ∀ {x : FundamentalGroupoid B}, p ⁻¹' {x.as} → (S.obj x ≅ ModuleCat.of k A))

section Coordinates

variable (hsmul : ∀ {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (g : G),
      letI := hG.mulActionFiber x.as
      (ψ (g • e)).hom = (ψ e).hom ≫ ModuleCat.ofHom (A.ρ g))
  (hmap : ∀ {x y : FundamentalGroupoid B} (γ : x ⟶ y) (e : p ⁻¹' {x.as}),
    S.map γ ≫ (ψ (hG.isCoveringMap.monodromy γ e)).hom = (ψ e).hom)

variable {ψ} in
include hsmul in
/-- Sheet coordinates compatible with the action identify the fibre of the associated local system
with that of `S` independently of the sheet: the coordinates of the associated local system and
those of `S` change by the same `A.ρ g` when the sheet `e` is moved to `g • e`. -/
lemma associatedLocalSystemFiberIso_hom_comp_inv_eq {x : FundamentalGroupoid B}
    (e e' : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemFiberIso k A e').hom ≫ (ψ e').inv =
      (hG.associatedLocalSystemFiberIso k A e).hom ≫ (ψ e).inv := by
  let := hG.mulActionFiber x.as
  obtain ⟨g, rfl⟩ : ∃ g : G, g • e = e' :=
    ⟨hG.fiberEquivGroup e e', Subtype.ext (hG.fiberEquivGroup_smul_self e)⟩
  rw [associatedLocalSystemFiberIso_hom_smul, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, hsmul, Iso.inv_hom_id_assoc]

/-- **An associated local system is recognized by its sheet coordinates.** Let `S` be a local
system on `B` with, for every sheet `e` over a point `x`, an identification `ψ e : S_x ≅ A`, such
that moving the sheet to `g • e` composes the coordinates with `A.ρ g` and transport along a path
`γ` is the identity in the coordinates of `e` and of the endpoint `γ_* e` of its lift. Then `S` is
isomorphic to the local system associated to `A`, by the isomorphism which is the identity of `A`
in the coordinates of any sheet (`associatedLocalSystemIsoOfSheetCoordinates_hom_app_comp`). -/
def associatedLocalSystemIsoOfSheetCoordinates : hG.associatedLocalSystem k A ≅ S :=
  NatIso.ofComponents
    (fun x ↦ hG.associatedLocalSystemFiberIso k A ⟨_, (hG.surjective x.as).choose_spec⟩ ≪≫
      (ψ ⟨_, (hG.surjective x.as).choose_spec⟩).symm)
    fun {x y} γ ↦ by
      -- Read both sides in the coordinates of a sheet over `x` and of its transport over `y`.
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [hG.associatedLocalSystemFiberIso_hom_comp_inv_eq k hsmul
        (hG.isCoveringMap.monodromy γ ⟨_, (hG.surjective x.as).choose_spec⟩)
        ⟨_, (hG.surjective y.as).choose_spec⟩, associatedLocalSystemFiberIso_map_hom_assoc,
        Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, Iso.comp_inv_eq, hmap]

/-- In the coordinates of any sheet `e`, the isomorphism of the associated local system with `S`
given by compatible sheet coordinates is the identity of `A`. -/
@[reassoc (attr := simp)]
lemma associatedLocalSystemIsoOfSheetCoordinates_hom_app_comp {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemIsoOfSheetCoordinates k ψ hsmul hmap).hom.app x ≫ (ψ e).hom =
      (hG.associatedLocalSystemFiberIso k A e).hom := by
  -- By definition, the component reads in the coordinates of a chosen sheet over `x`.
  have h : (hG.associatedLocalSystemIsoOfSheetCoordinates k ψ hsmul hmap).hom.app x =
      (hG.associatedLocalSystemFiberIso k A ⟨_, (hG.surjective x.as).choose_spec⟩).hom ≫
        (ψ ⟨_, (hG.surjective x.as).choose_spec⟩).inv :=
    rfl
  rw [← Iso.eq_comp_inv, h, hG.associatedLocalSystemFiberIso_hom_comp_inv_eq k hsmul _ e]

/-- In the coordinates of any sheet `e`, the inverse of the isomorphism given by compatible sheet
coordinates is the identity of `A`. -/
@[reassoc (attr := simp)]
lemma associatedLocalSystemIsoOfSheetCoordinates_comp_inv_app {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) :
    (ψ e).inv ≫ (hG.associatedLocalSystemIsoOfSheetCoordinates k ψ hsmul hmap).inv.app x =
      (hG.associatedLocalSystemFiberIso k A e).inv := by
  rw [Iso.inv_comp_eq, ← cancel_epi
    ((hG.associatedLocalSystemIsoOfSheetCoordinates k ψ hsmul hmap).hom.app x),
    Iso.hom_inv_id_app, associatedLocalSystemIsoOfSheetCoordinates_hom_app_comp_assoc,
    Iso.hom_inv_id]

/-- The isomorphism given by compatible sheet coordinates sends the class of `a ⊗ r[e]` to the
element of `S_x` with coordinates `r • a` in the sheet `e`. -/
lemma associatedLocalSystemIsoOfSheetCoordinates_hom_app_coinvariantsTensorMk
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (a : A) (r : k) :
    ((hG.associatedLocalSystemIsoOfSheetCoordinates k ψ hsmul hmap).hom.app x).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e r)) =
      (ψ e).inv.hom (r • a) := by
  have h := hG.associatedLocalSystemIsoOfSheetCoordinates_hom_app_comp k ψ hsmul hmap e
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  -- In the coordinates of the sheet `e` itself, the class of `a ⊗ r[e]` is `r • a`.
  refine congrArg (ψ e).inv.hom
    ((hG.associatedLocalSystemFiberIso_hom_coinvariantsTensorMk k A e e a r).trans ?_)
  simp

end Coordinates

/-! ### The trivial representation -/

section Trivial

variable (M : Type u) [AddCommGroup M] [Module k M]

/-- The sheet coordinates of the constant system `M`: the identity of `M` for every sheet. -/
private abbrev trivialCoordinates {x : FundamentalGroupoid B} (_ : p ⁻¹' {x.as}) :
    ((LocalCoefficientSystem.constantFunctor B).obj (ModuleCat.of k M)).obj x ≅
      ModuleCat.of k (Rep.trivial k G M) :=
  Iso.refl _

/-- The trivial action does not move the coordinates of the constant system. -/
private lemma trivialCoordinates_smul {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (g : G) :
    letI := hG.mulActionFiber x.as
    (trivialCoordinates k M (g • e)).hom =
      (trivialCoordinates k M e).hom ≫ ModuleCat.ofHom ((Rep.trivial k G M).ρ g) := by
  rw [Rep.trivial_ρ, ModuleCat.ofHom_id, Category.comp_id]

/-- Transport in the constant system is the identity in the coordinates of any two sheets. -/
private lemma trivialCoordinates_map {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (e : p ⁻¹' {x.as}) :
    ((LocalCoefficientSystem.constantFunctor B).obj (ModuleCat.of k M)).map γ ≫
        (trivialCoordinates (G := G) k M (hG.isCoveringMap.monodromy γ e)).hom =
      (trivialCoordinates (G := G) k M e).hom := by
  rw [LocalCoefficientSystem.constantFunctor_obj_map]
  exact Category.id_comp _

/-- **The local system associated to a trivial representation is constant.** For the trivial
representation of `G` on a `k`-module `M`, the fibre `(M ⊗ k[p⁻¹ x])_G` is identified with `M`,
sending the class of `m ⊗ r[e]` to `r • m` whatever the sheet `e`, compatibly with transport. -/
def associatedLocalSystemTrivialIso :
    hG.associatedLocalSystem k (Rep.trivial k G M) ≅
      (LocalCoefficientSystem.constantFunctor B).obj (ModuleCat.of k M) :=
  hG.associatedLocalSystemIsoOfSheetCoordinates k (trivialCoordinates k M)
    (hG.trivialCoordinates_smul k M) (hG.trivialCoordinates_map k M)

/-- The identification of the local system associated to a trivial representation with the constant
system sends the class of `m ⊗ r[e]` to `r • m`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
lemma associatedLocalSystemTrivialIso_hom_app_coinvariantsTensorMk {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (m : M) (r : k) :
    ((hG.associatedLocalSystemTrivialIso k M).hom.app x).hom
        (Rep.coinvariantsTensorMk (Rep.trivial k G M) (Rep.of (hG.fiberRepresentation k x.as)) m
          (Finsupp.single e r)) =
      r • m :=
  hG.associatedLocalSystemIsoOfSheetCoordinates_hom_app_coinvariantsTensorMk k
    (trivialCoordinates k M) (hG.trivialCoordinates_smul k M) (hG.trivialCoordinates_map k M) e m r

/-- The inverse identification of the constant system with the local system associated to a
trivial representation sends `m` to the class of `m ⊗ [e]`, for any sheet `e` over the point. -/
-- Not a simp lemma: `simp` rewrites the domain of the component by
-- `TauCeti.LocalCoefficientSystem.constantFunctor_obj_obj` first.
lemma associatedLocalSystemTrivialIso_inv_app_apply {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (m : M) :
    ((hG.associatedLocalSystemTrivialIso k M).inv.app x).hom m =
      Rep.coinvariantsTensorMk (Rep.trivial k G M) (Rep.of (hG.fiberRepresentation k x.as)) m
        (Finsupp.single e 1) :=
  (congrArg (fun f ↦ f.hom m) (hG.associatedLocalSystemIsoOfSheetCoordinates_comp_inv_app k
    (trivialCoordinates k M) (hG.trivialCoordinates_smul k M) (hG.trivialCoordinates_map k M)
      e)).trans (hG.associatedLocalSystemFiberIso_inv_apply k (Rep.trivial k G M) e m)

end Trivial

end IsQuotientCoveringMap
