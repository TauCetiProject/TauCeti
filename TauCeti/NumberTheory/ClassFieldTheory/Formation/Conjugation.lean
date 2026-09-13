/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# Conjugation of finite normal layers

Conjugating a finite normal layer `V ◁ U` by an element `g` of the ambient group gives the layer
`gVg⁻¹ ◁ gUg⁻¹`. In field notation, if `U = G_F` and `V = G_K` then the conjugate layer is
`g(K)/g(F)`. Conjugation identifies everything attached to the two layers: the Galois groups
(`conjGalEquiv`, `uγu⁻¹`-style conjugation of cosets), the levels (`levelConj`, the action of `g`
on the coefficient module carries `A^U` onto `A^{gUg⁻¹}`), hence the coefficient modules
(`conjRepIso`) and the cohomology of the two layers (`layerCohomologyConj`). These identifications
are the ingredients of the compatibility of the reciprocity map with conjugation, which is what
makes the norm residue symbol of a global field independent of choices of embeddings.

## Main definitions

* `TauCeti.ClassFieldTheory.conjOpenSubgroup`: the conjugate `gUg⁻¹` of an open subgroup.
* `TauCeti.ClassFieldTheory.conjugateLayer`: the conjugate layer `gVg⁻¹ ◁ gUg⁻¹`.
* `TauCeti.ClassFieldTheory.conjGroundEquiv`, `conjGalEquiv`: conjugation on ground subgroups
  and on Galois groups.
* `TauCeti.ClassFieldTheory.levelConj`: the action of `g` carries the level `A^U` onto
  `A^{gUg⁻¹}`.
* `TauCeti.ClassFieldTheory.conjRepIso`: the coefficient module of a layer is the coefficient
  module of its conjugate, restricted along `conjGalEquiv`.
* `TauCeti.ClassFieldTheory.layerCohomologyConj`, `layerGroundConj`, `layerGalConj`:
  conjugation on ordinary cohomology, on ground levels and on
  abelianized Galois groups.

## Main statements

* `TauCeti.ClassFieldTheory.mem_conjOpenSubgroup`: `x ∈ gUg⁻¹ ↔ g⁻¹xg ∈ U`.
* `TauCeti.ClassFieldTheory.conjugateLayer_one`, `conjugateLayer_mul`: conjugation of layers is
  an action of the ambient group.
* `TauCeti.ClassFieldTheory.map_level_conjOpenSubgroup`: the action of `g` maps `A^U` onto
  `A^{gUg⁻¹}`.

## Implementation notes

The conjugate `gUg⁻¹` is built as the *preimage* of `U` under conjugation by `g⁻¹`, so that
membership in it is definitionally `g⁻¹ * x * g ∈ U` and no image-of-a-subgroup existential has to
be unpacked. Conjugation by `g⁻¹` is continuous, which is all `OpenSubgroup.comap` asks for.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §2.
* J. Neukirch, *Class Field Theory*, Chapter III, §1.
-/

-- The signatures of `conjugateLayer`, `layerCohomologyConj`, `layerGroundConj` and
-- `layerGalConj` below follow the Tau Ceti `ClassFieldTheory` blueprint, `README.md` and
-- `Suggested.lean`.

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Conjugates of open subgroups -/

/-- The conjugate `gUg⁻¹` of an open subgroup, as the preimage of `U` under the continuous
conjugation `x ↦ g⁻¹xg`, so that `x ∈ gUg⁻¹ ↔ g⁻¹xg ∈ U` holds by definition
(`mem_conjOpenSubgroup`); its underlying subgroup is the image of `U` under conjugation by `g`
(`toSubgroup_conjOpenSubgroup`). -/
def conjOpenSubgroup (g : G) (U : OpenSubgroup G) : OpenSubgroup G :=
  U.comap (MulAut.conj g).symm.toMonoidHom ((continuous_const_mul g⁻¹).mul_const g)

/-- Membership in a conjugate open subgroup. -/
@[simp]
theorem mem_conjOpenSubgroup {g : G} {U : OpenSubgroup G} {x : G} :
    x ∈ conjOpenSubgroup g U ↔ g⁻¹ * x * g ∈ U :=
  Iff.rfl

/-- The underlying subgroup of a conjugate open subgroup is the image of the original subgroup
under conjugation by `g`. -/
theorem toSubgroup_conjOpenSubgroup (g : G) (U : OpenSubgroup G) :
    (conjOpenSubgroup g U).toSubgroup = U.toSubgroup.map (MulAut.conj g).toMonoidHom :=
  (Subgroup.comap_equiv_eq_map_symm' (MulAut.conj g).symm U.toSubgroup).trans
    (by rw [MulEquiv.symm_symm])

/-- Conjugation by `1` is the identity on open subgroups. -/
@[simp]
theorem conjOpenSubgroup_one (U : OpenSubgroup G) : conjOpenSubgroup 1 U = U := by
  ext x
  simp only [mem_conjOpenSubgroup, inv_one, one_mul, mul_one]

/-- Conjugation of open subgroups is an action of the ambient group. -/
theorem conjOpenSubgroup_mul (g h : G) (U : OpenSubgroup G) :
    conjOpenSubgroup (g * h) U = conjOpenSubgroup g (conjOpenSubgroup h U) := by
  ext x
  simp only [mem_conjOpenSubgroup, mul_inv_rev, mul_assoc]

/-! ### Conjugate layers -/

section Layer

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The **conjugate layer** `gVg⁻¹ ◁ gUg⁻¹` of a finite normal layer `V ◁ U`. In field notation it
is the layer `g(K)/g(F)`. -/
def conjugateLayer (g : G) (L : NormalLayer G) : NormalLayer G where
  ground := conjOpenSubgroup g L.ground
  top := conjOpenSubgroup g L.top
  top_le_ground := fun _ hx ↦ L.top_le_ground hx
  normal :=
    ⟨fun v hv u ↦ Subgroup.mem_subgroupOf.2 <| by
      have hu : g⁻¹ * (u : G) * g ∈ L.ground := u.2
      have hv' : g⁻¹ * (v : G) * g ∈ L.top := Subgroup.mem_subgroupOf.1 hv
      have h := L.conj_mem_top hu hv'
      rw [OpenSubgroup.mem_toSubgroup, mem_conjOpenSubgroup, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv,
        show g⁻¹ * (↑u * ↑v * (↑u)⁻¹) * g =
          g⁻¹ * ↑u * g * (g⁻¹ * ↑v * g) * (g⁻¹ * ↑u * g)⁻¹ by group]
      exact h⟩

/-- The ground subgroup of the conjugate layer is the conjugate of the ground subgroup. -/
@[simp]
theorem ground_conjugateLayer (g : G) (L : NormalLayer G) :
    (conjugateLayer g L).ground = conjOpenSubgroup g L.ground :=
  (rfl)

/-- The top subgroup of the conjugate layer is the conjugate of the top subgroup. -/
@[simp]
theorem top_conjugateLayer (g : G) (L : NormalLayer G) :
    (conjugateLayer g L).top = conjOpenSubgroup g L.top :=
  (rfl)

/-- Membership in the ground subgroup of a conjugate layer. -/
theorem mem_ground_conjugateLayer {g : G} {L : NormalLayer G} {x : G} :
    x ∈ (conjugateLayer g L).ground ↔ g⁻¹ * x * g ∈ L.ground :=
  Iff.rfl

/-- Membership in the top subgroup of a conjugate layer. -/
theorem mem_top_conjugateLayer {g : G} {L : NormalLayer G} {x : G} :
    x ∈ (conjugateLayer g L).top ↔ g⁻¹ * x * g ∈ L.top :=
  Iff.rfl

/-- Conjugation by `1` is the identity on layers. -/
@[simp]
theorem conjugateLayer_one (L : NormalLayer G) : conjugateLayer 1 L = L :=
  NormalLayer.ext ((ground_conjugateLayer 1 L).trans (conjOpenSubgroup_one _))
    ((top_conjugateLayer 1 L).trans (conjOpenSubgroup_one _))

/-- Conjugation of layers is an action of the ambient group. -/
theorem conjugateLayer_mul (g h : G) (L : NormalLayer G) :
    conjugateLayer (g * h) L = conjugateLayer g (conjugateLayer h L) :=
  NormalLayer.ext (by simp only [ground_conjugateLayer, conjOpenSubgroup_mul])
    (by simp only [top_conjugateLayer, conjOpenSubgroup_mul])

/-! ### Conjugation on Galois groups -/

/-- Conjugation by `g` identifies the ground subgroup `U` of a layer with the ground subgroup
`gUg⁻¹` of its conjugate. -/
def conjGroundEquiv (g : G) (L : NormalLayer G) : L.ground ≃* (conjugateLayer g L).ground :=
  Subgroup.congrOfMapEq (MulAut.conj g) (toSubgroup_conjOpenSubgroup g L.ground).symm

/-- Conjugation on the ground subgroup, read in the ambient group. -/
@[simp]
theorem conjGroundEquiv_apply_coe (g : G) (L : NormalLayer G) (u : L.ground) :
    ((conjGroundEquiv g L u : (conjugateLayer g L).ground) : G) = g * u * g⁻¹ := by
  rw [conjGroundEquiv]
  exact (Subgroup.coe_congrOfMapEq_apply (MulAut.conj g) _ u).trans (MulAut.conj_apply g _)

/-- The inverse of conjugation on the ground subgroup, read in the ambient group. -/
@[simp]
theorem conjGroundEquiv_symm_apply_coe (g : G) (L : NormalLayer G)
    (x : (conjugateLayer g L).ground) :
    (((conjGroundEquiv g L).symm x : L.ground) : G) = g⁻¹ * x * g := by
  rw [conjGroundEquiv]
  exact (Subgroup.coe_congrOfMapEq_symm_apply (MulAut.conj g) _ x).trans
    (MulAut.conj_symm_apply g _)

/-- Conjugation carries the top subgroup of a layer onto the top subgroup of its conjugate. -/
theorem map_relativeTop_conjGroundEquiv (g : G) (L : NormalLayer G) :
    L.relativeTop.map (conjGroundEquiv g L).toMonoidHom = (conjugateLayer g L).relativeTop := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, conjGroundEquiv_apply_coe,
      OpenSubgroup.mem_toSubgroup, mem_top_conjugateLayer,
      show g⁻¹ * (g * (u : G) * g⁻¹) * g = (u : G) by group]
    exact Subgroup.mem_subgroupOf.1 hu
  · intro hx
    refine ⟨(conjGroundEquiv g L).symm x, Subgroup.mem_subgroupOf.2 ?_,
      (conjGroundEquiv g L).apply_symm_apply x⟩
    rw [conjGroundEquiv_symm_apply_coe]
    exact mem_top_conjugateLayer.1 (Subgroup.mem_subgroupOf.1 hx)

/-- **Conjugation on Galois groups:** `U/V ≃ gUg⁻¹/gVg⁻¹`, induced by `conjGroundEquiv`. -/
def conjGalEquiv (g : G) (L : NormalLayer G) : L.Gal ≃* (conjugateLayer g L).Gal :=
  QuotientGroup.congr L.relativeTop (conjugateLayer g L).relativeTop (conjGroundEquiv g L)
    (map_relativeTop_conjGroundEquiv g L)

/-- Conjugation on Galois groups is induced by conjugation on ground subgroups. -/
@[simp]
theorem conjGalEquiv_mk (g : G) (L : NormalLayer G) (u : L.ground) :
    conjGalEquiv g L (QuotientGroup.mk u) = QuotientGroup.mk (conjGroundEquiv g L u) :=
  QuotientGroup.congr_mk _ _ _ _ u

/-! ### Conjugation on levels and coefficient modules -/

section Coefficients

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (F : Formation G)

/-- **The action of `g` carries the level `A^U` onto the level `A^{gUg⁻¹}`.** -/
theorem map_level_conjOpenSubgroup (g : G) (U : OpenSubgroup G) :
    (F.level U).map (F.toRep.ρ g) = F.level (conjOpenSubgroup g U) := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formation.mem_level]
    intro v hv
    rw [mem_conjOpenSubgroup] at hv
    rw [← Module.End.mul_apply, ← map_mul, show v * g = g * (g⁻¹ * v * g) by group, map_mul,
      Module.End.mul_apply, (F.mem_level.1 hx) _ hv]
  · intro hy
    refine ⟨F.toRep.ρ g⁻¹ y, ?_, ?_⟩
    · rw [Formation.mem_level]
      intro u hu
      have hmem : g * u * g⁻¹ ∈ conjOpenSubgroup g U := by
        rw [mem_conjOpenSubgroup, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
        exact hu
      rw [← Module.End.mul_apply, ← map_mul, show u * g⁻¹ = g⁻¹ * (g * u * g⁻¹) by group,
        map_mul, Module.End.mul_apply, (F.mem_level.1 hy) _ hmem]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- **Conjugation on levels:** the action of `g` identifies `A^U` with `A^{gUg⁻¹}`. -/
def levelConj (g : G) (U : OpenSubgroup G) : F.level U ≃ₗ[ℤ] F.level (conjOpenSubgroup g U) :=
  LinearEquiv.ofSubmodules (DistribMulAction.toLinearEquiv ℤ F.toRep.V g) _ _
    (map_level_conjOpenSubgroup F g U)

/-- Conjugation on levels is the action of `g`, read in the ambient module. -/
@[simp]
theorem levelConj_apply_coe (g : G) (U : OpenSubgroup G) (x : F.level U) :
    ((levelConj F g U x : F.level (conjOpenSubgroup g U)) : F.toRep.V) = F.toRep.ρ g x :=
  (rfl)

/-- Conjugation on the top level of a layer, `A^V ≃ A^{gVg⁻¹}`, with its target read as the
coefficient module of the conjugate layer. -/
def topLevelConj (g : G) (L : NormalLayer G) :
    F.level L.top ≃ₗ[ℤ] F.level (conjugateLayer g L).top :=
  levelConj F g L.top

/-- Conjugation on the top level of a layer is the action of `g`, read in the ambient module. -/
@[simp]
theorem topLevelConj_apply_coe (g : G) (L : NormalLayer G) (x : F.level L.top) :
    ((topLevelConj F g L x : F.level (conjugateLayer g L).top) : F.toRep.V) = F.toRep.ρ g x :=
  (rfl)

/-- Conjugation on the top level intertwines the actions of the two Galois groups through
`conjGalEquiv`: `g · (γ · x) = (gγg⁻¹) · (g · x)`. -/
theorem topLevelConj_comp_rep_ρ (g : G) (L : NormalLayer G) (γ : (conjugateLayer g L).Gal) :
    (topLevelConj F g L).toLinearMap ∘ₗ (L.rep F).ρ ((conjGalEquiv g L).symm γ) =
      ((conjugateLayer g L).rep F).ρ γ ∘ₗ (topLevelConj F g L).toLinearMap := by
  induction γ using QuotientGroup.induction_on with
  | H x =>
    have hx : (conjGalEquiv g L).symm (QuotientGroup.mk x) =
        QuotientGroup.mk ((conjGroundEquiv g L).symm x) := by
      rw [MulEquiv.symm_apply_eq, conjGalEquiv_mk, MulEquiv.apply_symm_apply]
    rw [hx]
    ext y
    -- Expose the ambient-module coercions hidden behind the representation wrappers before
    -- applying the public coercion lemmas.
    change ((topLevelConj F g L ((L.rep F).ρ (QuotientGroup.mk ((conjGroundEquiv g L).symm x)) y) :
        F.level (conjugateLayer g L).top) : F.toRep.V) =
      ((((conjugateLayer g L).rep F).ρ (QuotientGroup.mk x) (topLevelConj F g L y) :
        F.level (conjugateLayer g L).top) : F.toRep.V)
    rw [topLevelConj_apply_coe, L.rep_ρ_mk_apply_coe, (conjugateLayer g L).rep_ρ_mk_apply_coe,
      topLevelConj_apply_coe, conjGroundEquiv_symm_apply_coe, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

/-- **The coefficient module of a layer is the coefficient module of its conjugate**, read as a
representation of the Galois group of the conjugate along `conjGalEquiv`. -/
def conjRepIso (g : G) (L : NormalLayer G) :
    Rep.res (conjGalEquiv g L).symm.toMonoidHom (L.rep F) ≅ (conjugateLayer g L).rep F :=
  Rep.mkIso (Representation.Equiv.mk (topLevelConj F g L) (topLevelConj_comp_rep_ρ F g L))

/-- The identification of coefficient modules is the action of `g`, read in the ambient
module. -/
@[simp]
theorem conjRepIso_hom_apply_coe (g : G) (L : NormalLayer G) (x : F.level L.top) :
    (((conjRepIso F g L).hom.hom x : F.level (conjugateLayer g L).top) : F.toRep.V) =
      F.toRep.ρ g x :=
  (rfl)

end Coefficients

/-! ### Conjugation on cohomology, ground levels and abelianized Galois groups -/

section Maps

variable (F : Formation G)

/-- **Conjugation on ordinary finite-layer cohomology**, `H^n(U/V, A^V) → H^n(gUg⁻¹/gVg⁻¹,
A^{gVg⁻¹})`: the map of cohomology induced by `conjGalEquiv` and `conjRepIso`. -/
def layerCohomologyConj (g : G) (L : NormalLayer G) (n : ℕ) :
    L.H F n →+ (conjugateLayer g L).H F n :=
  (groupCohomology.map (conjGalEquiv g L).symm.toMonoidHom (conjRepIso F g L).hom n).hom
    |>.toAddMonoidHom

/-- **Conjugation on ground levels:** the action of `g` carries `A^U` onto `A^{gUg⁻¹}`. -/
def layerGroundConj (g : G) (L : NormalLayer G) :
    F.level L.ground →+ F.level (conjugateLayer g L).ground :=
  (levelConj F g L.ground).toLinearMap.toAddMonoidHom

/-- Conjugation on ground levels is the action of `g`, read in the ambient module. -/
@[simp]
theorem layerGroundConj_apply_coe (g : G) (L : NormalLayer G) (x : F.level L.ground) :
    ((layerGroundConj F g L x : F.level (conjugateLayer g L).ground) : F.toRep.V) =
      F.toRep.ρ g x := by
  rw [layerGroundConj]
  exact levelConj_apply_coe F g L.ground x

/-- **Conjugation on abelianized Galois groups**, written additively. -/
def layerGalConj (g : G) (L : NormalLayer G) :
    Additive (Abelianization L.Gal) →+ Additive (Abelianization (conjugateLayer g L).Gal) :=
  MonoidHom.toAdditive (Abelianization.map (conjGalEquiv g L).toMonoidHom)

/-- Conjugation on abelianized Galois groups sends the class of `γ` to the class of
`conjGalEquiv g L γ`. -/
@[simp]
theorem layerGalConj_of (g : G) (L : NormalLayer G) (γ : L.Gal) :
    layerGalConj g L (Additive.ofMul (Abelianization.of γ)) =
      Additive.ofMul (Abelianization.of (conjGalEquiv g L γ)) := by
  rw [layerGalConj, MonoidHom.toAdditive_apply_apply, toMul_ofMul, Abelianization.map_of,
    MulEquiv.coe_toMonoidHom]

/-- **In degree zero, conjugation of cohomology is conjugation of ground levels.** Read through the
identification of `H⁰(U/V, A^V)` with the ground level `A^U`, conjugating a class by `g` is the
action of `g` on the ground level, `layerGroundConj`. -/
theorem groundLevelEquiv_layerCohomologyConj_zero_apply (g : G) (L : NormalLayer G) (x : L.H F 0) :
    (conjugateLayer g L).groundLevelEquiv F
        ((groupCohomology.H0Iso ((conjugateLayer g L).rep F)).hom.hom
          (layerCohomologyConj F g L 0 x)) =
      layerGroundConj F g L
        (L.groundLevelEquiv F ((groupCohomology.H0Iso (L.rep F)).hom.hom x)) := by
  refine Subtype.ext ?_
  rw [NormalLayer.groundLevelEquiv_apply_coe, layerGroundConj_apply_coe,
    NormalLayer.groundLevelEquiv_apply_coe, layerCohomologyConj]
  have h := groupCohomology.map_H0Iso_hom_f_apply (conjGalEquiv g L).symm.toMonoidHom
    (conjRepIso F g L).hom x
  exact (congrArg Subtype.val h).trans (conjRepIso_hom_apply_coe F g L _)

end Maps

end Layer

end TauCeti.ClassFieldTheory
