/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Finite
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Intermediate
public import TauCeti.Geometry.Symplectic.Floer.Seamed.Cover
import TauCeti.GroupTheory.Finiteness

/-!
# The torus-class cover of a space of seamed paths

Let `φ` be a homeomorphism of a space `F`, with mapping torus `Y_φ`, and let `C` be the path
component of a `φ`-seamed path `γ₀` in the space of seamed paths `TauCeti.SeamedPath φ`. A loop of
seamed paths at `γ₀` sweeps out a torus in `Y_φ`, whose class is its torus class
`π₁(C, γ₀) → H₂(Y_φ; ℤ)` (`TauCeti.Floer.seamedTorusClassHom`). Its image is the group

`H ⊆ H₂(Y_φ; ℤ)`

of classes swept out by loops of seamed paths at `γ₀` (`TauCeti.Floer.seamedTorusClassGroup`). In
the Floer–Novikov theory of a symplectomorphism `φ` of a closed symplectic manifold `F`, every
period and index character of the generators factors through `H`: the symplectic area, the first
Chern number and the action of a closed one-form are evaluated on the swept tori.

**Finite generation.** The group `H` is finitely generated as soon as `H₂(Y_φ; ℤ)` is, being a
subgroup of a finitely generated abelian group (`TauCeti.Floer.fg_seamedTorusClassGroup`). This
holds when `F` has finite CW type, for instance when it is a compact manifold
(`TauCeti.Floer.fg_seamedTorusClassGroup_of_finiteCWType`), through the Wang sequence of the
mapping torus (`TauCeti.MappingTorus.finite_singularHomology`). No finiteness of `π₁(C, γ₀)` is
needed, and none is available in general. The period group `Γ` of a pair of transgressions
`Iω`, `Ic` is the image of `H` under them (`TauCeti.Floer.map_seamedTorusClassGroup`), so it is
finitely generated as well (`TauCeti.Floer.fg_seamedPeriodGroup`).

**The torus-class cover.** The **torus-class cover** `TauCeti.Floer.TorusClassCover γ₀` is the
connected covering space of `C` attached to the kernel of the torus class
(`TauCeti.Floer.torusClassCoverSubgroup`). A point over `γ` is a homotopy class of paths in `C`
from `γ₀` to `γ`, modulo the loops of seamed paths sweeping out null-homologous tori. When `C` is
locally path-connected and semilocally simply connected, the projection is a covering map
(`TauCeti.Floer.isCoveringMap_torusClassCoverProj`), so paths and their homotopies in `C` lift to
it. The cover is regular with deck group `H` (`TauCeti.Floer.torusClassCoverDeckEquiv`): the torus
class of a loop acts by transport around that loop (`TauCeti.Floer.seamedTorusClass_vadd_mk`), and
every fibre is a torsor under `H` (`TauCeti.Floer.instAddTorsorTorusClassCoverFiber`), the
difference of two points of a fibre being the torus class of the loop relating them
(`TauCeti.Floer.TorusClassCover.vsub_mk`).

Every loop with null-homologous swept torus has trivial period class, so the torus-class cover
covers the reference-cylinder cover of every pair of transgressions
(`TauCeti.Floer.exists_isCoveringMap_referenceCylinderCoverProj_comp_eq`).

## Main definitions

* `TauCeti.Floer.seamedTorusClassGroup γ₀`: the group `H` of classes swept out by loops of seamed
  paths at `γ₀`.
* `TauCeti.Floer.seamedTorusClass γ₀`: the torus class onto `H`.
* `TauCeti.Floer.torusClassCoverSubgroup γ₀`: its kernel, read in the fundamental group of `C`.
* `TauCeti.Floer.TorusClassCover`, `TauCeti.Floer.torusClassCoverProj`: the torus-class cover and
  its projection to `C`.
* `TauCeti.Floer.torusClassCoverDeckEquiv`: the deck group of the cover is `H`.

## Main results

* `TauCeti.Floer.fg_seamedTorusClassGroup`,
  `TauCeti.Floer.fg_seamedTorusClassGroup_of_finiteCWType`: `H` is finitely generated.
* `TauCeti.Floer.fg_seamedPeriodGroup`: the period group of a pair of transgressions is finitely
  generated.
* `TauCeti.Floer.isCoveringMap_torusClassCoverProj`, `TauCeti.Floer.isRegular_torusClassCoverProj`:
  the cover is a regular covering space.
* `TauCeti.Floer.mem_range_mapOfEq_torusClassCoverProj_iff`: a loop of seamed paths lifts to a
  loop of the cover exactly when the torus it sweeps out is null-homologous.
* `TauCeti.Floer.seamedTorusClass_vadd_mk`, `TauCeti.Floer.TorusClassCover.vsub_mk`: the deck
  action is transport around loops, and differences in a fibre are torus classes.
* `TauCeti.Floer.exists_isCoveringMap_referenceCylinderCoverProj_comp_eq`: the torus-class
  cover covers the reference-cylinder cover.

## References

* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, §3.1, on the covering spaces of the space of
  sections of the mapping torus in Floer–Novikov theory.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3, on the
  covering space attached to a subgroup of the fundamental group and its deck group.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti.UniversalCover

namespace TauCeti.Floer

variable {F : Type} [TopologicalSpace F] {φ : F ≃ₜ F} (γ₀ : SeamedPath φ)

/-! ### The group of swept classes -/

/-- **The group `H` of swept classes** of the path component `C` of `γ₀`: the classes in
`H₂(Y_φ; ℤ)` of the tori swept out by loops of seamed paths at `γ₀`, the image of the torus
class. -/
def seamedTorusClassGroup :
    AddSubgroup (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ))) :=
  (seamedTorusClassHom γ₀).range

/-- A class lies in `H` exactly when it is the torus class of a loop of seamed paths at `γ₀`. -/
theorem mem_seamedTorusClassGroup_iff
    {A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ))} :
    A ∈ seamedTorusClassGroup γ₀ ↔ ∃ a, seamedTorusClassHom γ₀ a = A :=
  AddMonoidHom.mem_range

/-- **The torus class onto `H`**: the torus class of a loop of seamed paths at `γ₀`, with its
codomain restricted to its image. -/
def seamedTorusClass :
    Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀)) →+
      seamedTorusClassGroup γ₀ :=
  (seamedTorusClassHom γ₀).rangeRestrict

/-- The torus class onto `H`, as a class of `H₂(Y_φ; ℤ)`, is the torus class of the loop. -/
@[simp]
theorem coe_seamedTorusClass
    (a : Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))) :
    (seamedTorusClass γ₀ a : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (MappingTorus φ))) = seamedTorusClassHom γ₀ a :=
  (rfl)

/-- Every element of `H` is the torus class of a loop of seamed paths at `γ₀`. -/
theorem seamedTorusClass_surjective : Function.Surjective (seamedTorusClass γ₀) :=
  AddMonoidHom.rangeRestrict_surjective _

/-- **The group of swept classes is finitely generated** when the second homology of the mapping
torus is, as a subgroup of a finitely generated abelian group. No finiteness of the fundamental
group of the path component is used. -/
theorem fg_seamedTorusClassGroup
    [Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ)))] :
    (seamedTorusClassGroup γ₀).FG :=
  -- The `ℤ`-module structure of a `ModuleCat ℤ` object is not syntactically the canonical one of
  -- an additive group, so `convert` identifies the two, `ℤ`-module structures being unique.
  have : AddGroup.FG (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ))) :=
    Module.Finite.iff_addGroup_fg.1 (by convert ‹Module.Finite ℤ _›; exact Subsingleton.elim _ _)
  (AddGroup.fg_iff_addSubgroup_fg _).1 inferInstance

/-- **The group of swept classes is finitely generated** when `F` has finite CW type, for
instance when it is a compact manifold (`TauCeti.FiniteCWType.of_isManifold`): the second homology
of the mapping torus is then finitely generated
(`TauCeti.MappingTorus.finite_singularHomology`). -/
theorem fg_seamedTorusClassGroup_of_finiteCWType [FiniteCWType F] :
    (seamedTorusClassGroup γ₀).FG :=
  have := MappingTorus.finite_singularHomology φ (ModuleCat.of ℤ ℤ) 2
  fg_seamedTorusClassGroup γ₀

variable (Iω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (MappingTorus φ)) →+ ℝ)
  (Ic : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (MappingTorus φ)) →+ ℤ)

/-- **The period group is the image of the group of swept classes** under the pair of
transgressions `(Iω, Ic)`. -/
theorem map_seamedTorusClassGroup :
    (seamedTorusClassGroup γ₀).map (Iω.prod Ic) = seamedPeriodGroup γ₀ Iω Ic := by
  ext p
  simp [mem_seamedTorusClassGroup_iff, mem_seamedPeriodGroup_iff, seamedPeriodHom_eq_comp]

/-- **The period group is finitely generated** when the second homology of the mapping torus is,
as the image of the group of swept classes. -/
theorem fg_seamedPeriodGroup
    [Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ)))] :
    (seamedPeriodGroup γ₀ Iω Ic).FG := by
  rw [← map_seamedTorusClassGroup, AddSubgroup.fg_iff_addSubmonoid_fg,
    AddSubgroup.map_toAddSubmonoid]
  exact ((AddSubgroup.fg_iff_addSubmonoid_fg _).1 (fg_seamedTorusClassGroup γ₀)).map _

/-! ### The torus-class cover -/

/-- **The subgroup of the torus-class cover**: the classes in the fundamental group of the path
component of `γ₀` of the loops of seamed paths whose swept-out torus is null-homologous in the
mapping torus, the kernel of the torus class. -/
def torusClassCoverSubgroup :
    Subgroup (FundamentalGroup (pathComponent γ₀) (pathComponentSelf γ₀)) :=
  additiveKerSubgroup (pathComponentSelf γ₀) (seamedTorusClass γ₀)

/-- A class of the fundamental group of the path component of `γ₀` lies in the subgroup of the
torus-class cover exactly when its torus class vanishes. -/
@[simp]
theorem mem_torusClassCoverSubgroup_iff
    (g : FundamentalGroup (pathComponent γ₀) (pathComponentSelf γ₀)) :
    g ∈ torusClassCoverSubgroup γ₀ ↔
      seamedTorusClassHom γ₀
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)) = 0 := by
  rw [torusClassCoverSubgroup, mem_additiveKerSubgroup_iff, ← ZeroMemClass.coe_eq_zero,
    coe_seamedTorusClass]

/-- The subgroup of the torus-class cover is normal, being the kernel of a homomorphism. -/
instance torusClassCoverSubgroup_normal : (torusClassCoverSubgroup γ₀).Normal :=
  additiveKerSubgroup_normal _ _

/-- A loop of seamed paths sweeping out a null-homologous torus has trivial period class: the
subgroup of the torus-class cover lies in that of the reference-cylinder cover of every pair of
transgressions. -/
theorem torusClassCoverSubgroup_le_referenceCylinderCoverSubgroup :
    torusClassCoverSubgroup γ₀ ≤ referenceCylinderCoverSubgroup γ₀ Iω Ic := fun g hg ↦ by
  rw [mem_torusClassCoverSubgroup_iff] at hg
  rw [mem_referenceCylinderCoverSubgroup_iff, seamedPeriodHom_eq_comp, AddMonoidHom.comp_apply, hg,
    map_zero]

/-- **The torus-class cover** of the path component `C` of a seamed path `γ₀`: the connected
covering space of `C` attached to the subgroup `torusClassCoverSubgroup γ₀` of `π₁(C, γ₀)`. A point
over `γ` is a homotopy class of paths in `C` from `γ₀` to `γ`, modulo the loops of seamed paths
whose swept-out torus is null-homologous in the mapping torus. -/
abbrev TorusClassCover : Type :=
  SubgroupQuotient (pathComponentSelf γ₀) (torusClassCoverSubgroup γ₀)

/-- The projection of the torus-class cover to the path component of `γ₀`. -/
abbrev torusClassCoverProj : TorusClassCover γ₀ → pathComponent γ₀ :=
  subgroupQuotientProj (pathComponentSelf γ₀) (torusClassCoverSubgroup γ₀)

section Covering

variable [LocallyPathConnectedSpace (pathComponent γ₀)]
  [SemilocallySimplyConnectedSpace (pathComponent γ₀)]

/-- **The torus-class cover is a covering space** of the path component of `γ₀`, when that
component is locally path-connected and semilocally simply connected. -/
theorem isCoveringMap_torusClassCoverProj : IsCoveringMap (torusClassCoverProj γ₀) :=
  isCoveringMap_subgroupQuotientProj _ _

/-- **A loop of seamed paths lifts to a loop of the torus-class cover**, at its base point, exactly
when the torus it sweeps out is null-homologous in the mapping torus. -/
theorem mem_range_mapOfEq_torusClassCoverProj_iff
    (g : FundamentalGroup (pathComponent γ₀) (pathComponentSelf γ₀)) :
    g ∈ (FundamentalGroup.mapOfEq
        ⟨torusClassCoverProj γ₀, continuous_subgroupQuotientProj _ _⟩
        (subgroupQuotientProj_basepoint _ _)).range ↔
      seamedTorusClassHom γ₀
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)) = 0 := by
  rw [range_mapOfEq_subgroupQuotientProj, mem_torusClassCoverSubgroup_iff]

/-- The torus-class cover is a regular covering of the path component of `γ₀`. -/
theorem isRegular_torusClassCoverProj : Deck.IsRegular (torusClassCoverProj γ₀) :=
  (isRegular_subgroupQuotientProj_iff_normal _ _).mpr inferInstance

/-- **The deck group of the torus-class cover is the group `H` of swept classes**: the torus class
maps `π₁(C, γ₀)` onto `H` with kernel `torusClassCoverSubgroup γ₀`, and the deck group of the
cover attached to the kernel of a surjective homomorphism is its target. -/
def torusClassCoverDeckEquiv :
    Multiplicative (seamedTorusClassGroup γ₀) ≃* deck (torusClassCoverProj γ₀) :=
  deckAdditiveKerEquiv _ (seamedTorusClass γ₀) (seamedTorusClass_surjective γ₀)

/-- The deck transformation of the torus class of a loop `a` of seamed paths acts on the
torus-class cover through the action of `a` on the universal cover of the path component of
`γ₀`. -/
@[simp]
theorem torusClassCoverDeckEquiv_seamedTorusClass_apply_mk
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀)) :
    (torusClassCoverDeckEquiv γ₀ (Multiplicative.ofAdd
        (seamedTorusClass γ₀ (Additive.ofMul a)))).val (Quotient.mk'' e) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  deckAdditiveKerEquiv_apply_mk _ _ (seamedTorusClass_surjective γ₀) a e

/-- The group of swept classes acts on the torus-class cover through its deck group. -/
noncomputable instance instAddActionTorusClassCover :
    AddAction (seamedTorusClassGroup γ₀) (TorusClassCover γ₀) :=
  Deck.addActionOfMulEquiv (torusClassCoverDeckEquiv γ₀)

namespace TorusClassCover

/-- The group of swept classes acts on the torus-class cover by the deck transformations of
`torusClassCoverDeckEquiv`. -/
theorem vadd_def (g : seamedTorusClassGroup γ₀) (e : TorusClassCover γ₀) :
    g +ᵥ e = (torusClassCoverDeckEquiv γ₀ (Multiplicative.ofAdd g)).val e :=
  Deck.addActionOfMulEquiv_vadd (torusClassCoverDeckEquiv γ₀) g e

end TorusClassCover

open TorusClassCover

/-- The action of the group of swept classes preserves the projection of the torus-class
cover. -/
@[simp]
theorem torusClassCoverProj_vadd (g : seamedTorusClassGroup γ₀) (e : TorusClassCover γ₀) :
    torusClassCoverProj γ₀ (g +ᵥ e) = torusClassCoverProj γ₀ e :=
  Deck.proj_addActionOfMulEquiv_vadd (torusClassCoverDeckEquiv γ₀) g e

/-- **Transporting a point of the torus-class cover around a loop of seamed paths adds the class
of the torus it sweeps out**: the torus class of `a ∈ π₁(C, γ₀)` acts on the torus-class cover as
`a` acts on the universal cover of `C`. -/
@[simp]
theorem seamedTorusClass_vadd_mk
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀)) :
    seamedTorusClass γ₀ (Additive.ofMul a) +ᵥ (Quotient.mk'' e : TorusClassCover γ₀) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  deckAdditiveKerEquiv_vadd_mk _ _ (seamedTorusClass_surjective γ₀) a e

/-- **Each fibre of the torus-class cover is a torsor under the group of swept classes**: the deck
group `H` of the regular cover acts simply transitively on every fibre. -/
noncomputable instance instAddTorsorTorusClassCoverFiber (γ : pathComponent γ₀) :
    AddTorsor (seamedTorusClassGroup γ₀) (torusClassCoverProj γ₀ ⁻¹' {γ}) :=
  Deck.fiberAddTorsorOfMulEquiv (isCoveringMap_torusClassCoverProj γ₀)
    (isRegular_torusClassCoverProj γ₀) (torusClassCoverDeckEquiv γ₀) γ

/-- The action of the group of swept classes on a fibre of the torus-class cover is its action on
the cover. -/
@[simp]
theorem TorusClassCover.coe_vadd_fiber {γ : pathComponent γ₀} (g : seamedTorusClassGroup γ₀)
    (e : torusClassCoverProj γ₀ ⁻¹' {γ}) :
    ((g +ᵥ e : torusClassCoverProj γ₀ ⁻¹' {γ}) : TorusClassCover γ₀) =
      g +ᵥ (e : TorusClassCover γ₀) :=
  Deck.coe_fiberAddTorsorOfMulEquiv_vadd _ _ (torusClassCoverDeckEquiv γ₀) g e

/-- **The difference of two points of a fibre of the torus-class cover is the torus class of the
loop relating them**: transporting `e` around a loop `a` of seamed paths gives the point whose
difference from `e` is the class of the torus swept out by `a`. -/
@[simp]
theorem TorusClassCover.vsub_mk {γ : pathComponent γ₀}
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀))
    (h₁ : (Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :
      TorusClassCover γ₀) ∈ torusClassCoverProj γ₀ ⁻¹' {γ})
    (h₂ : (Quotient.mk'' e : TorusClassCover γ₀) ∈ torusClassCoverProj γ₀ ⁻¹' {γ}) :
    (⟨_, h₁⟩ : torusClassCoverProj γ₀ ⁻¹' {γ}) -ᵥ ⟨_, h₂⟩ =
      seamedTorusClass γ₀ (Additive.ofMul a) :=
  deckAdditiveKerEquiv_vsub_mk _ _ (seamedTorusClass_surjective γ₀) a e h₁ h₂

/-- **The torus-class cover covers the reference-cylinder cover** of every pair of transgressions
`(Iω, Ic)`: there is a covering map between them over the path component of `γ₀`, matching the
distinguished points. -/
theorem exists_isCoveringMap_referenceCylinderCoverProj_comp_eq :
    ∃ g : C(TorusClassCover γ₀, ReferenceCylinderCover γ₀ Iω Ic), IsCoveringMap g ∧
      g (SubgroupQuotient.basepoint _ _) = SubgroupQuotient.basepoint _ _ ∧
      referenceCylinderCoverProj γ₀ Iω Ic ∘ g = torusClassCoverProj γ₀ :=
  (exists_isCoveringMap_subgroupQuotientProj_comp_eq_iff_le _ _ _).2
    (torusClassCoverSubgroup_le_referenceCylinderCoverSubgroup γ₀ Iω Ic)

end Covering

end TauCeti.Floer
