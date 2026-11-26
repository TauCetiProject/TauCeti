/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.PathComponent
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.SeamedTorusClass
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.AdditiveKer

/-!
# The reference-cylinder cover of a space of seamed paths

The Floer theory of a symplectomorphism `φ` of a closed symplectic manifold `F` is built on the
space of `φ`-seamed paths, the paths `γ` with `γ 1 = φ (γ 0)` (`TauCeti.SeamedPath`), whose constant
paths are the fixed points of `φ`. The generators of the Floer complex, the fixed points, lie in
path components of this space; in each such component `C` one fixes a reference seamed path `γ₀`. A
generator `γ` of `C` is then lifted to a homotopy class of paths from `γ₀` to `γ` in `C`, a
*reference cylinder*, modulo the loops at `γ₀` that are invisible to the action and the index. This
file constructs that covering space of `C`.

A loop of seamed paths at `γ₀` sweeps out a torus in the mapping torus `Y_φ`, with class
`TauCeti.SeamedPath.torusClassHom` in `H₂(Y_φ; ℤ)`. Let `Iω : H₂(Y_φ; ℤ) → ℝ` and
`Ic : H₂(Y_φ; ℤ) → ℤ` be homomorphisms: in the application, the periods of the closed vertical
two-form induced by the symplectic form, and the first Chern number of the vertical tangent bundle.
They are the two transgressions of loops of seamed paths. Together they define the **period
homomorphism** `π₁(C, γ₀) → ℝ × ℤ` (`TauCeti.Floer.seamedPeriodHom`), whose image is the
**period group** `Γ` (`TauCeti.Floer.seamedPeriodGroup`); the **period class** of a loop is its
image in `Γ` (`TauCeti.Floer.seamedPeriodClass`). The two transgressions need not vanish when `ω`
and `c₁` vanish on spheres of `F`: for `φ = id` on a torus `F = ℝ² / ℤ²`, the loop `s ↦ γ_s` of
seamed paths `γ_s t = (t, s)` sweeps out a torus covering `F` once, of nonzero area.

The **reference-cylinder cover** `TauCeti.Floer.ReferenceCylinderCover γ₀ Iω Ic` is the connected
covering space of `C` attached to the joint kernel of the two transgressions
(`TauCeti.Floer.referenceCylinderCoverSubgroup`), the quotient of the universal cover of `C` by
it. When `C` is locally path-connected and semilocally simply connected, for instance when the
space of seamed paths is, the projection is a covering map
(`TauCeti.Floer.isCoveringMap_referenceCylinderCoverProj`), so paths and their homotopies in `C`
lift to it. The cover is regular with deck group `Γ`
(`TauCeti.Floer.referenceCylinderCoverDeckEquiv`): the period class of a loop acts by transport
around that loop (`TauCeti.Floer.seamedPeriodClass_vadd_mk`), and every fibre is a
torsor under `Γ` (`TauCeti.Floer.instAddTorsorReferenceCylinderCoverFiber`), the difference of two
points of a fibre being the period class of the loop relating them
(`TauCeti.Floer.ReferenceCylinderCover.vsub_mk`).

This is the analogue, for seamed paths, of the cap cover of the contractible free loops
(`TauCeti.Floer.CapCover`): for `φ = id` the seamed paths are the free loops, and the reference
cylinder replaces the cap. Both are covers attached to the kernel of an onto homomorphism
`π₁ → Γ`, and their deck groups, actions and fibre torsors come from that generic construction
(`TauCeti.UniversalCover.deckAdditiveKerEquiv`).

## Main definitions

* `TauCeti.Floer.seamedTorusClassHom γ₀`: the torus class `π₁(C, γ₀) → H₂(Y_φ; ℤ)`.
* `TauCeti.Floer.seamedPeriodHom γ₀ Iω Ic`: the period homomorphism `π₁(C, γ₀) → ℝ × ℤ`.
* `TauCeti.Floer.seamedPeriodGroup γ₀ Iω Ic`: its image, the period group `Γ`.
* `TauCeti.Floer.seamedPeriodClass γ₀ Iω Ic`: the period homomorphism onto `Γ`.
* `TauCeti.Floer.referenceCylinderCoverSubgroup γ₀ Iω Ic`: its kernel, read in the fundamental group
  of `C`.
* `TauCeti.Floer.ReferenceCylinderCover`, `TauCeti.Floer.referenceCylinderCoverProj`: the
  reference-cylinder cover and its projection to `C`.
* `TauCeti.Floer.referenceCylinderCoverDeckEquiv`: the deck group of the cover is `Γ`.

## Main results

* `TauCeti.Floer.seamedPeriodHom_eq_zero_iff`: a loop of seamed paths has trivial period class
  exactly when both transgressions vanish on the torus it sweeps out.
* `TauCeti.Floer.isCoveringMap_referenceCylinderCoverProj`,
  `TauCeti.Floer.isRegular_referenceCylinderCoverProj`: the cover is a regular covering space.
* `TauCeti.Floer.mem_range_mapOfEq_referenceCylinderCoverProj_iff`: a loop of seamed paths lifts
  to a loop of the cover exactly when both transgressions vanish on the torus it sweeps out.
* `TauCeti.Floer.seamedPeriodClass_vadd_mk`: the period class of a loop acts on the
  cover as the loop acts on the universal cover.
* `TauCeti.Floer.ReferenceCylinderCover.vsub_mk`: the difference of two points of a fibre is the
  period class of the loop relating them.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the covering space of capped loops.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, §3.1.
* A. Hatcher, *Algebraic Topology*, Section 1.3, on the covering space attached to a subgroup of
  the fundamental group and its deck group.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti.UniversalCover

namespace TauCeti.Floer

variable {F : Type} [TopologicalSpace F] {φ : F ≃ₜ F} (γ₀ : SeamedPath φ)
  {Iω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (MappingTorus φ)) →+ ℝ}
  {Ic : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of (MappingTorus φ)) →+ ℤ}

/-! ### The period homomorphism and the period group -/

/-- **The torus class of a loop of seamed paths in the path component `C` of `γ₀`**
`π₁(C, γ₀) → H₂(Y_φ; ℤ)`: the class of the torus that the loop sweeps out in the mapping torus,
`TauCeti.SeamedPath.torusClassHom` read through the inclusion of `C` into the space of seamed
paths. -/
def seamedTorusClassHom :
    Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀)) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (MappingTorus φ)) :=
  (SeamedPath.torusClassHom φ γ₀).comp
    (HomotopyGroup.mapHom (⟨Subtype.val, continuous_subtypeVal⟩ :
      C(pathComponent γ₀, SeamedPath φ)) rfl).toAdditive

/-- The torus class of a loop in the path component of `γ₀` is the torus class of the same loop
of seamed paths. -/
theorem seamedTorusClassHom_apply
    (a : Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))) :
    seamedTorusClassHom γ₀ a =
      SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
          a.toMul)) :=
  (rfl)

variable (Iω Ic) in
/-- **The period homomorphism of a loop of seamed paths** `π₁(C, γ₀) → ℝ × ℤ`, on the path
component `C` of `γ₀`: a loop of `φ`-seamed paths at `γ₀` goes to the values of the two
transgressions `Iω` and `Ic` on the class of the torus it sweeps out in the mapping torus. -/
def seamedPeriodHom :
    Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀)) →+ ℝ × ℤ :=
  (Iω.prod Ic).comp (seamedTorusClassHom γ₀)

/-- The period homomorphism is the torus class followed by the pair of transgressions. -/
theorem seamedPeriodHom_eq_comp :
    seamedPeriodHom γ₀ Iω Ic = (Iω.prod Ic).comp (seamedTorusClassHom γ₀) :=
  (rfl)

/-- The first coordinate of the period class of a loop of seamed paths is the value of `Iω` on
the torus it sweeps out. -/
@[simp]
theorem fst_seamedPeriodHom
    (a : Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))) :
    (seamedPeriodHom γ₀ Iω Ic a).1 =
      Iω (SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
          a.toMul))) :=
  (rfl)

/-- The second coordinate of the period class of a loop of seamed paths is the value of `Ic` on
the torus it sweeps out. -/
@[simp]
theorem snd_seamedPeriodHom
    (a : Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))) :
    (seamedPeriodHom γ₀ Iω Ic a).2 =
      Ic (SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
          a.toMul))) :=
  (rfl)

/-- **The kernel of the period homomorphism**: a loop of seamed paths has trivial period class
exactly when both transgressions vanish on the torus it sweeps out. -/
theorem seamedPeriodHom_eq_zero_iff
    (a : Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))) :
    seamedPeriodHom γ₀ Iω Ic a = 0 ↔
      Iω (SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
            a.toMul))) = 0 ∧
        Ic (SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
            a.toMul))) = 0 := by
  rw [Prod.ext_iff, fst_seamedPeriodHom, snd_seamedPeriodHom, Prod.fst_zero, Prod.snd_zero]

variable (Iω Ic) in
/-- **The period group** `Γ ⊆ ℝ × ℤ` of the path component of `γ₀`: the values of the two
transgressions on the tori swept out by loops of seamed paths at `γ₀`, the image of the period
homomorphism. -/
def seamedPeriodGroup : AddSubgroup (ℝ × ℤ) :=
  (seamedPeriodHom γ₀ Iω Ic).range

/-- A pair lies in the period group exactly when it is the period class of a loop of seamed
paths at `γ₀`. -/
theorem mem_seamedPeriodGroup_iff {p : ℝ × ℤ} :
    p ∈ seamedPeriodGroup γ₀ Iω Ic ↔ ∃ a, seamedPeriodHom γ₀ Iω Ic a = p :=
  AddMonoidHom.mem_range

variable (Iω Ic) in
/-- **The period class** of a loop of seamed paths at `γ₀`, as an element of the period group:
the period homomorphism with its codomain restricted to its image. -/
def seamedPeriodClass :
    Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀)) →+
      seamedPeriodGroup γ₀ Iω Ic :=
  (seamedPeriodHom γ₀ Iω Ic).rangeRestrict

/-- The period class of a loop of seamed paths, as a pair, is its image under the period
homomorphism. -/
@[simp]
theorem coe_seamedPeriodClass
    (a : Additive (HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))) :
    (seamedPeriodClass γ₀ Iω Ic a : ℝ × ℤ) = seamedPeriodHom γ₀ Iω Ic a :=
  (rfl)

/-- Every element of the period group is the period class of a loop of seamed paths at `γ₀`. -/
theorem seamedPeriodClass_surjective : Function.Surjective (seamedPeriodClass γ₀ Iω Ic) :=
  AddMonoidHom.rangeRestrict_surjective _

/-! ### The reference-cylinder cover -/

variable (Iω Ic) in
/-- **The subgroup of the reference-cylinder cover**: the classes in the fundamental group of the
path component of `γ₀` of the loops of seamed paths on whose swept-out torus both transgressions
vanish, the kernel of the period homomorphism. -/
def referenceCylinderCoverSubgroup :
    Subgroup (FundamentalGroup (pathComponent γ₀) (pathComponentSelf γ₀)) :=
  additiveKerSubgroup (pathComponentSelf γ₀) (seamedPeriodClass γ₀ Iω Ic)

/-- A class of the fundamental group of the path component of `γ₀` lies in the subgroup of the
reference-cylinder cover exactly when its period class vanishes. -/
@[simp]
theorem mem_referenceCylinderCoverSubgroup_iff
    (g : FundamentalGroup (pathComponent γ₀) (pathComponentSelf γ₀)) :
    g ∈ referenceCylinderCoverSubgroup γ₀ Iω Ic ↔
      seamedPeriodHom γ₀ Iω Ic
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)) = 0 := by
  rw [referenceCylinderCoverSubgroup, mem_additiveKerSubgroup_iff, ← ZeroMemClass.coe_eq_zero,
    coe_seamedPeriodClass]

/-- The subgroup of the reference-cylinder cover is normal, being the kernel of a
homomorphism. -/
instance referenceCylinderCoverSubgroup_normal : (referenceCylinderCoverSubgroup γ₀ Iω Ic).Normal :=
  additiveKerSubgroup_normal _ _

variable (Iω Ic) in
/-- **The reference-cylinder cover** of the path component `C` of a seamed path `γ₀`: the
connected covering space of `C` attached to the subgroup
`referenceCylinderCoverSubgroup γ₀ Iω Ic` of `π₁(C, γ₀)`. A point over `γ` is a homotopy class
of paths in `C` from `γ₀` to `γ`, a reference cylinder, modulo the loops of seamed paths on whose
swept-out torus both transgressions vanish. -/
abbrev ReferenceCylinderCover : Type :=
  SubgroupQuotient (pathComponentSelf γ₀) (referenceCylinderCoverSubgroup γ₀ Iω Ic)

variable (Iω Ic) in
/-- The projection of the reference-cylinder cover to the path component of `γ₀`. -/
abbrev referenceCylinderCoverProj : ReferenceCylinderCover γ₀ Iω Ic → pathComponent γ₀ :=
  subgroupQuotientProj (pathComponentSelf γ₀) (referenceCylinderCoverSubgroup γ₀ Iω Ic)

section Covering

variable [LocallyPathConnectedSpace (pathComponent γ₀)]
  [SemilocallySimplyConnectedSpace (pathComponent γ₀)]

/-- **The reference-cylinder cover is a covering space** of the path component of `γ₀`, when that
component is locally path-connected and semilocally simply connected, for instance when the space
of seamed paths is. -/
theorem isCoveringMap_referenceCylinderCoverProj :
    IsCoveringMap (referenceCylinderCoverProj γ₀ Iω Ic) :=
  isCoveringMap_subgroupQuotientProj _ _

/-- **A loop of seamed paths lifts to a loop of the reference-cylinder cover**, at its base point,
exactly when both transgressions vanish on the torus it sweeps out: the subgroup of `π₁(C, γ₀)`
recovered by the reference-cylinder cover is `TauCeti.Floer.referenceCylinderCoverSubgroup`. -/
theorem mem_range_mapOfEq_referenceCylinderCoverProj_iff
    (g : FundamentalGroup (pathComponent γ₀) (pathComponentSelf γ₀)) :
    g ∈ (FundamentalGroup.mapOfEq
        ⟨referenceCylinderCoverProj γ₀ Iω Ic, continuous_subgroupQuotientProj _ _⟩
        (subgroupQuotientProj_basepoint _ _)).range ↔
      Iω (SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 ∧
        Ic (SeamedPath.torusClassHom φ γ₀ (Additive.ofMul (HomotopyGroup.map
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent γ₀, SeamedPath φ)) rfl
            (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)))) = 0 := by
  rw [range_mapOfEq_subgroupQuotientProj, mem_referenceCylinderCoverSubgroup_iff,
    seamedPeriodHom_eq_zero_iff, toMul_ofMul]

/-- The reference-cylinder cover is a regular covering of the path component of `γ₀`. -/
theorem isRegular_referenceCylinderCoverProj :
    Deck.IsRegular (referenceCylinderCoverProj γ₀ Iω Ic) :=
  (isRegular_subgroupQuotientProj_iff_normal _ _).mpr inferInstance

variable (Iω Ic) in
/-- **The deck group of the reference-cylinder cover is the period group** `Γ`: the period
homomorphism maps `π₁(C, γ₀)` onto `Γ` with kernel `referenceCylinderCoverSubgroup γ₀ Iω Ic`, and
the deck group of the cover attached to the kernel of a surjective homomorphism is its
target. -/
def referenceCylinderCoverDeckEquiv :
    Multiplicative (seamedPeriodGroup γ₀ Iω Ic) ≃* deck (referenceCylinderCoverProj γ₀ Iω Ic) :=
  deckAdditiveKerEquiv _ (seamedPeriodClass γ₀ Iω Ic) (seamedPeriodClass_surjective γ₀)

/-- The deck transformation of the period class of a loop `a` of seamed paths acts on the
reference-cylinder cover through the action of `a` on the universal cover of the path component
of `γ₀`. -/
@[simp]
theorem referenceCylinderCoverDeckEquiv_seamedPeriodClass_apply_mk
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀)) :
    (referenceCylinderCoverDeckEquiv γ₀ Iω Ic (Multiplicative.ofAdd
        (seamedPeriodClass γ₀ Iω Ic (Additive.ofMul a)))).val
        (Quotient.mk'' e) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  deckAdditiveKerEquiv_apply_mk _ _ (seamedPeriodClass_surjective γ₀) a e

/-- The inverse of the deck transformation of the period class of a loop `a` of seamed paths acts
on the reference-cylinder cover through the action of `a⁻¹` on the universal cover of the path
component of `γ₀`. -/
@[simp]
theorem referenceCylinderCoverDeckEquiv_seamedPeriodClass_symm_apply_mk
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀)) :
    (referenceCylinderCoverDeckEquiv γ₀ Iω Ic (Multiplicative.ofAdd
        (seamedPeriodClass γ₀ Iω Ic (Additive.ofMul a)))).val.symm
        (Quotient.mk'' e) =
      Quotient.mk'' ((HomotopyGroup.pi1MulEquivFundamentalGroup a)⁻¹ • e) := by
  rw [Homeomorph.symm_apply_eq, referenceCylinderCoverDeckEquiv_seamedPeriodClass_apply_mk,
    smul_inv_smul]

/-- The period group acts on the reference-cylinder cover through its deck group. -/
noncomputable instance instAddActionReferenceCylinderCover :
    AddAction (seamedPeriodGroup γ₀ Iω Ic) (ReferenceCylinderCover γ₀ Iω Ic) :=
  Deck.addActionOfMulEquiv (referenceCylinderCoverDeckEquiv γ₀ Iω Ic)

namespace ReferenceCylinderCover

/-- The period group acts on the reference-cylinder cover by the deck transformations of
`referenceCylinderCoverDeckEquiv`. -/
theorem vadd_def (g : seamedPeriodGroup γ₀ Iω Ic) (e : ReferenceCylinderCover γ₀ Iω Ic) :
    g +ᵥ e = (referenceCylinderCoverDeckEquiv γ₀ Iω Ic (Multiplicative.ofAdd g)).val e :=
  Deck.addActionOfMulEquiv_vadd (referenceCylinderCoverDeckEquiv γ₀ Iω Ic) g e

end ReferenceCylinderCover

open ReferenceCylinderCover

/-- The action of the period group preserves the projection of the reference-cylinder cover. -/
@[simp]
theorem referenceCylinderCoverProj_vadd (g : seamedPeriodGroup γ₀ Iω Ic)
    (e : ReferenceCylinderCover γ₀ Iω Ic) :
    referenceCylinderCoverProj γ₀ Iω Ic (g +ᵥ e) = referenceCylinderCoverProj γ₀ Iω Ic e :=
  Deck.proj_addActionOfMulEquiv_vadd (referenceCylinderCoverDeckEquiv γ₀ Iω Ic) g e

/-- **Transporting a reference cylinder around a loop of seamed paths adds the period class of
the torus it sweeps out**: the period class of `a ∈ π₁(C, γ₀)` acts on the reference-cylinder cover
as `a` acts on the universal cover of `C`. -/
@[simp]
theorem seamedPeriodClass_vadd_mk
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀)) :
    seamedPeriodClass γ₀ Iω Ic (Additive.ofMul a) +ᵥ
        (Quotient.mk'' e : ReferenceCylinderCover γ₀ Iω Ic) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  deckAdditiveKerEquiv_vadd_mk _ _ (seamedPeriodClass_surjective γ₀) a e

/-- **Each fibre of the reference-cylinder cover is a torsor under the period group** `Γ`: the
deck group `Γ` of the regular cover acts simply transitively on every fibre. -/
noncomputable instance instAddTorsorReferenceCylinderCoverFiber (γ : pathComponent γ₀) :
    AddTorsor (seamedPeriodGroup γ₀ Iω Ic) (referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ}) :=
  Deck.fiberAddTorsorOfMulEquiv (isCoveringMap_referenceCylinderCoverProj γ₀)
    (isRegular_referenceCylinderCoverProj γ₀) (referenceCylinderCoverDeckEquiv γ₀ Iω Ic) γ

/-- The action of the period group on a fibre of the reference-cylinder cover is its action on
the cover. -/
@[simp]
theorem ReferenceCylinderCover.coe_vadd_fiber {γ : pathComponent γ₀}
    (g : seamedPeriodGroup γ₀ Iω Ic) (e : referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ}) :
    ((g +ᵥ e : referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ}) : ReferenceCylinderCover γ₀ Iω Ic) =
      g +ᵥ (e : ReferenceCylinderCover γ₀ Iω Ic) :=
  Deck.coe_fiberAddTorsorOfMulEquiv_vadd _ _ (referenceCylinderCoverDeckEquiv γ₀ Iω Ic) g e

/-- The difference of two points of a fibre of the reference-cylinder cover carries the second to
the first on the cover. -/
@[simp]
theorem ReferenceCylinderCover.vsub_vadd_coe {γ : pathComponent γ₀}
    (e₁ e₂ : referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ}) :
    (e₁ -ᵥ e₂) +ᵥ (e₂ : ReferenceCylinderCover γ₀ Iω Ic) = e₁ := by
  rw [← coe_vadd_fiber, vsub_vadd]

/-- **The difference of two points of a fibre of the reference-cylinder cover is the period class
of the loop relating them**: transporting `e` around a loop `a` of seamed paths gives the point
whose difference from `e` is the period class of `a`. -/
@[simp]
theorem ReferenceCylinderCover.vsub_mk {γ : pathComponent γ₀}
    (a : HomotopyGroup (Fin 1) (pathComponent γ₀) (pathComponentSelf γ₀))
    (e : UniversalCover (pathComponentSelf γ₀))
    (h₁ : (Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :
      ReferenceCylinderCover γ₀ Iω Ic) ∈ referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ})
    (h₂ : (Quotient.mk'' e : ReferenceCylinderCover γ₀ Iω Ic) ∈
      referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ}) :
    (⟨_, h₁⟩ : referenceCylinderCoverProj γ₀ Iω Ic ⁻¹' {γ}) -ᵥ ⟨_, h₂⟩ =
      seamedPeriodClass γ₀ Iω Ic (Additive.ofMul a) :=
  deckAdditiveKerEquiv_vsub_mk _ _ (seamedPeriodClass_surjective γ₀) a e h₁ h₂

end Covering

end TauCeti.Floer
