/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Bijection
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.DeckGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Torsor
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The cover attached to the kernel of an additive homomorphism on `π₁`

Let `f : π₁(X, x₀) → A` be a homomorphism to an additive group, written on
`Additive (HomotopyGroup (Fin 1) X x₀)`, as period homomorphisms usually are. Its kernel, read in
the fundamental group `FundamentalGroup X x₀` (`TauCeti.UniversalCover.additiveKerSubgroup`), is a
normal subgroup, and the attached cover `UniversalCover x₀ / ker f` is a regular cover of the path
component of `x₀`. When `f` is onto, its deck group is `A`
(`TauCeti.UniversalCover.deckAdditiveKerEquiv`): `f a` acts by transport around the loop `a`
(`TauCeti.UniversalCover.deckAdditiveKerEquiv_vadd_mk`), so every fibre is an `A`-torsor whose
differences are the values of `f` on the loops relating its points
(`TauCeti.UniversalCover.deckAdditiveKerEquiv_vsub_mk`).

This is `TauCeti.UniversalCover.deckSubgroupQuotientProjKerEquivOfSurjective` read additively,
with the action and the fibre torsors of `TauCeti.Deck.addActionOfMulEquiv` and
`TauCeti.Deck.fiberAddTorsorOfMulEquiv`. The covers of Floer theory attached to period
homomorphisms, such as the cap cover `TauCeti.Floer.CapCover` and the reference-cylinder cover
`TauCeti.Floer.ReferenceCylinderCover`, are instances.

## Main definitions

* `TauCeti.UniversalCover.fundamentalGroupHomOfAdditive x₀ f`: `f` read multiplicatively on the
  fundamental group.
* `TauCeti.UniversalCover.additiveKerSubgroup x₀ f`: the kernel of `f`, as a subgroup of
  `π₁(X, x₀)`.
* `TauCeti.UniversalCover.deckAdditiveKerEquiv x₀ f hf`: for onto `f`, the deck group of the
  attached cover is `A`.

## Main results

* `TauCeti.UniversalCover.deckAdditiveKerEquiv_vadd_mk`: `f a` acts on the cover as `a` acts on
  the universal cover.
* `TauCeti.UniversalCover.deckAdditiveKerEquiv_vsub_mk`: the difference of two points of a fibre
  is the value of `f` on the loop relating them.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.3, on the covering space attached to a subgroup of
  the fundamental group and its deck group.
-/

public section

noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] (x₀ : X) {A : Type*} [AddGroup A]
  (f : Additive (HomotopyGroup (Fin 1) X x₀) →+ A)

/-- **An additive homomorphism on `π₁` read on the fundamental group**: `f`, with values in `A`
read multiplicatively, through `π₁ ≅ FundamentalGroup`. -/
def fundamentalGroupHomOfAdditive : FundamentalGroup X x₀ →* Multiplicative A :=
  (AddMonoidHom.toMultiplicativeRight f).comp
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.toMonoidHom

theorem fundamentalGroupHomOfAdditive_apply (g : FundamentalGroup X x₀) :
    fundamentalGroupHomOfAdditive x₀ f g = Multiplicative.ofAdd
      (f (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g))) :=
  (rfl)

@[simp]
theorem fundamentalGroupHomOfAdditive_pi1MulEquivFundamentalGroup
    (a : HomotopyGroup (Fin 1) X x₀) :
    fundamentalGroupHomOfAdditive x₀ f (HomotopyGroup.pi1MulEquivFundamentalGroup a) =
      Multiplicative.ofAdd (f (Additive.ofMul a)) := by
  simp [fundamentalGroupHomOfAdditive]

/-- An onto additive homomorphism on `π₁` is onto when read on the fundamental group. -/
theorem fundamentalGroupHomOfAdditive_surjective (hf : Function.Surjective f) :
    Function.Surjective (fundamentalGroupHomOfAdditive x₀ f) :=
  hf.comp HomotopyGroup.pi1MulEquivFundamentalGroup.symm.surjective

/-- **The kernel of an additive homomorphism on `π₁`, read in the fundamental group**: the classes
of `FundamentalGroup X x₀` of the loops `a` with `f a = 0`. -/
def additiveKerSubgroup : Subgroup (FundamentalGroup X x₀) :=
  (fundamentalGroupHomOfAdditive x₀ f).ker

/-- A class of the fundamental group lies in the kernel of `f` exactly when `f` vanishes on the
corresponding element of `π₁`. -/
theorem mem_additiveKerSubgroup_iff (g : FundamentalGroup X x₀) :
    g ∈ additiveKerSubgroup x₀ f ↔
      f (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup.symm g)) = 0 := by
  rw [additiveKerSubgroup, MonoidHom.mem_ker, fundamentalGroupHomOfAdditive_apply, ofAdd_eq_one]

/-- The kernel of an additive homomorphism on `π₁` is a normal subgroup. -/
instance additiveKerSubgroup_normal : (additiveKerSubgroup x₀ f).Normal :=
  MonoidHom.normal_ker _

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- **The deck group of the cover attached to the kernel of an onto additive homomorphism
`f : π₁(X, x₀) → A` is `A`**: the deck transformation labelled by `f a` is that of the class of
`a`. -/
def deckAdditiveKerEquiv (hf : Function.Surjective f) :
    Multiplicative A ≃* deck (subgroupQuotientProj x₀ (additiveKerSubgroup x₀ f)) :=
  (deckSubgroupQuotientProjKerEquivOfSurjective x₀ (fundamentalGroupHomOfAdditive x₀ f)
    (fundamentalGroupHomOfAdditive_surjective x₀ f hf)).symm

/-- The deck transformation labelled by the value of `f` on a class `g` of the fundamental group
acts on the cover attached to the kernel of `f` through the action of `g` on the universal
cover. -/
@[simp]
theorem deckAdditiveKerEquiv_fundamentalGroupHomOfAdditive_apply_mk (hf : Function.Surjective f)
    (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    (deckAdditiveKerEquiv x₀ f hf (fundamentalGroupHomOfAdditive x₀ f g)).val (Quotient.mk'' e) =
      Quotient.mk'' (g • e) :=
  -- the cover is attached to `additiveKerSubgroup x₀ f`, which is by definition the kernel of
  -- `fundamentalGroupHomOfAdditive x₀ f`
  deckSubgroupQuotientProjKerEquivOfSurjective_symm_apply_mk _ _ _ g e

/-- The inverse of the deck transformation labelled by the value of `f` on a class `g` of the
fundamental group acts on the cover attached to the kernel of `f` through the action of `g⁻¹` on
the universal cover. -/
@[simp]
theorem deckAdditiveKerEquiv_fundamentalGroupHomOfAdditive_symm_apply_mk
    (hf : Function.Surjective f) (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    (deckAdditiveKerEquiv x₀ f hf (fundamentalGroupHomOfAdditive x₀ f g)).val.symm
        (Quotient.mk'' e) =
      Quotient.mk'' (g⁻¹ • e) := by
  rw [Homeomorph.symm_apply_eq, deckAdditiveKerEquiv_fundamentalGroupHomOfAdditive_apply_mk,
    smul_inv_smul]

/-- The deck transformation labelled by `f a` acts on the cover attached to the kernel of `f`
through the action of `a` on the universal cover. -/
@[simp]
theorem deckAdditiveKerEquiv_apply_mk (hf : Function.Surjective f)
    (a : HomotopyGroup (Fin 1) X x₀) (e : UniversalCover x₀) :
    (deckAdditiveKerEquiv x₀ f hf (Multiplicative.ofAdd (f (Additive.ofMul a)))).val
        (Quotient.mk'' e) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) := by
  rw [← fundamentalGroupHomOfAdditive_pi1MulEquivFundamentalGroup]
  exact deckAdditiveKerEquiv_fundamentalGroupHomOfAdditive_apply_mk x₀ f hf _ e

/-- **`f a` acts on the cover attached to the kernel of `f` as `a` acts on the universal
cover**, for the action of `A` through the deck group. -/
theorem deckAdditiveKerEquiv_vadd_mk (hf : Function.Surjective f)
    (a : HomotopyGroup (Fin 1) X x₀) (e : UniversalCover x₀) :
    letI := Deck.addActionOfMulEquiv (deckAdditiveKerEquiv x₀ f hf)
    f (Additive.ofMul a) +ᵥ (Quotient.mk'' e : SubgroupQuotient x₀ (additiveKerSubgroup x₀ f)) =
      Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :=
  (Deck.addActionOfMulEquiv_vadd _ _ _).trans (deckAdditiveKerEquiv_apply_mk x₀ f hf a e)

/-- **The difference of two points of a fibre of the cover attached to the kernel of `f` is the
value of `f` on the loop relating them**, for the torsor structure of the fibre under the deck
group `A`. -/
theorem deckAdditiveKerEquiv_vsub_mk (hf : Function.Surjective f) {x : X}
    (a : HomotopyGroup (Fin 1) X x₀) (e : UniversalCover x₀)
    (h₁ : (Quotient.mk'' (HomotopyGroup.pi1MulEquivFundamentalGroup a • e) :
      SubgroupQuotient x₀ (additiveKerSubgroup x₀ f)) ∈
        subgroupQuotientProj x₀ (additiveKerSubgroup x₀ f) ⁻¹' {x})
    (h₂ : (Quotient.mk'' e : SubgroupQuotient x₀ (additiveKerSubgroup x₀ f)) ∈
      subgroupQuotientProj x₀ (additiveKerSubgroup x₀ f) ⁻¹' {x}) :
    letI := Deck.fiberAddTorsorOfMulEquiv (isCoveringMap_subgroupQuotientProj x₀ _)
      ((isRegular_subgroupQuotientProj_iff_normal _ _).mpr inferInstance)
      (deckAdditiveKerEquiv x₀ f hf) x
    (⟨_, h₁⟩ : subgroupQuotientProj x₀ (additiveKerSubgroup x₀ f) ⁻¹' {x}) -ᵥ ⟨_, h₂⟩ =
      f (Additive.ofMul a) := by
  let := Deck.fiberAddTorsorOfMulEquiv (isCoveringMap_subgroupQuotientProj x₀ _)
    ((isRegular_subgroupQuotientProj_iff_normal _ _).mpr inferInstance)
    (deckAdditiveKerEquiv x₀ f hf) x
  rw [← eq_vadd_iff_vsub_eq]
  exact Subtype.ext ((deckAdditiveKerEquiv_vadd_mk x₀ f hf a e).symm.trans
    (Deck.coe_fiberAddTorsorOfMulEquiv_vadd _ _ (deckAdditiveKerEquiv x₀ f hf)
      (f (Additive.ofMul a)) ⟨_, h₂⟩).symm)

end TauCeti.UniversalCover
