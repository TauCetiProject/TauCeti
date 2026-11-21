/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Subquotients along homomorphisms, subgroup inclusions, and boundary cases

This file develops canonical multiplicative and additive isomorphisms for group subquotients of
the form `H ⧸ K.subgroupOf H`:

* **Pullback along a surjective homomorphism**: for `f : G →* Q` surjective and `K, H ≤ Q` with
  `K.subgroupOf H` normal, `MonoidHom.comapSubquotientEquivOfSurjective` identifies
  `(H.comap f) ⧸ (K.comap f).subgroupOf (H.comap f)` with `H ⧸ K.subgroupOf H`.
* **Pushforward along a subgroup inclusion**: for `K, H ≤ M ≤ G` with `K.subgroupOf H` normal,
  `Subgroup.mapSubtypeSubquotientEquiv` identifies `H ⧸ K.subgroupOf H` with
  `(H.map M.subtype) ⧸ (K.map M.subtype).subgroupOf (H.map M.subtype)`.
* **Boundary case `H = ⊤, K = ⊥`**: `Subgroup.subquotientEquivOfEqTopOfEqBot` identifies
  `H ⧸ K.subgroupOf H` with `G`.

## Main definitions

* `MonoidHom.comapSubquotientEquivOfSurjective`: subquotient isomorphism for preimages under a
  surjective homomorphism.
* `Subgroup.mapSubtypeSubquotientEquiv`: subquotient isomorphism for images under a subgroup
  inclusion.
* `Subgroup.subquotientEquivOfEqTopOfEqBot`: subquotient isomorphism when `H = ⊤` and `K = ⊥`.
-/

public section

namespace Subgroup

variable {G Q : Type*} [Group G] [Group Q]

/-- Pulling back two subgroups along `f : G →* Q` and restricting one to the other agrees with
pulling back `K.subgroupOf H` along `f.subgroupComap H`. -/
@[to_additive /-- Pulling back two additive subgroups along `f : G →+ Q` and restricting one to
the other agrees with pulling back `K.addSubgroupOf H` along `f.addSubgroupComap H`. -/]
theorem comap_subgroupOf (f : G →* Q) (K H : Subgroup Q) :
    (K.comap f).subgroupOf (H.comap f) = (K.subgroupOf H).comap (f.subgroupComap H) :=
  rfl

/-- Normality of `K.subgroupOf H` pulls back along any group homomorphism `f : G →* Q`. -/
@[to_additive /-- Normality of `K.addSubgroupOf H` pulls back along any additive group
homomorphism `f : G →+ Q`. -/]
instance normal_comap_subgroupOf (f : G →* Q) (K H : Subgroup Q)
    [hN : (K.subgroupOf H).Normal] :
    ((K.comap f).subgroupOf (H.comap f)).Normal := by
  rw [comap_subgroupOf]; exact hN.comap _

/-- The kernel of `x ↦ f x mod (K.subgroupOf H)` on `H.comap f` is
`(K.comap f).subgroupOf (H.comap f)`. -/
@[to_additive /-- The kernel of `x ↦ f x mod (K.addSubgroupOf H)` on `H.comap f` is
`(K.comap f).addSubgroupOf (H.comap f)`. -/]
theorem _root_.MonoidHom.ker_mk'_comp_subgroupComap (f : G →* Q) (K H : Subgroup Q)
    [(K.subgroupOf H).Normal] :
    ((QuotientGroup.mk' (K.subgroupOf H)).comp (f.subgroupComap H)).ker =
      (K.comap f).subgroupOf (H.comap f) := by
  ext x; exact QuotientGroup.eq_one_iff _

/-- **A surjective group homomorphism identifies subquotients.** Given `f : G →* Q` surjective and
subgroups `K, H` of `Q` with `K.subgroupOf H` normal, the subquotient of their preimages is
canonically isomorphic to `H ⧸ K.subgroupOf H`. -/
@[to_additive /-- **A surjective additive group homomorphism identifies subquotients.** -/]
noncomputable def _root_.MonoidHom.comapSubquotientEquivOfSurjective (f : G →* Q)
    (hf : Function.Surjective f) (K H : Subgroup Q) [(K.subgroupOf H).Normal] :
    ((H.comap f) ⧸ (K.comap f).subgroupOf (H.comap f)) ≃* (H ⧸ K.subgroupOf H) :=
  (QuotientGroup.quotientMulEquivOfEq (f.ker_mk'_comp_subgroupComap K H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp (f.subgroupComap_surjective H hf)))

/-- Evaluation of `MonoidHom.comapSubquotientEquivOfSurjective` on coset representatives. -/
@[to_additive (attr := simp) /-- Evaluation of
`AddMonoidHom.comapSubquotientEquivOfSurjective` on coset representatives. -/]
theorem _root_.MonoidHom.comapSubquotientEquivOfSurjective_mk (f : G →* Q)
    (hf : Function.Surjective f) (K H : Subgroup Q) [(K.subgroupOf H).Normal]
    (x : H.comap f) :
    f.comapSubquotientEquivOfSurjective hf K H (QuotientGroup.mk x) =
      QuotientGroup.mk (f.subgroupComap H x) := by
  rw [MonoidHom.comapSubquotientEquivOfSurjective]; rfl

/-- Mapping two subgroups of `M ≤ G` into `G` via `M.subtype` preserves normality of their
relative subgroup. -/
@[to_additive /-- Mapping two additive subgroups of `M ≤ G` into `G` via `M.subtype` preserves
normality of their relative additive subgroup. -/]
instance normal_map_subtype_subgroupOf {M : Subgroup G} (K H : Subgroup M)
    [hN : (K.subgroupOf H).Normal] :
    ((K.map M.subtype).subgroupOf (H.map M.subtype)).Normal := by
  let e := H.equivMapOfInjective M.subtype M.subtype_injective
  have heq : (K.map M.subtype).subgroupOf (H.map M.subtype) =
      (K.subgroupOf H).map e.toMonoidHom := by
    ext ⟨_, ⟨x, hxH, rfl⟩⟩
    exact ⟨fun ⟨y, hyK, hyx⟩ ↦ ⟨⟨y, M.subtype_injective hyx ▸ hxH⟩, hyK, Subtype.ext hyx⟩,
      fun ⟨⟨y, _⟩, hyK, hyx⟩ ↦ ⟨y, hyK, congrArg (Subtype.val : H.map M.subtype → G) hyx⟩⟩
  exact heq ▸ hN.map e.toMonoidHom e.surjective

/-- Mapping subgroups `K, H ≤ M` to `G` along `M.subtype` identifies their subquotient in `G` with
`H ⧸ K.subgroupOf H`. -/
@[to_additive /-- Mapping additive subgroups `K, H ≤ M` to `G` along `M.subtype` identifies their
subquotient in `G` with `H ⧸ K.addSubgroupOf H`. -/]
noncomputable def mapSubtypeSubquotientEquiv {M : Subgroup G} (K H : Subgroup M)
    [(K.subgroupOf H).Normal] :
    (H ⧸ K.subgroupOf H) ≃*
      ((H.map M.subtype) ⧸ (K.map M.subtype).subgroupOf (H.map M.subtype)) :=
  let e := H.equivMapOfInjective M.subtype M.subtype_injective
  let φ := (QuotientGroup.mk' ((K.map M.subtype).subgroupOf (H.map M.subtype))).comp e.toMonoidHom
  have hker : φ.ker = K.subgroupOf H := by
    ext x
    simp only [φ, e, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_map]
    exact ⟨fun ⟨y, hyK, hyx⟩ ↦ M.subtype_injective hyx ▸ hyK, fun hxK ↦ ⟨x.val, hxK, rfl⟩⟩
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ
      ((QuotientGroup.mk'_surjective _).comp e.surjective))

/-- Evaluation of `Subgroup.mapSubtypeSubquotientEquiv` on coset representatives. -/
@[to_additive (attr := simp) /-- Evaluation of `AddSubgroup.mapSubtypeSubquotientEquiv` on coset
representatives. -/]
theorem mapSubtypeSubquotientEquiv_mk {M : Subgroup G} (K H : Subgroup M)
    [(K.subgroupOf H).Normal] (x : H) :
    mapSubtypeSubquotientEquiv K H (QuotientGroup.mk x) =
      QuotientGroup.mk (H.equivMapOfInjective M.subtype M.subtype_injective x) := by
  rw [mapSubtypeSubquotientEquiv]; rfl

/-- For `H = ⊤` and `K = ⊥`, the subquotient `H ⧸ K.subgroupOf H` is canonically isomorphic to
`G`. -/
@[to_additive /-- For `H = ⊤` and `K = ⊥`, the additive subquotient `H ⧸ K.addSubgroupOf H` is
canonically isomorphic to `G`. -/]
noncomputable def subquotientEquivOfEqTopOfEqBot {H K : Subgroup G} [(K.subgroupOf H).Normal]
    (hH : H = ⊤) (hK : K = ⊥) : (H ⧸ K.subgroupOf H) ≃* G :=
  have hker : H.subtype.ker = K.subgroupOf H := by ext x; simp [hK]
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective H.subtype fun g ↦ ⟨⟨g, hH.symm ▸ mem_top g⟩, rfl⟩)

/-- Evaluation of `Subgroup.subquotientEquivOfEqTopOfEqBot` on coset representatives. -/
@[to_additive (attr := simp) /-- Evaluation of `AddSubgroup.subquotientEquivOfEqTopOfEqBot` on
coset representatives. -/]
theorem subquotientEquivOfEqTopOfEqBot_mk {H K : Subgroup G} [(K.subgroupOf H).Normal]
    (hH : H = ⊤) (hK : K = ⊥) (x : H) :
    subquotientEquivOfEqTopOfEqBot hH hK (QuotientGroup.mk x) = (x : G) := by
  rw [subquotientEquivOfEqTopOfEqBot]; rfl

end Subgroup
