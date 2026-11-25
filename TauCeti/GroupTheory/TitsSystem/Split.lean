/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.NormalClosure

/-!
# Split Tits systems

A **split Tits system** on a group `G` is a Tits system `(B, N)` on `G` together with a solvable
normal subgroup `U` of `B` complemented by `B ∩ N`:

```text
U ≤ B,   U ⊴ B,   U solvable,   B = U (B ∩ N),   U ∩ (B ∩ N) = 1.
```

This is the split BN-pair of the literature. For `SL_n` over a field, `B` is the upper triangular
subgroup, `N` the monomial subgroup and `U` the upper unitriangular subgroup; for the finite
groups of Lie type, `U` is the product of the positive root subgroups and `B ∩ N` is the
maximal torus.

The structure supplies the hypotheses on `U` of Tits's simplicity criterion
`TauCeti.TitsSystem.isSimpleGroup_derivedCentralQuotient` other than `Z ∩ U = 1` (solvability,
`B ≤ N_G(U)` and `B ≤ U (B ∩ N)`), so that a group of Lie type built with a split Tits system
only has to supply the remaining group-theoretic inputs: an irreducible Weyl group, `Z ∩ U = 1`
for `Z = ⋂_{g : G} g B g⁻¹`, the equality of the normal closure of `U` with `[G, G]`, and
perfectness of `[G, G]`. Under these hypotheses the centre of `[G, G]` is `Z ∩ [G, G]`, and the
derived central quotient `[G, G] / Z([G, G])` is simple as soon as `U ≠ 1`.

Split Tits systems pull back along multiplicative equivalences, with the same Weyl group and
simple reflections. Together with `TauCeti.DerivedCentralQuotient.congr` and
`MulEquiv.isSimpleGroup_congr`, this lets a split Tits system built on a concrete model of a group
prove simplicity for every group isomorphic to it.

## Main definitions

* `TauCeti.SplitTitsSystem`: a Tits system with a solvable normal complement `U` to `B ∩ N` in
  `B`.
* `TauCeti.SplitTitsSystem.comap`: the pullback of a split Tits system along a multiplicative
  equivalence.

## Main results

* `TauCeti.SplitTitsSystem.subgroupB_le_normalizer`, `TauCeti.SplitTitsSystem.subgroupB_le_sup`:
  the hypotheses on `U` of Tits's simplicity criterion.
* `TauCeti.SplitTitsSystem.isIrreducible_comap_iff`: the pullback is irreducible exactly when the
  original split Tits system is.
* `TauCeti.SplitTitsSystem.center_commutator_eq_normalCore_subgroupOf`: the centre of `[G, G]` is
  `Z ∩ [G, G]`.
* `TauCeti.SplitTitsSystem.isSimpleGroup_derivedCentralQuotient`: the derived central quotient is
  simple.

## References

* B. Conrad, handout on Tits systems for Math 249B (Stanford, Winter 2016), the definition of a
  split BN-pair and Theorem 2.4.
* R. W. Carter, *Simple Groups of Lie Type* (1972), Chapters 8 and 11.
-/

public section

namespace TauCeti

universe u v

/-- A **split Tits system** on `G`: a Tits system `(B, N)` together with a solvable subgroup `U`
of `B`, normal in `B`, of which `B ∩ N` is a complement in `B`. -/
@[ext]
structure SplitTitsSystem (G : Type u) [Group G] extends TitsSystem G where
  /-- The subgroup conventionally denoted `U`, the unipotent radical of `B`. -/
  subgroupU : Subgroup G
  /-- The subgroup `U` lies in `B`. -/
  subgroupU_le_subgroupB : subgroupU ≤ subgroupB
  /-- The subgroup `U` is normal in `B`. -/
  normal_subgroupU_subgroupOf : (subgroupU.subgroupOf subgroupB).Normal
  /-- The subgroup `U` is solvable. -/
  isSolvable_subgroupU : Group.IsSolvable subgroupU
  /-- The subgroups `U` and `B ∩ N` generate `B`. -/
  subgroupU_sup_eq : subgroupU ⊔ subgroupB ⊓ subgroupN = subgroupB
  /-- The subgroups `U` and `B ∩ N` meet trivially. -/
  subgroupU_inf_eq_bot : subgroupU ⊓ (subgroupB ⊓ subgroupN) = ⊥

namespace SplitTitsSystem

variable {G : Type u} [Group G] (S : SplitTitsSystem G)

instance : Group.IsSolvable S.subgroupU :=
  S.isSolvable_subgroupU

instance : (S.subgroupU.subgroupOf S.subgroupB).Normal :=
  S.normal_subgroupU_subgroupOf

/-- The subgroup `B` normalizes `U`. -/
theorem subgroupB_le_normalizer : S.subgroupB ≤ Subgroup.normalizer (S.subgroupU : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf S.subgroupU_le_subgroupB

/-- The subgroup `B` lies in the product of `U` and `B ∩ N`. -/
theorem subgroupB_le_sup : S.subgroupB ≤ S.subgroupU ⊔ S.subgroupB ⊓ S.subgroupN :=
  S.subgroupU_sup_eq.ge

/-! ### Transport along multiplicative equivalences -/

variable {G' : Type v} [Group G'] (e : G' ≃* G)

/-- The **pullback of a split Tits system** along a multiplicative equivalence `e : G' ≃* G`: the
preimages of `B`, `N` and `U`, with the simple reflections of `TauCeti.TitsSystem.comap`. -/
def comap : SplitTitsSystem G' where
  toTitsSystem :=
    S.toTitsSystem.comap e.toMonoidHom (S.exists_mul_eq_of_surjective e.surjective)
  subgroupU := S.subgroupU.comap e.toMonoidHom
  subgroupU_le_subgroupB := by
    rw [TitsSystem.comap_subgroupB]
    exact Subgroup.comap_mono S.subgroupU_le_subgroupB
  normal_subgroupU_subgroupOf := by
    rw [TitsSystem.comap_subgroupB,
      Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.comap_mono S.subgroupU_le_subgroupB),
      ← Subgroup.comap_normalizer_eq_of_surjective _ e.surjective]
    exact Subgroup.comap_mono S.subgroupB_le_normalizer
  isSolvable_subgroupU :=
    Group.isSolvable_of_isSolvable_injective (e.toMonoidHom.subgroupComap_injective _ e.injective)
  subgroupU_sup_eq := by
    rw [TitsSystem.comap_subgroupB, TitsSystem.comap_subgroupN, ← Subgroup.comap_inf,
      Subgroup.comap_sup_eq e.toMonoidHom _ _ e.surjective, S.subgroupU_sup_eq]
  subgroupU_inf_eq_bot := by
    rw [TitsSystem.comap_subgroupB, TitsSystem.comap_subgroupN, ← Subgroup.comap_inf,
      ← Subgroup.comap_inf, S.subgroupU_inf_eq_bot, MonoidHom.comap_bot,
      MonoidHom.ker_eq_bot_iff]
    exact e.injective

/-- The underlying Tits system of the pullback is the pullback of the underlying Tits system. -/
@[simp]
theorem comap_toTitsSystem :
    (S.comap e).toTitsSystem =
      S.toTitsSystem.comap e.toMonoidHom (S.exists_mul_eq_of_surjective e.surjective) :=
  (rfl)

/-- The `B` subgroup of the pullback is the preimage of `B`. -/
theorem comap_subgroupB : (S.comap e).subgroupB = S.subgroupB.comap e.toMonoidHom :=
  TitsSystem.comap_subgroupB _ _ _

/-- The `N` subgroup of the pullback is the preimage of `N`. -/
theorem comap_subgroupN : (S.comap e).subgroupN = S.subgroupN.comap e.toMonoidHom :=
  TitsSystem.comap_subgroupN _ _ _

/-- The `U` subgroup of the pullback is the preimage of `U`. -/
@[simp]
theorem comap_subgroupU : (S.comap e).subgroupU = S.subgroupU.comap e.toMonoidHom :=
  (rfl)

/-- **The pullback of a split Tits system is irreducible exactly when the original one is**: the
Weyl groups are identified, with their simple reflections, by
`TauCeti.TitsSystem.comapWeylGroupMulEquiv`. -/
theorem isIrreducible_comap_iff :
    (S.comap e).IsIrreducible ↔ S.IsIrreducible :=
  S.toTitsSystem.isIrreducible_comap_iff e.toMonoidHom _

/-! ### Simplicity -/

variable {S}

/-- **The centre of the derived subgroup.** For a split Tits system with irreducible Weyl group
such that `U` meets `Z = ⋂_{g : G} g B g⁻¹` trivially and its normal closure is a perfect derived
subgroup `[G, G]`, the centre of `[G, G]` is `Z ∩ [G, G]`. -/
theorem center_commutator_eq_normalCore_subgroupOf (hirr : S.IsIrreducible)
    (hZU : S.subgroupB.normalCore ⊓ S.subgroupU = ⊥)
    (hU : Subgroup.normalClosure (S.subgroupU : Set G) = commutator G)
    [Group.IsPerfect (commutator G)] :
    Subgroup.center (commutator G) = S.subgroupB.normalCore.subgroupOf (commutator G) := by
  -- Replace `[G, G]` by the normal closure of `U`, where the criterion applies.
  suffices key : ∀ P : Subgroup G, Subgroup.normalClosure (S.subgroupU : Set G) = P →
      ∀ [Group.IsPerfect P], Subgroup.center P = S.subgroupB.normalCore.subgroupOf P from
    key _ hU
  rintro P rfl _
  exact S.center_normalClosure_eq_normalCore_subgroupOf hirr S.subgroupB_le_normalizer
    S.subgroupB_le_sup hZU

/-- **Simplicity of the derived central quotient from a split Tits system.** Suppose the Weyl
group is irreducible, `U ≠ 1` meets `Z = ⋂_{g : G} g B g⁻¹` trivially, the normal closure of `U`
is the derived subgroup `[G, G]`, and `[G, G]` is perfect. Then the derived central quotient
`[G, G] / Z([G, G])` is simple. -/
theorem isSimpleGroup_derivedCentralQuotient (hirr : S.IsIrreducible)
    (hZU : S.subgroupB.normalCore ⊓ S.subgroupU = ⊥)
    (hU : Subgroup.normalClosure (S.subgroupU : Set G) = commutator G)
    [Group.IsPerfect (commutator G)] (hU₁ : S.subgroupU ≠ ⊥) :
    IsSimpleGroup (DerivedCentralQuotient G) := by
  -- `[G, G]` contains `U ≠ 1`, so it is nontrivial, and a nontrivial perfect group is not
  -- central.
  have : Nontrivial (commutator G) := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (ne_bot_of_le_ne_bot hU₁ (hU ▸ Subgroup.le_normalClosure))
  exact S.toTitsSystem.isSimpleGroup_derivedCentralQuotient hirr S.subgroupB_le_normalizer
    S.subgroupB_le_sup hZU hU

end SplitTitsSystem

end TauCeti

end
