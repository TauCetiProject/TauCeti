/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Transfer
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction

/-!
# The ground-level and abelianized-Galois maps of a restriction

Let `T : LayerRestriction small big` be a restriction of finite normal layers, the layer `K/F`
restricted to `K/E` for an intermediate field `F ⊆ E ⊆ K`, with ground subgroups `U' ≤ U`. Beyond
the restriction `LayerRestriction.cohomologyRes` on cohomology, a restriction induces four more
maps that the Artin–Tate functoriality diagrams are stated against:

* on ground levels, the **norm** `A^{U'} → A^U` (`groundNorm`), the sum of the translates by
  representatives of the cosets `U/U'`, with `groundNorm ∘ groundInclusion = [U : U'] • id`
  (`groundNorm_groundInclusion`), building on the inclusion `groundInclusion` of #6221;
* on abelianized Galois groups, the group-theoretic **transfer** `(U/V)^ab → (U'/V)^ab`
  (`transferHom`) and the map induced by the inclusion `U' ≤ U` (`inclusionHom`).

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm`: the norm `A^{U'} → A^U` between
  the ground levels of a restriction, and its interaction with the inclusion.
* `TauCeti.ClassFieldTheory.LayerRestriction.transferHom`, `inclusionHom`: the transfer and the
  inclusion on abelianized Galois groups.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm_groundInclusion`: the norm of an element of
  the ground level `A^U` is its multiple by the relative degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. S. Milne, *Class Field Theory*, Chapter II, 1.29–1.30 (the norm along a subgroup).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (1.5.9) (the transfer).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRestriction

variable {small big : NormalLayer G}

section GroundLevels

/-- The cosets of one open subgroup of a compact group in another are finite. The norm along a
restriction sums over representatives of the cosets `U/U'`. -/
instance (U U' : OpenSubgroup G) :
    Finite (U ⧸ U'.toSubgroup.subgroupOf U.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen' _ _ U.isOpen (U.toSubgroup.subgroupOf_isOpen _ U'.isOpen)

/-- The sum of the translates of an element of `A^{U'}` by representatives of the cosets `U/U'` is
fixed by `U`: translating by `u ∈ U` permutes the cosets, and the ambiguity in the representatives
lies in `U'`, which fixes the element. -/
theorem finsum_ρ_out_mem_level (_T : LayerRestriction small big) (F : Formation G)
    (x : F.level small.ground) :
    ∑ᶠ q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
      F.toRep.ρ (q.out : G) x ∈ F.level big.ground := by
  rw [Formation.mem_level]
  intro u hu
  -- Translating by `u ∈ U` permutes the cosets `U/U'`, and `u` times a representative differs
  -- from the representative of the translated coset by an element of `U'`, which fixes `x`.
  have hperm : ∀ q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
      F.toRep.ρ u (F.toRep.ρ (q.out : G) x) =
        F.toRep.ρ ((((⟨u, hu⟩ : big.ground) • q).out : big.ground) : G) x := by
    intro q
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul
      (small.ground.toSubgroup.subgroupOf big.ground.toSubgroup) ((⟨u, hu⟩ : big.ground) * q.out)
    have hq : (⟨u, hu⟩ : big.ground) • q =
        QuotientGroup.mk ((⟨u, hu⟩ : big.ground) * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      exact MulAction.Quotient.smul_mk
        (H := small.ground.toSubgroup.subgroupOf big.ground.toSubgroup) _ _
    rw [hq, hh, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, F.mem_level.1 x.2 _ (Subgroup.mem_subgroupOf.1 h.2)]
  rw [map_finsum
    (f := fun q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup ↦
      F.toRep.ρ (q.out : G) x) (F.toRep.ρ u) (Set.toFinite _), finsum_congr hperm]
  exact finsum_comp_equiv (MulAction.toPerm (⟨u, hu⟩ : big.ground))
    (f := fun q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup ↦
      F.toRep.ρ (q.out : G) x)

/-- The **norm** `N_{U/U'} : A^{U'} → A^U` along a restriction `U' ≤ U` of ground subgroups: the
sum of the translates of an element of `A^{U'}` by representatives of the cosets `U/U'`. The
subgroup `U'` need not be normal in `U`, so this is not the norm of a layer; it is the map that
corestriction restricts to in degree zero. -/
def groundNorm (T : LayerRestriction small big) (F : Formation G) :
    F.level small.ground →+ F.level big.ground where
  toFun x :=
    ⟨∑ᶠ q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
      F.toRep.ρ (q.out : G) x, T.finsum_ρ_out_mem_level F x⟩
  map_zero' := Subtype.ext (by simp only [Submodule.coe_zero, map_zero, finsum_zero])
  map_add' x y := Subtype.ext <| by
    simp only [Submodule.coe_add, map_add]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

/-- The norm along a restriction is the sum of the translates by coset representatives, read in
the ambient module. -/
@[simp]
theorem groundNorm_apply_coe (T : LayerRestriction small big) (F : Formation G)
    (x : F.level small.ground) :
    ((T.groundNorm F x : F.level big.ground) : F.toRep.V) =
      ∑ᶠ q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
        F.toRep.ρ (q.out : G) x :=
  (rfl)

/-- **The norm of an element of the ground level `A^U` is its multiple by the relative degree:**
every translate of such an element is the element itself. -/
theorem groundNorm_groundInclusion (T : LayerRestriction small big) (F : Formation G)
    (x : F.level big.ground) :
    T.groundNorm F (T.groundInclusion F x) = T.relativeDegree • x := by
  have h : ∀ q : big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
      F.toRep.ρ (q.out : G) (T.groundInclusion F x : F.toRep.V) = x := fun q ↦ by
    rw [groundInclusion_apply_coe]
    exact F.mem_level.1 x.2 _ q.out.2
  let _ : Fintype (big.ground ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup) :=
    Fintype.ofFinite _
  refine Subtype.ext ?_
  rw [Submodule.coe_smul_of_tower, groundNorm_apply_coe, finsum_congr h,
    finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, relativeDegree_def,
    Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  rfl

end GroundLevels

/-! ### The abelianized Galois groups of a restriction -/

section Abelianization

/-- The group-theoretic **transfer** `(U/V)^ab → (U'/V)^ab` along a restriction, written
additively: Mathlib's `MonoidHom.transfer` for the finite-index subgroup `galHom.range ≅ U'/V` of
`U/V`, with values in the abelianization of `U'/V`. -/
def transferHom (T : LayerRestriction small big) :
    Additive (Abelianization big.Gal) →+ Additive (Abelianization small.Gal) :=
  MonoidHom.toAdditive <| Abelianization.lift <| MonoidHom.transfer <|
    Abelianization.of.comp (MonoidHom.ofInjective T.galHom_injective).symm.toMonoidHom

/-- The map `(U'/V)^ab → (U/V)^ab` of abelianized Galois groups induced by the inclusion
`U' ≤ U`, written additively. -/
def inclusionHom (T : LayerRestriction small big) :
    Additive (Abelianization small.Gal) →+ Additive (Abelianization big.Gal) :=
  MonoidHom.toAdditive (Abelianization.map T.galHom)

end Abelianization

end LayerRestriction

end TauCeti.ClassFieldTheory
