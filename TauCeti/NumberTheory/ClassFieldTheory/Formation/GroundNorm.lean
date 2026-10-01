/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Transitivity
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Norms between levels, and the ground-level norm of a restriction

Let `T : LayerRestriction small big` be a restriction of finite normal layers, the layer `K/F`
restricted to `K/E` for an intermediate field `F ⊆ E ⊆ K`, with ground subgroups `U' ≤ U`. On
ground levels a restriction has the inclusion `A^U ⊆ A^{U'}` (`LayerRestriction.groundInclusion`)
and, in the other direction, the **norm** `N_{U/U'} : A^{U'} → A^U`, the sum of the translates of
an element by representatives of the cosets `U/U'`. It is the map the Artin–Tate functoriality
diagram `artinMap_groundNorm` is stated against.

The norm is not a new construction. The level `A^W` of an open subgroup is the degree-zero
cohomology `H⁰(W, A)` of `W` acting on the coefficient module (`Formation.levelEquivH0`), and the
norm `Formation.levelNorm` between the levels of any open subgroups `W' ≤ W` is Tau Ceti's
relative degree-zero corestriction `ContCohomology.explicitCor0Le` along `W' ≤ W`, read on levels.
The ground-level norm of a restriction is its instance `W = U`, `W' = U'`.

## Main definitions

* `TauCeti.ClassFieldTheory.Formation.levelNorm`: the norm `A^{W'} → A^W` between the levels of
  open subgroups `W' ≤ W`.
* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm`: the norm `A^{U'} → A^U` between the
  ground levels of a restriction.

## Main statements

* `TauCeti.ClassFieldTheory.Formation.levelNorm_trans`: norms between levels compose along a
  tower of open subgroups.
* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm_apply_coe`: the norm is the sum of the
  translates by coset representatives.
* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm_groundInclusion`: the norm of an element of
  the ground level `A^U` is its multiple by the relative degree.
* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm_trans`: ground-level norms compose along a
  tower of restrictions.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. S. Milne, *Class Field Theory*, Chapter II, 1.29–1.30 (the norm along a subgroup).
-/

-- The signature of `groundNorm` follows the blueprint `Suggested.lean` of the Tau Ceti
-- `ClassFieldTheory` roadmap (`namespace LayerRestriction`).

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-! ### The norm between two levels -/

namespace Formation

variable (F : Formation G) {W W' : OpenSubgroup G}

/-- The **norm** `N_{W/W'} : A^{W'} → A^W` between the levels of open subgroups `W' ≤ W`: the
relative degree-zero corestriction `ContCohomology.explicitCor0Le` along `W' ≤ W`, read on levels
(`levelEquivH0_levelNorm`) and evaluated by `levelNorm_apply_coe`. The subgroup `W'` need not be
normal in `W`. -/
def levelNorm (h : W' ≤ W) : F.level W' →+ F.level W :=
  (F.levelEquivH0 W).symm.toAddMonoidHom.comp <|
    (ContCohomology.explicitCor0Le G F.toRep.V _ _ (OpenSubgroup.toSubgroup_le.2 h)).comp
      (F.levelEquivH0 W').toAddMonoidHom

/-- Read in degree-zero cohomology, the norm between two levels is the relative corestriction
`ContCohomology.explicitCor0Le`. -/
theorem levelEquivH0_levelNorm (h : W' ≤ W) (x : F.level W') :
    F.levelEquivH0 W (F.levelNorm h x) =
      ContCohomology.explicitCor0Le G F.toRep.V _ _ (OpenSubgroup.toSubgroup_le.2 h)
        (F.levelEquivH0 W' x) :=
  (F.levelEquivH0 W).apply_symm_apply _

-- The `simp` lemmas on the norm of an element state their left-hand sides through `dsimp% only`:
-- `toRep` is an `abbrev`, and `simp` reduces its carrier in implicit type arguments before it looks
-- a term up, so a left-hand side stated plainly over `F.toRep.V` or its levels is never found.
-- This follows #8315; see the implementation notes of `Formation/Basic.lean`.
/-- The norm between two levels is the sum of the translates by coset representatives, read in the
ambient module: `N_{W/W'} x = ∑ ρ(g) x` over the representatives `g = q.out` of the cosets
`q ∈ W/W'`. -/
@[simp]
theorem levelNorm_apply_coe (h : W' ≤ W) (x : F.level W') :
    (dsimp% only (F.levelNorm h x : F.toRep.V)) =
      ∑ᶠ q : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup, F.toRep.ρ (q.out : G) x := by
  rw [levelNorm, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Formation.levelEquivH0_symm_apply_coe, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ContCohomology.coe_explicitCor0Le, finsum_eq_sum_of_fintype, Formation.levelEquivH0_apply_coe]
  -- Termwise, the action of a coset representative of `W/W'` on the level is by definition the
  -- operator `ρ` of the formation at its underlying element of `G`.
  rfl

/-- The norm from a level to itself is the identity. -/
@[simp]
theorem levelNorm_self (h : W ≤ W) : F.levelNorm h = AddMonoidHom.id (F.level W) := by
  ext x
  rw [levelNorm_apply_coe, AddMonoidHom.id_apply]
  -- Every coset representative lies in `W`, so it fixes an element of the level `A^W`.
  simp [finsum_eq_sum_of_fintype, F.mem_level.1 x.2, ← Nat.card_eq_fintype_card]

/-- Norms between levels compose along a tower `W'' ≤ W' ≤ W` of open subgroups. -/
theorem levelNorm_trans {W'' : OpenSubgroup G} (h : W' ≤ W) (h' : W'' ≤ W') :
    F.levelNorm (h'.trans h) = (F.levelNorm h).comp (F.levelNorm h') := by
  ext x : 1
  apply (F.levelEquivH0 W).injective
  rw [levelEquivH0_levelNorm, AddMonoidHom.comp_apply, levelEquivH0_levelNorm,
    levelEquivH0_levelNorm, ContCohomology.explicitCor0Le_trans G F.toRep.V W'.toSubgroup
      W''.toSubgroup (OpenSubgroup.toSubgroup_le.2 h') W.toSubgroup
      (OpenSubgroup.toSubgroup_le.2 h), AddMonoidHom.comp_apply]

end Formation

/-! ### The norm between the ground levels of a restriction -/

namespace LayerRestriction

variable {small big : NormalLayer G}

/-- The **norm** `N_{U/U'} : A^{U'} → A^U` along a restriction `U' ≤ U` of ground subgroups: the
norm `Formation.levelNorm` between the two ground levels, evaluated by `groundNorm_apply_coe`. The
subgroup `U'` need not be normal in `U`, so this is not the norm of a layer. -/
def groundNorm (T : LayerRestriction small big) (F : Formation G) :
    F.level small.ground →+ F.level big.ground :=
  F.levelNorm T.ground_le

-- `dsimp% only` on the left-hand side, as explained above `Formation.levelNorm_apply_coe`.
/-- The norm along a restriction is the sum of the translates by coset representatives, read in the
ambient module: `N_{U/U'} x = ∑ ρ(g) x` over the representatives `g = q.out` of the cosets
`q ∈ U/U'`. -/
@[simp]
theorem groundNorm_apply_coe (T : LayerRestriction small big) (F : Formation G)
    (x : F.level small.ground) : (dsimp% only (T.groundNorm F x : F.toRep.V)) =
      ∑ᶠ q : big.ground.toSubgroup ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
        F.toRep.ρ (q.out : G) x :=
  F.levelNorm_apply_coe T.ground_le x

/-- **The norm of an element of the ground level `A^U` is its multiple by the relative degree.** -/
@[simp]
theorem groundNorm_groundInclusion (T : LayerRestriction small big) (F : Formation G)
    (x : F.level big.ground) :
    (dsimp% only (T.groundNorm F (T.groundInclusion F x))) = T.relativeDegree • x := by
  ext
  rw [groundNorm_apply_coe, groundInclusion_apply_coe]
  -- Every coset representative lies in `U`, so it fixes an element of the ground level `A^U`.
  simp [finsum_eq_sum_of_fintype, F.mem_level.1 x.2, Subgroup.relIndex, Subgroup.index_eq_card]

/-! ### Towers -/

/-- The norm along the trivial layer restriction is the identity. -/
@[simp]
theorem groundNorm_self {L : NormalLayer G} (T : LayerRestriction L L) (F : Formation G) :
    T.groundNorm F = AddMonoidHom.id (F.level L.ground) :=
  F.levelNorm_self T.ground_le

/-- Ground-level norms compose along a tower of layer restrictions. -/
theorem groundNorm_trans {a b c : NormalLayer G} (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (F : Formation G) :
    (T.trans T').groundNorm F = (T'.groundNorm F).comp (T.groundNorm F) :=
  F.levelNorm_trans T'.ground_le T.ground_le

end LayerRestriction

end TauCeti.ClassFieldTheory
