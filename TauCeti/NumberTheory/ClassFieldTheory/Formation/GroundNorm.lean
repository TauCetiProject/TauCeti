/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Transitivity

/-!
# The norm between the ground levels of a restriction

Let `T : LayerRestriction small big` be a restriction of finite normal layers, the layer `K/F`
restricted to `K/E` for an intermediate field `F ⊆ E ⊆ K`, with ground subgroups `U' ≤ U`. On
ground levels a restriction has the inclusion `A^U ⊆ A^{U'}` (`LayerRestriction.groundInclusion`)
and, in the other direction, the **norm** `N_{U/U'} : A^{U'} → A^U`, the sum of the translates of
an element by representatives of the cosets `U/U'`. It is the map the Artin–Tate functoriality
diagram `artinMap_groundNorm` is stated against.

The norm is not a new construction. The level `A^U` of an open subgroup is the degree-zero
cohomology `H⁰(U, A)` of `U` acting on the coefficient module (`Formation.levelEquivH0`), and the
norm is Tau Ceti's relative degree-zero corestriction `ContCohomology.explicitCor0Le` along
`U' ≤ U`, read on levels.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction.groundNorm`: the norm `A^{U'} → A^U` between the
  ground levels of a restriction.

## Main statements

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

namespace LayerRestriction

variable {small big : NormalLayer G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- An open subgroup of the compact group `G` has finite index. -/
local instance (U : OpenSubgroup G) : U.toSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

/-- The **norm** `N_{U/U'} : A^{U'} → A^U` along a restriction `U' ≤ U` of ground subgroups: the
relative degree-zero corestriction `ContCohomology.explicitCor0Le`, read on levels and evaluated by
`groundNorm_apply_coe`. The subgroup `U'` need not be normal in `U`, so this is not the norm of a
layer. -/
def groundNorm (T : LayerRestriction small big) (F : Formation G) :
    F.level small.ground →+ F.level big.ground :=
  (F.levelEquivH0 big.ground).symm.toAddMonoidHom.comp <|
    (ContCohomology.explicitCor0Le G F.toRep.V _ _ T.ground_toSubgroup_le).comp
      (F.levelEquivH0 small.ground).toAddMonoidHom

/-- The norm along a restriction is the sum of the translates by coset representatives, read in the
ambient module: `N_{U/U'} x = ∑ ρ(g) x` over the representatives `g = q.out` of the cosets
`q ∈ U/U'`. -/
@[simp]
theorem groundNorm_apply_coe (T : LayerRestriction small big) (F : Formation G)
    (x : F.level small.ground) : (T.groundNorm F x : F.toRep.V) =
      ∑ᶠ q : big.ground.toSubgroup ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup,
        F.toRep.ρ (q.out : G) x := by
  rw [groundNorm, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Formation.levelEquivH0_symm_apply_coe, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ContCohomology.coe_explicitCor0Le, finsum_eq_sum_of_fintype, Formation.levelEquivH0_apply_coe]
  -- Termwise, the action of a coset representative of `U/U'` on the level is by definition the
  -- operator `ρ` of the formation at its underlying element of `G`.
  rfl

/-- **The norm of an element of the ground level `A^U` is its multiple by the relative degree.** -/
@[simp]
theorem groundNorm_groundInclusion (T : LayerRestriction small big) (F : Formation G)
    (x : F.level big.ground) : T.groundNorm F (T.groundInclusion F x) = T.relativeDegree • x := by
  ext
  rw [groundNorm_apply_coe, groundInclusion_apply_coe]
  -- Every coset representative lies in `U`, so it fixes an element of the ground level `A^U`.
  simp [finsum_eq_sum_of_fintype, F.mem_level.1 x.2, Subgroup.relIndex, Subgroup.index_eq_card]

/-! ### Towers -/

/-- The norm along the trivial layer restriction is the identity. -/
@[simp]
theorem groundNorm_self {L : NormalLayer G} (T : LayerRestriction L L) (F : Formation G) :
    T.groundNorm F = AddMonoidHom.id (F.level L.ground) := by
  ext x
  simpa [relativeDegree_def] using congrArg Subtype.val (T.groundNorm_groundInclusion F x)

/-- Ground-level norms compose along a tower of layer restrictions. -/
theorem groundNorm_trans {a b c : NormalLayer G} (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (F : Formation G) :
    (T.trans T').groundNorm F = (T'.groundNorm F).comp (T.groundNorm F) := by
  ext x
  rw [groundNorm_apply_coe, AddMonoidHom.comp_apply, groundNorm_apply_coe,
    groundNorm_apply_coe]
  let m : ContCohomology.H0 a.ground.toSubgroup F.toRep.V :=
    ⟨x, (FixedPoints.mem_addSubgroup a.ground.toSubgroup F.toRep.V x).2 fun u ↦
      F.mem_level.1 x.2 u u.2⟩
  have h := congrArg (fun f ↦ f m)
    (ContCohomology.explicitCor0Le_trans G F.toRep.V b.ground.toSubgroup
      a.ground.toSubgroup T.ground_toSubgroup_le c.ground.toSubgroup
      T'.ground_toSubgroup_le)
  simpa only [ContCohomology.coe_explicitCor0Le, AddMonoidHom.comp_apply,
    Subgroup.smul_def, finsum_eq_sum_of_fintype,
    Representation.ofDistribMulAction_apply_apply] using congrArg Subtype.val h

end LayerRestriction

end TauCeti.ClassFieldTheory
