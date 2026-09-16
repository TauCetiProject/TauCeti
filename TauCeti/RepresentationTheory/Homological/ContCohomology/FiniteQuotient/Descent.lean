/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Discrete
import TauCeti.Topology.Algebra.Group.LocallyConstant
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# Descent of continuous functions to finite quotients

A continuous function from a profinite group to a discrete module factors through a sufficiently
deep finite quotient, with values in the fixed points at that level. The quotient may be chosen
below any prescribed open normal subgroup.

## Main statement

* `TauCeti.ContCohomology.exists_openNormalSubgroup_descendContinuous`: continuous functions
  descend to fixed-point-valued functions on sufficiently deep finite quotients.
-/

public section

namespace TauCeti.ContCohomology

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A continuous function from a profinite group to a discrete module descends below any
prescribed open normal subgroup to a continuous function on a finite quotient, with values fixed
by that subgroup. -/
theorem exists_openNormalSubgroup_descendContinuous (U : OpenNormalSubgroup G)
    (b : G → M) (hb : Continuous b) :
    ∃ (V : OpenNormalSubgroup G) (_hVU : V ≤ U)
      (bV : G ⧸ V.toSubgroup → FixedPoints.addSubgroup V.toSubgroup M),
      Continuous bV ∧ ∀ g : G, (bV (g : G ⧸ V.toSubgroup) : M) = b g := by
  have hloc : IsLocallyConstant b := (IsLocallyConstant.iff_continuous _).2 hb
  have hopen : IsOpen (rightTranslationStabilizer b : Set G) :=
    isOpen_rightTranslationStabilizer hloc
  obtain ⟨W, hW⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen
      (rightTranslationStabilizer b).one_mem
  obtain ⟨A, hA⟩ :=
    hloc.range_finite.exists_openNormalSubgroup_smul_eq_self (G := G)
  let V := (U ⊓ W) ⊓ A
  have hVU : V ≤ U := (inf_le_left : V ≤ U ⊓ W).trans inf_le_left
  have hright : ∀ (g : G) (n : V), b (g * n) = b g := by
    intro g n
    apply mem_rightTranslationStabilizer.mp
      (hW ((inf_le_right : U ⊓ W ≤ W) ((inf_le_left : V ≤ U ⊓ W) n.2)))
  have hfixed : ∀ (n : V) (g : G), n • b g = b g := by
    intro n g
    exact hA n
      ((inf_le_right : V ≤ A) n.2) (b g) ⟨g, rfl⟩
  let b' : G → FixedPoints.addSubgroup V.toSubgroup M := fun g =>
    ⟨b g, (FixedPoints.mem_addSubgroup V.toSubgroup M _).2 fun n => hfixed n g⟩
  have hb' : Continuous b' :=
    hb.subtype_mk fun g => (FixedPoints.mem_addSubgroup V.toSubgroup M _).2 fun n => hfixed n g
  have hrel : ∀ a c : G, QuotientGroup.leftRel V.toSubgroup a c → b' a = b' c :=
    fun a c hac => Subtype.ext <| by
      simpa [b'] using (hright a ⟨a⁻¹ * c, QuotientGroup.leftRel_apply.1 hac⟩).symm
  exact ⟨V, hVU, fun q => Quotient.liftOn' q b' hrel, hb'.quotient_liftOn' hrel, fun _ => rfl⟩

end TauCeti.ContCohomology
