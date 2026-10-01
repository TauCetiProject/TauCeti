/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Quotient
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# The congruence topology on continuous automorphisms

For a topological group `G`, the congruence topology on `ContinuousAut G` is the initial topology
for its actions on the quotients by topologically characteristic open normal subgroups.  Each
coordinate

`ContinuousAut G →* MulAut (G ⧸ N)`

has discrete target.  Thus two automorphisms are close when they induce the same automorphism on
a sufficiently fine characteristic finite quotient.  Finiteness of the quotient is not needed to
define the topology; it enters later when proving compactness for topologically finitely generated
profinite groups.

The quotient coordinates are homomorphisms, so the initial topology makes `ContinuousAut G` a
topological group.  The inner-automorphism homomorphism `ContinuousAut.conj` is continuous: on
the quotient by `N` it is the composite of the quotient map `G → G ⧸ N` with the inner
automorphism map of the discrete quotient.

## Main results

* `TauCeti.ContinuousAut.continuous_mapQuotient`: every characteristic quotient coordinate is
  continuous into its discrete automorphism group.
* `TauCeti.ContinuousAut.continuous_iff_forall_continuous_mapQuotient`: continuity into the
  automorphism group can be checked on all characteristic quotient coordinates.
* `TauCeti.ContinuousAut.instIsTopologicalGroup`: composition and inversion are continuous for
  the congruence topology.
* `TauCeti.ContinuousAut.continuous_conj`: the homomorphism from `G` to its continuous inner
  automorphisms is continuous.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

namespace TauCeti

namespace ContinuousAut

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- The congruence topology on `ContinuousAut G`: the initial topology of its actions on the
discrete automorphism groups of all topologically characteristic open normal quotients. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (ContinuousAut G) :=
  ⨅ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N.toSubgroup},
    TopologicalSpace.induced (mapQuotient N.property) ⊥

/-- The action of `ContinuousAut G` on every topologically characteristic open normal quotient is
continuous when the quotient automorphism group is discrete. -/
theorem continuous_mapQuotient
    (N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N.toSubgroup}) :
    @Continuous _ _ inferInstance ⊥ (mapQuotient N.property) :=
  continuous_iInf_dom (i := N) continuous_induced_dom

/-- A map into `ContinuousAut G` is continuous exactly when all of its characteristic quotient
coordinates are continuous into the corresponding discrete automorphism groups. -/
theorem continuous_iff_forall_continuous_mapQuotient {X : Type*} [TopologicalSpace X]
    {f : X → ContinuousAut G} :
    Continuous f ↔
      ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N.toSubgroup},
        @Continuous _ _ inferInstance ⊥ (mapQuotient N.property ∘ f) := by
  unfold instTopologicalSpace
  rw [continuous_iInf_rng]
  simp_rw [continuous_induced_rng]

/-- The kernel of a characteristic quotient coordinate is open in the congruence topology. -/
theorem isOpen_ker_mapQuotient
    (N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N.toSubgroup}) :
    IsOpen ((mapQuotient N.property).ker : Set (ContinuousAut G)) := by
  let _ : TopologicalSpace (MulAut (G ⧸ N.val.toSubgroup)) := ⊥
  have _ : DiscreteTopology (MulAut (G ⧸ N.val.toSubgroup)) := ⟨rfl⟩
  have hker : ((mapQuotient N.property).ker : Set (ContinuousAut G)) =
      mapQuotient N.property ⁻¹' {1} := by
    ext
    simp
  rw [hker]
  exact (continuous_mapQuotient G N).isOpen_preimage {1} (isOpen_discrete {1})

/-- The congruence topology makes the continuous automorphisms into a topological group. -/
instance instIsTopologicalGroup : IsTopologicalGroup (ContinuousAut G) := by
  apply isTopologicalGroup_iInf
  intro N
  let _ : TopologicalSpace (MulAut (G ⧸ N.val.toSubgroup)) := ⊥
  have _ : DiscreteTopology (MulAut (G ⧸ N.val.toSubgroup)) := ⟨rfl⟩
  exact isTopologicalGroup_induced (mapQuotient N.property)

variable [SeparatelyContinuousMul G]

/-- The homomorphism sending an element of `G` to its continuous inner automorphism is continuous
for the congruence topology on `ContinuousAut G`. -/
theorem continuous_conj : Continuous (conj : G →* ContinuousAut G) := by
  unfold instTopologicalSpace
  rw [continuous_iInf_rng]
  intro N
  rw [continuous_induced_rng]
  have hquot : Continuous fun g : G ↦ (g : G ⧸ N.val.toSubgroup) :=
    QuotientGroup.continuous_mk
  let _ : TopologicalSpace (MulAut (G ⧸ N.val.toSubgroup)) := ⊥
  have _ : DiscreteTopology (MulAut (G ⧸ N.val.toSubgroup)) := ⟨rfl⟩
  have hinner : @Continuous (G ⧸ N.val.toSubgroup) (MulAut (G ⧸ N.val.toSubgroup))
      inferInstance ⊥ MulAut.conj :=
    continuous_of_discreteTopology
  exact (hinner.comp hquot).congr fun g ↦ (mapQuotient_conj N.property g).symm

end ContinuousAut

end TauCeti
