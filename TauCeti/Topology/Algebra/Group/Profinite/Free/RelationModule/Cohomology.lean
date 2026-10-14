/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Extension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Second cohomology in Lyndon's relation-module coordinates

For a finite group presented by a finite generating family, Lyndon's isomorphism identifies
its pro-`p` relation group with the integral group-algebra relation module. This file reads
explicit continuous second cohomology of the former as algebraic second cohomology of the
latter, retaining the action of the presented group. Thus a map of algebraic relation modules
can be compared with a coefficient map on the kernels of profinite extensions.

The coefficient identification is `abelianizationProPEquivRelationModule`, and the cohomology
identification is `ContCohomology.explicitH2AddEquivGroupCohomology` at that compatible pair.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (5.6.6) and the proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti.freeProfiniteGroup

open Additive CategoryTheory ContCohomology _root_.Rep

variable (p : ℕ) [Fact p.Prime] {G ι : Type} [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G] [Fintype ι] [DecidableEq ι]
  {g : ι → G} (hg : Subgroup.closure (Set.range g) = ⊤)

/-- Lyndon's coordinates intertwine the presented group's conjugation action with its
left group-algebra action on the relation module. -/
@[simp]
theorem abelianizationProPEquivRelationModule_presentation_smul (t : G)
    (x : Additive (abelianizationProP p (freeProfiniteGroup ι)
      (lift g : freeProfiniteGroup ι →* G).ker)) :
    letI := presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    abelianizationProPEquivRelationModule p hg (t • x) =
      MonoidAlgebra.single t (1 : ℤ_[p]) • abelianizationProPEquivRelationModule p hg x := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set G) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  let := presentationClassModuleAction p hd
  obtain ⟨f, rfl⟩ := lift_surjective hd t
  rw [← ofMul_toMul x, ← ofMul_smul, presentationClassModuleAction_lift_smul,
    ofMul_smul]
  exact abelianizationProPEquivRelationModule_smul p hg f x

/-- Explicit second cohomology of the pro-`p` relation group, with the presented group's
conjugation action, is second cohomology of its integral relation-module representation. -/
def explicitH2EquivRelationModule :
    letI := presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    H2 G (Additive (abelianizationProP p (freeProfiniteGroup ι)
      (lift g : freeProfiniteGroup ι →* G).ker)) ≃+
      _root_.groupCohomology
        (ofModuleMonoidAlgebra.obj
          (ModuleCat.of (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra.relationModule ℤ_[p] G g))) 2 := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set G) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  letI := presentationClassModuleAction p hd
  letI := continuousSMul_presentationClassModuleAction p hd
  exact explicitH2AddEquivGroupCohomology (.refl G)
    ((abelianizationProPEquivRelationModule p hg).trans
      (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] G)
        (MonoidAlgebra.relationModule ℤ_[p] G g)).symm)
    (fun t x ↦ by
      -- The representation attached to a group-algebra module acts by `single t 1`.
      change abelianizationProPEquivRelationModule p hg (t • x) =
        MonoidAlgebra.single t (1 : ℤ_[p]) • abelianizationProPEquivRelationModule p hg x
      exact abelianizationProPEquivRelationModule_presentation_smul p hg t x)

/-- The comparison sends a cocycle class to that same cocycle in Lyndon's coordinates. -/
theorem explicitH2EquivRelationModule_mk :
    letI := presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    ∀ (z : Z2 G (Additive (abelianizationProP p (freeProfiniteGroup ι)
        (lift g : freeProfiniteGroup ι →* G).ker)))
      (c : _root_.groupCohomology.cocycles₂
        (ofModuleMonoidAlgebra.obj
          (ModuleCat.of (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra.relationModule ℤ_[p] G g)))),
      (∀ t, c t = abelianizationProPEquivRelationModule p hg ((z : G × G → _) t)) →
      explicitH2EquivRelationModule p hg (z : H2 G _) = _root_.groupCohomology.H2π _ c := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set G) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  let := presentationClassModuleAction p hd
  let := continuousSMul_presentationClassModuleAction p hd
  intros z c hc
  apply explicitH2AddEquivGroupCohomology_mk
  exact hc

end TauCeti.freeProfiniteGroup
