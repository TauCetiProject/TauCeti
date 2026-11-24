/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Conservative
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FieldSheaf
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FundamentalGroup
public import TauCeti.CategoryTheory.Galois.Sheaf
public import TauCeti.CategoryTheory.Sites.JointlySurjective

/-!
# Étale sheaves on a field as continuous discrete Galois sets

Let `K` be a field with separable closure `Ω`. Étale sheaves on `Spec K` are sheaves on finite
étale `K`-schemes (`TauCeti.FiniteEtaleScheme.fieldSheafEquiv`), and Galois theory transports
their topology to the topology `TauCeti.FiniteEtaleScheme.galoisTopology K Ω` on finite continuous
`Gal(Ω/K)`-sets. This file shows that this topology is the jointly surjective topology
`ContAction.jointlySurjectiveTopology Gal(Ω/K)` (`TauCeti.FiniteEtaleScheme.galoisTopology_eq`),
so that étale sheaves on `Spec K` are sheaves for the jointly surjective topology
(`TauCeti.FiniteEtaleScheme.jointlySurjectiveSheafEquiv`). It then composes with
`ContAction.sheafEquiv`, which identifies sheaves of sets for the jointly
surjective topology with `Gal(Ω/K)`-sets whose stabilizers are open. The result,
`TauCeti.VanishingCycles.fieldSheavesEquiv K Ω`, identifies étale sheaves of sets on `Spec K`
with continuous discrete `Gal(Ω/K)`-sets.

The comparison of topologies goes through geometric fibres. Over a connected base, a family of
morphisms of finite étale schemes is jointly surjective exactly when it is jointly surjective on
a geometric fibre (`TauCeti.FiniteEtaleScheme.iUnion_range_eq_univ_iff`, from
`TauCeti.AlgebraicGeometry.FiniteEtale.Conservative`). At the geometric point
`Spec Ω ⟶ Spec K`, the geometric fibre is the underlying set of the finite Galois set attached by
`TauCeti.FiniteEtaleScheme.galoisEquivalence K Ω`
(`TauCeti.FiniteEtaleScheme.fiberIsoFiniteEtaleFiber`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.jointlySurjectiveSheafEquiv K Ω A`: étale sheaves on `Spec K` with
  values in `A` are sheaves on finite continuous `Gal(Ω/K)`-sets for the jointly surjective
  topology.
* `TauCeti.VanishingCycles.fieldSheavesEquiv K Ω`: étale sheaves of sets on `Spec K` are
  continuous discrete `Gal(Ω/K)`-sets.

## Main results

* `TauCeti.FiniteEtaleScheme.galoisTopology_eq`: the topology `galoisTopology K Ω` is the jointly
  surjective topology.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
* The Stacks Project, Tag 03QQ.
-/

public section

open CategoryTheory Limits AlgebraicGeometry FintypeCatDiscrete

universe v u

namespace TauCeti.FiniteEtaleScheme

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω]

/-- The geometric fibre at `Spec Ω ⟶ Spec K` of the finite étale `K`-scheme of a finite
continuous `Gal(Ω/K)`-set is its underlying set. -/
private noncomputable def inverseCompFiberIso :
    (galoisEquivalence K Ω).inverse ⋙ fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⋙
      FintypeCat.incl ≅ ContAction.fiberFunctor Gal(Ω/K) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (fiberIsoFiniteEtaleFiber K Ω ≪≫
      eqToIso (by rw [galoisEquivalence_functor, Functor.assoc, galoisFiber_comp_forget₂]) :
        _ ≅ (galoisEquivalence K Ω).functor ⋙ forget₂ _ FintypeCat) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (galoisEquivalence K Ω).counitIso _ ≪≫ Functor.leftUnitor _

/-- **The Galois topology is the jointly surjective topology.** A family of morphisms of finite
continuous `Gal(Ω/K)`-sets covers for `galoisTopology K Ω` exactly when it is jointly surjective
on underlying sets. -/
theorem galoisTopology_eq :
    galoisTopology K Ω = ContAction.jointlySurjectiveTopology Gal(Ω/K) := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_galoisTopology_iff, ContAction.ofArrows_mem_jointlySurjectiveTopology_iff,
    iUnion_range_eq_univ_iff (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))]
  exact (inverseCompFiberIso K Ω).forall_exists_mem_range_map_iff _

instance isDenseSubsite_inverse_galoisEquivalence :
    (galoisEquivalence K Ω).inverse.IsDenseSubsite
      (ContAction.jointlySurjectiveTopology Gal(Ω/K)) (fieldTopology K) :=
  galoisTopology_eq K Ω ▸ inferInstance

variable (A : Type v) [Category.{u} A] [HasLimitsOfSize.{u, u} A]

/-- **Étale sheaves on a field are sheaves for the jointly surjective topology.** For a separable
closure `Ω` of `K`, étale sheaves on `Spec K` with values in `A` are sheaves on finite continuous
`Gal(Ω/K)`-sets for the jointly surjective topology. -/
noncomputable def jointlySurjectiveSheafEquiv :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) A ≌
      Sheaf (ContAction.jointlySurjectiveTopology Gal(Ω/K)) A :=
  (fieldSheafEquiv K A).trans ((galoisEquivalence K Ω).sheafCongr (fieldTopology K)
    (ContAction.jointlySurjectiveTopology Gal(Ω/K)) A)

/-- The functor of `jointlySurjectiveSheafEquiv K Ω A` restricts a sheaf to finite étale
`K`-schemes and transports it along `galoisEquivalence K Ω`. -/
@[simp] theorem jointlySurjectiveSheafEquiv_functor :
    (jointlySurjectiveSheafEquiv K Ω A).functor = (fieldSheafEquiv K A).functor ⋙
      ((galoisEquivalence K Ω).sheafCongr (fieldTopology K)
        (ContAction.jointlySurjectiveTopology Gal(Ω/K)) A).functor :=
  (rfl)

/-- The inverse of `jointlySurjectiveSheafEquiv K Ω A` transports a sheaf back along
`galoisEquivalence K Ω` and then inverts the restriction to finite étale `K`-schemes. -/
@[simp] theorem jointlySurjectiveSheafEquiv_inverse :
    (jointlySurjectiveSheafEquiv K Ω A).inverse =
      ((galoisEquivalence K Ω).sheafCongr (fieldTopology K)
        (ContAction.jointlySurjectiveTopology Gal(Ω/K)) A).inverse ⋙
        (fieldSheafEquiv K A).inverse :=
  (rfl)

end TauCeti.FiniteEtaleScheme

namespace TauCeti.VanishingCycles

open FiniteEtaleScheme

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω]

/-- **Étale sheaves on a field are continuous discrete Galois sets** (SGA 4, Exposé VIII, §2).
For a separable closure `Ω` of `K`, étale sheaves of sets on `Spec K` are equivalent to sets with
an action of `Gal(Ω/K)` whose stabilizers are open. -/
noncomputable def fieldSheavesEquiv :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) (Type u) ≌ Action.SmoothSet Gal(Ω/K) :=
  (jointlySurjectiveSheafEquiv K Ω (Type u)).trans (ContAction.sheafEquiv Gal(Ω/K))

/-- The functor of `fieldSheavesEquiv K Ω` restricts an étale sheaf to finite étale `K`-schemes,
transports it to finite continuous `Gal(Ω/K)`-sets and takes its stalk at the forgetful point. -/
@[simp] theorem fieldSheavesEquiv_functor :
    (fieldSheavesEquiv K Ω).functor = (jointlySurjectiveSheafEquiv K Ω (Type u)).functor ⋙
      ContAction.fromSheaf Gal(Ω/K) := by
  rw [fieldSheavesEquiv, Equivalence.trans_functor, ContAction.sheafEquiv_functor]

/-- The inverse of `fieldSheavesEquiv K Ω` sends a continuous discrete `Gal(Ω/K)`-set to the
sheaf of `Gal(Ω/K)`-maps into it and transports that sheaf to an étale sheaf on `Spec K`. -/
@[simp] theorem fieldSheavesEquiv_inverse :
    (fieldSheavesEquiv K Ω).inverse = ContAction.toSheaf Gal(Ω/K) ⋙
      (jointlySurjectiveSheafEquiv K Ω (Type u)).inverse := by
  rw [fieldSheavesEquiv, Equivalence.trans_inverse, ContAction.sheafEquiv_inverse]

end TauCeti.VanishingCycles
