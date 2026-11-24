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

/-!
# Étale sheaves on a field as continuous discrete Galois sets

Let `K` be a field with separable closure `Ω`. Étale sheaves on `Spec K` are sheaves on finite
continuous `Gal(Ω/K)`-sets for the topology `TauCeti.FiniteEtaleScheme.galoisTopology K Ω`
transported from finite étale `K`-schemes (`TauCeti.FiniteEtaleScheme.galoisSheafEquiv`). This
file shows that this topology is the jointly surjective topology
`ContAction.jointlySurjectiveTopology Gal(Ω/K)` (`TauCeti.FiniteEtaleScheme.galoisTopology_eq`),
and composes with `ContAction.sheafEquiv`, which identifies sheaves of sets for the jointly
surjective topology with `Gal(Ω/K)`-sets whose stabilizers are open. The result,
`TauCeti.VanishingCycles.fieldSheavesEquiv K Ω`, identifies étale sheaves of sets on `Spec K`
with continuous discrete `Gal(Ω/K)`-sets.

The comparison of topologies goes through geometric fibres. Over a connected base, a family of
morphisms of finite étale schemes is jointly surjective exactly when it is jointly surjective on
a geometric fibre (`TauCeti.FiniteEtaleScheme.iUnion_range_eq_univ_iff`). At the geometric point
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

* `TauCeti.FiniteEtaleScheme.iUnion_range_eq_univ_iff`: over a connected base, a family of
  morphisms of finite étale schemes is jointly surjective if and only if it is jointly surjective
  on a geometric fibre.
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

section Fiber

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- A morphism `f` of finite étale schemes hits the image of a lift `s` of a geometric point
exactly when `s` lifts through `f`. -/
private theorem mem_range_fiber_map_of_mem_range (x : Spec (.of Ω) ⟶ S)
    {X Y : FiniteEtaleScheme S} (f : Y ⟶ X) (s : (fiber x ⋙ FintypeCat.incl).obj X)
    (p : Spec (.of Ω)) (hs : ((fiberCompInclIso x).hom.app X s).left p ∈ Set.range f.hom.left) :
    s ∈ Set.range ((fiber x ⋙ FintypeCat.incl).map f) := by
  set s' := (fiberCompInclIso x).hom.app X s
  -- The point `s'` of `X` lifts to `Y`, seen as a finite étale `X`-scheme `Z`.
  let Z : FiniteEtaleScheme X.obj.left :=
    ⟨Over.mk f.hom.left, (finiteEtaleSchemeProperty_iff _).mpr
      ⟨(inferInstance : IsFinite f.hom.left), (inferInstance : Etale f.hom.left)⟩⟩
  obtain ⟨a⟩ := (nonempty_fiber_obj_iff_range_subset_range s'.left Z).mpr (by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p]
    exact hs)
  let a' := (fiberCompInclIso s'.left).hom.app Z a
  have ha : a'.left ≫ f.hom.left = s'.left := Over.w a'
  let t : Over.mk x ⟶ Y.obj := Over.homMk a'.left (by
    rw [← Over.w f.hom, ← Category.assoc, ha]; exact Over.w s')
  refine ⟨(fiberCompInclIso x).inv.app Y t, ?_⟩
  apply ((fiberCompInclIso x).app X).toEquiv.injective
  have h := NatTrans.naturality_apply (fiberCompInclIso x).hom f ((fiberCompInclIso x).inv.app Y t)
  refine h.trans ?_
  simp only [Iso.app_hom, Iso.toEquiv_fun, Iso.inv_hom_id_app_apply]
  exact Over.OverMorphism.ext ha

/-- **Joint surjectivity on a geometric fibre.** Over a connected base, a family of morphisms of
finite étale schemes is jointly surjective exactly when it is jointly surjective on the geometric
fibre at any geometric point. -/
theorem iUnion_range_eq_univ_iff [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    {X : FiniteEtaleScheme S} {ι : Type*} {Y : ι → FiniteEtaleScheme S} (f : ∀ i, Y i ⟶ X) :
    ⋃ i, Set.range (f i).hom.left = .univ ↔
      ∀ s : (fiber x ⋙ FintypeCat.incl).obj X, ∃ i,
        s ∈ Set.range ((fiber x ⋙ FintypeCat.incl).map (f i)) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  refine ⟨fun h s ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (h ▸ Set.mem_univ (((fiberCompInclIso x).hom.app X s).left p))
    exact ⟨i, mem_range_fiber_map_of_mem_range x (f i) s p hi⟩
  have : Finite ((fiber x ⋙ FintypeCat.incl).obj X) := inferInstanceAs (Finite ((fiber x).obj X))
  choose j hj using h
  -- The points of `X` missed by the finitely many maps `f (j s)` form an open and closed set.
  let C : Set X.obj.left := ⋂ s, (Set.range (f (j s)).hom.left)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s ↦
    (f (j s)).hom.left.isOpenMap.isOpen_range.isClosed_compl
  let U : X.obj.left.Opens := ⟨C, isOpen_iInter_of_finite fun s ↦
    (f (j s)).hom.left.isClosedMap.isClosed_range.isOpen_compl⟩
  let v := clopenSubschemeι U hC
  refine Set.eq_univ_of_forall fun y ↦ by_contra fun hy ↦ ?_
  obtain ⟨q, -⟩ : y ∈ Set.range v.hom.left := by
    rw [range_clopenSubschemeι_hom_left]
    exact Set.mem_iInter.mpr fun s hs ↦ hy (Set.mem_iUnion.mpr ⟨_, hs⟩)
  -- A point `a` of the geometric fibre of `C` maps to a point of the fibre of `X`, which comes
  -- from a point `b` of the fibre of some `Y (j s)`.
  obtain ⟨a⟩ := (nonempty_fiber_obj_iff_nonempty x (clopenSubscheme U hC)).mpr ⟨q⟩
  set s := (fiber x ⋙ FintypeCat.incl).map v a
  obtain ⟨b, hb⟩ := hj s
  have h₁ := NatTrans.naturality_apply (fiberCompInclIso x).hom (f (j s)) b
  have h₂ := NatTrans.naturality_apply (fiberCompInclIso x).hom v a
  have h : (fiberCompInclIso x).hom.app _ b ≫ (f (j s)).hom =
      (fiberCompInclIso x).hom.app _ a ≫ v.hom := by
    simpa using h₁.symm.trans ((congrArg ((fiberCompInclIso x).hom.app X) hb).trans h₂)
  have hp := congrArg (fun g : Over.mk x ⟶ X.obj ↦ g.left p) h
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at hp
  have hv : v.hom.left (((fiberCompInclIso x).hom.app _ a).left p) ∈ (U : Set X.obj.left) :=
    range_clopenSubschemeι_hom_left U hC ▸ Set.mem_range_self _
  exact Set.mem_iInter.mp (show _ ∈ C from hv) s ⟨_, hp⟩

end Fiber

/-- Joint surjectivity of a family of maps under a functor to types is invariant under natural
isomorphism. -/
private theorem forall_exists_mem_range_iff {C : Type*} [Category* C] {F F' : C ⥤ Type u}
    (e : F ≅ F') {X : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    (∀ s : F.obj X, ∃ i, s ∈ Set.range (F.map (f i))) ↔
      ∀ s : F'.obj X, ∃ i, s ∈ Set.range (F'.map (f i)) := by
  suffices H : ∀ {F F' : C ⥤ Type u}, (F ≅ F') →
      (∀ s : F.obj X, ∃ i, s ∈ Set.range (F.map (f i))) →
        ∀ s : F'.obj X, ∃ i, s ∈ Set.range (F'.map (f i)) from ⟨H e, H e.symm⟩
  intro F F' e h s
  obtain ⟨i, t, ht⟩ := h (e.inv.app X s)
  refine ⟨i, e.hom.app _ t, ?_⟩
  rw [← NatTrans.naturality_apply, ht, Iso.inv_hom_id_app_apply]

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω]

/-- The geometric fibre at `Spec Ω ⟶ Spec K` of the finite étale `K`-scheme of a finite
continuous `Gal(Ω/K)`-set is its underlying set. -/
noncomputable def inverseCompFiberIso :
    (galoisEquivalence K Ω).inverse ⋙ fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⋙
      FintypeCat.incl ≅ ContAction.fiberFunctor Gal(Ω/K) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (fiberIsoFiniteEtaleFiber K Ω ≪≫
      eqToIso (by rw [galoisEquivalence_functor]; rfl) :
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
  exact forall_exists_mem_range_iff (inverseCompFiberIso K Ω) _

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

end TauCeti.VanishingCycles
