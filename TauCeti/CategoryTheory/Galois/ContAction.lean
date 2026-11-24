/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import TauCeti.CategoryTheory.Action.EssentiallySmall

/-!
# A profinite group is the fundamental group of its finite continuous actions

Let `G` be a topological group. Mathlib shows that finite sets with a continuous `G`-action form
a Galois category `ContAction FintypeCat G`. This file shows that the forgetful functor to finite
sets is a fibre functor and that, when `G` is profinite (compact, Hausdorff and totally
disconnected), `G` itself is a fundamental group of it in the sense of
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`. Consequently
`CategoryTheory.PreGaloisCategory.toAutMulEquiv` identifies `G` with the automorphism group of the
forgetful functor, as groups and as topological spaces.

Recognising a category as equivalent to `ContAction FintypeCat G` therefore computes the
fundamental group of a fibre functor: for instance, Galois theory identifies finite étale
algebras over a field with finite continuous sets under its absolute Galois group.

The two inputs are that a connected finite continuous `G`-set is a transitive `G`-set, since an
orbit is a subobject (`ContAction.isPretransitive_of_isConnected`), and that a nontrivial element
of a profinite group moves a coset of some open normal subgroup
(`ContAction.eq_one_of_forall_smul_eq`).

The file also records basic facts about the underlying sets of finite continuous `G`-sets
(`ContAction.fiberFunctor`): a finite `G`-set is continuous exactly when its stabilizers are open
(`Action.isContinuous_iff_isOpen_stabilizer`), morphisms are `G`-maps (`ContAction.fiberHom`),
and points of underlying sets lift to pullbacks (`ContAction.exists_fiberFunctor_pullback`).

## Main results

* `Action.isContinuous_iff_isOpen_stabilizer`: an action on a finite set is continuous exactly
  when its stabilizers are open.
* `ContAction.isPretransitive_of_isConnected`: `G` acts transitively on a connected object of
  `ContAction FintypeCat G`.
* `ContAction.mulActionHom_ext_of_isConnected`: `G`-maps out of a connected finite continuous
  `G`-set are determined by their value at one point.
* `ContAction.instIsFundamentalGroup`: a profinite group `G` is a fundamental group of the
  forgetful fibre functor on `ContAction FintypeCat G`.

## References

* H. W. Lenstra, *Galois theory for schemes*, Example 3.5 and Theorem 3.17.
-/

public section

open CategoryTheory Limits PreGaloisCategory FintypeCatDiscrete

universe u

/-- An action on a finite set is continuous exactly when its stabilizers are open, since the
underlying space carries the discrete topology. -/
theorem Action.isContinuous_iff_isOpen_stabilizer {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : Action FintypeCat.{u} G) :
    Action.isContinuous FintypeCat G X ↔ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G) :=
  -- `FintypeCatDiscrete` gives the underlying space of a finite set the discrete topology.
  have : DiscreteTopology ((forget₂ (Action FintypeCat.{u} G) TopCat).obj X) :=
    inferInstanceAs (DiscreteTopology X.V)
  continuousSMul_iff_stabilizer_isOpen (X := (forget₂ (Action FintypeCat.{u} G) TopCat).obj X)

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The forgetful functor from finite continuous `G`-sets to finite sets is a fibre functor. -/
noncomputable instance : FiberFunctor (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) :=
  inferInstanceAs <|
    FiberFunctor ((Action.isContinuous FintypeCat G).ι ⋙ Action.forget FintypeCat G)

/-- `G` acts on the underlying finite set of a finite continuous `G`-set. -/
instance instMulActionObjForget₂ (X : ContAction FintypeCat.{u} G) :
    MulAction G ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}).obj X) :=
  inferInstanceAs (MulAction G X.obj.V)

/-- A connected finite continuous `G`-set is connected as a finite `G`-set: its subobjects as a
finite `G`-set are again continuous. -/
theorem isConnected_obj (X : ContAction FintypeCat.{u} G) [IsConnected X] : IsConnected X.obj where
  notInitial := (not_initial_iff_fiber_nonempty (Action.forget FintypeCat G) X.obj).mpr
    (nonempty_fiber_of_isConnected (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) X)
  noTrivialComponent Y i _ hY := by
    have hYc : Action.isContinuous FintypeCat G Y :=
      (Action.isContinuous FintypeCat G).prop_of_mono i X.property
    let j : (⟨Y, hYc⟩ : ContAction FintypeCat.{u} G) ⟶ X := ObjectProperty.homMk i
    have : Mono j := (Action.isContinuous FintypeCat G).ι.mono_of_mono_map ‹_›
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty (Action.forget FintypeCat G) Y).mp hY
    have : IsIso j := IsConnected.noTrivialComponent _ j
      (not_initial_of_inhabited (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) y)
    have : IsIso ((Action.isContinuous FintypeCat G).ι.map j) := inferInstance
    rwa [ObjectProperty.ι_map, ObjectProperty.homMk_hom] at this

/-- `G` acts transitively on a connected finite continuous `G`-set. -/
theorem isPretransitive_of_isConnected (X : ContAction FintypeCat.{u} G) [IsConnected X] :
    MulAction.IsPretransitive G X.obj.V :=
  have := isConnected_obj X
  FintypeCat.Action.pretransitive_of_isConnected G X.obj

variable (G) in
/-- The underlying set of a finite continuous `G`-set, as a functor to types. -/
abbrev fiberFunctor : ContAction FintypeCat.{u} G ⥤ Type u :=
  forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl

/-- `G` acts on the underlying set of a finite continuous `G`-set. -/
instance instMulActionFiberFunctorObj (S : ContAction FintypeCat.{u} G) :
    MulAction G ((fiberFunctor G).obj S) :=
  inferInstanceAs (MulAction G S.obj.V)

variable (G) in
/-- Finite continuous `G`-sets form an essentially small category. -/
instance instEssentiallySmallIsContinuous :
    ObjectProperty.EssentiallySmall.{u} (Action.isContinuous FintypeCat.{u} G) :=
  .of_le (Q := ⊤) le_top

omit [IsTopologicalGroup G] in
/-- Morphisms of finite continuous `G`-sets are `G`-equivariant. -/
theorem fiberFunctor_map_smul {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T) (g : G)
    (s : (fiberFunctor G).obj S) :
    (fiberFunctor G).map f (g • s) = g • (fiberFunctor G).map f s :=
  ConcreteCategory.congr_hom (f.hom.comm g) s

/-- Stabilizers of points of a finite continuous `G`-set are open. -/
theorem isOpen_stabilizer (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) :
    IsOpen (MulAction.stabilizer G s : Set G) :=
  (Action.isContinuous_iff_isOpen_stabilizer S.obj).1 S.property s

/-- A morphism of finite continuous `G`-sets as a `G`-map of underlying sets. -/
@[expose]
def fiberHom {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T) :
    (fiberFunctor G).obj S →[G] (fiberFunctor G).obj T where
  toFun := (fiberFunctor G).map f
  map_smul' := fiberFunctor_map_smul f

omit [IsTopologicalGroup G] in
/-- `fiberHom f` applies `f` to underlying points. -/
theorem fiberHom_apply {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T)
    (s : (fiberFunctor G).obj S) : fiberHom f s = (fiberFunctor G).map f s :=
  (rfl)

/-- Every pair of points of finite continuous `G`-sets with the same image in `S` comes from a
point of the pullback. -/
theorem exists_fiberFunctor_pullback {S T₁ T₂ : ContAction FintypeCat.{u} G} (f₁ : T₁ ⟶ S)
    (f₂ : T₂ ⟶ S) (t₁ : (fiberFunctor G).obj T₁) (t₂ : (fiberFunctor G).obj T₂)
    (h : (fiberFunctor G).map f₁ t₁ = (fiberFunctor G).map f₂ t₂) :
    ∃ p : (fiberFunctor G).obj (pullback f₁ f₂),
      (fiberFunctor G).map (pullback.fst f₁ f₂) p = t₁ ∧
        (fiberFunctor G).map (pullback.snd f₁ f₂) p = t₂ :=
  ⟨(fiberPullbackEquiv (forget₂ _ FintypeCat.{u}) f₁ f₂).symm ⟨(t₁, t₂), h⟩,
    fiberPullbackEquiv_symm_fst_apply .., fiberPullbackEquiv_symm_snd_apply ..⟩

/-- Two `G`-maps out of the underlying set of a connected finite continuous `G`-set that agree at
one point are equal, since `G` acts transitively. -/
theorem mulActionHom_ext_of_isConnected {A : ContAction FintypeCat.{u} G} [IsConnected A]
    {Y : Type*} [MulAction G Y] {φ ψ : (fiberFunctor G).obj A →[G] Y}
    (a : (fiberFunctor G).obj A) (h : φ a = ψ a) : φ = ψ := by
  have : MulAction.IsPretransitive G ((fiberFunctor G).obj A) := isPretransitive_of_isConnected A
  ext b
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a b
  rw [map_smul, map_smul, h]

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- An element of a profinite group acting trivially on every finite continuous `G`-set is the
identity: otherwise it moves the base coset of an open normal subgroup avoiding it. -/
theorem eq_one_of_forall_smul_eq (g : G)
    (h : ∀ (X : ContAction FintypeCat.{u} G) (x : X.obj.V), g • x = x) : g = 1 := by
  by_contra hg
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := g)) (Ne.symm hg)
  have : Fintype (G ⧸ H.toSubgroup) := Fintype.ofFinite _
  -- `G ⧸ H` is a finite continuous `G`-set, since the normal subgroup `H` acts trivially on it.
  have hX : Action.isContinuous FintypeCat G (G ⧸ₐ H.toSubgroup) :=
    Action.trivialOnSet_le_isContinuous H.toOpenSubgroup _ fun h hh => by
      ext x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      -- The action of `h` on the finite `G`-set `G ⧸ₐ H` is left multiplication on cosets.
      change h • (a : G ⧸ H.toSubgroup) = (a : G ⧸ H.toSubgroup)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using H.isNormal'.conj_mem _ (H.inv_mem hh) a⁻¹
  have h1 := h ⟨_, hX⟩ (1 : G ⧸ H.toSubgroup)
  -- The action on the underlying set of `⟨G ⧸ₐ H, hX⟩` is the action of `G` on cosets.
  change g • (1 : G ⧸ H.toSubgroup) = 1 at h1
  rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    QuotientGroup.mk_one, QuotientGroup.eq_one_iff] at h1
  exact hH h1 rfl

/-- **A profinite group is a fundamental group of the forgetful functor on its finite continuous
actions.** -/
instance instIsFundamentalGroup :
    IsFundamentalGroup (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) G where
  naturality g _ _ f x := ConcreteCategory.congr_hom (f.hom.comm g) x
  transitive_of_isGalois X _ := isPretransitive_of_isConnected X
  continuous_smul X := X.property
  non_trivial' g h := eq_one_of_forall_smul_eq g h

end ContAction
