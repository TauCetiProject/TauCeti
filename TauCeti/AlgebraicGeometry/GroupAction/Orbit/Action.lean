/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme

/-!
# The algebraic action on an orbit scheme

The locally closed scheme image of an orbit morphism carries the restriction of the
ambient group action. This is an action on all test-scheme points, including points
over nonreduced algebras. Its inclusion into the ambient scheme is equivariant, and
the orbit morphism is equivariant for left multiplication on the group.

Construct the action by factoring through the orbit immersion after the surjective,
scheme-theoretically dominant cover from the group. Flatness over the ground field
preserves schematic dominance when taking the product with the group. Neither the
group nor the acted-on scheme is required to be reduced or connected.

Use the existing `orbitScheme` and
`Scheme.Hom.existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant`,
together with Mathlib's flat-base-change theorem for schematic dominance.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- The orbit scheme as a scheme over the original ground field. -/
abbrev orbitOver : Over (Spec (.of k)) := Over.mk (orbitToBase G x)

/-- The orbit immersion as a morphism over the ground field. -/
def orbitInclusion : orbitOver G x ⟶ X :=
  Over.homMk (orbitι G x) (orbitToBase_def G x).symm

/-- The orbit factorization as a morphism over the ground field. -/
def orbitProjection : G ⟶ orbitOver G x :=
  Over.homMk (toOrbit G x) (toOrbit_toBase G x)

/-- Forgetting the base recovers the orbit immersion. -/
@[simp]
theorem orbitInclusion_left : (orbitInclusion G x).left = orbitι G x := (rfl)

/-- Forgetting the base recovers the surjective orbit factorization. -/
@[simp]
theorem orbitProjection_left : (orbitProjection G x).left = toOrbit G x := (rfl)

/-- The factorization over the field recovers the ambient orbit map. -/
@[reassoc (attr := simp)]
theorem orbitProjection_inclusion : orbitProjection G x ≫ orbitInclusion G x = orbitMap G x := by
  ext
  simp

instance : Mono (orbitInclusion G x) := by
  have : Mono (orbitInclusion G x).left := by
    rw [orbitInclusion_left]
    infer_instance
  exact Over.mono_of_mono_left _

private theorem isPullback_orbitProjection :
    IsPullback (pullback.snd G.hom G.hom) (G ◁ orbitProjection G x).left
      (toOrbit G x) (pullback.snd G.hom (orbitToBase G x)) := by
  have hf : (G ◁ orbitProjection G x).left ≫ pullback.fst G.hom (orbitToBase G x) =
      pullback.fst G.hom G.hom := Over.whiskerLeft_left_fst (orbitProjection G x)
  have h : IsPullback (pullback.snd G.hom G.hom)
      ((G ◁ orbitProjection G x).left ≫ pullback.fst G.hom (orbitToBase G x))
      (toOrbit G x ≫ orbitToBase G x) G.hom := by
    rw [hf, toOrbit_toBase]
    exact (IsPullback.of_hasPullback G.hom G.hom).flip
  exact h.of_bot (by
    simpa only [orbitOver, Over.mk_hom, orbitProjection_left] using
      (Over.whiskerLeft_left_snd (R := G) (orbitProjection G x)).symm)
    (IsPullback.of_hasPullback G.hom (orbitToBase G x)).flip

private theorem exists_orbitAction :
    ∃! a : (G ⊗ orbitOver G x).left ⟶ orbitScheme G x,
      a ≫ orbitι G x = (G ◁ orbitInclusion G x).left ≫ (γ[G, X]).left := by
  have : Surjective (G ◁ orbitProjection G x).left :=
    MorphismProperty.of_isPullback (isPullback_orbitProjection G x) inferInstance
  have : IsSchemeTheoreticallyDominant (G ◁ orbitProjection G x).left :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_orbitProjection G x)
  apply (orbitι G x).existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    _ (G ◁ orbitProjection G x).left ((μ[G]).left ≫ toOrbit G x)
  rw [Category.assoc, toOrbit_ι]
  have h' : μ[G] ≫ orbitMap G x =
      G ◁ orbitProjection G x ≫ G ◁ orbitInclusion G x ≫ γ[G, X] := by
    rw [← whiskerLeft_comp_assoc, orbitProjection_inclusion]
    exact mul_orbitMap G x
  simpa only [Over.comp_left] using congrArg Over.Hom.left h'

/-- The restricted action morphism on the orbit scheme over the ground field. -/
def orbitAction : G ⊗ orbitOver G x ⟶ orbitOver G x :=
  Over.homMk (exists_orbitAction G x).exists.choose (by
    calc
      _ = (exists_orbitAction G x).exists.choose ≫ orbitι G x ≫ X.hom :=
        congrArg ((exists_orbitAction G x).exists.choose ≫ ·) (orbitToBase_def G x)
      _ = (G ⊗ orbitOver G x).hom := by
        rw [← Category.assoc, (exists_orbitAction G x).exists.choose_spec,
          Category.assoc, Over.w]
        exact Over.w (G ◁ orbitInclusion G x))

/-- The restricted action followed by the orbit immersion is the ambient action. -/
@[reassoc (attr := simp)]
theorem orbitAction_inclusion :
    orbitAction G x ≫ orbitInclusion G x = G ◁ orbitInclusion G x ≫ γ[G, X] := by
  ext
  exact (exists_orbitAction G x).exists.choose_spec

/-- The ambient algebraic group action restricts to its locally closed orbit scheme. -/
instance orbitModObj : ModObj G (orbitOver G x) where
  smul := orbitAction G x
  one_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionUnitIso]
    apply (cancel_mono (orbitInclusion G x)).mp
    simp only [Category.assoc, orbitAction_inclusion]
    rw [← whisker_exchange_assoc, ModObj.one_smul_self]
    exact leftUnitor_naturality _
  mul_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionHomRight,
      MonoidalCategory.selfLeftAction_actionAssocIso]
    apply (cancel_mono (orbitInclusion G x)).mp
    simp only [Category.assoc, orbitAction_inclusion]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self]
    rw [← whiskerLeft_comp_assoc, orbitAction_inclusion, whiskerLeft_comp, Category.assoc,
      associator_naturality_right_assoc]

/-- The orbit immersion is equivariant for the restricted algebraic action. -/
instance : IsModHom G (orbitInclusion G x) where
  smul_hom := orbitAction_inclusion G x

/-- The displayed action morphism is the scalar multiplication of the orbit action. -/
theorem orbitAction_eq_smul : orbitAction G x = γ[G, orbitOver G x] := (rfl)

/-- The orbit immersion determines the restricted action morphism uniquely. -/
theorem orbitAction_unique (a : G ⊗ orbitOver G x ⟶ orbitOver G x)
    (ha : a ≫ orbitInclusion G x = G ◁ orbitInclusion G x ≫ γ[G,X]) :
    a = orbitAction G x :=
  (cancel_mono (orbitInclusion G x)).mp (ha.trans (orbitAction_inclusion G x).symm)

/-- The orbit factorization intertwines left multiplication with the restricted action. -/
@[reassoc]
theorem mul_orbitProjection :
    μ[G] ≫ orbitProjection G x = G ◁ orbitProjection G x ≫ γ[G, orbitOver G x] := by
  apply (cancel_mono (orbitInclusion G x)).mp
  simp only [Category.assoc, orbitProjection_inclusion, IsModHom.smul_hom,
    MonoidalCategory.selfLeftAction_actionHomRight]
  rw [← whiskerLeft_comp_assoc, orbitProjection_inclusion, mul_orbitMap]

/-- Equivariance of the orbit factorization on points of every test scheme. -/
theorem mul_comp_orbitProjection {T : Over (Spec (.of k))} (g h : T ⟶ G) :
    (g * h) ≫ orbitProjection G x = g • (h ≫ orbitProjection G x) := by
  simp only [Hom.mul_def, Category.assoc, mul_orbitProjection, Hom.smul_def,
    ← lift_whiskerLeft_assoc]

/-- The restricted algebraic action recovers the previously constructed orbit translations. -/
theorem translation_orbitOver (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (Over.forget _).mapIso (translation (orbitOver G x) g) = orbitTranslation G x g := by
  apply Iso.ext
  apply (cancel_mono (orbitι G x)).mp
  rw [orbitTranslation_hom_ι]
  exact congrArg Over.Hom.left (translation_hom_comp g (orbitInclusion G x))

end TauCeti.SchemeAction
