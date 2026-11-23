/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

import TauCeti.CategoryTheory.Sites.CoverPreserving

/-!
# Restricting a generated Grothendieck topology

Let `K` be a coverage on the ambient category `D` and `F : C ⥤ D` a functor.
Two independent conditions on generators at objects in the image of `F` suffice for
comparison with the generated comap topology. Covering of their pullbacks in the generated
comap topology gives equality with the restricted topology for fully faithful `F`.
Covering of their pullbacks' pushforwards in the ambient topology gives local cover density.
Together these conditions give cover detection by pushforward.

The comap `K.toPrecoverage.comap F` is a precoverage. The comparison concerns generated
Grothendieck topologies: `K` need not be stable under composition, and the comap precoverage
need not itself be a coverage. When every ambient generator at an image object has a refining
comap generator, `Coverage.comapOfRefineGenerators` supplies a coverage with this precoverage.

## Main results

* `Coverage.comapOfRefineGenerators`: the comap coverage under generator refinements.
* `Coverage.functorPullback_mem_toGrothendieck_comap_of_refine_generators`: a pulled-back
  ambient cover is covering for the generated comap topology.
* `Coverage.locallyCoverDense_of_refine_generators`: covering pushforwards of pulled-back
  generators imply local cover density for the generated topology.
* `Coverage.toGrothendieck_comap_eq_restrictedTopology_of_refine_generators`: covering
  pullbacks of generators give the comparison with the restricted topology.
* `Coverage.mem_toGrothendieck_comap_iff_of_refine_generators`: the resulting cover detection
  criterion by pushforward of sieves.
-/

public section

namespace CategoryTheory.Coverage

variable {C D : Type*} [Category* C] [Category* D] (K : Coverage D) (F : C ⥤ D)

/-- Refinements of ambient generators at image objects also refine their pullbacks along
arbitrary arrows from image objects. -/
theorem exists_presieve_pullback_le_of_refine_generators
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ∃ Q ∈ (K.toPrecoverage.comap F) X, Q.map F ≤ (Sieve.generate R).arrows)
    {Y : D} {R : Presieve Y} (hR : R ∈ K Y) (X : C) (f : F.obj X ⟶ Y) :
    ∃ Q ∈ (K.toPrecoverage.comap F) X,
      Q.map F ≤ ((Sieve.generate R).pullback f).arrows := by
  obtain ⟨P, hP, hf⟩ := K.pullback f R hR
  obtain ⟨Q, hQ, hle⟩ := refineGen hP
  have hP' : Sieve.generate P ≤ (Sieve.generate R).pullback f := by
    rw [Sieve.generate_le_iff]
    exact fun Z g hg ↦ hf hg
  exact ⟨Q, hQ, hle.trans hP'⟩

/-- Restrict a coverage along a fully faithful functor when every ambient generator at an
image object has a refining generator from the comap precoverage. -/
def comapOfRefineGenerators [F.Full] [F.Faithful]
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ∃ Q ∈ (K.toPrecoverage.comap F) X, Q.map F ≤ (Sieve.generate R).arrows) :
    Coverage C where
  __ := K.toPrecoverage.comap F
  pullback X Y f R hR := by
    rw [Precoverage.mem_comap_iff] at hR
    obtain ⟨Q, hQ, hle⟩ :=
      K.exists_presieve_pullback_le_of_refine_generators F refineGen hR Y (F.map f)
    refine ⟨Q, hQ, ?_⟩
    intro Z g hg
    have hgf := hle _ _ (Presieve.map_map hg)
    rw [Sieve.pullback_apply, ← F.map_comp, Sieve.generate_map_eq_functorPushforward] at hgf
    have hgf' : ((Sieve.generate R).functorPushforward F).functorPullback F (g ≫ f) := hgf
    rw [Sieve.functorPullback_functorPushforward_eq] at hgf'
    exact hgf'

/-- The restricted coverage has exactly the comap's generating presieves. -/
@[simp]
theorem comapOfRefineGenerators_toPrecoverage [F.Full] [F.Faithful]
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ∃ Q ∈ (K.toPrecoverage.comap F) X, Q.map F ≤ (Sieve.generate R).arrows) :
    (K.comapOfRefineGenerators F refineGen).toPrecoverage = K.toPrecoverage.comap F := by
  rfl

/-- An ambient covering sieve pulled back along an arrow from `F.obj X` and then along `F`
covers for the generated comap topology if the pullbacks of generators at image objects cover.
No fullness or faithfulness assumption on `F` is required. -/
theorem functorPullback_mem_toGrothendieck_comap_of_refine_generators
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      (Sieve.generate R).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X)
    {Y : D} {T : Sieve Y} (hT : T ∈ K.toGrothendieck Y) (X : C) (f : F.obj X ⟶ Y) :
    (T.pullback f).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X := by
  rw [Coverage.mem_toGrothendieck] at hT
  induction hT generalizing X with
  | of Y R hR =>
    obtain ⟨P, hP, hf⟩ := K.pullback f R hR
    apply GrothendieckTopology.superset_covering _ ?_ (refineGen hP)
    apply Sieve.functorPullback_monotone
    rw [Sieve.generate_le_iff]
    exact fun Z g hg ↦ hf hg
  | top Y => simp
  | transitive Y R T _ _ ihR ihT =>
    apply GrothendieckTopology.transitive _ (ihR X f)
    intro W g hg
    rw [← Sieve.functorPullback_pullback, ← Sieve.pullback_comp]
    simpa using ihT (by simpa [Sieve.pullback_apply] using hg) W (𝟙 _)

/-- A functor is locally cover dense for the topology generated by a coverage if the pullback
of each generator at an image object has covering pushforward. -/
theorem locallyCoverDense_of_refine_generators
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ((Sieve.generate R).functorPullback F).functorPushforward F ∈
        K.toGrothendieck (F.obj X)) :
    F.LocallyCoverDense K.toGrothendieck where
  functorPushforward_functorPullback_mem X T := by
    suffices ∀ {Y : D} {T : Sieve Y}, T ∈ K.toGrothendieck Y → ∀ (X : C) (f : F.obj X ⟶ Y),
        ((T.pullback f).functorPullback F).functorPushforward F ∈
          K.toGrothendieck (F.obj X) by
      simpa using this T.property X (𝟙 _)
    intro Y T hT X f
    rw [Coverage.mem_toGrothendieck] at hT
    induction hT generalizing X with
    | of Y R hR =>
      obtain ⟨P, hP, hf⟩ := K.pullback f R hR
      apply GrothendieckTopology.superset_covering _ ?_ (refineGen hP)
      apply Sieve.functorPushforward_monotone
      apply Sieve.functorPullback_monotone
      rw [Sieve.generate_le_iff]
      exact fun Z g hg ↦ hf hg
    | top Y => simp
    | transitive Y R T _ _ ihR ihT =>
      apply K.toGrothendieck.functorPushforward_transitive F (ihR X f)
      intro W g hg
      rw [← Sieve.functorPullback_pullback, ← Sieve.pullback_comp]
      simpa using ihT (by simpa [Sieve.pullback_apply] using hg) W (𝟙 _)

/-- Generating a topology from the comap precoverage agrees with restricting the topology
generated by the ambient coverage if the pullback of each generator at an image object covers
for the generated comap topology. Neither local cover density nor covering of the pushforwards
of these pullbacks is required. -/
theorem toGrothendieck_comap_eq_restrictedTopology_of_refine_generators [F.Full] [F.Faithful]
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      (Sieve.generate R).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X) :
    (K.toPrecoverage.comap F).toGrothendieck = F.restrictedTopology K.toGrothendieck := by
  refine le_antisymm ?_ ?_
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact Precoverage.toGrothendieck_comap_le_restrictedTopology K.toPrecoverage
  · rw [Functor.restrictedTopology, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    rw [Precoverage.mem_comap_iff] at hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff] at hR ⊢
    rw [Sieve.generate_map_eq_functorPushforward] at hR
    simpa [Sieve.functorPullback_functorPushforward_eq] using
      K.functorPullback_mem_toGrothendieck_comap_of_refine_generators F refineGen hR X (𝟙 _)

/-- For a fully faithful functor, a sieve covers in the topology generated by the comap
precoverage exactly when its pushforward covers in the topology generated by the ambient
coverage, if pullbacks of generators cover in the generated comap topology and their
pushforwards cover in the ambient topology. -/
theorem mem_toGrothendieck_comap_iff_of_refine_generators [F.Full] [F.Faithful]
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      (Sieve.generate R).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X)
    (pushforwardGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ((Sieve.generate R).functorPullback F).functorPushforward F ∈
        K.toGrothendieck (F.obj X))
    {X : C} {S : Sieve X} :
    S ∈ (K.toPrecoverage.comap F).toGrothendieck X ↔
      S.functorPushforward F ∈ K.toGrothendieck (F.obj X) := by
  have := K.locallyCoverDense_of_refine_generators F pushforwardGen
  rw [K.toGrothendieck_comap_eq_restrictedTopology_of_refine_generators F refineGen]
  exact Functor.mem_restrictedTopology_iff

end CategoryTheory.Coverage
