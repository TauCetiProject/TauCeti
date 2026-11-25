/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

import TauCeti.CategoryTheory.Sites.Coverage
import TauCeti.CategoryTheory.Sites.CoverPreserving

/-!
# Restricting a generated Grothendieck topology

Let `K` be a coverage on the ambient category `D` and `F : C ⥤ D` a functor.
The refinement membership criterion itself only needs a precoverage.
Two independent conditions on generators at objects in the image of `F` suffice for
comparison with the generated comap topology. Covering of their pullbacks in the generated
comap topology gives equality with the restricted topology for fully faithful `F`.
Covering of their pullbacks' pushforwards in the ambient topology gives local cover density.
Together these conditions give cover detection by pushforward.

The comap `K.toPrecoverage.comap F` is a precoverage. The comparison concerns generated
Grothendieck topologies: `K` need not be stable under composition, and the comap precoverage
need not itself be a coverage. When every ambient generator at an image object has a refining
comap generator, `Coverage.comapOfRefineGenerators` supplies a coverage with this precoverage.

The comparison and local cover density criteria extend Mathlib's
`Precoverage.toGrothendieck_comap_eq_restrictedTopology` and
`Precoverage.locallyCoverDense_of_map_functorPullback_mem`, respectively. Both Mathlib theorems
assume stability under composition.

## Main results

* `Coverage.comapOfRefineGenerators`: the comap coverage under generator refinements.
* `Precoverage.functorPullback_mem_and_functorPushforward_mem_of_refinement`: a comap generator
  refining an ambient sieve gives covering pullback and pushforward.
* `Coverage.functorPullback_mem_toGrothendieck_comap_of_functorPullback_mem`: a pulled-back
  ambient cover is covering for the generated comap topology.
* `Coverage.locallyCoverDense_of_functorPushforward_functorPullback_mem`: covering pushforwards
  of pulled-back generators imply local cover density for the generated topology.
* `Coverage.toGrothendieck_comap_eq_restrictedTopology_of_functorPullback_mem`: covering
  pullbacks of generators give the comparison with the restricted topology.

The theorem
`mem_toGrothendieck_comap_iff_of_functorPullback_mem_of_functorPushforward_functorPullback_mem`
gives the resulting cover detection criterion by pushforward of sieves.
-/

public section

namespace CategoryTheory.Precoverage

variable {C D : Type*} [Category* C] [Category* D] (K : Precoverage D) (F : C ⥤ D)

/-- A comap generator refining an ambient sieve makes its functor pullback covering in the
comap topology and the pushforward of that pullback covering in the ambient topology.
No fullness or faithfulness assumption on the functor is required. -/
theorem functorPullback_mem_and_functorPushforward_mem_of_refinement
    {X : C} {Q : Presieve X} {T : Sieve (F.obj X)}
    (hQ : Q ∈ (K.comap F) X) (hle : Q.map F ≤ T.arrows) :
    T.functorPullback F ∈ (K.comap F).toGrothendieck X ∧
      (T.functorPullback F).functorPushforward F ∈ K.toGrothendieck (F.obj X) := by
  have hle' : Sieve.generate Q ≤ T.functorPullback F := by
    rw [Sieve.generate_le_iff]
    exact Presieve.map_le_iff_le_functorPullback.mp hle
  refine ⟨GrothendieckTopology.superset_covering _ hle'
    (Precoverage.generate_mem_toGrothendieck hQ), ?_⟩
  apply GrothendieckTopology.superset_covering _ (Sieve.functorPushforward_monotone F X hle')
  rw [← Sieve.generate_map_eq_functorPushforward]
  exact Precoverage.generate_mem_toGrothendieck hQ

end CategoryTheory.Precoverage

namespace CategoryTheory.Coverage

variable {C D : Type*} [Category* C] [Category* D] (K : Coverage D) (F : C ⥤ D)

/-- Refinements of ambient generators at image objects also refine their pullbacks along
arbitrary arrows from image objects. -/
theorem exists_map_le_pullback_of_refine_generators
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ∃ Q ∈ (K.toPrecoverage.comap F) X, Q.map F ≤ (Sieve.generate R).arrows)
    {Y : D} {R : Presieve Y} (hR : R ∈ K Y) (X : C) (f : F.obj X ⟶ Y) :
    ∃ Q ∈ (K.toPrecoverage.comap F) X,
      Q.map F ≤ ((Sieve.generate R).pullback f).arrows := by
  obtain ⟨P, hP, hle⟩ := exists_generate_le_pullback K hR f
  obtain ⟨Q, hQ, hQle⟩ := refineGen hP
  exact ⟨Q, hQ, hQle.trans hle⟩

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
      K.exists_map_le_pullback_of_refine_generators F refineGen hR Y (F.map f)
    refine ⟨Q, hQ, ?_⟩
    intro Z g hg
    have hgf := hle _ _ (Presieve.map_map hg)
    rw [Sieve.pullback_apply, ← F.map_comp, Sieve.generate_map_eq_functorPushforward] at hgf
    rw [← Presieve.functorPullback_mem F ((Sieve.generate R).functorPushforward F).arrows
      (g ≫ f), ← Sieve.functorPullback_apply,
      Sieve.functorPullback_functorPushforward_eq] at hgf
    exact hgf

/-- The restricted coverage has exactly the comap's generating presieves. -/
@[simp]
theorem comapOfRefineGenerators_toPrecoverage [F.Full] [F.Faithful]
    (refineGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ∃ Q ∈ (K.toPrecoverage.comap F) X, Q.map F ≤ (Sieve.generate R).arrows) :
    (K.comapOfRefineGenerators F refineGen).toPrecoverage = K.toPrecoverage.comap F := by
  rfl

/-- Propagate a predicate on pulled-back sieves from coverage generators using its
monotonicity, top, and transitivity laws. -/
private lemma functorPullback_property_of_generators
    (P : ∀ X : C, Sieve X → Prop)
    (mono : ∀ {X : C} {R T : Sieve X}, R ≤ T → P X R → P X T)
    (top : ∀ X, P X ⊤)
    (trans : ∀ {X : C} {R T : Sieve X}, P X R →
      (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → P Y (T.pullback f)) → P X T)
    (gen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      P X ((Sieve.generate R).functorPullback F))
    {Y : D} {T : Sieve Y} (hT : T ∈ K.toGrothendieck Y) (X : C) (f : F.obj X ⟶ Y) :
    P X ((T.pullback f).functorPullback F) := by
  rw [Coverage.mem_toGrothendieck] at hT
  induction hT generalizing X with
  | of Y R hR =>
    obtain ⟨Q, hQ, hle⟩ := K.exists_generate_le_pullback hR f
    exact mono (Sieve.functorPullback_monotone _ _ hle) (gen hQ)
  | top Y => simpa only [Sieve.pullback_top, Sieve.functorPullback_top] using top X
  | transitive Y R T _ _ ihR ihT =>
    apply trans (ihR X f)
    intro W g hg
    have hg' : R (F.map g ≫ f) := by
      simpa only [Sieve.functorPullback_apply, Presieve.functorPullback_mem,
        Sieve.pullback_apply] using hg
    rw [← Sieve.functorPullback_pullback, ← Sieve.pullback_comp]
    simpa only [Sieve.pullback_id] using ihT hg' W (𝟙 _)

/-- An ambient covering sieve pulled back along an arrow from `F.obj X` and then along `F`
covers for the generated comap topology if the pullbacks of generators at image objects cover.
No fullness or faithfulness assumption on `F` is required. -/
theorem functorPullback_mem_toGrothendieck_comap_of_functorPullback_mem
    (pullbackGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      (Sieve.generate R).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X)
    {Y : D} {T : Sieve Y} (hT : T ∈ K.toGrothendieck Y) (X : C) (f : F.obj X ⟶ Y) :
    (T.pullback f).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X := by
  let J := (K.toPrecoverage.comap F).toGrothendieck
  exact functorPullback_property_of_generators K F (fun X R ↦ R ∈ J X)
    (fun h hR ↦ J.superset_covering h hR) J.top_mem
    (fun hR hT ↦ J.transitive hR _ hT) pullbackGen hT X f

/-- A functor is locally cover dense for the topology generated by a coverage if the pullback
of each generator at an image object has covering pushforward. -/
theorem locallyCoverDense_of_functorPushforward_functorPullback_mem
    (pushforwardGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ((Sieve.generate R).functorPullback F).functorPushforward F ∈
        K.toGrothendieck (F.obj X)) :
    F.LocallyCoverDense K.toGrothendieck where
  functorPushforward_functorPullback_mem X T := by
    have h := functorPullback_property_of_generators K F
      (fun X R ↦ R.functorPushforward F ∈ K.toGrothendieck (F.obj X))
      (fun h hR ↦ K.toGrothendieck.superset_covering
        (Sieve.functorPushforward_monotone _ _ h) hR)
      (fun X ↦ by simp only [Sieve.functorPushforward_top]; exact K.toGrothendieck.top_mem _)
      (fun hR hT ↦ K.toGrothendieck.functorPushforward_transitive F hR hT)
      pushforwardGen T.property X (𝟙 _)
    simpa only [Sieve.pullback_id] using h

/-- Generating a topology from the comap precoverage agrees with restricting the topology
generated by the ambient coverage if the pullback of each generator at an image object covers
for the generated comap topology. Neither local cover density nor covering of the pushforwards
of these pullbacks is required. -/
theorem toGrothendieck_comap_eq_restrictedTopology_of_functorPullback_mem [F.Full] [F.Faithful]
    (pullbackGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
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
      K.functorPullback_mem_toGrothendieck_comap_of_functorPullback_mem F pullbackGen hR X (𝟙 _)

/-- For a fully faithful functor, a sieve covers in the topology generated by the comap
precoverage exactly when its pushforward covers in the topology generated by the ambient
coverage, if pullbacks of generators cover in the generated comap topology and their
pushforwards cover in the ambient topology. -/
lemma mem_toGrothendieck_comap_iff_of_functorPullback_mem_of_functorPushforward_functorPullback_mem
    [F.Full] [F.Faithful]
    (pullbackGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      (Sieve.generate R).functorPullback F ∈ (K.toPrecoverage.comap F).toGrothendieck X)
    (pushforwardGen : ∀ {X : C} {R : Presieve (F.obj X)}, R ∈ K (F.obj X) →
      ((Sieve.generate R).functorPullback F).functorPushforward F ∈
        K.toGrothendieck (F.obj X))
    {X : C} {S : Sieve X} :
    S ∈ (K.toPrecoverage.comap F).toGrothendieck X ↔
      S.functorPushforward F ∈ K.toGrothendieck (F.obj X) := by
  have := K.locallyCoverDense_of_functorPushforward_functorPullback_mem F pushforwardGen
  rw [K.toGrothendieck_comap_eq_restrictedTopology_of_functorPullback_mem F pullbackGen]
  exact Functor.mem_restrictedTopology_iff

end CategoryTheory.Coverage
