/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.Algebra.Homology.CochainComplex.Of

/-!
# The auxiliary universe of the homogeneous cochain complex

For a topological group `G : Type u`, Mathlib's homogeneous cochain complex
`TopRep.homogeneousCochains.{w, u, v}` and continuous cohomology `continuousCohomology.{w, u, v}`
carry a universe parameter `v` that enters only through the coefficient universe `max u v`:
they take a representation `X : TopRep.{max u v} k G`. Distinct parameters with the same
coefficient universe, such as `v = u` and `v = 0`, give distinct constants, and these are not
definitionally equal at a variable degree because the coinduced resolution `TopRep.resolutionX`
is defined by recursion on the degree.

This file shows that the parameter `v` can be replaced by `max u v`: the levels and
differentials of the coinduced resolution agree in every degree, by induction on the degree, so
the shifted resolution, the homogeneous cochain complex and continuous cohomology are equal as
objects. The specialization `v = 0` compares the parameters `0` and `u`. Invariants defined
through these objects, such as the vanishing of a cohomology group or of its `p`-primary
component, therefore do not depend on `v` beyond `max u v`.

## Main results

* `TopRep.resolutionX_universe_eq`, `TopRep.resolution_universe_eq`,
  `TopRep.resolution'_universe_eq`: the levels, the coinduced resolution and its shift do not
  depend on `v` beyond `max u v`.
* `TopRep.homogeneousCochains_universe_eq`: the same for the homogeneous cochain complex.
* `TauCeti.continuousCohomology_universe_eq`: the same for continuous cohomology in every degree.
* `TauCeti.ContinuousCohomology.π_comp_eqToHom`,
  `TauCeti.ContinuousCohomology.cochainsMap_comp_eqToHom`,
  `TauCeti.ContinuousCohomology.map_comp_eqToHom`: the comparisons preserve cocycle classes and
  commute with compatible group and coefficient maps.
-/

public section

open CategoryTheory

universe w u v

variable {k : Type w} [Ring k] [TopologicalSpace k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace TopRep

/-- In every degree, the level and the differential of the coinduced resolution at the
parameter `v` agree with those at the parameter `max u v`. Each step applies `coind₁` to the
previous level and builds the next differential from the previous one by the same formula. -/
private theorem resolution_sigma_universe_eq (X : TopRep.{max u v} k G) (n : ℕ) :
    (⟨resolutionX.{w, u, v} X n, d.{w, u, v} X n⟩ : Σ A : TopRep.{max u v} k G, A ⟶ A.coind₁) =
      ⟨resolutionX.{w, u, max u v} X n, d.{w, u, max u v} X n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- `d_succ`: the next differential is `coind₁ι - coind₁Functor.map` of the previous one.
    exact congrArg (fun s : Σ A : TopRep.{max u v} k G, A ⟶ A.coind₁ ↦
      (⟨s.1.coind₁, ofHom s.1.coind₁.ρ.coind₁ι - (coind₁Functor k G).map s.2⟩ :
        Σ A : TopRep.{max u v} k G, A ⟶ A.coind₁)) ih

/-- Each level of the coinduced resolution is unchanged when the auxiliary universe parameter
`v` is replaced by `max u v`. -/
theorem resolutionX_universe_eq (X : TopRep.{max u v} k G) (n : ℕ) :
    resolutionX.{w, u, v} X n = resolutionX.{w, u, max u v} X n :=
  congrArg Sigma.fst (resolution_sigma_universe_eq X n)

/-- The coinduced resolution at the auxiliary universe parameter `v` is the one at the
parameter `max u v`. -/
theorem resolution_universe_eq (X : TopRep.{max u v} k G) :
    resolution.{w, u, v} X = resolution.{w, u, max u v} X :=
  CochainComplex.of_congr _ _ (funext (resolutionX_universe_eq X))
    (Function.hfunext rfl fun n _ hn ↦ by
      cases hn
      exact (Sigma.ext_iff.1 (resolution_sigma_universe_eq X n)).2)

/-- The shifted coinduced resolution at the auxiliary universe parameter `v` is the one at the
parameter `max u v`. -/
theorem resolution'_universe_eq (X : TopRep.{max u v} k G) :
    resolution'.{w, u, v} X = resolution'.{w, u, max u v} X :=
  CochainComplex.of_congr _ _
    (funext fun n ↦ congrArg Sigma.fst (resolution_sigma_universe_eq X (n + 1)))
    (Function.hfunext rfl fun n _ hn ↦ by
      cases hn
      exact (Sigma.ext_iff.1 (resolution_sigma_universe_eq X (n + 1))).2)

/-- The homogeneous cochain complex at the auxiliary universe parameter `v` is the one at the
parameter `max u v`. -/
theorem homogeneousCochains_universe_eq (X : TopRep.{max u v} k G) :
    homogeneousCochains.{w, u, v} X = homogeneousCochains.{w, u, max u v} X :=
  congrArg ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution'_universe_eq X)

end TopRep

namespace TauCeti

/-- **Continuous cohomology does not depend on the auxiliary universe parameter** beyond the
coefficient universe: `continuousCohomology.{w, u, v} n X` is `continuousCohomology.{w, u, max u v}
n X` in every degree `n`. At `v = 0` this compares the parameters `0` and `u`. -/
theorem continuousCohomology_universe_eq (n : ℕ) (X : TopRep.{max u v} k G) :
    continuousCohomology.{w, u, v} n X = continuousCohomology.{w, u, max u v} n X :=
  congrArg (·.homology n) (TopRep.homogeneousCochains_universe_eq X)

namespace ContinuousCohomology

open TopRep _root_.ContinuousCohomology

/-- The cocycles at the auxiliary universe parameter `v` agree with those at `max u v`. -/
theorem cocycles_universe_eq (n : ℕ) (X : TopRep.{max u v} k G) :
    cocycles.{w, u, v} X n = cocycles.{w, u, max u v} X n :=
  congrArg (·.cycles n) (homogeneousCochains_universe_eq X)

/-- The universe comparison sends the cohomology class of a cocycle to the class of its image
under the cocycle comparison. -/
@[reassoc]
theorem π_comp_eqToHom (n : ℕ) (X : TopRep.{max u v} k G) :
    π.{w, u, v} X n ≫ eqToHom (continuousCohomology_universe_eq n X) =
      eqToHom (cocycles_universe_eq n X) ≫ π.{w, u, max u v} X n :=
  eqToHom_naturality (fun C : CochainComplex (TopModuleCat k) ℕ ↦ C.homologyπ n)
    (homogeneousCochains_universe_eq X)

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max u v} k G} {Y : TopRep.{max u v} k H}

/-- The resolution maps at the two universe parameters agree together with their source and
target levels. The successor step applies the same coinduction map to the previous map. -/
private theorem resolutionMap_sigma_universe_eq (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    (⟨(resolutionX.{w, u, v} X n, resolutionX.{w, u, v} Y n),
      resolutionMap.{w, u, v} φ f n⟩ :
      Σ AB : TopRep.{max u v} k G × TopRep.{max u v} k H, res φ AB.1 ⟶ AB.2) =
    ⟨(resolutionX.{w, u, max u v} X n, resolutionX.{w, u, max u v} Y n),
      resolutionMap.{w, u, max u v} φ f n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun s :
      Σ AB : TopRep.{max u v} k G × TopRep.{max u v} k H, res φ AB.1 ⟶ AB.2 ↦
        (⟨(s.1.1.coind₁, s.1.2.coind₁),
          ofHom (ContRepresentation.coind₁ResMap φ s.2.hom)⟩ :
          Σ AB : TopRep.{max u v} k G × TopRep.{max u v} k H, res φ AB.1 ⟶ AB.2)) ih

/-- The homogeneous cochain universe comparison is natural in compatible group and coefficient
maps. -/
@[reassoc]
theorem cochainsMap_comp_eqToHom (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    cochainsMap.{w, u, v} φ f ≫ eqToHom (homogeneousCochains_universe_eq Y) =
      eqToHom (homogeneousCochains_universe_eq X) ≫ cochainsMap.{w, u, max u v} φ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply eq_of_heq
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
  have h := congrArg (fun s :
    Σ AB : TopRep.{max u v} k G × TopRep.{max u v} k H, res φ AB.1 ⟶ AB.2 ↦
      (⟨(s.1.1.invariants, s.1.2.invariants), invariantsResMap φ s.2⟩ :
        Σ AB : TopModuleCat k × TopModuleCat k, AB.1 ⟶ AB.2))
    (resolutionMap_sigma_universe_eq φ f (n + 1))
  exact (Sigma.ext_iff.1 h).2

/-- The continuous cohomology universe comparison is natural in compatible group and
coefficient maps. -/
@[reassoc]
theorem map_comp_eqToHom (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{w, u, v} φ f n ≫
        eqToHom (continuousCohomology_universe_eq n Y) =
      eqToHom (continuousCohomology_universe_eq n X) ≫
        _root_.ContinuousCohomology.map.{w, u, max u v} φ f n := by
  have h := congrArg
    (HomologicalComplex.homologyFunctor (TopModuleCat k) (ComplexShape.up ℕ) n).map
    (cochainsMap_comp_eqToHom.{w, u, v} φ f)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map] at h
  -- Unfold the functor wrapper to identify both its object transport and its maps with homology.
  simpa only [HomologicalComplex.homologyFunctor] using h

end ContinuousCohomology

end TauCeti
