/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

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

* `TopRep.resolution'_universe_eq`: the shifted coinduced resolution does not depend on `v`
  beyond `max u v`.
* `TopRep.homogeneousCochains_universe_eq`: the same for the homogeneous cochain complex.
* `TopRep.continuousCohomology_universe_eq`: the same for continuous cohomology in every degree.
-/

public section

open CategoryTheory

namespace TopRep

universe w u v

variable {k : Type w} [Ring k] [TopologicalSpace k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

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

/-- Two complexes built by `CochainComplex.of` are equal when their objects are equal and their
differentials agree up to that equality. -/
private theorem cochainComplexOf_congr {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {Y Y' : ℕ → C} {δ : ∀ n, Y n ⟶ Y (n + 1)} {δ' : ∀ n, Y' n ⟶ Y' (n + 1)}
    (h : ∀ n, δ n ≫ δ (n + 1) = 0) (h' : ∀ n, δ' n ≫ δ' (n + 1) = 0) (hY : Y = Y')
    (hδ : HEq δ δ') : CochainComplex.of Y δ h = CochainComplex.of Y' δ' h' := by
  subst hY
  cases hδ
  rfl

/-- The shifted coinduced resolution at the auxiliary universe parameter `v` is the one at the
parameter `max u v`. -/
theorem resolution'_universe_eq (X : TopRep.{max u v} k G) :
    resolution'.{w, u, v} X = resolution'.{w, u, max u v} X :=
  cochainComplexOf_congr _ _
    (funext fun n ↦ congrArg Sigma.fst (resolution_sigma_universe_eq X (n + 1)))
    (Function.hfunext rfl fun n _ hn ↦ by
      cases hn
      exact (Sigma.ext_iff.1 (resolution_sigma_universe_eq X (n + 1))).2)

/-- The homogeneous cochain complex at the auxiliary universe parameter `v` is the one at the
parameter `max u v`. -/
theorem homogeneousCochains_universe_eq (X : TopRep.{max u v} k G) :
    homogeneousCochains.{w, u, v} X = homogeneousCochains.{w, u, max u v} X :=
  congrArg ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution'_universe_eq X)

/-- **Continuous cohomology does not depend on the auxiliary universe parameter** beyond the
coefficient universe: `continuousCohomology.{w, u, v} n X` is `continuousCohomology.{w, u, max u v}
n X` in every degree `n`. At `v = 0` this compares the parameters `0` and `u`. -/
theorem continuousCohomology_universe_eq (n : ℕ) (X : TopRep.{max u v} k G) :
    continuousCohomology.{w, u, v} n X = continuousCohomology.{w, u, max u v} n X :=
  congrArg (·.homology n) (homogeneousCochains_universe_eq X)

end TopRep
