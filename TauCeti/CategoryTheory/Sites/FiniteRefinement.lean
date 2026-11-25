/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.Basic.Finite.Sigma

/-!
# Finite refinements in a generated topology

Finite covering refinements whose sources belong to a specified class of objects propagate
from the generators of a coverage to every sieve in its generated Grothendieck topology.
-/

public section

universe w

namespace CategoryTheory.Coverage

variable {C : Type*} [Category* C]

/-- If generators over objects in `P` admit finite covering refinements with sources in `P`,
then every covering sieve over an object in `P` admits such a refinement. The index universe
of the finite families can be chosen independently of the category's universes. -/
theorem exists_finite_refinement_of_mem_toGrothendieck (K : Coverage C) (P : C → Prop)
    (refineGen : ∀ {X : C} {R : Presieve X}, R ∈ K X → P X →
      ∃ (ι : Type w) (_ : Finite ι) (Y : ι → C) (f : ∀ i, Y i ⟶ X),
        (∀ i, P (Y i)) ∧ (∀ i, Sieve.generate R (f i)) ∧
          Sieve.ofArrows Y f ∈ K.toGrothendieck X)
    {X : C} {R : Sieve X} (hR : R ∈ K.toGrothendieck X) (hX : P X) :
    ∃ (ι : Type w) (_ : Finite ι) (Y : ι → C) (f : ∀ i, Y i ⟶ X),
      (∀ i, P (Y i)) ∧ (∀ i, R (f i)) ∧ Sieve.ofArrows Y f ∈ K.toGrothendieck X := by
  classical
  rw [Coverage.mem_toGrothendieck] at hR
  induction hR with
  | of X R hR => exact refineGen hR hX
  | top X =>
    refine ⟨PUnit, inferInstance, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ hX,
      fun _ ↦ trivial, ?_⟩
    simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit,
      Sieve.generate_of_singleton_isSplitEpi] using K.toGrothendieck.top_mem X
  | transitive X R S _ _ ihR ihS =>
    obtain ⟨ι, hι, Y, f, hY, hf, hfcov⟩ := ihR hX
    choose σ hσ Z g hZ hg hgcov using fun i ↦ ihS (hf i) (hY i)
    let : ∀ i, Finite (σ i) := hσ
    refine ⟨Σ i, σ i, inferInstance, fun p ↦ Z p.1 p.2,
      fun p ↦ g p.1 p.2 ≫ f p.1, fun p ↦ hZ p.1 p.2, fun p ↦ hg p.1 p.2, ?_⟩
    rw [Sieve.ofArrows, ← Presieve.bindOfArrows_ofArrows]
    exact K.toGrothendieck.bindOfArrows hfcov hgcov

end CategoryTheory.Coverage
