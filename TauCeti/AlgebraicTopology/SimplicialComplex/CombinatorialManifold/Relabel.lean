/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Homotopy
import TauCeti.Data.Finset.Card

/-!
# Reflecting spheres and manifolds along injective vertex maps

An injective map of ambient vertex types not only preserves combinatorial balls, spheres, and
manifolds (`CombinatorialManifold.Map`) and reflects combinatorial balls, it also reflects
combinatorial spheres and therefore reflects combinatorial manifolds. This lets local models
computed after injective vertex tagging — such as closed stars and closed-star boundaries expressed
as joins on `ι ⊕ ι` — be transferred back to the original complex on `ι` without assuming extra
unused ambient vertices in `ι`.

Reflecting a combinatorial `n`-sphere `K.map f` back to `K` requires finding an `(n + 2)`-element
model vertex set in `ι`: `K` has an `(n + 1)`-element face from its dimension, and cannot be
contained in that single simplex because otherwise `K.map f` would be a combinatorial `n`-ball,
contradicting `IsCombinatorialSphere.not_isCombinatorialBall`. Once such a witness set is chosen in
`ι`, `StellarEquivalentUpToRelabeling.of_map` compresses the stellar comparison from `κ ⊕ ℕ` back to
`ι ⊕ ℕ`.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialSphere.of_map` and
  `PreAbstractSimplicialComplex.isCombinatorialSphere_map_iff`: injective vertex maps reflect
  combinatorial spheres.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.of_map` and
  `PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff`: injective vertex maps reflect
  combinatorial manifolds.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : PreAbstractSimplicialComplex ι} {n : ℕ}

/-- An injective vertex map reflects combinatorial spheres. -/
theorem IsCombinatorialSphere.of_map (f : ι → κ) (hf : Function.Injective f)
    (h : IsCombinatorialSphere (K.map f) n) : IsCombinatorialSphere K n := by
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  have hdim : dimension K = (n : WithBot ℕ∞) := by
    rw [← dimension_map_of_injective f hf, h.dimension_eq]
  obtain ⟨τ, hτ, hτcard⟩ := exists_face_card_eq_of_dimension_eq hdim
  have hnot_le : ¬ K ≤ simplex τ := by
    intro hle
    have hKeq : K = simplex τ := le_antisymm hle (simplex_le_iff.mpr fun _ => hτ)
    have hball : IsCombinatorialBall (K.map f) n := by
      rw [hKeq, map_simplex]
      exact isCombinatorialBall_simplex (by rw [card_image_of_injective τ hf, hτcard])
    exact h.not_isCombinatorialBall hball
  have hex : ∃ u, ({u} : Finset ι) ∈ K ∧ u ∉ τ := by
    by_contra! hall
    exact hnot_le fun σ hσ => mem_simplex.mpr ⟨(K.isRelLowerSet_faces hσ).1,
      fun u hu => hall u (singleton_mem_of_mem hσ hu)⟩
  obtain ⟨u, -, huτ⟩ := hex
  let V : Finset ι := insert u τ
  have hVcard : V.card = n + 2 := by rw [card_insert_of_notMem huτ, hτcard]
  obtain ⟨W, hWcard, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨g, hg, hVimg⟩ := Finset.exists_injective_image_eq hf (hVcard.trans hWcard.symm)
  have hmap : (simplexBoundary V).map g = simplexBoundary W := by
    simpa only [Function.Embedding.coeFn_mk, hVimg] using map_simplexBoundary V ⟨g, hg⟩
  rw [← hmap] at he
  exact isCombinatorialSphere_iff.mpr ⟨V, hVcard,
    StellarEquivalentUpToRelabeling.of_map hKfin hf hg he⟩

/-- Injective relabeling preserves and reflects combinatorial spheres. -/
@[simp]
theorem isCombinatorialSphere_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialSphere (K.map f) n ↔ IsCombinatorialSphere K n :=
  ⟨IsCombinatorialSphere.of_map f hf, fun h => h.map f hf⟩

/-- An injective vertex map reflects combinatorial manifolds. -/
theorem IsCombinatorialManifold.of_map (f : ι → κ) (hf : Function.Injective f)
    (h : IsCombinatorialManifold (K.map f) n) : IsCombinatorialManifold K n := by
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun v hv => ?_
    have hbot := isCombinatorialManifold_zero_iff.mp h (singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩)
    rwa [← image_singleton, ← map_link f hf, map_eq_bot_iff] at hbot
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun v hv => ?_
    have hlink := isCombinatorialManifold_succ_iff.mp h (singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩)
    rwa [← image_singleton, ← map_link f hf, isCombinatorialSphere_map_iff f hf,
      isCombinatorialBall_map_iff f hf] at hlink

/-- Injective relabeling preserves and reflects combinatorial manifolds. -/
@[simp]
theorem isCombinatorialManifold_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialManifold (K.map f) n ↔ IsCombinatorialManifold K n :=
  ⟨IsCombinatorialManifold.of_map f hf, fun h => h.map f hf⟩

end PreAbstractSimplicialComplex
