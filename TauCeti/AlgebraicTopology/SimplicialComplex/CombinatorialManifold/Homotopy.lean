/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Realization
public import TauCeti.AlgebraicTopology.Sphere.Contractible
import Mathlib.Analysis.Convex.Contractible

/-!
# Distinguishing combinatorial balls and spheres

The weak polyhedron of a combinatorial ball is contractible, whereas that of a combinatorial
sphere is not. Consequently a complex cannot be both a combinatorial ball and a combinatorial
sphere, even if the two asserted dimensions differ. This makes the ball-versus-sphere choice
in a manifold's vertex-link condition unambiguous.

The statements use the actual subpolyhedron in an arbitrary ambient weak realization.
Unused ambient vertices have no effect, and the ambient vertex type need not be finite.
The topological models are supplied by `IsCombinatorialBall.nonempty_homeomorph_closedBall`
and `IsCombinatorialSphere.nonempty_homeomorph_sphere`. Distinguishing spheres from balls also
allows combinatorial spheres and manifolds to be reflected along injective vertex maps
(`IsCombinatorialSphere.of_map` and `IsCombinatorialManifold.of_map`), complementing
`CombinatorialManifold.Map`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (combinatorial balls, spheres, and vertex links).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {P : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {n m : ℕ}

/-- The weak polyhedron of a combinatorial ball is contractible in any ambient realization
containing the complex. This includes the one-point zero-ball. -/
theorem IsCombinatorialBall.contractibleSpace (h : IsCombinatorialBall P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    ContractibleSpace {x : Realization A // x.1.support ∈ P} := by
  obtain ⟨e⟩ := h.nonempty_homeomorph_closedBall hA
  let := Metric.contractibleSpace_closedBall
    (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1) zero_le_one
  exact e.contractibleSpace

/-- The weak polyhedron of a combinatorial sphere is not contractible, including the
two-point zero-sphere. -/
theorem IsCombinatorialSphere.not_contractibleSpace (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    ¬ ContractibleSpace {x : Realization A // x.1.support ∈ P} := by
  obtain ⟨e⟩ := h.nonempty_homeomorph_sphere hA
  intro hc
  let := hc
  exact TauCeti.not_contractibleSpace_sphere e.symm.contractibleSpace

/-- A combinatorial sphere cannot be a combinatorial ball of any dimension. In particular,
the spherical and ball cases of the vertex-link condition are mutually exclusive. -/
theorem IsCombinatorialSphere.not_isCombinatorialBall (h : IsCombinatorialSphere P n) :
    ¬ IsCombinatorialBall P m := by
  intro hb
  exact h.not_contractibleSpace (A := ⊤) (le_top P)
    (hb.contractibleSpace (A := ⊤) (le_top P))

/-! ### Reflecting spheres and manifolds along injective vertex maps -/

/-- An injective vertex map reflects combinatorial spheres. -/
theorem IsCombinatorialSphere.of_map {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (h : IsCombinatorialSphere (P.map f) n) :
    IsCombinatorialSphere P n := by
  obtain ⟨W, hW, he⟩ := isCombinatorialSphere_iff.mp h
  have hfin : P.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  let U : Finset ι := faceUnion hfin
  obtain ⟨τ₀, hτ₀, hτ₀card⟩ := exists_face_card_eq_of_dimension_eq h.dimension_eq
  obtain ⟨σ₀, hσ₀, rfl⟩ := mem_map_iff.mp hτ₀
  have hσ₀card : σ₀.card = n + 1 := by
    rwa [Finset.card_image_of_injective σ₀ hf] at hτ₀card
  have hσ₀U : σ₀ ⊆ U := subset_faceUnion hfin hσ₀
  have hUcard : n + 2 ≤ U.card := by
    by_contra hlt
    have hle : U.card ≤ σ₀.card := by omega
    have hUeq : σ₀ = U := Finset.eq_of_subset_of_card_le hσ₀U hle
    have hPeq : P = simplex U := by
      refine SetLike.ext fun ρ => ⟨fun hρ => mem_simplex.mpr ⟨(P.isRelLowerSet_faces hρ).1,
        subset_faceUnion hfin hρ⟩, fun hρ => ?_⟩
      obtain ⟨hne, hρU⟩ := mem_simplex.mp hρ
      exact (P.isRelLowerSet_faces (hUeq ▸ hσ₀)).2 hρU hne
    have hball : IsCombinatorialBall (P.map f) n := by
      rw [hPeq]
      exact (isCombinatorialBall_simplex (hUeq ▸ hσ₀card)).map f hf
    exact h.not_isCombinatorialBall hball
  obtain ⟨V, -, hVcard⟩ := Finset.exists_subset_card_eq hUcard
  refine isCombinatorialSphere_iff.mpr ⟨V, hVcard, ?_⟩
  apply StellarEquivalentUpToRelabeling.of_map hfin f hf
  have hmap : (simplexBoundary V).map f = simplexBoundary (V.image f) := by
    simpa only [Function.Embedding.coeFn_mk] using map_simplexBoundary V ⟨f, hf⟩
  rw [hmap]
  have hVfcard : (V.image f).card = n + 2 := by
    rw [Finset.card_image_of_injective V hf, hVcard]
  exact he.trans (stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq
    (hW.trans hVfcard.symm))

/-- An injective vertex map preserves and reflects combinatorial spheres. -/
theorem IsCombinatorialSphere.map_iff_of_injective {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) :
    IsCombinatorialSphere (P.map f) n ↔ IsCombinatorialSphere P n :=
  ⟨IsCombinatorialSphere.of_map f hf, fun h => h.map f hf⟩

/-- An injective vertex map reflects combinatorial manifolds. -/
theorem IsCombinatorialManifold.of_map {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (h : IsCombinatorialManifold (P.map f) n) :
    IsCombinatorialManifold P n := by
  cases n with
  | zero =>
      refine isCombinatorialManifold_zero_iff.mpr fun v hv => ?_
      have hfv : ({f v} : Finset κ) ∈ P.map f := singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩
      have hbot := isCombinatorialManifold_zero_iff.mp h hfv
      rw [← Finset.image_singleton f v, ← map_link f hf, map_eq_bot_iff] at hbot
      exact hbot
  | succ n =>
      refine isCombinatorialManifold_succ_iff.mpr fun v hv => ?_
      have hfv : ({f v} : Finset κ) ∈ P.map f := singleton_mem_map_iff.mpr ⟨v, hv, rfl⟩
      have hlink := isCombinatorialManifold_succ_iff.mp h hfv
      rw [← Finset.image_singleton f v, ← map_link f hf] at hlink
      exact hlink.imp (IsCombinatorialSphere.of_map f hf) (IsCombinatorialBall.of_map f hf)

/-- An injective vertex map preserves and reflects combinatorial manifolds. -/
theorem IsCombinatorialManifold.map_iff_of_injective {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) :
    IsCombinatorialManifold (P.map f) n ↔ IsCombinatorialManifold P n :=
  ⟨IsCombinatorialManifold.of_map f hf, fun h => h.map f hf⟩

end PreAbstractSimplicialComplex
