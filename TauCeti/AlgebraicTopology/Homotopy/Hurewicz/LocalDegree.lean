/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Hurewicz classes of spheres detected by a fibre

A generalized loop `p : Iⁿ⁺² → Sⁿ⁺²` of a sphere has a Hurewicz class generating the top integral
homology `Hₙ₊₂(Sⁿ⁺²; ℤ)` as soon as its pointed map `GenLoop.toSphere p : Sⁿ⁺² → Sⁿ⁺²` covers some
nonempty open set `V` bijectively, that is, every point of `V` has exactly one preimage
(`GenLoop.isIso_hurewicz_of_bijOn_toSphere`). Away from `V` the loop may fold and overlap
arbitrarily.

This extends `GenLoop.isIso_hurewicz_of_bijective_toSphere`, where `V` is the whole sphere, to the
cubes met in practice when loops are concatenated or transported along paths: their pieces retrace
arcs and cover only part of the sphere once. The proof reads the degree of the pointed map at a
point of `V`. A continuous map of compact Hausdorff spaces is closed, so it restricts to a
homeomorphism from the preimage of `V` onto `V` (`IsClosedMap.isLocalHomeomorphOn_preimage`); the
local index at the single preimage of a point of `V` is therefore `±1`, and so is the degree. A
self-map of the sphere of degree `±1` induces an isomorphism on top homology, and the Hurewicz
class of `p` is the image under it of the class of the tautological loop
(`GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp`), which generates.

The sphere has dimension at least two, so that it is simply connected and the orientations needed
for the degree exist without further hypotheses.

## Main results

* `GenLoop.isIso_hurewicz_of_bijOn_toSphere`: a generalized loop of `Sⁿ⁺²` that covers a nonempty
  open set bijectively has a Hurewicz class generating `Hₙ₊₂(Sⁿ⁺²; ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Proposition 2.30 (the degree of a map of spheres as a sum of local degrees), and
  Section 4.2 (the Hurewicz map).
-/

public section

open CategoryTheory Metric Module TauCeti
open scoped Topology.Homotopy

namespace GenLoop

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **A generalized loop of a sphere covering an open set once has a generating Hurewicz class.**
Let `E` have dimension `n + 3`, and let `p` be a generalized loop of the unit sphere `Sⁿ⁺²` of `E`.
If the pointed map `GenLoop.toSphere p` sends the preimage of a nonempty open set `V` bijectively
onto `V`, then the integral Hurewicz class of `p` is an isomorphism `ℤ ≅ Hₙ₊₂(Sⁿ⁺²; ℤ)`. -/
theorem isIso_hurewicz_of_bijOn_toSphere (hE : finrank ℝ E = n + 3) {x : sphere (0 : E) 1}
    (p : Ω^ (Fin (n + 2)) (sphere (0 : E) 1) x) {V : Set (sphere (0 : E) 1)} (hV : IsOpen V)
    (hVne : V.Nonempty) (hp : Set.BijOn (toSphere p) (toSphere p ⁻¹' V) V) :
    IsIso (hurewicz (ModuleCat.of ℤ ℤ) p) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have : Fact (finrank ℝ E = n + 2 + 1) := ⟨hE⟩
  have hrank : 2 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, hE]
    exact_mod_cast (by omega : 2 < n + 3)
  -- Both spheres are simply connected, hence connected and orientable.
  have : SimplyConnectedSpace (sphere (0 : E) 1) := simplyConnectedSpace_sphere hrank 0 zero_le_one
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1) :=
    simplyConnectedSpace_sphere_euclideanSpace (by omega)
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1) (E := EuclideanSpace ℝ (Fin (n + 2)))
    finrank_euclideanSpace_fin
  obtain ⟨o'⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := sphere (0 : E) 1) (E := EuclideanSpace ℝ (Fin (n + 2))) finrank_euclideanSpace_fin
  -- A point of `V` has a single preimage, near which `toSphere p` is a local homeomorphism.
  set f := toSphere p
  obtain ⟨y, hy⟩ := hVne
  obtain ⟨s, hs, rfl⟩ := hp.surjOn hy
  have hfib : f ⁻¹' {f s} = {s} := by
    ext t
    refine ⟨fun ht ↦ hp.injOn (show f t ∈ V from (Set.mem_singleton_iff.1 ht).symm ▸ hy) hs
      (Set.mem_singleton_iff.1 ht), ?_⟩
    rintro rfl
    rfl
  have hloc := IsClosedMap.isLocalHomeomorphOn_preimage f.continuous f.continuous.isClosedMap hV hp
  -- So `f` has degree `±1`, and is an isomorphism on top homology.
  have hbij := (o.bijective_singularHomologyMap_iff o' finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin f).2 (o.degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn o'
      finrank_euclideanSpace_fin finrank_euclideanSpace_fin f.continuous.isProperMap hfib hloc hs)
  have : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  rw [hurewicz_eq_hurewicz_sphereGenLoop_comp]
  infer_instance

end GenLoop
