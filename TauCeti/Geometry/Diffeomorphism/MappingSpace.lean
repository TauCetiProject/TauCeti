/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Homogeneity
public import TauCeti.Geometry.Diffeomorphism.LocalSection
public import TauCeti.Topology.MappingSpace.Action

/-!
# Evaluation on mapping spaces into a closed manifold

Let `M` be a compact connected boundaryless `C^m` manifold modelled on a finite-dimensional
space, `1 ≤ m`, and let `(B, b₀)` be any pointed space. The group `Diff(M)` of
`C^m` self-diffeomorphisms acts transitively on `M`, and evaluation `Diff(M) → M` at a point
`x₀` has continuous local sections around every point
(`TauCeti.exists_continuousOn_diffeomorph_apply_eq_of_mem_orbit`). Translating maps by these
local sections trivializes evaluation

`Map_*(B, M) → Map(B, M) → M`

at `b₀` around every point of `M`, with fibre the based mapping space of maps sending `b₀` to
`x₀` (`TauCeti.exists_trivialization_mappingSpaceEval_of_preconnectedSpace`, through
`TauCeti.mappingSpaceEvalTrivialization`). So evaluation is a Serre fibration
(`TauCeti.mappingSpaceEval_mem_serreFibrations_of_preconnectedSpace`). Unlike the
restriction fibrations of `TauCeti.Topology.MappingSpace.Fibration`, this needs neither local
compactness of `B` nor that `b₀` be a cofibrant point.

In the charts `TauCeti.mappingSpaceEvalTrivialization` built from such a local section `s`, the
action map `Diff(M) × Map_*(B, M) → Map(B, M)`, `(φ, u) ↦ φ ∘ u` (`TauCeti.BasedMap.actionMap`),
is the action of the stabilizer of `x₀` on the fibre, read in the chart
`TauCeti.orbitMapTrivialization` of `Diff(M) → M` given by `s`
(`TauCeti.mappingSpaceEvalTrivialization_actionMap`). For `B = S²` this is the map of
fibrations along which classes of `Diff(M)` are compared with classes of `Map(S², M)`.

## Main results

* `TauCeti.exists_trivialization_mappingSpaceEval_of_preconnectedSpace`: evaluation
  `Map(B, M) → M` is locally trivial, with fibre `Map_*(B, M)`.
* `TauCeti.mappingSpaceEval_mem_serreFibrations_of_preconnectedSpace`: evaluation
  `Map(B, M) → M` is a Serre fibration.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, proof of Proposition 6.29.
* R. Palais, *Local triviality of the restriction map for embeddings*, Comment. Math. Helv. 34
  (1960), 305–312.
-/

public section

open Set MulAction
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

universe u

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] {m : ℕ∞} [CompactSpace M] [IsManifold I m M]
  [PreconnectedSpace M]

variable (I) in
include I in
/-- **Evaluation on maps into a closed connected manifold is locally trivial.** Let `M` be a
compact connected boundaryless `C^m` manifold modelled on a finite-dimensional space, `1 ≤ m`. For
every pointed space `(B, b₀)` and every `x₀ : M`, evaluation `Map(B, M) → M` at `b₀` has, around
every point of `M`, a trivialization with fibre the space `Map_*(B, M)` of maps sending `b₀` to
`x₀`. -/
theorem exists_trivialization_mappingSpaceEval_of_preconnectedSpace (hm : 1 ≤ m) {B : Type*}
    [TopologicalSpace B] (b₀ : B) (x₀ z : M) :
    ∃ e : Bundle.Trivialization (BasedMap B M b₀ x₀) (mappingSpaceEval (X := M) b₀),
      z ∈ e.baseSet :=
  -- Evaluation `φ ↦ φ x₀` is the orbit map `φ ↦ φ • x₀` by definition (`Diffeomorph.smul_def`).
  exists_trivialization_mappingSpaceEval b₀ x₀ (fun y ↦
    exists_continuousOn_diffeomorph_apply_eq_of_mem_orbit (I := I) hm
      (by rw [orbit_diffeomorph_eq_univ hm]; exact mem_univ y)) z

variable (I) in
include I in
/-- **Evaluation on maps into a closed connected manifold is a Serre fibration.** Let `M` be a
compact connected boundaryless `C^m` manifold modelled on a finite-dimensional space, `1 ≤ m`.
For every pointed space `(B, b₀)`, evaluation `Map(B, M) → M` at `b₀` is a Serre fibration. -/
theorem mappingSpaceEval_mem_serreFibrations_of_preconnectedSpace [Nonempty M] (hm : 1 ≤ m)
    {B : Type u} [TopologicalSpace B] (b₀ : B) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom (mappingSpaceEval b₀) :
        _root_.TopCat.of C(B, M) ⟶ _root_.TopCat.of M) :=
  -- Evaluation `φ ↦ φ x₀` is the orbit map `φ ↦ φ • x₀` by definition (`Diffeomorph.smul_def`).
  mappingSpaceEval_mem_serreFibrations b₀ (Classical.arbitrary M) fun y ↦
    exists_continuousOn_diffeomorph_apply_eq_of_mem_orbit (I := I) hm
      (by rw [orbit_diffeomorph_eq_univ hm]; exact mem_univ y)

end TauCeti
