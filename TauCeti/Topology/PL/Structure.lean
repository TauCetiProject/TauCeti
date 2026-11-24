/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CombinatoriallyTriangulable
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Compact
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.EulerCharacteristic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Topology.PL.Map

/-!
# PL structures

A **PL structure** of dimension `n` on a topological space `M` is a triangulation of `M` by a
finite combinatorial `n`-manifold: a finite vertex type `ι`, an abstract simplicial complex `K` on
`ι` in which the link of every vertex is a combinatorial sphere or ball of dimension `n - 1`
(void when `n = 0`; `PreAbstractSimplicialComplex.IsCombinatorialManifold`), and a homeomorphism
`e` from the weak realization of `K` onto `M`. For `n = 2` this is a triangulation of a compact
surface, possibly with boundary, by a finite combinatorial surface.

The homeomorphism is part of the data. Precomposing it with a self-homeomorphism of the
realization that is not piecewise linear gives a second PL structure on the same complex, and the
identity of `M` is not piecewise linear from one to the other. A map `f : M → N` is piecewise
linear for PL structures `s` on `M` and `t` on `N` (`TauCeti.PLStructure.IsPLMap`) when, read in
barycentric coordinates through `s.e` and `t.e`, it is the restriction of a map of coordinate
spaces which is piecewise linear (`TauCeti.IsPLOn`) on the coordinate image of the realization of
`s.K`. This is the reading of maps by which `PreAbstractSimplicialComplex.PLHomeomorphic` compares
complexes. It is relative to triangulations; for charted spaces with a piecewise-linear atlas the
chart-wise notion is `TauCeti.IsPLMap`.

A space with a PL structure is compact and Hausdorff, has finite CW type, and its Euler
characteristic is the alternating count of the faces of the triangulating complex. Conversely, a
compact space with a triangulation by a combinatorial `n`-manifold carries a PL structure.

## Main definitions

* `TauCeti.PLStructure M n`: a triangulation of `M` by a finite combinatorial `n`-manifold.
* `TauCeti.PLStructure.ofRealization`: the realization of a finite combinatorial manifold,
  triangulated by itself.
* `TauCeti.PLStructure.map`: transport of a PL structure along a homeomorphism.
* `TauCeti.PLStructure.IsPLMap`: piecewise-linear maps between spaces with PL structures.
* `TauCeti.PLStructure.sphere` and `TauCeti.PLStructure.closedBall`: the unit sphere `Sⁿ`
  triangulated by the boundary of the standard `(n + 1)`-simplex, and the closed unit `n`-ball
  triangulated by the standard `n`-simplex.

## Main results

* `TauCeti.PLStructure.compactSpace`, `TauCeti.PLStructure.t2Space`,
  `TauCeti.PLStructure.finiteCWType`: a space with a PL structure is compact, Hausdorff and of
  finite CW type.
* `TauCeti.PLStructure.eulerChar_eq`: its Euler characteristic is the alternating count of the
  faces of the triangulating complex.
* `TauCeti.nonempty_plStructure_iff`: a space has a PL structure of dimension `n` exactly when it
  is compact and has a triangulation by a combinatorial `n`-manifold.
* `TauCeti.PLStructure.isPLMap_id`, `TauCeti.PLStructure.IsPLMap.comp`,
  `TauCeti.PLStructure.IsPLMap.continuous`: piecewise-linear maps include the identity, compose,
  and are continuous.
* `TauCeti.PLStructure.isPLMap_map_left_iff`, `TauCeti.PLStructure.isPLMap_map_right_iff`,
  `TauCeti.PLStructure.isPLMap_map`: how piecewise linearity reads after transporting a PL
  structure, and that a homeomorphism is piecewise linear onto the structure it transports to.
* `TauCeti.PLStructure.sphere_eq_map`, `TauCeti.PLStructure.closedBall_eq_map`: the standard
  examples as transported realizations.

## References

* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Graduate Texts in Mathematics 47,
  Springer (1977), Chapters 4 and 8 (triangulations of surfaces, piecewise-linear maps).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 1–2 (piecewise-linear maps and combinatorial manifolds).
-/

public section

noncomputable section

open AbstractSimplicialComplex Set TauCeti.SetLike

namespace TauCeti

universe u v w

open Classical in
/-- A **PL structure** of dimension `n` on `M`: a triangulation of `M` by a finite combinatorial
`n`-manifold. It consists of a finite vertex type, an abstract simplicial complex on it in which
every vertex link is a combinatorial sphere or ball of dimension `n - 1` (void when `n = 0`), and
a homeomorphism from the weak realization of the complex onto `M`. The homeomorphism is part of
the data: two PL structures on the same complex differ by their comparison homeomorphism, which
need not be piecewise linear. -/
structure PLStructure (M : Type u) [TopologicalSpace M] (n : ℕ) where
  /-- The vertex type of the triangulating complex. -/
  ι : Type u
  /-- The triangulating complex has finitely many vertices. -/
  [finite_ι : Finite ι]
  /-- The triangulating complex. -/
  K : AbstractSimplicialComplex ι
  /-- The triangulating complex is a combinatorial `n`-manifold, possibly with boundary. -/
  isCombinatorialManifold : K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n
  /-- The triangulation homeomorphism. -/
  e : Realization K ≃ₜ M

namespace PLStructure

attribute [instance] finite_ι

variable {m n p : ℕ}

/-! ### Construction and transport -/

section Transport

variable {M N P : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- The realization of a finite combinatorial `n`-manifold, triangulated by itself. The body is
exposed so that the complex of the structure is the given complex by definition. -/
@[expose] def ofRealization {ι : Type u} [Finite ι] [DecidableEq ι]
    (K : AbstractSimplicialComplex ι)
    (hK : K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n) :
    PLStructure (Realization K) n where
  ι := ι
  K := K
  -- `convert` replaces the `DecidableEq ι` instance of `hK` by the classical one of the field.
  isCombinatorialManifold := by convert hK
  e := Homeomorph.refl _

@[simp]
theorem ofRealization_e {ι : Type u} [Finite ι] [DecidableEq ι] (K : AbstractSimplicialComplex ι)
    (hK : K.toPreAbstractSimplicialComplex.IsCombinatorialManifold n) :
    (ofRealization K hK).e = Homeomorph.refl (Realization K) :=
  (rfl)

/-- Transport of a PL structure along a homeomorphism `f : M ≃ₜ N`: the same complex,
triangulating `N` through the triangulation of `M` followed by `f`. The body is exposed so that
the transported structure has the same complex by definition. -/
@[expose] def map (s : PLStructure M n) (f : M ≃ₜ N) : PLStructure N n where
  ι := s.ι
  K := s.K
  isCombinatorialManifold := s.isCombinatorialManifold
  e := s.e.trans f

@[simp]
theorem map_e (s : PLStructure M n) (f : M ≃ₜ N) : (s.map f).e = s.e.trans f :=
  (rfl)

@[simp]
theorem map_refl (s : PLStructure M n) : s.map (Homeomorph.refl M) = s :=
  (rfl)

@[simp]
theorem map_map (s : PLStructure M n) (f : M ≃ₜ N) (g : N ≃ₜ P) :
    (s.map f).map g = s.map (f.trans g) :=
  (rfl)

end Transport

variable {M : Type u} {N : Type v} {P : Type w} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace P]

/-! ### Topological consequences -/

/-- A space with a PL structure is compact: the triangulating complex has finitely many
vertices. -/
protected theorem compactSpace (s : PLStructure M n) : CompactSpace M :=
  s.e.compactSpace

/-- A space with a PL structure is Hausdorff. -/
protected theorem t2Space (s : PLStructure M n) : T2Space M :=
  s.e.t2Space

/-- A space with a PL structure has finite CW type, so its Euler characteristic is defined. -/
protected theorem finiteCWType (s : PLStructure M n) : FiniteCWType M :=
  s.e.symm.finiteCWType

/-- The Euler characteristic of a space with a PL structure is the alternating count of the
faces of the triangulating complex, a face with `k + 1` vertices counted with sign `(-1) ^ k`.
For a combinatorial surface this is `V - E + F`. -/
theorem eulerChar_eq (s : PLStructure M n) [FiniteCWType M] :
    eulerChar M = ∑ᶠ σ : Face s.K, (-1 : ℤ) ^ (σ.val.card + 1) :=
  eulerChar_eq_finsum_of_homeomorph s.K s.e

/-- A space with a PL structure of dimension `n` has a triangulation by a combinatorial
`n`-manifold. -/
theorem isCombinatoriallyTriangulable (s : PLStructure M n) :
    IsCombinatoriallyTriangulable.{u} M n :=
  -- `convert` reconciles the `DecidableEq s.ι` instances of the field and of the
  -- characterization, both classical but elaborated separately.
  isCombinatoriallyTriangulable_iff.mpr ⟨s.ι, s.K, by convert s.isCombinatorialManifold, ⟨s.e⟩⟩

/-! ### Piecewise-linear maps -/

/-- A map `f : M → N` is **piecewise linear** for the PL structures `s` on `M` and `t` on `N`
when, read in barycentric coordinates through `s.e` and `t.e`, it is the restriction of a map of
coordinate spaces which is piecewise linear on the coordinate image of the realization of
`s.K`. -/
def IsPLMap (s : PLStructure M m) (t : PLStructure N n) (f : M → N) : Prop :=
  ∃ F : (s.ι → ℝ) → (t.ι → ℝ),
    IsPLOn F (range fun y : Realization s.K => (y.val : s.ι → ℝ)) ∧
      ∀ y : Realization s.K, F (y.val : s.ι → ℝ) = ((t.e.symm (f (s.e y))).val : t.ι → ℝ)

/-- The witness characterization of `TauCeti.PLStructure.IsPLMap`. -/
theorem isPLMap_iff {s : PLStructure M m} {t : PLStructure N n} {f : M → N} :
    s.IsPLMap t f ↔ ∃ F : (s.ι → ℝ) → (t.ι → ℝ),
      IsPLOn F (range fun y : Realization s.K => (y.val : s.ι → ℝ)) ∧
        ∀ y : Realization s.K, F (y.val : s.ι → ℝ) = ((t.e.symm (f (s.e y))).val : t.ι → ℝ) :=
  Iff.rfl

/-- The identity is piecewise linear from a PL structure to itself. -/
@[simp]
theorem isPLMap_id (s : PLStructure M n) : s.IsPLMap s id :=
  ⟨id, isPLOn_id _, fun y => by simp⟩

/-- Piecewise-linear maps compose. -/
theorem IsPLMap.comp {s : PLStructure M m} {t : PLStructure N n} {r : PLStructure P p}
    {f : M → N} {g : N → P} (hg : t.IsPLMap r g) (hf : s.IsPLMap t f) :
    s.IsPLMap r (g ∘ f) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨G ∘ F, hG.comp hF ?_, fun y => ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨t.e.symm (f (s.e y)), (hFf y).symm⟩
  · simp [hFf, hGg]

/-- A piecewise-linear map is continuous. -/
theorem IsPLMap.continuous {s : PLStructure M m} {t : PLStructure N n} {f : M → N}
    (h : s.IsPLMap t f) : Continuous f := by
  obtain ⟨F, hF, hFf⟩ := h
  -- Read `f` on the realizations; in coordinates it is the continuous map `F`.
  have hcoord : Continuous fun y : Realization s.K => ((t.e.symm (f (s.e y))).val : t.ι → ℝ) :=
    (hF.continuousOn.comp_continuous (continuous_realization_coe s.K)
      fun y => mem_range_self y).congr hFf
  -- Coordinates are a closed embedding of the realization of a finite complex.
  have hg : Continuous fun y : Realization s.K => t.e.symm (f (s.e y)) :=
    (t.K.isClosedEmbedding_realization_coe (Set.toFinite _)).continuous_iff.mpr hcoord
  exact t.e.symm.comp_continuous_iff.mp (s.e.comp_continuous_iff'.mp hg)

/-- Transporting the source structure along `g` replaces the map by its composite with `g`. -/
@[simp]
theorem isPLMap_map_left_iff {N' : Type u} [TopologicalSpace N'] {s : PLStructure M m}
    {t : PLStructure P n} (g : M ≃ₜ N') {f : N' → P} :
    (s.map g).IsPLMap t f ↔ s.IsPLMap t (f ∘ g) :=
  Iff.rfl

/-- Transporting the target structure along `g` replaces the map by its composite with
`g.symm`. -/
@[simp]
theorem isPLMap_map_right_iff {P' : Type v} [TopologicalSpace P'] {s : PLStructure M m}
    {t : PLStructure N n} (g : N ≃ₜ P') {f : M → P'} :
    s.IsPLMap (t.map g) f ↔ s.IsPLMap t (g.symm ∘ f) :=
  Iff.rfl

/-- A homeomorphism is piecewise linear from a PL structure to its transport along it. -/
theorem isPLMap_map {N' : Type u} [TopologicalSpace N'] (s : PLStructure M n) (g : M ≃ₜ N') :
    s.IsPLMap (s.map g) g := by
  simp

/-! ### Standard examples -/

/-- The unit sphere `Sⁿ`, triangulated by the boundary of the standard `(n + 1)`-simplex. -/
def sphere (n : ℕ) : PLStructure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n :=
  (ofRealization (standardSuccSimplexBoundary n) (by
    rw [standardSuccSimplexBoundary_toPreAbstractSimplicialComplex]
    exact PreAbstractSimplicialComplex.isCombinatorialManifold_simplexBoundary (by simp))).map
    (realizationStandardSuccSimplexBoundaryHomeomorphSphere n)

/-- `TauCeti.PLStructure.sphere` is the realization of the boundary of the standard
`(n + 1)`-simplex, transported to the sphere. It is stated for any proof `h` of the manifold
condition, so rewriting with it does not restate that proof. -/
theorem sphere_eq_map
    (h : (standardSuccSimplexBoundary n).toPreAbstractSimplicialComplex.IsCombinatorialManifold n) :
    sphere n = (ofRealization (standardSuccSimplexBoundary n) h).map
      (realizationStandardSuccSimplexBoundaryHomeomorphSphere n) :=
  (rfl)

/-- The closed unit `n`-ball, triangulated by the standard `n`-simplex. -/
def closedBall (n : ℕ) : PLStructure (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) n :=
  (ofRealization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) (by
    rw [top_toPreAbstractSimplicialComplex, ← PreAbstractSimplicialComplex.simplex_univ]
    exact PreAbstractSimplicialComplex.isCombinatorialManifold_simplex (by simp))).map
    (realizationTopHomeomorphClosedBall n)

/-- `TauCeti.PLStructure.closedBall` is the realization of the standard `n`-simplex, transported
to the closed ball. It is stated for any proof `h` of the manifold condition, so rewriting with it
does not restate that proof. -/
theorem closedBall_eq_map
    (h : PreAbstractSimplicialComplex.IsCombinatorialManifold
      (⊤ : AbstractSimplicialComplex (Fin (n + 1))).toPreAbstractSimplicialComplex n) :
    closedBall n = (ofRealization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) h).map
      (realizationTopHomeomorphClosedBall n) :=
  (rfl)

end PLStructure

/-- A space has a PL structure of dimension `n` exactly when it is compact and has a
triangulation by a combinatorial `n`-manifold whose vertex type lies in the universe of the space.
Compactness forces the triangulating complex to have finitely many vertices. -/
theorem nonempty_plStructure_iff {M : Type u} [TopologicalSpace M] {n : ℕ} :
    Nonempty (PLStructure M n) ↔ CompactSpace M ∧ IsCombinatoriallyTriangulable.{u} M n := by
  refine ⟨fun ⟨s⟩ => ⟨s.compactSpace, s.isCombinatoriallyTriangulable⟩, ?_⟩
  rintro ⟨hM, h⟩
  obtain ⟨ι, K, hK, ⟨e⟩⟩ := isCombinatoriallyTriangulable_iff.mp h
  have : CompactSpace (Realization K) := e.symm.compactSpace
  have : Finite ι := (K.compactSpace_realization_iff_finite).mp inferInstance
  -- `convert` replaces the classical `DecidableEq ι` instance of `hK` by that of the field.
  exact ⟨⟨ι, K, by convert hK, e⟩⟩

end TauCeti
