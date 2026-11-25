/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LinearExtension
public import TauCeti.Analysis.Convex.SimplicialComplex.Map

/-!
# The geometric complex spanned by an injective linear extension

Let `K` be an abstract simplicial complex and `p : ι → E` vertex data in a real vector space whose
linear extension `K.linearExtension p : |K| → E` is injective. Then the images `p '' σ` of the
faces `σ` of `K` are the faces of a geometric simplicial complex `K.imageComplex p hp` in `E`,
whose underlying space is the image of the linear extension
(`AbstractSimplicialComplex.space_imageComplex`). It is the image of the standard geometric
complex of `K` in `ι →₀ ℝ` under the linear map `Finsupp.linearCombination ℝ p`
(`AbstractSimplicialComplex.imageComplex_def`), and its underlying abstract complex is the
relabeling of `K` by `p` (`AbstractSimplicialComplex.toPreAbstractSimplicialComplex_imageComplex`).

This is how an injective map of a realization which is linear in barycentric coordinates on every
closed simplex, such as an injective secant map `K.secantMap f` with `p = f ∘ vertex K`, becomes a
rectilinear complex in its target. There it can be fitted together with other polyhedra. For
instance, when `K` has finitely many faces and `E` is a finite-dimensional real normed space,
`Geometry.SimplicialComplex.exists_space_eq_union` triangulates its union with the polyhedron of
another finite complex by subdivisions of both. Rewriting with
`AbstractSimplicialComplex.imageComplex_def`,
`Geometry.SimplicialComplex.IsSubdivision.existsUnique_isSubdivision_map_eq` shows that every
subdivision of the image complex chosen in `E` is the image of a unique subdivision of the
standard geometric complex of `K`, on every simplex of which `Finsupp.linearCombination ℝ p` is
still linear. Fitting an embedded complex, made rectilinear in a coordinate chart, together with
other polyhedra there needs exactly this, as in Munkres' construction of smooth triangulations.

## Main definitions

* `AbstractSimplicialComplex.imageComplex K p hp`: the geometric complex in `E` whose faces are
  the images of the faces of `K` under `p`.

## Main results

* `AbstractSimplicialComplex.mem_imageComplex_faces`,
  `AbstractSimplicialComplex.faces_imageComplex`: its faces are the images of the faces of `K`.
* `AbstractSimplicialComplex.space_imageComplex`: its underlying space equals the range of the
  linear extension.
* `AbstractSimplicialComplex.vertices_imageComplex`: its vertices are the points `p v`.
* `AbstractSimplicialComplex.finite_faces_imageComplex_iff`: it is finite exactly when `K` is.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial maps and triangulations of polyhedra).
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Theorems 10.5–10.6.
-/

public section

noncomputable section

open Set Function TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E] {K : AbstractSimplicialComplex ι}
  {p : ι → E}

variable (K p) in
/-- The geometric simplicial complex in `E` spanned by vertex data `p` whose linear extension over
`|K|` is injective: its faces are the images under `p` of the faces of `K`. It is the image of the
standard geometric complex of `K` under the linear map `Finsupp.linearCombination ℝ p`. -/
def imageComplex (hp : Injective (K.linearExtension p)) : Geometry.SimplicialComplex ℝ E :=
  K.standardGeometricComplex.map (Finsupp.linearCombination ℝ p)
    (injOn_linearCombination_space hp)
    fun _ _ => ⟨(Finsupp.linearCombination ℝ p).toAffineMap, fun _ _ => rfl⟩

variable {hp : Injective (K.linearExtension p)}

/-- The image complex is the image of the standard geometric complex of `K` under the linear map
`Finsupp.linearCombination ℝ p`. -/
theorem imageComplex_def :
    K.imageComplex p hp = K.standardGeometricComplex.map (Finsupp.linearCombination ℝ p)
      (injOn_linearCombination_space hp)
      (fun _ _ => ⟨(Finsupp.linearCombination ℝ p).toAffineMap, fun _ _ => rfl⟩) :=
  (rfl)

/-- The underlying abstract complex of the image complex is the relabeling of `K` by `p`. -/
theorem toPreAbstractSimplicialComplex_imageComplex [DecidableEq E] :
    (K.imageComplex p hp).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex.map p := by
  classical
  rw [imageComplex_def, Geometry.SimplicialComplex.toPreAbstractSimplicialComplex_map,
    toPreAbstractSimplicialComplex_standardGeometricComplex, PreAbstractSimplicialComplex.map_map]
  -- The standard precomplex relabels vertices by coordinate vectors; compose this with `p`.
  simp only [Function.comp_def, Finsupp.linearCombination_single, one_smul]

/-- The faces of the image complex are the images under `p` of the faces of `K`. -/
@[simp]
theorem mem_imageComplex_faces {t : Finset E} :
    t ∈ (K.imageComplex p hp).faces ↔ ∃ σ ∈ K, p '' (σ : Set ι) = t := by
  classical
  rw [PreAbstractSimplicialComplex.mem_faces, toPreAbstractSimplicialComplex_imageComplex,
    PreAbstractSimplicialComplex.mem_map_iff]
  simp only [mem_toPreAbstractSimplicialComplex, ← Finset.coe_inj, Finset.coe_image]

/-- The face set of the image complex is the direct image under `p` of the face set of `K`. -/
theorem faces_imageComplex [DecidableEq E] :
    (K.imageComplex p hp).faces = (fun σ : Finset ι => σ.image p) '' K.faces := by
  rw [← PreAbstractSimplicialComplex.faces_map]
  exact congrArg PreAbstractSimplicialComplex.faces toPreAbstractSimplicialComplex_imageComplex

/-- The underlying space of the image complex equals the range of the linear extension of `p`. -/
@[simp]
theorem space_imageComplex : (K.imageComplex p hp).space = range (K.linearExtension p) := by
  ext y
  simp [imageComplex_def, linearExtension_apply]

/-- The vertices of the image complex are the points `p v`. -/
@[simp]
theorem vertices_imageComplex : (K.imageComplex p hp).vertices = range p := by
  classical
  ext y
  rw [Geometry.SimplicialComplex.mem_vertices, PreAbstractSimplicialComplex.mem_faces,
    toPreAbstractSimplicialComplex_imageComplex, PreAbstractSimplicialComplex.singleton_mem_map_iff]
  exact exists_congr fun x => and_iff_right (K.singleton_mem x)

/-- The image complex has finitely many faces exactly when `K` has. -/
@[simp]
theorem finite_faces_imageComplex_iff : (K.imageComplex p hp).faces.Finite ↔ K.faces.Finite := by
  classical
  rw [faces_imageComplex, ← PreAbstractSimplicialComplex.faces_map]
  exact PreAbstractSimplicialComplex.finite_faces_map_iff_of_injOn p
    (injective_of_injective_linearExtension hp).injOn

end AbstractSimplicialComplex
