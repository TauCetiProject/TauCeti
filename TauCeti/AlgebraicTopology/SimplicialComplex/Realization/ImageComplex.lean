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
complex of `K` in `ι →₀ ℝ` under the linear map `Finsupp.linearCombination ℝ p`.

This is how an injective map of a realization which is linear in barycentric coordinates on every
closed simplex, such as an injective secant map `K.secantMap f` with `p = f ∘ vertex K`, becomes a
rectilinear complex in its target. There it can be fitted together with other polyhedra, for
instance by `Geometry.SimplicialComplex.exists_space_eq_union`. Every subdivision of the image
complex chosen in `E` comes from a subdivision of the standard geometric complex of `K`
(`AbstractSimplicialComplex.exists_isSubdivision_map_eq_of_isSubdivision_imageComplex`), on which
`p` is still linear on every simplex. Fitting an embedded complex, made rectilinear in a
coordinate chart, together with other polyhedra there needs exactly this, as in Munkres'
construction of smooth triangulations.

## Main definitions

* `AbstractSimplicialComplex.imageComplex K p hp`: the geometric complex in `E` whose faces are
  the images of the faces of `K` under `p`.

## Main results

* `AbstractSimplicialComplex.mem_imageComplex_faces`: its faces are the images of the faces of
  `K`.
* `AbstractSimplicialComplex.space_imageComplex`: it triangulates the image of the linear
  extension.
* `AbstractSimplicialComplex.vertices_imageComplex`: its vertices are the points `p v`.
* `AbstractSimplicialComplex.finite_faces_imageComplex_iff`: it is finite exactly when `K` is.
* `AbstractSimplicialComplex.exists_isSubdivision_map_eq_of_isSubdivision_imageComplex`: its
  subdivisions are the images of subdivisions of the standard geometric complex of `K`.

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

/-- If the linear extension of `p` over `|K|` is injective, then so is the linear combination
of `p` on the underlying space of the standard geometric complex of `K`. -/
theorem injOn_linearCombination_space (hp : Injective (K.linearExtension p)) :
    InjOn (Finsupp.linearCombination ℝ p) K.standardGeometricComplex.space :=
  fun x hx y hy hxy => congrArg Subtype.val (hp (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) <| by
    rwa [linearExtension_apply, linearExtension_apply])

/-- If the linear extension of `p` over `|K|` is injective, then so is `p`. -/
theorem injective_of_injective_linearExtension (hp : Injective (K.linearExtension p)) :
    Injective p := fun v w hvw => K.vertex_injective <| hp <| by
  rw [linearExtension_vertex, linearExtension_vertex, hvw]

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
theorem imageComplex_eq_map :
    K.imageComplex p hp = K.standardGeometricComplex.map (Finsupp.linearCombination ℝ p)
      (injOn_linearCombination_space hp)
      (fun _ _ => ⟨(Finsupp.linearCombination ℝ p).toAffineMap, fun _ _ => rfl⟩) :=
  (rfl)

/-- The faces of the image complex are the images under `p` of the faces of `K`. -/
@[simp]
theorem mem_imageComplex_faces [DecidableEq E] {t : Finset E} :
    t ∈ (K.imageComplex p hp).faces ↔ ∃ σ ∈ K, σ.image p = t := by
  classical
  simp only [imageComplex_eq_map, Geometry.SimplicialComplex.mem_map_faces,
    mem_standardGeometricComplex_faces_iff]
  refine ⟨fun ⟨s, ⟨σ, hσ, hσs⟩, hst⟩ => ⟨σ, hσ, ?_⟩, fun ⟨σ, hσ, hσt⟩ => ⟨_, ⟨σ, hσ, rfl⟩, ?_⟩⟩
  · rw [← Finset.coe_inj, ← hst, ← hσs, Finset.coe_image, Finset.coe_image, Set.image_image]
    simp
  · rw [← hσt, Finset.coe_image, Finset.coe_image, Set.image_image]
    simp

/-- The image complex triangulates the image of the linear extension of `p`. -/
@[simp]
theorem space_imageComplex : (K.imageComplex p hp).space = range (K.linearExtension p) := by
  ext y
  simp [imageComplex_eq_map, linearExtension_apply]

/-- The vertices of the image complex are the points `p v`. -/
@[simp]
theorem vertices_imageComplex : (K.imageComplex p hp).vertices = range p := by
  classical
  ext y
  rw [Geometry.SimplicialComplex.mem_vertices, mem_imageComplex_faces]
  refine ⟨fun ⟨σ, _, hσ⟩ => ?_, fun ⟨v, hv⟩ => ⟨{v}, K.singleton_mem v, by simp [hv]⟩⟩
  obtain ⟨v, -, hvy⟩ := Finset.mem_image.1 (hσ ▸ Finset.mem_singleton_self y)
  exact ⟨v, hvy⟩

/-- The image complex has finitely many faces exactly when `K` has. -/
theorem finite_faces_imageComplex_iff : (K.imageComplex p hp).faces.Finite ↔ K.faces.Finite := by
  classical
  have hfaces : (K.imageComplex p hp).faces = (fun σ => σ.image p) '' K.faces := by
    ext t
    rw [mem_imageComplex_faces, Set.mem_image]
    simp only [PreAbstractSimplicialComplex.mem_faces, mem_toPreAbstractSimplicialComplex]
  rw [hfaces]
  exact finite_image_iff
    (Finset.image_injective (injective_of_injective_linearExtension hp)).injOn

/-- **Subdivisions of the image complex.** Every subdivision `L` of the image complex of `K` is
the image, under the linear map `Finsupp.linearCombination ℝ p`, of a subdivision `K'` of the
standard geometric complex of `K`. In particular `p` is linear on every simplex of `K'`, and
`K'` triangulates `|K|`. -/
theorem exists_isSubdivision_map_eq_of_isSubdivision_imageComplex
    {L : Geometry.SimplicialComplex ℝ E} (hL : L.IsSubdivision (K.imageComplex p hp)) :
    ∃ (K' : Geometry.SimplicialComplex ℝ (ι →₀ ℝ))
      (hK' : K'.IsSubdivision K.standardGeometricComplex),
      K'.map (Finsupp.linearCombination ℝ p)
        ((injOn_linearCombination_space hp).mono hK'.space_eq.le)
        (fun _ _ => ⟨(Finsupp.linearCombination ℝ p).toAffineMap, fun _ _ => rfl⟩) = L := by
  rw [imageComplex_eq_map] at hL
  exact hL.exists_isSubdivision_map_eq

end AbstractSimplicialComplex
