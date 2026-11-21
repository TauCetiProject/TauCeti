/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.FacePresentation.Boundary
public import TauCeti.Combinatorics.PolygonalComplex.Pants
public import TauCeti.Combinatorics.PolygonalComplex.TriangulatedDisc

/-!
# Face groups and boundary words of the disc and the pair of pants

This file computes the face presentations of two surface models with boundary, together with
their boundary words.

* **Discs.** In the one-vertex disc `a`, the face relation kills the boundary loop, so the boundary
  word of every boundary circuit is trivial (`SurfaceModel.boundaryWord_disc`). The triangulated
  disc, three triangles around an inner vertex, also has trivial face group relative to every
  spanning tree (`SurfaceModel.instSubsingletonFacePresentationTriangulatedDisc`): its three faces
  express each rim edge through the spokes, and a spanning tree kills the spokes up to a common
  factor. Its boundary word is trivial whatever darts are killed, since every closed path
  telescopes (`SurfaceModel.boundaryWord_triangulatedDisc`).
* **The pair of pants.** The only spanning tree of the pants graph consists of the three arcs `cᵢ`
  (`SurfaceModel.spanningTree_darts_pants`), so the face relator `c₀ h₀ c₀⁻¹ c₁ h₁ c₁⁻¹ c₂ h₂ c₂⁻¹`
  becomes `h₀ h₁ h₂`. The face group is the surface group `S⁺(0, 3) = ⟨p₁, p₂, p₃ | p₁ p₂ p₃⟩`
  (`SurfaceModel.pantsFacePresentationEquiv`), which is free on `p₁, p₂` with `p₃ = (p₁ p₂)⁻¹`
  (`SurfaceGroup.Orientable.equivFreeGroup`). A boundary circuit around the `i`-th hole
  traverses the loop `hᵢ` once, so its boundary word is the peripheral element `pᵢ` or its
  inverse (`SurfaceModel.pantsFacePresentationEquiv_boundaryWord`), and the three boundary
  components are marked by the three peripheral elements (`SurfaceModel.marksBoundary_pants`).

## Main definitions

* `TauCeti.SurfaceModel.pantsFacePresentationEquiv`: the face group of the pair of pants is
  `S⁺(0, 3)`.

## Main results

* `TauCeti.SurfaceModel.boundaryWord_disc`,
  `TauCeti.SurfaceModel.boundaryWord_triangulatedDisc`: the boundary words of the discs are
  trivial.
* `TauCeti.SurfaceModel.instSubsingletonFacePresentationTriangulatedDisc`: the face group of the
  triangulated disc is trivial.
* `TauCeti.SurfaceModel.pantsFacePresentationEquiv_boundaryWord`,
  `TauCeti.SurfaceModel.marksBoundary_pants`: the boundary words of the pair of pants are the
  peripheral elements of `S⁺(0, 3)` up to inversion, one for each hole.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  §6.6 (the fundamental groups of the sphere with holes: the boundary elements `dᵢ = cᵢ hᵢ cᵢ⁻¹`
  satisfy `d₁ ⋯ d_q = 1`, and the disc has trivial group) and Figure 6.6 (the triangulated disc).
-/

public section

namespace TauCeti

namespace SurfaceModel

open PolygonalComplex

/-! ### Discs -/

/-- The boundary word of every boundary circuit of the one-vertex disc is trivial: the face relation
kills the boundary loop. -/
theorem boundaryWord_disc (T : Set disc.graph.E) {b : disc.BoundaryComponent}
    (c : disc.BoundaryCircuit b) : disc.boundaryWord T c = 1 :=
  Subsingleton.elim _ _

-- A potential for the generators of the face group of the triangulated disc: trivial at the
-- centre and the spoke `sᵢ` at the rim vertex `i`.
private def discPotential (T : Set triangulatedDiscGraph.E) (x : triangulatedDiscGraph.V) :
    PolygonalComplex.triangulatedDisc.FacePresentation T :=
  Option.elim x 1 fun i => PresentedGroup.of ((.inl i, true) : triangulatedDiscGraph.E)

-- Every generator of the face group of the triangulated disc is the quotient of the potential at
-- its two ends: the face `i` gives `bᵢ = sᵢ⁻¹ sᵢ₊₁`, whatever darts are killed.
private theorem of_eq_discPotential (T : Set triangulatedDiscGraph.E)
    (e : triangulatedDiscGraph.E) :
    (PresentedGroup.of e : PolygonalComplex.triangulatedDisc.FacePresentation T) =
      (discPotential T (triangulatedDiscGraph.src e))⁻¹ *
        discPotential T (triangulatedDiscGraph.tgt e) := by
  have hrev (x : Fin 3 ⊕ Fin 3) :
      PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
          ((x, false) : triangulatedDiscGraph.E) =
        (PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
          ((x, true) : triangulatedDiscGraph.E))⁻¹ :=
    FacePresentation.of_rev (T := T) (C := PolygonalComplex.triangulatedDisc)
      ((x, true) : triangulatedDiscGraph.E)
  -- The face `i` is attached along `sᵢ bᵢ sᵢ₊₁⁻¹`.
  have hface (i : Fin 3) :
      PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
          ((.inr i, true) : triangulatedDiscGraph.E) =
        (PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
          ((.inl i, true) : triangulatedDiscGraph.E))⁻¹ *
        PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
          ((.inl (i + 1), true) : triangulatedDiscGraph.E) := by
    have h :
        PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
            ((.inl i, true) : triangulatedDiscGraph.E) *
          (PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
              ((.inr i, true) : triangulatedDiscGraph.E) *
            PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T)
              ((.inl (i + 1), false) : triangulatedDiscGraph.E)) = 1 := by
      -- The sides of the face `i` are the entries of the list `[sᵢ, bᵢ, sᵢ₊₁⁻¹]`.
      exact FacePresentation.prod_ofFn_of_comp_side (T := T)
        (C := PolygonalComplex.triangulatedDisc) i
    rw [hrev, ← mul_assoc] at h
    exact eq_inv_mul_of_mul_eq (mul_inv_eq_one.1 h)
  obtain ⟨i | i, _ | _⟩ := e <;> simp [discPotential, hrev, hface]

-- Along a path of the triangulated disc, the product of the generators of the darts is the
-- quotient of the potential at the two ends.
private theorem prod_map_of_darts_discPotential (T : Set triangulatedDiscGraph.E)
    {a b : triangulatedDiscGraph.V} (p : triangulatedDiscGraph.Path a b) :
    ((SerreGraph.Path.darts _ p).map
        (PresentedGroup.of (rels := PolygonalComplex.triangulatedDisc.faceRelators T))).prod =
      (discPotential T a)⁻¹ * discPotential T b := by
  induction p with
  | nil => simp
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    rw [SerreGraph.Path.darts_cons, List.map_append, List.prod_append, ih, List.map_singleton,
      List.prod_singleton, of_eq_discPotential, mul_assoc, mul_inv_cancel_left]

/-- The face group of the triangulated disc relative to any spanning tree is trivial. -/
instance instSubsingletonFacePresentationTriangulatedDisc
    (T : triangulatedDisc.graph.SpanningTree) :
    Subsingleton (triangulatedDisc.FacePresentation T.darts) := by
  -- The potential is trivial, since the dart words of the tree paths from the centre are.
  have hpot (x : triangulatedDiscGraph.V) : discPotential T.darts x = 1 := by
    obtain ⟨p, -, hpT⟩ := T.exists_path none x
    have h := prod_map_of_darts_discPotential T.darts p
    rw [List.prod_eq_one fun g hg => ?_] at h
    · simpa [discPotential] using h.symm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
    exact FacePresentation.of_eq_one (hpT e he)
  have hof (e : triangulatedDiscGraph.E) :
      (PresentedGroup.of e : triangulatedDisc.FacePresentation T.darts) = 1 := by
    rw [of_eq_discPotential, hpot, hpot, inv_one, one_mul]
  have hid : MonoidHom.id (triangulatedDisc.FacePresentation T.darts) = 1 :=
    PresentedGroup.ext hof
  exact subsingleton_of_forall_eq 1 fun x => DFunLike.congr_fun hid x

/-- The boundary word of every boundary circuit of the triangulated disc is trivial, whatever darts
are killed: the three faces express each rim edge `bᵢ` as `sᵢ⁻¹ sᵢ₊₁`, and the rim word
telescopes. -/
theorem boundaryWord_triangulatedDisc (T : Set triangulatedDisc.graph.E)
    {b : triangulatedDisc.BoundaryComponent} (c : triangulatedDisc.BoundaryCircuit b) :
    triangulatedDisc.boundaryWord T c = 1 := by
  have h := prod_map_of_darts_discPotential T
    (triangulatedDisc.boundaryInclusion.toPrefunctor.mapPath c.path)
  rw [SerreGraph.Hom.darts_mapPath, List.map_map, inv_mul_cancel] at h
  rw [boundaryWord_def]
  exact h

/-! ### The pair of pants -/

-- The images of the darts of the pair of pants in `S⁺(0, 3)`: the arcs are trivial and the loop
-- `hᵢ` is the peripheral element `pᵢ`.
private def pantsDartImage (e : (Fin 3 ⊕ Fin 3) × Bool) : SurfaceGroup.Orientable 0 3 :=
  e.1.elim (fun _ => 1) fun i =>
    cond e.2 (SurfaceGroup.Orientable.peripheral 0 3 i)
      (SurfaceGroup.Orientable.peripheral 0 3 i)⁻¹

-- The face of the pair of pants is attached along `pantsWord`.
private theorem ofFn_side_pants (f : pants.Face) : List.ofFn (pants.side f) = pantsWord :=
  List.ofFn_getElem

-- The darts of the arcs are tree darts.
private theorem inl_mem_darts_pants (T : pants.graph.SpanningTree) (i : Fin 3) (b : Bool) :
    ((.inl i, b) : pants.graph.E) ∈ T.darts := by
  rw [spanningTree_darts_pants]
  rfl

private noncomputable def pantsToSurfaceGroup (T : pants.graph.SpanningTree) :
    pants.FacePresentation T.darts →* SurfaceGroup.Orientable 0 3 :=
  FacePresentation.lift pantsDartImage
    (fun e he => by
      rw [spanningTree_darts_pants] at he
      obtain ⟨i | i, b⟩ := e
      · rfl
      · exact absurd he Bool.false_ne_true)
    (fun e => by
      obtain ⟨i | i, _ | _⟩ := e <;> simp [pantsDartImage])
    (fun f => by
      have h := SurfaceGroup.Orientable.orientableWord_a_b_peripheral (g := 0) (m := 3)
      simp only [SurfaceGroup.orientableWord_def, List.ofFn_zero, List.prod_nil, one_mul,
        List.ofFn_succ, List.prod_cons] at h
      rw [ofFn_side_pants]
      -- Read the letters of `pantsWord` as pairs, the type of the darts of the pants graph.
      change (pantsWord.map pantsDartImage).prod = 1
      simpa [pantsWord, pantsDartImage] using h)

-- In the face group of the pair of pants, the loops multiply to the identity: the face relation
-- `c₀ h₀ c₀⁻¹ c₁ h₁ c₁⁻¹ c₂ h₂ c₂⁻¹ = 1` with the tree darts `cᵢ` killed.
private theorem of_mul_of_mul_of_pants (T : pants.graph.SpanningTree) :
    PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr 0, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr 1, true) : pants.graph.E) *
        PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr 2, true) : pants.graph.E)) =
      1 := by
  have harc (i : Fin 3) (b : Bool) :
      PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inl i, b) : pants.graph.E) = 1 :=
    FacePresentation.of_eq_one (inl_mem_darts_pants T i b)
  have h₀ := FacePresentation.prod_ofFn_of_comp_side (T := T.darts)
    (C := pants.toPolygonalComplex) ()
  -- The sides of the face are the letters of `pantsWord`.
  have h : PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inl 0, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr 0, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inl 0, false) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inl 1, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr 1, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inl 1, false) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inl 2, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr 2, true) : pants.graph.E) *
      (PresentedGroup.of (rels := pants.faceRelators T.darts)
        ((.inl 2, false) : pants.graph.E))))))))) = 1 := h₀
  rw [harc, harc, harc, harc, harc, harc] at h
  simpa only [one_mul, mul_one] using h

private noncomputable def surfaceGroupToPants (T : pants.graph.SpanningTree) :
    SurfaceGroup.Orientable 0 3 →* pants.FacePresentation T.darts :=
  SurfaceGroup.Orientable.lift Fin.elim0 Fin.elim0
    (fun i => PresentedGroup.of (rels := pants.faceRelators T.darts)
      ((.inr i, true) : pants.graph.E)) <| by
    simpa [SurfaceGroup.orientableWord_def, List.ofFn_succ] using of_mul_of_mul_of_pants T

private theorem pantsToSurfaceGroup_of (T : pants.graph.SpanningTree) (e : pants.graph.E) :
    pantsToSurfaceGroup T (PresentedGroup.of e) = pantsDartImage e :=
  FacePresentation.lift_of _ _ _ _ e

private theorem surfaceGroupToPants_peripheral (T : pants.graph.SpanningTree) (i : Fin 3) :
    surfaceGroupToPants T (SurfaceGroup.Orientable.peripheral 0 3 i) =
      PresentedGroup.of (rels := pants.faceRelators T.darts) ((.inr i, true) : pants.graph.E) :=
  SurfaceGroup.Orientable.lift_peripheral _ _ _ _ i

/-- **The face group of the pair of pants is `S⁺(0, 3)`.** Relative to any spanning tree, the face
presentation of the pair of pants is the surface group `⟨p₁, p₂, p₃ | p₁ p₂ p₃⟩`: the arcs `cᵢ`
are trivial and the loop `hᵢ` around the `i`-th hole is the peripheral element `pᵢ`. -/
noncomputable def pantsFacePresentationEquiv (T : pants.graph.SpanningTree) :
    pants.FacePresentation T.darts ≃* SurfaceGroup.Orientable 0 3 :=
  MonoidHom.toMulEquiv (pantsToSurfaceGroup T) (surfaceGroupToPants T)
    (PresentedGroup.ext fun e => by
      refine (congrArg (surfaceGroupToPants T) (pantsToSurfaceGroup_of T e)).trans ?_
      obtain ⟨i | i, _ | _⟩ := e
      · exact (map_one _).trans (FacePresentation.of_eq_one (inl_mem_darts_pants T i false)).symm
      · exact (map_one _).trans (FacePresentation.of_eq_one (inl_mem_darts_pants T i true)).symm
      · exact ((map_inv _ _).trans (congrArg _ (surfaceGroupToPants_peripheral T i))).trans
          (FacePresentation.of_rev (C := pants.toPolygonalComplex) (T := T.darts)
            ((.inr i, true) : pants.graph.E)).symm
      · exact surfaceGroupToPants_peripheral T i)
    (SurfaceGroup.Orientable.hom_ext (fun i => i.elim0) (fun i => i.elim0) fun j =>
      (congrArg (pantsToSurfaceGroup T) (surfaceGroupToPants_peripheral T j)).trans
        (pantsToSurfaceGroup_of T _))

private theorem pantsFacePresentationEquiv_apply (T : pants.graph.SpanningTree)
    (x : pants.FacePresentation T.darts) :
    pantsFacePresentationEquiv T x = pantsToSurfaceGroup T x := rfl

/-- The arcs of the pair of pants are trivial in its face group. -/
@[simp] theorem pantsFacePresentationEquiv_of_inl (T : pants.graph.SpanningTree) (i : Fin 3)
    (b : Bool) :
    pantsFacePresentationEquiv T (PresentedGroup.of ((.inl i, b) : pants.graph.E)) = 1 :=
  (pantsFacePresentationEquiv_apply T _).trans (pantsToSurfaceGroup_of T _)

/-- The loop `hᵢ` around the `i`-th hole is the peripheral element `pᵢ`. -/
@[simp] theorem pantsFacePresentationEquiv_of_inr_true (T : pants.graph.SpanningTree) (i : Fin 3) :
    pantsFacePresentationEquiv T (PresentedGroup.of ((.inr i, true) : pants.graph.E)) =
      SurfaceGroup.Orientable.peripheral 0 3 i :=
  (pantsFacePresentationEquiv_apply T _).trans (pantsToSurfaceGroup_of T _)

/-- The loop `hᵢ` traversed backwards is the inverse of the peripheral element `pᵢ`. -/
@[simp] theorem pantsFacePresentationEquiv_of_inr_false (T : pants.graph.SpanningTree) (i : Fin 3) :
    pantsFacePresentationEquiv T (PresentedGroup.of ((.inr i, false) : pants.graph.E)) =
      (SurfaceGroup.Orientable.peripheral 0 3 i)⁻¹ :=
  (pantsFacePresentationEquiv_apply T _).trans (pantsToSurfaceGroup_of T _)

/-- The peripheral element `pᵢ` is the loop `hᵢ` around the `i`-th hole. -/
@[simp] theorem pantsFacePresentationEquiv_symm_peripheral (T : pants.graph.SpanningTree)
    (i : Fin 3) :
    (pantsFacePresentationEquiv T).symm (SurfaceGroup.Orientable.peripheral 0 3 i) =
      PresentedGroup.of ((.inr i, true) : pants.graph.E) :=
  surfaceGroupToPants_peripheral T i

-- A boundary circuit around the `i`-th hole of the pair of pants traverses the loop `hᵢ` once, in
-- one of its two directions.
private theorem exists_darts_eq_pants {b : pants.BoundaryComponent} (c : pants.BoundaryCircuit b) :
    ∃ d : pants.boundary.E, SerreGraph.Path.darts _ c.path = [d] ∧
      ∃ x : Bool, d.val = ((.inr (pantsBoundaryComponentEquiv b), x) : pants.graph.E) := by
  -- Every dart of the circuit is a dart of the loop of its hole.
  have hd (d : pants.boundary.E) (hmem : d ∈ SerreGraph.Path.darts _ c.path) :
      ∃ x : Bool, d.val = ((.inr (pantsBoundaryComponentEquiv b), x) : pants.graph.E) := by
    obtain ⟨⟨k | k, x⟩, he⟩ := d
    · exact absurd he (inl_notMem_boundaryDarts_pants k x)
    · refine ⟨x, ?_⟩
      have h := pantsBoundaryComponentEquiv_boundaryClass_inr k x he
      rw [c.boundaryClass_eq_of_mem_darts hmem] at h
      rw [h]
  -- The two darts of that loop lie on the same geometric edge, which the circuit traverses once.
  obtain ⟨d, l, hl⟩ := List.exists_cons_of_ne_nil c.darts_ne_nil
  refine ⟨d, ?_, hd d (by simp [hl])⟩
  rcases l with _ | ⟨d', l⟩
  · exact hl
  · have hnd := c.nodup_map_toGeomEdge_darts
    rw [hl] at hnd
    obtain ⟨x, hx⟩ := hd d (by simp [hl])
    obtain ⟨x', hx'⟩ := hd d' (by simp [hl])
    have h : pants.boundary.toGeomEdge d = pants.boundary.toGeomEdge d' := by
      rw [SerreGraph.toGeomEdge_eq_toGeomEdge_iff]
      cases x <;> cases x'
      · exact Or.inl (Subtype.ext (hx'.trans hx.symm))
      · exact Or.inr (Subtype.ext (by simp only [boundary_rev_val, hx, hx']; rfl))
      · exact Or.inr (Subtype.ext (by simp only [boundary_rev_val, hx, hx']; rfl))
      · exact Or.inl (Subtype.ext (hx'.trans hx.symm))
    simp [h] at hnd

/-- The boundary word of a boundary circuit around the `i`-th hole of the pair of pants is the
peripheral element `pᵢ` of `S⁺(0, 3)` or its inverse, according to the direction of the circuit. -/
theorem pantsFacePresentationEquiv_boundaryWord (T : pants.graph.SpanningTree)
    {b : pants.BoundaryComponent} (c : pants.BoundaryCircuit b) :
    pantsFacePresentationEquiv T (pants.boundaryWord T.darts c) =
        SurfaceGroup.Orientable.peripheral 0 3 (pantsBoundaryComponentEquiv b) ∨
      pantsFacePresentationEquiv T (pants.boundaryWord T.darts c) =
        (SurfaceGroup.Orientable.peripheral 0 3 (pantsBoundaryComponentEquiv b))⁻¹ := by
  obtain ⟨d, hdarts, x, hx⟩ := exists_darts_eq_pants c
  rw [boundaryWord_def, hdarts, List.map_singleton, List.prod_singleton, hx]
  cases x
  · exact Or.inr (pantsFacePresentationEquiv_of_inr_false T _)
  · exact Or.inl (pantsFacePresentationEquiv_of_inr_true T _)

/-- **The boundary of the pair of pants is marked by the peripheral elements.** The bijection from
the boundary components of the pair of pants to its holes takes every boundary circuit to the
peripheral element `pᵢ` of `S⁺(0, 3)` of its hole, up to inversion. -/
theorem marksBoundary_pants (T : pants.graph.SpanningTree) :
    pants.MarksBoundary T.darts (pantsFacePresentationEquiv T).toMonoidHom
      (SurfaceGroup.Orientable.peripheral 0 3) :=
  (marksBoundary_iff _ _ _ _).2 ⟨pantsBoundaryComponentEquiv, fun _ c => by
    rcases pantsFacePresentationEquiv_boundaryWord T c with h | h
    · exact Or.inl (by rw [MulEquiv.coe_toMonoidHom, h])
    · exact Or.inr (by rw [MulEquiv.coe_toMonoidHom, h])⟩

end SurfaceModel

end TauCeti
