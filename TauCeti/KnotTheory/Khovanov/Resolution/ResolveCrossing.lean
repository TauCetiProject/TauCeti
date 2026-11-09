/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Cube
public import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# The faces of the cube of resolutions at a crossing

Let `D` be a PD-code with `n + 1` crossings, `c` one of its crossings and `t` a smoothing of `c`.
The vertices of the cube of resolutions of `D` at which `c` carries the smoothing `t` form a face
of the cube, of dimension `n`. This file identifies that face with the whole cube of resolutions
of the resolved code `D.resolveCrossing c t`, whose crossing `i` is the crossing `c.succAbove i`
of `D`.

The vertex `S ⊆ Fin n` of the cube of the resolution lies over the vertex
`TauCeti.PDCode.resolveCrossingVertex c t S` of the cube of `D`: the image of `S` under
`c.succAbove`, together with `c` itself for the `B`-smoothing `t = false`. Its state is
`c.insertNth t` of the state of `S`, so the circles of the two smoothings correspond by
`TauCeti.PDCode.resolveCrossingResolvedCircleEquiv`. Reindexing the circle tensors along this
correspondence commutes with the saddle maps, merges and splits alike. On the `B`-face every
height is one larger than in the cube of the resolution, so the identification raises the quantum
degree by one there: the `1`-face of `⟦D⟧` at `c` is `⟦D_B⟧⟨1⟩`, while the `0`-face is `⟦D_A⟧`.

This is the comparison behind the skein exact sequence of the Khovanov complex, in which the
complex of `D` is assembled from the complexes of its two resolutions at `c` and the saddle map
between them (`TauCeti.PDCode.khovanovBracketMappingConeIso`).

## Main definitions

All in the namespace `TauCeti.PDCode`:

* `resolveCrossingVertex c t S`: the vertex of the cube of `D` over the vertex `S` of the cube of
  its resolution at `c` with smoothing `t`.
* `resolveCrossingCubeCircleEquiv D c t S`: the circles of the resolution of `D` at `c` smoothed
  by `S`, as the circles of `D` smoothed at the vertex `resolveCrossingVertex c t S`.
* `resolveCrossingCubeIso D c t hD hDt R hj`: the cube of resolutions of
  `D.resolveCrossing c t` in quantum degree `j'` is the face of the cube of `D` in quantum
  degree `j = j'` (for `t = true`) or `j = j' + 1` (for `t = false`).

## Main results

* `reindex_resolveCrossingResolvedCircleEquiv_resolutionEdgeMap`: reindexing along the circles of
  a vertex resolution commutes with the saddle maps in the directions of the other crossings.
* `resolveCrossingCubeIso_hom_app_comp_resolutionCubeι`: the identification of the faces
  reindexes the circle tensor of each vertex along `resolveCrossingCubeCircleEquiv`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.1.
-/

public section

noncomputable section

open CategoryTheory Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode (n + 1)) (c : Fin (n + 1)) (t : Bool)

/-! ### Saddle maps of a resolution -/

section Edge

variable {s s' : Fin n → Bool} {i : Fin n}
  (hss' : ∀ j, j ≠ i → s j = s' j) (hi : s i ≠ s' i)
  (hDss' : ∀ j, j ≠ c.succAbove i →
    (c.insertNth t s : Fin (n + 1) → Bool) j = (c.insertNth t s' : Fin (n + 1) → Bool) j)
  (hDi : (c.insertNth t s : Fin (n + 1) → Bool) (c.succAbove i) ≠
    (c.insertNth t s' : Fin (n + 1) → Bool) (c.succAbove i))
  (R : Type u) [CommSemiring R]

/-- Reindexing along the circles of a resolution commutes with the merge at another crossing:
the merge of `D.resolveCrossing c t` at its crossing `i` is the merge of `D` at
`c.succAbove i`. -/
theorem reindex_resolveCrossingResolvedCircleEquiv_resolutionMergeMap
    (hs : #((D.resolveCrossing c t).circlesAt s i) = 2)
    (hDs : #(D.circlesAt (c.insertNth t s) (c.succAbove i)) = 2)
    (x : Khovanov.CircleTensor R ((D.resolveCrossing c t).ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) (D.resolveCrossingResolvedCircleEquiv c t s')
        ((D.resolveCrossing c t).resolutionMergeMap hss' hi hs R x) =
      D.resolutionMergeMap hDss' hDi hDs R
        (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingResolvedCircleEquiv c t s) x) := by
  rw [resolutionMergeMap_def, resolutionMergeMap_def]
  exact reindex_fiberwiseMul _ _ (funext <|
    D.resolveCrossingResolvedCircleEquiv_saddleResolvedCircleMap c t hss'
      ((D.resolveCrossing c t).card_circlesAt_eq_one_of_card_circlesAt_eq_two hss' hi hs) hDss'
      (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hDss' hDi hDs)) x

/-- Reindexing along the circles of a resolution commutes with the split at another crossing:
the split of `D.resolveCrossing c t` at its crossing `i` is the split of `D` at
`c.succAbove i`. -/
theorem reindex_resolveCrossingResolvedCircleEquiv_resolutionSplitMap
    (hs' : #((D.resolveCrossing c t).circlesAt s' i) = 2)
    (hDs' : #(D.circlesAt (c.insertNth t s') (c.succAbove i)) = 2)
    (x : Khovanov.CircleTensor R ((D.resolveCrossing c t).ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) (D.resolveCrossingResolvedCircleEquiv c t s')
        ((D.resolveCrossing c t).resolutionSplitMap hss' hi hs' R x) =
      D.resolutionSplitMap hDss' hDi hDs' R
        (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingResolvedCircleEquiv c t s) x) := by
  -- The split is along the saddle correspondence from `s'` to `s`.
  rw [resolutionSplitMap_def, resolutionSplitMap_def]
  exact Khovanov.reindex_fiberwiseSplit _ _ (funext <|
    D.resolveCrossingResolvedCircleEquiv_saddleResolvedCircleMap c t (fun j hj ↦ (hss' j hj).symm)
      ((D.resolveCrossing c t).card_circlesAt_eq_one_of_card_circlesAt_eq_two
        (fun j hj ↦ (hss' j hj).symm) hi.symm hs')
      (fun j hj ↦ (hDss' j hj).symm)
      (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hDss' j hj).symm) hDi.symm
        hDs')) x

/-- **Saddle maps commute with resolving another crossing.** Reindexing along the circles of a
resolution carries the saddle map of `D.resolveCrossing c t` at its crossing `i` to the saddle
map of `D` at `c.succAbove i`. Every crossing-free and detached circle is retained. -/
theorem reindex_resolveCrossingResolvedCircleEquiv_resolutionEdgeMap
    (h : #((D.resolveCrossing c t).circlesAt s i) = 2 ∨
      #((D.resolveCrossing c t).circlesAt s' i) = 2)
    (hD₂ : #(D.circlesAt (c.insertNth t s) (c.succAbove i)) = 2 ∨
      #(D.circlesAt (c.insertNth t s') (c.succAbove i)) = 2)
    (x : Khovanov.CircleTensor R ((D.resolveCrossing c t).ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) (D.resolveCrossingResolvedCircleEquiv c t s')
        ((D.resolveCrossing c t).resolutionEdgeMap hss' hi h R x) =
      D.resolutionEdgeMap hDss' hDi hD₂ R
        (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingResolvedCircleEquiv c t s) x) := by
  by_cases hs : #((D.resolveCrossing c t).circlesAt s i) = 2
  · have hDs : #(D.circlesAt (c.insertNth t s) (c.succAbove i)) = 2 :=
      D.card_circlesAt_resolveCrossing c t s i ▸ hs
    rw [(D.resolveCrossing c t).resolutionEdgeMap_eq_resolutionMergeMap hss' hi h R hs,
      D.resolutionEdgeMap_eq_resolutionMergeMap hDss' hDi hD₂ R hDs, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    exact D.reindex_resolveCrossingResolvedCircleEquiv_resolutionMergeMap c t hss' hi hDss' hDi R
      hs hDs x
  · have hs' := h.resolve_left hs
    have hDs' : #(D.circlesAt (c.insertNth t s') (c.succAbove i)) = 2 :=
      D.card_circlesAt_resolveCrossing c t s' i ▸ hs'
    rw [(D.resolveCrossing c t).resolutionEdgeMap_eq_resolutionSplitMap hss' hi h R hs',
      D.resolutionEdgeMap_eq_resolutionSplitMap hDss' hDi hD₂ R hDs']
    exact D.reindex_resolveCrossingResolvedCircleEquiv_resolutionSplitMap c t hss' hi hDss' hDi R
      hs' hDs' x

end Edge

/-! ### The vertices of a face -/

section Vertex

variable {D}

/-- The vertex of the cube of resolutions of a code with `n + 1` crossings lying over the vertex
`S` of the cube of its resolution at the crossing `c` with smoothing `t`: the crossings of `S`,
renumbered by `c.succAbove`, together with `c` itself when `t` is the `B`-smoothing `false`. -/
def resolveCrossingVertex (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  bif t then S.map c.succAboveEmb else insert c (S.map c.succAboveEmb)

/-- On the `A`-face, the vertex over `S` is the image of `S`. -/
@[simp]
theorem resolveCrossingVertex_true (S : Finset (Fin n)) :
    resolveCrossingVertex c true S = S.map c.succAboveEmb :=
  (rfl)

/-- On the `B`-face, the vertex over `S` is the image of `S` together with `c`. -/
@[simp]
theorem resolveCrossingVertex_false (S : Finset (Fin n)) :
    resolveCrossingVertex c false S = insert c (S.map c.succAboveEmb) :=
  (rfl)

/-- The crossing `c.succAbove a` lies in the vertex over `S` exactly when `a` lies in `S`. -/
@[simp]
theorem succAbove_mem_resolveCrossingVertex_iff {S : Finset (Fin n)} {a : Fin n} :
    c.succAbove a ∈ resolveCrossingVertex c t S ↔ a ∈ S := by
  cases t <;> simp [Fin.succAbove_ne]

/-- The crossing `c` lies in the vertex over `S` exactly on the `B`-face. -/
@[simp]
theorem mem_resolveCrossingVertex_self_iff {S : Finset (Fin n)} :
    c ∈ resolveCrossingVertex c t S ↔ t = false := by
  cases t <;> simp

/-- The state of the vertex over `S` is the state of `S` with the smoothing `t` inserted at
`c`. -/
@[simp]
theorem cubeState_resolveCrossingVertex (S : Finset (Fin n)) :
    cubeState (resolveCrossingVertex c t S) = c.insertNth t (cubeState S) := by
  funext j
  obtain rfl | ⟨k, rfl⟩ := c.eq_self_or_eq_succAbove j
  · cases t <;> simp [cubeState_apply]
  · simp [cubeState_apply]

/-- The vertex over `S` has as many crossings as `S` on the `A`-face and one more on the
`B`-face. -/
@[simp]
theorem card_resolveCrossingVertex (S : Finset (Fin n)) :
    #(resolveCrossingVertex c t S) = #S + bif t then 0 else 1 := by
  cases t
  · simp [card_insert_of_notMem, Fin.succAbove_ne]
  · simp

/-- Adding a crossing to a vertex of the cube of the resolution adds the corresponding crossing
to the vertex over it. -/
@[simp]
theorem resolveCrossingVertex_insert (S : Finset (Fin n)) (a : Fin n) :
    resolveCrossingVertex c t (insert a S) = insert (c.succAbove a) (resolveCrossingVertex c t S) :=
  by cases t <;> simp [map_insert, insert_comm]

/-- The vertex over `S` is monotone in `S`. -/
theorem monotone_resolveCrossingVertex : Monotone (resolveCrossingVertex (n := n) c t) :=
  fun S T h ↦ by cases t <;> simp [map_subset_map.2 h, insert_subset_insert]

/-- An edge of the cube of the resolution lies over an edge of the cube of `D`. -/
theorem covBy_resolveCrossingVertex {S T : Finset (Fin n)} (h : S ⋖ T) :
    resolveCrossingVertex c t S ⋖ resolveCrossingVertex c t T := by
  obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
  rw [resolveCrossingVertex_insert]
  exact covBy_insert (by simpa using ha)

/-- The vertex over `S` on the `A`-face is contained in the vertex over `S` on the `B`-face, which
also contains `c`: the edge between them is the edge of the cube of `D` in the direction of `c`. -/
theorem resolveCrossingVertex_true_subset_false (S : Finset (Fin n)) :
    resolveCrossingVertex c true S ⊆ resolveCrossingVertex c false S := by
  simp [subset_insert]

end Vertex

/-! ### The circles of a face -/

/-- The circles of the resolution of `D` at `c` smoothed at the vertex `S`, as the circles of `D`
smoothed at the vertex over `S`. This is `TauCeti.PDCode.resolveCrossingResolvedCircleEquiv`, read
at the state of the vertex over `S`. -/
def resolveCrossingCubeCircleEquiv (S : Finset (Fin n)) :
    (D.resolveCrossing c t).ResolvedCircle (cubeState S) ≃
      D.ResolvedCircle (cubeState (resolveCrossingVertex c t S)) :=
  (D.resolveCrossingResolvedCircleEquiv c t (cubeState S)).trans
    (Equiv.cast (congrArg D.ResolvedCircle (cubeState_resolveCrossingVertex c t S).symm))

/-- Reading a circle through a half-edge at an equal state does not change it. -/
private theorem cast_inl_mk {u v : Fin (n + 1) → Bool} (h : u = v) (x : Fin (4 * (n + 1))) :
    Equiv.cast (congrArg D.ResolvedCircle h) (.inl ⟦x⟧) = .inl ⟦x⟧ := by
  subst h
  rfl

/-- Reading a crossing-free circle at an equal state does not change it. -/
private theorem cast_inr {u v : Fin (n + 1) → Bool} (h : u = v)
    (i : Fin D.crossinglessComponentCount) :
    Equiv.cast (congrArg D.ResolvedCircle h) (.inr i) = .inr i := by
  subst h
  rfl

/-- The circle of the resolution through the half-edge in slot `k` of its crossing `i` is the
circle of `D` through the half-edge in slot `k` of the crossing `c.succAbove i`. -/
@[simp]
theorem resolveCrossingCubeCircleEquiv_inl_mk (S : Finset (Fin n)) (i : Fin n) (k : Fin 4) :
    D.resolveCrossingCubeCircleEquiv c t S (.inl ⟦crossingSlotEquiv n (i, k)⟧) =
      .inl ⟦D.crossing (c.succAbove i) k⟧ := by
  rw [resolveCrossingCubeCircleEquiv, Equiv.trans_apply,
    resolveCrossingResolvedCircleEquiv_inl_mk,
    cast_inl_mk D (cubeState_resolveCrossingVertex c t S).symm]

/-- The crossing-free circles of `D` keep their labels at every vertex of the face. -/
@[simp]
theorem resolveCrossingCubeCircleEquiv_inr_castAdd (S : Finset (Fin n))
    (i : Fin D.crossinglessComponentCount) :
    D.resolveCrossingCubeCircleEquiv c t S
        (.inr ((Fin.castAdd (D.detachedCircleCount c t) i).cast
          (D.resolveCrossing_crossinglessComponentCount c t).symm)) = .inr i := by
  rw [resolveCrossingCubeCircleEquiv, Equiv.trans_apply,
    resolveCrossingResolvedCircleEquiv_inr_castAdd,
    cast_inr D (cubeState_resolveCrossingVertex c t S).symm]

/-- The detached circle with index `j` is the circle of `D` through slot `0` of `c` when `j = 0`
and the arc of `D` at slot `0` returns to its smoothing partner, and through slot `2`
otherwise. -/
@[simp]
theorem resolveCrossingCubeCircleEquiv_inr_natAdd (S : Finset (Fin n))
    (j : Fin (D.detachedCircleCount c t)) :
    D.resolveCrossingCubeCircleEquiv c t S
        (.inr ((Fin.natAdd D.crossinglessComponentCount j).cast
          (D.resolveCrossing_crossinglessComponentCount c t).symm)) =
      .inl ⟦D.crossing c (if (j : ℕ) = 0 ∧ D.edgePair.val (D.crossing c 0) =
          D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 0)
        then 0 else 2)⟧ := by
  rw [resolveCrossingCubeCircleEquiv, Equiv.trans_apply,
    resolveCrossingResolvedCircleEquiv_inr_natAdd,
    cast_inl_mk D (cubeState_resolveCrossingVertex c t S).symm]

/-- `TauCeti.PDCode.reindex_resolveCrossingResolvedCircleEquiv_resolutionEdgeMap`, with the
circles of `D` read at states `u` and `u'` equal to those of the two vertices. -/
private theorem reindex_cast_resolutionEdgeMap {s s' : Fin n → Bool} {u u' : Fin (n + 1) → Bool}
    (hu : c.insertNth t s = u) (hu' : c.insertNth t s' = u') {i : Fin n}
    (hss' : ∀ j, j ≠ i → s j = s' j) (hi : s i ≠ s' i)
    (h : #((D.resolveCrossing c t).circlesAt s i) = 2 ∨
      #((D.resolveCrossing c t).circlesAt s' i) = 2)
    (huu' : ∀ j, j ≠ c.succAbove i → u j = u' j) (hui : u (c.succAbove i) ≠ u' (c.succAbove i))
    (hu₂ : #(D.circlesAt u (c.succAbove i)) = 2 ∨ #(D.circlesAt u' (c.succAbove i)) = 2)
    (R : Type u) [CommSemiring R]
    (x : Khovanov.CircleTensor R ((D.resolveCrossing c t).ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) ((D.resolveCrossingResolvedCircleEquiv c t s').trans
        (Equiv.cast (congrArg D.ResolvedCircle hu')))
        ((D.resolveCrossing c t).resolutionEdgeMap hss' hi h R x) =
      D.resolutionEdgeMap huu' hui hu₂ R
        (reindex R (fun _ ↦ R[ε]) ((D.resolveCrossingResolvedCircleEquiv c t s).trans
          (Equiv.cast (congrArg D.ResolvedCircle hu))) x) := by
  subst hu hu'
  simpa only [Equiv.cast_refl, Equiv.trans_refl] using
    D.reindex_resolveCrossingResolvedCircleEquiv_resolutionEdgeMap c t hss' hi huu' hui R h hu₂ x

/-! ### The faces of the cube of resolutions -/

section Cube

variable (hD : D.IsPlanar) (hDt : (D.resolveCrossing c t).IsPlanar) (R : Type u) [CommRing R]
  {j j' : ℤ} (hj : j' + (bif t then 0 else 1) = j)

include hj in
/-- The vertex `S` of the cube of the resolution in quantum degree `j'` and the vertex over `S` of
the cube of `D` in quantum degree `j` are pieces of the same degree. -/
private theorem sub_card_resolveCrossingVertex (S : Finset (Fin n)) :
    j' - #S = j - #(resolveCrossingVertex c t S) := by
  rw [card_resolveCrossingVertex, ← hj]
  cases t <;> simp only [Bool.cond_true, Bool.cond_false] <;> push_cast <;> ring

/-- The vertex `S` of the cube of the resolution, as the vertex over `S` of the cube of `D`. -/
private def resolveCrossingCubeLinearEquiv (S : Finset (Fin n)) :
    ((D.resolveCrossing c t).resolutionCube hDt R j').obj S ≃ₗ[R]
      (D.resolutionCube hD R j).obj (resolveCrossingVertex c t S) :=
  (D.resolveCrossing c t).resolutionCubeObjCongr hDt R j' hD
    (D.resolveCrossingCubeCircleEquiv c t S) (sub_card_resolveCrossingVertex c t hj S)

private theorem resolutionCubeι_resolveCrossingCubeLinearEquiv (S : Finset (Fin n))
    (x : ((D.resolveCrossing c t).resolutionCube hDt R j').obj S) :
    (D.resolutionCubeι hD R j (resolveCrossingVertex c t S)).hom
        (D.resolveCrossingCubeLinearEquiv c t hD hDt R hj S x) =
      reindex R (fun _ ↦ R[ε]) (D.resolveCrossingCubeCircleEquiv c t S)
        (((D.resolveCrossing c t).resolutionCubeι hDt R j' S).hom x) :=
  (D.resolveCrossing c t).resolutionCubeι_resolutionCubeObjCongr hDt R j' hD _ _ x

/-- The vertex identifications commute with the edge maps of the two cubes. -/
private theorem resolveCrossingCubeLinearEquiv_naturality {S T : Finset (Fin n)} (h : S ⋖ T) :
    ((D.resolveCrossing c t).resolutionCube hDt R j').map (homOfLE h.le) ≫
        (D.resolveCrossingCubeLinearEquiv c t hD hDt R hj T).toModuleIso.hom =
      (D.resolveCrossingCubeLinearEquiv c t hD hDt R hj S).toModuleIso.hom ≫
        ((monotone_resolveCrossingVertex c t).functor ⋙ D.resolutionCube hD R j).map
          (homOfLE h.le) := by
  obtain ⟨a, haS, rfl⟩ := h.exists_finset_insert
  have h' := covBy_resolveCrossingVertex c t h
  have haS' : c.succAbove a ∉ resolveCrossingVertex c t S := by simpa using haS
  have haT' : c.succAbove a ∈ resolveCrossingVertex c t (insert a S) := by simp
  have hst := cubeState_eq_of_covBy h' haS' haT'
  have hc := cubeState_ne_of_notMem_of_mem haS' haT'
  -- Both composites land in the circle tensor of the target vertex of `D`, where the edge maps
  -- of the two cubes are saddle maps and the vertex identifications are reindexings.
  rw [Functor.comp_map, Subsingleton.elim ((monotone_resolveCrossingVertex c t).functor.map
      (homOfLE h.le)) (homOfLE h'.le), ← cancel_mono (D.resolutionCubeι hD R j _),
    Category.assoc, Category.assoc, D.resolutionCube_map_homOfLE_comp_resolutionCubeι hD R j haS'
      (resolveCrossingVertex_insert c t S a).symm _ hst hc
      (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst hc)]
  ext x
  have e₀ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((D.resolveCrossing c t).resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hDt R j'
      haS)) x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at e₀
  simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [resolutionCubeι_resolveCrossingCubeLinearEquiv,
    resolutionCubeι_resolveCrossingCubeLinearEquiv, e₀]
  exact D.reindex_cast_resolutionEdgeMap c t (cubeState_resolveCrossingVertex c t S).symm
    (cubeState_resolveCrossingVertex c t (insert a S)).symm _ _ _ _ _ _ R _

include hj in
/-- **The faces of the cube of resolutions.** The cube of resolutions of the resolution
`D.resolveCrossing c t` in quantum degree `j'` is the face of the cube of resolutions of `D` at
which `c` has the smoothing `t`, in quantum degree `j`, where `j = j'` on the `A`-face and
`j = j' + 1` on the `B`-face. Its vertex `S` is the vertex `resolveCrossingVertex c t S`, and the
circle tensors are reindexed along `TauCeti.PDCode.resolveCrossingCubeCircleEquiv`
(`TauCeti.PDCode.resolveCrossingCubeIso_hom_app_comp_resolutionCubeι`). -/
def resolveCrossingCubeIso :
    (D.resolveCrossing c t).resolutionCube hDt R j' ≅
      (monotone_resolveCrossingVertex c t).functor ⋙ D.resolutionCube hD R j :=
  NatIso.ofComponents (fun S ↦ (D.resolveCrossingCubeLinearEquiv c t hD hDt R hj S).toModuleIso)
    fun f ↦ by
      simpa only [NatTrans.ofCubeEdges_app] using
        (NatTrans.ofCubeEdges (F := (D.resolveCrossing c t).resolutionCube hDt R j')
          (G := (monotone_resolveCrossingVertex c t).functor ⋙ D.resolutionCube hD R j)
          (fun S ↦ (D.resolveCrossingCubeLinearEquiv c t hD hDt R hj S).toModuleIso.hom)
          (fun _ _ h ↦ D.resolveCrossingCubeLinearEquiv_naturality c t hD hDt R hj h)).naturality f

include hj in
/-- The identification of the faces reindexes the circle tensor of each vertex along the
circles of the face. -/
@[reassoc]
theorem resolveCrossingCubeIso_hom_app_comp_resolutionCubeι (S : Finset (Fin n)) :
    (D.resolveCrossingCubeIso c t hD hDt R hj).hom.app S ≫
        D.resolutionCubeι hD R j (resolveCrossingVertex c t S) =
      (D.resolveCrossing c t).resolutionCubeι hDt R j' S ≫
        ModuleCat.ofHom
          (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingCubeCircleEquiv c t S)).toLinearMap := by
  ext x
  exact D.resolutionCubeι_resolveCrossingCubeLinearEquiv c t hD hDt R hj S x

end Cube

end TauCeti.PDCode
