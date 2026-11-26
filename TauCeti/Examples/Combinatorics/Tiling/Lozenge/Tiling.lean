/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Tiling

/-!
# Regression examples: lozenge tilings

Edge directions `1, 2, 3` are the indices `0, 1, 2` of `TriEdge.k`.

* **The unit hexagon.** The six faces `R₆` at the origin have exactly two tilings,
  `T_a = {(0,3), ((−1,0),1), ((0,−1),2)}` and `T_b = {(0,1), (0,2), ((−1,−1),3)}`, each with one
  lozenge of each type. A tiling of `R₆` only uses the six edges at the origin, each face of `R₆`
  contains two of them, and consecutive faces around the origin share one, so a tiling picks
  every other edge around the origin.
* **A single face.** `{W(0)}` has no tiling, and exactly three free tilings, one for each edge of
  `W(0)`.
* **Frozen tilings.** The configurations `M₁`, `M₂`, `M₃` of all edges of one direction are plane
  tilings, while `M₁ ∪ M₃` is not, since `W(0)` contains two of its edges.
* **Placed tiles.** The tiling `T_a` of the unit hexagon is the family of placed tiles of indices
  `3`, `1`, `2` at `0`, `(−1,0)`, `(0,−1)`, with face sets `{W(0), B(0)}`, `{W(−e₁), B(−e₃)}`,
  `{W(−e₃), B(−e₂)}`, which partition `R₆`. The placed tiles of `(0,1)` and `(0,3)` share the face
  `W(0)`, so no tiling contains both edges. A translation other than `0` fixes no face and no placed
  tile, so the stabilizer of each prototile is trivial, equal to its (trivial) symmetry group.
* **A wedge.** For `R = {W(0), W(−e₁)}` and `M = {(0,3), (0,2)}`, `M` is a free tiling of `R` but
  not a tiling: its lozenges `W(0) ∪ B(0)` and `W(−e₁) ∪ B(0)` share the face `B(0) ∉ R`. The
  region `R` is not of the form `Faces(V)`, since the three vertices of `B(0)` are vertices of `R`.
-/

public section

namespace TauCeti.Examples.LozengeTiling

open TauCeti
open scoped Pointwise

/-! ### The unit hexagon -/

/-- The unit hexagon `R₆`: the six faces at the origin. -/
abbrev hexagon : Set TriFace := ↑(vertexFaces (0, 0))

/-- The tiling `T_a = {(0,3), ((−1,0),1), ((0,−1),2)}` of the unit hexagon. -/
def tilingA : Set TriEdge := {⟨(0, 0), 2⟩, ⟨(-1, 0), 0⟩, ⟨(0, -1), 1⟩}

/-- The tiling `T_b = {(0,1), (0,2), ((−1,−1),3)}` of the unit hexagon. -/
def tilingB : Set TriEdge := {⟨(0, 0), 0⟩, ⟨(0, 0), 1⟩, ⟨(-1, -1), 2⟩}

/-- An edge of a tiling of the unit hexagon is one of the six edges at the origin. -/
private theorem mem_edgesAtZero_of_isTiling {M : Set TriEdge} (h : IsTiling hexagon M)
    {e : TriEdge} (he : e ∈ M) :
    e = ⟨(0, 0), 0⟩ ∨ e = ⟨(0, 0), 1⟩ ∨ e = ⟨(0, 0), 2⟩ ∨ e = ⟨(-1, 0), 0⟩ ∨
      e = ⟨(0, -1), 1⟩ ∨ e = ⟨(-1, -1), 2⟩ := by
  have hw := h.whiteFace_mem he
  have hb := h.blackFace_mem he
  obtain ⟨⟨a, b⟩, k⟩ := e
  fin_cases k <;> simp [vertexFaces_def, Prod.ext_iff] at hw hb ⊢ <;> omega

/-- In a tiling of the unit hexagon, a face `f` of `R₆` whose only edges at the origin are `x` and
`y` contains exactly one of `x` and `y`. The hypothesis is a finite check, closed by `simp`. -/
private theorem mem_iff_notMem_of_isTiling {M : Set TriEdge} (h : IsTiling hexagon M)
    (f : TriFace) (x y : TriEdge)
    (hf : f ∈ vertexFaces (0, 0) ∧ x ∈ f.edges ∧ y ∈ f.edges ∧ x ≠ y ∧ ∀ e ∈ f.edges,
      (e = ⟨(0, 0), 0⟩ ∨ e = ⟨(0, 0), 1⟩ ∨ e = ⟨(0, 0), 2⟩ ∨ e = ⟨(-1, 0), 0⟩ ∨
        e = ⟨(0, -1), 1⟩ ∨ e = ⟨(-1, -1), 2⟩) → e = x ∨ e = y) : x ∈ M ↔ y ∉ M := by
  obtain ⟨hf, hx, hy, hxy, hall⟩ := hf
  obtain ⟨e₀, ⟨he₀, he₀f⟩, hu⟩ := h.existsUnique hf
  constructor
  · exact fun hx' hy' => hxy ((hu x ⟨hx', hx⟩).trans (hu y ⟨hy', hy⟩).symm)
  · intro hy'
    rcases hall e₀ he₀f (mem_edgesAtZero_of_isTiling h he₀) with rfl | rfl
    · exact he₀
    · exact absurd he₀ hy'

/-- A tiling of the unit hexagon is `T_a` or `T_b`. -/
theorem eq_tilingA_or_eq_tilingB {M : Set TriEdge} (h : IsTiling hexagon M) :
    M = tilingA ∨ M = tilingB := by
  -- the six faces around the origin, each with its two edges at the origin
  have h1 := mem_iff_notMem_of_isTiling h ⟨(0, 0), true⟩ ⟨(0, 0), 0⟩ ⟨(0, 0), 2⟩
    (by simp [vertexFaces_def])
  have h2 := mem_iff_notMem_of_isTiling h ⟨(0, 0), false⟩ ⟨(0, 0), 1⟩ ⟨(0, 0), 2⟩
    (by simp [vertexFaces_def])
  have h3 := mem_iff_notMem_of_isTiling h ⟨(-1, 0), true⟩ ⟨(-1, 0), 0⟩ ⟨(0, 0), 1⟩
    (by simp [vertexFaces_def])
  have h4 := mem_iff_notMem_of_isTiling h ⟨(-1, -1), false⟩ ⟨(-1, 0), 0⟩ ⟨(-1, -1), 2⟩
    (by simp [vertexFaces_def])
  have h5 := mem_iff_notMem_of_isTiling h ⟨(-1, -1), true⟩ ⟨(0, -1), 1⟩ ⟨(-1, -1), 2⟩
    (by simp [vertexFaces_def])
  have h6 := mem_iff_notMem_of_isTiling h ⟨(0, -1), false⟩ ⟨(0, -1), 1⟩ ⟨(0, 0), 0⟩
    (by simp [vertexFaces_def])
  by_cases hc : (⟨(0, 0), 2⟩ : TriEdge) ∈ M
  · left
    ext e
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rcases mem_edgesAtZero_of_isTiling h he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [tilingA] <;> tauto
    · simp only [tilingA, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;> tauto
  · right
    ext e
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rcases mem_edgesAtZero_of_isTiling h he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [tilingB] <;> tauto
    · simp only [tilingB, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;> tauto

/-- A finite set of edges whose faces lie in `R₆`, and which meets each face of `R₆` in exactly
one edge, is a tiling of the unit hexagon. Both hypotheses are finite checks, closed by `simp`. -/
private theorem isTiling_hexagon_of_card_filter {M : Finset TriEdge}
    (hM : ∀ e ∈ M, e.faces ⊆ vertexFaces (0, 0))
    (hu : ∀ f ∈ vertexFaces (0, 0), (M.filter (· ∈ f.edges)).card = 1) :
    IsTiling hexagon M := by
  refine isTiling_def.2 ⟨fun e he f hef => hM e he (TriEdge.mem_faces.2 hef), fun f hf => ?_⟩
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 (hu f hf)
  have hmem (y : TriEdge) : y ∈ M ∧ y ∈ f.edges ↔ y = e := by
    simpa using Finset.ext_iff.1 he y
  exact ⟨e, (hmem e).2 rfl, fun y hy => (hmem y).1 hy⟩

/-- `T_a` is a tiling of the unit hexagon. -/
theorem isTiling_tilingA : IsTiling hexagon tilingA := by
  simpa [tilingA] using isTiling_hexagon_of_card_filter
    (M := {⟨(0, 0), 2⟩, ⟨(-1, 0), 0⟩, ⟨(0, -1), 1⟩})
    (by simp [vertexFaces_def, TriEdge.faces_def, Finset.insert_subset_iff])
    (by simp [vertexFaces_def, Finset.filter_insert, Finset.filter_singleton])

/-- `T_b` is a tiling of the unit hexagon. -/
theorem isTiling_tilingB : IsTiling hexagon tilingB := by
  simpa [tilingB] using isTiling_hexagon_of_card_filter
    (M := {⟨(0, 0), 0⟩, ⟨(0, 0), 1⟩, ⟨(-1, -1), 2⟩})
    (by simp [vertexFaces_def, TriEdge.faces_def, Finset.insert_subset_iff])
    (by simp [vertexFaces_def, Finset.filter_insert, Finset.filter_singleton])

/-- **The unit hexagon has exactly two tilings**, `T_a` and `T_b`. -/
theorem isTiling_hexagon_iff {M : Set TriEdge} :
    IsTiling hexagon M ↔ M = tilingA ∨ M = tilingB :=
  ⟨eq_tilingA_or_eq_tilingB, by rintro (rfl | rfl); exacts [isTiling_tilingA, isTiling_tilingB]⟩

/-- Each of `T_a` and `T_b` has one lozenge of each type. -/
example : (∀ k : Fin 3, ∃! e, e ∈ tilingA ∧ e.k = k) ∧
    ∀ k : Fin 3, ∃! e, e ∈ tilingB ∧ e.k = k := by
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k <;>
  · refine existsUnique_of_exists_of_unique ?_ ?_
    · simp [tilingA, tilingB]
    · rintro y₁ y₂ ⟨hy₁, hk₁⟩ ⟨hy₂, hk₂⟩
      simp only [tilingA, tilingB, Set.mem_insert_iff, Set.mem_singleton_iff] at hy₁ hy₂
      rcases hy₁ with rfl | rfl | rfl <;> rcases hy₂ with rfl | rfl | rfl <;> simp_all

/-! ### A single face -/

/-- The white face `W(0)`. -/
abbrev white₀ : TriFace := ⟨(0, 0), true⟩

/-- `{W(0)}` has no tiling: an edge of a tiling has both its faces in the region. -/
theorem not_isTiling_white₀ (M : Set TriEdge) : ¬ IsTiling {white₀} M := by
  intro h
  obtain ⟨e, ⟨he, -⟩, -⟩ := h.existsUnique (f := white₀) rfl
  have hw := h.whiteFace_mem he
  have hb := h.blackFace_mem he
  rw [Set.mem_singleton_iff] at hw hb
  exact e.whiteFace_ne_blackFace (hw.trans hb.symm)

/-- `{W(0)}` has exactly three free tilings, one for each edge of `W(0)`. -/
theorem isFreeTiling_white₀_iff {M : Set TriEdge} :
    IsFreeTiling {white₀} M ↔ ∃ e ∈ white₀.edges, M = {e} := by
  constructor
  · intro h
    obtain ⟨hsub, hu⟩ := isFreeTiling_def.1 h
    obtain ⟨e, ⟨he, hef⟩, huniq⟩ := hu white₀ rfl
    refine ⟨e, hef, Set.eq_singleton_iff_unique_mem.2 ⟨he, fun e' he' => huniq e' ⟨he', ?_⟩⟩⟩
    obtain ⟨f, hf, he'f⟩ := mem_regionEdges.1 (hsub he')
    rwa [Set.mem_singleton_iff.1 hf] at he'f
  · rintro ⟨e, he, rfl⟩
    refine isFreeTiling_def.2
      ⟨Set.singleton_subset_iff.2 (mem_regionEdges.2 ⟨white₀, rfl, he⟩), fun f hf => ?_⟩
    rw [Set.mem_singleton_iff.1 hf]
    exact ⟨e, ⟨rfl, he⟩, fun e' he' => he'.1⟩

/-- `W(0)` has three edges, so `{W(0)}` has three free tilings. -/
example : white₀.edges.card = 3 := TriFace.card_edges _

/-! ### Frozen tilings -/

/-- The configuration `M_{k+1}` of all edges of direction `k + 1` is a plane tiling: every face
contains exactly one edge of each direction. -/
theorem isTiling_frozen (k : Fin 3) : IsTiling Set.univ {e : TriEdge | e.k = k} := by
  refine isTiling_univ_iff.2 fun f => ⟨f.edge k, ⟨TriFace.edge_k f k, f.edge_mem_edges k⟩, ?_⟩
  rintro e ⟨rfl, he⟩
  exact (TriFace.mem_edges_iff_edge_eq.1 he).symm

/-- `M₁ ∪ M₃` is not a plane tiling, since `W(0)` contains two of its edges. -/
theorem not_isTiling_frozen_union :
    ¬ IsTiling Set.univ ({e : TriEdge | e.k = 0} ∪ {e | e.k = 2}) := by
  intro h
  have := h.eq_of_mem_edges (f := white₀) (e := ⟨(0, 0), 0⟩) (e' := ⟨(0, 0), 2⟩)
    (Or.inl rfl) (Or.inr rfl) (by simp) (by simp)
  simp at this

/-! ### Placed tiles -/

/-- The placed tiles of `(0,1)` and `(0,3)` share the face `W(0)`. -/
theorem white₀_mem_toPlacedTile :
    white₀ ∈ (⟨(0, 0), 0⟩ : TriEdge).toPlacedTile ∧ white₀ ∈ (⟨(0, 0), 2⟩ : TriEdge).toPlacedTile :=
  ⟨by simp, by simp⟩

/-- No tiling contains both `(0,1)` and `(0,3)`, since both edges lie in `W(0)`. -/
theorem not_mem_and_mem_of_isTiling {R : Set TriFace} {M : Set TriEdge} (h : IsTiling R M) :
    ¬ ((⟨(0, 0), 0⟩ : TriEdge) ∈ M ∧ (⟨(0, 0), 2⟩ : TriEdge) ∈ M) := fun hM => by
  have := h.eq_of_mem_edges (f := white₀) hM.1 hM.2 (by simp) (by simp)
  simp at this

/-- The tiling `T_a` is the family of placed tiles of indices `3`, `1`, `2` (the `Fin 3` indices
`2`, `0`, `1`) at `0`, `(−1,0)`, `(0,−1)`. -/
theorem toPlacedTile_image_tilingA : TriEdge.toPlacedTile '' tilingA =
    {⟨2, (Multiplicative.ofAdd ((0, 0) : ℤ × ℤ) : Multiplicative (ℤ × ℤ))⟩,
      ⟨0, (Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ) : Multiplicative (ℤ × ℤ))⟩,
      ⟨1, (Multiplicative.ofAdd ((0, -1) : ℤ × ℤ) : Multiplicative (ℤ × ℤ))⟩} := by
  simp [tilingA, Set.image_insert_eq, TriEdge.toPlacedTile_def]

/-- The face sets of the placed tiles of `T_a`: `{W(0), B(0)}`, `{W(−e₁), B(−e₃)}` and
`{W(−e₃), B(−e₂)}`. -/
theorem coe_toPlacedTile_tilingA :
    ((⟨(0, 0), 2⟩ : TriEdge).toPlacedTile : Set TriFace) = {⟨(0, 0), true⟩, ⟨(0, 0), false⟩} ∧
    ((⟨(-1, 0), 0⟩ : TriEdge).toPlacedTile : Set TriFace) =
      {⟨(-1, 0), true⟩, ⟨(-1, -1), false⟩} ∧
    ((⟨(0, -1), 1⟩ : TriEdge).toPlacedTile : Set TriFace) =
      {⟨(-1, -1), true⟩, ⟨(0, -1), false⟩} := by
  simp [TriEdge.faces_def]

/-- The placed tiles of `T_a` partition the unit hexagon. -/
theorem placedTiles_tilingA_partition :
    tilingA.PairwiseDisjoint (fun e => (e.toPlacedTile : Set TriFace)) ∧
      ⋃ e ∈ tilingA, (e.toPlacedTile : Set TriFace) = hexagon := by
  obtain ⟨hsub, hdisj, hcov⟩ := isTiling_iff_placedTile.1 isTiling_tilingA
  exact ⟨hdisj, (Set.iUnion₂_subset hsub).antisymm hcov⟩

/-- A translation fixing a face is trivial. -/
theorem eq_one_of_smul_face_eq {g : Multiplicative (ℤ × ℤ)} {f : TriFace} (h : g • f = f) :
    g = 1 := by
  obtain ⟨w, rfl⟩ : ∃ w, Multiplicative.ofAdd w = g := ⟨g.toAdd, rfl⟩
  rw [ofAdd_smul, TriFace.vadd_eq_self_iff] at h
  simp [h]

/-- Translations act freely on placed tiles: a translation fixing a placed tile is trivial, since
it then fixes a face of it. -/
theorem eq_one_of_smul_placedTile_eq {g : Multiplicative (ℤ × ℤ)}
    {pt : DiscreteTiling.PlacedTile lozengeProtoset} (h : g • pt = pt) : g = 1 := by
  obtain ⟨e, rfl⟩ := TriEdge.toPlacedTile_bijective.2 pt
  obtain ⟨w, rfl⟩ : ∃ w, Multiplicative.ofAdd w = g := ⟨g.toAdd, rfl⟩
  rw [← TriEdge.toPlacedTile_vadd, TriEdge.toPlacedTile_bijective.1.eq_iff,
    TriEdge.vadd_eq_self_iff] at h
  simp [h]

/-- The stabilizer of each prototile of `lozengeProtoset` is trivial, so its trivial symmetry group
is the whole stabilizer. -/
theorem stabilizer_lozengeProtoset (k : Fin 3) :
    MulAction.stabilizer (Multiplicative (ℤ × ℤ)) (lozengeProtoset k : Set TriFace) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  have hmem : (⟨0, k⟩ : TriEdge).whiteFace ∈ (lozengeProtoset k : Set TriFace) := by
    simp [TriEdge.faces_def]
  have hg' : g • (lozengeProtoset k : Set TriFace) = lozengeProtoset k := hg
  rw [← hg'] at hmem
  obtain ⟨f, hf, hgf⟩ := hmem
  obtain ⟨w, rfl⟩ : ∃ w, Multiplicative.ofAdd w = g := ⟨g.toAdd, rfl⟩
  change w +ᵥ f = _ at hgf
  have hf' : f = (⟨0, k⟩ : TriEdge).whiteFace ∨ f = (⟨0, k⟩ : TriEdge).blackFace := by
    simpa [TriEdge.faces_def] using hf
  obtain ⟨w₁, w₂⟩ := w
  rcases hf' with rfl | rfl <;> fin_cases k <;>
    simp [TriFace.ext_iff, Prod.ext_iff] at hgf <;> simp [Prod.ext_iff] <;> omega

/-! ### A wedge -/

/-- The wedge `R = {W(0), W(−e₁)}`. -/
abbrev wedge : Set TriFace := {⟨(0, 0), true⟩, ⟨(-1, 0), true⟩}

/-- The configuration `M = {(0,3), (0,2)}`. -/
abbrev wedgeConfig : Set TriEdge := {⟨(0, 0), 2⟩, ⟨(0, 0), 1⟩}

/-- `M` is a free tiling of the wedge: `W(0)` contains only `(0,3)` and `W(−e₁)` only `(0,2)`. -/
theorem isFreeTiling_wedgeConfig : IsFreeTiling wedge wedgeConfig := by
  refine isFreeTiling_def.2 ⟨?_, ?_⟩
  · rintro e (rfl | rfl)
    · exact mem_regionEdges.2 ⟨⟨(0, 0), true⟩, by simp, by simp⟩
    · exact mem_regionEdges.2 ⟨⟨(-1, 0), true⟩, by simp, by simp⟩
  · rintro f (rfl | rfl)
    · refine ⟨⟨(0, 0), 2⟩, by simp, ?_⟩
      rintro e ⟨he, he'⟩
      rcases he with rfl | rfl <;> simp_all
    · refine ⟨⟨(0, 0), 1⟩, by simp, ?_⟩
      rintro e ⟨he, he'⟩
      rcases he with rfl | rfl <;> simp_all

/-- The lozenges of `(0,3)` and `(0,2)` share the face `B(0)`, which is not in the wedge. -/
theorem blackFace_mem_toPlacedTile_wedgeConfig :
    (⟨(0, 0), false⟩ : TriFace) ∈ (⟨(0, 0), 2⟩ : TriEdge).toPlacedTile ∧
      (⟨(0, 0), false⟩ : TriFace) ∈ (⟨(0, 0), 1⟩ : TriEdge).toPlacedTile ∧
      (⟨(0, 0), false⟩ : TriFace) ∉ wedge := by
  simp

/-- `M` is not a tiling of the wedge. -/
theorem not_isTiling_wedgeConfig : ¬ IsTiling wedge wedgeConfig := fun h =>
  blackFace_mem_toPlacedTile_wedgeConfig.2.2
    (h.mem_of_mem_edges (e := ⟨(0, 0), 2⟩) (by simp) (by simp))

/-- The wedge is not of the form `Faces(V)`: the three vertices of `B(0)` are vertices of it. -/
theorem wedge_ne_facesOf (V : Set (ℤ × ℤ)) : wedge ≠ facesOf V := by
  intro h
  have hV : regionVertices wedge ⊆ V := by
    intro u hu
    obtain ⟨f, hf, hu⟩ := mem_regionVertices.1 hu
    rw [h] at hf
    exact mem_facesOf.1 hf u hu
  have hB : (⟨(0, 0), false⟩ : TriFace) ∈ facesOf V := by
    refine mem_facesOf.2 fun u hu => ?_
    refine hV ?_
    simp only [TriFace.vertices_mk_false, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact mem_regionVertices.2 ⟨⟨(0, 0), true⟩, by simp, by simp⟩
    · exact mem_regionVertices.2 ⟨⟨(-1, 0), true⟩, by simp, by simp⟩
    · exact mem_regionVertices.2 ⟨⟨(0, 0), true⟩, by simp, by simp⟩
  rw [← h] at hB
  simp at hB

end TauCeti.Examples.LozengeTiling
