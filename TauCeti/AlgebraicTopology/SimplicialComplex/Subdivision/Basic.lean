/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Extension.Linear
public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex

import Mathlib.Order.Interval.Finset.Nat

/-!
# Barycentric subdivision of abstract simplicial complexes

The vertices of the first barycentric subdivision of a simplicial complex `K` are its faces, which
are always nonempty: `PreAbstractSimplicialComplex` requires its face collection to be a lower set
relative to `Finset.Nonempty`, so the empty face never occurs. A collection of these new vertices
spans a face exactly when the corresponding faces of `K` form a chain under inclusion.
Equivalently, the barycentric subdivision is the order complex of the face poset.

The construction is made for `PreAbstractSimplicialComplex`, since links, deletions, and collapse
subcomplexes need not contain every ambient singleton. Its result is an
`AbstractSimplicialComplex`: every face of the original complex is genuinely a vertex of the
subdivision. Simplicial maps act on face posets by taking vertexwise images, yielding the
functorial map `barycentricSubdivisionMap`.

The definition follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2,
"Derived Subdivisions". The realizations of a complex and of its subdivision are identified in
`Subdivision.Homeomorph`. The functoriality here is only at the level of abstract complexes: the
canonical identification of a subdivision's realization with the original realization is not
natural in arbitrary simplicial maps.

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision`: the order complex of the face
  poset.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.faceOrderHom`: the monotone map on face
  posets induced by a simplicial map.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricSubdivisionMap`: the induced
  simplicial map between barycentric subdivisions.
* `AbstractSimplicialComplex.subdivisionSubcomplex`: the barycentric subdivision of a
  subcomplex `P` of `K`, as a subcomplex of the barycentric subdivision of `K`.
* `AbstractSimplicialComplex.orderedBarycentricSubdivision`: the barycentric subdivision, with its
  vertices ordered by a linear extension of inclusion.
* `AbstractSimplicialComplex.subdivisionBarycenter`, `AbstractSimplicialComplex.lastVertexMap`: the
  barycenters of the faces of `K` in the ordered barycentric subdivision, and the simplicial map
  sending each face to its largest vertex.

## Main results

* `TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff`: the characteristic face
  criterion.
* `TauCeti.PreAbstractSimplicialComplex.pair_mem_barycentricSubdivision_iff`: two original faces
  span an edge exactly when one contains the other.
* `TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision`: subdivision does
  not increase the number of vertices of a face.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricSubdivisionMap_id` and
  `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricSubdivisionMap_comp`:
  functoriality laws.
-/

public section

open Finset Set

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {α β γ : Type*}

/-- The first **barycentric subdivision** of `K`: its vertices are the faces of `K`, and its faces
are the nonempty finite chains of faces under inclusion. -/
@[expose] noncomputable def barycentricSubdivision (K : PreAbstractSimplicialComplex α) :
    AbstractSimplicialComplex (SetLike.Face K) :=
  AbstractSimplicialComplex.orderComplex (SetLike.Face K)

/-- Barycentric subdivision is the order complex of the face poset. -/
theorem barycentricSubdivision_eq_orderComplex (K : PreAbstractSimplicialComplex α) :
    barycentricSubdivision K =
      AbstractSimplicialComplex.orderComplex (SetLike.Face K) :=
  rfl

variable {K : PreAbstractSimplicialComplex α}

/-- A collection of faces of `K` is a face of its barycentric subdivision exactly when it is
nonempty and totally ordered by inclusion. -/
@[simp]
theorem mem_barycentricSubdivision_iff {τ : Finset (SetLike.Face K)} :
    τ ∈ barycentricSubdivision K ↔
      τ.Nonempty ∧
        IsChain (· ≤ ·) (↑τ : Set (SetLike.Face K)) := by
  rw [barycentricSubdivision_eq_orderComplex,
    AbstractSimplicialComplex.mem_orderComplex_iff]

/-- A collection is a face of the barycentric subdivision exactly when it is nonempty and every
two original faces in the collection are nested. -/
theorem mem_barycentricSubdivision_iff' {ρ : Finset (SetLike.Face K)} :
    ρ ∈ barycentricSubdivision K ↔
      ρ.Nonempty ∧ ∀ σ ∈ ρ, ∀ τ ∈ ρ,
        (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ := by
  rw [barycentricSubdivision_eq_orderComplex,
    AbstractSimplicialComplex.mem_orderComplex_iff']
  simp only [SetLike.face_le_iff]

/-- Two faces of `K` span an edge in its barycentric subdivision exactly when one is contained in
the other.

This is not a `simp` lemma: `mem_barycentricSubdivision_iff` already rewrites the left-hand
side. -/
theorem pair_mem_barycentricSubdivision_iff [DecidableEq α] (σ τ : SetLike.Face K) :
    {σ, τ} ∈ barycentricSubdivision K ↔
      (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ := by
  rw [barycentricSubdivision_eq_orderComplex,
    AbstractSimplicialComplex.pair_mem_orderComplex_iff]
  simp only [SetLike.face_le_iff]

/-- Every two original faces occurring in one face of the barycentric subdivision are nested. -/
theorem subset_or_subset_of_mem_barycentricSubdivision
    {ρ : Finset (SetLike.Face K)}
    (hρ : ρ ∈ barycentricSubdivision K)
    {σ τ : SetLike.Face K}
    (hσ : σ ∈ ρ) (hτ : τ ∈ ρ) :
    (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ := by
  rw [barycentricSubdivision_eq_orderComplex] at hρ
  simpa only [SetLike.face_le_iff] using
    AbstractSimplicialComplex.le_or_le_of_mem_orderComplex hρ hσ hτ

/-- Barycentric subdivision does not increase the number of vertices of a face: if every face
of `K` has at most `D` vertices, so does every face of its barycentric subdivision. Distinct
members of a chain of nonempty faces have distinct cardinalities between `1` and `D`. -/
theorem card_le_of_mem_barycentricSubdivision {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D)
    {ρ : Finset (SetLike.Face K)} (hρ : ρ ∈ barycentricSubdivision K) : ρ.card ≤ D := by
  have hmaps : ∀ σ ∈ ρ, σ.val.card ∈ Finset.Icc 1 D := fun σ _ =>
    Finset.mem_Icc.2 ⟨Finset.card_pos.2 (K.isRelLowerSet_faces.prop_of_mem σ.property),
        hD σ.val σ.property⟩
  have hinj : Set.InjOn (fun σ : SetLike.Face K => σ.val.card) ρ := by
    intro σ hσ τ hτ hστ
    apply Subtype.ext
    rcases subset_or_subset_of_mem_barycentricSubdivision hρ hσ hτ with h | h
    · exact Finset.eq_of_subset_of_card_le h hστ.ge
    · exact (Finset.eq_of_subset_of_card_le h hστ.le).symm
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

namespace SimplicialMap

variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}
  {M : PreAbstractSimplicialComplex γ}

/-- A simplicial map induces a simplicial map between barycentric subdivisions by mapping every
face-vertex to its vertexwise image. -/
def barycentricSubdivisionMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    _root_.PreAbstractSimplicialComplex.SimplicialMap
      (barycentricSubdivision K).toPreAbstractSimplicialComplex
      (barycentricSubdivision L).toPreAbstractSimplicialComplex :=
  AbstractSimplicialComplex.orderComplexMap (faceOrderHom f)

/-- The subdivision map is the order-complex map induced by the map on face posets. -/
theorem barycentricSubdivisionMap_eq_orderComplexMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    barycentricSubdivisionMap f = AbstractSimplicialComplex.orderComplexMap (faceOrderHom f) :=
  (rfl)

theorem coe_barycentricSubdivisionMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    ⇑(barycentricSubdivisionMap f) = faceOrderHom f := by
  rw [barycentricSubdivisionMap_eq_orderComplexMap]
  exact AbstractSimplicialComplex.coe_orderComplexMap (faceOrderHom f)

@[simp]
theorem coe_barycentricSubdivisionMap_apply [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L)
    (σ : SetLike.Face K) :
    (barycentricSubdivisionMap f σ : Finset β) = σ.val.image f := by
  rw [← coe_faceOrderHom_apply, ← coe_barycentricSubdivisionMap]

/-- Barycentric subdivision sends the identity simplicial map to the identity simplicial map. -/
@[simp]
theorem barycentricSubdivisionMap_id [DecidableEq α] :
    barycentricSubdivisionMap (_root_.PreAbstractSimplicialComplex.SimplicialMap.id K) =
      _root_.PreAbstractSimplicialComplex.SimplicialMap.id
        (barycentricSubdivision K).toPreAbstractSimplicialComplex := by
  rw [barycentricSubdivisionMap_eq_orderComplexMap, faceOrderHom_id,
    AbstractSimplicialComplex.orderComplexMap_id]
  rfl

/-- Barycentric subdivision sends a composite of simplicial maps to the composite of their
induced maps. -/
@[simp]
theorem barycentricSubdivisionMap_comp [DecidableEq β] [DecidableEq γ]
    (g : _root_.PreAbstractSimplicialComplex.SimplicialMap L M)
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    barycentricSubdivisionMap (g.comp f) =
      (barycentricSubdivisionMap g).comp (barycentricSubdivisionMap f) := by
  rw [barycentricSubdivisionMap_eq_orderComplexMap, faceOrderHom_comp,
    AbstractSimplicialComplex.orderComplexMap_comp,
    barycentricSubdivisionMap_eq_orderComplexMap, barycentricSubdivisionMap_eq_orderComplexMap]
  rfl

end SimplicialMap

end PreAbstractSimplicialComplex

end TauCeti

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

/-- The barycentric subdivision of `P`, as a subcomplex of the barycentric subdivision of `K`:
the chains of faces of `K` all of whose members are faces of `P`. -/
def subdivisionSubcomplex : PreAbstractSimplicialComplex (TauCeti.SetLike.Face K) where
  faces := {ρ | ρ ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
    K.toPreAbstractSimplicialComplex ∧ ∀ σ ∈ ρ, σ.val ∈ P}
  isRelLowerSet_faces := by
    rintro ρ ⟨hρK, hρP⟩
    have h := (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).isRelLowerSet_faces
    exact ⟨h.prop_of_mem hρK, fun τ hτρ hτ => ⟨h.mem_of_le hρK hτρ hτ, fun σ hσ => hρP σ (hτρ hσ)⟩⟩

@[simp]
theorem mem_subdivisionSubcomplex_iff {ρ : Finset (TauCeti.SetLike.Face K)} :
    ρ ∈ K.subdivisionSubcomplex P ↔
      ρ ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex ∧ ∀ σ ∈ ρ, σ.val ∈ P :=
  Iff.rfl

end AbstractSimplicialComplex

noncomputable section

namespace AbstractSimplicialComplex

open TauCeti

variable {α : Type*} [LinearOrder α] (K : AbstractSimplicialComplex α)

/-- The **barycentric subdivision** of `K`, with its vertices, the faces of `K`, ordered by a linear
extension of inclusion, so that its ordered chain complex is defined.

`LinearExtension β` is a type synonym for `β`, so this is `barycentricSubdivision` itself with only
the order on its vertices changed; `ofSubdivisionVertex` and `toLinearExtension` pass between a
vertex and the face of `K` it is. -/
def orderedBarycentricSubdivision :
    _root_.AbstractSimplicialComplex
      (LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :=
  PreAbstractSimplicialComplex.barycentricSubdivision K.toPreAbstractSimplicialComplex

/-- The face of `K` that a vertex of `orderedBarycentricSubdivision K` is, as an element of
`TauCeti.SetLike.Face K`. This is the identity, since `LinearExtension β` is the type synonym `β`;
it is the inverse of `toLinearExtension`. -/
def ofSubdivisionVertex
    (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex :=
  p

omit [LinearOrder α] in
/-- The face of `K` underlying a face regarded as a vertex of the subdivision is that face. -/
@[simp]
theorem ofSubdivisionVertex_toLinearExtension
    (τ : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex) :
    ofSubdivisionVertex K (toLinearExtension τ) = τ :=
  (rfl)

omit [LinearOrder α] in
/-- A vertex of the subdivision is its underlying face of `K`, regarded as a vertex. -/
@[simp]
theorem toLinearExtension_ofSubdivisionVertex
    (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    toLinearExtension (ofSubdivisionVertex K p) = p :=
  (rfl)

/-- The face of `K` that a vertex of `orderedBarycentricSubdivision K` is, as a finite set. -/
def subdivisionFace (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    Finset α :=
  (ofSubdivisionVertex K p).val

omit [LinearOrder α] in
/-- The finite set underlying a vertex of the subdivision is that of its face of `K`. -/
theorem subdivisionFace_def
    (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    subdivisionFace K p = (ofSubdivisionVertex K p).val :=
  (rfl)

omit [LinearOrder α] in
/-- The finite set underlying a face regarded as a vertex of the subdivision is that face. -/
@[simp]
theorem subdivisionFace_toLinearExtension
    (τ : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex) :
    subdivisionFace K (toLinearExtension τ) = τ.val := by
  rw [subdivisionFace_def, ofSubdivisionVertex_toLinearExtension]

omit [LinearOrder α] in
/-- The face underlying a vertex of the subdivision is a face of `K`. -/
theorem subdivisionFace_mem
    (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    subdivisionFace K p ∈ K :=
  (ofSubdivisionVertex K p).property

omit [LinearOrder α] in
/-- A finite set of faces of `K` spans a face of the barycentric subdivision exactly when it is
nonempty and every two of its faces are nested. -/
theorem mem_orderedBarycentricSubdivision_iff
    {s : Finset (LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex))} :
    s ∈ orderedBarycentricSubdivision K ↔ s.Nonempty ∧ ∀ p ∈ s, ∀ q ∈ s,
      subdivisionFace K p ⊆ subdivisionFace K q ∨ subdivisionFace K q ⊆ subdivisionFace K p :=
  -- `orderedBarycentricSubdivision K` is `barycentricSubdivision K` on the type synonym
  -- `LinearExtension`, and `subdivisionFace K p` is the face `p` itself.
  PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'

omit [LinearOrder α] in
/-- Inclusion of the underlying faces implies the order of the linear extension. -/
theorem le_of_subdivisionFace_subset
    {p q : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)}
    (h : subdivisionFace K p ⊆ subdivisionFace K q) : p ≤ q := by
  rw [← toLinearExtension_ofSubdivisionVertex K p, ← toLinearExtension_ofSubdivisionVertex K q]
  exact toLinearExtension.monotone h

omit [LinearOrder α] in
/-- **The largest vertex of a face of the subdivision is its largest face.** In a face `s` of the
barycentric subdivision, the largest vertex in the linear extension contains every other vertex
as a face of `K`. -/
theorem subdivisionFace_subset_subdivisionFace_max'
    {s : Finset (LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex))}
    (hs : s ∈ orderedBarycentricSubdivision K) {p} (hp : p ∈ s) :
    subdivisionFace K p ⊆ subdivisionFace K (s.max' ⟨p, hp⟩) := by
  rcases ((mem_orderedBarycentricSubdivision_iff K).mp hs).2 p hp _ (s.max'_mem _) with h | h
  · exact h
  · exact subset_of_eq (congrArg (subdivisionFace K)
      (le_antisymm (s.le_max' p hp) (le_of_subdivisionFace_subset K h)))

/-- The barycenter of a face of `K` in the barycentric subdivision: the face itself, regarded as a
vertex. -/
def subdivisionBarycenter (τ : TauCeti.SetLike.Face K) :
    LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex) :=
  toLinearExtension (⟨τ.val, τ.property⟩ : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)

omit [LinearOrder α] in
/-- The face underlying the barycenter of a face is that face. -/
@[simp]
theorem subdivisionFace_subdivisionBarycenter (τ : TauCeti.SetLike.Face K) :
    subdivisionFace K (subdivisionBarycenter K τ) = τ.val := by
  rw [subdivisionBarycenter, subdivisionFace_toLinearExtension]

omit [LinearOrder α] in
/-- Barycenters of larger faces are larger in the linear extension of inclusion. -/
theorem strictMono_subdivisionBarycenter : StrictMono (subdivisionBarycenter K) := fun σ τ h ↦
  lt_of_le_of_ne (le_of_subdivisionFace_subset K (by simpa using h.le)) fun h' ↦ h.ne
    (Subtype.ext (by simpa using congrArg (subdivisionFace K) h'))

omit [LinearOrder α] in
/-- A barycenter can be adjoined to every face of the barycentric subdivision spanned by
barycenters of proper subfaces. -/
theorem insert_subdivisionBarycenter_mem_orderedBarycentricSubdivision
    ⦃s : Finset (LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex))⦄
    (hs : s ∈ orderedBarycentricSubdivision K) (ρ : TauCeti.SetLike.Face K)
    (hρ : ∀ w ∈ s, ∃ τ < ρ, subdivisionBarycenter K τ = w) :
    insert (subdivisionBarycenter K ρ) s ∈ orderedBarycentricSubdivision K := by
  rw [mem_orderedBarycentricSubdivision_iff] at hs ⊢
  have hle : ∀ w ∈ s, subdivisionFace K w ⊆ ρ.val := fun w hw ↦ by
    obtain ⟨τ, hτ, rfl⟩ := hρ w hw
    rw [subdivisionFace_subdivisionBarycenter]
    exact SetLike.face_le_iff.mp hτ.le
  refine ⟨Finset.insert_nonempty _ _, fun p hp q hq ↦ ?_⟩
  rcases Finset.mem_insert.mp hp with rfl | hp <;> rcases Finset.mem_insert.mp hq with rfl | hq
  · exact Or.inl subset_rfl
  · exact Or.inr (hle q hq)
  · exact Or.inl (hle p hp)
  · exact hs.2 p hp q hq

/-- The **last-vertex map** of the barycentric subdivision: the simplicial map sending a face of
`K`, a vertex of the subdivision, to its largest vertex. -/
def lastVertexMap :
    PreAbstractSimplicialComplex.SimplicialMap
      (orderedBarycentricSubdivision K).toPreAbstractSimplicialComplex
      K.toPreAbstractSimplicialComplex where
  toFun p := (subdivisionFace K p).max' (K.isRelLowerSet_faces (subdivisionFace_mem K p)).1
  map_face' := by
    intro s hs
    have hs' := (mem_orderedBarycentricSubdivision_iff K).mp hs
    -- The largest vertex of `s` in the linear extension is its largest face under inclusion.
    refine (K.isRelLowerSet_faces (subdivisionFace_mem K (s.max' hs'.1))).2 (fun v hv ↦ ?_)
      (hs'.1.image _)
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact subdivisionFace_subset_subdivisionFace_max' K hs hp (Finset.max'_mem _ _)

/-- The last-vertex map sends a vertex of the subdivision to the largest vertex of its face. -/
@[simp]
theorem lastVertexMap_apply
    (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    lastVertexMap K p =
      (subdivisionFace K p).max' (K.isRelLowerSet_faces (subdivisionFace_mem K p)).1 :=
  (rfl)

/-- The last-vertex map sends the barycenter of a face to its largest vertex. -/
theorem lastVertexMap_subdivisionBarycenter (τ : TauCeti.SetLike.Face K) :
    lastVertexMap K (subdivisionBarycenter K τ) =
      τ.val.max' (K.isRelLowerSet_faces τ.property).1 := by
  simp only [lastVertexMap_apply, subdivisionFace_subdivisionBarycenter]

end AbstractSimplicialComplex

end
