/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Extension.Linear
public import TauCeti.AlgebraicTopology.SimplicialComplex.Acyclic
public import TauCeti.AlgebraicTopology.SimplicialComplex.InducedChainMap
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Basic

/-!
# The subdivision chain map and the last-vertex map

Let `K` and `L` be simplicial complexes with linearly ordered vertices, and let `b` assign to each
face `τ` of `K` a vertex `b τ` of `L`, its *barycenter*. The **subdivision operator**
`TauCeti.OrderedSimplicialChain.subdivision` sends a vertex `[v]` of `K` to the vertex `[b {v}]` of
`L`, and an `(n + 1)`-cell `σ` to the cone with vertex `b σ` on the subdivision of its boundary,

`Sd [v] = [b {v}]`,  `Sd σ = (-1) ^ (n + 1) (Sd ∂σ) * b σ`,

where `z * w` is the cone operator `TauCeti.OrderedSimplicialChain.cone`, which adjoins `w` as a
last vertex. For the barycentric subdivision of `K` with its vertices ordered by a linear extension
of inclusion, this is the classical subdivision operator. In general `Sd` makes sense as soon as
barycenters of larger faces are larger, and a barycenter can be adjoined to every face of `L`
spanned by barycenters of proper subfaces. Under these two conditions `Sd` is a chain map
(`TauCeti.OrderedSimplicialChain.boundary_comp_subdivision`), packaged as a morphism of ordered
chain complexes `TauCeti.subdivisionChainMap`. Every simplex in the subdivision of a cell `σ` is
spanned by barycenters of faces of `σ`
(`TauCeti.OrderedSimplicialChain.exists_le_eq_of_mem_support_subdivision`).

A simplicial map `λ : L → K` sending each barycenter `b τ` to a vertex of `τ` is a chain inverse of
`Sd` on one side: `λ_# ∘ Sd = 1` (`TauCeti.OrderedSimplicialChain.map_comp_subdivision`). The
proof needs no sign bookkeeping. The chain `λ_# (Sd σ)` is supported on cells spanned by vertices
of `σ`, so it is a multiple `k σ`; since `λ_# ∘ Sd` is a chain map, `k ∂σ = ∂σ` by induction, and
the coefficient of the face opposite the first vertex gives `k = 1`.

For the barycentric subdivision (`AbstractSimplicialComplex.orderedBarycentricSubdivision`), whose
vertices are the faces of `K`, the barycenter of a face is the face itself
(`AbstractSimplicialComplex.subdivisionBarycenter`), and the *last-vertex map* sending a face to its
largest vertex (`AbstractSimplicialComplex.lastVertexMap`) is simplicial and satisfies the
hypothesis, so `λ_# ∘ Sd = 1` on ordered chains
(`TauCeti.OrderedSimplicialChain.map_lastVertexMap_comp_subdivision`). For the edge `[v₀, v₁]` the
subdivision is `[{v₀}, {v₀, v₁}] - [{v₁}, {v₀, v₁}]`, and the last-vertex map sends the first
simplex to the edge and collapses the second.

## Main definitions

* `TauCeti.OrderedSimplicialChain.subdivision`: the subdivision operator on ordered chains.
* `TauCeti.subdivisionChainMap`: the subdivision chain map of ordered chain complexes.
* `AbstractSimplicialComplex.orderedBarycentricSubdivision`: the barycentric subdivision, with its
  vertices ordered by a linear extension of inclusion.
* `AbstractSimplicialComplex.subdivisionBarycenter`, `AbstractSimplicialComplex.lastVertexMap`: the
  barycenters of the faces of `K` in the barycentric subdivision, and the simplicial map sending
  each face to its largest vertex.

## Main results

* `TauCeti.OrderedSimplicialChain.boundary_comp_subdivision`: `∂ ∘ Sd = Sd ∘ ∂`.
* `TauCeti.OrderedSimplicialChain.map_comp_subdivision`: `λ_# ∘ Sd = 1` for every simplicial map
  sending each barycenter to a vertex of its face.
* `TauCeti.OrderedSimplicialChain.map_lastVertexMap_comp_subdivision`: the same for the last-vertex
  map of the barycentric subdivision.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1 (the subdivision operator) and Section 2.C
  (simplicial approximation and the Lefschetz fixed-point theorem).
* J. R. Munkres, *Elements of Algebraic Topology*, §17 (the subdivision operator and its
  simplicial approximation).
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v

open AbstractSimplicialComplex

namespace TauCeti

namespace OrderedSimplicialChain

variable {α ι : Type*} [LinearOrder α] [LinearOrder ι]
  {K : _root_.AbstractSimplicialComplex α} {L : _root_.AbstractSimplicialComplex ι}

section Support

variable {R : Type*} [Semiring R] {n : ℕ}

/-- A cell in the support of a finite sum of chains lies in the support of one of the summands. -/
private theorem exists_mem_support_of_mem_support_sum {κ : Type*} {s : Finset κ}
    {f : κ → OrderedSimplicialChain L R n} {d : RealizationCell L n}
    (hd : d ∈ (∑ j ∈ s, f j).support) : ∃ j ∈ s, d ∈ (f j).support := by
  by_contra! h
  exact (Finsupp.mem_support_iff.mp hd) (by
    rw [show (∑ j ∈ s, f j) d = ∑ j ∈ s, f j d from map_sum (Finsupp.applyAddHom d) f s]
    exact Finset.sum_eq_zero fun j hj ↦ Finsupp.notMem_support_iff.mp (h j hj))

/-- Every cell in the support of a cone is the cone on a cell of the original chain that can be
coned off. -/
theorem exists_eq_cone_of_mem_support_cone {w : ι} {z : OrderedSimplicialChain L R n}
    {d : RealizationCell L (n + 1)} (hd : d ∈ (cone R w n z).support) :
    ∃ e ∈ z.support, ∃ (hlt : ∀ x ∈ e.1.1, x < w) (hL : insert w e.1.1 ∈ L),
      d = e.cone w hlt hL := by
  classical
  rw [← z.sum_single, Finsupp.sum, map_sum] at hd
  obtain ⟨e, he, hd⟩ := exists_mem_support_of_mem_support_sum hd
  by_cases h : (∀ x ∈ e.1.1, x < w) ∧ insert w e.1.1 ∈ L
  · rw [cone_single e h.1 h.2] at hd
    exact ⟨e, he, h.1, h.2, Finset.mem_singleton.mp (Finsupp.support_single_subset hd)⟩
  · simp [cone_single_of_not e h] at hd

/-- A chain of `K` all of whose cells are spanned by vertices of one cell `c` of the same dimension
is a multiple of `c`. -/
theorem eq_single_of_forall_mem_support_subset {x : OrderedSimplicialChain K R n}
    {c : RealizationCell K n} (hx : ∀ d ∈ x.support, d.1.1 ⊆ c.1.1) : x = single c (x c) := by
  classical
  ext d
  by_cases hdc : d = c
  · subst hdc
    simp
  · rw [single_eq_of_ne hdc]
    by_contra hne
    refine hdc (RealizationCell.ext (Finset.eq_of_subset_of_card_le
      (hx d (Finsupp.mem_support_iff.mpr hne)) ?_))
    rw [c.2, d.2]

end Support

section Subdivision

variable (R : Type*) [Ring R] (b : TauCeti.SetLike.Face K → ι)

/-- The **subdivision operator** on ordered chains, for a choice `b τ` of a barycenter for every
face `τ` of `K`. A vertex `[v]` goes to the vertex `[b {v}]`, and an `(n + 1)`-cell `σ` goes to
`(-1) ^ (n + 1)` times the cone with vertex `b σ` on the subdivision of its boundary. Under the
hypotheses of `boundary_comp_subdivision` this is a chain map. -/
def subdivision : (n : ℕ) → OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n
  | 0 => linearCombination R fun c ↦ single (RealizationCell.vertex L (b c.1)) 1
  | n + 1 => linearCombination R fun c ↦
      (-1 : R) ^ (n + 1) • cone R (b c.1) n (subdivision n (boundary R n (single c 1)))

variable {R b}

/-- The subdivision of a multiple of a vertex is that multiple of the vertex of its barycenter. -/
@[simp]
theorem subdivision_zero_single (c : RealizationCell K 0) (a : R) :
    subdivision (L := L) R b 0 (single c a) = single (RealizationCell.vertex L (b c.1)) a := by
  simp [subdivision]

/-- The subdivision of a cell of positive dimension is the signed cone, with vertex the barycenter
of the cell, on the subdivision of its boundary. -/
theorem subdivision_succ_single {n : ℕ} (c : RealizationCell K (n + 1)) :
    subdivision (L := L) R b (n + 1) (single c 1) =
      (-1 : R) ^ (n + 1) • cone R (b c.1) n (subdivision R b n (boundary R n (single c 1))) := by
  simp [subdivision]

/-- The subdivision preserves the augmentation of `0`-chains. -/
theorem augmentation_comp_subdivision_zero :
    linearCombination R (fun _ : RealizationCell L 0 ↦ (1 : R)) ∘ₗ subdivision (L := L) R b 0 =
      linearCombination R fun _ : RealizationCell K 0 ↦ (1 : R) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

/-- **Simplices of the subdivision of a cell are spanned by barycenters of its faces.** Every
vertex of a cell in the support of the subdivision of a cell `c` is the barycenter of a face of
`c`. -/
theorem exists_le_eq_of_mem_support_subdivision {n : ℕ} (c : RealizationCell K n)
    {d : RealizationCell L n} (hd : d ∈ (subdivision (L := L) R b n (single c 1)).support) {w : ι}
    (hw : w ∈ d.1.1) : ∃ τ : TauCeti.SetLike.Face K, τ ≤ c.1 ∧ b τ = w := by
  classical
  induction n with
  | zero =>
    rw [subdivision_zero_single] at hd
    obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hd)
    rw [RealizationCell.vertex_val] at hw
    exact ⟨c.1, le_rfl, (Finset.mem_singleton.mp hw).symm⟩
  | succ n ih =>
    rw [subdivision_succ_single] at hd
    obtain ⟨e, he, hlt, hL, rfl⟩ :=
      exists_eq_cone_of_mem_support_cone (Finsupp.support_smul hd)
    rw [RealizationCell.cone_val] at hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨c.1, le_rfl, rfl⟩
    · rw [boundary_single, map_sum] at he
      obtain ⟨j, -, he⟩ := exists_mem_support_of_mem_support_sum he
      rw [map_smul] at he
      obtain ⟨τ, hτ, rfl⟩ := ih (c.face j) (Finsupp.support_smul he) hw
      exact ⟨τ, hτ.trans (c.face_val_subset j), rfl⟩

/-- If a simplicial map `f : L → K` sends the barycenter of every face `τ` to a vertex of `τ`,
then every cell of `f_# (Sd c)` is spanned by vertices of `c`. -/
theorem subset_of_mem_support_map_subdivision
    (f : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hf : ∀ τ : TauCeti.SetLike.Face K, f (b τ) ∈ τ.1) {n : ℕ} (c : RealizationCell K n)
    {d : RealizationCell K n} (hd : d ∈ (map R f n (subdivision R b n (single c 1))).support) :
    d.1.1 ⊆ c.1.1 := by
  classical
  rw [← (subdivision R b n (single c 1)).sum_single, Finsupp.sum, map_sum] at hd
  obtain ⟨e, he, hd⟩ := exists_mem_support_of_mem_support_sum hd
  rw [map_single] at hd
  have hd := Finsupp.support_smul hd
  by_cases hinj : Function.Injective (f ∘ e.vertexEmbedding)
  · by_cases hK : Finset.univ.image (f ∘ e.vertexEmbedding) ∈ K
    · obtain ⟨d', σ, hσ⟩ := RealizationCell.exists_eq_vertexEmbedding_comp hinj hK
      rw [hσ, tupleChain_vertexEmbedding_comp] at hd
      obtain rfl := Finset.mem_singleton.mp
        (Finsupp.support_single_subset (Finsupp.support_smul hd))
      intro v hv
      have hv' : v ∈ Finset.univ.image (f ∘ e.vertexEmbedding) := by
        rwa [hσ, ← Finset.image_image, Finset.image_univ_of_surjective σ.surjective,
          d.image_vertexEmbedding]
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv'
      obtain ⟨τ, hτ, hτb⟩ := exists_le_eq_of_mem_support_subdivision c he (e.vertexEmbedding_mem i)
      simp only [Function.comp_apply, ← hτb]
      exact hτ (hf τ)
    · simp [tupleChain_eq_zero_of_image_notMem hK] at hd
  · simp [tupleChain_eq_zero_of_not_injective hinj] at hd

variable (hb : StrictMono b)
  (hL : ∀ ⦃s : Finset ι⦄, s ∈ L → ∀ ρ : TauCeti.SetLike.Face K,
    (∀ w ∈ s, ∃ τ < ρ, b τ = w) → insert (b ρ) s ∈ L)
include hb hL

/-- Every cell in the subdivision of the boundary of a cell `c` can be coned off at the barycenter
of `c`. -/
theorem forall_lt_and_insert_mem_of_mem_support_subdivision_boundary {n : ℕ}
    (c : RealizationCell K (n + 1)) {e : RealizationCell L n}
    (he : e ∈ (subdivision (L := L) R b n (boundary R n (single c 1))).support) :
    (∀ w ∈ e.1.1, w < b c.1) ∧ insert (b c.1) e.1.1 ∈ L := by
  classical
  rw [boundary_single, map_sum] at he
  obtain ⟨j, -, he⟩ := exists_mem_support_of_mem_support_sum he
  rw [map_smul] at he
  have hlt : ∀ w ∈ e.1.1, ∃ τ < c.1, b τ = w := fun w hw ↦ by
    obtain ⟨τ, hτ, rfl⟩ :=
      exists_le_eq_of_mem_support_subdivision (c.face j) (Finsupp.support_smul he) hw
    refine ⟨τ, lt_of_le_of_lt hτ (lt_of_le_of_ne (c.face_val_subset j) fun h ↦ ?_), rfl⟩
    have hcard := congrArg (fun σ : TauCeti.SetLike.Face K ↦ σ.1.card) h
    simp only [(c.face j).2, c.2] at hcard
    omega
  refine ⟨fun w hw ↦ ?_, hL e.1.2 c.1 hlt⟩
  obtain ⟨τ, hτ, rfl⟩ := hlt w hw
  exact hb hτ

/-- **The subdivision operator is a chain map**: `∂ ∘ Sd = Sd ∘ ∂`, provided barycenters of larger
faces are larger and a barycenter can be adjoined to every face of `L` spanned by barycenters of
proper subfaces. -/
theorem boundary_comp_subdivision (n : ℕ) :
    boundary R n ∘ₗ subdivision (L := L) R b (n + 1) = subdivision R b n ∘ₗ boundary R n := by
  induction n with
  | zero =>
    refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
    have hε := congrArg (fun φ ↦ φ (boundary R 0 (single c 1))) (augmentation_comp_subdivision_zero
      (L := L) (R := R) (b := b))
    have hε₀ := congrArg (fun φ ↦ φ (single c 1)) (augmentation_comp_boundary (K := K) R)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] at hε hε₀
    simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, subdivision_succ_single,
      zero_add, pow_one, neg_smul, one_smul, map_neg,
      boundary_cone_zero fun _ he ↦
        forall_lt_and_insert_mem_of_mem_support_subdivision_boundary hb hL c he,
      hε, hε₀, single_zero, zero_sub, neg_neg]
  | succ n ih =>
    refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
    have hz :
        boundary R n (subdivision (L := L) R b (n + 1) (boundary R (n + 1) (single c 1))) = 0 := by
      have h := congrArg (fun φ ↦ φ (boundary R (n + 1) (single c 1))) ih
      simp only [LinearMap.coe_comp, Function.comp_apply] at h
      rw [h, ← LinearMap.comp_apply (boundary R n), boundary_boundary, LinearMap.zero_apply,
        map_zero]
    simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, subdivision_succ_single,
      map_smul, boundary_cone_succ fun _ he ↦
        forall_lt_and_insert_mem_of_mem_support_subdivision_boundary hb hL c he,
      hz, map_zero, zero_add, smul_smul, ← pow_add, Even.neg_one_pow ⟨n + 2, rfl⟩, one_smul]

/-- **The last-vertex map is a left inverse of the subdivision operator.** If a simplicial map
`f : L → K` sends the barycenter of every face `τ` to a vertex of `τ`, then `f_# ∘ Sd = 1` on
ordered chains. -/
theorem map_comp_subdivision
    (f : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hf : ∀ τ : TauCeti.SetLike.Face K, f (b τ) ∈ τ.1) (n : ℕ) :
    map R f n ∘ₗ subdivision R b n = LinearMap.id := by
  induction n with
  | zero =>
    refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
    have hc : f (b c.1) = c.vertexEmbedding 0 := by
      have h := hf c.1
      rw [← c.image_vertexEmbedding] at h
      simpa [Fin.forall_fin_one, eq_comm] using h
    have hv : (f ∘ (RealizationCell.vertex L (b c.1)).vertexEmbedding) =
        (RealizationCell.vertex K (c.vertexEmbedding 0)).vertexEmbedding := by
      funext i
      simp [RealizationCell.vertexEmbedding_vertex, hc]
    simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, subdivision_zero_single,
      map_single, one_smul, hv, tupleChain_vertexEmbedding, LinearMap.id_coe, id_eq]
    rw [← RealizationCell.eq_vertex]
  | succ n ih =>
    refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, LinearMap.id_coe, id_eq]
    -- The chain `f_# (Sd c)` is spanned by vertices of `c`, hence a multiple of `c`.
    have hx := eq_single_of_forall_mem_support_subset
      fun d hd ↦ subset_of_mem_support_map_subdivision (R := R) f hf c hd
    -- Comparing boundaries, the multiple is `1`.
    have hbd : boundary R n (map R f (n + 1) (subdivision R b (n + 1) (single c 1))) =
        boundary R n (single c 1) := by
      have h₁ := congrArg (fun φ ↦ φ (subdivision R b (n + 1) (single c 1)))
        (boundary_comp_map (R := R) f n)
      have h₂ := congrArg (fun φ ↦ φ (single c 1)) (boundary_comp_subdivision hb hL (R := R) n)
      have h₃ := congrArg (fun φ ↦ φ (boundary R n (single c 1))) ih
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h₁ h₂ h₃
      rw [h₁, h₂, h₃]
    have hcoef := congrArg (fun y ↦ y (c.face 0)) hbd
    rw [hx, ← smul_single_one, map_smul, boundary_single_one] at hcoef
    simp only [Finsupp.smul_apply, boundaryCell_apply_face, Fin.val_zero, pow_zero, smul_eq_mul,
      mul_one] at hcoef
    rw [hx, hcoef]

end Subdivision

end OrderedSimplicialChain

open OrderedSimplicialChain

section ChainMap

variable {α ι : Type u} [LinearOrder α] [LinearOrder ι]
  {K : _root_.AbstractSimplicialComplex α} {L : _root_.AbstractSimplicialComplex ι}
  (R : Type v) [Ring R] {b : TauCeti.SetLike.Face K → ι} (hb : StrictMono b)
  (hL : ∀ ⦃s : Finset ι⦄, s ∈ L → ∀ ρ : TauCeti.SetLike.Face K,
    (∀ w ∈ s, ∃ τ < ρ, b τ = w) → insert (b ρ) s ∈ L)

/-- The **subdivision chain map** of ordered chain complexes, for barycenters `b` that increase
with the face and can be adjoined to every face of `L` spanned by barycenters of proper
subfaces. -/
def subdivisionChainMap :
    orderedSimplicialChainComplex K R ⟶ orderedSimplicialChainComplex L R where
  f n := eqToHom (orderedSimplicialChainComplex_X R n) ≫
    ModuleCat.ofHom (subdivision R b n) ≫ eqToHom (orderedSimplicialChainComplex_X R n).symm
  comm' i j h := by
    subst i
    simp only [orderedSimplicialChainComplex_d, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    congr 1
    simp only [← Category.assoc]
    congr 1
    exact ModuleCat.hom_ext (boundary_comp_subdivision hb hL j)

/-- The degreewise subdivision chain map is the subdivision operator. -/
@[simp]
theorem subdivisionChainMap_f (n : ℕ) :
    (subdivisionChainMap R hb hL).f n =
      eqToHom (orderedSimplicialChainComplex_X R n) ≫
        ModuleCat.ofHom (subdivision R b n) ≫ eqToHom (orderedSimplicialChainComplex_X R n).symm :=
  (rfl)

/-- A simplicial map sending the barycenter of every face to a vertex of that face is a left
inverse of the subdivision chain map. -/
theorem subdivisionChainMap_comp_orderedSimplicialChainComplexMap
    (f : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hf : ∀ τ : TauCeti.SetLike.Face K, f (b τ) ∈ τ.1) :
    subdivisionChainMap R hb hL ≫ orderedSimplicialChainComplexMap R f = 𝟙 _ := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, subdivisionChainMap_f, orderedSimplicialChainComplexMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, HomologicalComplex.id_f]
  rw [← Category.assoc (ModuleCat.ofHom _), ← ModuleCat.ofHom_comp,
    map_comp_subdivision hb hL f hf n, ModuleCat.ofHom_id, Category.id_comp, eqToHom_trans,
    eqToHom_refl]

end ChainMap

end TauCeti

namespace AbstractSimplicialComplex

open TauCeti

variable {α : Type u} [LinearOrder α] (K : AbstractSimplicialComplex α)

/-- The **barycentric subdivision** of `K`, with its vertices, the faces of `K`, ordered by a linear
extension of inclusion, so that its ordered chain complex is defined. -/
def orderedBarycentricSubdivision :
    _root_.AbstractSimplicialComplex
      (LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :=
  PreAbstractSimplicialComplex.barycentricSubdivision K.toPreAbstractSimplicialComplex

/-- The face of `K` that a vertex of `orderedBarycentricSubdivision K` is. -/
def subdivisionFace (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    Finset α :=
  Subtype.val (p : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)

omit [LinearOrder α] in
/-- The face underlying a vertex of the subdivision is a face of `K`. -/
theorem subdivisionFace_mem
    (p : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)) :
    subdivisionFace K p ∈ K :=
  Subtype.prop (p : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)

omit [LinearOrder α] in
/-- A finite set of faces of `K` spans a face of the barycentric subdivision exactly when it is
nonempty and every two of its faces are nested. -/
theorem mem_orderedBarycentricSubdivision_iff
    {s : Finset (LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex))} :
    s ∈ orderedBarycentricSubdivision K ↔ s.Nonempty ∧ ∀ p ∈ s, ∀ q ∈ s,
      subdivisionFace K p ⊆ subdivisionFace K q ∨ subdivisionFace K q ⊆ subdivisionFace K p :=
  PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'

omit [LinearOrder α] in
/-- Inclusion of the underlying faces implies the order of the linear extension. -/
theorem le_of_subdivisionFace_subset
    {p q : LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)}
    (h : subdivisionFace K p ⊆ subdivisionFace K q) : p ≤ q :=
  (toLinearExtension (α := TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)).monotone
    (a := p) (b := q) h

/-- The barycenter of a face of `K` in the barycentric subdivision: the face itself, regarded as a
vertex. -/
def subdivisionBarycenter (τ : TauCeti.SetLike.Face K) :
    LinearExtension (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex) :=
  toLinearExtension (⟨τ.1, τ.2⟩ : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex)

omit [LinearOrder α] in
/-- The face underlying the barycenter of a face is that face. -/
@[simp]
theorem subdivisionFace_subdivisionBarycenter (τ : TauCeti.SetLike.Face K) :
    subdivisionFace K (subdivisionBarycenter K τ) = τ.1 :=
  (rfl)

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
  have hle : ∀ w ∈ s, subdivisionFace K w ⊆ ρ.1 := fun w hw ↦ by
    obtain ⟨τ, hτ, rfl⟩ := hρ w hw
    exact hτ.le
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
    -- The largest vertex `M` of `s` in the linear extension is its largest face under inclusion.
    set M := s.max' hs'.1
    have hle : ∀ p ∈ s, subdivisionFace K p ⊆ subdivisionFace K M := fun p hp ↦ by
      rcases hs'.2 p hp M (s.max'_mem hs'.1) with h | h
      · exact h
      · rw [le_antisymm (s.le_max' p hp) (le_of_subdivisionFace_subset K h)]
    refine (K.isRelLowerSet_faces (subdivisionFace_mem K M)).2 (fun v hv ↦ ?_) (hs'.1.image _)
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact hle p hp (Finset.max'_mem _ _)

/-- The last-vertex map sends the barycenter of a face to its largest vertex. -/
theorem lastVertexMap_subdivisionBarycenter (τ : TauCeti.SetLike.Face K) :
    lastVertexMap K (subdivisionBarycenter K τ) = τ.1.max' (K.isRelLowerSet_faces τ.2).1 :=
  (rfl)

end AbstractSimplicialComplex

namespace TauCeti.OrderedSimplicialChain

open AbstractSimplicialComplex

variable {α : Type u} [LinearOrder α] (K : _root_.AbstractSimplicialComplex α)
variable (R : Type v) [Ring R]

/-- **The last-vertex map inverts the barycentric subdivision operator on the left**: on ordered
chains, `λ_# ∘ Sd = 1`. -/
theorem map_lastVertexMap_comp_subdivision (n : ℕ) :
    map R (lastVertexMap K) n ∘ₗ subdivision R (subdivisionBarycenter K) n = LinearMap.id :=
  map_comp_subdivision (strictMono_subdivisionBarycenter K)
    (insert_subdivisionBarycenter_mem_orderedBarycentricSubdivision K) (lastVertexMap K)
    (fun τ ↦ by rw [lastVertexMap_subdivisionBarycenter]; exact Finset.max'_mem _ _) n

end TauCeti.OrderedSimplicialChain
