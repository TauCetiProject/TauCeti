/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

For the barycentric subdivision (`AbstractSimplicialComplex.orderedBarycentricSubdivision`, in
`Subdivision.Basic`), whose vertices are the faces of `K`, the barycenter of a face is the face
itself (`AbstractSimplicialComplex.subdivisionBarycenter`), and the *last-vertex map* sending a face
to its largest vertex (`AbstractSimplicialComplex.lastVertexMap`) is simplicial and satisfies the
hypothesis, so `λ_# ∘ Sd = 1` on ordered chains
(`TauCeti.OrderedSimplicialChain.map_lastVertexMap_comp_subdivision`). For the edge `[v₀, v₁]` the
subdivision is `[{v₀}, {v₀, v₁}] - [{v₁}, {v₀, v₁}]`, and the last-vertex map sends the first
simplex to the edge and collapses the second.

## Main definitions

* `TauCeti.OrderedSimplicialChain.subdivision`: the subdivision operator on ordered chains.
* `TauCeti.subdivisionChainMap`: the subdivision chain map of ordered chain complexes.

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


section Subdivision

variable (R : Type*) [Ring R] (b : TauCeti.SetLike.Face K → ι)

/-- The **subdivision operator** on ordered chains, for a choice `b τ` of a barycenter for every
face `τ` of `K`. A vertex `[v]` goes to the vertex `[b {v}]`, and an `(n + 1)`-cell `σ` goes to
`(-1) ^ (n + 1)` times the cone with vertex `b σ` on the subdivision of its boundary. Under the
hypotheses of `boundary_comp_subdivision` this is a chain map. -/
def subdivision : (n : ℕ) → OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n
  | 0 => linearCombination R fun c ↦ single (RealizationCell.vertex L (b c.val)) 1
  | n + 1 => linearCombination R fun c ↦
      (-1 : R) ^ (n + 1) • cone R (b c.val) n (subdivision n (boundary R n (single c 1)))

variable {R b}

/-- The subdivision of a multiple of a vertex is that multiple of the vertex of its barycenter. -/
@[simp]
theorem subdivision_zero_single (c : RealizationCell K 0) (a : R) :
    subdivision (L := L) R b 0 (single c a) = single (RealizationCell.vertex L (b c.val)) a := by
  simp [subdivision]

/-- The subdivision of a cell of positive dimension is the signed cone, with vertex the barycenter
of the cell, on the subdivision of its boundary. -/
theorem subdivision_succ_single {n : ℕ} (c : RealizationCell K (n + 1)) :
    subdivision (L := L) R b (n + 1) (single c 1) =
      (-1 : R) ^ (n + 1) • cone R (b c.val) n (subdivision R b n (boundary R n (single c 1))) := by
  simp [subdivision]

/-- The subdivision preserves the augmentation of `0`-chains. -/
theorem augmentation_comp_subdivision_zero :
    linearCombination R (fun _ : RealizationCell L 0 ↦ (1 : R)) ∘ₗ subdivision (L := L) R b 0 =
      linearCombination R fun _ : RealizationCell K 0 ↦ (1 : R) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

/-- Every cell in the subdivision of the boundary of a cell `c` lies in the subdivision of a
codimension-one face of `c`. -/
theorem exists_mem_support_subdivision_face_of_mem_support_subdivision_boundary {n : ℕ}
    (c : RealizationCell K (n + 1)) {e : RealizationCell L n}
    (he : e ∈ (subdivision (L := L) R b n (boundary R n (single c 1))).support) :
    ∃ j, e ∈ (subdivision (L := L) R b n (single (c.face j) 1)).support := by
  classical
  rw [boundary_single, map_sum] at he
  obtain ⟨j, -, he⟩ := Finsupp.mem_support_finsetSum _ he
  rw [map_smul] at he
  exact ⟨j, Finsupp.support_smul he⟩

/-- **Simplices of the subdivision of a cell are spanned by barycenters of its faces.** Every
vertex of a cell in the support of the subdivision of a cell `c` is the barycenter of a face of
`c`. -/
theorem exists_le_eq_of_mem_support_subdivision {n : ℕ} (c : RealizationCell K n)
    {d : RealizationCell L n} (hd : d ∈ (subdivision (L := L) R b n (single c 1)).support) {w : ι}
    (hw : w ∈ d.val.val) : ∃ τ : TauCeti.SetLike.Face K, τ ≤ c.val ∧ b τ = w := by
  classical
  induction n with
  | zero =>
    rw [subdivision_zero_single] at hd
    obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hd)
    rw [RealizationCell.vertex_val] at hw
    exact ⟨c.val, le_rfl, (Finset.mem_singleton.mp hw).symm⟩
  | succ n ih =>
    rw [subdivision_succ_single] at hd
    obtain ⟨e, he, hlt, hL, rfl⟩ :=
      exists_eq_cone_of_mem_support_cone (Finsupp.support_smul hd)
    rw [RealizationCell.cone_val] at hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨c.val, le_rfl, rfl⟩
    · obtain ⟨j, he⟩ := exists_mem_support_subdivision_face_of_mem_support_subdivision_boundary c he
      obtain ⟨τ, hτ, rfl⟩ := ih (c.face j) he hw
      exact ⟨τ, hτ.trans (c.face_val_subset j), rfl⟩

/-- If a simplicial map `f : L → K` sends the barycenter of every face `τ` to a vertex of `τ`,
then every cell of `f_# (Sd c)` is spanned by vertices of `c`. -/
theorem subset_of_mem_support_map_subdivision
    (f : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hf : ∀ τ : TauCeti.SetLike.Face K, f (b τ) ∈ τ.val) {n : ℕ} (c : RealizationCell K n)
    {d : RealizationCell K n} (hd : d ∈ (map R f n (subdivision R b n (single c 1))).support) :
    d.val.val ⊆ c.val.val := by
  classical
  rw [← (subdivision R b n (single c 1)).sum_single, Finsupp.sum, map_sum] at hd
  obtain ⟨e, he, hd⟩ := Finsupp.mem_support_finsetSum _ hd
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
    (∀ w ∈ e.val.val, w < b c.val) ∧ insert (b c.val) e.val.val ∈ L := by
  obtain ⟨j, he⟩ := exists_mem_support_subdivision_face_of_mem_support_subdivision_boundary c he
  have hlt : ∀ w ∈ e.val.val, ∃ τ < c.val, b τ = w := fun w hw ↦ by
    obtain ⟨τ, hτ, rfl⟩ := exists_le_eq_of_mem_support_subdivision (c.face j) he hw
    exact ⟨τ, lt_of_le_of_lt hτ (c.face_val_ssubset j), rfl⟩
  refine ⟨fun w hw ↦ ?_, hL e.val.property c.val hlt⟩
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

/-- **A simplicial map sending barycenters to vertices of their faces inverts `Sd` on the left.**
Suppose barycenters of larger faces are larger and a barycenter can be adjoined to every face of
`L` spanned by barycenters of proper subfaces, so that `Sd` is a chain map. If a simplicial map
`f : L → K` sends the barycenter of every face `τ` to a vertex of `τ`, then `f_# ∘ Sd = 1` on
ordered chains. The last-vertex map is the case `map_lastVertexMap_comp_subdivision`. -/
theorem map_comp_subdivision
    (f : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hf : ∀ τ : TauCeti.SetLike.Face K, f (b τ) ∈ τ.val) (n : ℕ) :
    map R f n ∘ₗ subdivision R b n = LinearMap.id := by
  induction n with
  | zero =>
    refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
    have hc : f (b c.val) = c.vertexEmbedding 0 := by
      have h := hf c.val
      rw [← c.image_vertexEmbedding] at h
      simpa [Fin.forall_fin_one, eq_comm] using h
    have hv : (f ∘ (RealizationCell.vertex L (b c.val)).vertexEmbedding) =
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
    orderedSimplicialChainComplex K R ⟶ orderedSimplicialChainComplex L R :=
  orderedSimplicialChainComplexHomOfLinear R (subdivision R b) (boundary_comp_subdivision hb hL)

/-- The degreewise subdivision chain map is the subdivision operator. -/
@[simp]
theorem subdivisionChainMap_f (n : ℕ) :
    (subdivisionChainMap R hb hL).f n =
      eqToHom (orderedSimplicialChainComplex_X R n) ≫
        ModuleCat.ofHom (subdivision R b n) ≫ eqToHom (orderedSimplicialChainComplex_X R n).symm :=
  orderedSimplicialChainComplexHomOfLinear_f R _ _ n

/-- A simplicial map sending the barycenter of every face to a vertex of that face is a left
inverse of the subdivision chain map. -/
theorem subdivisionChainMap_comp_orderedSimplicialChainComplexMap
    (f : PreAbstractSimplicialComplex.SimplicialMap
      L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hf : ∀ τ : TauCeti.SetLike.Face K, f (b τ) ∈ τ.val) :
    subdivisionChainMap R hb hL ≫ orderedSimplicialChainComplexMap R f = 𝟙 _ := by
  simp only [subdivisionChainMap, orderedSimplicialChainComplexMap_def,
    orderedSimplicialChainComplexHomOfLinear_comp, map_comp_subdivision hb hL f hf,
    orderedSimplicialChainComplexHomOfLinear_id]

end ChainMap

end TauCeti


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
