/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.HexGraph
public import TauCeti.Combinatorics.Tiling.Lozenge.PartitionFunction
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Kasteleyn matrices of finite regions

Let `R` be a finite region of the triangular lattice and `w : TriEdge → ℝ` an edge weight. The
Kasteleyn matrix `K_R` of `R` has rows the white faces and columns the black faces of `R`, and its
entry at a white face `f` and a black face `g` is `w(e)` when `f` and `g` share the edge `e`, and
`0` otherwise. It is the weighted biadjacency matrix of the dual hexagonal graph restricted to `R`,
so each of its rows and columns has at most three nonzero entries.

A bijection `σ` from the white onto the black faces of `R` contributes to the Leibniz expansion of
the permanent or of the determinant of `K_R` the product `∏_f K_R(f, σ f)`. This product vanishes
unless every white face `f` shares an edge with `σ f`, and then those shared edges form a tiling of
`R` of weight `∏_f K_R(f, σ f)`. Every tiling arises from exactly one such bijection, so the
partition function of `R` is the permanent of `K_R`
(`TauCeti.partitionFunction_eq_sum_prod_kasteleynMatrix`). Kasteleyn's theorem, not proved here,
states that for simply connected regions and positive weights all nonzero terms of the determinant
have the same sign, so that `Z_R(w)` is also `|det K_R|`.

A determinant of `K_R` is taken after squaring it along a bijection from the black onto the white
faces. Changing the bijection changes the determinant only by a sign, and the inverse, read back as
a matrix with rows the black faces and columns the white faces, not at all; these are
`Matrix.det_submatrix_id_symm_eq_sign_mul_det` and `Matrix.inv_submatrix_id_symm_submatrix` for any
matrix with rows `m` and columns `n`.

## Main definitions

* `TauCeti.whiteFaces`, `TauCeti.blackFaces`: the white and the black faces of a finite region.
* `TauCeti.kasteleynMatrix`: the Kasteleyn matrix of a finite region for an edge weight.

## Main statements

* `TauCeti.kasteleynMatrix_apply_of_mem_edges`, `TauCeti.kasteleynMatrix_apply_of_not_adj`: the
  entry at faces sharing the edge `e` is `w(e)`, and it is `0` at faces that are not adjacent.
* `TauCeti.card_filter_kasteleynMatrix_row_ne_zero_le`,
  `TauCeti.card_filter_kasteleynMatrix_col_ne_zero_le`: each row and each column has at most three
  nonzero entries.
* `TauCeti.partitionFunction_eq_zero_of_card_ne`: a region with more white than black faces, or
  fewer, has no tiling, so its Kasteleyn matrix is square whenever its partition function is
  nonzero.
* `TauCeti.kasteleynMatrix_vadd_apply`, `TauCeti.kasteleynMatrix_rot_apply`: translations and the
  rotation `ρ` act compatibly, with translated or rotated weights.
* `TauCeti.partitionFunction_eq_sum_prod_kasteleynMatrix`: the partition function is the sum,
  over the bijections `σ` from the white onto the black faces, of `∏_f K_R(f, σ f)`, and
  `TauCeti.partitionFunction_eq_permanent` is the same statement for the permanent of the square
  matrix along any bijection from the black onto the white faces.

## References

* P. W. Kasteleyn, *The statistics of dimers on a lattice: I. The number of dimer arrangements on a
  quadratic lattice*, Physica 27 (1961).
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lectures 2 and 3.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Sections 3.1 and 3.4.
-/

public section

open scoped Pointwise

namespace TauCeti

/-! ### White and black faces -/

/-- The white faces of a finite region. -/
def whiteFaces (R : Finset TriFace) : Finset TriFace :=
  R.filter fun f => f.isWhite = true

/-- The black faces of a finite region. -/
def blackFaces (R : Finset TriFace) : Finset TriFace :=
  R.filter fun f => f.isWhite = false

variable {R : Finset TriFace} {w : TriEdge → ℝ} {f : TriFace}

@[simp] theorem mem_whiteFaces : f ∈ whiteFaces R ↔ f ∈ R ∧ f.isWhite = true :=
  Finset.mem_filter

@[simp] theorem mem_blackFaces : f ∈ blackFaces R ↔ f ∈ R ∧ f.isWhite = false :=
  Finset.mem_filter

/-- A white and a black face of a region are distinct. -/
private theorem whiteFaces_val_ne (f : whiteFaces R) (g : blackFaces R) : f.val ≠ g.val :=
  fun h => by simpa [h, (mem_blackFaces.1 g.property).2] using (mem_whiteFaces.1 f.property).2

/-- A region with more white than black faces, or fewer, has no tiling. -/
theorem partitionFunction_eq_zero_of_card_ne (w : TriEdge → ℝ)
    (h : (whiteFaces R).card ≠ (blackFaces R).card) : partitionFunction R w = 0 :=
  partitionFunction_eq_zero _ w fun _ hM =>
    h hM.card_filter_isWhite_eq_card_filter_isWhite_eq_false

/-! ### The Kasteleyn matrix -/

/-- The Kasteleyn matrix of a finite region `R` for an edge weight `w`: rows the white faces of
`R`, columns the black faces, and entry `w(e)` when the two faces share the edge `e`, `0`
otherwise (two distinct faces share at most one edge). -/
def kasteleynMatrix (R : Finset TriFace) (w : TriEdge → ℝ) :
    Matrix (whiteFaces R) (blackFaces R) ℝ :=
  Matrix.of fun f g => ∑ e ∈ f.val.edges ∩ g.val.edges, w e

theorem kasteleynMatrix_apply (R : Finset TriFace) (w : TriEdge → ℝ) (f : whiteFaces R)
    (g : blackFaces R) : kasteleynMatrix R w f g = ∑ e ∈ f.val.edges ∩ g.val.edges, w e :=
  (rfl)

/-- The entry of the Kasteleyn matrix at a white and a black face sharing the edge `e` is
`w(e)`. -/
theorem kasteleynMatrix_apply_of_mem_edges {f : whiteFaces R} {g : blackFaces R} {e : TriEdge}
    (hf : e ∈ f.val.edges) (hg : e ∈ g.val.edges) : kasteleynMatrix R w f g = w e := by
  rw [kasteleynMatrix_apply]
  refine Finset.sum_eq_single_of_mem e (Finset.mem_inter.2 ⟨hf, hg⟩) fun e' he' hne => ?_
  rw [Finset.mem_inter] at he'
  exact (hne (TriFace.eq_of_mem_edges_of_mem_edges (whiteFaces_val_ne f g) he'.1 he'.2 hf
    hg)).elim

/-- The entry of the Kasteleyn matrix at a white and a black face that are not adjacent in the
hexagonal graph is `0`. -/
theorem kasteleynMatrix_apply_of_not_adj {f : whiteFaces R} {g : blackFaces R}
    (h : ¬hexGraph.Adj f.val g.val) : kasteleynMatrix R w f g = 0 := by
  rw [kasteleynMatrix_apply]
  refine Finset.sum_eq_zero fun e he => (h ?_).elim
  rw [Finset.mem_inter] at he
  exact hexGraph_adj_of_mem_edges (whiteFaces_val_ne f g) he.1 he.2

/-- Each row of the Kasteleyn matrix has at most three nonzero entries. -/
theorem card_filter_kasteleynMatrix_row_ne_zero_le (w : TriEdge → ℝ) (f : whiteFaces R) :
    (Finset.univ.filter fun g => kasteleynMatrix R w f g ≠ 0).card ≤ 3 := by
  rw [← hexGraph_degree f.val, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn Subtype.val (fun g hg => ?_) Subtype.val_injective.injOn
  rw [Finset.coe_filter, Set.mem_ofPred_eq] at hg
  exact (SimpleGraph.mem_neighborFinset _ _ _).2
    (not_imp_comm.1 kasteleynMatrix_apply_of_not_adj hg.2)

/-- Each column of the Kasteleyn matrix has at most three nonzero entries. -/
theorem card_filter_kasteleynMatrix_col_ne_zero_le (w : TriEdge → ℝ) (g : blackFaces R) :
    (Finset.univ.filter fun f => kasteleynMatrix R w f g ≠ 0).card ≤ 3 := by
  rw [← hexGraph_degree g.val, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn Subtype.val (fun f hf => ?_) Subtype.val_injective.injOn
  rw [Finset.coe_filter, Set.mem_ofPred_eq] at hf
  exact (SimpleGraph.mem_neighborFinset _ _ _).2
    (not_imp_comm.1 kasteleynMatrix_apply_of_not_adj hf.2).symm

/-! ### Symmetries -/

/-- Transport of the sum of `w` over the edges shared by two faces along permutations `φ` of the
faces and `ψ` of the edges compatible with incidence. -/
private theorem sum_inter_edges_perm (φ : Equiv.Perm TriFace) (ψ : Equiv.Perm TriEdge)
    (hψ : ∀ e f, ψ e ∈ (φ f).edges ↔ e ∈ f.edges) (w : TriEdge → ℝ) (f g : TriFace) :
    ∑ e ∈ (φ f).edges ∩ (φ g).edges, w e = ∑ e ∈ f.edges ∩ g.edges, w (ψ e) := by
  refine Finset.sum_nbij' ψ.symm ψ (fun e he => ?_) (fun e he => ?_) (fun e _ => by simp)
    (fun e _ => by simp) (fun e _ => by simp)
  · rw [Finset.mem_inter] at he ⊢
    exact ⟨(hψ _ f).1 (by rw [Equiv.apply_symm_apply]; exact he.1),
      (hψ _ g).1 (by rw [Equiv.apply_symm_apply]; exact he.2)⟩
  · rw [Finset.mem_inter] at he ⊢
    exact ⟨(hψ e f).2 he.1, (hψ e g).2 he.2⟩

theorem vadd_mem_whiteFaces_vadd (u : ℤ × ℤ) :
    u +ᵥ f ∈ whiteFaces (u +ᵥ R) ↔ f ∈ whiteFaces R := by
  simp [Finset.vadd_mem_vadd_finset_iff]

theorem vadd_mem_blackFaces_vadd (u : ℤ × ℤ) :
    u +ᵥ f ∈ blackFaces (u +ᵥ R) ↔ f ∈ blackFaces R := by
  simp [Finset.vadd_mem_vadd_finset_iff]

/-- Translating a region and the weight together preserves the Kasteleyn matrix. -/
theorem kasteleynMatrix_vadd_apply (u : ℤ × ℤ) (R : Finset TriFace) (w : TriEdge → ℝ)
    (f : whiteFaces R) (g : blackFaces R) :
    kasteleynMatrix (u +ᵥ R) w ⟨u +ᵥ f.val, (vadd_mem_whiteFaces_vadd u).2 f.property⟩
        ⟨u +ᵥ g.val, (vadd_mem_blackFaces_vadd u).2 g.property⟩ =
      kasteleynMatrix R (fun e => w (u +ᵥ e)) f g := by
  simp only [kasteleynMatrix_apply]
  exact sum_inter_edges_perm (AddAction.toPerm u) (AddAction.toPerm u)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) w f.val g.val

theorem rot_mem_whiteFaces_map_rot :
    TriFace.rot f ∈ whiteFaces (R.map TriFace.rot.toEmbedding) ↔ f ∈ whiteFaces R := by
  simp

theorem rot_mem_blackFaces_map_rot :
    TriFace.rot f ∈ blackFaces (R.map TriFace.rot.toEmbedding) ↔ f ∈ blackFaces R := by
  simp

/-- Rotating a region by `ρ` and the weight together preserves the Kasteleyn matrix. -/
theorem kasteleynMatrix_rot_apply (R : Finset TriFace) (w : TriEdge → ℝ) (f : whiteFaces R)
    (g : blackFaces R) :
    kasteleynMatrix (R.map TriFace.rot.toEmbedding) w
        ⟨TriFace.rot f.val, rot_mem_whiteFaces_map_rot.2 f.property⟩
        ⟨TriFace.rot g.val, rot_mem_blackFaces_map_rot.2 g.property⟩ =
      kasteleynMatrix R (fun e => w (TriEdge.rot e)) f g := by
  simp only [kasteleynMatrix_apply]
  exact sum_inter_edges_perm TriFace.rot TriEdge.rot (fun _ _ => TriEdge.rot_mem_edges_rot) w
    f.val g.val

/-! ### The partition function as a permanent -/

section Bijection

/- A bijection `σ` from the white onto the black faces of `R` joining every white face `f` to an
adjacent black face `σ f` determines the tiling of the edges `adjEdge hσ f` shared by `f` and
`σ f`; every tiling of `R` arises from exactly one such `σ`. -/

/-- The edges joining the white faces of `R` to their images under a bijection `σ` from the white
onto the black faces, each edge being named by its white and its black face. -/
private def edgesOfEquiv (σ : whiteFaces R ≃ blackFaces R) : Set TriEdge :=
  {e | ∃ f : whiteFaces R, f.val = e.whiteFace ∧ (σ f).val = e.blackFace}

/-- The bijections joining every white face of `R` to an adjacent black face. -/
private def adjEquivs (R : Finset TriFace) : Set (whiteFaces R ≃ blackFaces R) :=
  {σ | ∀ f, ∃ e, e ∈ f.val.edges ∧ e ∈ (σ f).val.edges}

private theorem whiteFace_eq_val {e : TriEdge} (f : whiteFaces R) (he : e ∈ f.val.edges) :
    e.whiteFace = f.val :=
  (TriEdge.eq_whiteFace_of_mem_edges he (mem_whiteFaces.1 f.property).2).symm

private theorem blackFace_eq_val {e : TriEdge} (g : blackFaces R) (he : e ∈ g.val.edges) :
    e.blackFace = g.val :=
  (TriEdge.eq_blackFace_of_mem_edges he (mem_blackFaces.1 g.property).2).symm

variable {σ τ : whiteFaces R ≃ blackFaces R}

/-- The edge shared by a white face `f` and the adjacent black face `σ f`. -/
private noncomputable def adjEdge (hσ : σ ∈ adjEquivs R) (f : whiteFaces R) : TriEdge :=
  (hσ f).choose

private theorem adjEdge_mem_edges (hσ : σ ∈ adjEquivs R) (f : whiteFaces R) :
    adjEdge hσ f ∈ f.val.edges ∧ adjEdge hσ f ∈ (σ f).val.edges :=
  (hσ f).choose_spec

private theorem whiteFace_adjEdge (hσ : σ ∈ adjEquivs R) (f : whiteFaces R) :
    (adjEdge hσ f).whiteFace = f.val :=
  whiteFace_eq_val f (adjEdge_mem_edges hσ f).1

private theorem blackFace_adjEdge (hσ : σ ∈ adjEquivs R) (f : whiteFaces R) :
    (adjEdge hσ f).blackFace = (σ f).val :=
  blackFace_eq_val (σ f) (adjEdge_mem_edges hσ f).2

private theorem edgesOfEquiv_eq_range (hσ : σ ∈ adjEquivs R) :
    edgesOfEquiv σ = Set.range (adjEdge hσ) := by
  ext e
  constructor
  · rintro ⟨f, hw, hb⟩
    exact ⟨f, TriEdge.eq_of_whiteFace_eq_of_blackFace_eq (by rw [whiteFace_adjEdge, hw])
      (by rw [blackFace_adjEdge, hb])⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, (whiteFace_adjEdge hσ f).symm, (blackFace_adjEdge hσ f).symm⟩

private theorem adjEdge_injective (hσ : σ ∈ adjEquivs R) : Function.Injective (adjEdge hσ) :=
  fun f f' h => Subtype.ext (by rw [← whiteFace_adjEdge hσ f, h, whiteFace_adjEdge])

/-- The edges shared by the white faces and their images under `σ` form a tiling of `R`. -/
private theorem isTiling_edgesOfEquiv (hσ : σ ∈ adjEquivs R) :
    IsTiling (R : Set TriFace) (edgesOfEquiv σ) := by
  have key (f : whiteFaces R) (h : TriFace) :
      adjEdge hσ f ∈ h.edges ↔ h = f.val ∨ h = (σ f).val := by
    rw [TriFace.mem_edges_iff, whiteFace_adjEdge, blackFace_adjEdge]
  rw [edgesOfEquiv_eq_range hσ]
  refine isTiling_def.2 ⟨?_, fun h hh => ?_⟩
  · rintro _ ⟨f, rfl⟩ h hh
    rcases (key f h).1 hh with rfl | rfl
    exacts [(mem_whiteFaces.1 f.property).1, (mem_blackFaces.1 (σ f).property).1]
  -- The face `h` is a white face `f₀` or the image of one; its edge is `adjEdge hσ f₀`.
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, h = f₀.val ∨ h = (σ f₀).val := by
    cases hc : h.isWhite
    · exact ⟨σ.symm ⟨h, mem_blackFaces.2 ⟨hh, hc⟩⟩, Or.inr (by simp)⟩
    · exact ⟨⟨h, mem_whiteFaces.2 ⟨hh, hc⟩⟩, Or.inl rfl⟩
  refine ⟨adjEdge hσ f₀, ⟨⟨f₀, rfl⟩, (key f₀ h).2 hf₀⟩, ?_⟩
  rintro _ ⟨⟨f, rfl⟩, hfh⟩
  congr 1
  rcases (key f h).1 hfh with h₁ | h₁ <;> rcases hf₀ with h₂ | h₂
  · exact Subtype.ext (h₁.symm.trans h₂)
  · exact (whiteFaces_val_ne f (σ f₀) (h₁.symm.trans h₂)).elim
  · exact (whiteFaces_val_ne f₀ (σ f) (h₂.symm.trans h₁)).elim
  · exact σ.injective (Subtype.ext (h₁.symm.trans h₂))

/-- The weight of the tiling of `σ` is the product of the entries `K(f, σ f)`. -/
private theorem finprod_edgesOfEquiv (hσ : σ ∈ adjEquivs R) (w : TriEdge → ℝ) :
    ∏ᶠ e ∈ edgesOfEquiv σ, w e = ∏ f, kasteleynMatrix R w f (σ f) := by
  rw [edgesOfEquiv_eq_range hσ, finprod_mem_range (adjEdge_injective hσ),
    finprod_eq_prod_of_fintype]
  exact Finset.prod_congr rfl fun f _ =>
    (kasteleynMatrix_apply_of_mem_edges (adjEdge_mem_edges hσ f).1
      (adjEdge_mem_edges hσ f).2).symm

/-- A bijection joining some white face to a non-adjacent black face contributes `0`. -/
private theorem prod_kasteleynMatrix_eq_zero (hσ : σ ∉ adjEquivs R) (w : TriEdge → ℝ) :
    ∏ f, kasteleynMatrix R w f (σ f) = 0 := by
  simp only [adjEquivs, Set.mem_ofPred_eq, not_forall] at hσ
  obtain ⟨f, hf⟩ := hσ
  refine Finset.prod_eq_zero (Finset.mem_univ f) (kasteleynMatrix_apply_of_not_adj fun h => hf ?_)
  obtain ⟨-, e, he⟩ := hexGraph_adj.1 h
  exact ⟨e, he⟩

private theorem eq_of_edgesOfEquiv_eq (hσ : σ ∈ adjEquivs R) (hτ : τ ∈ adjEquivs R)
    (h : edgesOfEquiv σ = edgesOfEquiv τ) : σ = τ := by
  refine Equiv.ext fun f => ?_
  have hf : adjEdge hσ f ∈ Set.range (adjEdge hτ) := by
    rw [← edgesOfEquiv_eq_range hτ, ← h, edgesOfEquiv_eq_range hσ]
    exact ⟨f, rfl⟩
  obtain ⟨f', hf'⟩ := hf
  obtain rfl : f' = f := Subtype.ext (by rw [← whiteFace_adjEdge hτ f', hf', whiteFace_adjEdge])
  exact Subtype.ext (by rw [← blackFace_adjEdge hσ, ← hf', blackFace_adjEdge])

/-- Every tiling of `R` is the tiling of a bijection joining every white face to an adjacent black
face: the black partner of a white face `f` is the second face of the edge of the tiling in `f`. -/
private theorem exists_edgesOfEquiv_eq {M : Set TriEdge} (hM : IsTiling (R : Set TriFace) M) :
    ∃ σ ∈ adjEquivs R, edgesOfEquiv σ = M := by
  choose ε hε hεu using fun f : whiteFaces R => hM.existsUnique (mem_whiteFaces.1 f.property).1
  have hw (f : whiteFaces R) : (ε f).whiteFace = f.val := whiteFace_eq_val f (hε f).2
  -- The white face of an edge `e ∈ M` is the white face `f` with `ε f = e`.
  let fw {e : TriEdge} (he : e ∈ M) : whiteFaces R :=
    ⟨e.whiteFace, mem_whiteFaces.2 ⟨hM.whiteFace_mem he, e.whiteFace_isWhite⟩⟩
  have hεe {e : TriEdge} (he : e ∈ M) : ε (fw he) = e :=
    (hεu _ e ⟨he, e.mem_whiteFace_edges⟩).symm
  let p (f : whiteFaces R) : blackFaces R :=
    ⟨(ε f).blackFace, mem_blackFaces.2 ⟨hM.blackFace_mem (hε f).1, (ε f).blackFace_isWhite⟩⟩
  have hp : Function.Bijective p := by
    refine ⟨fun f f' h => Subtype.ext ?_, fun g => ?_⟩
    · have hb : (ε f).blackFace = (ε f').blackFace := congrArg Subtype.val h
      rw [← hw f, ← hw f', hM.eq_of_mem_edges (hε f).1 (hε f').1 (ε f).mem_blackFace_edges
        (hb ▸ (ε f').mem_blackFace_edges)]
    · obtain ⟨e, ⟨he, heg⟩, -⟩ := hM.existsUnique (mem_blackFaces.1 g.property).1
      exact ⟨fw he, Subtype.ext ((congrArg TriEdge.blackFace (hεe he)).trans
        (blackFace_eq_val g heg))⟩
  refine ⟨Equiv.ofBijective p hp, fun f => ⟨ε f, (hε f).2, (ε f).mem_blackFace_edges⟩, ?_⟩
  ext e
  refine ⟨fun ⟨f, hfw, hfb⟩ => ?_, fun he => ⟨fw he, rfl, congrArg TriEdge.blackFace (hεe he)⟩⟩
  rw [← TriEdge.eq_of_whiteFace_eq_of_blackFace_eq (e := ε f) (by rw [hw, hfw]) hfb]
  exact (hε f).1

/-- **The partition function as a permanent.** The partition function of a finite region is the
sum, over the bijections `σ` from its white onto its black faces, of `∏_f K_R(f, σ f)`: the
nonzero terms are those of the bijections joining every white face to an adjacent black face, and
the edges they join form the tilings of the region, each exactly once. -/
theorem partitionFunction_eq_sum_prod_kasteleynMatrix (R : Finset TriFace) (w : TriEdge → ℝ) :
    partitionFunction R w =
      ∑ σ : whiteFaces R ≃ blackFaces R, ∏ f, kasteleynMatrix R w f (σ f) := by
  classical
  have hbij : Set.BijOn edgesOfEquiv (adjEquivs R) {M | IsTiling (R : Set TriFace) M} :=
    ⟨fun σ hσ => isTiling_edgesOfEquiv hσ, fun σ hσ τ hτ h => eq_of_edgesOfEquiv_eq hσ hτ h,
      fun M hM => exists_edgesOfEquiv_eq hM⟩
  rw [partitionFunction_def, ← finsum_mem_eq_of_bijOn edgesOfEquiv hbij
    fun σ hσ => (finprod_edgesOfEquiv hσ w).symm,
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
  exact Finset.sum_subset (Finset.subset_univ _) fun σ _ hσ =>
    prod_kasteleynMatrix_eq_zero (by simpa using hσ) w

end Bijection

/-- The partition function of a finite region is the permanent of its Kasteleyn matrix, squared
along any bijection `σ` from the black onto the white faces. -/
theorem partitionFunction_eq_permanent (R : Finset TriFace) (w : TriEdge → ℝ)
    (σ : blackFaces R ≃ whiteFaces R) :
    partitionFunction R w = ((kasteleynMatrix R w).submatrix id σ.symm).permanent := by
  rw [partitionFunction_eq_sum_prod_kasteleynMatrix, Matrix.permanent]
  refine Fintype.sum_equiv ((Equiv.equivCongr (Equiv.refl _) σ).trans (Equiv.inv _)) _ _
    fun τ => Fintype.prod_equiv (τ.trans σ) _ _ fun f => ?_
  simp [Equiv.Perm.inv_def]

end TauCeti
