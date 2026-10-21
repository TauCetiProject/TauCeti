/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimplyLaced
import TauCeti.LinearAlgebra.Matrix.ZMatrix

/-!
# Simple graphs of finite type

A finite simple graph `G` with adjacency matrix `A` is read as a simply-laced diagram through its
generalized Cartan matrix `2I - A` (`SimpleGraph.graphCartanMatrix`). This file connects that
matrix with the finite-type Cartan matrices of `TauCeti.IsFiniteType` and their classification:
the diagram of `2I - A` is `G` itself, a positive definite `2I - A` over any linear ordered field is
of finite type, and a connected graph whose `2I - A` is of finite type is isomorphic to the diagram
of the standard Cartan matrix of a valid simply-laced Dynkin type. In other words, a connected
simple graph has a positive definite form `2I - A` exactly when it is a Dynkin diagram of type `A`,
`D` or `E`.

## Main results

* `SimpleGraph.diagramGraph_graphCartanMatrix`: the diagram of `2I - A` is `G`.
* `SimpleGraph.isFiniteType_graphCartanMatrix_of_posDef`: if `2I - A` is positive definite over a
  linear ordered field, then it is of finite type.
* `SimpleGraph.exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix`: a connected graph whose
  `2I - A` is of finite type is isomorphic to the diagram of a valid simply-laced Dynkin type.
* `SimpleGraph.graphCartanMatrix_diagramGraph_cartanMatrix`: the standard Cartan matrix of a
  Dynkin type whose Cartan matrix is simply laced is `2I - A` of its diagram.
* `SimpleGraph.posDef_graphCartanMatrix_iff`: a connected graph has a positive definite `2I - A`
  exactly when it is isomorphic to the diagram of a valid simply-laced Dynkin type.
* `TauCeti.DynkinType.exists_isSimplyLaced_diagramGraph_iso` and
  `SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff`: every standard Dynkin diagram is
  isomorphic as a simple graph to the diagram of a simply-laced Dynkin type.
* `TauCeti.DynkinType.isAcyclic_diagramGraph_cartanMatrix` and
  `TauCeti.DynkinType.isBipartite_diagramGraph_cartanMatrix`: every standard Dynkin diagram is
  acyclic and bipartite.
* `SimpleGraph.exists_pos_two_mul_le_sum_of_not_exists_dynkinType_iso`: a connected graph which is
  not a Dynkin diagram carries a positive weight `δ` with `2 δ i ≤ ∑_{j ∼ i} δ j` at every vertex;
  such a graph has no isolated vertex
  (`SimpleGraph.exists_adj_of_pos_two_mul_le_sum`,
  in `Combinatorics/SimpleGraph/AdditiveFunction.lean`).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4.
-/

public section

namespace SimpleGraph

open Matrix TauCeti

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The diagram of the generalized Cartan matrix `2I - A` of a simple graph is the graph itself. -/
@[simp]
theorem diagramGraph_graphCartanMatrix : diagramGraph (G.graphCartanMatrix ℤ) = G := by
  ext i j
  rw [diagramGraph_adj, graphCartanMatrix_apply, graphCartanMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp only [hij, hij.symm, ne_eq, not_false_eq_true, ↓reduceIte, true_and, G.adj_comm j i]
    split_ifs <;> simp_all

variable {G} [Finite V]

/-- **A positive definite graph Cartan matrix is of finite type.** If `2I - A` is positive
definite over some linear ordered field, then the integer matrix `2I - A` is of finite type. -/
theorem isFiniteType_graphCartanMatrix_of_posDef {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] (h : (G.graphCartanMatrix R).PosDef) :
    IsFiniteType (G.graphCartanMatrix ℤ) := by
  have : Fintype V := Fintype.ofFinite V
  refine isFiniteType_of_posDef_map_intCast (fun i ↦ by simp) (fun i j hij ↦ ?_) ?_
  · simp only [graphCartanMatrix_apply, hij, ↓reduceIte]
    split_ifs <;> simp
  have hmap : (G.graphCartanMatrix ℤ).map (Int.cast : ℤ → ℚ) = G.graphCartanMatrix ℚ :=
    graphCartanMatrix_map G (Int.castRingHom ℚ)
  rw [hmap, posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_iff_isSymm.mpr (isSymm_graphCartanMatrix G), fun x hx ↦ ?_⟩
  -- Read the rational vector `x` in `R`, where the form is positive.
  have hx' : Rat.castHom R ∘ x ≠ 0 := fun h0 ↦
    hx (funext fun i ↦ by simpa using congrFun h0 i)
  have hpos := h.dotProduct_mulVec_pos hx'
  rw [← graphCartanMatrix_map G (Rat.castHom R), star_trivial] at hpos
  have hcast : Rat.castHom R (x ⬝ᵥ G.graphCartanMatrix ℚ *ᵥ x) =
      Rat.castHom R ∘ x ⬝ᵥ (G.graphCartanMatrix ℚ).map (Rat.castHom R) *ᵥ (Rat.castHom R ∘ x) := by
    rw [RingHom.map_dotProduct]
    congr 1
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [← hcast, Rat.coe_castHom, Rat.cast_pos] at hpos
  rwa [star_trivial]

omit [Finite V] in
/-- **A connected graph of finite type is a simply-laced Dynkin diagram.** If the generalized
Cartan matrix `2I - A` of a connected simple graph `G` is of finite type, then `G` is isomorphic to
the diagram of the standard Cartan matrix of a valid Dynkin type, which is of type `A`, `D` or `E`:
the standard matrix is a relabelling of `2I - A`, whose off-diagonal entries are `0` or `-1`. -/
theorem exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix (hG : G.Connected)
    (h : IsFiniteType (G.graphCartanMatrix ℤ)) :
    ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    h.existsUnique_dynkinType ((diagramGraph_graphCartanMatrix G).symm ▸ hG)
  have hG' : G = (diagramGraph t.cartanMatrix).comap e := by
    rw [← diagramGraph_submatrix e.injective, ← diagramGraph_graphCartanMatrix G]
    exact congrArg diagramGraph (Matrix.ext he)
  have hsl : t.cartanMatrix.IsSimplyLaced := fun i j hij ↦ by
    have hij' : e.symm i ≠ e.symm j := e.symm.injective.ne hij
    have hentry := he (e.symm i) (e.symm j)
    rw [e.apply_symm_apply, e.apply_symm_apply, graphCartanMatrix_apply] at hentry
    simp only [hij', ↓reduceIte] at hentry
    split_ifs at hentry <;> simp [← hentry]
  refine ⟨t, ht, (DynkinType.isSimplyLaced_cartanMatrix_iff_of_valid ht).mp hsl, ⟨?_⟩⟩
  rw [hG']
  exact Iso.comap e _

/-- **The diagram of a simply-laced standard Cartan matrix recovers that matrix**: for a Dynkin
type whose Cartan matrix is simply laced, the matrix is `2I - A` of its diagram. -/
@[simp]
theorem graphCartanMatrix_diagramGraph_cartanMatrix {t : DynkinType}
    (ht : t.cartanMatrix.IsSimplyLaced) :
    (diagramGraph t.cartanMatrix).graphCartanMatrix ℤ = t.cartanMatrix := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  have hzero := DynkinType.cartanMatrix_apply_eq_zero_iff_symm t i j
  rcases ht hij with h | h <;> simp [h] at hzero <;> simp [hij, h, hzero]

omit [Finite V] in
/-- **A graph isomorphic to the diagram of a simply-laced standard Cartan matrix has a positive
definite `2I - A`.** The matrix `2I - A` of the diagram is the standard Cartan matrix
(`SimpleGraph.graphCartanMatrix_diagramGraph_cartanMatrix`), which is positive definite, and an
isomorphism of graphs relabels `2I - A`. -/
theorem posDef_graphCartanMatrix_of_iso {t : DynkinType} (ht : t.cartanMatrix.IsSimplyLaced)
    (φ : G ≃g diagramGraph t.cartanMatrix) : (G.graphCartanMatrix ℚ).PosDef := by
  have hrel : G.graphCartanMatrix ℚ =
      (t.cartanMatrix.map (Int.cast : ℤ → ℚ)).submatrix φ φ := by
    ext i j
    have hentry := congrFun₂ (graphCartanMatrix_diagramGraph_cartanMatrix ht) (φ i) (φ j)
    simp only [graphCartanMatrix_apply, φ.injective.eq_iff, φ.map_adj_iff] at hentry
    rw [Matrix.submatrix_apply, Matrix.map_apply, ← hentry, graphCartanMatrix_apply]
    split_ifs <;> simp
  rw [hrel]
  exact (t.posDef_map_intCast_cartanMatrix_of_isSimplyLaced ht).submatrix φ.injective

/-- **A connected graph has a positive definite `2I - A` exactly when it is a simply-laced Dynkin
diagram**, that is, isomorphic to the diagram of a valid Dynkin type of type `A`, `D` or `E`. -/
theorem posDef_graphCartanMatrix_iff (hG : G.Connected) :
    (G.graphCartanMatrix ℚ).PosDef ↔ ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
      Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
  have := Fintype.ofFinite V
  exact ⟨fun h ↦ exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix hG
      (isFiniteType_graphCartanMatrix_of_posDef h),
    fun ⟨t, _, ht, ⟨φ⟩⟩ ↦ posDef_graphCartanMatrix_of_iso
      ((DynkinType.isSimplyLaced_cartanMatrix_iff t).mpr (.inl ht)) φ⟩

/-- Every simply-laced standard Dynkin diagram is acyclic. -/
theorem _root_.TauCeti.DynkinType.IsSimplyLaced.isAcyclic_diagramGraph_cartanMatrix {t : DynkinType}
    (hs : t.IsSimplyLaced) : (diagramGraph t.cartanMatrix).IsAcyclic := by
  have h := (isFiniteType_graphCartanMatrix_of_posDef
    (posDef_graphCartanMatrix_of_iso
      ((DynkinType.isSimplyLaced_cartanMatrix_iff t).mpr (.inl hs))
      Iso.refl)).isAcyclic_diagramGraph
  rwa [diagramGraph_graphCartanMatrix] at h

/-- Every standard Dynkin diagram is isomorphic to the diagram of a simply-laced Dynkin type of the
same rank (preserving validity), since the underlying simple graphs of `Bₙ`, `Cₙ`, `F₄`, and `G₂`
are path graphs. -/
theorem _root_.TauCeti.DynkinType.exists_isSimplyLaced_diagramGraph_iso (t : DynkinType) :
    ∃ s : DynkinType, s.IsSimplyLaced ∧ (t.Valid → s.Valid) ∧
      Nonempty (diagramGraph t.cartanMatrix ≃g diagramGraph s.cartanMatrix) := by
  have hpath {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G = pathGraph n) :
      Nonempty (G ≃g diagramGraph (CartanMatrix.A n)) := by
    rw [hG, DynkinType.diagramGraph_cartanMatrix_A]
    exact ⟨Iso.refl⟩
  cases t with
  | A n | D n | E6 | E7 | E8 => exact ⟨_, by simp, id, ⟨Iso.refl⟩⟩
  | B n =>
    refine ⟨.A n, by simp, fun h => by have := DynkinType.valid_B.mp h; simp; omega, ?_⟩
    simpa only [DynkinType.rank_B, DynkinType.cartanMatrix_B, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph (CartanMatrix.B n)) <| by
      ext i j
      rw [diagramGraph_adj, pathGraph_adj]
      simp [CartanMatrix.B, Fin.ext_iff]
      omega
  | C n =>
    refine ⟨.A n, by simp, fun h => by have := DynkinType.valid_C.mp h; simp; omega, ?_⟩
    simpa only [DynkinType.rank_C, DynkinType.cartanMatrix_C, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph (CartanMatrix.C n)) <| by
      ext i j
      rw [diagramGraph_adj, pathGraph_adj]
      simp [CartanMatrix.C, Fin.ext_iff]
      omega
  | F4 =>
    refine ⟨.A 4, by simp, fun _ => by simp, ?_⟩
    simpa only [DynkinType.rank_F4, DynkinType.cartanMatrix_F4, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph CartanMatrix.F₄) <| by
      ext i j
      fin_cases i <;> fin_cases j <;> decide
  | G2 =>
    refine ⟨.A 2, by simp, fun _ => by simp, ?_⟩
    simpa only [DynkinType.rank_G2, DynkinType.cartanMatrix_G2, DynkinType.rank_A,
      DynkinType.cartanMatrix_A] using hpath (G := diagramGraph CartanMatrix.G₂.transpose) <| by
      ext i j
      fin_cases i <;> fin_cases j <;> decide

/-- Every standard Dynkin diagram is acyclic. -/
theorem _root_.TauCeti.DynkinType.isAcyclic_diagramGraph_cartanMatrix (t : DynkinType) :
    (diagramGraph t.cartanMatrix).IsAcyclic := by
  obtain ⟨s, hs, -, ⟨e⟩⟩ := t.exists_isSimplyLaced_diagramGraph_iso
  exact e.isAcyclic_iff.mpr hs.isAcyclic_diagramGraph_cartanMatrix

/-- Every standard Dynkin diagram is bipartite. -/
theorem _root_.TauCeti.DynkinType.isBipartite_diagramGraph_cartanMatrix (t : DynkinType) :
    (diagramGraph t.cartanMatrix).IsBipartite :=
  t.isAcyclic_diagramGraph_cartanMatrix.isBipartite

omit [DecidableEq V] [DecidableRel G.Adj] [Finite V] in
/-- A simple graph is isomorphic to the diagram of a valid simply-laced Dynkin type if and only if
it is isomorphic to the diagram of a valid Dynkin type. -/
theorem exists_valid_isSimplyLaced_dynkinType_iso_iff (G : SimpleGraph V) :
    (∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) ↔
      ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
  ⟨fun ⟨t, ht, _, h⟩ => ⟨t, ht, h⟩, fun ⟨t, ht, ⟨e⟩⟩ =>
    let ⟨s, hs, hval, ⟨f⟩⟩ := t.exists_isSimplyLaced_diagramGraph_iso
    ⟨s, hval ht, hs, ⟨e.trans f⟩⟩⟩

/-! ### Superadditive weights on graphs of infinite type -/

omit [Finite V] in
/-- **A graph whose `2I - A` is not positive definite carries a superadditive weight**: a nonzero
nonnegative real weight `δ` with `2 δ i ≤ ∑_{j ∼ i} δ j` at every vertex. -/
theorem exists_nonneg_two_mul_le_sum_of_not_posDef [Fintype V]
    (h : ¬ (G.graphCartanMatrix ℝ).PosDef) :
    ∃ δ : V → ℝ, 0 ≤ δ ∧ δ ≠ 0 ∧ ∀ i, 2 * δ i ≤ ∑ j ∈ G.neighborFinset i, δ j := by
  obtain ⟨δ, hδ0, hδ, hMδ⟩ := Matrix.exists_nonneg_mulVec_nonpos_of_not_posDef
    G.isSymm_graphCartanMatrix (fun i j hij ↦ by
      simp only [graphCartanMatrix_apply, hij, ↓reduceIte]
      split_ifs <;> norm_num) h
  refine ⟨δ, hδ0, hδ, fun i ↦ ?_⟩
  have hi := hMδ i
  rw [Pi.zero_apply, graphCartanMatrix_mulVec_apply] at hi
  linarith

omit [Finite V] [DecidableEq V] in
/-- **A connected non-Dynkin graph carries a positive superadditive weight.** If a connected finite
simple graph `G` is not isomorphic to the diagram of any valid Dynkin type, then some real weight
`δ`, positive at every vertex, satisfies `2 δ i ≤ ∑_{j ∼ i} δ j` at every vertex. -/
theorem exists_pos_two_mul_le_sum_of_not_exists_dynkinType_iso [Fintype V] (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ δ : V → ℝ, (∀ i, 0 < δ i) ∧ ∀ i, 2 * δ i ≤ ∑ j ∈ G.neighborFinset i, δ j := by
  classical
  obtain ⟨δ, hδ0, hδ, hδle⟩ := exists_nonneg_two_mul_le_sum_of_not_posDef fun h ↦ hD <| by
    obtain ⟨t, ht, -, hφ⟩ := exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix hG
      (isFiniteType_graphCartanMatrix_of_posDef h)
    exact ⟨t, ht, hφ⟩
  exact hG.exists_pos_smul_le_sum (c := (2 : ℝ)) hδ0 hδ hδle

end SimpleGraph
