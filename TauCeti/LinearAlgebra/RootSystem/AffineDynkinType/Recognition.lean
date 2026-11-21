/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.SingularCartanMatrix
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.AffineSubgraph
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.IntegralNullVector
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.SpecialNodes

/-!
# Recognition of the affine simply-laced diagrams

A connected finite simple graph `G` carries a nonzero weight `a : V → ℕ` with
`∑_{j ∼ i} a j = 2 * a i` at every vertex, that is a nonzero nonnegative integral null vector of
`2I - A`, exactly when `G` is isomorphic to the graph of a valid affine simply-laced diagram other
than `Ã₁`; that diagram is then unique. The possible graphs are therefore the cycles `Ãₙ` with
`n ≥ 2`, affine `Dₙ` with `n ≥ 4`, and affine `E₆`, `E₇` and `E₈`.

The marks of an affine diagram are such a weight on its graph. Conversely, a nonzero null vector
prevents `2I - A` from being positive definite, so `G` is not a Dynkin diagram and contains a copy
of the graph of an affine diagram
(`SimpleGraph.Connected.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Since
the marks of that diagram are a positive additive function, the proper-extension obstruction
`SimpleGraph.Copy.exists_iso_of_sum_le_two_mul` forces the copy to be all of `G`. The diagram is
unique by `TauCeti.AffineDynkinType.eq_of_graph_iso`: the graphs of distinct valid diagrams are
already told apart by their numbers of nodes, of leaves and of trivalent nodes.

Away from `Ã₁` this is Kac's characterisation of the connected affine diagrams by a positive null
vector, read on simple graphs; the double edge of `Ã₁` is not a simple-graph edge, so `Ã₁` is not
recognised by the simple-graph statement. Allowing non-negative integer off-diagonal entries brings
`Ã₁` back on equal footing: any symmetric, loop-free, connected matrix `M : Matrix ι ι ℕ` carrying
a positive vector `δ` with `δ i₀ = 1` and `M *ᵥ δ = 2 • δ` is isomorphic to `2I - t.cartanMatrix`
for a valid `t : AffineDynkinType`, with `δ` matching `t.marks` and `i₀` carried to `t.affineNode`
(`TauCeti.exists_affineDynkinType_of_symm_loopFree_nullVector`).

## Main results

* `SimpleGraph.Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso`: **the
  simple-graph recognition theorem** away from `Ã₁`.
* `SimpleGraph.Connected.posSemidef_and_det_eq_zero_iff_existsUnique_affineDynkinType_iso`: its
  semidefinite form, where the weight is replaced by the condition that `2I - A` is positive
  semidefinite and singular
  (`SimpleGraph.Preconnected.exists_sum_eq_two_mul_iff_posSemidef_and_det_eq_zero`).
* `TauCeti.exists_affineDynkinType_of_symm_loopFree_nullVector`: **matrix recognition** including
  `Ã₁`, with marks and affine-node normalization.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorem 4.3 and Table Aff 1.
* P. Etingof et al., *Introduction to representation theory*, Problem 5.3, for the semidefinite
  form of the classification.
-/

public section

namespace SimpleGraph

open Finset Matrix TauCeti

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Recognition of the affine simply-laced diagrams.** A connected finite simple graph carries a
nonzero weight `a : V → ℕ` with `∑_{j ∼ i} a j = 2 * a i` at every vertex exactly when it is
isomorphic to the graph of a unique valid affine simply-laced diagram other than `Ã₁`: a cycle
`Ãₙ` with `n ≥ 2`, affine `Dₙ` with `n ≥ 4`, or affine `E₆`, `E₇` or `E₈`. -/
theorem Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso
    (hG : G.Connected) :
    (∃ a : V → ℕ, a ≠ 0 ∧ ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) ↔
      ∃! t : AffineDynkinType, t.Valid ∧ t.IsGraphical ∧ Nonempty (G ≃g t.graph) := by
  classical
  constructor
  · rintro ⟨a, ha, hsum⟩
    -- A nonzero null vector of `2I - A` rules out positive definiteness, so `G` is not a Dynkin
    -- diagram and contains the graph of an affine diagram.
    have hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      rw [← exists_valid_isSimplyLaced_dynkinType_iso_iff, ← posDef_graphCartanMatrix_iff hG]
      intro hpos
      have hx : (fun i ↦ (a i : ℚ)) ≠ 0 := fun h ↦ ha (funext fun i ↦ by simpa using congrFun h i)
      have hnull : G.graphCartanMatrix ℚ *ᵥ (fun i ↦ (a i : ℚ)) = 0 :=
        graphCartanMatrix_mulVec_eq_zero G fun i ↦ by exact_mod_cast hsum i
      simpa [hnull] using hpos.dotProduct_mulVec_pos hx
    obtain ⟨t, ht, hg, ⟨f⟩⟩ :=
      hG.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso hD
    -- The marks are a positive additive function on that graph, so the copy is all of `G`.
    obtain ⟨e, -⟩ := f.exists_iso_of_sum_le_two_mul hG.preconnected AffineDynkinType.marks_pos
      (AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg) (a := fun i ↦ (a i : ℤ))
      (fun i ↦ by simp)
      (fun h ↦ ha (funext fun i ↦ by simpa using congrFun h i))
      (fun i ↦ by exact_mod_cast (hsum i).le)
    exact ⟨t, ⟨ht, hg, ⟨e.symm⟩⟩, fun t' ⟨ht', _, ⟨e'⟩⟩ ↦
      AffineDynkinType.eq_of_graph_iso ht' ht (e'.symm.trans e.symm)⟩
  · rintro ⟨t, ⟨ht, hg, ⟨e⟩⟩, -⟩
    -- The marks, transported along the isomorphism.
    refine ⟨fun v ↦ (t.marks (e v)).toNat, fun h ↦ ?_, fun i ↦ ?_⟩
    · simpa using congrFun h (e.symm t.affineNode)
    · have hsum : ∑ j ∈ G.neighborFinset i, t.marks (e j) = 2 * t.marks (e i) := by
        rw [← AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg (e i)]
        exact sum_equiv e.toEquiv (fun j ↦ by simp [e.map_adj_iff]) fun _ _ ↦ rfl
      have hpos (v : V) : ((t.marks (e v)).toNat : ℤ) = t.marks (e v) :=
        Int.toNat_of_nonneg (AffineDynkinType.marks_pos _).le
      exact (Nat.cast_inj (R := ℤ)).1 (by push_cast [hpos]; exact hsum)

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
  [TrivialStar R]

/-- **The semidefinite form of the recognition theorem.** For a connected finite simple graph,
`2I - A` over a linearly ordered field is positive semidefinite and singular exactly when the
graph is isomorphic to the graph of a unique valid affine simply-laced diagram other than `Ã₁`. -/
theorem Connected.posSemidef_and_det_eq_zero_iff_existsUnique_affineDynkinType_iso
    [DecidableEq V] (hG : G.Connected) :
    (G.graphCartanMatrix R).PosSemidef ∧ (G.graphCartanMatrix R).det = 0 ↔
      ∃! t : AffineDynkinType, t.Valid ∧ t.IsGraphical ∧ Nonempty (G ≃g t.graph) := by
  rw [← hG.preconnected.exists_sum_eq_two_mul_iff_posSemidef_and_det_eq_zero R]
  exact hG.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso

end SimpleGraph

namespace TauCeti

open Finset

section MatrixRecognition

variable {ι : Type*} [Fintype ι]

private abbrev IsAffineMatrixLabelling (M : Matrix ι ι ℕ) (i₀ : ι) (δ : ι → ℕ)
    (t : AffineDynkinType) (e : ι ≃ Fin t.nodes) : Prop :=
  t.Valid ∧
    (∀ x y : ι, (M x y : ℤ) = 2 * (if e x = e y then 1 else 0) - t.cartanMatrix (e x) (e y)) ∧
    (∀ x : ι, (δ x : ℤ) = t.marks (e x)) ∧
    e i₀ = t.affineNode

/-- Multi-edge branch (`2 ≤ M a b`): additive balance forces two vertices with a double edge. -/
private theorem exists_affineDynkinType_A_one_of_two_le
    (M : Matrix ι ι ℕ) (hSymm : M.IsSymm) (hLoop : ∀ i, M i i = 0) (i₀ : ι)
    (hReach : ∀ x y : ι, Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < M x y) x y)
    (δ : ι → ℕ) (hδ_pos : ∀ i, 0 < δ i) (hδ_one : δ i₀ = 1)
    (hδ_sum : ∀ i, ∑ j, M i j * δ j = 2 * δ i) {a b : ι} (hab2 : 2 ≤ M a b) :
    ∃ (t : AffineDynkinType) (e : ι ≃ Fin t.nodes), IsAffineMatrixLabelling M i₀ δ t e := by
  classical
  have hab : a ≠ b := fun h ↦ by rw [h, hLoop b] at hab2; omega
  have hle (x y : ι) : M x y * δ y ≤ 2 * δ x :=
    hδ_sum x ▸ single_le_sum (f := fun j ↦ M x j * δ j) (fun _ _ ↦ Nat.zero_le _) (mem_univ y)
  have hδ_le1 : 2 * δ b ≤ 2 * δ a := (Nat.mul_le_mul_right (δ b) hab2).trans (hle a b)
  have hδ_le2 : 2 * δ a ≤ 2 * δ b :=
    (Nat.mul_le_mul_right (δ a) (hSymm.apply a b ▸ hab2)).trans (hle b a)
  have hδ_ab : δ a = δ b := by omega
  have hMab_eq : M a b = 2 := by
    have := hδ_pos b
    have := Nat.mul_le_mul_right (δ b) hab2
    have : M a b * δ b ≤ 2 * δ b := hδ_ab ▸ hle a b
    nlinarith
  have hMba_eq : M b a = 2 := (hSymm.apply a b).trans hMab_eq
  have hMa_other (j : ι) (hjb : j ≠ b) : M a j = 0 :=
    Matrix.apply_eq_zero_of_mulVec_apply_eq_mul (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
      (by simpa [Matrix.mulVec, dotProduct, hMab_eq, hδ_ab] using hδ_sum a) hjb (hδ_pos j).ne'
  have hMb_other (j : ι) (hja : j ≠ a) : M b j = 0 :=
    Matrix.apply_eq_zero_of_mulVec_apply_eq_mul (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
      (by simpa [Matrix.mulVec, dotProduct, hMba_eq, hδ_ab] using hδ_sum b) hja (hδ_pos j).ne'
  have hall_ab (k : ι) : k = a ∨ k = b := by
    suffices ∀ x y : ι, Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < M x y) x y →
        (x = a ∨ x = b) → (y = a ∨ y = b) from this a k (hReach a k) (Or.inl rfl)
    intro x y hxy
    induction hxy with
    | refl => exact id
    | tail _ hstep ih =>
      intro hx; rcases ih hx with rfl | rfl
      · exact Or.inr (by_contra fun hyb ↦ by have := hMa_other _ hyb; have := hstep.2; omega)
      · exact Or.inl (by_contra fun hya ↦ by have := hMb_other _ hya; have := hstep.2; omega)
  obtain ⟨c, hc_ne, hc_all, hMic, hMci, hδc⟩ :
      ∃ c : ι, i₀ ≠ c ∧ (∀ k : ι, k = i₀ ∨ k = c) ∧ M i₀ c = 2 ∧ M c i₀ = 2 ∧ δ c = 1 := by
    rcases hall_ab i₀ with rfl | rfl
    · exact ⟨b, hab, hall_ab, hMab_eq, hMba_eq, hδ_ab.symm.trans hδ_one⟩
    · exact ⟨a, hab.symm, fun k ↦ (hall_ab k).symm, hMba_eq, hMab_eq, hδ_ab.trans hδ_one⟩
  let e' : ι ≃ Fin 2 :=
    { toFun x := if x = i₀ then 0 else 1
      invFun j := if j = 0 then i₀ else c
      left_inv x := by rcases hc_all x with rfl | rfl <;> simp [hc_ne.symm]
      right_inv := Fin.forall_fin_two.2 ⟨by simp, by simp [hc_ne.symm]⟩ }
  let e : ι ≃ Fin (AffineDynkinType.A 1).nodes := e'
  refine ⟨AffineDynkinType.A 1, e, AffineDynkinType.valid_A.mpr le_rfl, fun x y ↦ ?_,
    fun x ↦ ?_, ?_⟩
  · rw [AffineDynkinType.cartanMatrix_A_one_apply]; simp only [e.injective.eq_iff]
    rcases hc_all x with rfl | rfl <;> rcases hc_all y with rfl | rfl <;>
      simp [hLoop, hc_ne, hc_ne.symm, hMic, hMci]
  · rw [AffineDynkinType.marks_A_apply]; rcases hc_all x with rfl | rfl <;> simp [hδ_one, hδc]
  · rw [AffineDynkinType.affineNode_A]; exact (ite_eq_left rfl : e' i₀ = 0)

/-- `{0, 1}` graphical branch: recognized by Kac's theorem and normalized at `i₀`. -/
private theorem exists_affineDynkinType_of_le_one
    (M : Matrix ι ι ℕ) (hSymm : M.IsSymm) (hLoop : ∀ i, M i i = 0) (i₀ : ι)
    (hReach : ∀ x y : ι, Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < M x y) x y)
    (δ : ι → ℕ) (hδ_one : δ i₀ = 1) (hδ_sum : ∀ i, ∑ j, M i j * δ j = 2 * δ i)
    (hM_le1 : ∀ x y : ι, M x y ≤ 1) :
    ∃ (t : AffineDynkinType) (e : ι ≃ Fin t.nodes), IsAffineMatrixLabelling M i₀ δ t e := by
  classical
  let G : SimpleGraph ι :=
    { Adj x y := M x y ≠ 0
      symm := ⟨fun x y hxy ↦ by rwa [← hSymm.apply x y] at hxy⟩
      loopless := ⟨fun x hx ↦ hx (hLoop x)⟩ }
  have hM_ite (x y : ι) : M x y = if G.Adj x y then 1 else 0 := by
    have := hM_le1 x y; dsimp [G]; split_ifs <;> omega
  have _ : Nonempty ι := ⟨i₀⟩
  have hG_conn : G.Connected := ⟨fun x y ↦ by
    induction hReach x y with
    | refl => exact SimpleGraph.Reachable.refl (G := G) _
    | tail _ hstep ih => exact ih.trans (SimpleGraph.Adj.reachable hstep.2.ne')⟩
  have hG_sum (i : ι) : ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i := by
    rw [← hδ_sum i, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ ↦ by by_cases hadj : G.Adj i j <;> simp [hM_ite, hadj]
  obtain ⟨t, ⟨ht, hg, ⟨iso⟩⟩, -⟩ :=
    hG_conn.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso.mp
      ⟨δ, fun h ↦ by simp [h] at hδ_one, hG_sum⟩
  have hgcd : univ.gcd δ = 1 := Nat.dvd_one.mp (hδ_one ▸ univ.gcd_dvd (f := δ) (mem_univ i₀))
  have hmarks_iso (x : ι) : (δ x : ℤ) = t.marks (iso x) := by
    simpa [hgcd] using congrFun (iso.eq_gcd_smul_marks_comp ht hg hG_sum) x
  obtain ⟨σ, hσ⟩ := AffineDynkinType.exists_graph_iso_apply_eq_affineNode ht
    (by rw [← hmarks_iso i₀, hδ_one, Nat.cast_one] : t.marks (iso i₀) = 1)
  let e_iso : G ≃g t.graph := iso.trans σ
  refine ⟨t, e_iso.toEquiv, ht, fun x y ↦ ?_, fun x ↦ ?_, hσ⟩
  · rw [AffineDynkinType.cartanMatrix_apply hg]
    simp only [RelIso.coe_fn_toEquiv, e_iso.injective.eq_iff, e_iso.map_adj_iff, hM_ite]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp only [hxy, ↓reduceIte]; split_ifs <;> norm_num
  · simp only [e_iso, RelIso.coe_fn_toEquiv, RelIso.trans_apply,
      AffineDynkinType.marks_graph_iso_apply, hmarks_iso]

/-- **Matrix recognition of the affine simply-laced diagrams.** Any symmetric, loop-free, connected
matrix `M : Matrix ι ι ℕ` admitting a positive vector `δ` with `δ i₀ = 1` and `M *ᵥ δ = 2 • δ` is
isomorphic to `2I - t.cartanMatrix` for a valid `t : AffineDynkinType`, with `δ` matching `t.marks`
and `i₀` mapped to `t.affineNode`. -/
theorem exists_affineDynkinType_of_symm_loopFree_nullVector
    (M : Matrix ι ι ℕ) (hSymm : M.IsSymm) (hLoop : ∀ i, M i i = 0)
    (i₀ : ι) (hConn : ∀ i, Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < M x y) i i₀)
    (δ : ι → ℕ) (hδ_pos : ∀ i, 0 < δ i) (hδ_one : δ i₀ = 1)
    (hδ_sum : ∀ i, ∑ j, M i j * δ j = 2 * δ i) :
    ∃ (t : AffineDynkinType) (e : ι ≃ Fin t.nodes),
      t.Valid ∧
        (∀ x y : ι,
          (M x y : ℤ) = 2 * (if e x = e y then 1 else 0) - t.cartanMatrix (e x) (e y)) ∧
        (∀ x : ι, (δ x : ℤ) = t.marks (e x)) ∧
        e i₀ = t.affineNode := by
  classical
  let r : ι → ι → Prop := fun x y ↦ x ≠ y ∧ 0 < M x y
  have hsymm_rtg {x y : ι} (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.head ⟨hstep.1.symm, hSymm.apply _ _ ▸ hstep.2⟩
  have hReach (x y : ι) : Relation.ReflTransGen r x y := (hConn x).trans (hsymm_rtg (hConn y))
  if hMult : ∃ a b : ι, 2 ≤ M a b then
    obtain ⟨a, b, hab2⟩ := hMult
    exact exists_affineDynkinType_A_one_of_two_le M hSymm hLoop i₀ hReach δ hδ_pos hδ_one hδ_sum
      hab2
  else
    exact exists_affineDynkinType_of_le_one M hSymm hLoop i₀ hReach δ hδ_one hδ_sum
      fun x y ↦ Nat.le_of_not_lt fun h ↦ hMult ⟨x, y, h⟩

end MatrixRecognition

end TauCeti
