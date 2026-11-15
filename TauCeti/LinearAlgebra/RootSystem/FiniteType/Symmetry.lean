/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
import TauCeti.Combinatorics.SimpleGraph.Automorphism
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.UniqueBranch
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TypeA
import TauCeti.LinearAlgebra.RootSystem.SpecialNodePermutations

/-!
# Matrix symmetries and orbit orthogonality for finite-type Cartan matrices

A permutation `σ ∈ TauCeti.matrixSymmetryGroup A` preserving a square integer matrix `A` acts as a
graph automorphism on its diagram `TauCeti.diagramGraph A`. For connected finite-type Cartan
matrices, combining the Cartan-Killing classification with the tree and path-graph automorphism
results in `TauCeti.Combinatorics.SimpleGraph.Automorphism` determines both when nontrivial matrix
symmetries exist and when an orbit can contain an edge:

1. **Rigidity of non-simply-laced diagrams.** None of `Bₙ`, `Cₙ`, `F₄`, or `G₂` admits a
   nontrivial permutation preserving its Cartan matrix: on `Bₙ` (`2 ≤ n`) the underlying diagram is
   the path graph `pathGraph n`, whose only non-identity automorphism is reversal, and reversal
   moves the oriented double bond `(n - 2, n - 1)` with entry `-2` to `(1, 0)` with entry `-1`; `Cₙ`
   is the transpose of `Bₙ`; and `F₄` and `G₂` are rigid by
   `TauCeti.DynkinType.eq_one_of_cartanMatrix_F4` and
   `TauCeti.DynkinType.eq_one_of_cartanMatrix_G2`. Hence every connected non-simply-laced
   finite-type Cartan matrix has `matrixSymmetryGroup A = ⊥`.
2. **Orbit dichotomy for simply-laced diagrams.** For a connected simply-laced finite-type Cartan
   matrix `A` and any `σ ∈ matrixSymmetryGroup A`, either every `σ`-orbit is pairwise orthogonal
   (`A i j = 0` for distinct `i, j` in the same cycle of `σ`), or `A` reindexes to `A₂ₙ` (`1 ≤ n`)
   with `σ` acting as the chain reversal `Fin.rev`. Indeed, if `diagramGraph A` has a branch vertex
   of degree `3`, `TauCeti.IsFiniteType.eq_of_degree_eq_three` makes that vertex unique, so `σ`
   fixes it and every `σ`-orbit on the tree `diagramGraph A` is independent; otherwise every vertex
   has degree at most `2`, `A` reindexes to `Aₘ`, `σ` is the identity or `graphPermA m`, and odd
   chains still have independent reversal orbits while even chains `A₂ₙ` have `{n - 1, n}` as their
   unique adjacent reversal orbit.

We also record `TauCeti.DynkinType.diagramSymmetry_E7_eq_bot` alongside the existing `E₈` rigidity
theorem.

## Main definitions

* `TauCeti.diagramGraphIsoOfMemMatrixSymmetryGroup`: the automorphism of `diagramGraph A` induced
  by a permutation in `matrixSymmetryGroup A`.

## Main results

* `TauCeti.DynkinType.diagramGraph_cartanMatrix_B` and
  `TauCeti.DynkinType.diagramGraph_cartanMatrix_C`: the underlying diagrams of `Bₙ` and `Cₙ` are
  the path graph `pathGraph n`.
* `TauCeti.DynkinType.eq_one_of_cartanMatrix_B`, `TauCeti.DynkinType.diagramSymmetry_B_eq_bot`,
  `TauCeti.DynkinType.eq_one_of_cartanMatrix_C`, `TauCeti.DynkinType.diagramSymmetry_C_eq_bot`,
  `TauCeti.DynkinType.diagramSymmetry_F4_eq_bot`, `TauCeti.DynkinType.diagramSymmetry_G2_eq_bot`,
  and `TauCeti.DynkinType.diagramSymmetry_eq_bot_of_not_isSimplyLaced`: no non-simply-laced Dynkin
  type has a nontrivial Cartan-matrix symmetry.
* `TauCeti.DynkinType.diagramSymmetry_E7_eq_bot`: the `E₇` diagram has no nontrivial symmetry.
* `TauCeti.DynkinType.mem_diagramSymmetry_A_iff`: the symmetries of `Aₙ` are `1` and `graphPermA n`.
* `TauCeti.DynkinType.cartanMatrix_A_even_ne_zero_of_sameCycle_graphPermA_iff`: in `A₂ₙ` (`1 ≤ n`),
  `{n - 1, n}` is the unique non-orthogonal orbit of `graphPermA (2 * n)`.
* `TauCeti.IsFiniteType.matrixSymmetryGroup_eq_bot_of_not_isSimplyLaced`: a connected
  non-simply-laced finite-type Cartan matrix has trivial symmetry group.
* `TauCeti.IsFiniteType.orbit_apply_eq_zero_or_typeA_even`: the simply-laced orbit-orthogonality /
  even-`A` reversal dichotomy for connected finite-type Cartan matrices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4, Plates I–IX.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, §2.
-/

public section

namespace TauCeti

/-! ## Graph automorphisms from matrix symmetries -/

/-- **A permutation in `matrixSymmetryGroup A` acts as an automorphism of `diagramGraph A`.** -/
def diagramGraphIsoOfMemMatrixSymmetryGroup {B : Type*} {A : Matrix B B ℤ} {σ : Equiv.Perm B}
    (hσ : σ ∈ matrixSymmetryGroup A) : diagramGraph A ≃g diagramGraph A where
  toEquiv := σ
  map_rel_iff' := fun {i j} ↦ by
    have hij := congrFun₂ (mem_matrixSymmetryGroup_iff.mp hσ) i j
    have hji := congrFun₂ (mem_matrixSymmetryGroup_iff.mp hσ) j i
    simp only [Matrix.submatrix_apply] at hij hji
    rw [diagramGraph_adj, diagramGraph_adj, σ.injective.ne_iff, hij, hji]

/-- Applying `diagramGraphIsoOfMemMatrixSymmetryGroup hσ` evaluates the underlying permutation `σ`.
-/
@[simp]
theorem diagramGraphIsoOfMemMatrixSymmetryGroup_apply {B : Type*} {A : Matrix B B ℤ}
    {σ : Equiv.Perm B} (hσ : σ ∈ matrixSymmetryGroup A) (i : B) :
    diagramGraphIsoOfMemMatrixSymmetryGroup hσ i = σ i :=
  (rfl)

/-- The underlying equivalence of `diagramGraphIsoOfMemMatrixSymmetryGroup hσ` is `σ`. -/
@[simp]
theorem diagramGraphIsoOfMemMatrixSymmetryGroup_toEquiv {B : Type*} {A : Matrix B B ℤ}
    {σ : Equiv.Perm B} (hσ : σ ∈ matrixSymmetryGroup A) :
    (diagramGraphIsoOfMemMatrixSymmetryGroup hσ).toEquiv = σ :=
  (rfl)

/-- Transporting a matrix symmetry along a simultaneous relabelling of rows and columns. -/
private lemma conj_mem_matrixSymmetryGroup {B C α : Type*} {A : Matrix B B α} {A' : Matrix C C α}
    (e : B ≃ C) (he : ∀ i j, A i j = A' (e i) (e j)) {σ : Equiv.Perm B}
    (hσ : σ ∈ matrixSymmetryGroup A) :
    e.symm.trans (σ.trans e) ∈ matrixSymmetryGroup A' := by
  refine mem_matrixSymmetryGroup_iff.mpr (Matrix.ext fun i j ↦ ?_)
  have hij := congrFun₂ (mem_matrixSymmetryGroup_iff.mp hσ) (e.symm i) (e.symm j)
  simp only [Matrix.submatrix_apply, Equiv.trans_apply] at hij ⊢
  rw [← he (σ (e.symm i)) (σ (e.symm j)), hij, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ## Diagram symmetries of standard Dynkin types -/

namespace DynkinType

/-- The underlying diagram graph of `CartanMatrix.B n` is `SimpleGraph.pathGraph n`. -/
theorem diagramGraph_cartanMatrix_B (n : ℕ) :
    (diagramGraph (CartanMatrix.B n) : _root_.SimpleGraph (Fin n)) =
      _root_.SimpleGraph.pathGraph n := by
  ext i j
  rw [diagramGraph_adj, _root_.SimpleGraph.pathGraph_adj]
  simp [CartanMatrix.B, Fin.ext_iff]
  omega

/-- The underlying diagram graph of `CartanMatrix.C n` is `SimpleGraph.pathGraph n`. -/
theorem diagramGraph_cartanMatrix_C (n : ℕ) :
    (diagramGraph (CartanMatrix.C n) : _root_.SimpleGraph (Fin n)) =
      _root_.SimpleGraph.pathGraph n := by
  rw [← CartanMatrix.B_transpose, ← diagramGraph_cartanMatrix_B]
  ext i j
  simp only [diagramGraph_adj, Matrix.transpose_apply]
  tauto

/-- **The identity is the only permutation preserving the type-`Bₙ` Cartan matrix.** On `2 ≤ n`
the diagram is `pathGraph n`, so any symmetry is either `1` or reversal, and reversal carries the
double-bond entry `-2` at `(n - 2, n - 1)` to the entry `-1` at `(1, 0)`. -/
theorem eq_one_of_cartanMatrix_B {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ∀ i j : Fin n, (B n).cartanMatrix (σ i) (σ j) = (B n).cartanMatrix i j) : σ = 1 := by
  rcases le_or_gt n 1 with hn | hn
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
    exact Equiv.ext fun i ↦ Subsingleton.elim _ _
  · have hmem : σ ∈ matrixSymmetryGroup (CartanMatrix.B n) :=
      mem_matrixSymmetryGroup_iff.mpr (Matrix.ext fun i j ↦ by simpa using h i j)
    let f : _root_.SimpleGraph.pathGraph n ≃g _root_.SimpleGraph.pathGraph n :=
      { toEquiv := σ
        map_rel_iff' := by
          intro i j
          rw [← diagramGraph_cartanMatrix_B n]
          exact (diagramGraphIsoOfMemMatrixSymmetryGroup hmem).map_rel_iff' }
    rcases _root_.SimpleGraph.pathGraph_iso_eq_refl_or_rev f with hrefl | hrev
    · exact Equiv.ext fun i ↦ congrArg (fun φ : _root_.SimpleGraph.pathGraph n ≃g _ ↦ φ i) hrefl
    · exfalso
      have hrev_apply (i : Fin n) : σ i = i.rev := by
        have hi := congrArg (fun φ : _root_.SimpleGraph.pathGraph n ≃g _ ↦ φ i) hrev
        simpa [f, pathGraphRevIso_apply] using hi
      let u : Fin n := ⟨n - 2, by omega⟩
      let v : Fin n := ⟨n - 1, by omega⟩
      have huv := h u v
      rw [hrev_apply u, hrev_apply v, cartanMatrix_B] at huv
      have hu_rev : u.rev = ⟨1, by omega⟩ := Fin.ext (by simp [u, Fin.val_rev]; omega)
      have hv_rev : v.rev = ⟨0, by omega⟩ := Fin.ext (by simp [v, Fin.val_rev]; omega)
      rw [hu_rev, hv_rev] at huv
      have hleft : CartanMatrix.B n ⟨1, by omega⟩ ⟨0, by omega⟩ = -1 := by
        simp [CartanMatrix.B, Fin.ext_iff]
      have hright : CartanMatrix.B n u v = -2 := by
        simp only [CartanMatrix.B, Matrix.of_apply, u, v, Fin.ext_iff]
        split_ifs <;> omega
      omega

/-- **The Dynkin diagram of `Bₙ` has no nontrivial symmetry.** -/
@[simp]
theorem diagramSymmetry_B_eq_bot (n : ℕ) : (B n).diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hσ ↦
    eq_one_of_cartanMatrix_B (mem_diagramSymmetry_iff.mp hσ)

/-- **The identity is the only permutation preserving the type-`Cₙ` Cartan matrix**, since
`CartanMatrix.C n` is the transpose of `CartanMatrix.B n`. -/
theorem eq_one_of_cartanMatrix_C {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ∀ i j : Fin n, (C n).cartanMatrix (σ i) (σ j) = (C n).cartanMatrix i j) : σ = 1 := by
  refine eq_one_of_cartanMatrix_B fun i j ↦ ?_
  have hji := h j i
  simp only [cartanMatrix_C, ← CartanMatrix.B_transpose, Matrix.transpose_apply] at hji
  simpa only [cartanMatrix_B] using hji

/-- **The Dynkin diagram of `Cₙ` has no nontrivial symmetry.** -/
@[simp]
theorem diagramSymmetry_C_eq_bot (n : ℕ) : (C n).diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hσ ↦
    eq_one_of_cartanMatrix_C (mem_diagramSymmetry_iff.mp hσ)

/-- **The Dynkin diagram of `F₄` has no nontrivial symmetry.** -/
@[simp]
theorem diagramSymmetry_F4_eq_bot : F4.diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hσ ↦
    eq_one_of_cartanMatrix_F4 (mem_diagramSymmetry_iff.mp hσ)

/-- **The Dynkin diagram of `G₂` has no nontrivial symmetry.** -/
@[simp]
theorem diagramSymmetry_G2_eq_bot : G2.diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hσ ↦
    eq_one_of_cartanMatrix_G2 (mem_diagramSymmetry_iff.mp hσ)

/-- **Every non-simply-laced Dynkin type has trivial diagram symmetry group.** -/
theorem diagramSymmetry_eq_bot_of_not_isSimplyLaced {t : DynkinType} (ht : ¬ t.IsSimplyLaced) :
    t.diagramSymmetry = ⊥ := by
  cases t with
  | B n => exact diagramSymmetry_B_eq_bot n
  | C n => exact diagramSymmetry_C_eq_bot n
  | F4 => exact diagramSymmetry_F4_eq_bot
  | G2 => exact diagramSymmetry_G2_eq_bot
  | A _ | D _ | E6 | E7 | E8 => simp at ht

/-- **Every Dynkin type whose Cartan matrix is not simply laced has trivial diagram symmetry
group.** -/
theorem diagramSymmetry_eq_bot_of_not_isSimplyLaced_cartanMatrix {t : DynkinType}
    (ht : ¬ t.cartanMatrix.IsSimplyLaced) : t.diagramSymmetry = ⊥ :=
  diagramSymmetry_eq_bot_of_not_isSimplyLaced fun hsl ↦
    ht ((isSimplyLaced_cartanMatrix_iff t).mpr (Or.inl hsl))

open _root_.Matrix in
/-- A permutation of the nodes of `E₇` preserving the Cartan matrix is the identity. -/
private theorem eq_one_of_submatrix_cartanMatrix_E7 {σ : Equiv.Perm (Fin 7)}
    (hσ : (CartanMatrix.E 7).submatrix σ σ = CartanMatrix.E 7) : σ = 1 := by
  have hinv (v : Fin 7 → ℤ) (hv : v ∘ σ = v) :
      (CartanMatrix.E 7 *ᵥ v) ∘ σ = CartanMatrix.E 7 *ᵥ v := by
    conv_rhs => rw [← hσ, ← hv]
    rw [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id]
  have hfix := hinv _ (hinv _ (hinv _ (hinv (fun _ ↦ 1) rfl)))
  have hinj : Function.Injective (CartanMatrix.E 7 *ᵥ (CartanMatrix.E 7 *ᵥ
      (CartanMatrix.E 7 *ᵥ (CartanMatrix.E 7 *ᵥ fun _ ↦ (1 : ℤ))))) := by
    decide +kernel
  ext i
  exact congrArg Fin.val (hinj (congrFun hfix i))

/-- **The Dynkin diagram of `E₇` has no nontrivial symmetry.** -/
@[simp]
theorem diagramSymmetry_E7_eq_bot : E7.diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hσ ↦
    eq_one_of_submatrix_cartanMatrix_E7 (cartanMatrix_E7 ▸ mem_diagramSymmetry_iff_submatrix.mp hσ)

/-- **The diagram symmetries of `Aₙ` are the identity and the chain reversal `graphPermA n`.** -/
theorem mem_diagramSymmetry_A_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ (A n).diagramSymmetry ↔ σ = 1 ∨ σ = graphPermA n := by
  refine ⟨fun hσ ↦ ?_, ?_⟩
  · have hmem : σ ∈ matrixSymmetryGroup (CartanMatrix.A n) :=
      mem_matrixSymmetryGroup_iff.mpr (cartanMatrix_A n ▸ mem_diagramSymmetry_iff_submatrix.mp hσ)
    let f : _root_.SimpleGraph.pathGraph n ≃g _root_.SimpleGraph.pathGraph n :=
      { toEquiv := σ
        map_rel_iff' := by
          intro i j
          rw [← diagramGraph_cartanMatrix_A n]
          exact (diagramGraphIsoOfMemMatrixSymmetryGroup hmem).map_rel_iff' }
    rcases _root_.SimpleGraph.pathGraph_iso_eq_refl_or_rev f with hrefl | hrev
    · exact Or.inl <| Equiv.ext fun i ↦
        congrArg (fun φ : _root_.SimpleGraph.pathGraph n ≃g _ ↦ φ i) hrefl
    · refine Or.inr <| Equiv.ext fun i ↦ ?_
      have hi := congrArg (fun φ : _root_.SimpleGraph.pathGraph n ≃g _ ↦ φ i) hrev
      simpa [f, graphPermA_apply] using hi
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact mem_diagramSymmetry_iff.mpr (cartanMatrix_A_graphPermA n)

/-- **In `A₂ₙ` (`1 ≤ n`) under `graphPermA (2 * n)`, the middle pair `{n - 1, n}` is the unique
orbit with a nonzero off-diagonal Cartan entry.** -/
theorem cartanMatrix_A_even_ne_zero_of_sameCycle_graphPermA_iff {n : ℕ} (hn : 1 ≤ n)
    {i j : Fin (2 * n)} (hcyc : (graphPermA (2 * n)).SameCycle i j) (hne : i ≠ j) :
    (A (2 * n)).cartanMatrix i j ≠ 0 ↔
      (i = ⟨n - 1, by omega⟩ ∧ j = ⟨n, by omega⟩) ∨
        (i = ⟨n, by omega⟩ ∧ j = ⟨n - 1, by omega⟩) := by
  have hperm : graphPermA (2 * n) = Fin.revPerm := Equiv.ext (graphPermA_apply (2 * n))
  rw [hperm] at hcyc
  have hadj_iff : (A (2 * n)).cartanMatrix i j ≠ 0 ↔
      (_root_.SimpleGraph.pathGraph (2 * n)).Adj i j := by
    rw [← diagramGraph_cartanMatrix_A (2 * n), diagramGraph_adj, cartanMatrix_A]
    have hsymm := (CartanMatrix.A_isSymm (2 * n)).apply i j
    exact ⟨fun h ↦ ⟨hne, h, fun hji ↦ h (hsymm.symm.trans hji)⟩, fun h ↦ h.2.1⟩
  rw [hadj_iff, ← _root_.SimpleGraph.pathGraph_even_adj_of_sameCycle_revPerm_iff hn]
  exact (and_iff_right hcyc).symm

end DynkinType

/-! ## Connected finite-type Cartan matrices -/

namespace IsFiniteType

variable {B : Type*} {A : Matrix B B ℤ}

/-- **A connected non-simply-laced finite-type Cartan matrix has trivial symmetry group.** -/
theorem matrixSymmetryGroup_eq_bot_of_not_isSimplyLaced (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) (hnsl : ¬ A.IsSimplyLaced) :
    matrixSymmetryGroup A = ⊥ := by
  obtain ⟨t, ⟨-, e, he⟩, -⟩ := h.existsUnique_dynkinType hconn
  have ht_nsl : ¬ t.cartanMatrix.IsSimplyLaced := fun hsl ↦
    hnsl fun i j hij ↦ by
      dsimp only
      rw [he i j]
      exact hsl (e.injective.ne hij)
  have hbot : t.diagramSymmetry = ⊥ :=
    DynkinType.diagramSymmetry_eq_bot_of_not_isSimplyLaced_cartanMatrix ht_nsl
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
  have hmem : e.symm.trans (σ.trans e) ∈ t.diagramSymmetry :=
    DynkinType.mem_diagramSymmetry_iff_submatrix.mpr
      (mem_matrixSymmetryGroup_iff.mp (conj_mem_matrixSymmetryGroup e he hσ))
  have hτ : e.symm.trans (σ.trans e) = 1 := Subgroup.mem_bot.mp (hbot.le hmem)
  ext i
  have hi := Equiv.ext_iff.mp hτ (e i)
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at hi
  exact e.injective hi

/-- **Simply-laced orbit dichotomy for connected finite-type Cartan matrices.** Let `A` be a
connected simply-laced finite-type Cartan matrix and `σ ∈ matrixSymmetryGroup A`. Either every
`σ`-orbit is pairwise orthogonal (`A i j = 0` whenever `i ≠ j` lie on the same cycle of `σ`), or
`A` reindexes to `A₂ₙ` (`1 ≤ n`) with `σ` acting on the node labels by `Fin.rev`. -/
theorem orbit_apply_eq_zero_or_typeA_even (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) (hsl : A.IsSimplyLaced)
    {σ : Equiv.Perm B} (hσ : σ ∈ matrixSymmetryGroup A) :
    (∀ i j : B, σ.SameCycle i j → i ≠ j → A i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∃ e : B ≃ Fin (2 * n),
        (∀ i j : B, A i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        ∀ i : B, e (σ i) = (e i).rev := by
  classical
  have := h.finite
  have : Fintype B := Fintype.ofFinite B
  have htree : (diagramGraph A).IsTree := h.isTree_diagramGraph hconn
  let f : diagramGraph A ≃g diagramGraph A := diagramGraphIsoOfMemMatrixSymmetryGroup hσ
  by_cases hc : ∃ c : B, (diagramGraph A).degree c = 3
  · -- Branching diagram (`Dₙ`, `E₆`, `E₇`, `E₈`): the unique branch vertex is fixed by `f`.
    left
    obtain ⟨c, hc3⟩ := hc
    intro i j hcyc hne
    have hnot_adj : ¬ (diagramGraph A).Adj i j :=
      htree.not_adj_of_sameCycle_of_degree_unique (f := f) (c := c)
        (fun w hw ↦ h.eq_of_degree_eq_three hsl hconn (hw.trans hc3) hc3) hcyc
    by_contra hnz
    exact hnot_adj (h.diagramGraph_adj_iff.mpr ⟨hne, hnz⟩)
  · -- Unbranched diagram (`Aₘ`): reindex onto `(DynkinType.A m).cartanMatrix`.
    have hdeg : ∀ v : B, (diagramGraph A).degree v ≤ 2 := fun v ↦ by
      have h3le := h.degree_le_three v
      have hne3 : (diagramGraph A).degree v ≠ 3 := fun hv3 ↦ hc ⟨v, hv3⟩
      omega
    obtain ⟨e₀, he₀⟩ := h.exists_equiv_forall_eq_cartanMatrix_A hconn hsl hdeg
    let m := Fintype.card B
    have hm_pos : 1 ≤ m := Fintype.card_pos_iff.mpr hconn.nonempty
    let τ : Equiv.Perm (Fin m) := e₀.symm.trans (σ.trans e₀)
    have hτ : τ ∈ (DynkinType.A m).diagramSymmetry :=
      DynkinType.mem_diagramSymmetry_iff_submatrix.mpr
        (mem_matrixSymmetryGroup_iff.mp (conj_mem_matrixSymmetryGroup e₀ he₀ hσ))
    rcases DynkinType.mem_diagramSymmetry_A_iff.mp hτ with hτ1 | hτrev
    · -- Identity symmetry: every cycle is a singleton.
      left
      have hσ1 : σ = 1 := by
        ext i
        have hi := Equiv.ext_iff.mp hτ1 (e₀ i)
        simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at hi
        exact e₀.injective hi
      intro i j hcyc hne
      rw [hσ1] at hcyc
      exact absurd (Equiv.Perm.SameCycle.eq_of_left hcyc rfl) hne
    · -- Reversal symmetry on `Aₘ`: odd `m` gives orthogonal orbits, even `m` gives `A₂ₙ`.
      have hrev : ∀ z : B, e₀ (σ z) = (e₀ z).rev := fun z ↦ by
        have hz := Equiv.ext_iff.mp hτrev (e₀ z)
        simpa only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, graphPermA_apply] using hz
      rcases Nat.even_or_odd m with ⟨n, hm_even⟩ | hm_odd
      · right
        have hm2 : m = 2 * n := by omega
        have hn1 : 1 ≤ n := by omega
        let e : B ≃ Fin (2 * n) := e₀.trans (finCongr hm2)
        refine ⟨n, hn1, e, fun i j ↦ ?_, fun i ↦ ?_⟩
        · rw [he₀ i j]
          simp only [DynkinType.cartanMatrix_A, CartanMatrix.A, Matrix.of_apply, e,
            Equiv.trans_apply, Fin.ext_iff, finCongr_apply, Fin.val_cast]
        · apply Fin.ext
          simp only [e, Equiv.trans_apply, finCongr_apply, Fin.val_cast, hrev i, Fin.val_rev]
          change m - ((e₀ i : ℕ) + 1) = 2 * n - ((e₀ i : ℕ) + 1)
          omega
      · left
        intro i j hcyc hne
        have hcyc_rev : Fin.revPerm.SameCycle (e₀ i) (e₀ j) :=
          hcyc.map fun z ↦ by simpa only [Fin.revPerm_apply] using hrev z
        have hnot_adj := _root_.SimpleGraph.not_pathGraph_adj_of_sameCycle_revPerm_of_odd hm_odd
          hcyc_rev
        rw [← DynkinType.diagramGraph_cartanMatrix_A m, diagramGraph_adj] at hnot_adj
        rw [he₀ i j, DynkinType.cartanMatrix_A]
        by_contra hnz
        have hsymm := (CartanMatrix.A_isSymm m).apply (e₀ i) (e₀ j)
        exact hnot_adj ⟨e₀.injective.ne hne, hnz, fun hji ↦ hnz (hsymm.symm.trans hji)⟩

end IsFiniteType

end TauCeti
