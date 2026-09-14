/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic

/-!
# The exceptional affine Dynkin diagrams as stars

The exceptional simply-laced affine Dynkin diagrams are three-armed stars. This file identifies
the arm-coordinate numbering of `TauCeti.AffineDynkinType.graph` with the canonical star indices
used by `TauCeti.starCartanMatrix`:

```text
  Ẽ₆ = T₃,₃,₃,    Ẽ₇ = T₂,₄,₄,    Ẽ₈ = T₂,₃,₆.
```

The parameters in `TauCeti.StarIndex` count vertices beyond the centre, so the corresponding arm
vectors are `![2, 2, 2]`, `![1, 3, 3]`, and `![1, 2, 5]`. The explicit equivalences below send the
star centre to affine node `0` and number every arm outwards. They identify both the generalized
Cartan matrices and their diagram graphs, allowing results about stars to be applied directly to
the affine exceptional types.

## Main definitions

* `TauCeti.AffineDynkinType.starIndexEquivE6`, `starIndexEquivE7`, and `starIndexEquivE8` are the
  explicit relabellings from the three canonical star index types to the affine node types.
* `TauCeti.AffineDynkinType.starGraphIsoE6`, `starGraphIsoE7`, and `starGraphIsoE8` identify the
  corresponding star diagrams with the affine exceptional diagrams.

## References

The star descriptions follow V. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4 and
Table Aff 1.
-/

public section

open scoped Matrix

namespace TauCeti

namespace AffineDynkinType

private def e6StarEmbedding : StarIndex ![2, 2, 2] → Fin E6.nodes
  | none => 0
  | some ⟨i, s⟩ => ⟨2 * i + s + 1, by
      fin_cases i <;> simp at s ⊢
      all_goals omega⟩

private theorem e6StarEmbedding_injective : Function.Injective e6StarEmbedding := by
  intro v w h
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · rfl
  · exfalso
    have := congrArg Fin.val h
    fin_cases j <;> simp [e6StarEmbedding] at this t
  · exfalso
    have := congrArg Fin.val h
    fin_cases i <;> simp [e6StarEmbedding] at this s
  · fin_cases i <;> fin_cases j <;>
      simp [e6StarEmbedding] at h s t ⊢ <;> try omega
    all_goals congr 1
    all_goals exact Fin.ext (by omega)

/-- The arm-coordinate relabelling from the star `T₃,₃,₃` to affine `E₆`. It sends the
centre to node `0` and sends the vertices on arms `i = 0, 1, 2`, in order away from the centre, to
`1, 2`, to `3, 4`, and to `5, 6`, respectively. -/
noncomputable def starIndexEquivE6 : StarIndex ![2, 2, 2] ≃ Fin E6.nodes :=
  Equiv.ofBijective e6StarEmbedding <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨e6StarEmbedding_injective, by
      simp only [StarIndex, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
        Fin.sum_univ_three]
      norm_num [Matrix.cons_val_two]⟩

/-- The affine `E₆` star relabelling sends the centre to node `0`. -/
@[simp] theorem starIndexEquivE6_none : starIndexEquivE6 none = 0 := (rfl)

/-- The value of the affine `E₆` star relabelling on an arm vertex. -/
@[simp] theorem starIndexEquivE6_some_val (i : Fin 3) (s : Fin (![2, 2, 2] i)) :
    ((starIndexEquivE6 (some ⟨i, s⟩) : Fin E6.nodes) : ℕ) =
      2 * (i : ℕ) + (s : ℕ) + 1 := (rfl)

private def e7StarEmbedding : StarIndex ![1, 3, 3] → Fin E7.nodes
  | none => 0
  | some ⟨i, s⟩ =>
      ⟨if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then 2 + s else 5 + s, by
        fin_cases i <;> simp at s ⊢
        all_goals omega⟩

private theorem e7StarEmbedding_injective : Function.Injective e7StarEmbedding := by
  intro v w h
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · rfl
  · exfalso
    have := congrArg Fin.val h
    fin_cases j <;> simp [e7StarEmbedding] at this t
    all_goals omega
  · exfalso
    have := congrArg Fin.val h
    fin_cases i <;> simp [e7StarEmbedding] at this s
  · fin_cases i <;> fin_cases j <;>
      simp [e7StarEmbedding] at h s t ⊢ <;> try omega
    all_goals congr 1
    all_goals exact Fin.ext (by omega)

/-- The arm-coordinate relabelling from the star `T₂,₄,₄` to affine `E₇`. It sends the
centre to node `0` and sends the vertices on arms `i = 0, 1, 2`, in order away from the centre, to
`1`, to `2, 3, 4`, and to `5, 6, 7`, respectively. -/
noncomputable def starIndexEquivE7 : StarIndex ![1, 3, 3] ≃ Fin E7.nodes :=
  Equiv.ofBijective e7StarEmbedding <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨e7StarEmbedding_injective, by
      simp only [StarIndex, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
        Fin.sum_univ_three]
      norm_num [Matrix.cons_val_two]⟩

/-- The affine `E₇` star relabelling sends the centre to node `0`. -/
@[simp] theorem starIndexEquivE7_none : starIndexEquivE7 none = 0 := (rfl)

/-- The value of the affine `E₇` star relabelling on an arm vertex. -/
@[simp] theorem starIndexEquivE7_some_val (i : Fin 3) (s : Fin (![1, 3, 3] i)) :
    ((starIndexEquivE7 (some ⟨i, s⟩) : Fin E7.nodes) : ℕ) =
      if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then 2 + (s : ℕ) else 5 + (s : ℕ) :=
  (rfl)

private def e8StarEmbedding : StarIndex ![1, 2, 5] → Fin E8.nodes
  | none => 0
  | some ⟨i, s⟩ =>
      ⟨if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then 2 + s else 4 + s, by
        fin_cases i <;> simp at s ⊢
        all_goals omega⟩

private theorem e8StarEmbedding_injective : Function.Injective e8StarEmbedding := by
  intro v w h
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · rfl
  · exfalso
    have := congrArg Fin.val h
    fin_cases j <;> simp [e8StarEmbedding] at this t
    all_goals omega
  · exfalso
    have := congrArg Fin.val h
    fin_cases i <;> simp [e8StarEmbedding] at this s
  · fin_cases i <;> fin_cases j <;>
      simp [e8StarEmbedding] at h s t ⊢ <;> try omega
    all_goals congr 1
    all_goals exact Fin.ext (by omega)

/-- The arm-coordinate relabelling from the star `T₂,₃,₆` to affine `E₈`. It sends the
centre to node `0` and sends the vertices on arms `i = 0, 1, 2`, in order away from the centre, to
`1`, to `2, 3`, and to `4, 5, 6, 7, 8`, respectively. -/
noncomputable def starIndexEquivE8 : StarIndex ![1, 2, 5] ≃ Fin E8.nodes :=
  Equiv.ofBijective e8StarEmbedding <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨e8StarEmbedding_injective, by
      simp only [StarIndex, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
        Fin.sum_univ_three]
      norm_num [Matrix.cons_val_two]⟩

/-- The affine `E₈` star relabelling sends the centre to node `0`. -/
@[simp] theorem starIndexEquivE8_none : starIndexEquivE8 none = 0 := (rfl)

/-- The value of the affine `E₈` star relabelling on an arm vertex. -/
@[simp] theorem starIndexEquivE8_some_val (i : Fin 3) (s : Fin (![1, 2, 5] i)) :
    ((starIndexEquivE8 (some ⟨i, s⟩) : Fin E8.nodes) : ℕ) =
      if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then 2 + (s : ℕ) else 4 + (s : ℕ) :=
  (rfl)

/-! ## Cartan matrix descriptions -/

/-- **Affine `E₆` is the star `T₃,₃,₃`**: after the explicit arm-coordinate relabelling,
its generalized Cartan matrix is the canonical star matrix with three arms of length two beyond
the centre. -/
theorem starCartanMatrix_two_two_two_eq_submatrix_E6 :
    starCartanMatrix ![2, 2, 2] =
      E6.cartanMatrix.submatrix starIndexEquivE6 starIndexEquivE6 := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starIndexEquivE6, e6StarEmbedding,
      cartanMatrix_apply, graph_E6_adj]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE6, e6StarEmbedding,
        cartanMatrix_apply, graph_E6_adj]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE6, e6StarEmbedding,
        cartanMatrix_apply, graph_E6_adj]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE6, e6StarEmbedding,
        cartanMatrix_apply, graph_E6_adj]

/-- **Affine `E₇` is the star `T₂,₄,₄`**: after the explicit arm-coordinate relabelling,
its generalized Cartan matrix is the canonical star matrix with arms of lengths one, three and
three beyond the centre. -/
theorem starCartanMatrix_one_three_three_eq_submatrix_E7 :
    starCartanMatrix ![1, 3, 3] =
      E7.cartanMatrix.submatrix starIndexEquivE7 starIndexEquivE7 := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starIndexEquivE7, e7StarEmbedding,
      cartanMatrix_apply, graph_E7_adj]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE7, e7StarEmbedding,
        cartanMatrix_apply, graph_E7_adj]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE7, e7StarEmbedding,
        cartanMatrix_apply, graph_E7_adj]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE7, e7StarEmbedding,
        cartanMatrix_apply, graph_E7_adj]

/-- **Affine `E₈` is the star `T₂,₃,₆`**: after the explicit arm-coordinate relabelling,
its generalized Cartan matrix is the canonical star matrix with arms of lengths one, two and five
beyond the centre. -/
theorem starCartanMatrix_one_two_five_eq_submatrix_E8 :
    starCartanMatrix ![1, 2, 5] =
      E8.cartanMatrix.submatrix starIndexEquivE8 starIndexEquivE8 := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starIndexEquivE8, e8StarEmbedding,
      cartanMatrix_apply, graph_E8_adj]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE8, e8StarEmbedding,
        cartanMatrix_apply, graph_E8_adj]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE8, e8StarEmbedding,
        cartanMatrix_apply, graph_E8_adj]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE8, e8StarEmbedding,
        cartanMatrix_apply, graph_E8_adj]

private def starGraphIso (t : AffineDynkinType) {l : Fin 3 → ℕ}
    (e : StarIndex l ≃ Fin t.nodes)
    (h : starCartanMatrix l = t.cartanMatrix.submatrix e e) :
    diagramGraph (starCartanMatrix l) ≃g t.graph where
  toEquiv := e
  map_rel_iff' := by
    intro v w
    rw [h, diagramGraph_submatrix e.injective, SimpleGraph.comap_adj,
      t.graph_eq_diagramGraph_cartanMatrix]

/-! ## Graph descriptions -/

/-- The graph isomorphism `T₃,₃,₃ ≅ Ẽ₆` induced by the explicit arm-coordinate
relabelling. -/
noncomputable def starGraphIsoE6 :
    diagramGraph (starCartanMatrix ![2, 2, 2]) ≃g E6.graph :=
  starGraphIso E6 starIndexEquivE6 starCartanMatrix_two_two_two_eq_submatrix_E6

/-- The star graph isomorphism for affine `E₆` has the prescribed arm-coordinate map. -/
@[simp] theorem starGraphIsoE6_apply (v : StarIndex ![2, 2, 2]) :
    starGraphIsoE6 v = starIndexEquivE6 v := (rfl)

/-- The graph isomorphism `T₂,₄,₄ ≅ Ẽ₇` induced by the explicit arm-coordinate
relabelling. -/
noncomputable def starGraphIsoE7 :
    diagramGraph (starCartanMatrix ![1, 3, 3]) ≃g E7.graph :=
  starGraphIso E7 starIndexEquivE7 starCartanMatrix_one_three_three_eq_submatrix_E7

/-- The star graph isomorphism for affine `E₇` has the prescribed arm-coordinate map. -/
@[simp] theorem starGraphIsoE7_apply (v : StarIndex ![1, 3, 3]) :
    starGraphIsoE7 v = starIndexEquivE7 v := (rfl)

/-- The graph isomorphism `T₂,₃,₆ ≅ Ẽ₈` induced by the explicit arm-coordinate
relabelling. -/
noncomputable def starGraphIsoE8 :
    diagramGraph (starCartanMatrix ![1, 2, 5]) ≃g E8.graph :=
  starGraphIso E8 starIndexEquivE8 starCartanMatrix_one_two_five_eq_submatrix_E8

/-- The star graph isomorphism for affine `E₈` has the prescribed arm-coordinate map. -/
@[simp] theorem starGraphIsoE8_apply (v : StarIndex ![1, 2, 5]) :
    starGraphIsoE8 v = starIndexEquivE8 v := (rfl)

end AffineDynkinType

end TauCeti
