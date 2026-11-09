/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Vertices of faces and degeneracies of simplices of `Δ[p] ⊗ Δ[q]`

Mathlib's `SSet.prodStdSimplex.objEquiv` identifies the `n`-simplices of `Δ[p] ⊗ Δ[q]` with the
monotone chains of `n + 1` vertices in `Fin (p + 1) × Fin (q + 1)`. In these terms, faces and
degeneracies reindex the chain by `Fin.succAbove` and `Fin.predAbove`
(`SSet.prodStdSimplex.objEquiv_δ`, `SSet.prodStdSimplex.objEquiv_σ`), a simplex repeating the
vertex at `j` and `j + 1` is a degeneracy of its face (`SSet.prodStdSimplex.σ_δ_succ_of_eq`),
and `f ▷ Δ[q]` applies `f` to the first coordinates of the vertices
(`SSet.prodStdSimplex.objEquiv_whiskerRight_app`).
-/

public section

universe u

open CategoryTheory Simplicial MonoidalCategory

namespace SSet

namespace prodStdSimplex

variable {p q : ℕ}

/-- The vertices of a face of a simplex of `Δ[p] ⊗ Δ[q]` are those of the simplex, reindexed by
`Fin.succAbove`. -/
lemma objEquiv_δ {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n + 1⦌) (j : Fin (n + 2)) :
    ⇑(objEquiv ((Δ[p] ⊗ Δ[q]).δ j x)) = objEquiv x ∘ j.succAbove :=
  funext (objEquiv_δ_apply x j)

/-- The vertices of a degeneracy of a simplex of `Δ[p] ⊗ Δ[q]` are those of the simplex,
reindexed by `Fin.predAbove`. -/
lemma objEquiv_σ {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (j : Fin (n + 1)) :
    ⇑(objEquiv ((Δ[p] ⊗ Δ[q]).σ j x)) = objEquiv x ∘ j.predAbove :=
  funext (objEquiv_map_apply x (SimplexCategory.σ j))

/-- A simplex of `Δ[p] ⊗ Δ[q]` with the same vertex at `j` and `j + 1` is the degeneracy `σ j` of
its face opposite `j + 1`. -/
lemma σ_δ_succ_of_eq {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n + 1⦌) (j : Fin (n + 1))
    (hj : objEquiv x j.castSucc = objEquiv x j.succ) :
    (Δ[p] ⊗ Δ[q]).σ j ((Δ[p] ⊗ Δ[q]).δ j.succ x) = x := by
  apply objEquiv.injective
  refine OrderHom.ext _ _ (funext fun k ↦ ?_)
  rw [objEquiv_σ, Function.comp_apply, objEquiv_δ, Function.comp_apply]
  rcases lt_trichotomy k j.succ with hk | hk | hk
  · rw [Fin.predAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 hk),
      Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hk), Fin.castSucc_castPred]
  · subst hk
    rw [Fin.predAbove_succ_self, Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ, hj]
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] at hk ⊢; lia),
      Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, Fin.lt_def] at hk ⊢; lia),
      Fin.succ_pred]

/-- The vertices of the image of a simplex of `Δ[m] ⊗ Δ[q]` under `f ▷ Δ[q]` are those of the
simplex, with `f` applied to the first coordinates. -/
lemma objEquiv_whiskerRight_app {m n r : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (Δ[m] ⊗ Δ[q] : SSet.{u}) _⦋r⦌) :
    ⇑(objEquiv ((SSet.stdSimplex.map f ▷ Δ[q]).app _ y)) = Prod.map f id ∘ objEquiv y :=
  funext fun i ↦ Prod.ext (objEquiv_apply_fst _ i) (objEquiv_apply_snd _ i)

end prodStdSimplex

end SSet
