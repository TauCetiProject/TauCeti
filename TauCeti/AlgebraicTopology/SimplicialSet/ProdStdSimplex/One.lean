/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
# The nondegenerate simplices of the prism `Δ[p] ⊗ Δ[1]` as morphisms

Mathlib's `SSet.prodStdSimplex₁.nonDegenerateEquiv` enumerates the nondegenerate
`(p + 1)`-simplices of the prism `Δ[p] ⊗ Δ[1]`, and `SSet.prodStdSimplex₁.codimOneSimplex` its
`p`-simplices which are faces of them. This file repackages them as morphisms out of standard
simplices: `SSet.prodStdSimplex₁.ι i : Δ[p + 1] ⟶ Δ[p] ⊗ Δ[1]` is the `i`th nondegenerate
`(p + 1)`-simplex. We compute its first projection (`SSet.prodStdSimplex₁.ι_fst`) and its faces
opposite to the vertices `(i, 0)` and `(i, 1)` (`SSet.prodStdSimplex₁.δ_castSucc_ι`,
`SSet.prodStdSimplex₁.δ_succ_ι`), and identify the extreme faces `codimOneSimplex 0` and
`codimOneSimplex (Fin.last (p + 1))` with the top and bottom inclusions `ι₁` and `ι₀` of `Δ[p]`.
The vertices of the `k`th nondegenerate `(p + 1)`-simplex are `(i, 0)` at `i.castSucc` for `i ≤ k`
and `(i, 1)` at `i.succ` for `k ≤ i`, all distinct.

For `p = 1`, the square `Δ[1] ⊗ Δ[1]` is the union of the `2`-simplices `ι 0`, with vertices
`(0, 0), (0, 1), (1, 1)`, and `ι 1`, with vertices `(0, 0), (1, 0), (1, 1)`, glued along the
diagonal (`SSet.prodStdSimplex₁.δ_one_ι_zero`). We describe their sides as whiskered inclusions
of `Δ[0] ⊗ Δ[1]` and `Δ[1] ⊗ Δ[0]`, the form in which maps out of `Δ[1] ⊗ Z` are constrained on
`{i} × Z` and `Z × {i}`.
-/

public section

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace SSet

namespace prodStdSimplex₁

variable {p : ℕ}

/-- The `i`th nondegenerate `(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]`, with vertices
`(0, 0), …, (i, 0), (i, 1), …, (p, 1)`, as a morphism `Δ[p + 1] ⟶ Δ[p] ⊗ Δ[1]`. -/
noncomputable def ι (i : Fin (p + 1)) : Δ[p + 1] ⟶ (Δ[p] ⊗ Δ[1] : SSet.{u}) :=
  yonedaEquiv.symm (nonDegenerateEquiv i).val

/-- The first projection of `ι i` is the degeneracy `σ i : Δ[p + 1] ⟶ Δ[p]`. -/
@[reassoc (attr := simp)]
lemma ι_fst (i : Fin (p + 1)) :
    ι.{u} i ≫ fst _ _ = stdSimplex.σ i :=
  yonedaEquiv.injective (yonedaEquiv_map _).symm

/-- The face of `ι i` opposite to its vertex `(i, 0)`. -/
@[reassoc]
lemma δ_castSucc_ι (i : Fin (p + 1)) :
    stdSimplex.δ i.castSucc ≫ ι.{u} i =
      yonedaEquiv.symm (codimOneSimplex i.castSucc).val := by
  rw [ι, stdSimplex.δ_comp_yonedaEquiv_symm, δ_castSucc_nonDegenerateEquiv]

/-- The face of `ι i` opposite to its vertex `(i, 1)`. -/
@[reassoc]
lemma δ_succ_ι (i : Fin (p + 1)) :
    stdSimplex.δ i.succ ≫ ι.{u} i =
      yonedaEquiv.symm (codimOneSimplex i.succ).val := by
  rw [ι, stdSimplex.δ_comp_yonedaEquiv_symm, δ_succ_nonDegenerateEquiv]

/-- The `p`-simplex `codimOneSimplex j` of `Δ[p] ⊗ Δ[1]` is a section of the first projection. -/
@[reassoc]
lemma yonedaEquiv_symm_codimOneSimplex_fst (j : Fin (p + 2)) :
    yonedaEquiv.symm (codimOneSimplex.{u} j).val ≫ fst _ _ = 𝟙 _ :=
  yonedaEquiv.injective rfl

/-- The `p`-simplex of `Δ[p] ⊗ Δ[1]` whose second projection never takes the value `0` is the top
inclusion `ι₁`. -/
lemma yonedaEquiv_symm_codimOneSimplex_zero :
    yonedaEquiv.symm (codimOneSimplex.{u} (p := p) 0).val = ι₁ := by
  rw [Equiv.symm_apply_eq, ← Category.id_comp ι₁, yonedaEquiv_comp]
  refine Prod.ext rfl (stdSimplex.ext _ _ fun k ↦ ?_)
  simp [stdSimplex.objMk₁_apply]

/-- The `p`-simplex of `Δ[p] ⊗ Δ[1]` whose second projection is constant with value `0` is the
bottom inclusion `ι₀`. -/
lemma yonedaEquiv_symm_codimOneSimplex_last :
    yonedaEquiv.symm (codimOneSimplex.{u} (Fin.last (p + 1))).val = ι₀ := by
  rw [Equiv.symm_apply_eq, ← Category.id_comp ι₀, yonedaEquiv_comp]
  refine Prod.ext rfl (stdSimplex.ext _ _ fun k ↦ ?_)
  simp [stdSimplex.objMk₁_apply]

/-- The vertex at `i.castSucc` of the `k`th nondegenerate `(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]` is
`(i, 0)` when `i ≤ k`. -/
lemma objEquiv_nonDegenerateEquiv_castSucc (k i : Fin (p + 1)) (hi : i ≤ k) :
    prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val i.castSucc = (i, 0) := by
  refine Prod.ext ?_ ?_
  · exact Fin.predAbove_castSucc_of_le _ _ hi
  · refine stdSimplex.objMk₁_of_castSucc_lt _ _ ?_
    rw [Fin.lt_def]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have := Fin.le_def.1 hi
    lia

/-- The vertex at `i.succ` of the `k`th nondegenerate `(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]` is
`(i, 1)` when `k ≤ i`. -/
lemma objEquiv_nonDegenerateEquiv_succ (k i : Fin (p + 1)) (hi : k ≤ i) :
    prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val i.succ = (i, 1) := by
  refine Prod.ext ?_ ?_
  · exact Fin.predAbove_succ_of_le _ _ hi
  · refine stdSimplex.objMk₁_of_le_castSucc _ _ ?_
    rw [Fin.le_def]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have := Fin.le_def.1 hi
    lia

/-- The vertices of a nondegenerate `(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]` are distinct. -/
lemma injective_objEquiv_nonDegenerateEquiv (k : Fin (p + 1)) :
    Function.Injective (prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val) :=
  (prodStdSimplex.nonDegenerate_iff_injective_objEquiv _).1 (nonDegenerateEquiv k).property

/-! ### The square `Δ[1] ⊗ Δ[1]` -/

/-- The side of `ι 0 : Δ[2] ⟶ Δ[1] ⊗ Δ[1]` opposite to its vertex `(1, 1)` is the edge
`{0} × Δ[1]`. -/
@[reassoc]
lemma δ_two_ι_zero :
    stdSimplex.δ 2 ≫ ι.{u} (p := 1) 0 =
      lift (stdSimplex.σ 0) (𝟙 _) ≫ stdSimplex.δ 1 ▷ Δ[1] := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext i : 2
  fin_cases i <;> rfl

/-- The side of `ι 1 : Δ[2] ⟶ Δ[1] ⊗ Δ[1]` opposite to its vertex `(0, 0)` is the edge
`{1} × Δ[1]`. -/
@[reassoc]
lemma δ_zero_ι_one :
    stdSimplex.δ 0 ≫ ι.{u} (p := 1) 1 =
      lift (stdSimplex.σ 0) (𝟙 _) ≫ stdSimplex.δ 0 ▷ Δ[1] := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext i : 2
  fin_cases i <;> rfl

/-- The side of `ι 0 : Δ[2] ⟶ Δ[1] ⊗ Δ[1]` opposite to its vertex `(0, 0)` is the edge
`Δ[1] × {1}`. -/
@[reassoc]
lemma δ_zero_ι_zero :
    stdSimplex.δ 0 ≫ ι.{u} (p := 1) 0 =
      lift (𝟙 _) (stdSimplex.σ 0) ≫ Δ[1] ◁ stdSimplex.δ 0 := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext i : 2
  fin_cases i <;> rfl

/-- The side of `ι 1 : Δ[2] ⟶ Δ[1] ⊗ Δ[1]` opposite to its vertex `(1, 1)` is the edge
`Δ[1] × {0}`. -/
@[reassoc]
lemma δ_two_ι_one :
    stdSimplex.δ 2 ≫ ι.{u} (p := 1) 1 =
      lift (𝟙 _) (stdSimplex.σ 0) ≫ Δ[1] ◁ stdSimplex.δ 1 := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext i : 2
  fin_cases i <;> rfl

/-- The two `2`-simplices `ι 0` and `ι 1` of `Δ[1] ⊗ Δ[1]` share their diagonal, the edge from
`(0, 0)` to `(1, 1)`. -/
@[reassoc]
lemma δ_one_ι_zero : stdSimplex.δ 1 ≫ ι.{u} (p := 1) 0 = stdSimplex.δ 1 ≫ ι 1 :=
  (δ_succ_ι 0).trans (δ_castSucc_ι 1).symm

end prodStdSimplex₁

end SSet
