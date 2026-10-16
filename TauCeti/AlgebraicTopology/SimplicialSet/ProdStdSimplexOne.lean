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
    ι.{u} i ≫ fst _ _ = stdSimplex.σ i := by
  apply yonedaEquiv.injective
  exact (yonedaEquiv_map _).symm

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
    yonedaEquiv.symm (codimOneSimplex.{u} j).val ≫ fst _ _ = 𝟙 _ := by
  apply yonedaEquiv.injective
  rfl

/-- The `p`-simplex of `Δ[p] ⊗ Δ[1]` whose second projection never takes the value `0` is the top
inclusion `ι₁`. -/
lemma yonedaEquiv_symm_codimOneSimplex_zero :
    yonedaEquiv.symm (codimOneSimplex.{u} (p := p) 0).val = ι₁ := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← Category.id_comp ι₁, yonedaEquiv_comp]
  refine Prod.ext rfl (stdSimplex.ext _ _ fun k ↦ ?_)
  simp [stdSimplex.objMk₁_apply]

/-- The `p`-simplex of `Δ[p] ⊗ Δ[1]` whose second projection is constant with value `0` is the
bottom inclusion `ι₀`. -/
lemma yonedaEquiv_symm_codimOneSimplex_last :
    yonedaEquiv.symm (codimOneSimplex.{u} (Fin.last (p + 1))).val = ι₀ := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← Category.id_comp ι₀, yonedaEquiv_comp]
  refine Prod.ext rfl (stdSimplex.ext _ _ fun k ↦ ?_)
  simp [stdSimplex.objMk₁_apply]

end prodStdSimplex₁

end SSet
