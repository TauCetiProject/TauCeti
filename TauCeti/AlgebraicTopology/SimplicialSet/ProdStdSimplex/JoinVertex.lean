/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import TauCeti.AlgebraicTopology.SimplexCategory.JoinVertex

/-!
# The collapse `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]`

The map `SSet.prodStdSimplex.toJoinVertex n : Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` sends the vertex `(0, k)`
to `k` and every vertex `(1, k)` to the last vertex `n + 1`. Viewing `Δ[n + 1]` as the join
`Δ[n] ⋆ Δ[0]`, it is the identity of `Δ[n]` on `{0} × Δ[n]` and collapses `{1} × Δ[n]` to the
cone point. Precomposition with it sends an `(n + 1)`-simplex of a simplicial set whose last vertex
is `y` and whose face opposite to `y` is constant at `x` to a map `Δ[1] ⊗ Δ[n] ⟶ X` which is
constant at `x` on `{0} × Δ[n]` and at `y` on `{1} × Δ[n]`. This compares the right mapping
spaces `Hom^R_X(x, y)` with the mapping spaces `Hom_X(x, y)`, which are fibres of `Fun(Δ[1], X)`.

## Main definitions and results

* `SSet.prodStdSimplex.toJoinVertex n`: the collapse `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]`.
* `SSet.prodStdSimplex.whiskerLeft_map_toJoinVertex`: it is natural in `n`, a simplicial operator
  `f` acting on `Δ[n + 1]` through `SimplexCategory.joinVertex.map f`.
* `SSet.prodStdSimplex.whiskerRight_δ_one_toJoinVertex`,
  `SSet.prodStdSimplex.whiskerRight_δ_zero_toJoinVertex`: its restrictions to `{0} × Δ[n]` and
  `{1} × Δ[n]`.
* `SSet.prodStdSimplex.toJoinVertex_zero`: for `n = 0` it is the first projection.
* `SSet.prodStdSimplex.toJoinVertexSection_toJoinVertex`: it has a section, so it is an
  epimorphism.

## References

* J. Lurie, *Higher Topos Theory*, §4.2.1, where this map `Δ^n × Δ^1 ⟶ Δ^n ⋆ Δ^0` compares the
  two slice constructions.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial

universe u

namespace SSet

namespace prodStdSimplex

variable (n : ℕ)

/-- The monotone map `Fin 2 × Fin (n + 1) → Fin (n + 2)` which sends `(0, k)` to `k` and `(1, k)`
to the last element. -/
def toJoinVertexOrderHom : Fin 2 × Fin (n + 1) →o Fin (n + 2) where
  toFun z := if z.1 = 0 then z.2.castSucc else Fin.last _
  monotone' := by
    rintro ⟨a, k⟩ ⟨a', k'⟩ ⟨ha, hk⟩
    dsimp only
    split_ifs <;>
      simp only [Fin.le_def, Fin.ext_iff, Fin.val_zero, Fin.val_castSucc, Fin.val_last] at * <;>
      lia

/-- The map `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` which collapses `{1} × Δ[n]` to the last vertex and is the
inclusion of the face opposite to the last vertex on `{0} × Δ[n]`. -/
noncomputable def toJoinVertex : (Δ[1] ⊗ Δ[n] : SSet.{u}) ⟶ Δ[n + 1] where
  app _ := TypeCat.ofHom fun z ↦ stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
    ((toJoinVertexOrderHom n).comp
      ((stdSimplex.objEquiv z.1).toOrderHom.prod (stdSimplex.objEquiv z.2).toOrderHom)))

/-- The defining formula of `toJoinVertexOrderHom n`. -/
lemma toJoinVertexOrderHom_apply (z : Fin 2 × Fin (n + 1)) :
    toJoinVertexOrderHom n z = if z.1 = 0 then z.2.castSucc else Fin.last _ :=
  (rfl)

/-- The vertices of the image of a simplex under `toJoinVertex n` are the images of its vertices
under `toJoinVertexOrderHom n`. -/
lemma toJoinVertex_app_apply {d : ℕ} (z : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (toJoinVertex n).app _ z i = toJoinVertexOrderHom n (z.1 i, z.2 i) :=
  (rfl)

variable {n} in
/-- The maps `toJoinVertex` are natural: on the second factor, a simplicial operator `f` acts on
`Δ[n + 1]` through `joinVertex.map f`, which fixes the last vertex. -/
@[reassoc]
lemma whiskerLeft_map_toJoinVertex {m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    Δ[1] ◁ stdSimplex.map f ≫ toJoinVertex.{u} n =
      toJoinVertex m ≫ stdSimplex.map (SimplexCategory.joinVertex.map f) := by
  ext ⟨⟨d⟩⟩ z i
  refine congrArg Fin.val (?_ : toJoinVertexOrderHom n (z.1 i, f.toOrderHom (z.2 i)) =
    (SimplexCategory.joinVertex.map f).toOrderHom (toJoinVertexOrderHom m (z.1 i, z.2 i)))
  simp only [toJoinVertexOrderHom_apply]
  split_ifs <;> simp

/-- On `{0} × Δ[n]`, the map `toJoinVertex n` is the face of `Δ[n + 1]` opposite to its last
vertex. -/
@[reassoc]
lemma whiskerRight_δ_one_toJoinVertex :
    stdSimplex.δ 1 ▷ Δ[n] ≫ toJoinVertex.{u} n = snd _ _ ≫ stdSimplex.δ (Fin.last (n + 1)) := by
  ext ⟨⟨d⟩⟩ z i
  refine congrArg Fin.val (?_ : toJoinVertexOrderHom n (Fin.succAbove 1 (z.1 i), z.2 i) =
    Fin.succAbove (Fin.last _) (z.2 i))
  simp [toJoinVertexOrderHom_apply, Fin.fin_one_eq_zero (z.1 i)]

/-- On `{1} × Δ[n]`, the map `toJoinVertex n` is constant at the last vertex of `Δ[n + 1]`. -/
@[reassoc]
lemma whiskerRight_δ_zero_toJoinVertex :
    stdSimplex.δ 0 ▷ Δ[n] ≫ toJoinVertex.{u} n =
      const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) := by
  ext ⟨⟨d⟩⟩ z i
  refine congrArg Fin.val (?_ : toJoinVertexOrderHom n (Fin.succAbove 0 (z.1 i), z.2 i) =
    Fin.last _)
  simp [toJoinVertexOrderHom_apply]

/-- For `n = 0`, the map `toJoinVertex 0 : Δ[1] ⊗ Δ[0] ⟶ Δ[1]` is the first projection. -/
lemma toJoinVertex_zero : toJoinVertex.{u} 0 = fst _ _ := by
  ext ⟨⟨d⟩⟩ z i
  refine congrArg Fin.val (?_ : toJoinVertexOrderHom 0 (z.1 i, z.2 i) = z.1 i)
  rw [toJoinVertexOrderHom_apply, Fin.fin_one_eq_zero (z.2 i)]
  split_ifs with h
  · exact h.symm
  · exact ((Fin.eq_one_of_ne_zero _ h).symm : _)

/-- A section of `toJoinVertex n`: the map `Δ[n + 1] ⟶ Δ[1] ⊗ Δ[n]` sending the vertex `k ≤ n`
to `(0, k)` and the last vertex to `(1, n)`. -/
noncomputable def toJoinVertexSection : Δ[n + 1] ⟶ (Δ[1] ⊗ Δ[n] : SSet.{u}) :=
  lift (stdSimplex.map (SimplexCategory.joinVertex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)))
    (stdSimplex.σ (Fin.last n))

/-- `toJoinVertexSection n` is a section of `toJoinVertex n`. -/
@[reassoc (attr := simp)]
lemma toJoinVertexSection_toJoinVertex :
    toJoinVertexSection n ≫ toJoinVertex.{u} n = 𝟙 _ := by
  ext ⟨⟨d⟩⟩ z i
  refine congrArg Fin.val (?_ : toJoinVertexOrderHom n
    ((SimplexCategory.joinVertex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).toOrderHom (z i),
      (SimplexCategory.σ (Fin.last n)).toOrderHom (z i)) = z i)
  generalize z i = k
  induction k using Fin.lastCases with
  | last => simp [toJoinVertexOrderHom_apply]
  | cast k =>
    have : (SimplexCategory.σ (Fin.last n)).toOrderHom k.castSucc = k :=
      Fin.predAbove_last_castSucc
    simp [toJoinVertexOrderHom_apply, this]

/-- The collapse `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` is an epimorphism, since it has a section. -/
instance : Epi (toJoinVertex.{u} n) :=
  epi_of_epi_fac (toJoinVertexSection_toJoinVertex n)

end prodStdSimplex

end SSet
