/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.RingTheory.Idempotents

/-!
# Idempotent endomorphisms of distinguished triangles

Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle in a pretriangulated category, and let
`e₁` and `e₂` be idempotent endomorphisms of `X` and `Y` with `f ≫ e₂ = e₁ ≫ f`. The morphism axiom
extends `(e₁, e₂)` to an endomorphism `(e₁, e₂, c)` of `T`, but `c` need not be idempotent. It is
idempotent up to a square-zero error: `n = c ≫ c - c` vanishes after `g` and before `h`, so it
factors through `h` and `n ≫ n = 0`. An idempotent lifts along a square-zero ideal, here as the
polynomial `1 - (1 - c²)²` in `c` (Mathlib's `isIdempotentElem_one_sub_one_sub_pow_pow`), and
`(e₁, e₂, 1 - (1 - c²)²)` is again an endomorphism of `T`
(`CategoryTheory.Pretriangulated.Triangle.exists_idempotent_hom₃`).

This is the key step in making the idempotent completion of a pretriangulated category
pretriangulated (`TauCeti/CategoryTheory/Triangulated/Karoubi.lean`): it completes a morphism
of the idempotent completion to a distinguished triangle.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, J. Algebra
  236 (2001), Lemma 1.13.
-/

public section

namespace CategoryTheory

open Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

/-- Idempotent endomorphisms `e₁` and `e₂` of the first two objects of a distinguished triangle
which commute with its first morphism extend to an idempotent endomorphism of the triangle. -/
theorem Triangle.exists_idempotent_hom₃ (T : Triangle C) (hT : T ∈ distTriang C)
    {e₁ : T.obj₁ ⟶ T.obj₁} {e₂ : T.obj₂ ⟶ T.obj₂} (he₁ : e₁ ≫ e₁ = e₁) (he₂ : e₂ ≫ e₂ = e₂)
    (comm : T.mor₁ ≫ e₂ = e₁ ≫ T.mor₁) :
    ∃ e₃ : T.obj₃ ⟶ T.obj₃, e₃ ≫ e₃ = e₃ ∧ T.mor₂ ≫ e₃ = e₂ ≫ T.mor₂ ∧
      T.mor₃ ≫ e₁⟦(1 : ℤ)⟧' = e₃ ≫ T.mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism T T hT hT e₁ e₂ comm
  have hcc₂ : T.mor₂ ≫ c ≫ c = e₂ ≫ T.mor₂ := by rw [reassoc_of% hc₂, hc₂, reassoc_of% he₂]
  have hcc₃ : (c ≫ c) ≫ T.mor₃ = T.mor₃ ≫ e₁⟦(1 : ℤ)⟧' := by
    rw [assoc, ← hc₃, ← reassoc_of% hc₃, ← Functor.map_comp, he₁]
  -- The error `c ≫ c - c` vanishes after `T.mor₂`, so it factors through `T.mor₃`; it also
  -- vanishes before `T.mor₃`, so it squares to zero.
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ T hT (c ≫ c - c) (by rw [comp_sub, hcc₂, hc₂, sub_self])
  have hn : (c - c ≫ c) ≫ (c - c ≫ c) = 0 := by
    rw [← neg_sub (c ≫ c), neg_comp, comp_neg, neg_neg]
    conv_lhs => arg 2; rw [hk]
    rw [← assoc, sub_comp, hcc₃, hc₃, sub_self, zero_comp]
  let x : End T.obj₃ := .of c
  have hx : (x - x ^ 2) ^ 2 = 0 := by
    ext
    simpa [sq, x] using hn
  have he := isIdempotentElem_one_sub_one_sub_pow_pow x 2 hx
  have h₂ : T.mor₂ ≫ (𝟙 _ - c ≫ c) = (𝟙 _ - e₂) ≫ T.mor₂ := by simp [hcc₂]
  have h₃ : (𝟙 _ - c ≫ c) ≫ T.mor₃ = T.mor₃ ≫ (𝟙 _ - e₁⟦(1 : ℤ)⟧') := by simp [hcc₃]
  refine ⟨(1 - (1 - x ^ 2) ^ 2).asHom, congr_arg End.asHom he.eq, ?_, ?_⟩
  all_goals
    simp only [sq, End.sub_asHom, End.mul_asHom, End.one_asHom, x]
    generalize 𝟙 T.obj₃ - c ≫ c = d at h₂ h₃ ⊢
  · simp [comp_sub, sub_comp, reassoc_of% h₂, h₂, reassoc_of% he₂]
  · simp [comp_sub, sub_comp, h₃, reassoc_of% h₃, ← Functor.map_comp, he₁]

end Pretriangulated

end CategoryTheory
