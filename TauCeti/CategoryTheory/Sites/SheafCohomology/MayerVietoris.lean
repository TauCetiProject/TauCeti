/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Vanishing and naturality for the Mayer-Vietoris sequence

For a Mayer-Vietoris square `S` in a site, where `S.X₄` is covered by `S.X₂` and `S.X₃`
meeting in `S.X₁`, Mathlib provides a long exact sequence relating the cohomology of an abelian
sheaf `F` on those four objects. This file records the two consequences that a vanishing
argument needs:

* `epi_δ`: the connecting map `Hⁿ⁰(S.X₁) ⟶ Hⁿ¹(S.X₄)` is an epimorphism as soon as the degree
  `n₁` cohomology of `F` vanishes on `S.X₂` and on `S.X₃`;
* `subsingleton_H'_X₄`: if in addition the degree `n₀` cohomology of `F` vanishes on `S.X₁`,
  then its degree `n₁` cohomology vanishes on `S.X₄`.

So the cohomology of a covered object vanishes once it vanishes on the covering objects and on
their intersection one degree lower; this is the form in which Mayer-Vietoris is applied to a
scheme covered by two open subsets.

The file also records the naturality of the connecting map: with respect to morphisms of
Mayer-Vietoris squares (`δ_naturality_left`), for instance restriction from a cover
`X₄ = X₂ ∪ X₃` to a cover of a smaller open, and with respect to morphisms of coefficient sheaves
(`δ_naturality_right`). Together with the evident naturality of the restriction maps, these make
the Mayer-Vietoris sequences into commutative ladders. The first follows from the naturality of
extension classes, Mathlib's `ShortComplex.ShortExact.extClass_naturality`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- If the cohomology of the two side objects vanishes in degree `n₁`, then the connecting map
from degree `n₀` to degree `n₁` is an epimorphism. -/
theorem epi_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Epi (S.δ F n₀ n₁ h) := by
  have hg : S.toBiprod F n₁ = 0 :=
    ((biprod_isZero_iff _ _).2
      ⟨AddCommGrpCat.isZero_of_subsingleton _,
        AddCommGrpCat.isZero_of_subsingleton _⟩).eq_of_tgt _ _
  have hex := (S.sequence_exact F n₀ n₁ h).exact' 2 3 4
  exact hex.epi_f hg

/-- If the lower-left and the two side cohomology groups in consecutive degrees vanish, then the
upper-right cohomology group vanishes. -/
theorem subsingleton_H'_X₄ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (F.H' n₀ S.X₁))
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Subsingleton (F.H' n₁ S.X₄) := by
  have hsurj : Function.Surjective (S.δ F n₀ n₁ h) :=
    (AddCommGrpCat.epi_iff_surjective _).mp (S.epi_δ F n₀ n₁ h h₂ h₃)
  exact hsurj.subsingleton

/-- **Naturality of the Mayer-Vietoris connecting map in the coefficients.** The connecting map
commutes with the maps on cohomology induced by a morphism `f : F ⟶ G` of abelian sheaves. -/
@[reassoc]
theorem δ_naturality_right {G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ ((Sheaf.cohomologyPresheafFunctor J n₁).map f).app (Opposite.op S.X₄) =
      ((Sheaf.cohomologyPresheafFunctor J n₀).map f).app (Opposite.op S.X₁) ≫ S.δ G n₀ n₁ h := by
  ext x
  -- The connecting map is precomposition with an extension class, and the map induced by `f` is
  -- postcomposition with `f`.
  exact Abelian.Ext.comp_assoc _ _ _ (show 1 + n₀ = n₁ by omega) (add_zero n₀)
    (show 1 + n₀ + 0 = n₁ by omega)

/-- **Naturality of the Mayer-Vietoris connecting map.** For a morphism `φ` from the square
underlying a Mayer-Vietoris square `S'` to that underlying `S`, restricting along `φ` commutes
with the connecting maps of the two Mayer-Vietoris sequences. -/
@[reassoc]
theorem δ_naturality_left {S' : J.MayerVietorisSquare} (φ : S'.toSquare ⟶ S.toSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ (F.cohomologyPresheaf n₁).map φ.τ₄.op =
      (F.cohomologyPresheaf n₀).map φ.τ₁.op ≫ S'.δ F n₀ n₁ h := by
  -- `φ` induces a morphism `ψ` between the short exact sequences of free abelian sheaves
  -- `ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄]` attached to `S'` and to `S`.
  let P := yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v}
  have h₁₂ : P.map φ.τ₁ ≫ biprod.lift (P.map S.f₁₂) (-P.map S.f₁₃) =
      biprod.lift (P.map S'.f₁₂) (-P.map S'.f₁₃) ≫ biprod.map (P.map φ.τ₂) (P.map φ.τ₃) := by
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  have h₂₃ : biprod.map (P.map φ.τ₂) (P.map φ.τ₃) ≫ biprod.desc (P.map S.f₂₄) (P.map S.f₃₄) =
      biprod.desc (P.map S'.f₂₄) (P.map S'.f₃₄) ≫ P.map φ.τ₄ := by
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]
  let ψ : S'.shortComplex ⟶ S.shortComplex :=
    { τ₁ := P.map φ.τ₁
      τ₂ := biprod.map (P.map φ.τ₂) (P.map φ.τ₃)
      τ₃ := P.map φ.τ₄
      comm₁₂ := h₁₂
      comm₂₃ := h₂₃ }
  -- Restrictions are precompositions with the maps of free abelian sheaves and the connecting
  -- maps are precompositions with the extension classes, which are natural in `ψ`.
  have := ShortComplex.ShortExact.extClass_naturality S'.shortComplex_shortExact
    S.shortComplex_shortExact ψ
  ext x
  exact (Abelian.Ext.comp_assoc _ _ x (zero_add 1) (show 1 + n₀ = n₁ by omega)
    (show 0 + 1 + n₀ = n₁ by omega)).symm.trans
    ((congrArg (fun e ↦ e.comp x (show 1 + n₀ = n₁ by omega)) this).symm.trans
      (Abelian.Ext.comp_assoc _ _ x (add_zero 1) (zero_add n₀) (show 1 + 0 + n₀ = n₁ by omega)))

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare
