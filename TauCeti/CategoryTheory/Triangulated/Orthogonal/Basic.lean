/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Right orthogonality of third vertices of triangles

Let `P` be a class of objects of a pretriangulated category, stable under shifts, and let
`T : X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be a distinguished triangle. If every morphism from an object of `P`
to `X₂` factors uniquely through `X₁ ⟶ X₂`, then `X₃` is right orthogonal to `P`. This is the
long exact sequence of `Hom(K, -)` for objects `K` of `P`: surjectivity at `K` kills the image of
`Hom(K, X₂)` in `Hom(K, X₃)`, and injectivity at `K⟦-1⟧` kills the connecting map to
`Hom(K, X₁⟦1⟧)`.

This is how one shows that an object built as a cone is orthogonal to a class of objects
satisfying a lifting property, as for curved modules with projective underlying graded module
and totalizations of short exact sequences.

Dually, `X₃` has no nonzero morphism to any shift of an object `M` if and only if precomposition
with `X₁ ⟶ X₂` is a bijection `Hom(X₂, M⟦n⟧) → Hom(X₁, M⟦n⟧)` for every `n`
(`CategoryTheory.Pretriangulated.forall_hom_shift_eq_zero_iff`), by the long exact sequence of
`Hom(-, M)`.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]

/-- Let `T` be a distinguished triangle such that, for every object `K` of a shift-stable class
`P`, composition with `T.mor₁` is a bijection from morphisms `K ⟶ T.obj₁` to morphisms
`K ⟶ T.obj₂`. Then `T.obj₃` is right orthogonal to `P`. -/
theorem rightOrthogonal_obj₃_of_bijective (T : Triangle C) (hT : T ∈ distTriang C)
    (H : ∀ K, P K → Function.Bijective fun f : K ⟶ T.obj₁ ↦ f ≫ T.mor₁) :
    P.rightOrthogonal T.obj₃ := by
  intro K φ hK
  -- The connecting morphism `φ ≫ T.mor₃` vanishes: its unshift by `-1` lands in `T.obj₁` and
  -- becomes zero after composing with `T.mor₁`, so it is zero by injectivity at `K⟦-1⟧`.
  have hφ : φ ≫ T.mor₃ = 0 := by
    let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
    have h₀ : ((φ ≫ T.mor₃)⟦(-1 : ℤ)⟧' ≫ e.hom.app T.obj₁) ≫ T.mor₁ = 0 ≫ T.mor₁ := by
      have hn := e.hom.naturality T.mor₁
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
      rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, Category.assoc,
        comp_distTriang_mor_zero₃₁ T hT, comp_zero, Functor.map_zero, zero_comp, zero_comp]
    have h₁ := (H _ (P.le_shift (-1 : ℤ) K hK)).1 h₀
    rw [Preadditive.IsIso.comp_right_eq_zero] at h₁
    exact ((shiftFunctor C (-1 : ℤ)).map_eq_zero_iff).1 h₁
  obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ T hT φ hφ
  obtain ⟨χ, rfl⟩ := (H K hK).2 ψ
  rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Pretriangulated

open Limits

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The third object of a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` has no nonzero
morphism to any shift of `M` if and only if precomposition with `X₁ ⟶ X₂` is a bijection
`Hom(X₂, M⟦n⟧) → Hom(X₁, M⟦n⟧)` for every `n`. -/
theorem forall_hom_shift_eq_zero_iff {T : Triangle D} (hT : T ∈ distTriang D) (M : D) :
    (∀ (n : ℤ) (φ : T.obj₃ ⟶ M⟦n⟧), φ = 0) ↔
      ∀ n : ℤ, Function.Bijective fun g : T.obj₂ ⟶ M⟦n⟧ ↦ T.mor₁ ≫ g := by
  -- Shifting by `1` identifies morphisms `X ⟶ M⟦n⟧` with morphisms `X⟦1⟧ ⟶ M⟦n + 1⟧`.
  let e (n : ℤ) : (M⟦n⟧)⟦(1 : ℤ)⟧ ≅ M⟦n + 1⟧ := (shiftFunctorAdd' D n 1 (n + 1) rfl).symm.app M
  constructor
  · intro h n
    refine ⟨fun g₁ g₂ hg ↦ ?_, fun k ↦ ?_⟩
    · dsimp only at hg
      rw [← sub_eq_zero]
      obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ T hT (g₁ - g₂) (by rw [Preadditive.comp_sub, hg,
        sub_self])
      rw [hφ, h n φ, comp_zero]
    · -- `k` extends along `X₁ ⟶ X₂` since its composite with `X₃⟦-1⟧ ⟶ X₁` vanishes.
      have hrot := inv_rot_of_distTriang T hT
      have key (k' : T.invRotate.obj₂ ⟶ M⟦n⟧) : ∃ g, k' = T.invRotate.mor₂ ≫ g :=
        Triangle.yoneda_exact₂ _ hrot k' (by
          apply (shiftFunctor D (1 : ℤ)).map_injective
          rw [Functor.map_zero, ← cancel_mono (e n).hom, zero_comp]
          have h' := h (n + 1) (((shiftFunctorCompIsoId D (-1 : ℤ) 1 (by lia)).app T.obj₃).inv ≫
            (T.invRotate.mor₁ ≫ k')⟦1⟧' ≫ (e n).hom)
          exact (Iso.cancel_iso_inv_left _ _ _).1 (h'.trans comp_zero.symm))
      obtain ⟨g, hg⟩ := key k
      exact ⟨g, hg.symm⟩
  · intro h n φ
    -- The composite `X₂ ⟶ X₃ ⟶ M⟦n⟧` vanishes on `X₁`, so it is zero.
    have h₂ : T.mor₂ ≫ φ = 0 :=
      (h n).1 (by dsimp only; rw [comp_distTriang_mor_zero₁₂_assoc _ hT, comp_zero, zero_comp])
    obtain ⟨ψ, rfl⟩ := Triangle.yoneda_exact₃ T hT φ h₂
    -- `ψ : X₁⟦1⟧ ⟶ M⟦n⟧` extends along `X₁⟦1⟧ ⟶ X₂⟦1⟧`.
    let e' : M⟦n⟧ ≅ (M⟦n - 1⟧)⟦(1 : ℤ)⟧ := (shiftFunctorAdd' D (n - 1) 1 n (by lia)).app M
    obtain ⟨θ, hθ⟩ := (shiftFunctor D (1 : ℤ)).map_surjective (ψ ≫ e'.hom)
    obtain ⟨χ, rfl⟩ := (h (n - 1)).2 θ
    rw [← cancel_mono e'.hom, Category.assoc, ← hθ, Functor.map_comp,
      comp_distTriang_mor_zero₃₁_assoc _ hT, zero_comp, zero_comp]

end CategoryTheory.Pretriangulated
