/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive

/-!
# Duals of simple objects

In a rigid monoidal abelian category whose tensor product is additive, the right dual of a simple
object is simple. Taking right adjoint mates is a bijection `(A ⟶ B) ≃ (Bᘁ ⟶ Aᘁ)` reversing
composition, with inverse the left adjoint mate, and every object `Y` is the right dual `(ᘁY)ᘁ` of
its left dual. So a monomorphism `f : Y ⟶ Xᘁ` is the mate of the epimorphism `ᘁf : X ⟶ ᘁY`, which
out of the simple object `X` is an isomorphism or zero.

This is what makes duality act on the simple isomorphism classes of a fusion category.

If the tensor unit is simple, the tensor product of two nonzero objects is nonzero
(`TauCeti.not_isZero_tensorObj`). The coevaluation `𝟙_ C ⟶ Y ⊗ Yᘁ` of a nonzero object is nonzero,
hence a monomorphism out of the simple unit, and whiskering by `X` keeps it a monomorphism because
`X ⊗ -` is right adjoint to `Xᘁ ⊗ -`. So `X ≅ X ⊗ 𝟙_ C` embeds into `(X ⊗ Y) ⊗ Yᘁ`. Without a
simple unit this fails: in a multifusion category two distinct simple summands of the unit have
zero tensor product.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.8
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Abelian

variable [Abelian C] [MonoidalPreadditive C] [RigidCategory C]

/-- In a rigid monoidal abelian category, the right dual of a simple object is simple. -/
instance simple_rightDual (X : C) [Simple X] : Simple Xᘁ where
  mono_isIso_iff_nonzero {Y} f _ := by
    -- `f` is the right mate of its left mate `g : X ⟶ ᘁY`.
    let g : X ⟶ ᘁY := ᘁf
    have hg : gᘁ = f := rightAdjointMate_leftAdjointMate f
    have hg0 : g = 0 ↔ f = 0 := by
      rw [← hg, ← rightAdjointMate_injective.eq_iff, rightAdjointMate_zero]
    -- Since `f` is a monomorphism, `g` is an epimorphism.
    have : Epi g := ⟨fun {Z} a b hab ↦ by
      have h := congrArg rightAdjointMate hab
      rw [comp_rightAdjointMate, comp_rightAdjointMate, hg, cancel_mono] at h
      exact rightAdjointMate_injective h⟩
    refine ⟨fun _ h0 ↦ ?_, fun h0 ↦ ?_⟩
    · -- If `f` were a zero isomorphism, then `Xᘁ` and hence `X` would be zero.
      have h : (𝟙 X)ᘁ = (0 : X ⟶ X)ᘁ := by
        rw [rightAdjointMate_id, rightAdjointMate_zero, ← IsIso.inv_hom_id f]
        simp only [h0, comp_zero]
      exact id_nonzero X (rightAdjointMate_injective h)
    · have : IsIso g := isIso_of_epi_of_nonzero (mt hg0.1 h0)
      -- The mate of `inv g` inverts `gᘁ = f`; the identity of `(ᘁY)ᘁ` is that of `Y`, since
      -- `(ᘁY)ᘁ = Y` holds by definition (`CategoryTheory.rightDual_leftDual`).
      rw [← hg]
      exact ⟨⟨(inv g)ᘁ,
        by rw [← comp_rightAdjointMate, IsIso.inv_hom_id, rightAdjointMate_id]; rfl,
        by rw [← comp_rightAdjointMate, IsIso.hom_inv_id, rightAdjointMate_id]⟩⟩

end Abelian

/-- In a right rigid monoidal preadditive category with kernels and simple tensor unit, the tensor
product of two nonzero objects is nonzero. -/
theorem not_isZero_tensorObj [Preadditive C] [HasKernels C] [MonoidalPreadditive C]
    [RightRigidCategory C] [Simple (𝟙_ C)] {X Y : C} (hX : ¬IsZero X) (hY : ¬IsZero Y) :
    ¬IsZero (X ⊗ Y) := by
  intro h
  have : Mono (η_ Y Yᘁ) := mono_of_nonzero_from_simple (coevaluation_ne_zero hY)
  have : Mono (X ◁ η_ Y Yᘁ) :=
    (Functor.preservesMonomorphisms_of_adjunction (tensorLeftAdjunction X Xᘁ)).preserves (η_ Y Yᘁ)
  have h' : IsZero (X ⊗ Y ⊗ Yᘁ) := ((tensorRight Yᘁ).map_isZero h).of_iso (α_ X Y Yᘁ).symm
  refine hX (IsZero.of_iso ?_ (ρ_ X).symm)
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X ◁ η_ Y Yᘁ)]
  exact h'.eq_of_tgt _ _

end TauCeti
