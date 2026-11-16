/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Diagonals of monomorphisms as pullbacks

For a monomorphism `ι : X ⟶ Y` between objects admitting binary self-products, the diagonal
`diag X : X ⟶ X ⨯ X` is the pullback of `diag Y : Y ⟶ Y ⨯ Y` along `ι ⨯ ι`
(`CategoryTheory.Limits.isPullback_diag_of_mono`). Consequently every morphism property stable under
base change passes from `diag Y` to `diag X`.
-/

public section

namespace CategoryTheory.Limits

/-- For a monomorphism `ι : X ⟶ Y` between objects with binary self-products, the diagonal of `X`
is the pullback of the diagonal of `Y` along `ι ⨯ ι`. -/
theorem isPullback_diag_of_mono {D : Type*} [Category* D] {X Y : D}
    [HasBinaryProduct X X] [HasBinaryProduct Y Y] (ι : X ⟶ Y) [Mono ι] :
    IsPullback ι (Limits.diag X) (Limits.diag Y) (prod.map ι ι) := by
  refine IsPullback.mk' (by ext <;> simp)
    (fun _ _ _ h₁ _ ↦ (cancel_mono ι).1 h₁) fun _ a b h ↦ ?_
  have h₁ : a = (b ≫ prod.fst) ≫ ι := by simpa using h =≫ prod.fst
  have h₂ : a = (b ≫ prod.snd) ≫ ι := by simpa using h =≫ prod.snd
  have h₁₂ : b ≫ prod.fst = b ≫ prod.snd := (cancel_mono ι).1 (h₁.symm.trans h₂)
  exact ⟨b ≫ prod.fst, h₁.symm, by ext <;> simp [h₁₂]⟩

end CategoryTheory.Limits
