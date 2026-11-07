/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The preadditive coYoneda functor on morphisms out of its object

For an object `M` of a preadditive category with `Γ = End M`, the functor `Hom(M, -)`
(Mathlib's `CategoryTheory.preadditiveCoyonedaObj M`) takes values in `Γᵐᵒᵖ`-modules. By the
Yoneda argument, it is bijective on the morphisms `M ⟶ Y`: a `Γᵐᵒᵖ`-linear map
`φ : Hom(M, M) → Hom(M, Y)` is composition with `φ (𝟙 M)`, since
`φ f = φ (f • 𝟙 M) = f ≫ φ (𝟙 M)` (`CategoryTheory.preadditiveCoyonedaObj_map_bijective_self`).
-/

public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **Yoneda for `Hom(M, -)` as a `Γᵐᵒᵖ`-module, `Γ = End M`.** Composition identifies the
morphisms `M ⟶ Y` with the `Γᵐᵒᵖ`-linear maps `Hom(M, M) → Hom(M, Y)`: a linear map `φ` is
composition with `φ (𝟙 M)`, since `φ f = φ (f • 𝟙 M) = f ≫ φ (𝟙 M)`. -/
theorem preadditiveCoyonedaObj_map_bijective_self (M Y : C) :
    Function.Bijective ((preadditiveCoyonedaObj M).map : (M ⟶ Y) → _) := by
  -- The elements of `(preadditiveCoyonedaObj M).obj X` are the morphisms `M ⟶ X`, and
  -- `(preadditiveCoyonedaObj M).map g` acts on them by composition with `g`; both facts hold by
  -- definition, so the steps below are stated as equalities of morphisms of `C`.
  refine ⟨fun g g' h ↦ ?_, fun φ ↦ ⟨φ.hom (𝟙 M), ?_⟩⟩
  · exact (Category.id_comp g).symm.trans (congr(($h).hom (𝟙 M)).trans (Category.id_comp g'))
  · let ψ : (M ⟶ M) →ₗ[(End M)ᵐᵒᵖ] (M ⟶ Y) := φ.hom
    have key (f : M ⟶ M) : f ≫ ψ (𝟙 M) = ψ f :=
      calc f ≫ ψ (𝟙 M) = MulOpposite.op (End.of f) • ψ (𝟙 M) :=
            (End.smul_left (r := .op (.of f)) (f := ψ (𝟙 M))).symm
        _ = ψ (MulOpposite.op (End.of f) • 𝟙 M) := (ψ.map_smul _ _).symm
        _ = ψ f := congrArg ψ ((End.smul_left (r := .op (.of f)) (f := 𝟙 M)).trans
            (Category.comp_id f))
    ext f
    exact key f

end CategoryTheory
