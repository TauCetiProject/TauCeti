/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.DirectLimit
public import TauCeti.Algebra.HopfAlgebra.Basic

/-!
# Directed colimits of Hopf algebras

Let `(Aᵢ, fᵢⱼ)` be a directed system of `R`-Hopf algebras with bialgebra morphisms as transition
maps. The colimit `DirectLimit A f` is a bialgebra (`DirectLimit.instBialgebra`); it is a Hopf
algebra, with antipode `S (ofᵢ a) = ofᵢ (S a)`.

## Main definitions

* `DirectLimit.instHopfAlgebra`: the Hopf algebra structure on the colimit.
-/

public section

open TensorProduct Coalgebra

namespace DirectLimit

variable {R : Type*} [CommSemiring R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {A : ι → Type*} [∀ i, Semiring (A i)]

section HopfAlgebra

variable [∀ i, HopfAlgebra R (A i)] (f : ∀ i j, i ≤ j → A i →ₐc[R] A j)
  [DirectedSystem A (f · · ·)]

/-- A directed colimit of Hopf algebras along bialgebra morphisms is a Hopf algebra, with
antipode `S ⟦⟨i, x⟩⟧ = ⟦⟨i, S x⟩⟧` (`antipode_mk`). -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (DirectLimit A f) where
  antipode := Module.lift R ι A f
    (fun i ↦ Module.of R ι A f i ∘ₗ HopfAlgebra.antipode R (A := A i)) fun i j h x ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← BialgHomClass.map_antipode, Module.of_f]
  mul_antipode_rTensor_comul := Module.hom_ext fun i ↦ LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, Module.of_apply, comul_mk, Algebra.linearMap_apply,
      counit_mk, algebraMap_def i]
    rw [← HopfAlgebra.mul_antipode_rTensor_comul_apply]
    induction comul (R := R) x using TensorProduct.inductionOn with
    | tmul a b => simp [mul_def]
    | add a b ha hb => simp only [map_add, ha, hb, add_def]
  mul_antipode_lTensor_comul := Module.hom_ext fun i ↦ LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, Module.of_apply, comul_mk, Algebra.linearMap_apply,
      counit_mk, algebraMap_def i]
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply]
    induction comul (R := R) x using TensorProduct.inductionOn with
    | tmul a b => simp [mul_def]
    | add a b ha hb => simp only [map_add, ha, hb, add_def]

@[simp]
theorem antipode_mk (i : ι) (x : A i) :
    HopfAlgebra.antipode R (⟦⟨i, x⟩⟧ : DirectLimit A f) = ⟦⟨i, HopfAlgebra.antipode R x⟩⟧ :=
  (rfl)

end HopfAlgebra

end DirectLimit
