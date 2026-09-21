/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.LinearAlgebra.Dual.RightAction

/-!
# The dual of the regular module as a cogenerator

For a finite-dimensional module `M` over an algebra `A`, its linear dual has a finite basis.
Evaluating the action of `A` against the coordinate functionals of that basis embeds `M` into a
finite power of the dual `D(A_A)` of the right regular module.

## Main results

* `LinearEquiv.exists_injective_linearMap_pi_of_dual`: if a left `A`-module is identified with
  `D(A_A)`, every finite-dimensional left `A`-module embeds into a finite power of it.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable {Q : Type*} [AddCommGroup Q] [Module A Q] [Module k Q]

/-- **The dual of the right regular module is a cogenerator.** Let `A` be an algebra over a field
`k` and `Q` a left `A`-module identified with `Module.Dual k A` by a `k`-linear equivalence carrying
the action of `a` to precomposition with right multiplication by `a`. Every finite-dimensional left
`A`-module embeds `A`-linearly into a finite power of `Q`. -/
theorem _root_.LinearEquiv.exists_injective_linearMap_pi_of_dual
    (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) (M : Type*) [AddCommGroup M]
    [Module A M] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    ∃ (n : ℕ) (f : M →ₗ[A] (Fin n → Q)), Function.Injective f := by
  let b := Module.finBasis k M
  -- The coordinate `i` of `f m` is the functional `x ↦ b.coord i (x • m)`.
  let f₀ (m : M) (i : Fin (Module.finrank k M)) : Module.Dual k A :=
    (b.coord i).comp ((LinearMap.toSpanSingleton A M m).restrictScalars k)
  have hf₀ (m : M) (i : Fin (Module.finrank k M)) (x : A) : f₀ m i x = b.coord i (x • m) := rfl
  let f : M →ₗ[A] (Fin (Module.finrank k M) → Q) :=
    { toFun := fun m i ↦ e.symm (f₀ m i)
      map_add' := fun _ _ ↦ by ext i; apply e.injective; ext; simp [hf₀]
      map_smul' := fun _ _ ↦ by ext i; apply e.injective; ext; simp [hf₀, he, mul_smul] }
  refine ⟨_, f, (injective_iff_map_eq_zero f).2 fun m hm ↦ b.ext_elem fun i ↦ ?_⟩
  have hm' : e.symm (f₀ m i) = 0 := congr_fun hm i
  have h : f₀ m i = 0 := by simpa using congr(e $hm')
  simpa [hf₀] using congr($h 1)

end TauCeti
