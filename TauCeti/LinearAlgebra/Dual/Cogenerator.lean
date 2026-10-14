/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The dual of the regular module as a cogenerator

Let `A` be a semiring with a module structure over a commutative semiring `k`.
If a left `A`-module `M` is finite free over `k` and the scalar actions form a tower, evaluating
the action of `A` against coordinate functionals embeds `M` into a finite power of the dual
`D(A_A)` of the right regular module. This includes every finite-dimensional module over an
algebra over a field.

## Main results

* `LinearEquiv.exists_injective_linearMap_pi_of_dual`: if a left `A`-module is identified with
  `D(A_A)`, every left `A`-module that is finite free over `k` embeds into a finite power of it.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [CommSemiring k]
variable {A : Type u} [Semiring A] [Module k A]
variable {Q : Type*} [AddCommMonoid Q] [Module A Q] [Module k Q]

/-- **The dual of the right regular module cogenerates finite free semimodules.** Let `Q` be a
left `A`-module identified with `Module.Dual k A` by a `k`-linear equivalence carrying the action
of `a` to precomposition with right multiplication by `a`. Every left `A`-module that is finite
free over `k`, with compatible scalar actions, embeds `A`-linearly into a finite power of `Q`. -/
theorem _root_.LinearEquiv.exists_injective_linearMap_pi_of_dual
    (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) (M : Type*) [AddCommMonoid M]
    [Module A M] [Module k M] [IsScalarTower k A M] [Module.Free k M] [Module.Finite k M] :
    ∃ (n : ℕ) (f : M →ₗ[A] (Fin n → Q)), Function.Injective f := by
  let n := Fintype.card (Module.Free.ChooseBasisIndex k M)
  let b := (Module.Free.chooseBasis k M).reindex (Fintype.equivFin _)
  -- The coordinate `i` of `f m` is the functional `x ↦ b.coord i (x • m)`.
  let f₀ (m : M) (i : Fin n) : Module.Dual k A :=
    (b.coord i).comp ((LinearMap.toSpanSingleton A M m).restrictScalars k)
  have hf₀ (m : M) (i : Fin n) (x : A) : f₀ m i x = b.coord i (x • m) := rfl
  let f : M →ₗ[A] (Fin n → Q) :=
    { toFun := fun m i ↦ e.symm (f₀ m i)
      map_add' := fun _ _ ↦ by ext i; apply e.injective; ext; simp [hf₀]
      map_smul' := fun _ _ ↦ by ext i; apply e.injective; ext; simp [hf₀, he, mul_smul] }
  refine ⟨_, f, fun m m' hm ↦ b.ext_elem fun i ↦ ?_⟩
  have hm' : e.symm (f₀ m i) = e.symm (f₀ m' i) := congr_fun hm i
  have h : f₀ m i = f₀ m' i := e.symm.injective hm'
  simpa [hf₀] using congr($h 1)

end TauCeti
