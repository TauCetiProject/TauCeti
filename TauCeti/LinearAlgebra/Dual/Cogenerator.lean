/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# The dual of the regular module as a cogenerator

Let `A` be a semiring with a module structure over a commutative semiring `k`.
If a left `A`-module `M` is finite projective over `k` and the scalar actions form a tower,
evaluating the action of `A` against the coordinates of a `k`-linear embedding of `M` into a
finite free `k`-module embeds `M` into a finite power of the dual `D(A_A)` of the right regular
module. This includes every finite-dimensional module over an algebra over a field.

## Main results

* `LinearEquiv.exists_injective_linearMap_pi_of_dual`: if a left `A`-module is identified with
  `D(A_A)`, every left `A`-module that is finite projective over `k` embeds into a finite power
  of it.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [CommSemiring k]
variable {A : Type u} [Semiring A] [Module k A]
variable {Q : Type*} [AddCommMonoid Q] [Module A Q] [Module k Q]

/-- **The dual of the right regular module cogenerates finite projective semimodules.** Let `Q`
be a left `A`-module identified with `Module.Dual k A` by a `k`-linear equivalence carrying the
action of `a` to precomposition with right multiplication by `a`. Every left `A`-module that is
finite projective over `k`, with compatible scalar actions, embeds `A`-linearly into a finite
power of `Q`. -/
theorem _root_.LinearEquiv.exists_injective_linearMap_pi_of_dual
    (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) (M : Type*) [AddCommMonoid M]
    [Module A M] [Module k M] [IsScalarTower k A M] [Module.Projective k M] [Module.Finite k M] :
    ∃ (n : ℕ) (f : M →ₗ[A] (Fin n → Q)), Function.Injective f := by
  obtain ⟨n, -, g, -, hg, -⟩ := Module.Finite.exists_comp_eq_id_of_projective k M
  -- The coordinate `i` of `f m` is the functional `x ↦ g (x • m) i`.
  let f₀ (m : M) (i : Fin n) : Module.Dual k A :=
    (LinearMap.proj i ∘ₗ g) ∘ₗ (LinearMap.toSpanSingleton A M m).restrictScalars k
  have hf₀ (m : M) (i : Fin n) (x : A) : f₀ m i x = g (x • m) i := rfl
  let f : M →ₗ[A] (Fin n → Q) :=
    { toFun := fun m i ↦ e.symm (f₀ m i)
      map_add' := fun _ _ ↦ by ext i; apply e.injective; ext; simp [hf₀]
      map_smul' := fun _ _ ↦ by ext i; apply e.injective; ext; simp [hf₀, he, mul_smul] }
  refine ⟨n, f, fun m m' hm ↦ hg (funext fun i ↦ ?_)⟩
  simpa [f, hf₀] using congr(e ($hm i) 1)

end TauCeti
