/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Pointwise
public import TauCeti.RingTheory.Idempotented.Basic

/-!
# Checks for idempotented algebras and nondegenerate modules

* A nonzero ring with the zero multiplication is not idempotented.
* For a nontrivial commutative ring `A`, the algebra `H = ⊕_{n ∈ ℕ} A = ℕ →₀ A` with the
  componentwise product is idempotented, and the product `∏_n A = ℕ → A`, a module over
  `A ⊕ H` through the inclusion `H → ∏_n A`, is not nondegenerate: the all-one tuple has no finite
  local unit.
* A nondegenerate module is its own nondegenerate part, a module annihilated by `H` has zero
  nondegenerate part, and so does the zero module.
-/

public section

open TauCeti

/-- A nontrivial structure with the zero multiplication is not idempotented. -/
example {H : Type*} [Mul H] [Zero H] [Nontrivial H] (h : ∀ x y : H, x * y = 0) :
    ¬IsIdempotented H := fun _ ↦
  not_subsingleton H (IsIdempotented.subsingleton_of_mul_eq_zero h)

namespace TauCeti.Examples.Idempotented

variable (A : Type*) [CommRing A]

/-- `∏_n A` as a module over the unitization of `⊕_n A`, through the inclusion
`Finsupp.coeFnNonUnitalAlgHom`. -/
noncomputable abbrev piModule : Module (Unitization A (ℕ →₀ A)) (ℕ → A) :=
  Module.compHom (ℕ → A) (Unitization.lift (Finsupp.coeFnNonUnitalAlgHom A)).toRingHom

attribute [local instance] piModule

/-- The action of `A ⊕ (⊕_n A)` on `∏_n A`: apply the inclusion, then multiply. -/
theorem piModule_smul (r : Unitization A (ℕ →₀ A)) (m : ℕ → A) :
    r • m = Unitization.lift (Finsupp.coeFnNonUnitalAlgHom A) r * m :=
  rfl

/-- `⊕_n A` with the componentwise product is idempotented. -/
example : IsIdempotented (ℕ →₀ A) := inferInstance

/-- **`∏_n A` is not a nondegenerate `⊕_n A`-module** for `A ≠ 0`: a local unit `e` of the
all-one tuple would satisfy `e n = 1` for every `n`, so it would not be finitely supported. -/
example [Nontrivial A] : ¬IsNondegenerate A (ℕ →₀ A) (ℕ → A) := by
  rw [isNondegenerate_iff]
  push Not
  refine ⟨1, fun e _ he ↦ ?_⟩
  have h1 : ∀ n, e n = 1 := fun n ↦ by simpa [piModule_smul] using congrFun he n
  exact Set.infinite_univ (e.support.finite_toSet.subset fun n _ ↦ by simp [h1 n])

end TauCeti.Examples.Idempotented

variable {A H M : Type*} [CommRing A] [NonUnitalRing H] [Module A H] [IsScalarTower A H H]
  [SMulCommClass A H H] [AddCommGroup M] [Module (Unitization A H) M]

/-- A nondegenerate module is its own nondegenerate part. -/
example (hM : IsNondegenerate A H M) : nondegeneratePart A H M = ⊤ :=
  hM.nondegeneratePart_eq_top

/-- A module annihilated by `H` has zero nondegenerate part. -/
example (h : ∀ (h : H) (m : M), (h : Unitization A H) • m = 0) : nondegeneratePart A H M = ⊥ :=
  nondegeneratePart_eq_bot_iff.2 h

/-- The zero module has zero nondegenerate part. -/
example [Subsingleton M] : nondegeneratePart A H M = ⊥ :=
  Subsingleton.elim _ _
