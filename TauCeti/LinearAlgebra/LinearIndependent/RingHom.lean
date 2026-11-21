/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence of coordinate vectors after a change of rings

A family `v` of coordinate vectors `ι → R` that admits a dual family of linear forms, `φ x (v y)`
being `1` for `x = y` and `0` otherwise, is linearly independent
(`LinearIndependent.of_pairwise_dual_eq_zero_one`). Applying a ring homomorphism `f : R →+* A` to
every coordinate keeps it linearly independent over `A`, since the linear forms can be written as
row vectors and mapped along `f` as well. No flatness of `A` over `R` is needed. For instance, a
basis over `R` of a direct summand of `ι → R` stays linearly independent over every `R`-algebra.

## Main results

* `LinearIndependent.map_of_pairwise_dual_eq_zero_one`: the coordinatewise images `f ∘ v x` of a
  family with a dual family are linearly independent over `A`.
-/

public section

variable {X ι R A : Type*} [Finite ι] [CommSemiring R] [CommRing A]

/-- If a family `v` of coordinate vectors over `R` admits linear forms `φ` with `φ x (v y)` equal
to `1` for `x = y` and to `0` otherwise, then its coordinatewise images `f ∘ v x` under a ring
homomorphism `f : R →+* A` are linearly independent over `A`. -/
theorem LinearIndependent.map_of_pairwise_dual_eq_zero_one (f : R →+* A) (v : X → ι → R)
    (φ : X → Module.Dual R (ι → R)) (h1 : Pairwise fun x y ↦ φ x (v y) = 0)
    (h2 : ∀ x, φ x (v x) = 1) : LinearIndependent A fun x ↦ f ∘ v x := by
  classical
  have := Fintype.ofFinite ι
  -- The linear form `φ x` is the row vector of its values on the standard basis, mapped by `f`.
  let ψ : X → Module.Dual A (ι → A) := fun x ↦
    Fintype.linearCombination A fun j ↦ f (φ x fun j' ↦ if j = j' then 1 else 0)
  have hψ (x y : X) : ψ x (f ∘ v y) = f (φ x (v y)) := by
    rw [LinearMap.pi_apply_eq_sum_univ (φ x) (v y), map_sum, Fintype.linearCombination_apply]
    simp
  refine .of_pairwise_dual_eq_zero_one _ ψ (fun x y hxy ↦ ?_) fun x ↦ ?_
  · simp only [hψ, h1 hxy, map_zero]
  · rw [hψ, h2, map_one]
