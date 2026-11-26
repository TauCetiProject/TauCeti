/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Retracts of finite powers

If a module `Y` is a retract of a finite power `Xᵐ`, with `s : Y → Xᵐ` and `r : Xᵐ → Y` such that
`r ∘ s = id`, then `id_Y` is the finite sum over `j` of the maps `Y → X → Y` through the `j`-th
coordinate (`LinearMap.sum_comp_eq_id_of_comp_eq_id`). This is the form in which a retract of a
finite power enters fullness arguments for idempotents of endomorphism rings. Conversely, if `id_Y`
is a finite sum of maps `u j ∘ v j` factoring through `X`, then `Y` is a retract of a finite power
of `X` (`LinearMap.comp_eq_id_of_sum_comp_eq_id`).

## Main results

* `LinearMap.sum_comp_eq_id_of_comp_eq_id`: a retract of a finite power of `X` writes its identity
  map as a finite sum of maps factoring through `X`.
* `LinearMap.comp_eq_id_of_sum_comp_eq_id`: conversely, a finite sum of maps factoring through `X`
  that equals `id_Y` exhibits `Y` as a retract of a finite power of `X`.
-/

public section

namespace LinearMap

variable {A : Type*} [Semiring A] {X Y : Type*} [AddCommMonoid X] [Module A X] [AddCommMonoid Y]
  [Module A Y]

/-- A retract `Y` of a finite power `Xᵐ` writes `id_Y` as a finite sum of maps factoring through
`X`. -/
theorem sum_comp_eq_id_of_comp_eq_id {m : ℕ} {s : Y →ₗ[A] (Fin m → X)}
    {r : (Fin m → X) →ₗ[A] Y} (hrs : r ∘ₗ s = .id) :
    ∑ j, (r ∘ₗ LinearMap.single A (fun _ ↦ X) j) ∘ₗ (LinearMap.proj j ∘ₗ s) = .id := by
  refine LinearMap.ext fun y ↦ ?_
  simpa [LinearMap.sum_apply, ← map_sum] using
    (congrArg r (LinearMap.sum_single_apply (fun _ ↦ X) (s y))).trans (LinearMap.congr_fun hrs y)

/-- If `id_Y` is a finite sum of maps `u j ∘ v j` factoring through `X`, then `Y` is a retract of
the finite power `ι → X`, through `y ↦ (v j y)ⱼ` and `x ↦ ∑ j, u j (x j)`. -/
theorem comp_eq_id_of_sum_comp_eq_id {ι : Type*} [Fintype ι] {u : ι → X →ₗ[A] Y}
    {v : ι → Y →ₗ[A] X} (h : ∑ j, u j ∘ₗ v j = .id) :
    (∑ j, u j ∘ₗ LinearMap.proj j) ∘ₗ LinearMap.pi v = .id := by
  refine LinearMap.ext fun y ↦ ?_
  simpa [LinearMap.sum_apply] using LinearMap.congr_fun h y

end LinearMap
