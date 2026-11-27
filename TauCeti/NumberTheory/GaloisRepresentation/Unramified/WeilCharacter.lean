/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Topology

/-!
# Unramified characters of the Weil group

Let `K` be a nonarchimedean local field with Weil group `W_K` and degree
`deg : W_K → ℤ` (`TauCeti.ClassFieldTheory.weilDegree`), normalized so that the arithmetic
Frobenius lifts have degree `1`. For every element `α` of a topological group `G` the
**unramified Weil character** `w ↦ α ^ deg w` is a continuous character of `W_K`
(`TauCeti.GaloisRep.weilUnramifiedCharacter`): unlike its Galois counterpart, it needs no
continuity condition on `n ↦ α ^ n`, because the degree map to the discrete group `ℤ` is
continuous for the Weil topology. It is trivial on inertia and sends every arithmetic Frobenius
lift to `α`, and it is the only homomorphism with these two properties
(`TauCeti.GaloisRep.eq_weilUnramifiedCharacter`).

In the docstrings below, `λ(α)` is shorthand for `weilUnramifiedCharacter K α`.

## Main definitions

* `TauCeti.GaloisRep.weilUnramifiedCharacter K α`: the continuous character `w ↦ α ^ deg w`.

## Main results

* `TauCeti.GaloisRep.weilUnramifiedCharacter_apply_of_mem_inertiaSubgroup`,
  `TauCeti.GaloisRep.weilUnramifiedCharacter_apply_of_isArithFrobeniusLift`: trivial on
  inertia, `α` at Frobenius lifts.
* `TauCeti.GaloisRep.eq_weilUnramifiedCharacter`: uniqueness given the value at one Frobenius
  lift.
* `TauCeti.GaloisRep.weilUnramifiedCharacter_one`, `TauCeti.GaloisRep.weilUnramifiedCharacter_mul`,
  `TauCeti.GaloisRep.weilUnramifiedCharacter_inv`, `TauCeti.GaloisRep.weilUnramifiedCharacter_div`,
  `TauCeti.GaloisRep.comp_weilUnramifiedCharacter`: `λ(1) = 1`, `λ(αβ) = λ(α) λ(β)`,
  `λ(α⁻¹) = λ(α)⁻¹`, `λ(α / β) = λ(α) / λ(β)` and coefficient change.
-/

public section

noncomputable section

open ValuativeRel TauCeti.ClassFieldTheory

namespace TauCeti

namespace GaloisRep

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {G : Type*} [Group G] [TopologicalSpace G]

/-- **The unramified character of the Weil group** attached to `α ∈ G`: `w ↦ α ^ deg w`. It is
continuous for the Weil topology, since the degree is continuous into the discrete group `ℤ`. -/
def weilUnramifiedCharacter (α : G) : WeilGroup K →ₜ* G where
  toMonoidHom := (zpowersHom G α).comp (weilDegree K)
  continuous_toFun :=
    (continuous_of_discreteTopology (f := zpowersHom G α)).comp (continuous_weilDegree K)

variable {K}

@[simp]
theorem weilUnramifiedCharacter_apply (α : G) (w : WeilGroup K) :
    weilUnramifiedCharacter K α w = α ^ (weilDegree K w).toAdd := by
  simp [weilUnramifiedCharacter]

/-- The unramified Weil character is trivial on inertia. -/
theorem weilUnramifiedCharacter_apply_of_mem_inertiaSubgroup (α : G) {w : WeilGroup K}
    (hw : weilToAbsolute K w ∈ inertiaSubgroup K) : weilUnramifiedCharacter K α w = 1 := by
  have : weilDegree K w = 1 := (ker_weilDegree K).ge (Subgroup.mem_comap.2 hw)
  simp [this]

/-- The unramified Weil character sends every arithmetic Frobenius lift to `α`. -/
theorem weilUnramifiedCharacter_apply_of_isArithFrobeniusLift (α : G) {w : WeilGroup K}
    (hw : IsArithFrobeniusLift K (weilToAbsolute K w)) : weilUnramifiedCharacter K α w = α := by
  rw [weilUnramifiedCharacter_apply, weilDegree_eq_ofAdd_one_iff.2 hw, toAdd_ofAdd, zpow_one]

/-- **Uniqueness**: a homomorphism `W_K → G` trivial on inertia that sends one arithmetic Frobenius
lift to `α` is the unramified Weil character of `α`. -/
theorem eq_weilUnramifiedCharacter (α : G) (χ : WeilGroup K →* G)
    (hχ : ∀ w, weilToAbsolute K w ∈ inertiaSubgroup K → χ w = 1) {w₀ : WeilGroup K}
    (hw₀ : IsArithFrobeniusLift K (weilToAbsolute K w₀)) (hχw₀ : χ w₀ = α) :
    χ = (weilUnramifiedCharacter K α : WeilGroup K →* G) := by
  ext w
  set n := (weilDegree K w).toAdd
  have hdeg : weilDegree K (w₀ ^ n) = weilDegree K w := by
    simp [n, map_zpow, weilDegree_eq_ofAdd_one_iff.2 hw₀, ← ofAdd_zsmul]
  have hker : (w₀ ^ n)⁻¹ * w ∈ (weilDegree K).ker := by
    simp [MonoidHom.mem_ker, hdeg]
  have h := hχ _ (Subgroup.mem_comap.1 ((ker_weilDegree K).le hker))
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  simp [← h, n, map_zpow, hχw₀]

variable (K) in
/-- `λ(1) = 1`: the unramified Weil character of `1` is trivial. -/
@[simp]
theorem weilUnramifiedCharacter_one : weilUnramifiedCharacter K (1 : G) = 1 := by
  ext w
  simp

/-- `λ(αβ) = λ(α) λ(β)`: the unramified Weil character `weilUnramifiedCharacter K` is
multiplicative in `α` in a commutative group. -/
@[simp]
theorem weilUnramifiedCharacter_mul {A : Type*} [CommGroup A] [TopologicalSpace A]
    [ContinuousMul A] (α β : A) :
    weilUnramifiedCharacter K (α * β) =
      weilUnramifiedCharacter K α * weilUnramifiedCharacter K β := by
  ext w
  simp [mul_zpow]

/-- `λ(α⁻¹) = λ(α)⁻¹` in a commutative topological group. -/
@[simp]
theorem weilUnramifiedCharacter_inv {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (α : A) :
    weilUnramifiedCharacter K α⁻¹ = (weilUnramifiedCharacter K α)⁻¹ := by
  ext w
  simp

/-- `λ(α / β) = λ(α) / λ(β)` in a commutative topological group. -/
@[simp]
theorem weilUnramifiedCharacter_div {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (α β : A) :
    weilUnramifiedCharacter K (α / β) =
      weilUnramifiedCharacter K α / weilUnramifiedCharacter K β := by
  simp [div_eq_mul_inv]

/-- **Coefficient change**: composing with a continuous homomorphism `f` gives the unramified Weil
character of `f α`. -/
@[simp]
theorem comp_weilUnramifiedCharacter {H : Type*} [Group H] [TopologicalSpace H] (f : G →ₜ* H)
    (α : G) : f.comp (weilUnramifiedCharacter K α) = weilUnramifiedCharacter K (f α) := by
  ext w
  simp

end GaloisRep

end TauCeti
