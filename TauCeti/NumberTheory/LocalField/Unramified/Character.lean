/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.Units.Decomposition
public import TauCeti.Topology.Algebra.Group.SmoothCharacter

/-!
# Unramified characters of a local field

Let `K` be a nonarchimedean local field with normalized valuation `v_K : Kˣ → ℤ`, and let `a` be
an element of a topological group `G`, typically the unit group `Λˣ` of a topological ring. The
*unramified character* attached to `a` is

```text
μ_a : Kˣ → G,    μ_a(x) = a ^ v_K(x).
```

It is continuous because `v_K` is locally constant, it is trivial on the units `U(K,0) = 𝒪[K]ˣ`
of the valuation ring, and it sends every uniformizer to `a`. Conversely a continuous character
of `Kˣ` that is trivial on `U(K,0)` is the unramified character of its value at any uniformizer.
Over `ℚ_p` these are the characters written `μ_λ` by Colmez; under local class field theory,
normalized by geometric Frobenius, they correspond to the unramified Galois characters sending a
geometric Frobenius to `λ`.

## Main definitions

* `TauCeti.unramifiedCharacter K a`: the continuous character `x ↦ a ^ v_K(x)` of `Kˣ`.

## Main results

* `TauCeti.unramifiedCharacter_apply_of_isUniformizer`: `μ_a` sends every uniformizer to `a`.
* `TauCeti.unramifiedCharacter_apply_of_valuation_eq_one`: `μ_a` is trivial on `U(K,0)`.
* `TauCeti.unramifiedCharacter_mul`, `TauCeti.unramifiedCharacter_inv`: `μ_{ab} = μ_a μ_b` and
  `μ_{a⁻¹} = (μ_a)⁻¹` for a commutative group `G`.
* `TauCeti.apply_eq_unramifiedCharacter_of_isUniformizer`: a homomorphism trivial on `U(K,0)` is
  the unramified character of its value at a uniformizer.
* `TauCeti.exists_eq_unramifiedCharacter_iff`: a continuous character is unramified exactly when
  it is trivial on `U(K,0)`.
* `TauCeti.unramifiedCharacter_injective`: `a ↦ μ_a` is injective.
* `TauCeti.isSmoothCharacter_unramifiedCharacter`: `μ_t` with values in a unit group `Aˣ` is a
  smooth character, whatever the topology on `Aˣ`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §1.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The **unramified character** `μ_a : Kˣ → G`, `x ↦ a ^ v_K(x)`, attached to an element `a` of
a topological group `G`. It is continuous because the normalized valuation is locally constant. -/
def unramifiedCharacter (a : G) : Kˣ →ₜ* G where
  toMonoidHom := (zpowersHom G a).comp (normalizedValuation K)
  continuous_toFun := (continuous_of_discreteTopology (f := ⇑(zpowersHom G a))).comp
    (continuous_normalizedValuation K)

variable {K}

/-- The unramified character `μ_a` sends `x` to `a ^ v_K(x)`. -/
@[simp]
theorem unramifiedCharacter_apply (a : G) (x : Kˣ) :
    unramifiedCharacter K a x = a ^ (normalizedValuation K x).toAdd :=
  zpowersHom_apply (α := G) a _

/-- The unramified character `μ_a` sends every uniformizer to `a`. -/
theorem unramifiedCharacter_apply_of_isUniformizer (a : G) {π : Kˣ} (hπ : IsUniformizer K π) :
    unramifiedCharacter K a π = a := by
  rw [unramifiedCharacter_apply, (isUniformizer_def π).1 hπ, toAdd_ofAdd, zpow_one]

/-- The unramified character is trivial on the units `U(K,0)` of the valuation ring. -/
theorem unramifiedCharacter_apply_of_valuation_eq_one (a : G) {u : Kˣ}
    (hu : valuation K (u : K) = 1) : unramifiedCharacter K a u = 1 := by
  rw [unramifiedCharacter_apply, (normalizedValuation_eq_one_iff u).2 hu, toAdd_one, zpow_zero]

variable (K) in
/-- The unramified character attached to `1` is trivial. -/
@[simp]
theorem unramifiedCharacter_one : unramifiedCharacter K (1 : G) = 1 := by
  ext x
  simp

/-- **Unramified characters multiply.** For a commutative group `G`, `μ_{ab} = μ_a μ_b`. -/
@[simp]
theorem unramifiedCharacter_mul {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] (a b : G) :
    unramifiedCharacter K (a * b) = unramifiedCharacter K a * unramifiedCharacter K b := by
  ext x
  simp [mul_zpow]

/-- **Unramified characters invert.** For a commutative topological group `G`,
`μ_{a⁻¹} = (μ_a)⁻¹`. -/
@[simp]
theorem unramifiedCharacter_inv {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (a : G) :
    unramifiedCharacter K a⁻¹ = (unramifiedCharacter K a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← unramifiedCharacter_mul, inv_mul_cancel, unramifiedCharacter_one]

/-- **Characterization of unramified characters.** A homomorphism `δ : Kˣ → G` that is trivial
on the units `U(K,0)` of the valuation ring agrees with the unramified character of its value at
any uniformizer `π`: `δ(x) = δ(π) ^ v_K(x)`. -/
theorem apply_eq_unramifiedCharacter_of_isUniformizer {δ : Kˣ →* G}
    (hδ : ∀ u : Kˣ, valuation K (u : K) = 1 → δ u = 1) {π : Kˣ} (hπ : IsUniformizer K π)
    (x : Kˣ) : δ x = unramifiedCharacter K (δ π) x := by
  set n := (normalizedValuation K x).toAdd
  have hu : valuation K ((x * π ^ (-n) : Kˣ) : K) = 1 := (mem_unitFiltration_zero _).1
    (mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def π).1 hπ) x)
  calc δ x = δ (π ^ n * (x * π ^ (-n))) := by simp [zpow_neg, mul_left_comm]
    _ = unramifiedCharacter K (δ π) x := by
        rw [map_mul, map_zpow, hδ _ hu, mul_one, unramifiedCharacter_apply]

/-- A continuous character of `Kˣ` is unramified, that is of the form `μ_a`, exactly when it is
trivial on the units `U(K,0)` of the valuation ring. -/
theorem exists_eq_unramifiedCharacter_iff {δ : Kˣ →ₜ* G} :
    (∃ a : G, δ = unramifiedCharacter K a) ↔ ∀ u : Kˣ, valuation K (u : K) = 1 → δ u = 1 := by
  refine ⟨?_, fun hδ ↦ ?_⟩
  · rintro ⟨a, rfl⟩ u hu
    exact unramifiedCharacter_apply_of_valuation_eq_one a hu
  · obtain ⟨π, hπ⟩ := exists_isUniformizer K
    exact ⟨δ π, ContinuousMonoidHom.ext <| apply_eq_unramifiedCharacter_of_isUniformizer
      (δ := δ.toMonoidHom) hδ hπ⟩

variable (K) in
/-- An unramified character determines its value at a uniformizer, so `a ↦ μ_a` is injective. -/
theorem unramifiedCharacter_injective :
    Function.Injective (unramifiedCharacter K : G → Kˣ →ₜ* G) := by
  intro a b h
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  rw [← unramifiedCharacter_apply_of_isUniformizer a hπ,
    ← unramifiedCharacter_apply_of_isUniformizer b hπ, h]

variable (K) in
/-- **Commutativity criterion for pointwise products of unramified characters.** For any
nonarchimedean local field `K`, topological group `G`, and elements `a, b : G`, the pointwise
product `x ↦ μ_a(x) * μ_b(x)` is a group homomorphism on `Kˣ` if and only if `a` and `b`
commute. -/
theorem exists_monoidHom_mul_unramifiedCharacter_iff (a b : G) :
    (∃ δ : Kˣ →* G,
      ∀ x : Kˣ, δ x = unramifiedCharacter K a x * unramifiedCharacter K b x) ↔
      Commute a b := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  constructor
  · rintro ⟨δ, hδ⟩
    have hsq : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
      have ha : unramifiedCharacter K a π = a := unramifiedCharacter_apply_of_isUniformizer a hπ
      have hb : unramifiedCharacter K b π = b := unramifiedCharacter_apply_of_isUniformizer b hπ
      have h1 : δ (π ^ 2) = (a * b) ^ 2 := by rw [map_pow, hδ, ha, hb]
      have h2 : δ (π ^ 2) = a ^ 2 * b ^ 2 := by rw [hδ, map_pow, map_pow, ha, hb]
      exact h1.symm.trans h2
    rw [sq, sq, sq] at hsq
    have h1 : b * a * b = a * b * b :=
      mul_left_cancel (a := a) (by simpa [mul_assoc] using hsq)
    exact (mul_right_cancel h1).symm
  · intro hcomm
    refine ⟨(unramifiedCharacter K (a * b)).toMonoidHom, fun x ↦ ?_⟩
    simp [hcomm.mul_zpow]

variable (K) in
/-- The unramified character `μ_t` with values in a unit group `Aˣ` is smooth, whatever the topology
on `Aˣ`: its kernel contains the open subgroup `U(K,0)` of units of valuation one. -/
theorem isSmoothCharacter_unramifiedCharacter {A : Type*} [Monoid A] [TopologicalSpace Aˣ]
    (t : Aˣ) : IsSmoothCharacter (unramifiedCharacter K t : Kˣ →* Aˣ) := by
  refine isSmoothCharacter_iff.2 (Subgroup.isOpen_mono (fun u hu ↦ ?_) (isOpen_unitFiltration 0))
  rw [MonoidHom.mem_ker, MonoidHom.coe_ofClass]
  exact unramifiedCharacter_apply_of_valuation_eq_one t ((mem_unitFiltration_zero u).1 hu)

end TauCeti
