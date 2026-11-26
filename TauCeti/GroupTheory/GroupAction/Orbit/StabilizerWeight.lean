/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Module.BigOperators
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Stabiliser weights on the orbits of a finite group

Let a finite group `G` act on a type `X` and let `c` be a natural number. A *stabiliser weight*
is a function `u : X → ℕ` whose translates add up to `c`, that is `∑_{g ∈ G} u (g • x) = c` for
every `x`. Choosing a point `r` in each orbit, the function equal to `c / |Stab(r)|` at `r` and to
`0` elsewhere is such a weight whenever every stabiliser order divides `c`. Conversely the sum
`∑_g u (g • x)` is `|Stab(x)|` times the sum of `u` over the orbit of `x`, so a stabiliser weight
exists exactly when every stabiliser order divides `c`. No finiteness of `X` is needed.

Multiplication by a stabiliser weight is an operator `Ψ` on the functions `X → M` whose
conjugates add up to `c`: with `G` acting on functions by `(g f)(x) = f (g⁻¹ • x)`, that is by
`LinearMap.funLeft R M (g⁻¹ • ·)`, one has `∑_g g⁻¹ Ψ g = c`. This is the hypothesis of the
version of Higman's criterion up to `c`.

## Main results

* `TauCeti.MulAction.card_filter_smul_eq`: `#{g | g • x = a • x} = |Stab(x)|`.
* `TauCeti.MulAction.sum_smul_eq_natCard_stabilizer_nsmul`: `∑_g f (g • x)` is `|Stab(x)|` times
  the sum of `f` over the orbit of `x`.
* `TauCeti.MulAction.exists_sum_smul_eq_iff`: a weight `u : X → ℕ` with
  `∑_g u (g • x) = c` for every `x` exists if and only if every stabiliser order divides `c`.
* `TauCeti.MulAction.exists_sum_funLeft_comp_eq_smul`: when every stabiliser order divides `c`,
  multiplication by some `u : X → ℕ` is an operator `Ψ` on `X → M` with `∑_g g⁻¹ Ψ g = c`.

## Provenance

The construction of the weight follows `New.Patching.exists_orbit_weight` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC), the
combinatorial core of `New.Patching.BaseLevel.exists_higman_operator`, stated here for an
arbitrary action of a finite group.
-/

public section

namespace TauCeti.MulAction

open _root_.MulAction Finset

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]

/-- The elements of a finite group moving `x` to `a • x` are as many as the stabiliser of `x`. -/
theorem card_filter_smul_eq (x : X) (a : G) [DecidablePred fun g : G ↦ g • x = a • x] :
    #{g : G | g • x = a • x} = Nat.card (stabilizer G x) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine card_nbij' (a⁻¹ * ·) (a * ·) (fun g hg ↦ ?_) (fun g hg ↦ ?_) (fun g _ ↦ by simp)
    (fun g _ ↦ by simp)
  · simp_all [mul_smul]
  · simp_all [mul_smul]

/-- The sum of `f (g • x)` over a finite group is the order of the stabiliser of `x` times the
sum of `f` over the orbit of `x`. -/
theorem sum_smul_eq_natCard_stabilizer_nsmul {M : Type*} [AddCommMonoid M] [DecidableEq X]
    (f : X → M) (x : X) :
    ∑ g : G, f (g • x) =
      Nat.card (stabilizer G x) • ∑ y ∈ univ.image (fun g : G ↦ g • x), f y := by
  rw [Finset.sum_comp, Finset.smul_sum]
  refine sum_congr rfl fun y hy ↦ ?_
  obtain ⟨a, -, rfl⟩ := mem_image.mp hy
  rw [card_filter_smul_eq]

/-- If every stabiliser order divides `c`, some `u : X → ℕ` satisfies `∑_g u (g • x) = c` for
every `x`. -/
theorem exists_sum_smul_eq_of_natCard_stabilizer_dvd {c : ℕ}
    (hc : ∀ x : X, Nat.card (stabilizer G x) ∣ c) :
    ∃ u : X → ℕ, ∀ x, ∑ g : G, u (g • x) = c := by
  classical
  -- `u` is `c / |Stab(r)|` at the chosen point `r` of each orbit and `0` elsewhere.
  let r : X → X := fun x ↦ (Quotient.mk'' x : orbitRel.Quotient G X).out
  have hr (g : G) (x : X) : r (g • x) = r x :=
    congrArg Quotient.out (Quotient.sound (mem_orbit x g))
  refine ⟨fun x ↦ if x = r x then c / Nat.card (stabilizer G x) else 0, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : G, a • x = r x := Quotient.mk_out (s := orbitRel G X) x
  have hstab : Nat.card (stabilizer G (r x)) = Nat.card (stabilizer G x) :=
    TauCeti.card_stabilizer_of_orbitRel ⟨a, ha⟩
  calc ∑ g : G, (if g • x = r (g • x) then c / Nat.card (stabilizer G (g • x)) else 0)
      = ∑ g : G, if g • x = a • x then c / Nat.card (stabilizer G x) else 0 := by
        refine sum_congr rfl fun g _ ↦ ?_
        rw [hr, ← ha]
        split_ifs with h
        · rw [h, ha, hstab]
        · rfl
    _ = c := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, card_filter_smul_eq, smul_eq_mul,
          Nat.mul_div_cancel' (hc x)]

/-- A weight `u : X → ℕ` with `∑_g u (g • x) = c` for every `x` exists if and only if every
stabiliser order divides `c`. -/
theorem exists_sum_smul_eq_iff {c : ℕ} :
    (∃ u : X → ℕ, ∀ x, ∑ g : G, u (g • x) = c) ↔ ∀ x : X, Nat.card (stabilizer G x) ∣ c := by
  classical
  refine ⟨fun ⟨u, hu⟩ x ↦ ?_, exists_sum_smul_eq_of_natCard_stabilizer_dvd⟩
  rw [← hu x, sum_smul_eq_natCard_stabilizer_nsmul, smul_eq_mul]
  exact dvd_mul_right _ _

/-- If every stabiliser order divides `c`, multiplication by some `u : X → ℕ` is an operator `Ψ`
on `X → M` whose conjugates `g⁻¹ Ψ g` add up to `c`, where `g` acts by `f ↦ f (g⁻¹ • ·)`. -/
theorem exists_sum_funLeft_comp_eq_smul (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] {c : ℕ} (hc : ∀ x : X, Nat.card (stabilizer G x) ∣ c) :
    ∃ (u : X → ℕ) (Ψ : (X → M) →ₗ[R] X → M), (∀ f x, Ψ f x = u x • f x) ∧
      ∑ g : G, LinearMap.funLeft R M (g • ·) ∘ₗ Ψ ∘ₗ LinearMap.funLeft R M (g⁻¹ • ·) =
        c • LinearMap.id := by
  obtain ⟨u, hu⟩ := exists_sum_smul_eq_of_natCard_stabilizer_dvd hc
  refine ⟨u, LinearMap.pi fun x ↦ u x • LinearMap.proj x, fun _ _ ↦ rfl, ?_⟩
  ext f x
  simp [LinearMap.funLeft, ← sum_smul, hu]

end TauCeti.MulAction
