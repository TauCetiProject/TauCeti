/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.Uniformizer
public import TauCeti.RingTheory.LaurentSeries.Substitution

/-!
# Parameter changes act trivially on the Galois group of `K⸨X⸩`

Let `K` be an algebraically closed field of characteristic zero, `F = K⸨X⸩` and `P` the Puiseux
field, an algebraic closure of `F`. Since `P` is algebraically closed, a `K`-algebra
automorphism `τ` of `F`, such as the substitution `f ↦ f (φ)` of a formal coordinate `φ`, lifts
to a `K`-algebra automorphism `ρ` of `P` (`AlgEquiv.exists_algEquiv_apply_algebraMap`). Since
`ρ` preserves `F`, conjugation by `ρ` is an automorphism `σ ↦ ρ σ ρ⁻¹` of the Galois group
`Gal(P/F)`. This file proves that this conjugation is the identity whenever `τ` sends the
parameter `t` to a uniformizer of `F`: every lift `ρ` commutes with every Galois automorphism `σ`.
In particular any two lifts of `τ` induce the same conjugation, and the identification of
`Gal(P/F)` with the Tate module `lim_n μₙ(K)` is unchanged by transport along a change of
parameter.

The proof compares the characters `θₙ (g) = g (α) / α` of `σ` and of `ρ σ ρ⁻¹`. Take the `n`-th
root `α = ρ (t ^ (1 / n))` of the uniformizer `π = τ (t)`. Since `ρ` fixes the constants `K`,
`ρ σ ρ⁻¹` multiplies `α` by the same root of unity by which `σ` multiplies `t ^ (1 / n)`. The
character `θₙ (ρ σ ρ⁻¹)` does not depend on the uniformizer or on its root
(`TauCeti.puiseuxField.apply_eq_algebraMap_proj_galEquivTateModule_mul`), so `σ` and `ρ σ ρ⁻¹`
have the same image in the Tate module `lim_n μₙ(K)`, and hence are equal.

## Main results

* `TauCeti.puiseuxField.apply_comm_of_apply_algebraMap`: a lift `ρ` of a `K`-algebra automorphism
  of `F` sending `t` to a uniformizer satisfies `ρ (σ x) = σ (ρ x)` for every Galois automorphism
  `σ` of `P` over `F`.
* `TauCeti.puiseuxField.commute_restrictScalars_of_apply_algebraMap`: the same statement as
  commutation in the group of `K`-algebra automorphisms of `P`.
* `TauCeti.puiseuxField.commute_restrictScalars_of_apply_algebraMap_substAlgEquiv`: lifts of the
  substitution automorphism of a formal coordinate commute with the Galois group.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- **Parameter changes commute with the Galois group.** Let `τ` be a `K`-algebra automorphism
of `K⸨X⸩` sending the parameter `t` to a uniformizer, and `ρ` a `K`-algebra automorphism of the
Puiseux field extending `τ`. Then `ρ` commutes with every Galois automorphism `σ` of the Puiseux
field over `K⸨X⸩`: conjugation by `ρ` is trivial on the Galois group. -/
theorem apply_comm_of_apply_algebraMap {τ : K⸨X⸩ ≃ₐ[K] K⸨X⸩}
    (hτ : (τ (HahnSeries.single 1 1)).order = 1) {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) = algebraMap K⸨X⸩ (puiseuxField K) (τ f))
    (σ : Gal(puiseuxField K/K⸨X⸩)) (x : puiseuxField K) :
    ρ (σ x) = σ (ρ x) := by
  have hρ' (f : K⸨X⸩) :
      ρ.symm (algebraMap K⸨X⸩ (puiseuxField K) f) = algebraMap K⸨X⸩ (puiseuxField K) (τ.symm f) :=
    ρ.symm_apply_eq.mpr (by rw [hρ, τ.apply_symm_apply])
  -- The conjugate `c = ρ σ ρ⁻¹` fixes `K⸨X⸩`, so it is a Galois automorphism.
  let c : Gal(puiseuxField K/K⸨X⸩) :=
    AlgEquiv.ofRingEquiv (f := (ρ.symm.trans ((σ.restrictScalars K).trans ρ)).toRingEquiv)
      fun f ↦ by simp [hρ', hρ]
  have hc (y : puiseuxField K) : c y = ρ (σ (ρ.symm y)) := rfl
  suffices hcσ : c = σ by
    calc ρ (σ x) = c (ρ x) := by rw [hc, ρ.symm_apply_apply]
      _ = σ (ρ x) := by rw [hcσ]
  -- Compare the level-`n` components of the images of `c` and `σ` in the Tate module.
  refine (galEquivTateModule K).injective (PrimeToPTateModule.ext fun ⟨m, hm, hm'⟩ ↦ ?_)
  let n : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
  -- The `n`-th root `α = ρ (t ^ (1 / n))` of the uniformizer `τ (t)`.
  set α : puiseuxField K := ρ (levelParameter K n) with hα_def
  have hα : α ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (τ (HahnSeries.single 1 1)) := by
    rw [hα_def, ← map_pow, coe_levelParameter_pow, hρ]
  have hα0 : α ≠ 0 := by
    intro h
    have h0 : algebraMap K⸨X⸩ (puiseuxField K) (τ (HahnSeries.single 1 1)) = 0 := by
      rw [← hα, h, zero_pow n.ne_zero]
    simp [HahnSeries.single_eq_zero_iff] at h0
  have hcα := apply_eq_algebraMap_proj_galEquivTateModule_mul c n hτ hα
  rw [hc, hα_def, ρ.symm_apply_apply, apply_coe_levelParameter, map_mul, AlgEquiv.commutes]
    at hcα
  exact Subtype.ext <| Units.ext <| (algebraMap K (puiseuxField K)).injective
    (mul_right_cancel₀ hα0 hcα).symm

/-- **Parameter changes commute with the Galois group**, as commutation in the group of
`K`-algebra automorphisms of the Puiseux field: a lift `ρ` of a `K`-algebra automorphism of
`K⸨X⸩` sending `t` to a uniformizer commutes with every Galois automorphism over `K⸨X⸩`. -/
theorem commute_restrictScalars_of_apply_algebraMap {τ : K⸨X⸩ ≃ₐ[K] K⸨X⸩}
    (hτ : (τ (HahnSeries.single 1 1)).order = 1) {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) = algebraMap K⸨X⸩ (puiseuxField K) (τ f))
    (σ : Gal(puiseuxField K/K⸨X⸩)) :
    Commute ρ (σ.restrictScalars K) :=
  AlgEquiv.ext (apply_comm_of_apply_algebraMap hτ hρ σ)

/-- **Coordinate changes commute with the Galois group.** A `K`-algebra automorphism of the
Puiseux field extending the substitution automorphism `f ↦ f (φ)` of a formal coordinate `φ`
commutes with every Galois automorphism over `K⸨X⸩`. -/
theorem commute_restrictScalars_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (σ : Gal(puiseuxField K/K⸨X⸩)) :
    Commute ρ (σ.restrictScalars K) := by
  refine commute_restrictScalars_of_apply_algebraMap ?_ hρ σ
  rw [LaurentSeries.coe_substAlgEquiv, LaurentSeries.substAlgHom_single_one,
    PowerSeries.order_coe, φ.order_toPowerSeries]
  rfl

end TauCeti.puiseuxField
