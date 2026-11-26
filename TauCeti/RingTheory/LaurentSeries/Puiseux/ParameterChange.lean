/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.AlgClosure
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Uniformizer
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

/-!
# Parameter changes act trivially on the Galois group of `K⸨X⸩`

Let `K` be an algebraically closed field of characteristic zero, `F = K⸨X⸩` and `L` an algebraic
closure of `F`, such as the Puiseux field or Mathlib's `AlgebraicClosure F`. Since `L` is
algebraically closed, a `K`-algebra automorphism `τ` of `F`, such as the substitution `f ↦ f (φ)`
of a formal coordinate `φ`, lifts to an automorphism `ρ` of `L`
(`RingEquiv.exists_ringEquiv_apply_algebraMap`), which is `K`-linear since `τ` is. Since `ρ`
preserves `F`, conjugation by `ρ` is an automorphism `σ ↦ ρ σ ρ⁻¹` of the Galois group
`Gal(L/F)`. This file proves that this conjugation
is the identity whenever `τ` sends the parameter `t` to a uniformizer of `F`: every lift `ρ`
commutes with every Galois automorphism `σ`. In particular any two lifts of `τ` induce the same
conjugation, and the identification of `Gal(L/F)` with the Tate module `lim_n μₙ(K)` is unchanged
by transport along a change of parameter. For `L = AlgebraicClosure F` the Galois group is the
absolute Galois group `Field.absoluteGaloisGroup F`.

The proof first treats the Puiseux field `P`, comparing the characters `θₙ (g) = g (α) / α` of
`σ` and of `ρ σ ρ⁻¹`. Take the `n`-th root `α = ρ (t ^ (1 / n))` of the uniformizer `π = τ (t)`.
Since `ρ` fixes the constants `K`, `ρ σ ρ⁻¹` multiplies `α` by the same root of unity by which `σ`
multiplies `t ^ (1 / n)`. The character `θₙ (ρ σ ρ⁻¹)` does not depend on the uniformizer or on
its root (`TauCeti.puiseuxField.apply_eq_algebraMap_proj_galEquivTateModule_mul`), so `σ` and
`ρ σ ρ⁻¹` have the same image in the Tate module `lim_n μₙ(K)`, and hence are equal. A general
algebraic closure `L` is `F`-isomorphic to `P`, and the statement is transported along such an
isomorphism.

## Main results

* `TauCeti.puiseuxField.apply_comm_of_apply_algebraMap`: on an algebraic closure `L` of `F`, a
  lift `ρ` of a `K`-algebra automorphism of `F` sending `t` to a uniformizer satisfies
  `ρ (σ x) = σ (ρ x)` for every Galois automorphism `σ` of `L` over `F`.
* `TauCeti.puiseuxField.commute_toRingEquiv_of_apply_algebraMap`: the same statement as
  commutation in the group of ring automorphisms of `L`.
* `TauCeti.puiseuxField.commute_toRingEquiv_of_apply_algebraMap_substAlgEquiv`: lifts of the
  substitution automorphism of a formal coordinate commute with the Galois group.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- The case of `TauCeti.puiseuxField.apply_comm_of_apply_algebraMap` where the algebraic
closure is the Puiseux field itself, proved by comparing characters `θₙ`. -/
private theorem apply_comm_of_apply_algebraMap_puiseuxField {τ : K⸨X⸩ ≃ₐ[K] K⸨X⸩}
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

variable {L : Type*} [Field L] [Algebra K⸨X⸩ L] [IsAlgClosure K⸨X⸩ L]

/-- **Parameter changes commute with the Galois group.** Let `L` be an algebraic closure of
`K⸨X⸩`, such as the Puiseux field or `AlgebraicClosure K⸨X⸩`, `τ` a `K`-algebra automorphism of
`K⸨X⸩` sending the parameter `t` to a uniformizer, and `ρ` an automorphism of `L` extending `τ`,
which is then `K`-linear. Then `ρ` commutes with every Galois automorphism `σ` of `L` over
`K⸨X⸩`: conjugation by `ρ` is trivial on the Galois group. -/
theorem apply_comm_of_apply_algebraMap {τ : K⸨X⸩ ≃ₐ[K] K⸨X⸩}
    (hτ : (τ (HahnSeries.single 1 1)).order = 1) {ρ : L ≃+* L}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (τ f)) (σ : Gal(L/K⸨X⸩)) (x : L) :
    ρ (σ x) = σ (ρ x) := by
  -- Transport `ρ` to the Puiseux field along an isomorphism `e` with `L`; it fixes `K` there,
  -- since `τ` does.
  let e := IsAlgClosure.equiv K⸨X⸩ (puiseuxField K) L
  have hρ' (f : K⸨X⸩) : e.symm (ρ (e (algebraMap K⸨X⸩ (puiseuxField K) f))) =
      algebraMap K⸨X⸩ (puiseuxField K) (τ f) := by
    simp [hρ]
  let ρ' : puiseuxField K ≃ₐ[K] puiseuxField K :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv.trans (ρ.trans e.symm.toRingEquiv)) fun k ↦ by
      simpa [IsScalarTower.algebraMap_apply K K⸨X⸩ (puiseuxField K)] using hρ' (algebraMap K _ k)
  have h := apply_comm_of_apply_algebraMap_puiseuxField hτ (ρ := ρ') hρ' (e.symm.autCongr σ)
    (e.symm x)
  simpa [ρ', AlgEquiv.autCongr_apply] using h

/-- **Parameter changes commute with the Galois group**, as commutation in the group of ring
automorphisms of an algebraic closure `L` of `K⸨X⸩`: a lift `ρ` of a `K`-algebra automorphism of
`K⸨X⸩` sending `t` to a uniformizer commutes with every Galois automorphism over `K⸨X⸩`. For
`L = AlgebraicClosure K⸨X⸩` these are the elements of `Field.absoluteGaloisGroup K⸨X⸩`, so any two
lifts induce the same conjugation on it, the identity. -/
theorem commute_toRingEquiv_of_apply_algebraMap {τ : K⸨X⸩ ≃ₐ[K] K⸨X⸩}
    (hτ : (τ (HahnSeries.single 1 1)).order = 1) {ρ : RingAut L}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (τ f)) (σ : Gal(L/K⸨X⸩)) :
    Commute ρ σ.toRingEquiv :=
  RingEquiv.ext (apply_comm_of_apply_algebraMap hτ hρ σ)

/-- **Coordinate changes commute with the Galois group.** An automorphism of an algebraic closure
`L` of `K⸨X⸩` extending the substitution automorphism `f ↦ f (φ)` of a formal coordinate `φ`
commutes with every Galois automorphism over `K⸨X⸩`. -/
theorem commute_toRingEquiv_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : RingAut L}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (LaurentSeries.substAlgEquiv φ f))
    (σ : Gal(L/K⸨X⸩)) :
    Commute ρ σ.toRingEquiv := by
  refine commute_toRingEquiv_of_apply_algebraMap ?_ hρ σ
  rw [LaurentSeries.coe_substAlgEquiv, LaurentSeries.substAlgHom_single_one,
    PowerSeries.order_coe, φ.order_toPowerSeries]
  rfl

end TauCeti.puiseuxField
