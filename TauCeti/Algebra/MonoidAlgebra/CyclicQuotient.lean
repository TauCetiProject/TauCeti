/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import TauCeti.Algebra.Algebra.CyclicQuotient

/-!
# Cyclic quotient of a group ring: the identity-coefficient functional

For a group `G` and an arbitrary ring `Λ`, the identity-coefficient map `x ↦ x.coeff 1` on the
group ring `Λ[G]` is symmetric on products modulo the commutator subgroup `[Λ, Λ]`, so it kills
`[Λ[G], Λ[G]]` and descends to an additive linear functional
`TauCeti.MonoidAlgebra.cyclicCoeffOne Λ G : Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]`.

## Main definitions

* `TauCeti.MonoidAlgebra.cyclicCoeffOne`: the identity-coefficient map
  `Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]`.

## Main results

* `MonoidAlgebra.commutatorSubmodule_mkQ_coeff_one_mul_comm`: modulo `[Λ, Λ]`, `(x * y).coeff 1`
  equals `(y * x).coeff 1`.
* `MonoidAlgebra.coeff_one_mem_commutatorSubmodule`: elements of `[Λ[G], Λ[G]]` have identity
  coefficient in `[Λ, Λ]`.
* `TauCeti.MonoidAlgebra.cyclicCoeffOne_mk`: evaluation of `cyclicCoeffOne` on quotient classes.
* `TauCeti.MonoidAlgebra.cyclicCoeffOne_mapRingHom`: naturality in ring homomorphisms `Λ →+* Λ'`.
* `TauCeti.MonoidAlgebra.cyclicCoeffOne_mapDomainRingHom_of_injective`: pushing forward along an
  injective group homomorphism `H →* G` preserves `cyclicCoeffOne`.

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.1 and 64.15.3).
-/

public section

noncomputable section

namespace MonoidAlgebra

section CyclicCoeffOne

variable {Λ G : Type*} [Ring Λ] [Group G]

/-- Modulo `[Λ, Λ]`, the identity coefficient of a product in `Λ[G]` is symmetric. -/
theorem commutatorSubmodule_mkQ_coeff_one_mul_comm (x y : Λ[G]) :
    (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((x * y).coeff 1) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((y * x).coeff 1) := by
  induction x using induction_linear with
  | zero => simp
  | add _ _ hx₁ hx₂ => simp only [add_mul, mul_add, coeff_add, Finsupp.add_apply, map_add, hx₁, hx₂]
  | single g a =>
    induction y using induction_linear with
    | zero => simp
    | add _ _ hy₁ hy₂ =>
      simp only [mul_add, add_mul, coeff_add, Finsupp.add_apply, map_add, hy₁, hy₂]
    | single h b =>
      simp only [single_mul_single, coeff_single]
      by_cases hgh : g * h = 1
      · simp only [hgh, mul_eq_one_comm.1 hgh, Finsupp.single_eq_same, Submodule.mkQ_apply,
          Submodule.Quotient.eq]
        exact TauCeti.mul_sub_mul_mem_commutatorSubmodule ℤ Λ a b
      · simp [Finsupp.single_eq_of_ne (Ne.symm hgh),
          Finsupp.single_eq_of_ne (Ne.symm (mt mul_eq_one_comm.1 hgh))]

/-- The identity coefficient of any element in `[Λ[G], Λ[G]]` belongs to `[Λ, Λ]`. -/
theorem coeff_one_mem_commutatorSubmodule {x : Λ[G]}
    (hx : x ∈ TauCeti.commutatorSubmodule ℤ Λ[G]) :
    x.coeff 1 ∈ TauCeti.commutatorSubmodule ℤ Λ := by
  have hle : TauCeti.commutatorSubmodule ℤ Λ[G] ≤
      LinearMap.ker ((TauCeti.commutatorSubmodule ℤ Λ).mkQ.comp
        ((Finsupp.lapply (1 : G)).comp (coeffLinearEquiv ℤ).toLinearMap)) :=
    (TauCeti.commutatorSubmodule_le_ker_iff _).2 fun _ _ ↦
      commutatorSubmodule_mkQ_coeff_one_mul_comm _ _
  simpa [Submodule.Quotient.mk_eq_zero] using LinearMap.mem_ker.1 (hle hx)

end CyclicCoeffOne

end MonoidAlgebra

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

section CyclicCoeffOne

variable (Λ G : Type*) [Ring Λ] [Group G]

/-- **The identity-coefficient map on cyclic quotients**
`ε : Λ[G] / [Λ[G], Λ[G]] →ₗ[ℤ] Λ / [Λ, Λ]` (Stacks Project, Section 64.15, Lemma 64.15.1). -/
def cyclicCoeffOne : TauCeti.cyclicQuotient ℤ Λ[G] →ₗ[ℤ] TauCeti.cyclicQuotient ℤ Λ :=
  Submodule.mapQ (TauCeti.commutatorSubmodule ℤ Λ[G]) (TauCeti.commutatorSubmodule ℤ Λ)
    ((Finsupp.lapply (1 : G)).comp (coeffLinearEquiv ℤ).toLinearMap)
    fun _ hx ↦ coeff_one_mem_commutatorSubmodule hx

@[simp] theorem cyclicCoeffOne_mk (x : Λ[G]) :
    cyclicCoeffOne Λ G (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x.coeff 1) := by rfl

variable {Λ G}

/-- Naturality of `cyclicCoeffOne` in ring homomorphisms `φ : Λ →+* Λ'`. -/
@[simp] theorem cyclicCoeffOne_mapRingHom {Λ' : Type*} [Ring Λ'] (φ : Λ →+* Λ')
    (c : TauCeti.cyclicQuotient ℤ Λ[G]) :
    cyclicCoeffOne Λ' G (TauCeti.cyclicQuotientRingHomMap (mapRingHom G φ) c) =
      TauCeti.cyclicQuotientRingHomMap φ (cyclicCoeffOne Λ G c) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c; simp

/-- Pushing forward along an injective group homomorphism `p : H →* G` preserves `cyclicCoeffOne`
(Stacks Project, Section 64.15, Lemma 64.15.3). -/
@[simp] theorem cyclicCoeffOne_mapDomainRingHom_of_injective {H : Type*} [Group H] {p : H →* G}
    (hp : Function.Injective p) (c : TauCeti.cyclicQuotient ℤ Λ[H]) :
    cyclicCoeffOne Λ G (TauCeti.cyclicQuotientRingHomMap (mapDomainRingHom Λ p) c) =
      cyclicCoeffOne Λ H c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [TauCeti.cyclicQuotientRingHomMap_mk, cyclicCoeffOne_mk, cyclicCoeffOne_mk,
    mapDomainRingHom_apply, coeff_mapDomain, ← p.map_one, Finsupp.mapDomain_apply_of_injective hp]

end CyclicCoeffOne

end TauCeti.MonoidAlgebra

end
