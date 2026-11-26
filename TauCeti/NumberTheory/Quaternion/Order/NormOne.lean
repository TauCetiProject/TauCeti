/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import TauCeti.NumberTheory.Quaternion.Order.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.RingTheory.Ideal.Extended

/-!
# Reduced-norm-one groups of quaternion orders

The reduced-norm-one elements of an order form a subgroup of Mathlib's `unitary` group of the
ambient quaternion algebra. Over a ring with finite quotients any two such groups have finite
relative index. For nested orders, the smaller norm-one group therefore has finite index in
the larger one. In particular this applies to orders over the ring of integers of a number field.

The finite-index proof clears denominators to find a nonzero scalar `r` with `r • Γ ⊆ Λ`.
The kernel of reduction from `Γ¹` to the units of the finite ring `Γ / rΓ` lies in `Λ¹`.

## References

* J. Voight, *Quaternion algebras*, §38.1.5 and §38.3.1.
-/

public section

open scoped Quaternion Pointwise nonZeroDivisors

namespace TauCeti.IntegralOrder.IsOrder

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]
  [IsFractionRing R F] [IsIntegrallyClosed R] {c₁ c₂ c₃ : F}
  [alg : Algebra R ℍ[F,c₁,c₂,c₃]]
  [tower : @IsScalarTower R F ℍ[F,c₁,c₂,c₃] _ _ alg.toSMul]
  {Λ : Subalgebra R ℍ[F,c₁,c₂,c₃]}

/-- The reduced-norm-one group of a quaternion order, as a subgroup of the ambient norm-one
group. Inversion is quaternion conjugation, which preserves the order. -/
def normOne (hΛ : IsOrder F Λ) : Subgroup (unitary ℍ[F,c₁,c₂,c₃]) where
  carrier := {x | (x : ℍ[F,c₁,c₂,c₃]) ∈ Λ}
  one_mem' := Λ.one_mem
  mul_mem' := Λ.mul_mem
  inv_mem' := by
    have halg : alg = QuaternionAlgebra.instAlgebra :=
      Algebra.algebra_ext _ _ fun r =>
        @IsScalarTower.algebraMap_apply R F ℍ[F,c₁,c₂,c₃] _ _ _ _ _ alg tower r
    subst alg
    intro x hx
    exact hΛ.star_mem hx

/-- An ambient reduced-norm-one element belongs to the order's norm-one group exactly when its
underlying quaternion belongs to the order. -/
@[simp]
theorem mem_normOne (hΛ : IsOrder F Λ) {x : unitary ℍ[F,c₁,c₂,c₃]} :
    x ∈ hΛ.normOne ↔ (x : ℍ[F,c₁,c₂,c₃]) ∈ Λ :=
  Iff.rfl

variable {Γ : Subalgebra R ℍ[F,c₁,c₂,c₃]}

/-- Inclusion of quaternion orders induces inclusion of their reduced-norm-one groups. -/
theorem normOne_mono (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (h : Λ ≤ Γ) :
    hΛ.normOne ≤ hΓ.normOne :=
  fun _ hx => h hx

/-- **Any two orders have norm-one groups of finite relative index.** This holds over any
integrally closed ring with fraction field and finite quotients, including rings of integers of
number fields. -/
theorem normOne_isFiniteRelIndex [Ring.HasFiniteQuotients R]
    (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) :
    hΛ.normOne.IsFiniteRelIndex hΓ.normOne := by
  have halg : alg = QuaternionAlgebra.instAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      @IsScalarTower.algebraMap_apply R F ℍ[F,c₁,c₂,c₃] _ _ _ _ _ alg tower r
  subst alg
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (K := F)).2 (Field.toIsField F)
  have hfg : (Subalgebra.toSubmodule Γ).FG := Module.Finite.iff_fg.1 hΓ.finite
  obtain ⟨r, hr, hrΓ⟩ := hfg.exists_smul_mem_of_le_span (F := F)
    (M := Subalgebra.toSubmodule Λ) R⁰ (by
    intro v _
    -- The subalgebra and its underlying submodule have the same carrier.
    change v ∈ Submodule.span F (Λ : Set ℍ[F,c₁,c₂,c₃])
    rw [hΛ.span_eq_top]
    trivial)
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have : Finite (R ⧸ Ideal.span {r}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by simpa using hr0)
  have := hΓ.finite
  have : Finite (Γ ⧸ (Ideal.span {r} • (⊤ : Submodule R Γ))) :=
    Submodule.finite_quotient_smul (Ideal.span {r}) (Module.Finite.fg_top (R := R) (M := Γ))
  let J : Ideal Γ := (Ideal.span {r}).map (algebraMap R Γ)
  let inclusion : hΓ.normOne →* Γ :=
    { toFun := fun x => ⟨(x.val : ℍ[F,c₁,c₂,c₃]), x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let reduction : hΓ.normOne →* (Γ ⧸ J)ˣ :=
    ((Ideal.Quotient.mk J).toMonoidHom.comp inclusion).toHomUnits
  have : reduction.ker.FiniteIndex := inferInstance
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  refine Subgroup.finiteIndex_of_le (H := reduction.ker) fun x hx => ?_
  have hx' : inclusion x - 1 ∈ J := Ideal.Quotient.eq.mp (by
    have := congrArg Units.val hx
    simpa [reduction] using this)
  rw [Ideal.mem_map_algebraMap_iff, Submodule.ideal_span_singleton_smul] at hx'
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ r ⊤).mp hx'
  have hsub : ((inclusion x : Γ) : ℍ[F,c₁,c₂,c₃]) - 1 ∈ Λ := by
    rw [← Subalgebra.coe_one Γ, ← Subalgebra.coe_sub, ← hy]
    exact hrΓ y y.property
  exact (mem_normOne hΛ).mpr (by simpa [inclusion] using Λ.add_mem hsub Λ.one_mem)

end TauCeti.IntegralOrder.IsOrder
