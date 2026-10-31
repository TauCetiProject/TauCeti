/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.Field

/-!
# The tensor square of a purely inseparable extension

Let `L / K` be a purely inseparable field extension. For every `x : L` some `p`-power of `x` lies
in `K`, so the element `1 ⊗ x - x ⊗ 1` of `L ⊗[K] L` is nilpotent. Consequently `L ⊗[K] L` is
reduced only when `L = K`. This is the obstruction showing that a nontrivial finite purely
inseparable extension is not geometrically regular over its base.

Mathlib proves the triviality of `L / K` from the stronger hypothesis that `L` is unramified over
`K` (`Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable`); here the hypothesis is only
that the tensor square is reduced, and no finiteness of `L / K` is assumed.

Over a field `k ⊆ K`, the same nilpotence controls the zero divisors of `L ⊗[k] A` for a commutative
`k`-algebra `A`: every element has a positive power in the subring `K ⊗[k] A`. So if `K ⊗[k] A` is a
domain and `L ⊗[k] A` is reduced, then `L ⊗[k] A` is a domain as well.

## Main results

* `TauCeti.IsPurelyInseparable.isNilpotent_one_tmul_sub_tmul_one`: `1 ⊗ x - x ⊗ 1` is nilpotent in
  `L ⊗[K] L`.
* `TauCeti.IsPurelyInseparable.surjective_algebraMap_of_isReduced_tensorProduct`: if `L ⊗[K] L` is
  reduced, then `algebraMap K L` is surjective.
* `TauCeti.IsPurelyInseparable.isDomain_tensorProduct`: if `K ⊗[k] A` is a domain and `L ⊗[k] A`
  is reduced, then `L ⊗[k] A` is a domain.
-/

public section

open TensorProduct IntermediateField

namespace TauCeti.IsPurelyInseparable

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]

/-- For a purely inseparable extension `L / K` and `x : L`, the element `1 ⊗ x - x ⊗ 1` of
`L ⊗[K] L` is nilpotent. -/
theorem isNilpotent_one_tmul_sub_tmul_one (x : L) :
    IsNilpotent (1 ⊗ₜ[K] x - x ⊗ₜ[K] 1 : L ⊗[K] L) := by
  nontriviality L ⊗[K] L
  obtain ⟨n, r, hr⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) x
  have : ExpChar (L ⊗[K] L) (ringExpChar K) :=
    expChar_of_injective_ringHom (algebraMap K _).injective _
  refine ⟨ringExpChar K ^ n, ?_⟩
  rw [sub_pow_expChar_pow]
  simp [Algebra.TensorProduct.tmul_pow, ← hr, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

/-- A purely inseparable extension `L / K` whose tensor square `L ⊗[K] L` is reduced is trivial:
`algebraMap K L` is surjective. -/
theorem surjective_algebraMap_of_isReduced_tensorProduct [IsReduced (L ⊗[K] L)] :
    Function.Surjective (algebraMap K L) := by
  intro x
  -- Pass to the finite purely inseparable subextension `K⟮x⟯`, whose tensor square embeds into
  -- `L ⊗[K] L` and is therefore reduced.
  let E := K⟮x⟯
  have : FiniteDimensional K E :=
    adjoin.finiteDimensional (IsPurelyInseparable.isIntegral' K x)
  have : IsPurelyInseparable K E := IsPurelyInseparable.tower_bot K E L
  have : IsReduced (E ⊗[K] E) := isReduced_of_injective (Algebra.TensorProduct.map E.val E.val)
    (TensorProduct.map_injective_of_flat_flat _ _ E.val.injective E.val.injective)
  -- Every differential `d y = [1 ⊗ y - y ⊗ 1]` vanishes, so `E` is unramified over `K`.
  have : Algebra.FormallyUnramified K E := by
    refine ⟨subsingleton_of_forall_eq 0 fun ω ↦ ?_⟩
    have hD : Set.range (KaehlerDifferential.D K E) ⊆ {0} := by
      rintro _ ⟨y, rfl⟩
      rw [Set.mem_singleton_iff, KaehlerDifferential.D_apply]
      simp_rw [(isNilpotent_one_tmul_sub_tmul_one K E y).eq_zero]
      exact (KaehlerDifferential.ideal K E).toCotangent.map_zero
    have hω : ω ∈ Submodule.span E (Set.range (KaehlerDifferential.D K E)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    simpa using Submodule.span_mono hD hω
  obtain ⟨y, hy⟩ : AdjoinSimple.gen K x ∈ (algebraMap K E).range := by
    rw [Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable K E]; trivial
  exact ⟨y, congrArg Subtype.val hy⟩

/-- Let `L / K` be a purely inseparable extension of fields over `k`, and let `A` be a commutative
`k`-algebra. If `K ⊗[k] A` is a domain and `L ⊗[k] A` is reduced, then `L ⊗[k] A` is a domain. -/
theorem isDomain_tensorProduct {k : Type*} [Field k] [Algebra k K] [Algebra k L]
    [IsScalarTower k K L] (A : Type*) [CommRing A] [Algebra k A] [hK : IsDomain (K ⊗[k] A)]
    [hL : IsReduced (L ⊗[k] A)] : IsDomain (L ⊗[k] A) := by
  -- `L ⊗[k] A = (K ⊗[k] A) ⊗[K] L`, in which every element has a positive power in `K ⊗[k] A`
  let e : L ⊗[k] A ≃+* (K ⊗[k] A) ⊗[K] L :=
    (Algebra.TensorProduct.cancelBaseChange k K L L A).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm K L (K ⊗[k] A)).toRingEquiv
  have : IsReduced ((K ⊗[k] A) ⊗[K] L) := isReduced_of_injective e.symm e.symm.injective
  have hinj : Function.Injective (algebraMap (K ⊗[k] A) ((K ⊗[k] A) ⊗[K] L)) :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L).injective
  have : Nontrivial ((K ⊗[k] A) ⊗[K] L) := hinj.nontrivial
  have : IsDomain ((K ⊗[k] A) ⊗[K] L) := by
    refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab ↦ ?_⟩
    obtain ⟨m, hm, c, hc⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct a
    obtain ⟨n, hn, d, hd⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct b
    -- `a ^ (m n) b ^ (m n) = 0` comes from `c ^ n d ^ m = 0` in the domain `K ⊗[k] A`
    have hcd : c ^ n * d ^ m = 0 := hinj <| by
      rw [map_mul, map_pow, map_pow, hc, hd, ← pow_mul, ← pow_mul, mul_comm m n, ← mul_pow, hab,
        zero_pow (by positivity), map_zero]
    rcases mul_eq_zero.mp hcd with h | h
    · exact .inl (IsReduced.eq_zero a ⟨m, by rw [← hc, pow_eq_zero_iff hn.ne' |>.mp h, map_zero]⟩)
    · exact .inr (IsReduced.eq_zero b ⟨n, by rw [← hd, pow_eq_zero_iff hm.ne' |>.mp h, map_zero]⟩)
  exact e.toMulEquiv.isDomain

end TauCeti.IsPurelyInseparable
