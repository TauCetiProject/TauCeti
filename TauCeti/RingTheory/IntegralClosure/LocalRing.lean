/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Regular.LinearMap

/-!
# Integrally closed reduced local rings are domains

Mathlib's `IsIntegrallyClosed R` asks `R` to be integrally closed in its total ring of fractions
`FractionRing R`, without assuming that `R` is a domain. This file shows that for a reduced
Noetherian local ring this already forces `R` to be a domain: two minimal primes would split off
a nontrivial idempotent of the total ring of fractions, which is integral over `R` but cannot lie
in the local ring `R` (compare Stacks, Lemma 10.37.16 (030C)).

This is the step of Serre's criterion for normality which turns integral closedness in the total
ring of fractions into the statement that every local ring is an integrally closed domain.

The idempotent is built from an element `x ≠ 0` with `x y = 0`: the ideals `J = ann x` and
`I = ann J` meet in zero, and `I + J` contains a nonzerodivisor `b = i + j`, so `i / b` is an
idempotent of the total ring of fractions. Locality of `R` forces `i = 0` or `j = 0`.

## Main results

* `Ideal.exists_mem_annihilator_sup_isSMulRegular`: in a reduced Noetherian ring, every ideal
  together with its annihilator contains a nonzerodivisor.
* `IsLocalRing.isDomain_of_isIntegrallyClosed`: a reduced Noetherian local ring that is integrally
  closed in its total ring of fractions is a domain.
-/

public section

open IsLocalRing Polynomial

open scoped nonZeroDivisors

/-- In a reduced Noetherian ring, every ideal `J` together with its annihilator contains a
nonzerodivisor: some element of `J.annihilator ⊔ J` is regular on `R`. -/
theorem Ideal.exists_mem_annihilator_sup_isSMulRegular {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsReduced R] (J : Ideal R) :
    ∃ b ∈ J.annihilator ⊔ J, IsSMulRegular R b := by
  -- an element killing `J.annihilator ⊔ J` lies in and kills `J.annihilator`, so its square is zero
  have hann (m : R) (hm : ∀ k ∈ J.annihilator ⊔ J, k * m = 0) : m = 0 := by
    have hmI : m ∈ J.annihilator := Submodule.mem_annihilator.2 fun j hj ↦ by
      rw [smul_eq_mul, mul_comm]
      exact hm j (Ideal.mem_sup_right hj)
    exact IsReduced.eq_zero m ⟨2, by rw [pow_two]; exact hm m (Ideal.mem_sup_left hmI)⟩
  -- so every linear map `R ⧸ (J.annihilator ⊔ J) → R` vanishes
  rw [← Ideal.annihilator_quotient (I := J.annihilator ⊔ J)]
  refine IsSMulRegular.subsingleton_linearMap_iff.1 (subsingleton_of_forall_eq 0 fun f ↦ ?_)
  have hmk (r : R) : Ideal.Quotient.mk (J.annihilator ⊔ J) r = r • Ideal.Quotient.mk _ 1 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]
  have h0 : f (Ideal.Quotient.mk _ 1) = 0 := hann _ fun k hk ↦ by
    rw [← smul_eq_mul, ← map_smul, ← hmk, Ideal.Quotient.eq_zero_iff_mem.2 hk, map_zero]
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]

/-- A reduced Noetherian local ring that is integrally closed in its total ring of fractions is a
domain. -/
theorem IsLocalRing.isDomain_of_isIntegrallyClosed {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsReduced R] [IsIntegrallyClosed R] : IsDomain R := by
  suffices NoZeroDivisors R from NoZeroDivisors.to_isDomain R
  refine ⟨fun {x y} hxy ↦ or_iff_not_and_not.2 fun ⟨hx, hy⟩ ↦ ?_⟩
  -- `J = ann x` and `I = ann J` meet in zero, since `R` is reduced, and `I ⊔ J` contains a
  -- nonzerodivisor `b = i + j`
  let J : Ideal R := (Ideal.span {x}).annihilator
  let I : Ideal R := J.annihilator
  have hJ (j : R) : j ∈ J ↔ j * x = 0 := by
    simp only [J, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hI (i : R) (hi : i ∈ I) (j : R) (hj : j ∈ J) : i * j = 0 :=
    Submodule.mem_annihilator.1 hi j hj
  have hIJ (z : R) (hzI : z ∈ I) (hzJ : z ∈ J) : z = 0 :=
    IsReduced.eq_zero z ⟨2, by rw [pow_two]; exact hI z hzI z hzJ⟩
  obtain ⟨b, hbIJ, hb⟩ := J.exists_mem_annihilator_sup_isSMulRegular
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 hbIJ
  have hb0 : b ∈ R⁰ := mem_nonZeroDivisors_iff_left.2 fun z hz ↦
    hb (show b • z = b • 0 by rw [smul_eq_mul, smul_zero, hz])
  -- `z = i / b` is an idempotent of the total ring of fractions, so it is integral over `R`
  have hii : i * i = i * b := by
    rw [← hij, mul_add, hI i hi j hj, add_zero]
  let K := FractionRing R
  let z : K := IsLocalization.mk' K i ⟨b, hb0⟩
  have hz : z * z = z := by
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq, Submonoid.coe_mul, hii]
    congr 1
    ring
  have hzint : IsIntegral R z := ⟨X ^ 2 - X, (monic_X_pow 2).sub_of_left (by
    rw [degree_X, degree_X_pow]; exact_mod_cast one_lt_two), by simp [pow_two, hz]⟩
  -- hence `z = c` for some `c ∈ R`, and `i (1 - c) = j c` lies in `I ⊓ J`, so it vanishes
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff K).1 ‹_› hzint
  have hcb : c * b = i := IsFractionRing.injective R K <| by
    rw [map_mul, hc, IsLocalization.mk'_spec]
  have hw : i * (1 - c) = j * c := by linear_combination hij.symm * c - hcb
  have hw0 : i * (1 - c) = 0 := hIJ _ (I.mul_mem_right _ hi) (hw ▸ J.mul_mem_right _ hj)
  -- since `R` is local, `c` or `1 - c` is a unit
  rcases isUnit_or_isUnit_one_sub_self c with hu | hu
  · -- `j = 0`, so `b = i` kills `y ∈ J`
    have hj0 : j = 0 := hu.mul_left_eq_zero.1 (hw ▸ hw0)
    rw [hj0, add_zero] at hij
    refine hy (mem_nonZeroDivisors_iff_left.1 hb0 y ?_)
    rw [← hij, hI i hi y ((hJ y).2 (by rw [mul_comm, hxy]))]
  · -- `i = 0`, so `b = j ∈ J` kills `x`
    have hi0 : i = 0 := hu.mul_left_eq_zero.1 hw0
    rw [hi0, zero_add] at hij
    refine hx (mem_nonZeroDivisors_iff_left.1 hb0 x ?_)
    rw [← hij, (hJ j).1 hj]
