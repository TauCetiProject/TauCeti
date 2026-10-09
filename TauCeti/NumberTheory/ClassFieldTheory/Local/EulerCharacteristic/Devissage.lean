/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Additivity
public import TauCeti.RepresentationTheory.Continuous.TopRep.KernelCokernel
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars

/-!
# Reducing the local Euler characteristic formula to prime coefficients

Let `F` be a finite extension of `ℚ_p`. Tate's local Euler characteristic formula
`χ_F(A) = φ_F(A)` is stated for every finite smooth discrete `A : GalRep n F`. This file reduces
it to modules with coefficients in a prime field `ZMod ℓ`, the first reduction in the classical
proof (NSW (7.3.1); Milne, *Arithmetic Duality Theorems*, I, Theorem 2.8).

Two observations make the reduction. First, the continuous cohomology of a discrete module does
not see its scalars (`TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv`), so a
module with `ZMod n`-scalars that a prime `ℓ` kills has the same local Euler characteristic and
order as the same module with `ZMod ℓ`-scalars. Second, both invariants are multiplicative in
short exact sequences (`localEulerCharacteristic_mul_of_exact`, `localCardNorm_mul_of_exact`),
and a finite module that a prime `ℓ` dividing its order does not kill sits in the exact sequence
`0 → A[ℓ] → A → A / A[ℓ] → 0` with both ends nonzero and so strictly smaller. Induction on the
order of `A` concludes.

## Main results

* `localEulerCharacteristic_eq_localCardNorm_of_nsmul_eq_zero`: the formula for a module killed by
  a prime `ℓ` follows from the formula with `ZMod ℓ`-coefficients.
* `localEulerCharacteristic_eq_localCardNorm_of_forall_prime`: the formula for every finite smooth
  discrete module follows from the formula with prime-field coefficients.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

attribute [local instance] TopRep.distribMulAction

variable (p : ℕ) [Fact p.Prime]
  {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **Changing the coefficients to a prime field.** Let `A : GalRep n F` be finite smooth discrete
and killed by a prime `ℓ`. If Tate's formula `χ_F = φ_F` holds for every finite smooth discrete
module with `ZMod ℓ`-coefficients, it holds for `A`: reading `A` with `ZMod ℓ`-scalars changes
neither its order nor its continuous cohomology groups as abelian groups. -/
theorem localEulerCharacteristic_eq_localCardNorm_of_nsmul_eq_zero {n ℓ : ℕ} [NeZero n]
    [Fact ℓ.Prime]
    (h : ∀ (B : GalRep ℓ F) [Finite B.V] [Fact (IsSmoothDiscrete (ZMod ℓ) B)],
      localEulerCharacteristic (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) B =
        localCardNorm p B)
    (A : GalRep n F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)]
    (hA : ∀ x : A.V, ℓ • x = 0) :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne n)) A = localCardNorm p A := by
  have hsmooth : IsSmoothDiscrete (ZMod n) A := Fact.out
  have := hsmooth.discreteTopology
  let : Module (ZMod ℓ) A.V := AddCommGroup.zmodModule hA
  let : ContinuousSMul (ZMod ℓ) A.V := ⟨continuous_of_discreteTopology⟩
  let B : GalRep ℓ F := ofDiscreteModule (ZMod ℓ) (Field.absoluteGaloisGroup F) A.V
  have : Finite B.V := inferInstanceAs (Finite A.V)
  have hBdisc : DiscreteTopology B.V := inferInstanceAs (DiscreteTopology A.V)
  have : Fact (IsSmoothDiscrete (ZMod ℓ) B) :=
    ⟨⟨inferInstanceAs (DiscreteTopology A.V), fun x ↦ hsmooth.stabilizer_isOpen x⟩⟩
  have hcard (i : ℕ) :
      Nat.card (continuousCohomology i A) = Nat.card (continuousCohomology i B) := by
    -- `B` has the carrier and the operators of `A`, so `A` and `B` have the same discrete
    -- `ℤ`-coefficient object, whose cohomology `ofDiscreteModuleRestrictScalarsIntEquiv`
    -- identifies with that of each. Its instance argument is passed explicitly because
    -- elaboration from `B` alone leaves the instance problem `DiscreteTopology B.V` stuck.
    have eA := ofDiscreteModuleRestrictScalarsIntEquiv A i
    have eB := @ofDiscreteModuleRestrictScalarsIntEquiv (ZMod ℓ) _ _
      (Field.absoluteGaloisGroup F) _ _ _ B hBdisc i
    exact Nat.card_congr (eA.symm.trans eB).toEquiv
  have hB := h B
  apply Subtype.ext
  apply Units.ext
  have hχ := congrArg (fun x : Units.posSubgroup ℚ ↦ ((x.1 : ℚ))) hB
  simp only [localEulerCharacteristic_coe, localCardNorm_coe] at hχ ⊢
  rw [hcard 0, hcard 1, hcard 2]
  exact hχ

/-- **Reduction of Tate's local Euler characteristic formula to prime coefficients.** If
`χ_F = φ_F` holds for every finite smooth discrete module with coefficients in a prime field, it
holds for every finite smooth discrete `A : GalRep n F`. -/
theorem localEulerCharacteristic_eq_localCardNorm_of_forall_prime
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (B : GalRep ℓ F) [Finite B.V]
      [Fact (IsSmoothDiscrete (ZMod ℓ) B)],
      localEulerCharacteristic (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) B =
        localCardNorm p B)
    (n : ℕ) [NeZero n] (A : GalRep n F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne n)) A = localCardNorm p A := by
  -- Strong induction on `#A`. A module killed by a prime is the prime-field case; otherwise a
  -- prime `ℓ` dividing `#A` gives `0 → A[ℓ] → A → A / A[ℓ] → 0` with both ends strictly smaller.
  induction hN : Nat.card A.V using Nat.strong_induction_on generalizing A with
  | _ N ih =>
  have := (Fact.out : IsSmoothDiscrete (ZMod n) A).discreteTopology
  rcases subsingleton_or_nontrivial A.V with hA | hA
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact localEulerCharacteristic_eq_localCardNorm_of_nsmul_eq_zero p (h 2) A
      fun _ ↦ Subsingleton.elim _ _
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := A.V)).ne'
  have : Fact ℓ.Prime := ⟨hℓ⟩
  by_cases hkill : ∀ x : A.V, ℓ • x = 0
  · exact localEulerCharacteristic_eq_localCardNorm_of_nsmul_eq_zero p (h ℓ) A hkill
  push Not at hkill
  obtain ⟨x, hx⟩ := hkill
  have : Fintype A.V := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card (G := A.V) ℓ
    (by rwa [← Nat.card_eq_fintype_card])
  -- `A[ℓ]` is the kernel `K` of multiplication by `ℓ`, and `C = A / A[ℓ]`.
  let f : A ⟶ A := (ℓ : ZMod n) • 𝟙 A
  have hf (a : A.V) : f.hom a = ℓ • a := by
    rw [TopRep.hom_smul, TopRep.hom_id, ContIntertwiningMap.smul_apply,
      ContIntertwiningMap.id_apply, Nat.cast_smul_eq_nsmul]
  let ι := TopRep.kerι f
  let π := TopRep.cokerπ ι
  have hι : Function.Injective ι.hom := TopRep.kerι_injective f
  have hπ : Function.Surjective π.hom := TopRep.cokerπ_surjective ι
  have hιπ : Function.Exact ι.hom π.hom := TopRep.exact_cokerπ ι
  have : DiscreteTopology (TopRep.coker ι).V :=
    QuotientAddGroup.discreteTopology (isOpen_discrete _)
  have : Finite (TopRep.ker f).V := .of_injective _ hι
  have : Finite (TopRep.coker ι).V := .of_surjective _ hπ
  have : Fact (IsSmoothDiscrete (ZMod n) (TopRep.ker f)) := ⟨.of_injective ι hι Fact.out⟩
  have : Fact (IsSmoothDiscrete (ZMod n) (TopRep.coker ι)) := ⟨.of_surjective π hπ Fact.out⟩
  have : Fintype (TopRep.ker f).V := Fintype.ofFinite _
  have : Fintype (TopRep.coker ι).V := Fintype.ofFinite _
  -- `A[ℓ] ≠ A` because `ℓ • x ≠ 0`, and `A[ℓ] ≠ 0` by Cauchy's theorem.
  have hK : Nat.card (TopRep.ker f).V < N := by
    rw [← hN, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_not_surjective _ hι fun hsurj ↦ hx ?_
    obtain ⟨z, hz⟩ := hsurj x
    have hz' := z.2
    rw [LinearMap.mem_ker] at hz'
    rw [← hz, ← hf, show ι.hom z = z.1 from TopRep.kerι_apply f z]
    exact hz'
  have hC : Nat.card (TopRep.coker ι).V < N := by
    rw [← hN, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_surjective_not_injective _ hπ fun hinj ↦ ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp only [addOrderOf_zero] at hy
      exact hℓ.one_lt.ne hy
    have hyι : π.hom y = π.hom 0 := by
      have hyker : y ∈ LinearMap.ker (f.hom : A.V →ₗ[ZMod n] A.V) := by
        rw [LinearMap.mem_ker]
        exact (hf y).trans (by rw [← hy, addOrderOf_nsmul_eq_zero])
      rw [map_zero]
      exact (hιπ y).2 ⟨⟨y, hyker⟩, TopRep.kerι_apply f _⟩
    exact hy0 (hinj hyι)
  -- Both invariants are multiplicative along the sequence, and the ends satisfy the formula.
  have hn : IsUnit (n : F) := (Nat.cast_ne_zero.2 (NeZero.ne n)).isUnit
  rw [localEulerCharacteristic_mul_of_exact hn ι π hι hιπ hπ,
    localCardNorm_mul_of_exact p ι π hι hιπ hπ, ih _ hK (TopRep.ker f) rfl,
    ih _ hC (TopRep.coker ι) rfl]

end TauCeti.ClassFieldTheory
