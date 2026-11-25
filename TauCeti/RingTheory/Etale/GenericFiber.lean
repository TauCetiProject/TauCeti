/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Smooth.Fiber
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Unramified.Localization

/-!
# Generic fibres of algebras over a domain

Let `P` be a domain with fraction field `FP`, and let `B` be a `P`-algebra whose generic fibre
`FP ⊗[P] B` is reduced and essentially of finite type over `FP`. If at every minimal prime `p` of
`B` lying over the zero ideal of `P` the residue field `κ(p)` is algebraic and formally unramified
over `P`, then the generic fibre is étale over `FP`, that is, a finite product of finite separable
extensions of `FP`.

The primes of `FP ⊗[P] B` are the primes of `B` meeting no nonzero element of `P`, and
`Algebra.isUnramifiedAt_localization_iff` reduces unramifiedness of `FP ⊗[P] B` over `FP` at such a
prime `q` to unramifiedness of `B` over `P` at `q`. Algebraicity of the components makes every
such prime minimal (`Ideal.mem_minimalPrimes_of_under_eq_bot_of_isAlgebraic_quotient`): a prime
strictly above a minimal prime `p` contains a nonzero element of `B ⧸ p` algebraic over `P`, and
hence a nonzero element of `P`. At a minimal prime the local ring of `B`, which is also a local ring
of the reduced ring `FP ⊗[P] B`, is the residue field, so `FP ⊗[P] B` is unramified over `FP` at
every prime, hence formally unramified over `FP` by `Algebra.formallyUnramified_iff_forall`. Over
the field `FP` it is then formally étale (`Algebra.FormallyEtale.of_formallyUnramified_of_field`)
and finite, so étale (`Algebra.Etale.of_formallyUnramified_of_flat`).

Together with torsion-freeness
(`TauCeti.isTorsionFree_of_algebraMap_quotient_minimalPrimes_ne_zero`) these are the two
hypotheses on `B` in `TauCeti.Ring.finite_integralClosure_of_isTorsionFree_of_etale`. The étale
criterion is specialized to `P = R[X]` for a domain `R` with fraction field `K`, where `B` is a
`K`-algebra and, at every minimal prime `p` of `B` lying over the zero ideal of `R[X]`, the image
`y` of `X` in `κ(p)` is a separating element: `y` is then transcendental over `K`, `K(y)` is a
fraction field of `R[X]`, and `κ(p)` is separable over it. This is the affine finiteness step that
`TauCeti.finite_integralClosure_of_forall_transcendental_and_finrank_kaehlerDifferential_eq_one`
uses toward finite normalization of models of smooth curves over a possibly non-excellent discrete
valuation ring.

## Main results

* `TauCeti.etale_tensorProduct_of_isAlgebraic_and_formallyUnramified_at_minimalPrimes`: a reduced
  generic fibre essentially of finite type, algebraic and unramified at the minimal primes over the
  zero ideal, is étale.
* `TauCeti.etale_tensorProduct_polynomial_of_forall_isSeparable`: the case of a coordinate that is
  separating at every minimal prime lying over the zero ideal of `R[X]`.

## References

* The Stacks Project, Lemma 55.8.2, https://stacks.math.columbia.edu/tag/0C2T.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]

/-- **A reduced generic fibre of essentially finite type that is algebraic and unramified at its
generic points is étale.** Let `P` be a domain with fraction field `FP`, and let `B` be a
`P`-algebra such that `FP ⊗[P] B` is reduced and essentially of finite type over `FP`. If at every
minimal prime `p` of `B` lying over the zero ideal of `P` the residue field `κ(p)` is algebraic and
formally unramified over `P`, then `FP ⊗[P] B` is an étale `FP`-algebra. -/
theorem etale_tensorProduct_of_isAlgebraic_and_formallyUnramified_at_minimalPrimes (FP : Type*)
    [Field FP] [Algebra P FP] [IsFractionRing P FP] [Algebra.EssFiniteType FP (FP ⊗[P] B)]
    [IsReduced (FP ⊗[P] B)]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B → p.under P = ⊥ →
      Algebra.IsAlgebraic P p.ResidueField ∧ Algebra.FormallyUnramified P p.ResidueField) :
    Algebra.Etale FP (FP ⊗[P] B) := by
  let : Algebra B (FP ⊗[P] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors P)) (FP ⊗[P] B) :=
    IsLocalization.tensorRight FP _
  have : Algebra.FormallyUnramified FP (FP ⊗[P] B) := by
    refine Algebra.formallyUnramified_iff_forall.mpr fun Q ↦
      (Algebra.isUnramifiedAt_localization_iff (S := B) (nonZeroDivisors P) Q.asIdeal).mpr ?_
    -- The prime `Q ∩ B` lies over the prime `Q ∩ FP = 0` of the field `FP`.
    have hQ : (Q.asIdeal.under B).under P = ⊥ := by
      rw [Ideal.under_under, ← Ideal.under_under (B := FP),
        Ideal.eq_bot_of_prime (Q.asIdeal.under FP)]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective P FP)
    have hq : Q.asIdeal.under B ∈ minimalPrimes B := by
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Q.asIdeal.under B)
      have := hp.1.1
      have := (h p hp (le_bot_iff.mp (hQ ▸ Ideal.comap_mono hpq))).1
      have : Algebra.IsAlgebraic P (B ⧸ p) :=
        .of_injective (IsScalarTower.toAlgHom P (B ⧸ p) p.ResidueField)
          p.injective_algebraMap_quotient_residueField
      exact Ideal.mem_minimalPrimes_of_under_eq_bot_of_isAlgebraic_quotient hp hpq hQ
    -- The local ring of `B` at `Q ∩ B` is that of the reduced ring `FP ⊗[P] B` at `Q`.
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors P)) (Localization.AtPrime Q.asIdeal) Q.asIdeal
    let e := IsLocalization.algEquiv (Q.asIdeal.under B).primeCompl
      (Localization.AtPrime (Q.asIdeal.under B)) (Localization.AtPrime Q.asIdeal)
    have : IsReduced (Localization.AtPrime (Q.asIdeal.under B)) :=
      isReduced_of_injective e.toRingHom e.injective
    have := (h _ hq hQ).2
    exact .of_equiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom P _ _)
      (Ideal.bijective_algebraMap_residueField_of_mem_minimalPrimes _ hq)).symm
  have := Algebra.FormallyUnramified.finite_of_free FP (FP ⊗[P] B)
  have : Algebra.FinitePresentation FP (FP ⊗[P] B) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact .of_formallyUnramified_of_flat

section Coordinate

open Polynomial IntermediateField

variable {R K B : Type*} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B]
  [Algebra K B] [IsScalarTower R K B] [Algebra R[X] B] [IsScalarTower R R[X] B]

/-- **A separating coordinate makes a reduced generic fibre of essentially finite type étale.** Let
`R` be a domain with fraction field `K`, let `L` be a fraction field of `R[X]`, and let `B` be an
`R[X]`-algebra which is also a `K`-algebra, whose generic fibre `L ⊗[R[X]] B` is reduced and
essentially of finite type over `L`. Suppose that at every minimal prime `p` of `B` lying over the
zero ideal of `R[X]` the residue field `κ(p)` is separable over the subfield `K(y)` generated by the
image `y` of `X`. Then `L ⊗[R[X]] B` is a finite étale `L`-algebra. -/
theorem etale_tensorProduct_polynomial_of_forall_isSeparable [IsFractionRing R K] (L : Type*)
    [Field L] [Algebra R[X] L] [IsFractionRing R[X] L] [Algebra.EssFiniteType L (L ⊗[R[X]] B)]
    [IsReduced (L ⊗[R[X]] B)]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B → p.under R[X] = ⊥ →
      Algebra.IsSeparable K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField) :
    Algebra.Etale L (L ⊗[R[X]] B) := by
  have := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  refine etale_tensorProduct_of_isAlgebraic_and_formallyUnramified_at_minimalPrimes
    L fun p _ hp hp0 ↦ ?_
  have := h p hp hp0
  -- Over the zero ideal of `R[X]`, the image `y` of `X` is transcendental over `R`, hence over `K`.
  have hy : Transcendental K (algebraMap R[X] p.ResidueField X) := by
    refine (IsFractionRing.isAlgebraic_iff R K _).not.mp (transcendental_iff.mpr fun f hf ↦ ?_)
    rw [← algebraMap_eq_aeval, IsScalarTower.algebraMap_apply R[X] B,
      Ideal.algebraMap_residueField_eq_zero, ← Ideal.mem_comap] at hf
    exact Ideal.mem_bot.mp (hp0 ▸ hf)
  -- Factor `R[X] → κ(p)` through `K(y)`, a fraction field of `R[X]` over which `κ(p)` is
  -- separable.
  let := (aeval (R := R) (AdjoinSimple.gen K (algebraMap R[X] p.ResidueField X))).toAlgebra
  let ι : K⟮algebraMap R[X] p.ResidueField X⟯ →ₐ[R] p.ResidueField :=
    (K⟮algebraMap R[X] p.ResidueField X⟯).val.restrictScalars R
  have : IsScalarTower R[X] K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField :=
    .of_algebraMap_eq fun f ↦ by
      rw [algebraMap_eq_aeval, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, IntermediateField.algebraMap_apply]
      exact aeval_algHom_apply ι (AdjoinSimple.gen K _) f
  have := hy.isFractionRing_adjoin_simple (R := R)
  have : Algebra.FormallyUnramified K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField :=
    .of_isSeparable _ _
  have : Algebra.FormallyUnramified R[X] K⟮algebraMap R[X] p.ResidueField X⟯ :=
    .of_isLocalization (nonZeroDivisors R[X])
  have := IsLocalization.isAlgebraic K⟮algebraMap R[X] p.ResidueField X⟯ (nonZeroDivisors R[X])
  exact ⟨.trans R[X] K⟮algebraMap R[X] p.ResidueField X⟯ _,
    .comp R[X] K⟮algebraMap R[X] p.ResidueField X⟯ _⟩

end Coordinate

end TauCeti
