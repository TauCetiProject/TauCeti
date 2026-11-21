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
import TauCeti.FieldTheory.IntermediateField.Adjoin.Transcendental
import TauCeti.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Unramified.Localization

/-!
# Generic fibres of reduced algebras over a domain

Let `P` be a domain with fraction field `FP`, and let `B` be a reduced `P`-algebra essentially of
finite type. If at every minimal prime `p` of `B` lying over the zero ideal of `P` the residue
field `κ(p)` is algebraic and formally unramified over `P`, then the generic fibre `FP ⊗[P] B` is
étale over `FP`, that is, a finite product of finite separable extensions of `FP`.

The primes of `FP ⊗[P] B` are the primes of `B` meeting no nonzero element of `P`, and
`Algebra.isUnramifiedAt_localization_iff` reduces unramifiedness of `FP ⊗[P] B` over `FP` at such a
prime `q` to unramifiedness of `B` over `P` at `q`. Algebraicity of the components makes every
such prime minimal (`Ideal.mem_minimalPrimes_of_under_eq_bot`): a prime strictly above a minimal
prime `p` contains a nonzero element of `B ⧸ p` algebraic over `P`, and hence a nonzero element of
`P`. At a minimal prime the local ring of the reduced ring `B` is the residue field, so
`FP ⊗[P] B` is unramified over `FP` at every prime, hence formally unramified over `FP` by
`Algebra.formallyUnramified_iff_forall`. Over the field `FP` it is then formally étale
(`Algebra.FormallyEtale.of_formallyUnramified_of_field`) and finite, so étale
(`Algebra.Etale.of_formallyUnramified_of_flat`).

Together with torsion-freeness
(`TauCeti.isTorsionFree_of_injective_algebraMap_quotient_minimalPrimes`) these are the two
hypotheses on `B` in `TauCeti.Ring.finite_integralClosure_of_isTorsionFree_of_etale`. The étale
criterion is specialized to `P = R[X]` for a domain `R` with fraction field `K`, where `B` is a
`K`-algebra and the image `y` of `X` in every residue field `κ(p)` at a minimal prime is a
separating transcendental element: `K(y)` is then a fraction field of `R[X]` over which `κ(p)` is
separable. This is the affine finiteness step that
`TauCeti.finite_integralClosure_of_forall_finrank_kaehlerDifferential_eq_one` uses toward finite
normalization of models of smooth curves over a possibly non-excellent discrete valuation ring.

## Main results

* `TauCeti.etale_tensorProduct_of_isAlgebraic_and_formallyUnramified_at_minimalPrimes`: the
  generic fibre of a reduced algebra essentially of finite type, algebraic and unramified at its
  minimal primes over the zero ideal, is étale.
* `TauCeti.etale_tensorProduct_polynomial_of_forall_isSeparable`: the case of a coordinate that is
  separating on every component of `B`.

## References

* The Stacks Project, Lemma 55.8.2, https://stacks.math.columbia.edu/tag/0C2T.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]

/-- **A generic fibre that is algebraic and unramified at its generic points is étale.** Let `P`
be a domain with fraction field `FP`, and let `B` be a reduced `P`-algebra essentially of finite
type. If at every minimal prime `p` of `B` lying over the zero ideal of `P` the residue field
`κ(p)` is algebraic and formally unramified over `P`, then `FP ⊗[P] B` is an étale
`FP`-algebra. -/
theorem etale_tensorProduct_of_isAlgebraic_and_formallyUnramified_at_minimalPrimes (FP : Type*)
    [Field FP] [Algebra P FP] [IsFractionRing P FP] [Algebra.EssFiniteType P B] [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B → p.under P = ⊥ →
      Algebra.IsAlgebraic P p.ResidueField ∧ Algebra.FormallyUnramified P p.ResidueField) :
    Algebra.Etale FP (FP ⊗[P] B) := by
  have := (IsFractionRing.injective P FP).isDomain (algebraMap P FP)
  let : Algebra B (FP ⊗[P] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors P)) (FP ⊗[P] B) :=
    IsLocalization.tensorRight FP _
  have : Algebra.FormallyUnramified FP (FP ⊗[P] B) := by
    refine Algebra.formallyUnramified_iff_forall.mpr fun Q ↦
      (Algebra.isUnramifiedAt_localization_iff (S := B) (nonZeroDivisors P) Q.asIdeal).mpr ?_
    -- The prime `Q ∩ B` meets no nonzero element of `P`, which is a unit in `FP ⊗[P] B`.
    have hQ : (Q.asIdeal.under B).under P = ⊥ := by
      refine eq_bot_iff.mpr fun a haQ ↦ Ideal.mem_bot.mpr (by_contra fun ha ↦ ?_)
      refine Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ haQ ?_)
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply P FP]
      exact ((IsFractionRing.injective P FP).ne_iff' (map_zero _)).mpr ha |>.isUnit.map _
    have hq : Q.asIdeal.under B ∈ minimalPrimes B := by
      refine Ideal.mem_minimalPrimes_of_under_eq_bot _ hQ fun p hp hpq ↦ ?_
      have := hp.1.1
      have := (h p hp (le_bot_iff.mp (hQ ▸ Ideal.comap_mono hpq))).1
      exact .of_injective (IsScalarTower.toAlgHom P (B ⧸ p) p.ResidueField)
        p.injective_algebraMap_quotient_residueField
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

/-- **A separating coordinate makes the generic fibre étale.** Let `R` be a domain with fraction
field `K`, and let `B` be a reduced `R[X]`-algebra which is also a `K`-algebra essentially of finite
type. Suppose that at every minimal prime `p` of `B` lying over the zero ideal of `R[X]` the image
`y` of `X` in `κ(p)` is transcendental over `K` and `κ(p)` is separable over `K(y)`. Then the
generic fibre of `B` over `R[X]` is a finite étale algebra over the fraction field of `R[X]`. -/
theorem etale_tensorProduct_polynomial_of_forall_isSeparable [IsFractionRing R K]
    [Algebra.EssFiniteType K B] [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B → p.under R[X] = ⊥ →
      Transcendental K (algebraMap R[X] p.ResidueField X) ∧
        Algebra.IsSeparable K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField) :
    Algebra.Etale (FractionRing R[X]) (FractionRing R[X] ⊗[R[X]] B) := by
  have := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  have : Algebra.EssFiniteType R B := .comp R K B
  have : Algebra.EssFiniteType R[X] B := .of_comp R R[X] B
  refine etale_tensorProduct_of_isAlgebraic_and_formallyUnramified_at_minimalPrimes _
    fun p _ hp hp0 ↦ ?_
  obtain ⟨hy, hsep⟩ := h p hp hp0
  -- Factor `R[X] → κ(p)` through `K(y)`, a fraction field of `R[X]` over which `κ(p)` is
  -- separable.
  let := (aeval (R := R) (AdjoinSimple.gen K (algebraMap R[X] p.ResidueField X))).toAlgebra
  have : IsScalarTower R[X] K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField :=
    .of_algebraMap_eq fun f ↦ by
      rw [algebraMap_eq_aeval]
      exact (aeval_algHom_apply
        ((K⟮algebraMap R[X] p.ResidueField X⟯).val.restrictScalars R) (AdjoinSimple.gen K _) f)
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
