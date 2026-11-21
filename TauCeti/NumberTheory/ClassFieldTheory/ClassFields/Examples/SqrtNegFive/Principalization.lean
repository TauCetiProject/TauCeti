/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Examples.SqrtNegFive.Basic
import Mathlib.Algebra.GroupWithZero.Torsion
import TauCeti.NumberTheory.NumberField.Quadratic.PrimeDecomposition
import TauCeti.NumberTheory.NumberField.WorkedExamples.SqrtNegFive.ClassNumber

/-!
# Principalization in the Hilbert class field of `ℚ(√-5)`

The nonprincipal ideal `(2, √-5 - 1)` of `ℚ(√-5)` extends to `(1 + i)` in the Hilbert class
field `ℚ(i, √5)`. The sign of the chosen square root of `-5` does not affect the ideal, since
it contains `2`. Both the extended ideal and `(1 + i)` square to `(2)`, so unique factorization
of ideals identifies them. This calculation finds a generator without using the general principal
ideal theorem (Artin–Tate, *Class Field Theory*, Chapter XIII).
-/

public noncomputable section

open NumberField IntermediateField TauCeti.Multiquadratic

namespace TauCeti.ClassFieldTheory

variable (hd : Squarefree (-5 : ℤ))

-- Compare the two presentations without losing the chosen generator of the quadratic base.
private theorem exists_ringEquiv_candidateGenusFieldBaseGen :
    ∃ g : 𝓞 (QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0) ≃+* 𝓞 (candidateGenusFieldBase hd),
      g (integralSqrt (QuadraticAlgebra.omega_sq_eq_algebraMap_int (d := -5))) =
        candidateGenusFieldBaseGen hd := by
  have hs : candidateGenusFieldBaseSqrt hd * candidateGenusFieldBaseSqrt hd =
      ((-5 : ℤ) : ℚ) • (1 : candidateGenusFieldBase hd) +
        (0 : ℚ) • candidateGenusFieldBaseSqrt hd := by
    rw [← sq, candidateGenusFieldBaseSqrt_sq, zero_smul, add_zero, Algebra.smul_def, mul_one]
    norm_num
  let f : QuadraticAlgebra ℚ ((-5 : ℤ) : ℚ) 0 →ₐ[ℚ] candidateGenusFieldBase hd :=
    QuadraticAlgebra.lift ⟨_, hs⟩
  have hf : Function.Surjective f := by
    rw [← AlgHom.range_eq_top]
    dsimp only [f]
    rw [QuadraticAlgebra.range_lift hs]
    simpa only [← coe_candidateGenusFieldBaseGen] using adjoin_candidateGenusFieldBaseGen_eq_top hd
  have he : Function.Bijective f := ⟨f.injective, hf⟩
  let e := AlgEquiv.ofBijective f he
  let g := RingOfIntegers.mapRingEquiv e.toRingEquiv
  refine ⟨g, RingOfIntegers.ext ?_⟩
  dsimp only [g]
  rw [RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_toRingEquiv,
    RingOfIntegers.coe_eq_algebraMap, algebraMap_integralSqrt, coe_candidateGenusFieldBaseGen]
  dsimp only [e]
  rw [AlgEquiv.ofBijective_apply]
  dsimp only [f]
  rw [QuadraticAlgebra.lift_apply_apply (a := ((-5 : ℤ) : ℚ)) (b := 0)]
  simp [QuadraticAlgebra.omega]

/-- The ideal `(2, √-5 - 1)` of the embedded quadratic base is not principal. -/
theorem not_isPrincipal_span_two_candidateGenusFieldBaseGen_sub_one :
    ¬ (Ideal.span {(2 : 𝓞 (candidateGenusFieldBase hd)),
      candidateGenusFieldBaseGen hd - 1}).IsPrincipal := by
  intro h
  obtain ⟨g, hg⟩ := exists_ringEquiv_candidateGenusFieldBaseGen hd
  have h' := h.map_ringHom g.symm.toRingHom
  have hgen' := congrArg g.symm hg
  rw [RingEquiv.symm_apply_apply] at hgen'
  rw [Ideal.map_span, Set.image_pair, map_ofNat, map_sub, map_one] at h'
  apply TauCeti.NumberField.SqrtNegFive.not_isPrincipal_span_two_integralSqrt_sub_one
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← hgen'] using h'

-- Give typeclass search the base action directly, rather than searching through the
-- tower of intermediate fields used to construct the base.
/-- The canonical action of the quadratic base on its separable closure. -/
local instance instAlgebraQuadraticBaseSeparableClosure : Algebra (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd)) :=
  (separableClosure (candidateGenusFieldBase hd)
    (AlgebraicClosure (candidateGenusFieldBase hd))).toSubalgebra.algebra

/-- The canonical action of the quadratic base on a subfield of its separable closure. -/
local instance instAlgebraQuadraticBaseIntermediateField
    (F : IntermediateField (candidateGenusFieldBase hd)
      (SeparableClosure (candidateGenusFieldBase hd))) : Algebra (candidateGenusFieldBase hd) F :=
  F.toSubalgebra.algebra

/-- In the Hilbert class field of `ℚ(√-5)`, the ideal `(2, √-5 - 1)` extends to `(1 + i)`
for either root `i` of `X² + 1`. -/
theorem map_span_two_candidateGenusFieldBaseGen_sub_one
    (i : 𝓞 (hilbertClassField (candidateGenusFieldBase hd))) (hi : i ^ 2 = -1) :
    (Ideal.span {(2 : 𝓞 (candidateGenusFieldBase hd)), candidateGenusFieldBaseGen hd - 1}).map
      (algebraMap (𝓞 (candidateGenusFieldBase hd))
        (𝓞 (hilbertClassField (candidateGenusFieldBase hd)))) = Ideal.span {1 + i} := by
  obtain ⟨g, hg⟩ := exists_ringEquiv_candidateGenusFieldBaseGen hd
  have hsq := congrArg (Ideal.map g.toRingHom)
    (QuadraticAlgebra.span_two_integralSqrt_sub_one_sq_eq_span_two (d := -5) (by decide))
  simp only [Ideal.map_pow, Ideal.map_span, Set.image_pair, Set.image_singleton, map_ofNat,
    map_sub, map_one, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hg] at hsq
  have hiunit : IsUnit i := IsUnit.of_mul_eq_one (-i) (by linear_combination -hi)
  have hpi : (1 + i) ^ 2 = 2 * i := by linear_combination hi
  apply (pow_left_inj two_ne_zero).mp
  rw [← Ideal.map_pow, hsq, Ideal.map_span, Set.image_singleton, map_ofNat,
    Ideal.span_singleton_pow, hpi, Ideal.span_singleton_mul_right_unit hiunit]

/-- The generator `1 + i` of the extended ideal exists in the canonical Hilbert class field:
`i` is the transport of the complex imaginary unit from the compositum `ℚ(i, √5)`. -/
theorem exists_sq_eq_neg_one_and_map_span_two_candidateGenusFieldBaseGen_sub_one :
    ∃ i : 𝓞 (hilbertClassField (candidateGenusFieldBase hd)), i ^ 2 = -1 ∧
      (Ideal.span {(2 : 𝓞 (candidateGenusFieldBase hd)), candidateGenusFieldBaseGen hd - 1}).map
        (algebraMap (𝓞 (candidateGenusFieldBase hd))
          (𝓞 (hilbertClassField (candidateGenusFieldBase hd)))) = Ideal.span {1 + i} := by
  obtain ⟨e⟩ := nonempty_algEquiv_hilbertClassField_sqrt_neg_five hd
  let z : adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ) :=
    ⟨Complex.I, subset_adjoin _ _ (Set.mem_insert _ _)⟩
  have hz : z ^ 2 = -1 := Subtype.ext Complex.I_sq
  have hroot : e.symm z ^ 2 = -1 := by rw [← map_pow, hz, map_neg, map_one]
  let i : 𝓞 (hilbertClassField (candidateGenusFieldBase hd)) :=
    integralSqrt (d := -1) (by simpa using hroot)
  have hi : i ^ 2 = -1 := by simp [i, integralSqrt_sq]
  exact ⟨i, hi, map_span_two_candidateGenusFieldBaseGen_sub_one hd i hi⟩

end TauCeti.ClassFieldTheory
