/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Normal
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Regular parameters on finite normal local algebras

Let `A → B` be a finite injective local homomorphism from a two-dimensional regular local ring
to a normal local domain. Every pair generating the maximal ideal of `A` is regular on `B`,
viewed as an `A`-module. Such a pair is also regular on `A` itself. These are the simultaneous
regular parameters needed to apply a regular-sequence criterion for freeness to `B`.

The argument uses normality to exclude the maximal ideal of `B` from the associated primes of
a principal quotient. Integrality and locality imply that the images of the parameters generate
an ideal with maximal radical in `B`. No flatness assumption is made.

## Main results

* `TauCeti.IsRegularLocalRing.isRegular_pair_of_finite_normal`: a parameter pair on the base is
  regular on the finite normal local algebra.
* `TauCeti.IsRegularLocalRing.exists_regular_parameters_of_finite_normal`: a pair generating
  the base maximal ideal and regular on both rings exists.

## References

* The Stacks Project, Lemma 10.106.3 (00NQ), regular systems of parameters.
* The Stacks Project, Lemma 10.157.4 (031S), normal rings satisfy Serre's condition `(S₂)`.
-/

public section

open IsLocalRing Ideal RingTheory.Sequence

namespace TauCeti.IsRegularLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsRegularLocalRing A] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Module.Finite A B] [IsLocalHom (algebraMap A B)]

/-- Over a two-dimensional regular local ring, every pair generating the maximal ideal is
regular on any finite injective normal local algebra, considered as a module over the base. -/
theorem isRegular_pair_of_finite_normal (hinj : Function.Injective (algebraMap A B))
    (hdim : ringKrullDim A = 2) {x y : A} (hxy : span {x, y} = maximalIdeal A) :
    IsRegular B [x, y] := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  -- Integrality preserves dimension, so the normal-domain depth-two input applies to `B`.
  have hdimB : 2 ≤ ringKrullDim B := by
    rw [TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := A), hdim]
  have hmB : ¬ (maximalIdeal B).IsPrincipal := fun h ↦
    absurd (hdimB.trans (ringKrullDim_le_one_of_isPrincipal_maximalIdeal h)) (by decide)
  have hmem : ∀ r ∈ [x, y], r ∈ maximalIdeal A := fun r hr ↦ by
    rw [← hxy]
    exact subset_span (by simpa using hr)
  have hregA : IsRegular A [x, y] := isRegular_of_ofList_eq_maximalIdeal
    (by rw [ofList_cons, ofList_singleton, ← span_insert]; exact hxy) (by
      have h := _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
      rw [hdim] at h
      have hrank : 2 ≤ (maximalIdeal A).spanFinrank := by exact_mod_cast h.ge
      simpa using hrank)
  have hx : x ≠ 0 := by
    intro hx
    have hreg := ((isRegular_cons_iff A x [y]).mp hregA).1
    have : (1 : A) = 0 := hreg.right_eq_zero_of_smul (by simp [hx])
    exact one_ne_zero this
  have hxB : algebraMap A B x ≠ 0 := by simpa using hinj.ne hx
  have hmap : (span {x, y}).map (algebraMap A B) =
      span {algebraMap A B x, algebraMap A B y} := by
    simp [Ideal.map_span, Set.image_insert_eq]
  -- Every prime containing the parameter images lies over `𝔪_A`, hence is the unique maximal.
  have hrad : (span {algebraMap A B x, algebraMap A B y}).radical = maximalIdeal B := by
    refine le_antisymm ((maximalIdeal.isMaximal B).isPrime.radical_le_iff.mpr ?_) ?_
    · rw [← hmap, hxy]
      exact map_maximalIdeal_le (algebraMap A B)
    · rw [radical_eq_sInf]
      refine le_sInf fun q hq ↦ ?_
      have : q.IsPrime := hq.2
      have hcom : q.under A = maximalIdeal A := by
        have hqcom : (q.under A).IsPrime := inferInstance
        symm
        apply (maximalIdeal.isMaximal A).eq_of_le hqcom.ne_top
        apply Ideal.map_le_iff_le_comap.mp
        rw [← hxy, hmap]
        exact hq.1
      have hmax : q.IsMaximal := isMaximal_of_isIntegral_of_isMaximal_under q
        (hcom ▸ maximalIdeal.isMaximal A)
      exact (eq_maximalIdeal hmax).symm.le
  -- Form the regular pair over `B`, then restrict scalars to `A` using the native comparison.
  have hregB : IsWeaklyRegular B [algebraMap A B x, algebraMap A B y] := by
    have e : QuotSMulTop (algebraMap A B x) B ≃ₗ[B] B ⧸ span {algebraMap A B x} :=
      (quotientEquivAlgOfEq B (by simp [← Submodule.ideal_span_singleton_smul])).toLinearEquiv
    refine IsWeaklyRegular.cons (IsSMulRegular.of_ne_zero hxB) ?_
    rw [e.isWeaklyRegular_congr, isWeaklyRegular_singleton_iff]
    exact TauCeti.IsIntegrallyClosed.isSMulRegular_quotient_span_singleton_of_radical_span_pair
      hmB hxB hrad
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hmem
  exact (isWeaklyRegular_map_algebraMap_iff B B [x, y]).mp (by simpa using hregB)

/-- A finite injective normal local algebra over a two-dimensional regular local ring admits
a pair of base parameters regular on both the base and the algebra. -/
theorem exists_regular_parameters_of_finite_normal
    (hinj : Function.Injective (algebraMap A B)) (hdim : ringKrullDim A = 2) :
    ∃ x y : A, span {x, y} = maximalIdeal A ∧ IsRegular A [x, y] ∧ IsRegular B [x, y] := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal A).fg_of_isNoetherianRing
  have hrank : (maximalIdeal A).spanFinrank = 2 := by
    have h := _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp (hcard.trans hrank)
  have hxy : span {x, y} = maximalIdeal A := by simpa using hspan
  refine ⟨x, y, hxy, ?_, isRegular_pair_of_finite_normal hinj hdim hxy⟩
  exact isRegular_of_ofList_eq_maximalIdeal
    (by rw [ofList_cons, ofList_singleton, ← span_insert]; exact hxy)
    (by simp [hrank])

end TauCeti.IsRegularLocalRing
