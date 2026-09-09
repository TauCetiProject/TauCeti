/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.AdicPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Add
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# The formal parameter map is additive

For an adic ideal `I` of a complete ring `O` mapping injectively to a field `K`, the Weierstrass
formal group law makes its elements into `WeierstrassCurve.FormalGroupPoint W I`.  The usual
parametrisation sends zero to the point at infinity and, for a nonzero parameter, is given by

`t ↦ (t / w(t), -1 / w(t))`

This file proves that this map is an additive homomorphism into the points of the base-changed
curve whenever every parameter distinct from its inverse admits an auxiliary parameter distinct
from it, its inverse, and its own inverse.  It then establishes that property for the maximal ideal
in the completion at a height-one prime of a Dedekind domain, in every characteristic.

## Main definitions

* `WeierstrassCurve.formalPointHom`: the additive homomorphism from formal-group parameters in an
  adic ideal to points of the curve over a field.
* `WeierstrassCurve.formalPointHomAdicCompletion`: its specialization to the maximal ideal in an
  adic completion.

## Main results

* `WeierstrassCurve.formalPoint_add`: the parametrisation preserves addition when auxiliary
  parameters exist.
* `WeierstrassCurve.formalPoint_add_adicCompletion`: the unconditional adic-completion
  specialization.
* `WeierstrassCurve.formalPointHom_injective`: the resulting homomorphism is injective.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and VII.2.

## Provenance

Adapted from Michael Stoll's elliptic-curve development
(`github.com/MichaelStollBayreuth/EllipticCurves` @ `66889eada51a`, Apache-2.0), files
`EllipticCurves/WeierstrassFormalGroup/Foundations.lean` and
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declarations `exists_aux_param`,
`exists_aux_point`, `formalPoint_add_self` and `formalPoint_add`.  The source works with its own
multivariable formal-group points; here the argument is rebased onto
`WeierstrassCurve.FormalGroupPoint` and the one-dimensional formal-group API already in Mathlib and
Tau Ceti.
-/

public section

open IsDedekindDomain WithZero

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

local notation "O_v" => v.adicCompletionIntegers K
local notation "K_v" => v.adicCompletion K
local notation "m_v" => IsLocalRing.maximalIdeal O_v

local instance : IsLinearTopology O_v O_v :=
  v.isAdic_maximalIdeal_adicCompletionIntegers (K := K) ▸ Ideal.isLinearTopology m_v

local instance : Fact (IsAdic m_v) :=
  ⟨v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)⟩

variable (W : WeierstrassCurve (v.adicCompletionIntegers K))

private theorem valued_coe_isUnit {a : O_v} (ha : IsUnit a) :
    Valued.v (a : K_v) = 1 :=
  (Valuation.integer.integers
    (Valued.v : Valuation K_v (WithZero (Multiplicative ℤ)))).isUnit_iff_valuation_eq_one.mp ha

private theorem valued_formalInverseEval {t : O_v} (ht : t ∈ m_v) :
    Valued.v (W.formalInverseEval t : K_v) = Valued.v (t : K_v) := by
  have hE : PowerSeries.HasEval t :=
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)).isTopologicallyNilpotent_of_mem ht
  rw [WeierstrassCurve.formalInverseEval_eq W hE]
  push_cast
  rw [Valuation.map_neg, map_mul, valued_coe_isUnit v
      (WeierstrassCurve.isUnit_formalInverseDenomInvEval W hE), mul_one]

private theorem valued_formalWEval {t : O_v} (ht : t ∈ m_v) :
    Valued.v (W.formalWEval t : K_v) = Valued.v (t : K_v) ^ 3 := by
  have hE : PowerSeries.HasEval t :=
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)).isTopologicallyNilpotent_of_mem ht
  rw [WeierstrassCurve.formalWEval_eq_pow_mul_formalUEval W hE]
  push_cast
  rw [map_mul, map_pow, valued_coe_isUnit v
      (WeierstrassCurve.isUnit_formalUEval W
        (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)) ht), mul_one]

private theorem ne_of_valued_lt {a b : O_v}
    (h : Valued.v (a : K_v) < Valued.v (b : K_v)) : a ≠ b :=
  fun hab ↦ h.ne (by rw [hab])

private theorem eq_two_of_formalInverseEval_self {t : O_v} (ht : t ∈ m_v) (ht0 : t ≠ 0)
    (hfix : t = W.formalInverseEval t) :
    2 = W.a₁ * t + W.a₃ * W.formalWEval t := by
  have hE : PowerSeries.HasEval t :=
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)).isTopologicallyNilpotent_of_mem ht
  have h := WeierstrassCurve.formalInverseEval_mul_formalInverseDenomEval W hE
  rw [← hfix, WeierstrassCurve.formalInverseDenomEval_eq W hE] at h
  apply mul_left_cancel₀ ht0
  linear_combination h

private theorem ne_formalInverseEval_self {t : O_v} (ht : t ∈ m_v) (ht0 : t ≠ 0)
    (h2 : Valued.v (t : K_v) < Valued.v ((2 : O_v) : K_v)) :
    t ≠ W.formalInverseEval t := by
  intro hfix
  have hw_le : Valued.v (W.formalWEval t : K_v) ≤ Valued.v (t : K_v) := by
    rw [valued_formalWEval v W ht]
    calc
      Valued.v (t : K_v) ^ 3 = Valued.v (t : K_v) * Valued.v (t : K_v) ^ 2 :=
        pow_succ' _ 2
      _ ≤ Valued.v (t : K_v) * 1 :=
        mul_le_mul' le_rfl (pow_le_one' t.property 2)
      _ = Valued.v (t : K_v) := mul_one _
  have hcoe := congrArg (fun a : O_v ↦ (a : K_v))
    (eq_two_of_formalInverseEval_self v W ht ht0 hfix)
  push_cast at hcoe
  have hval : Valued.v ((2 : O_v) : K_v) ≤ Valued.v (t : K_v) := by
    rw [hcoe]
    refine (Valued.v.map_add _ _).trans (max_le ?_ ?_)
    · rw [map_mul]
      exact (mul_le_mul' W.a₁.property le_rfl).trans_eq (one_mul _)
    · rw [map_mul]
      exact (mul_le_mul' W.a₃.property hw_le).trans_eq (one_mul _)
  exact (not_le_of_gt h2) hval

private theorem exists_small_param {a b : O_v} (ha : a ∈ m_v) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ s : O_v, s ∈ m_v ∧ s ≠ 0 ∧ Valued.v (s : K_v) < Valued.v (a : K_v) ∧
      Valued.v (s : K_v) < Valued.v (b : K_v) ∧ Valued.v (s : K_v) < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O_v
  have hπv : Valued.v (π : K_v) = exp (-1) := by
    rw [← Algebra.algebraMap_ofSubsemiring_apply
      (Valued.v : Valuation K_v (WithZero (Multiplicative ℤ))).valuationSubring π]
    exact v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ
  have haval0 : Valued.v (a : K_v) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact ha0
  have hbval0 : Valued.v (b : K_v) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact hb0
  obtain ⟨n, hna, hnb⟩ := exists_exp_neg_natCast_lt_and_lt haval0 hbval0
  let s : O_v := π ^ n
  have hsv : Valued.v (s : K_v) = exp (-(n : ℤ)) := by
    simp only [s]
    push_cast
    rw [map_pow, hπv, ← exp_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have ha_le : Valued.v (a : K_v) ≤ exp (-1) := by
    apply (v.mem_maximalIdeal_pow_iff (K := K) (x := a) (n := 1)).mp
    simpa using ha
  have hsm : s ∈ m_v := by
    have h := v.mem_maximalIdeal_pow_iff (K := K) (x := s) (n := 1)
    rw [pow_one] at h
    apply h.mpr
    rw [hsv]
    exact (hna.trans_le ha_le).le
  have hs0 : s ≠ 0 := by
    exact pow_ne_zero _ hπ.ne_zero
  refine ⟨s, hsm, hs0, ?_, ?_, ?_⟩
  · rwa [hsv]
  · rwa [hsv]
  · rw [hsv, ← exp_zero, exp_lt_exp]
    exact (exp_lt_exp.mp (hna.trans_le ha_le)).trans_le (by omega)

private theorem exists_aux_param [(W.baseChange K_v).IsElliptic] {t : O_v}
    (ht : t ∈ m_v) (ht0 : t ≠ 0) :
    ∃ s : O_v, s ∈ m_v ∧ s ≠ 0 ∧ s ≠ t ∧ s ≠ W.formalInverseEval t ∧
      s ≠ W.formalInverseEval s := by
  by_cases htwo : (2 : K_v) = 0
  -- In characteristic two, ellipticity forces at least one of `a₁` and `a₃` to be nonzero.
  -- A sufficiently small parameter then cannot satisfy the formal-inverse fixed-point equation.
  · let _ : CharP K_v 2 :=
      (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 htwo
    have htwo' : ((2 : O_v) : K_v) = 0 := by
      calc
        ((2 : O_v) : K_v) = algebraMap O_v K_v (2 : O_v) :=
          (Algebra.algebraMap_ofSubsemiring_apply
            (Valued.v : Valuation K_v (WithZero (Multiplicative ℤ))).valuationSubring _).symm
        _ = (2 : K_v) := map_ofNat (algebraMap O_v K_v) 2
        _ = 0 := htwo
    have ha₁a₃ : (W.a₁ : K_v) ≠ 0 ∨ (W.a₃ : K_v) ≠ 0 := by
      by_contra h
      push Not at h
      have hΔ : (W.baseChange K_v).Δ = 0 := by
        rw [(W.baseChange K_v).Δ_of_char_two]
        simp [h.1, h.2]
      exact (W.baseChange K_v).isUnit_Δ.ne_zero hΔ
    by_cases ha₁ : (W.a₁ : K_v) = 0
    · have ha₃ := ha₁a₃.resolve_left (fun h ↦ h ha₁)
      have ha₃O : W.a₃ ≠ 0 := fun h ↦ ha₃ (by simp [h])
      obtain ⟨s, hsm, hs0, hst, _, _⟩ := exists_small_param v ht ht0 ha₃O
      refine ⟨s, hsm, hs0, ne_of_valued_lt v hst,
        ne_of_valued_lt v (valued_formalInverseEval v W ht ▸ hst), ?_⟩
      intro hfix
      have hcoe := congrArg (fun a : O_v ↦ (a : K_v))
        (eq_two_of_formalInverseEval_self v W hsm hs0 hfix)
      push_cast at hcoe
      rw [htwo', ha₁, zero_mul, zero_add] at hcoe
      have hw0 : (W.formalWEval s : K_v) ≠ 0 :=
        W.algebraMap_formalWEval_ne_zero (Fact.out : IsAdic m_v) hsm
          ((FaithfulSMul.algebraMap_injective O_v K_v).ne hs0)
      exact (mul_ne_zero ha₃ hw0) hcoe.symm
    · have ha₁O : W.a₁ ≠ 0 := fun h ↦ ha₁ (by simp [h])
      obtain ⟨s, hsm, hs0, hst, hsa₁, hsone⟩ :=
        exists_small_param v ht ht0 ha₁O
      refine ⟨s, hsm, hs0, ne_of_valued_lt v hst,
        ne_of_valued_lt v (valued_formalInverseEval v W ht ▸ hst), ?_⟩
      intro hfix
      have hcoe := congrArg (fun a : O_v ↦ (a : K_v))
        (eq_two_of_formalInverseEval_self v W hsm hs0 hfix)
      push_cast at hcoe
      rw [htwo'] at hcoe
      have hsval0 : Valued.v (s : K_v) ≠ 0 := by
        exact (_root_.map_eq_zero (Valued.v :
          Valuation K_v (WithZero (Multiplicative ℤ)))).not.mpr
            (fun h ↦ hs0 (ZeroMemClass.coe_eq_zero.mp h))
      have hsq : Valued.v (s : K_v) ^ 2 < Valued.v (W.a₁ : K_v) := by
        calc
          Valued.v (s : K_v) ^ 2 = Valued.v (s : K_v) * Valued.v (s : K_v) :=
            pow_two _
          _ < 1 * Valued.v (s : K_v) :=
            mul_lt_mul_of_pos_right hsone (pos_iff_ne_zero.mpr hsval0)
          _ = Valued.v (s : K_v) := one_mul _
          _ < Valued.v (W.a₁ : K_v) := hsa₁
      have hw_le : Valued.v (W.a₃ * W.formalWEval s : K_v) ≤
          Valued.v (s : K_v) ^ 3 := by
        rw [map_mul, valued_formalWEval v W hsm]
        exact (mul_le_mul' W.a₃.property le_rfl).trans_eq (one_mul _)
      have hval : Valued.v (W.a₃ * W.formalWEval s : K_v) <
          Valued.v (W.a₁ * s : K_v) := hw_le.trans_lt (by
        rw [map_mul, pow_succ]
        exact mul_lt_mul_of_pos_right hsq (pos_iff_ne_zero.mpr hsval0))
      have heq : (W.a₁ * s : K_v) = -(W.a₃ * W.formalWEval s : K_v) :=
        eq_neg_of_add_eq_zero_left hcoe.symm
      exact hval.ne (by rw [heq, Valuation.map_neg])
  · have htwoO : (2 : O_v) ≠ 0 := fun h ↦ htwo (by
      calc
        (2 : K_v) = algebraMap O_v K_v (2 : O_v) :=
          (map_ofNat (algebraMap O_v K_v) 2).symm
        _ = ((2 : O_v) : K_v) := Algebra.algebraMap_ofSubsemiring_apply
          (Valued.v : Valuation K_v (WithZero (Multiplicative ℤ))).valuationSubring _
        _ = 0 := congrArg (fun a : O_v ↦ (a : K_v)) h)
    obtain ⟨s, hsm, hs0, hst, hs2, _⟩ := exists_small_param v ht ht0 htwoO
    refine ⟨s, hsm, hs0, ne_of_valued_lt v hst,
      ne_of_valued_lt v (valued_formalInverseEval v W ht ▸ hst),
      ne_formalInverseEval_self v W hsm hs0 hs2⟩

private theorem exists_aux_point [(W.baseChange K_v).IsElliptic]
    {P : FormalGroupPoint W m_v} (hP0 : P ≠ 0) :
    ∃ U : FormalGroupPoint W m_v, U ≠ 0 ∧ U ≠ P ∧ U ≠ -P ∧ -U ≠ P ∧
      -U ≠ -P ∧ U ≠ -U := by
  have hPval0 : P.val ≠ 0 := fun h ↦ hP0 (FormalGroupPoint.ext (by simpa using h))
  obtain ⟨u, hu, hu0, huP, huInvP, huInv⟩ := exists_aux_param v W P.property hPval0
  let U : FormalGroupPoint W m_v := ⟨u, hu⟩
  refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h ↦ hu0 (congrArg FormalGroupPoint.val h)
  · exact fun h ↦ huP (congrArg FormalGroupPoint.val h)
  · exact fun h ↦ huInvP (by simpa [U] using congrArg FormalGroupPoint.val h)
  · intro h
    apply huInvP
    simpa [U] using congrArg FormalGroupPoint.val (congrArg Neg.neg h)
  · intro h
    apply huP
    simpa [U] using congrArg FormalGroupPoint.val (neg_injective h)
  · exact fun h ↦ huInv (by simpa [U] using congrArg FormalGroupPoint.val h)

section PointMap

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {S : Type*} [Field S] [Algebra O S] [FaithfulSMul O S]
  (I : Ideal O) [Fact (IsAdic I)] (E : WeierstrassCurve O) [(E.baseChange S).IsElliptic]

private noncomputable def formalPointMap (P : FormalGroupPoint E I) :
    (E.baseChange S).toAffine.Point :=
  E.formalPoint (K := S) (Fact.out : IsAdic I) P.property

private theorem formalPointMap_injective :
    Function.Injective (formalPointMap (S := S) I E) := by
  intro P Q hPQ
  have hPQ' : E.formalPoint (K := S) (Fact.out : IsAdic I) P.property =
      E.formalPoint (K := S) (Fact.out : IsAdic I) Q.property := by
    simpa only [formalPointMap] using hPQ
  have hinj := E.formalPoint_injective (K := S) (Fact.out : IsAdic I)
  have heq := hinj (a₁ := (⟨P.val, P.property⟩ : I))
    (a₂ := (⟨Q.val, Q.property⟩ : I)) hPQ'
  exact FormalGroupPoint.ext (congrArg Subtype.val heq)

private theorem formalPointMap_neg (P : FormalGroupPoint E I) :
    formalPointMap (S := S) I E (-P) = -formalPointMap (S := S) I E P := by
  simp only [formalPointMap, FormalGroupPoint.coe_neg]
  exact E.formalPoint_formalInverseEval (Fact.out : IsAdic I) P.property

open Classical in
private theorem formalPointMap_add_of_ne (P Q : FormalGroupPoint E I)
    (hne : Q ≠ P) (hnneg : Q ≠ -P) :
    formalPointMap (S := S) I E (P + Q) =
      formalPointMap (S := S) I E P + formalPointMap (S := S) I E Q := by
  exact (E.add_eq_formalPoint_formalAddEval_of_ne_of_ne_formalInverseEval
    (K := S) (Fact.out : IsAdic I) P.property Q.property
    (fun _ _ h ↦ hne (FormalGroupPoint.ext h))
    (fun _ _ h ↦ hnneg (FormalGroupPoint.ext (by simpa using h)))).symm

open Classical in
private theorem formalPointMap_add_self (P : FormalGroupPoint E I) (hself : P ≠ -P)
    (haux : ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U) :
    formalPointMap (S := S) I E (P + P) =
      formalPointMap (S := S) I E P + formalPointMap (S := S) I E P := by
  obtain ⟨U, hUP, hUnP, hUnegn⟩ := haux
  have hnUP : -U ≠ P := fun h ↦ hUnP (by simpa using congrArg Neg.neg h)
  have hnUnP : -U ≠ -P := fun h ↦ hUP (neg_injective h)
  have c1 := formalPointMap_add_of_ne (S := S) I E P U hUP hUnP
  have c2 := formalPointMap_add_of_ne (S := S) I E P (-U) hnUP hnUnP
  have hne : P + -U ≠ P + U := by
    intro h
    have h' := congrArg (formalPointMap (S := S) I E) h
    rw [c1, c2] at h'
    exact hUnegn (formalPointMap_injective (S := S) I E (add_left_cancel h').symm)
  have hnneg : P + -U ≠ -(P + U) := by
    intro h
    have h' := congrArg (formalPointMap (S := S) I E) h
    rw [c2, formalPointMap_neg (S := S) I E, formalPointMap_neg (S := S) I E,
      c1, neg_add] at h'
    have h'' := add_right_cancel h'
    rw [← formalPointMap_neg (S := S) I E] at h''
    exact hself (formalPointMap_injective (S := S) I E h'')
  have c3 := formalPointMap_add_of_ne (S := S) I E (P + U) (P + -U) hne hnneg
  have hkey : (P + U) + (P + -U) = P + P := by abel
  rw [← hkey, c3, c1, c2, formalPointMap_neg (S := S) I E]
  abel

open Classical in
/-- **The formal parametrisation preserves addition** whenever every parameter distinct from its
inverse has an auxiliary parameter distinct from it, its inverse, and the auxiliary parameter's
own inverse. -/
theorem formalPoint_add
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U)
    (P Q : FormalGroupPoint E I) :
    E.formalPoint (K := S) (Fact.out : IsAdic I) (P + Q).property =
      E.formalPoint (K := S) (Fact.out : IsAdic I) P.property +
        E.formalPoint (K := S) (Fact.out : IsAdic I) Q.property := by
  suffices h : formalPointMap (S := S) I E (P + Q) =
      formalPointMap (S := S) I E P + formalPointMap (S := S) I E Q by
    simpa only [formalPointMap] using h
  rcases eq_or_ne P 0 with rfl | hP0
  · simp [formalPointMap]
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp [formalPointMap]
  rcases eq_or_ne Q (-P) with rfl | hQneg
  · rw [add_neg_cancel, formalPointMap_neg (S := S) I E]
    simp [formalPointMap]
  rcases eq_or_ne Q P with hQP | hQP
  · subst Q
    exact formalPointMap_add_self (S := S) I E P hQneg (haux P hQneg)
  · exact formalPointMap_add_of_ne (S := S) I E P Q hQP hQneg

open Classical in
/-- **The formal parameter map into the curve's points**, as an additive homomorphism whenever
the required auxiliary parameters exist. -/
noncomputable def formalPointHom
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U) :
    FormalGroupPoint E I →+ (E.baseChange S).toAffine.Point where
  toFun := formalPointMap (S := S) I E
  map_zero' := by simp [formalPointMap]
  map_add' := formalPoint_add I E haux

open Classical in
/-- The formal point homomorphism evaluates to the usual formal parametrisation. -/
@[simp]
theorem formalPointHom_apply
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U)
    (P : FormalGroupPoint E I) :
    E.formalPointHom I haux P =
      E.formalPoint (K := S) (Fact.out : IsAdic I) P.property :=
  (rfl)

open Classical in
/-- **The formal point homomorphism is injective.** -/
theorem formalPointHom_injective
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U) :
    Function.Injective (E.formalPointHom (S := S) I haux) :=
  formalPointMap_injective (S := S) I E

end PointMap

section AdicCompletion

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

private theorem exists_aux_point_simple
    {P : FormalGroupPoint C (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F))}
    (hPneg : P ≠ -P) :
    ∃ U : FormalGroupPoint C (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F)),
      U ≠ P ∧ U ≠ -P ∧ U ≠ -U := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hPneg (by simp)
  obtain ⟨U, _, hUP, hUnP, _, _, hUnegn⟩ := exists_aux_point u C hP0
  exact ⟨U, hUP, hUnP, hUnegn⟩

open Classical in
/-- **The formal parametrisation preserves addition in an adic completion.** -/
@[simp]
theorem formalPoint_add_adicCompletion
    (P Q : FormalGroupPoint C (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F))) :
    C.formalPoint (K := u.adicCompletion F)
        (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F))
        (P + Q).property =
      C.formalPoint (K := u.adicCompletion F)
          (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F))
          P.property +
        C.formalPoint (K := u.adicCompletion F)
          (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F))
          Q.property :=
  formalPoint_add (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F)) C
    (fun P hP ↦ exists_aux_point_simple u C (P := P) hP) P Q

open Classical in
/-- **The formal parameter map for an adic completion**, as an additive homomorphism. -/
noncomputable def formalPointHomAdicCompletion :
    FormalGroupPoint C (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F)) →+
      (C.baseChange (u.adicCompletion F)).toAffine.Point :=
  C.formalPointHom (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F))
    (fun P hP ↦ exists_aux_point_simple u C (P := P) hP)

open Classical in
/-- The adic-completion formal point homomorphism evaluates to the usual parametrisation. -/
@[simp]
theorem formalPointHomAdicCompletion_apply
    (P : FormalGroupPoint C (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F))) :
    C.formalPointHomAdicCompletion u P =
      C.formalPoint (K := u.adicCompletion F)
        (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) P.property :=
  (rfl)

open Classical in
/-- **The adic-completion formal point homomorphism is injective.** -/
theorem formalPointHomAdicCompletion_injective :
    Function.Injective (C.formalPointHomAdicCompletion u) :=
  formalPointHom_injective (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F)) C
    (fun P hP ↦ exists_aux_point_simple u C (P := P) hP)

end AdicCompletion

end WeierstrassCurve

end
