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

For a height-one prime `v` of a Dedekind domain, the maximal ideal of the ring of integers
`O_v` of the completion is an adic ideal.  The Weierstrass formal group law therefore makes its
elements into `WeierstrassCurve.FormalGroupPoint W m_v`.  The usual parametrisation sends zero to
the point at infinity and, for a nonzero parameter, is given by

`t ↦ (t / w(t), -1 / w(t))`

This file proves that this map is an additive homomorphism into the points of the base-changed
curve, in every characteristic.

## Main definitions

* `WeierstrassCurve.formalPointHom`: the additive homomorphism from formal-group parameters in the
  maximal ideal of `O_v` to points of the curve over the completion.

## Main results

* `WeierstrassCurve.formalPoint_add`: the parametrisation preserves addition.
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
  obtain ⟨i, hi⟩ : ∃ i : ℤ, Valued.v (a : K_v) = exp i :=
    ⟨_, (exp_log haval0).symm⟩
  have hi_le : i ≤ -1 := by
    have h := v.mem_maximalIdeal_pow_iff (K := K) (n := 1) |>.mp (pow_one m_v ▸ ha)
    rwa [hi, exp_le_exp] at h
  have hbval0 : Valued.v (b : K_v) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact hb0
  obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v (b : K_v) = exp j :=
    ⟨_, (exp_log hbval0).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = max (-i) (-j) + 1 :=
    ⟨(max (-i) (-j) + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  let s : O_v := π ^ n
  have hsv : Valued.v (s : K_v) = exp (-(n : ℤ)) := by
    simp only [s]
    push_cast
    rw [map_pow, hπv, ← exp_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have hni : -(n : ℤ) < i := by omega
  have hnj : -(n : ℤ) < j := by omega
  have hsm : s ∈ m_v := by
    have h := v.mem_maximalIdeal_pow_iff (K := K) (x := s) (n := 1)
    rw [pow_one] at h
    apply h.mpr
    rw [hsv, exp_le_exp]
    omega
  have hs0 : s ≠ 0 := by
    exact pow_ne_zero _ hπ.ne_zero
  refine ⟨s, hsm, hs0, ?_, ?_, ?_⟩
  · rw [hsv, hi, exp_lt_exp]
    exact hni
  · rw [hsv, hj, exp_lt_exp]
    exact hnj
  · rw [hsv, ← exp_zero, exp_lt_exp]
    omega

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

variable [(W.baseChange (v.adicCompletion K)).IsElliptic]

private noncomputable def formalPointMap (P : FormalGroupPoint W m_v) :
    (W.baseChange K_v).toAffine.Point :=
  W.formalPoint (K := K_v) (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)) P.property

private theorem formalPointMap_injective : Function.Injective (formalPointMap v W) := by
  intro P Q hPQ
  have hPQ' : W.formalPoint (K := K_v)
      (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)) P.property =
        W.formalPoint (K := K_v)
          (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)) Q.property := by
    simpa only [formalPointMap] using hPQ
  have hinj := W.formalPoint_injective (K := K_v)
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K))
  have heq := hinj (a₁ := (⟨P.val, P.property⟩ : m_v))
    (a₂ := (⟨Q.val, Q.property⟩ : m_v)) hPQ'
  exact FormalGroupPoint.ext (congrArg Subtype.val heq)

private theorem formalPointMap_neg (P : FormalGroupPoint W m_v) :
    formalPointMap v W (-P) = -formalPointMap v W P := by
  let hI := v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)
  simp only [formalPointMap, FormalGroupPoint.coe_neg]
  exact W.formalPoint_formalInverseEval hI P.property

open Classical in
private theorem formalPointMap_add_of_ne (P Q : FormalGroupPoint W m_v)
    (hne : Q ≠ P) (hnneg : Q ≠ -P) :
    formalPointMap v W (P + Q) = formalPointMap v W P + formalPointMap v W Q := by
  exact (W.add_eq_formalPoint_formalAddEval_of_ne_of_ne_formalInverseEval
    (K := K_v) (Fact.out : IsAdic m_v) P.property Q.property
    (fun _ _ h ↦ hne (FormalGroupPoint.ext h))
    (fun _ _ h ↦ hnneg (FormalGroupPoint.ext (by simpa using h)))).symm

open Classical in
private theorem formalPointMap_add_self (P : FormalGroupPoint W m_v) (hP0 : P ≠ 0)
    (hself : P ≠ -P) :
    formalPointMap v W (P + P) = formalPointMap v W P + formalPointMap v W P := by
  obtain ⟨U, _, hUP, hUnP, hnUP, hnUnP, hUnegn⟩ := exists_aux_point v W hP0
  have c1 := formalPointMap_add_of_ne v W P U hUP hUnP
  have c2 := formalPointMap_add_of_ne v W P (-U) hnUP hnUnP
  have hne : P + -U ≠ P + U := by
    intro h
    have h' := congrArg (formalPointMap v W) h
    rw [c1, c2] at h'
    exact hUnegn (formalPointMap_injective v W (add_left_cancel h').symm)
  have hnneg : P + -U ≠ -(P + U) := by
    intro h
    have h' := congrArg (formalPointMap v W) h
    rw [c2, formalPointMap_neg v W, formalPointMap_neg v W, c1, neg_add] at h'
    have h'' := add_right_cancel h'
    rw [← formalPointMap_neg v W] at h''
    exact hself (formalPointMap_injective v W h'')
  have c3 := formalPointMap_add_of_ne v W (P + U) (P + -U) hne hnneg
  have hkey : (P + U) + (P + -U) = P + P := by abel
  rw [← hkey, c3, c1, c2, formalPointMap_neg v W]
  abel

open Classical in
/-- **The formal parametrisation preserves addition.** -/
@[simp]
theorem formalPoint_add (P Q : FormalGroupPoint W m_v) :
    W.formalPoint (K := K_v) (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K))
        (P + Q).property =
      W.formalPoint (K := K_v) (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K))
          P.property +
        W.formalPoint (K := K_v) (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K))
          Q.property := by
  suffices h : formalPointMap v W (P + Q) =
      formalPointMap v W P + formalPointMap v W Q by
    simpa only [formalPointMap] using h
  rcases eq_or_ne P 0 with rfl | hP0
  · simp [formalPointMap]
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp [formalPointMap]
  rcases eq_or_ne Q (-P) with rfl | hQneg
  · rw [add_neg_cancel, formalPointMap_neg v W]
    simp [formalPointMap]
  rcases eq_or_ne Q P with hQP | hQP
  · subst Q
    exact formalPointMap_add_self v W P hP0 hQneg
  · exact formalPointMap_add_of_ne v W P Q hQP hQneg

open Classical in
/-- **The formal parameter map into the curve's points**, as an additive homomorphism. -/
noncomputable def formalPointHom :
    FormalGroupPoint W m_v →+ (W.baseChange K_v).toAffine.Point where
  toFun := formalPointMap v W
  map_zero' := by simp [formalPointMap]
  map_add' := formalPoint_add v W

open Classical in
/-- The formal point homomorphism evaluates to the usual formal parametrisation. -/
@[simp]
theorem formalPointHom_apply (P : FormalGroupPoint W m_v) :
    W.formalPointHom v P =
      W.formalPoint (K := K_v) (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)) P.property :=
  (rfl)

open Classical in
/-- **The formal point homomorphism is injective.** -/
theorem formalPointHom_injective : Function.Injective (W.formalPointHom v) :=
  formalPointMap_injective v W

end PointMap

end WeierstrassCurve

end
