/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Hom
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Formal points over a Dedekind adic completion

For a Weierstrass curve over the ring of integers `O_v` in the completion of a Dedekind domain at
a height-one prime, the maximal ideal has enough auxiliary parameters to apply the generic formal
point homomorphism construction. This file packages the resulting unconditional additive and
injective map from the formal group on that maximal ideal into the points over the completion. It
is the discrete adic-completion specialization; the generic construction, conditional on the
existence of auxiliary parameters, is in `Point.Hom`.

## Main definitions

* `WeierstrassCurve.formalPointHomAdicCompletion`: the additive homomorphism from formal-group
  parameters in the maximal ideal of `O_v` to points over the completion.

## Main results

* `WeierstrassCurve.formalPoint_add_adicCompletion`: the parametrisation preserves addition.
* `WeierstrassCurve.formalPointHomAdicCompletion_injective`: the homomorphism is injective.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and VII.2.

## Provenance

Adapted from Michael Stoll's elliptic-curve development
(`github.com/MichaelStollBayreuth/EllipticCurves` @ `66889eada51a`, Apache-2.0), files
`EllipticCurves/WeierstrassFormalGroup/Foundations.lean` and
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declarations `exists_aux_param`,
`exists_aux_point`, `formalPoint_add_self` and `formalPoint_add`. The source works with its own
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
      obtain ⟨s, hsm, hs0, hst, _, _⟩ :=
        v.exists_ne_zero_mem_maximalIdeal_valued_lt ht0 ha₃O
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
        v.exists_ne_zero_mem_maximalIdeal_valued_lt ht0 ha₁O
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
    obtain ⟨s, hsm, hs0, hst, hs2, _⟩ :=
      v.exists_ne_zero_mem_maximalIdeal_valued_lt ht0 htwoO
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
  formalPointHom_apply (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F)) C
    (fun P hP ↦ exists_aux_point_simple u C (P := P) hP) P

open Classical in
/-- **The adic-completion formal point homomorphism is injective.** -/
theorem formalPointHomAdicCompletion_injective :
    Function.Injective (C.formalPointHomAdicCompletion u) :=
  formalPointHom_injective (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F)) C
    (fun P hP ↦ exists_aux_point_simple u C (P := P) hP)

end AdicCompletion

end WeierstrassCurve

end
