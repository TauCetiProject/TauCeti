/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Rat.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
public import TauCeti.RingTheory.CohenMacaulay.TrivSqZeroExt
import TauCeti.RingTheory.Ideal.OfList
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
public import TauCeti.RingTheory.Secant.CohenMacaulay

/-!
# Examples of annihilator products, secant, CM-secant, and `p`-standard sequences

This file checks concrete nontrivial instances of `localCohomology.annihilatorProduct`,
`RingTheory.Sequence.IsSecant`, `RingTheory.Sequence.IsCMSecant`, and
`RingTheory.Sequence.IsPStandard`:

* the zero module (`PUnit`): only `[]` is secant, CM-secant, and `p`-standard, and every annihilator
  product is `⊤`;
* the field `ℚ`: `[]` is secant, CM-secant, and `p`-standard, while `[0]` and `[1]` are not secant;
* prefix quotients over `ℤ`: `ℤ ⧸ []`, `ℤ ⧸ [2]` (nonzero), and `ℤ ⧸ [2, 3]` (zero);
* the one-dimensional DVR `k⟦X⟧`: `[X]` and `[X ^ 2]` are secant, CM-secant, and `p`-standard,
  while `[X, X]` and `[1]` are not secant;
* `k⟦X⟧ ⧸ (X ^ 2)`: the cutoff-one annihilator product is `(X ^ 2)` exactly, strictly smaller than
  its radical `(X)`;
* the two-dimensional regular local ring `k⟦X⟧⟦X⟧`: `[C X, X]` is CM-secant and its reversal
  `[X, C X]` is `p`-standard; `[C X * X]` is secant, whereas `[C X * X, X]` is not;
* the one-dimensional non-Cohen–Macaulay local ring `S = TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ 𝔪)`
  (algebraically `k⟦x, y⟧ ⧸ (x², xy)`): `[]` is not CM-secant,
  `annihilatorProduct (maximalIdeal S) S 1 = maximalIdeal S ≠ ⊤`, and `inl X` is not regular on `S`,
  yet `[inl X]` and `[inl X + inr 1]` are secant, CM-secant, and `p`-standard.
-/

open IsLocalRing RingTheory.Sequence Pointwise

section ZeroModule

variable {R : Type*} [CommRing R] [IsLocalRing R]

example (r : R) :
    IsSecant (PUnit : Type _) ([] : List R) ∧ ¬ IsSecant (PUnit : Type _) [r] :=
  ⟨isSecant_nil, fun h ↦ by
    have := isSecant_iff_eq_nil_of_subsingleton.mp h
    simp at this⟩

example (R : Type u) [CommRing R] [IsLocalRing R] (r : R) :
    IsCMSecant (R := R) (PUnit : Type u) ([] : List R) ∧
      ¬ IsCMSecant (R := R) (PUnit : Type u) [r] ∧
      IsPStandard (R := R) (PUnit : Type u) ([] : List R) ∧
      ¬ IsPStandard (R := R) (PUnit : Type u) [r] :=
  ⟨isCMSecant_iff_eq_nil_of_subsingleton.mpr rfl,
    fun h ↦ by simp [isCMSecant_iff_eq_nil_of_subsingleton] at h,
    isPStandard_iff_eq_nil_of_subsingleton.mpr rfl,
    fun h ↦ by simp [isPStandard_iff_eq_nil_of_subsingleton] at h⟩

example (R : Type u) [CommRing R] (J : Ideal R) (d : ℕ) :
    localCohomology.annihilatorProduct J (PUnit : Type u) d = ⊤ :=
  localCohomology.annihilatorProduct_of_subsingleton J PUnit d

end ZeroModule

section Field

example :
    IsSecant ℚ ([] : List ℚ) ∧
      ¬ IsSecant ℚ ([0] : List ℚ) ∧
      ¬ IsSecant ℚ ([1] : List ℚ) := by
  refine ⟨isSecant_nil, fun h ↦ ?_, fun h ↦ ?_⟩
  · have hlen := h.length_le_supportDim
    rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq_zero_of_isField (Field.toIsField ℚ)]
      at hlen
    exact absurd hlen (by norm_cast)
  · exact (notMem_maximalIdeal.mpr isUnit_one) (h.mem_maximalIdeal List.mem_cons_self)

example :
    IsCMSecant ℚ ([] : List ℚ) ∧
      ¬ IsCMSecant ℚ ([0] : List ℚ) ∧
      IsPStandard ℚ ([] : List ℚ) := by
  refine ⟨isCMSecant_nil_iff.mpr Module.isCohenMacaulay_of_krullDimLE_zero, fun h ↦ ?_, ?_⟩
  · have hlen := h.isSecant.length_le_supportDim
    rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq_zero_of_isField (Field.toIsField ℚ)]
      at hlen
    exact absurd hlen (by norm_cast)
  · rw [isPStandard_nil_iff, Module.supportDim_self_eq_ringKrullDim,
      ringKrullDim_eq_zero_of_isField (Field.toIsField ℚ)]

end Field

section PrefixQuotientsInt

example : Nontrivial (ℤ ⧸ Ideal.ofList ([] : List ℤ) • (⊤ : Submodule ℤ ℤ)) :=
  (Submodule.quotOfListNilSMulTopEquiv ℤ ℤ).toEquiv.nontrivial_congr.mpr inferInstance

example : Nontrivial (ℤ ⧸ Ideal.ofList ([2] : List ℤ) • (⊤ : Submodule ℤ ℤ)) := by
  refine Submodule.Quotient.nontrivial_iff.mpr fun h ↦ ?_
  have h1 : (1 : ℤ) ∈ Ideal.ofList ([2] : List ℤ) • (⊤ : Submodule ℤ ℤ) := by
    rw [h]; exact Submodule.mem_top
  rw [Ideal.ofList_singleton, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton] at h1
  omega

example : Subsingleton (ℤ ⧸ Ideal.ofList ([2, 3] : List ℤ) • (⊤ : Submodule ℤ ℤ)) := by
  refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ ↦ ?_)
  have htop : Ideal.ofList ([2, 3] : List ℤ) = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    have h2 : (2 : ℤ) ∈ Ideal.ofList [2, 3] := Ideal.subset_span (by simp)
    have h3 : (3 : ℤ) ∈ Ideal.ofList [2, 3] := Ideal.subset_span (by simp)
    simpa using sub_mem h3 h2
  rw [htop, Submodule.top_smul]
  exact Submodule.mem_top

end PrefixQuotientsInt

section OneDimPowerSeries

open _root_.PowerSeries

variable (k : Type u) [Field k]

example :
    IsSecant k⟦X⟧ ([X] : List k⟦X⟧) ∧
      IsSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) ∧
      ¬ IsSecant k⟦X⟧ ([X, X] : List k⟦X⟧) ∧
      ¬ IsSecant k⟦X⟧ ([1] : List k⟦X⟧) ∧
      IsCMSecant k⟦X⟧ ([X] : List k⟦X⟧) ∧
      IsCMSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) ∧
      IsPStandard k⟦X⟧ ([X] : List k⟦X⟧) ∧
      IsPStandard k⟦X⟧ ([X ^ 2] : List k⟦X⟧) := by
  have hcm : Module.IsCohenMacaulay k⟦X⟧ k⟦X⟧ := TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hdim : Module.supportDim k⟦X⟧ k⟦X⟧ = 1 := by
    rw [Module.supportDim_self_eq_ringKrullDim, IsDiscreteValuationRing.ringKrullDim_eq_one]
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ := by
    rw [maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  have hreg_x : IsRegular k⟦X⟧ ([X] : List k⟦X⟧) := by
    refine hcm.isRegular_of_le_radical (by simpa using hx_mem) ?_ ?_
    · rw [Ideal.ofList_singleton, maximalIdeal_eq_span_X]
      exact le_sup_left.trans Ideal.le_radical
    · simp [hdim]
  have hsec_x : IsSecant k⟦X⟧ ([X] : List k⟦X⟧) := hreg_x.isSecant
  have hsec_x2 : IsSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) :=
    hsec_x.set_pow (i := 0) (by simp) (by omega)
  have hdim_x :
      Module.supportDim k⟦X⟧ (k⟦X⟧ ⧸ Ideal.ofList ([X] : List k⟦X⟧) • (⊤ : Submodule k⟦X⟧ k⟦X⟧)) =
        0 := by
    have h := hsec_x.supportDim_add_length_eq
    rw [hdim] at h
    exact ENat.WithBot.add_one_cancel.mp (by simpa using h)
  have hdim_x2 :
      Module.supportDim k⟦X⟧
          (k⟦X⟧ ⧸ Ideal.ofList ([X ^ 2] : List k⟦X⟧) • (⊤ : Submodule k⟦X⟧ k⟦X⟧)) = 0 := by
    have h := hsec_x2.supportDim_add_length_eq
    rw [hdim] at h
    exact ENat.WithBot.add_one_cancel.mp (by simpa using h)
  refine ⟨hsec_x, hsec_x2, fun hxx ↦ ?_, fun h1 ↦ ?_,
    hcm.isCMSecant_of_isSecant hsec_x, hcm.isCMSecant_of_isSecant hsec_x2, ?_, ?_⟩
  · have hlen := hxx.length_le_supportDim
    rw [hdim] at hlen
    exact absurd hlen (by norm_cast)
  · exact (notMem_maximalIdeal.mpr isUnit_one) (h1.mem_maximalIdeal List.mem_cons_self)
  · exact (isCMSecant_iff_isPStandard_reverse hdim_x.le).mp (hcm.isCMSecant_of_isSecant hsec_x)
  · exact (isCMSecant_iff_isPStandard_reverse hdim_x2.le).mp (hcm.isCMSecant_of_isSecant hsec_x2)

/-- Cutoff-one exactness: for `R = k⟦X⟧` and `M = R ⧸ (X²)`, `a_𝔪(M, 1) = (X²)` (not its radical
`(X)`). -/
example :
    localCohomology.annihilatorProduct (maximalIdeal k⟦X⟧) (k⟦X⟧ ⧸ Ideal.span {(X : k⟦X⟧) ^ 2}) 1 =
        Ideal.span {X ^ 2} ∧
      (X : k⟦X⟧) ∉
        localCohomology.annihilatorProduct (maximalIdeal k⟦X⟧)
          (k⟦X⟧ ⧸ Ideal.span {(X : k⟦X⟧) ^ 2}) 1 := by
  set I : Ideal k⟦X⟧ := Ideal.span {(X : k⟦X⟧) ^ 2}
  have hprim : (maximalIdeal k⟦X⟧).primaryComponent (k⟦X⟧ ⧸ I) = ⊤ := by
    refine eq_top_iff.mpr fun m _ ↦ ?_
    rw [Ideal.primaryComponent_mem]
    refine ⟨2, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    rw [maximalIdeal_eq_span_X, Ideal.span_singleton_pow] at ha
    induction m using Submodule.Quotient.induction_on with | H r =>
      change Ideal.Quotient.mk I (a * r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right r I ha
  have heq : localCohomology.annihilatorProduct (maximalIdeal k⟦X⟧) (k⟦X⟧ ⧸ I) 1 = I := by
    rw [localCohomology.annihilatorProduct_one_eq_annihilator_primaryComponent, hprim]
    exact (Submodule.topEquiv (R := k⟦X⟧) (M := k⟦X⟧ ⧸ I)).annihilator_eq.trans
      Ideal.annihilator_quotient
  refine ⟨heq, fun hx ↦ ?_⟩
  rw [heq, Ideal.mem_span_singleton] at hx
  obtain ⟨q, hq⟩ := hx
  have hunit : IsUnit (X : k⟦X⟧) := isUnit_iff_exists_inv.mpr ⟨q, by
    refine mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k)) ?_
    rw [mul_one, ← mul_assoc, ← sq, ← hq]⟩
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ := by
    rw [maximalIdeal_eq_span_X]; exact Ideal.subset_span rfl
  exact (notMem_maximalIdeal.mpr hunit) hx_mem

end OneDimPowerSeries

section TwoDimPowerSeries

open _root_.PowerSeries

variable (k : Type u) [Field k]

example :
    IsCMSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) ∧
      IsPStandard k⟦X⟧⟦X⟧ ([X, C X] : List k⟦X⟧⟦X⟧) ∧
      IsSecant k⟦X⟧⟦X⟧ ([C X * X] : List k⟦X⟧⟦X⟧) ∧
      ¬ IsSecant k⟦X⟧⟦X⟧ ([C X * X, X] : List k⟦X⟧⟦X⟧) := by
  have hcm : Module.IsCohenMacaulay k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ := TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hdim : Module.supportDim k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ = 2 := by
    rw [Module.supportDim_self_eq_ringKrullDim,
      TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing]
  have hmax : maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} :=
    TauCeti.PowerSeries.maximalIdeal_eq_span_C_X irreducible_X
  have hcx_mem : (C X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := by
    rw [hmax]; exact Ideal.subset_span (by simp)
  have hx_mem : (X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := by
    rw [hmax]; exact Ideal.subset_span (by simp)
  have hreg : IsRegular k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := by
    refine hcm.isRegular_of_le_radical ?_ ?_ ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> assumption
    · have hlist : Ideal.ofList ([C X, X] : List k⟦X⟧⟦X⟧) = Ideal.span {C X, X} := by
        rw [Ideal.ofList]
        congr 1
        ext r
        simp
      rw [hlist, hmax]
      exact le_sup_left.trans Ideal.le_radical
    · simp [hdim]
  have hsec : IsSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := hreg.isSecant
  have hcm_sec : IsCMSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := hcm.isCMSecant_of_isSecant hsec
  have hdim_q :
      Module.supportDim k⟦X⟧⟦X⟧
          (k⟦X⟧⟦X⟧ ⧸ Ideal.ofList ([C X, X] : List k⟦X⟧⟦X⟧) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧)) =
        0 := by
    have h := hsec.supportDim_add_length_eq
    rw [hdim] at h
    have h2 : Module.supportDim k⟦X⟧⟦X⟧
        (k⟦X⟧⟦X⟧ ⧸ Ideal.ofList ([C X, X] : List k⟦X⟧⟦X⟧) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧)) +
          1 + 1 = 0 + 1 + 1 := by
      simpa [add_assoc, one_add_one_eq_two] using h
    exact ENat.WithBot.add_one_cancel.mp (ENat.WithBot.add_one_cancel.mp h2)
  refine ⟨hcm_sec, ?_, ?_, fun hbad ↦ ?_⟩
  · simpa using (isCMSecant_iff_isPStandard_reverse hdim_q.le).mp hcm_sec
  · simpa using hsec.take_append_mul (i := 0) (j := 1) (by omega) (by simp)
  · have h_eq_id : Ideal.ofList ([C X * X, X] : List k⟦X⟧⟦X⟧) = Ideal.span {X} := by
      refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · intro r hr
        rcases show r = C X * X ∨ r = X by simpa using hr with rfl | rfl
        · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
        · exact Ideal.subset_span rfl
      · rintro _ rfl
        exact Ideal.subset_span (by simp)
    have hdim_bad := hbad.supportDim_add_length_eq
    have he := Submodule.quotEquivOfEq
      (Ideal.ofList ([C X * X, X] : List k⟦X⟧⟦X⟧) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧))
      ((X : k⟦X⟧⟦X⟧) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧))
      (by rw [h_eq_id, Submodule.ideal_span_singleton_smul])
    rw [Module.supportDim_eq_of_equiv he, hdim] at hdim_bad
    have hx_reg : IsSMulRegular (k⟦X⟧⟦X⟧) (X : k⟦X⟧⟦X⟧) := fun a b hab ↦
      mul_left_cancel₀ PowerSeries.X_ne_zero hab
    have hdim_x : Module.supportDim k⟦X⟧⟦X⟧ (QuotSMulTop (X : k⟦X⟧⟦X⟧) k⟦X⟧⟦X⟧) = 1 := by
      have hx1 := Module.supportDim_quotSMulTop_succ_eq_supportDim hx_reg hx_mem
      rw [hdim] at hx1
      exact ENat.WithBot.add_one_cancel.mp (by simpa [one_add_one_eq_two] using hx1)
    rw [hdim_x] at hdim_bad
    change (1 : WithBot ℕ∞) + (2 : ℕ) = 2 at hdim_bad
    exact absurd hdim_bad (by norm_cast)

example :
    ∃ ys : List k⟦X⟧⟦X⟧,
      IsCMSecant k⟦X⟧⟦X⟧ ([C X] ++ ys) ∧
        IsPStandard k⟦X⟧⟦X⟧ ([C X] ++ ys).reverse ∧
        Module.supportDim k⟦X⟧⟦X⟧
            (k⟦X⟧⟦X⟧ ⧸ Ideal.ofList ([C X] ++ ys) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧)) = 0 := by
  have hcm : Module.IsCohenMacaulay k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ := TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hdim : Module.supportDim k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ = 2 := by
    rw [Module.supportDim_self_eq_ringKrullDim,
      TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing]
  have hcx_mem : (C X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := by
    rw [TauCeti.PowerSeries.maximalIdeal_eq_span_C_X irreducible_X]
    exact Ideal.subset_span (by simp)
  have hcx_reg : IsSMulRegular (k⟦X⟧⟦X⟧) (C X : k⟦X⟧⟦X⟧) := fun a b hab ↦
    mul_left_cancel₀ (map_ne_zero_iff _ PowerSeries.C_injective |>.mpr PowerSeries.X_ne_zero) hab
  have hdim_cx : Module.supportDim k⟦X⟧⟦X⟧ (QuotSMulTop (C X : k⟦X⟧⟦X⟧) k⟦X⟧⟦X⟧) = 1 := by
    have h1 := Module.supportDim_quotSMulTop_succ_eq_supportDim hcx_reg hcx_mem
    rw [hdim] at h1
    exact ENat.WithBot.add_one_cancel.mp (by simpa [one_add_one_eq_two] using h1)
  have hcm_cx : IsCMSecant k⟦X⟧⟦X⟧ ([C X] : List k⟦X⟧⟦X⟧) :=
    hcm.isCMSecant_of_isSecant (isSecant_singleton_iff.mpr ⟨hcx_mem, by rw [hdim_cx, hdim]; decide⟩)
  obtain ⟨ys, hcm_ext, hdim0⟩ := hcm_cx.exists_append_supportDim_eq_zero
  exact ⟨ys, hcm_ext, (isCMSecant_iff_isPStandard_reverse hdim0.le).mp hcm_ext, hdim0⟩

end TwoDimPowerSeries

section NonCohenMacaulay

open _root_.PowerSeries TrivSqZeroExt

variable (k : Type u) [Field k]

local notation "κ" => k⟦X⟧ ⧸ maximalIdeal k⟦X⟧
local notation "S" => TrivSqZeroExt k⟦X⟧ κ

/-- The one-dimensional non-Cohen–Macaulay local ring `S = k⟦X⟧ ⊕ k` (algebraically
`k⟦x, y⟧ ⧸ (x², xy)`): `[]` is not CM-secant, `a_𝔪(S, 1) = 𝔪 ≠ ⊤`, and `y = inl X` is a zero
divisor (`y * inr 1 = 0`), yet both `[inl X]` and `[inl X + inr 1]` are secant, CM-secant, and
`p`-standard. -/
public theorem TauCeti.Examples.Secant.trivSqZeroExt_nonCohenMacaulay :
    let y : S := inl X
    let y' : S := inl X + inr 1
    ¬ Module.IsCohenMacaulay S S ∧
      ¬ IsCMSecant S ([] : List S) ∧
      localCohomology.annihilatorProduct (maximalIdeal S) S 1 = maximalIdeal S ∧
      localCohomology.annihilatorProduct (maximalIdeal S) S 1 ≠ ⊤ ∧
      ¬ IsSMulRegular S y ∧
      IsSecant S [y] ∧
      IsCMSecant S [y] ∧
      IsPStandard S [y] ∧
      IsCMSecant S [y'] ∧
      IsPStandard S [y'] := by
  intro y y'
  have hdimA : ringKrullDim k⟦X⟧ = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one k⟦X⟧
  have hdimS : Module.supportDim S S = 1 := by
    rw [Module.supportDim_self_eq_ringKrullDim, TrivSqZeroExt.ringKrullDim_eq, hdimA]
  have hκ : depth (ModuleCat.of k⟦X⟧ κ) = 0 :=
    depth_eq_zero_iff_nontrivial_linearMap.mpr
      ⟨⟨LinearMap.id, 0, fun h ↦ by simpa using LinearMap.congr_fun h 1⟩⟩
  have hnotCM : ¬ Module.IsCohenMacaulay S S :=
    TrivSqZeroExt.not_isCohenMacaulay hκ (by rw [hdimA]; decide)
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ := by
    rw [maximalIdeal_eq_span_X]; exact Ideal.subset_span rfl
  have hy_mem : y ∈ maximalIdeal S := by
    rw [TrivSqZeroExt.mem_maximalIdeal_iff]
    exact hx_mem
  have hy'_mem : y' ∈ maximalIdeal S := by
    rw [TrivSqZeroExt.mem_maximalIdeal_iff]
    simpa [y'] using hx_mem
  -- `𝔪_S` annihilates `inr b` for every `b : κ`.
  have hmul_inr : ∀ t ∈ maximalIdeal S, ∀ b : κ, t * inr b = 0 := by
    intro t ht b
    rw [TrivSqZeroExt.mem_maximalIdeal_iff] at ht
    apply TrivSqZeroExt.ext
    · rw [fst_mul, fst_inr, mul_zero, fst_zero]
    · rw [snd_mul, fst_inr, snd_inr, snd_zero]
      simp only [MulOpposite.op_zero, zero_smul, add_zero]
      induction b using Submodule.Quotient.induction_on with | H a =>
        change Ideal.Quotient.mk (maximalIdeal k⟦X⟧) (t.fst * a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right a (maximalIdeal k⟦X⟧) ht
  -- The `𝔪_S`-primary component of `S` consists precisely of the elements with `fst = 0`.
  have hprim_mem : ∀ s : S, s ∈ (maximalIdeal S).primaryComponent S ↔ s.fst = 0 := by
    intro s
    rw [Ideal.primaryComponent_mem]
    constructor
    · rintro ⟨n, hn⟩
      rw [Submodule.mem_torsionBySet_iff] at hn
      have hyn : y ^ n ∈ (maximalIdeal S) ^ n := Ideal.pow_mem_pow hy_mem n
      have h0 : y ^ n * s = 0 := hn ⟨y ^ n, hyn⟩
      have hfst : (X : k⟦X⟧) ^ n * s.fst = 0 := by
        have h1 := congrArg TrivSqZeroExt.fst h0
        rw [fst_mul, fst_zero, fst_pow] at h1
        simpa [y] using h1
      exact (mul_eq_zero.mp hfst).resolve_left (pow_ne_zero n PowerSeries.X_ne_zero)
    · intro hfst
      refine ⟨1, ?_⟩
      rw [pow_one, Submodule.mem_torsionBySet_iff]
      rintro ⟨t, ht⟩
      have hs : s = inr s.snd := TrivSqZeroExt.ext (by simp [hfst]) (by simp)
      rw [hs]
      exact hmul_inr t ht s.snd
  -- Therefore `a_𝔪(S, 1) = Ann_S(𝔪_S-primary component) = 𝔪_S`.
  have hann : localCohomology.annihilatorProduct (maximalIdeal S) S 1 = maximalIdeal S := by
    rw [localCohomology.annihilatorProduct_one_eq_annihilator_primaryComponent]
    ext t
    rw [Module.mem_annihilator]
    constructor
    · intro ht
      have hinr : (inr 1 : S) ∈ (maximalIdeal S).primaryComponent S := (hprim_mem _).mpr rfl
      have h0 : (t * (inr 1 : S)).snd = 0 :=
        congrArg (fun x ↦ x.val.snd) (ht ⟨inr 1, hinr⟩)
      rw [snd_mul, fst_inr, snd_inr] at h0
      have hfst : t.fst • (1 : κ) = 0 := by simpa using h0
      have hmk : Ideal.Quotient.mk (maximalIdeal k⟦X⟧) t.fst = 0 := by
        simpa [Algebra.smul_def] using hfst
      rw [TrivSqZeroExt.mem_maximalIdeal_iff]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
    · intro ht ⟨s, hs⟩
      apply Subtype.ext
      have hs' : s = inr s.snd := TrivSqZeroExt.ext (by simp [(hprim_mem s).mp hs]) (by simp)
      change t * s = 0
      rw [hs']
      exact hmul_inr t ht s.snd
  -- Every prime containing `y` (or `y'`) equals `maximalIdeal S`, so both quotients have dim `≤ 0`.
  have hsupp_le_zero : ∀ z ∈ maximalIdeal S,
      (∀ p : Ideal S, p.IsPrime → z ∈ p → y ∈ p) →
      Module.supportDim S (QuotSMulTop z S) ≤ 0 := by
    intro z _ hzy
    have key : ∀ p ∈ Module.support S (QuotSMulTop z S), p.asIdeal = maximalIdeal S := by
      intro p hp
      rw [Module.support_quotSMulTop] at hp
      have hzp : z ∈ p.asIdeal := by simpa using hp.2
      have hyp : y ∈ p.asIdeal := hzy p.asIdeal p.isPrime hzp
      refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) fun s hs ↦ ?_
      have hsfst : s.fst ∈ Ideal.span {(X : k⟦X⟧)} := by
        rw [← maximalIdeal_eq_span_X]
        exact TrivSqZeroExt.mem_maximalIdeal_iff.mp hs
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hsfst
      have hdiff : s - inl r * y = inr s.snd :=
        TrivSqZeroExt.ext (by simp [y, hr, mul_comm]) (by simp [y])
      have hinr_p : inr s.snd ∈ p.asIdeal := by
        refine p.isPrime.mem_of_pow_mem 2 ?_
        rw [sq, inr_mul_inr]
        exact p.asIdeal.zero_mem
      have : s = inl r * y + inr s.snd := by
        rw [← hdiff, add_sub_cancel]
      rw [this]
      exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hyp) hinr_p
    have : Subsingleton (Module.support S (QuotSMulTop z S)) :=
      ⟨fun p q ↦ Subtype.ext (PrimeSpectrum.ext ((key p.1 p.2).trans (key q.1 q.2).symm))⟩
    exact Order.krullDim_nonpos_of_subsingleton
  have hdim_y : Module.supportDim S (QuotSMulTop y S) ≤ 0 :=
    hsupp_le_zero y hy_mem fun _ _ h ↦ h
  have hdim_y' : Module.supportDim S (QuotSMulTop y' S) ≤ 0 := by
    refine hsupp_le_zero y' hy'_mem fun p hp hpy' ↦ hp.mem_of_pow_mem 2 ?_
    have hsq : y' ^ 2 = y ^ 2 := by
      rw [sq, sq]
      have hxy : y * inr (1 : κ) = 0 := hmul_inr y hy_mem 1
      have hyx : inr (1 : κ) * y = 0 := by rw [mul_comm]; exact hxy
      calc
        (y + inr 1) * (y + inr 1) = y * y + y * inr 1 + inr 1 * y + inr 1 * inr 1 := by ring
        _ = y * y := by rw [hxy, hyx, inr_mul_inr, add_zero, add_zero, add_zero]
    rw [← hsq]
    exact p.pow_mem_of_mem hpy' 2 (by decide)
  have hsec_y : IsSecant S [y] :=
    isSecant_singleton_iff.mpr ⟨hy_mem, hdim_y.trans_lt (by rw [hdimS]; decide)⟩
  have hsec_y' : IsSecant S [y'] :=
    isSecant_singleton_iff.mpr ⟨hy'_mem, hdim_y'.trans_lt (by rw [hdimS]; decide)⟩
  have hcm_y : IsCMSecant S [y] :=
    isCMSecant_singleton_iff.mpr
      ⟨hsec_y, Module.isCohenMacaulay_of_supportDim_nonpos hdim_y, 1, hdimS,
        by rw [hann]; exact hy_mem⟩
  have hcm_y' : IsCMSecant S [y'] :=
    isCMSecant_singleton_iff.mpr
      ⟨hsec_y', Module.isCohenMacaulay_of_supportDim_nonpos hdim_y', 1, hdimS,
        by rw [hann]; exact hy'_mem⟩
  have hdim_yl : Module.supportDim S (S ⧸ Ideal.ofList [y] • (⊤ : Submodule S S)) ≤ 0 := by
    rwa [Module.supportDim_eq_of_equiv (Submodule.quotOfListSingletonSMulTopEquiv S y)]
  have hdim_y'l : Module.supportDim S (S ⧸ Ideal.ofList [y'] • (⊤ : Submodule S S)) ≤ 0 := by
    rwa [Module.supportDim_eq_of_equiv (Submodule.quotOfListSingletonSMulTopEquiv S y')]
  have hnotreg : ¬ IsSMulRegular S y := fun hreg ↦ by
    have h0 : y • (inr 1 : S) = y • (0 : S) := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero]
      exact hmul_inr y hy_mem 1
    have h1 : (inr 1 : S) = 0 := hreg h0
    exact one_ne_zero (congrArg TrivSqZeroExt.snd h1)
  refine ⟨hnotCM, fun h ↦ hnotCM (isCMSecant_nil_iff.mp h), hann, ?_, hnotreg,
    hsec_y, hcm_y, ?_, hcm_y', ?_⟩
  · rw [hann]
    exact (maximalIdeal.isMaximal _).ne_top
  · exact (isCMSecant_iff_isPStandard_reverse hdim_yl).mp hcm_y
  · exact (isCMSecant_iff_isPStandard_reverse hdim_y'l).mp hcm_y'

end NonCohenMacaulay
