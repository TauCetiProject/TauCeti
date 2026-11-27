/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.CohenMacaulay.Secant
public import TauCeti.RingTheory.CohenMacaulay.TrivSqZeroExt
import Mathlib.Data.Rat.Defs
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Examples of CM-secant lists, parameter completion, and `p`-standard systems

Concrete instances of `TauCeti.IsCMSecant`, `TauCeti.IsPStandard`, and
`localCohomology.annihilatorProduct`:

* the zero module `PUnit`, the field `ℚ`, and `ℤ` prefix quotients (`[]`, `[2]`, `[2, 3]`);
* the discrete valuation ring `k⟦X⟧` (`[X]` and `[X²]` are CM-secant and `p`-standard) and
  cutoff-one exactness `a_𝔪(k⟦X⟧ ⧸ (X²), 1) = (X²) ≠ (X)`;
* the two-dimensional regular local ring `k⟦X⟧⟦X⟧` (`[C X, X]` is CM-secant, `[X, C X]` is
  `p`-standard, `[C X * X]` is secant while `[C X * X, X]` is not, and `[C X]` extends by
  `IsCMSecant.exists_append_supportDim_eq_zero`);
* the one-dimensional non-Cohen–Macaulay local ring `S = TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ 𝔪)`
  (algebraically `k⟦x, y⟧ ⧸ (x², xy)`), where `[]` is not CM-secant,
  `TauCeti.annihilatorProduct_trivSqZeroExt_one` computes `a_𝔪(S, 1) = 𝔪 ≠ ⊤`, and
  `y = inl X` is a zero divisor yet both `[inl X]` and `[inl X + inr 1]` are CM-secant and
  `p`-standard.
-/

public section

universe u

open IsLocalRing Module localCohomology Pointwise

namespace TauCeti

section ZeroAndField

/-- For the zero module `PUnit`, only `[]` is CM-secant or `p`-standard, and every annihilator
product is `⊤`. -/
example (R : Type u) [CommRing R] [IsLocalRing R] (r : R) (J : Ideal R) (d : ℕ) :
    IsCMSecant (R := R) (PUnit : Type u) ([] : List R) ∧
      ¬ IsCMSecant (R := R) (PUnit : Type u) [r] ∧
      IsPStandard (R := R) (PUnit : Type u) ([] : List R) ∧
      ¬ IsPStandard (R := R) (PUnit : Type u) [r] ∧
      annihilatorProduct J (PUnit : Type u) d = ⊤ :=
  ⟨isCMSecant_iff_eq_nil.2 rfl, fun h ↦ by simp [isCMSecant_iff_eq_nil] at h,
    isPStandard_iff_eq_nil.2 rfl, fun h ↦ by simp [isPStandard_iff_eq_nil] at h,
    annihilatorProduct_eq_top_of_subsingleton J PUnit d⟩

/-- Over `ℚ`, `[]` is CM-secant and `p`-standard while `[0]` is not CM-secant. -/
example :
    IsCMSecant ℚ ([] : List ℚ) ∧ ¬ IsCMSecant ℚ ([0] : List ℚ) ∧ IsPStandard ℚ ([] : List ℚ) := by
  have hdim : supportDim ℚ ℚ = 0 := by
    rw [supportDim_self_eq_ringKrullDim, ringKrullDim_eq_zero_of_isField (Field.toIsField ℚ)]
  refine ⟨isCMSecant_nil_iff.2 isCohenMacaulay_of_krullDimLE_zero, fun h ↦ ?_,
    by rw [isPStandard_nil_iff, hdim]⟩
  have hlen := h.isSecant.length_le_supportDim
  rw [hdim] at hlen
  exact absurd hlen (by norm_cast)

end ZeroAndField

section PrefixQuotientsInt

example : Nontrivial (prefixQuotient ℤ ([] : List ℤ)) :=
  (prefixQuotient.nilEquiv ℤ).toEquiv.nontrivial_congr.2 inferInstance

example : Nontrivial (prefixQuotient ℤ ([2] : List ℤ)) := by
  refine Submodule.Quotient.nontrivial_iff.2 fun h ↦ ?_
  have h1 : (1 : ℤ) ∈ Ideal.ofList ([2] : List ℤ) • (⊤ : Submodule ℤ ℤ) := by
    rw [h]; exact Submodule.mem_top
  rw [Ideal.ofList_singleton, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton] at h1
  omega

example : Subsingleton (prefixQuotient ℤ ([2, 3] : List ℤ)) := by
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun _ _ ↦ ?_)
  have h3 : (3 : ℤ) ∈ Ideal.ofList ([2, 3] : List ℤ) := Ideal.subset_span (by simp)
  have h2 : (2 : ℤ) ∈ Ideal.ofList ([2, 3] : List ℤ) := Ideal.subset_span (by simp)
  have h1 : (1 : ℤ) ∈ Ideal.ofList ([2, 3] : List ℤ) := by simpa using sub_mem h3 h2
  rw [Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one, Submodule.top_smul]
  exact Submodule.mem_top

end PrefixQuotientsInt

section OneDimPowerSeries

open _root_.PowerSeries

variable (k : Type u) [Field k]

/-- Over `k⟦X⟧`, both `[X]` and `[X²]` are CM-secant and `p`-standard. -/
example :
    IsCMSecant k⟦X⟧ ([X] : List k⟦X⟧) ∧ IsCMSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) ∧
      IsPStandard k⟦X⟧ ([X] : List k⟦X⟧) ∧ IsPStandard k⟦X⟧ ([X ^ 2] : List k⟦X⟧) := by
  have hcm : IsCohenMacaulay k⟦X⟧ k⟦X⟧ := IsRegularLocalRing.isCohenMacaulay
  have hdim : supportDim k⟦X⟧ k⟦X⟧ = 1 := by
    rw [supportDim_self_eq_ringKrullDim, IsDiscreteValuationRing.ringKrullDim_eq_one]
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ := by
    rw [maximalIdeal_eq_span_X]; exact Ideal.subset_span rfl
  have hsec_x : IsSecant k⟦X⟧ ([X] : List k⟦X⟧) :=
    (hcm.isRegular_of_le_radical (by simpa using hx_mem)
      (by
        rw [Ideal.ofList_singleton, maximalIdeal_eq_span_X]
        exact le_sup_left.trans Ideal.le_radical)
      (by simp [hdim])).isSecant
  have hsec_x2 : IsSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) :=
    (isSecant_append_pow_cons_iff [] [] X two_ne_zero).2 hsec_x
  have hdim0 (r : k⟦X⟧) (hs : IsSecant k⟦X⟧ [r]) :
      supportDim k⟦X⟧ (prefixQuotient k⟦X⟧ [r]) = 0 :=
    hs.supportDim_prefixQuotient_eq_zero_iff.2 (by simp [hdim])
  exact ⟨hcm.isCMSecant_of_isSecant hsec_x, hcm.isCMSecant_of_isSecant hsec_x2,
    (isCMSecant_iff_isPStandard_reverse (hdim0 X hsec_x).le).1 (hcm.isCMSecant_of_isSecant hsec_x),
    (isCMSecant_iff_isPStandard_reverse (hdim0 (X ^ 2) hsec_x2).le).1
      (hcm.isCMSecant_of_isSecant hsec_x2)⟩

/-- Cutoff-one exactness over `k⟦X⟧`: `a_𝔪(k⟦X⟧ ⧸ (X²), 1) = (X²)`, so `X` does not belong to it. -/
example :
    annihilatorProduct (maximalIdeal k⟦X⟧) (k⟦X⟧ ⧸ Ideal.span {(X : k⟦X⟧) ^ 2}) 1 =
        Ideal.span {X ^ 2} ∧
      (X : k⟦X⟧) ∉
        annihilatorProduct (maximalIdeal k⟦X⟧) (k⟦X⟧ ⧸ Ideal.span {(X : k⟦X⟧) ^ 2}) 1 := by
  set I : Ideal k⟦X⟧ := Ideal.span {(X : k⟦X⟧) ^ 2}
  have hpow : (maximalIdeal k⟦X⟧) ^ 2 ≤ Module.annihilator k⟦X⟧ (k⟦X⟧ ⧸ I) := by
    rw [Ideal.annihilator_quotient, maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
  have heq : annihilatorProduct (maximalIdeal k⟦X⟧) (k⟦X⟧ ⧸ I) 1 = I := by
    rw [annihilatorProduct_one, annihilator_obj_zero_of_pow_le _ _ hpow, Ideal.annihilator_quotient]
  refine ⟨heq, fun hx ↦ ?_⟩
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (heq ▸ hx)
  have hunit : IsUnit (X : k⟦X⟧) := isUnit_iff_exists_inv.2 ⟨q,
    mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k)) (by rw [mul_one, ← mul_assoc, ← sq, ← hq])⟩
  exact (notMem_maximalIdeal.2 hunit) (maximalIdeal_eq_span_X (k := k) ▸ Ideal.subset_span rfl)

end OneDimPowerSeries

section TwoDimPowerSeries

open _root_.PowerSeries

variable (k : Type u) [Field k]

/-- Over `k⟦X⟧⟦X⟧`, `[C X, X]` is CM-secant, its reversal `[X, C X]` is `p`-standard, and the
truncated product `[C X * X]` is secant while the un-truncated list `[C X * X, X]` is not. -/
example :
    IsCMSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) ∧
      IsPStandard k⟦X⟧⟦X⟧ ([X, C X] : List k⟦X⟧⟦X⟧) ∧
      IsSecant k⟦X⟧⟦X⟧ ([C X * X] : List k⟦X⟧⟦X⟧) ∧
      ¬ IsSecant k⟦X⟧⟦X⟧ ([C X * X, X] : List k⟦X⟧⟦X⟧) := by
  have hcm : IsCohenMacaulay k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ := IsRegularLocalRing.isCohenMacaulay
  have hdim2 : supportDim k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ = 2 := by
    rw [supportDim_self_eq_ringKrullDim, PowerSeries.ringKrullDim_of_isDiscreteValuationRing]
  have hmax : maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} :=
    PowerSeries.maximalIdeal_eq_span_C_X irreducible_X
  have hsec : IsSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := by
    have hofList : Ideal.ofList ([C X, X] : List k⟦X⟧⟦X⟧) = maximalIdeal k⟦X⟧⟦X⟧ := by
      rw [Ideal.ofList_cons, Ideal.ofList_singleton, ← Ideal.span_union, Set.singleton_union, hmax]
    refine (hcm.isRegular_of_le_radical (fun r hr ↦ ?_)
      (by rw [hofList]; exact le_sup_left.trans Ideal.le_radical)
      (by rw [hdim2]; rfl)).isSecant
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hmax ▸ Ideal.subset_span (by simp)
    · exact (List.mem_singleton.1 hr) ▸ hmax ▸ Ideal.subset_span (by simp)
  have hcm_sec : IsCMSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := hcm.isCMSecant_of_isSecant hsec
  have hdim_q : supportDim k⟦X⟧⟦X⟧ (prefixQuotient k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧)) = 0 :=
    hsec.supportDim_prefixQuotient_eq_zero_iff.2 (by simp [hdim2])
  have hmem_x : (X : k⟦X⟧⟦X⟧) ∈ ([C X, X] : List k⟦X⟧⟦X⟧) := by simp
  refine ⟨hcm_sec, (isCMSecant_iff_isPStandard_reverse hdim_q.le).1 hcm_sec,
    hsec.append_mul (rs := []) (qs := [X]) (r := C (X : k⟦X⟧)) (s := X) hmem_x, fun hbad ↦ ?_⟩
  have hx_mem : (X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := hmax ▸ Ideal.subset_span (by simp)
  have h_eq_id : Ideal.ofList ([C X * X, X] : List k⟦X⟧⟦X⟧) = Ideal.span {X} := by
    refine le_antisymm (Ideal.span_le.2 fun r hr ↦ ?_)
      (Ideal.span_le.2 fun _ h ↦ h ▸ Ideal.subset_span (by simp))
    rcases List.mem_cons.1 hr with rfl | hr
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · exact (List.mem_singleton.1 hr) ▸ Ideal.subset_span rfl
  have hdim_x : supportDim k⟦X⟧⟦X⟧ (QuotSMulTop (X : k⟦X⟧⟦X⟧) k⟦X⟧⟦X⟧) = 1 := by
    have hx := supportDim_quotSMulTop_succ_eq_supportDim
      (fun _ _ ↦ mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k⟦X⟧))) hx_mem
    rw [hdim2, ← one_add_one_eq_two, ENat.WithBot.add_one_cancel] at hx
    exact hx
  have hdim_bad := hbad.supportDim_add_length_eq
  rw [supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _
      (by rw [h_eq_id, Submodule.ideal_span_singleton_smul])),
    hdim_x, hdim2, List.length_cons, List.length_singleton, Nat.cast_two] at hdim_bad
  exact absurd hdim_bad (by decide)

/-- Over `k⟦X⟧⟦X⟧`, the one-element CM-secant list `[C X]` extends via
`IsCMSecant.exists_append_supportDim_eq_zero` to a full CM-secant parameter list whose reversal is
`p`-standard. -/
example :
    ∃ ys : List k⟦X⟧⟦X⟧,
      IsCMSecant k⟦X⟧⟦X⟧ ([C X] ++ ys) ∧ IsPStandard k⟦X⟧⟦X⟧ ([C X] ++ ys).reverse ∧
        supportDim k⟦X⟧⟦X⟧ (prefixQuotient k⟦X⟧⟦X⟧ ([C X] ++ ys)) = 0 := by
  have hcm : IsCohenMacaulay k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ := IsRegularLocalRing.isCohenMacaulay
  have hmax : maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} :=
    PowerSeries.maximalIdeal_eq_span_C_X irreducible_X
  have hcx_mem : (C X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := hmax ▸ Ideal.subset_span (by simp)
  have hcx_reg : IsSMulRegular k⟦X⟧⟦X⟧ (C X : k⟦X⟧⟦X⟧) := fun _ _ hab ↦
    mul_left_cancel₀ ((map_ne_zero_iff _ PowerSeries.C_injective).2 PowerSeries.X_ne_zero) hab
  have hdrop := supportDim_quotSMulTop_succ_eq_supportDim hcx_reg hcx_mem
  have hcm_cx : IsCMSecant k⟦X⟧⟦X⟧ ([C X] : List k⟦X⟧⟦X⟧) :=
    hcm.isCMSecant_of_isSecant ((isSecant_singleton_iff (C X)).2
      ⟨hcx_mem, lt_supportDim_of_add_one_eq hdrop⟩)
  obtain ⟨ys, hcm_ext, hdim0⟩ := hcm_cx.exists_append_supportDim_eq_zero
  exact ⟨ys, hcm_ext, (isCMSecant_iff_isPStandard_reverse hdim0.le).1 hcm_ext, hdim0⟩

end TwoDimPowerSeries

section NonCohenMacaulay

open _root_.PowerSeries TrivSqZeroExt

variable (k : Type u) [Field k]

/-- In `S = k⟦X⟧ ⊕ k`, the cutoff-one local-cohomology annihilator product `a_𝔪(S, 1)` equals the
maximal ideal `𝔪` of `S`. -/
theorem annihilatorProduct_trivSqZeroExt_one :
    annihilatorProduct
      (maximalIdeal (TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)))
      (TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)) 1 =
      maximalIdeal (TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)) := by
  let S := TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)
  have hprim : ∀ s : S, s ∈ (maximalIdeal S).primaryComponent S ↔ s.fst = 0 := fun s ↦ by
    rw [Ideal.primaryComponent_mem]
    refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun hfst ↦ ⟨1, by
      rw [pow_one, Submodule.mem_torsionBySet_iff]; rintro ⟨t, ht⟩
      exact (TrivSqZeroExt.ext (by simp [hfst]) (by simp) : s = inr s.snd) ▸
        mul_inr_eq_zero_of_mem_maximalIdeal ht s.snd⟩⟩
    rw [Submodule.mem_torsionBySet_iff] at hn
    have hy : (inl X : S) ∈ maximalIdeal S := TrivSqZeroExt.mem_maximalIdeal_iff.2
      (maximalIdeal_eq_span_X (k := k) ▸ Ideal.subset_span rfl)
    have hfst : (X : k⟦X⟧) ^ n * s.fst = 0 := by
      simpa [S] using congrArg TrivSqZeroExt.fst (hn ⟨(inl X : S) ^ n, Ideal.pow_mem_pow hy n⟩)
    exact (mul_eq_zero.1 hfst).resolve_left (pow_ne_zero n PowerSeries.X_ne_zero)
  rw [annihilatorProduct_one, annihilator_obj_zero]
  ext t; rw [Module.mem_annihilator]
  refine ⟨fun ht ↦ ?_, fun ht ⟨s, hs⟩ ↦ Subtype.ext ?_⟩
  · have h0 : (t * (inr 1 : S)).snd = 0 :=
      congrArg (fun x ↦ x.val.snd) (ht ⟨inr 1, (hprim _).2 rfl⟩)
    rw [snd_mul, fst_inr, snd_inr] at h0
    exact TrivSqZeroExt.mem_maximalIdeal_iff.2 <|
      Ideal.Quotient.eq_zero_iff_mem.1 <| by simpa [Algebra.smul_def] using h0
  · have hs' : s = inr s.snd := TrivSqZeroExt.ext (by simp [(hprim s).1 hs]) (by simp)
    rw [SetLike.val_smul, smul_eq_mul, Submodule.coe_mk, ZeroMemClass.coe_zero, hs']
    exact mul_inr_eq_zero_of_mem_maximalIdeal ht s.snd

/-- In the one-dimensional non-Cohen–Macaulay local ring `S = k⟦X⟧ ⊕ k` (algebraically
`k⟦x, y⟧ ⧸ (x², xy)`), `S` is not Cohen–Macaulay, `[]` is not CM-secant, and
`a_𝔪(S, 1) = 𝔪 ≠ ⊤`. -/
example :
    let S := TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)
    ¬ IsCohenMacaulay S S ∧
      ¬ IsCMSecant S ([] : List S) ∧
      annihilatorProduct (maximalIdeal S) S 1 = maximalIdeal S ∧
      annihilatorProduct (maximalIdeal S) S 1 ≠ ⊤ := by
  intro S
  let κ := k⟦X⟧ ⧸ maximalIdeal k⟦X⟧
  have hdimA : ringKrullDim k⟦X⟧ = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one k⟦X⟧
  have hκ : depth (ModuleCat.of k⟦X⟧ κ) = 0 := depth_eq_zero_iff_nontrivial_linearMap.2
    ⟨⟨LinearMap.id, 0, fun h ↦ by simpa using LinearMap.congr_fun h 1⟩⟩
  have hnotCM : ¬ IsCohenMacaulay S S :=
    TrivSqZeroExt.not_isCohenMacaulay hκ (by rw [hdimA]; decide)
  have hann := annihilatorProduct_trivSqZeroExt_one k
  exact ⟨hnotCM, fun h ↦ hnotCM (isCMSecant_nil_iff.1 h), hann,
    by rw [hann]; exact (maximalIdeal.isMaximal _).ne_top⟩

/-- In `S = k⟦X⟧ ⊕ k`, `y = inl X` is a zero divisor (`y * inr 1 = 0`), yet both `[inl X]` and
`[inl X + inr 1]` are secant, CM-secant, and `p`-standard. -/
example :
    let S := TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)
    let y : S := inl X
    let y' : S := inl X + inr 1
    ¬ IsSMulRegular S y ∧
      IsSecant S [y] ∧ IsCMSecant S [y] ∧ IsPStandard S [y] ∧
      IsCMSecant S [y'] ∧ IsPStandard S [y'] := by
  intro S y y'
  have hann := annihilatorProduct_trivSqZeroExt_one k
  have hdimS : supportDim S S = 1 := by
    rw [supportDim_self_eq_ringKrullDim, TrivSqZeroExt.ringKrullDim_eq,
      IsDiscreteValuationRing.ringKrullDim_eq_one k⟦X⟧]
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ :=
    maximalIdeal_eq_span_X (k := k) ▸ Ideal.subset_span rfl
  have hy_mem : y ∈ maximalIdeal S := TrivSqZeroExt.mem_maximalIdeal_iff.2 hx_mem
  have hy'_mem : y' ∈ maximalIdeal S :=
    TrivSqZeroExt.mem_maximalIdeal_iff.2 (by simpa [S, y'] using hx_mem)
  have hy_inr : y * (inr 1 : S) = 0 := mul_inr_eq_zero_of_mem_maximalIdeal hy_mem 1
  have hnonpos : ∀ {z : S}, (∀ p : Ideal S, p.IsPrime → z ∈ p → y ∈ p) →
      supportDim S (QuotSMulTop z S) ≤ 0 := fun hzy ↦ by
    refine supportDim_nonpos_of_support_subsingleton
      (Set.subsingleton_singleton (a := closedPoint S) |>.anti fun p hp ↦ PrimeSpectrum.ext ?_)
    rw [support_quotSMulTop] at hp
    have hyp : y ∈ p.asIdeal := hzy p.asIdeal p.isPrime (by simpa using hp.2)
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) fun s hs ↦ ?_
    have hsfst : s.fst ∈ Ideal.span {(X : k⟦X⟧)} := by
      rw [← maximalIdeal_eq_span_X]; exact TrivSqZeroExt.mem_maximalIdeal_iff.1 hs
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hsfst
    have hinr_p : inr s.snd ∈ p.asIdeal :=
      p.isPrime.mem_of_pow_mem 2 (by rw [sq, inr_mul_inr]; exact p.asIdeal.zero_mem)
    have hs_eq : s = inl r * y + inr s.snd :=
      TrivSqZeroExt.ext (by simp [S, y, hr, mul_comm]) (by simp [S, y])
    exact hs_eq ▸ p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hyp) hinr_p
  have hdim_y : supportDim S (QuotSMulTop y S) ≤ 0 := hnonpos fun _ _ h ↦ h
  have hdim_y' : supportDim S (QuotSMulTop y' S) ≤ 0 := hnonpos fun p hp hpy' ↦ by
    refine hp.mem_of_pow_mem 2 ?_
    have hsq : y' ^ 2 = y ^ 2 := by
      calc (y + inr 1) ^ 2 = y ^ 2 + 2 * (y * inr 1) + inr 1 * inr 1 := by ring
        _ = y ^ 2 := by rw [hy_inr, inr_mul_inr, mul_zero, add_zero, add_zero]
    exact hsq ▸ p.pow_mem_of_mem hpy' 2 (by decide)
  have hsec_y : IsSecant S [y] :=
    (isSecant_singleton_iff y).2 ⟨hy_mem, hdim_y.trans_lt (by rw [hdimS]; decide)⟩
  have hcm_y : IsCMSecant S [y] := (isCMSecant_singleton_iff y).2
    ⟨hsec_y, isCohenMacaulay_of_supportDim_nonpos hdim_y, 1, hdimS, by rw [hann]; exact hy_mem⟩
  have hcm_y' : IsCMSecant S [y'] := (isCMSecant_singleton_iff y').2
    ⟨(isSecant_singleton_iff y').2 ⟨hy'_mem, hdim_y'.trans_lt (by rw [hdimS]; decide)⟩,
      isCohenMacaulay_of_supportDim_nonpos hdim_y', 1, hdimS, by rw [hann]; exact hy'_mem⟩
  have hnotreg : ¬ IsSMulRegular S y := fun hreg ↦ one_ne_zero <| congrArg TrivSqZeroExt.snd <|
    hreg (by simpa [smul_eq_mul] using hy_inr : y • (inr 1 : S) = y • (0 : S))
  exact ⟨hnotreg, hsec_y, hcm_y,
    (isCMSecant_iff_isPStandard_reverse
      ((supportDim_eq_of_equiv (prefixQuotient.singletonEquiv S y)).trans_le hdim_y)).1 hcm_y,
    hcm_y',
    (isCMSecant_iff_isPStandard_reverse
      ((supportDim_eq_of_equiv (prefixQuotient.singletonEquiv S y')).trans_le hdim_y')).1 hcm_y'⟩

end NonCohenMacaulay

end TauCeti
