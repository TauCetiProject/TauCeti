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

Concrete instances of `localCohomology.annihilatorProduct`, `RingTheory.Sequence.IsSecant`,
`RingTheory.Sequence.IsCMSecant`, and `RingTheory.Sequence.IsPStandard`: zero module (`PUnit`),
field `ℚ`, `ℤ` prefix quotients (`[]`, `[2]`, `[2, 3]`), DVR `k⟦X⟧`, cutoff-1 exactness on
`k⟦X⟧ ⧸ (X²)`, regular 2D local ring `k⟦X⟧⟦X⟧` (including parameter completion), and the 1D
non-Cohen–Macaulay local ring `TrivSqZeroExt k⟦X⟧ (k⟦X⟧ ⧸ maximalIdeal k⟦X⟧)`.
-/

open IsLocalRing RingTheory.Sequence Pointwise

section ZeroModule

example {R : Type*} [CommRing R] [IsLocalRing R] (r : R) :
    IsSecant (PUnit : Type _) ([] : List R) ∧ ¬ IsSecant (PUnit : Type _) [r] :=
  ⟨isSecant_nil, fun h ↦ by simp [isSecant_iff_eq_nil_of_subsingleton] at h⟩

example (R : Type u) [CommRing R] [IsLocalRing R] (r : R) (J : Ideal R) (d : ℕ) :
    IsCMSecant (R := R) (PUnit : Type u) ([] : List R) ∧
      ¬ IsCMSecant (R := R) (PUnit : Type u) [r] ∧
      IsPStandard (R := R) (PUnit : Type u) ([] : List R) ∧
      ¬ IsPStandard (R := R) (PUnit : Type u) [r] ∧
      localCohomology.annihilatorProduct J (PUnit : Type u) d = ⊤ :=
  ⟨isCMSecant_iff_eq_nil_of_subsingleton.mpr rfl,
    fun h ↦ by simp [isCMSecant_iff_eq_nil_of_subsingleton] at h,
    isPStandard_iff_eq_nil_of_subsingleton.mpr rfl,
    fun h ↦ by simp [isPStandard_iff_eq_nil_of_subsingleton] at h,
    localCohomology.annihilatorProduct_of_subsingleton J PUnit d⟩

end ZeroModule

section Field

example :
    IsSecant ℚ ([] : List ℚ) ∧ ¬ IsSecant ℚ ([0] : List ℚ) ∧ ¬ IsSecant ℚ ([1] : List ℚ) ∧
      IsCMSecant ℚ ([] : List ℚ) ∧ ¬ IsCMSecant ℚ ([0] : List ℚ) ∧
      IsPStandard ℚ ([] : List ℚ) := by
  have hdim : Module.supportDim ℚ ℚ = 0 := by
    rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq_zero_of_isField (Field.toIsField ℚ)]
  have h0 : ¬ IsSecant ℚ ([0] : List ℚ) := fun h ↦ by
    have hlen := h.length_le_supportDim; rw [hdim] at hlen; exact absurd hlen (by norm_cast)
  exact ⟨isSecant_nil, h0,
    fun h ↦ (notMem_maximalIdeal.mpr isUnit_one) (h.mem_maximalIdeal List.mem_cons_self),
    isCMSecant_nil_iff.mpr Module.isCohenMacaulay_of_krullDimLE_zero,
    fun h ↦ h0 h.isSecant, by rw [isPStandard_nil_iff, hdim]⟩

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
  refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun _ _ ↦ ?_)
  have h3 : (3 : ℤ) ∈ Ideal.ofList ([2, 3] : List ℤ) := Ideal.subset_span (by simp)
  have h2 : (2 : ℤ) ∈ Ideal.ofList ([2, 3] : List ℤ) := Ideal.subset_span (by simp)
  have h1 : (1 : ℤ) ∈ Ideal.ofList ([2, 3] : List ℤ) := by simpa using sub_mem h3 h2
  rw [Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one, Submodule.top_smul]; exact Submodule.mem_top

end PrefixQuotientsInt

section OneDimPowerSeries

open _root_.PowerSeries

variable (k : Type u) [Field k]

example :
    IsSecant k⟦X⟧ ([X] : List k⟦X⟧) ∧ IsSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) ∧
      ¬ IsSecant k⟦X⟧ ([X, X] : List k⟦X⟧) ∧ ¬ IsSecant k⟦X⟧ ([1] : List k⟦X⟧) ∧
      IsCMSecant k⟦X⟧ ([X] : List k⟦X⟧) ∧ IsCMSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) ∧
      IsPStandard k⟦X⟧ ([X] : List k⟦X⟧) ∧ IsPStandard k⟦X⟧ ([X ^ 2] : List k⟦X⟧) := by
  have hcm : Module.IsCohenMacaulay k⟦X⟧ k⟦X⟧ := TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hdim : Module.supportDim k⟦X⟧ k⟦X⟧ = 1 := by
    rw [Module.supportDim_self_eq_ringKrullDim, IsDiscreteValuationRing.ringKrullDim_eq_one]
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ := by
    rw [maximalIdeal_eq_span_X]; exact Ideal.subset_span rfl
  have hsec_x : IsSecant k⟦X⟧ ([X] : List k⟦X⟧) :=
    (hcm.isRegular_of_le_radical (by simpa using hx_mem)
      (by
        rw [Ideal.ofList_singleton, maximalIdeal_eq_span_X]
        exact le_sup_left.trans Ideal.le_radical)
      (by simp [hdim])).isSecant
  have hsec_x2 : IsSecant k⟦X⟧ ([X ^ 2] : List k⟦X⟧) := hsec_x.set_pow (i := 0) (by simp) (by omega)
  have hdim0 : ∀ r : k⟦X⟧, IsSecant k⟦X⟧ [r] →
      Module.supportDim k⟦X⟧ (k⟦X⟧ ⧸ Ideal.ofList [r] • (⊤ : Submodule k⟦X⟧ k⟦X⟧)) = 0 :=
    fun r hs ↦ ENat.WithBot.add_one_cancel.mp (by simpa [hdim] using hs.supportDim_add_length_eq)
  refine ⟨hsec_x, hsec_x2, fun hxx ↦ ?_,
    fun h1 ↦ (notMem_maximalIdeal.mpr isUnit_one) (h1.mem_maximalIdeal List.mem_cons_self),
    hcm.isCMSecant_of_isSecant hsec_x, hcm.isCMSecant_of_isSecant hsec_x2,
    (isCMSecant_iff_isPStandard_reverse (hdim0 X hsec_x).le).mp (hcm.isCMSecant_of_isSecant hsec_x),
    (isCMSecant_iff_isPStandard_reverse (hdim0 (X ^ 2) hsec_x2).le).mp
      (hcm.isCMSecant_of_isSecant hsec_x2)⟩
  have hlen := hxx.length_le_supportDim; rw [hdim] at hlen; exact absurd hlen (by norm_cast)

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
    rw [Ideal.primaryComponent_mem]; refine ⟨2, ?_⟩; rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    rw [maximalIdeal_eq_span_X, Ideal.span_singleton_pow] at ha
    induction m using Submodule.Quotient.induction_on with | H r =>
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right r I ha)
  have heq : localCohomology.annihilatorProduct (maximalIdeal k⟦X⟧) (k⟦X⟧ ⧸ I) 1 = I := by
    rw [localCohomology.annihilatorProduct_one_eq_annihilator_primaryComponent, hprim]
    exact (Submodule.topEquiv (R := k⟦X⟧) (M := k⟦X⟧ ⧸ I)).annihilator_eq.trans
      Ideal.annihilator_quotient
  refine ⟨heq, fun hx ↦ ?_⟩
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (heq ▸ hx)
  have hunit : IsUnit (X : k⟦X⟧) := isUnit_iff_exists_inv.mpr ⟨q,
    mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k)) (by rw [mul_one, ← mul_assoc, ← sq, ← hq])⟩
  exact (notMem_maximalIdeal.mpr hunit) (maximalIdeal_eq_span_X (k := k) ▸ Ideal.subset_span rfl)

end OneDimPowerSeries

section TwoDimPowerSeries

open _root_.PowerSeries

variable (k : Type u) [Field k]

private theorem supportDim_twoDim : Module.supportDim k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ = 2 := by
  rw [Module.supportDim_self_eq_ringKrullDim,
    TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing]

private theorem supportDim_quotSMulTop_eq_one_of_reg {f : k⟦X⟧⟦X⟧}
    (hf_reg : IsSMulRegular k⟦X⟧⟦X⟧ f) (hf_mem : f ∈ maximalIdeal k⟦X⟧⟦X⟧) :
    Module.supportDim k⟦X⟧⟦X⟧ (QuotSMulTop f k⟦X⟧⟦X⟧) = 1 :=
  ENat.WithBot.add_one_cancel.mp (by
    simpa [one_add_one_eq_two, supportDim_twoDim k] using
      Module.supportDim_quotSMulTop_succ_eq_supportDim hf_reg hf_mem)

private theorem isSecant_C_X : IsSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := by
  have hcm : Module.IsCohenMacaulay k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ := TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hmax : maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} :=
    TauCeti.PowerSeries.maximalIdeal_eq_span_C_X irreducible_X
  have hofList : Ideal.ofList ([C X, X] : List k⟦X⟧⟦X⟧) = maximalIdeal k⟦X⟧⟦X⟧ := by
    rw [Ideal.ofList_cons, Ideal.ofList_singleton, ← Ideal.span_union, Set.singleton_union, hmax]
  refine (hcm.isRegular_of_le_radical (fun r hr ↦ ?_) ?_ (by simp [supportDim_twoDim k])).isSecant
  · rcases (by simpa using hr : r = C X ∨ r = X) with rfl | rfl <;>
      exact hmax ▸ Ideal.subset_span (by simp)
  · rw [hofList]; exact le_sup_left.trans Ideal.le_radical

private theorem not_isSecant_C_X_mul_X_X : ¬ IsSecant k⟦X⟧⟦X⟧ ([C X * X, X] : List k⟦X⟧⟦X⟧) := by
  intro hbad
  have hmax : maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} :=
    TauCeti.PowerSeries.maximalIdeal_eq_span_C_X irreducible_X
  have hx_mem : (X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := hmax ▸ Ideal.subset_span (by simp)
  have h_eq_id : Ideal.ofList ([C X * X, X] : List k⟦X⟧⟦X⟧) = Ideal.span {X} := by
    refine le_antisymm (Ideal.span_le.mpr fun r hr ↦ ?_)
      (Ideal.span_le.mpr fun _ h ↦ h ▸ Ideal.subset_span (by simp))
    rcases (by simpa using hr : r = C X * X ∨ r = X) with rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · exact Ideal.subset_span rfl
  have hdim_bad := hbad.supportDim_add_length_eq
  rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _
      (by rw [h_eq_id, Submodule.ideal_span_singleton_smul])),
    supportDim_quotSMulTop_eq_one_of_reg k (fun _ _ ↦ mul_left_cancel₀ PowerSeries.X_ne_zero)
      hx_mem, supportDim_twoDim k] at hdim_bad
  exact absurd (by simpa using hdim_bad : (1 : WithBot ℕ∞) + 2 = 2) (by decide)

example :
    IsCMSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) ∧
      IsPStandard k⟦X⟧⟦X⟧ ([X, C X] : List k⟦X⟧⟦X⟧) ∧
      IsSecant k⟦X⟧⟦X⟧ ([C X * X] : List k⟦X⟧⟦X⟧) ∧
      ¬ IsSecant k⟦X⟧⟦X⟧ ([C X * X, X] : List k⟦X⟧⟦X⟧) ∧
      ∃ ys : List k⟦X⟧⟦X⟧,
        IsCMSecant k⟦X⟧⟦X⟧ ([C X] ++ ys) ∧ IsPStandard k⟦X⟧⟦X⟧ ([C X] ++ ys).reverse ∧
          Module.supportDim k⟦X⟧⟦X⟧
            (k⟦X⟧⟦X⟧ ⧸ Ideal.ofList ([C X] ++ ys) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧)) = 0 := by
  have hcm : Module.IsCohenMacaulay k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧ := TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hsec := isSecant_C_X k
  have hcm_sec : IsCMSecant k⟦X⟧⟦X⟧ ([C X, X] : List k⟦X⟧⟦X⟧) := hcm.isCMSecant_of_isSecant hsec
  have hdim_q : Module.supportDim k⟦X⟧⟦X⟧
      (k⟦X⟧⟦X⟧ ⧸ Ideal.ofList ([C X, X] : List k⟦X⟧⟦X⟧) • (⊤ : Submodule k⟦X⟧⟦X⟧ k⟦X⟧⟦X⟧)) = 0 :=
    ENat.WithBot.add_one_cancel.mp <| ENat.WithBot.add_one_cancel.mp <| by
      simpa [add_assoc, one_add_one_eq_two, supportDim_twoDim k] using hsec.supportDim_add_length_eq
  -- Complete the single parameter `[C X]` to a full CM-secant / reversed `p`-standard sequence.
  have hmax : maximalIdeal k⟦X⟧⟦X⟧ = Ideal.span {C X, X} :=
    TauCeti.PowerSeries.maximalIdeal_eq_span_C_X irreducible_X
  have hcx_mem : (C X : k⟦X⟧⟦X⟧) ∈ maximalIdeal k⟦X⟧⟦X⟧ := hmax ▸ Ideal.subset_span (by simp)
  have hcx_reg : IsSMulRegular k⟦X⟧⟦X⟧ (C X : k⟦X⟧⟦X⟧) := fun _ _ hab ↦
    mul_left_cancel₀ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr PowerSeries.X_ne_zero) hab
  have hcm_cx : IsCMSecant k⟦X⟧⟦X⟧ ([C X] : List k⟦X⟧⟦X⟧) := hcm.isCMSecant_of_isSecant
    (isSecant_singleton_iff.mpr ⟨hcx_mem, by
      rw [supportDim_quotSMulTop_eq_one_of_reg k hcx_reg hcx_mem, supportDim_twoDim k]; decide⟩)
  obtain ⟨ys, hcm_ext, hdim0⟩ := hcm_cx.exists_append_supportDim_eq_zero
  exact ⟨hcm_sec, by simpa using (isCMSecant_iff_isPStandard_reverse hdim_q.le).mp hcm_sec,
    by simpa using hsec.take_append_mul (i := 0) (j := 1) (by omega) (by simp),
    not_isSecant_C_X_mul_X_X k, ys, hcm_ext,
    (isCMSecant_iff_isPStandard_reverse hdim0.le).mp hcm_ext, hdim0⟩

end TwoDimPowerSeries

section NonCohenMacaulay

open _root_.PowerSeries TrivSqZeroExt

variable (k : Type u) [Field k]

local notation "κ" => k⟦X⟧ ⧸ maximalIdeal k⟦X⟧
local notation "S" => TrivSqZeroExt k⟦X⟧ κ

private theorem mul_inr_eq_zero {t : S} (ht : t ∈ maximalIdeal S) (b : κ) : t * inr b = 0 := by
  rw [TrivSqZeroExt.mem_maximalIdeal_iff] at ht
  refine TrivSqZeroExt.ext (by simp) ?_
  rw [snd_mul, fst_inr, snd_inr, snd_zero]; simp only [MulOpposite.op_zero, zero_smul, add_zero]
  induction b using Submodule.Quotient.induction_on with | H a =>
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right a _ ht)

private theorem mem_primaryComponent_trivSqZeroExt_iff (s : S) :
    s ∈ (maximalIdeal S).primaryComponent S ↔ s.fst = 0 := by
  rw [Ideal.primaryComponent_mem]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun hfst ↦ ⟨1, by
    rw [pow_one, Submodule.mem_torsionBySet_iff]; rintro ⟨t, ht⟩
    have hs : s = inr s.snd := TrivSqZeroExt.ext (by simp [hfst]) (by simp)
    exact hs ▸ mul_inr_eq_zero k ht s.snd⟩⟩
  rw [Submodule.mem_torsionBySet_iff] at hn
  have hy_mem : (inl X : S) ∈ maximalIdeal S := TrivSqZeroExt.mem_maximalIdeal_iff.mpr
    (maximalIdeal_eq_span_X (k := k) ▸ Ideal.subset_span rfl)
  have h0 : (inl X : S) ^ n * s = 0 := hn ⟨(inl X : S) ^ n, Ideal.pow_mem_pow hy_mem n⟩
  have hfst : (X : k⟦X⟧) ^ n * s.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h0
  exact (mul_eq_zero.mp hfst).resolve_left (pow_ne_zero n PowerSeries.X_ne_zero)

private theorem annihilatorProduct_trivSqZeroExt_one :
    localCohomology.annihilatorProduct (maximalIdeal S) S 1 = maximalIdeal S := by
  rw [localCohomology.annihilatorProduct_one_eq_annihilator_primaryComponent]
  ext t; rw [Module.mem_annihilator]
  refine ⟨fun ht ↦ ?_, fun ht ⟨s, hs⟩ ↦ Subtype.ext ?_⟩
  · have h0 : (t * (inr 1 : S)).snd = 0 := congrArg (fun x ↦ x.val.snd)
      (ht ⟨inr 1, (mem_primaryComponent_trivSqZeroExt_iff k _).mpr rfl⟩)
    rw [snd_mul, fst_inr, snd_inr] at h0
    exact TrivSqZeroExt.mem_maximalIdeal_iff.mpr <| Ideal.Quotient.eq_zero_iff_mem.mp <| by
      simpa [Algebra.smul_def] using h0
  · have hs' : s = inr s.snd := TrivSqZeroExt.ext
      (by simp [(mem_primaryComponent_trivSqZeroExt_iff k s).mp hs]) (by simp)
    rw [SetLike.val_smul, smul_eq_mul, Submodule.coe_mk, ZeroMemClass.coe_zero, hs']
    exact mul_inr_eq_zero k ht s.snd

private theorem supportDim_quotSMulTop_trivSqZeroExt_nonpos {z : S}
    (hzy : ∀ p : Ideal S, p.IsPrime → z ∈ p → (inl X : S) ∈ p) :
    Module.supportDim S (QuotSMulTop z S) ≤ 0 := by
  have key : ∀ p ∈ Module.support S (QuotSMulTop z S), p.asIdeal = maximalIdeal S := fun p hp ↦ by
    rw [Module.support_quotSMulTop] at hp
    have hyp : (inl X : S) ∈ p.asIdeal := hzy p.asIdeal p.isPrime (by simpa using hp.2)
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) fun s hs ↦ ?_
    have hsfst : s.fst ∈ Ideal.span {(X : k⟦X⟧)} := by
      rw [← maximalIdeal_eq_span_X]; exact TrivSqZeroExt.mem_maximalIdeal_iff.mp hs
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hsfst
    have hinr_p : inr s.snd ∈ p.asIdeal :=
      p.isPrime.mem_of_pow_mem 2 (by rw [sq, inr_mul_inr]; exact p.asIdeal.zero_mem)
    have hs_eq : s = inl r * (inl X : S) + inr s.snd :=
      TrivSqZeroExt.ext (by simp [hr, mul_comm]) (by simp)
    exact hs_eq ▸ p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hyp) hinr_p
  have : Subsingleton (Module.support S (QuotSMulTop z S)) := ⟨fun p q ↦
    Subtype.ext (PrimeSpectrum.ext ((key p.val p.property).trans (key q.val q.property).symm))⟩
  exact Order.krullDim_nonpos_of_subsingleton

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
  -- Dimension and failure of Cohen–Macaulayness on `S`.
  have hdimA : ringKrullDim k⟦X⟧ = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one k⟦X⟧
  have hdimS : Module.supportDim S S = 1 := by
    rw [Module.supportDim_self_eq_ringKrullDim, TrivSqZeroExt.ringKrullDim_eq, hdimA]
  have hκ : depth (ModuleCat.of k⟦X⟧ κ) = 0 := depth_eq_zero_iff_nontrivial_linearMap.mpr
    ⟨⟨LinearMap.id, 0, fun h ↦ by simpa using LinearMap.congr_fun h 1⟩⟩
  have hnotCM : ¬ Module.IsCohenMacaulay S S :=
    TrivSqZeroExt.not_isCohenMacaulay hκ (by rw [hdimA]; decide)
  -- Parameter quotients by `y` and `y'` are zero-dimensional, hence Cohen–Macaulay.
  have hx_mem : (X : k⟦X⟧) ∈ maximalIdeal k⟦X⟧ :=
    maximalIdeal_eq_span_X (k := k) ▸ Ideal.subset_span rfl
  have hy_mem : y ∈ maximalIdeal S := TrivSqZeroExt.mem_maximalIdeal_iff.mpr hx_mem
  have hy'_mem : y' ∈ maximalIdeal S :=
    TrivSqZeroExt.mem_maximalIdeal_iff.mpr (by simpa [y'] using hx_mem)
  have hdim_y : Module.supportDim S (QuotSMulTop y S) ≤ 0 :=
    supportDim_quotSMulTop_trivSqZeroExt_nonpos k fun _ _ h ↦ h
  have hdim_y' : Module.supportDim S (QuotSMulTop y' S) ≤ 0 := by
    refine supportDim_quotSMulTop_trivSqZeroExt_nonpos k fun p hp hpy' ↦ hp.mem_of_pow_mem 2 ?_
    have hsq : y' ^ 2 = y ^ 2 := by
      calc (y + inr 1) ^ 2 = y ^ 2 + 2 * (y * inr 1) + inr 1 * inr 1 := by ring
        _ = y ^ 2 := by rw [mul_inr_eq_zero k hy_mem 1, inr_mul_inr, mul_zero, add_zero, add_zero]
    exact hsq ▸ p.pow_mem_of_mem hpy' 2 (by decide)
  -- Assemble secancy, CM-secancy, and `p`-standardness for `[y]` and `[y']`.
  have hann := annihilatorProduct_trivSqZeroExt_one k
  have hsec_y : IsSecant S [y] :=
    isSecant_singleton_iff.mpr ⟨hy_mem, hdim_y.trans_lt (by rw [hdimS]; decide)⟩
  have hcm_y : IsCMSecant S [y] := isCMSecant_singleton_iff.mpr
    ⟨hsec_y, Module.isCohenMacaulay_of_supportDim_nonpos hdim_y, 1, hdimS,
      by rw [hann]; exact hy_mem⟩
  have hcm_y' : IsCMSecant S [y'] := isCMSecant_singleton_iff.mpr
    ⟨isSecant_singleton_iff.mpr ⟨hy'_mem, hdim_y'.trans_lt (by rw [hdimS]; decide)⟩,
      Module.isCohenMacaulay_of_supportDim_nonpos hdim_y', 1, hdimS, by rw [hann]; exact hy'_mem⟩
  have hnotreg : ¬ IsSMulRegular S y := fun hreg ↦ one_ne_zero <| congrArg TrivSqZeroExt.snd <|
    hreg (by simpa [smul_eq_mul] using mul_inr_eq_zero k hy_mem 1 : y • (inr 1 : S) = y • (0 : S))
  have h_yl : Module.supportDim S (S ⧸ Ideal.ofList [y] • (⊤ : Submodule S S)) ≤ 0 := by
    rwa [Module.supportDim_eq_of_equiv (Submodule.quotOfListSingletonSMulTopEquiv S y)]
  have h_y'l : Module.supportDim S (S ⧸ Ideal.ofList [y'] • (⊤ : Submodule S S)) ≤ 0 := by
    rwa [Module.supportDim_eq_of_equiv (Submodule.quotOfListSingletonSMulTopEquiv S y')]
  exact ⟨hnotCM, fun h ↦ hnotCM (isCMSecant_nil_iff.mp h), hann,
    by rw [hann]; exact (maximalIdeal.isMaximal _).ne_top, hnotreg, hsec_y, hcm_y,
    (isCMSecant_iff_isPStandard_reverse h_yl).mp hcm_y, hcm_y',
    (isCMSecant_iff_isPStandard_reverse h_y'l).mp hcm_y'⟩

end NonCohenMacaulay
