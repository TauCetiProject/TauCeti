/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.RingTheory.Cyclotomic.ComplexField
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree

/-!
# The completions of `ℚ(ζ₃)` at the places over `7` are `ℚ₇`

Let `F = ℚ(ζ₃) = complexField 3`. Since `7` does not divide `3`, the prime `7` is unramified in
`F`, and its residue degree is the order of `7` modulo `3`, which is `1`. By the local degree
formula `[F_w : ℚ_7] = e(w ∣ 7) f(w ∣ 7)`, every place `w` of `F` over `7` has local degree `1`:
the completion map from the `7`-adic completion of `ℚ` to `F_w` is bijective, and `F_w ≅ ℚ₇`.
-/

public section

open IsDedekindDomain NumberField HeightOneSpectrum TauCeti.Cyclotomic
open scoped AdicCompletionExtension

namespace TauCeti.Examples.CyclotomicCompletionSevenPadic

local notation "F" => complexField 3

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The prime `7` as a place of `ℚ`, the height-one prime of `ℤ` matching `7` under
`Rat.HeightOneSpectrum.primesEquiv`. -/
noncomputable abbrev placeSeven : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩

private theorem seven_mem_placeSeven : (7 : ℤ) ∈ placeSeven.asIdeal := by
  have hgen : Rat.HeightOneSpectrum.natGenerator placeSeven = 7 :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply _)
  have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff placeSeven (n := 7)).1 (hgen ▸ dvd_rfl)
  rw [Ideal.mem_map_of_equiv] at h
  obtain ⟨x, hx, hx7⟩ := h
  -- The only ring automorphism of `ℤ` is the identity.
  have hx' : Rat.IsIntegralClosure.intEquiv ℤ x = x := by simp
  have : x = 7 := by exact_mod_cast hx'.symm.trans hx7
  exact this ▸ hx

/-- Two proper ideals of `ℤ` containing `7` both equal `(7)`. -/
private theorem eq_span_seven {I : Ideal ℤ} (hI : I ≠ ⊤) (h7 : (7 : ℤ) ∈ I) :
    I = Ideal.span {(7 : ℤ)} := by
  have hmax : (Ideal.span {((7 : ℕ) : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 7
  push_cast at hmax
  exact (hmax.eq_of_le hI ((Ideal.span_singleton_le_iff_mem I).2 h7)).symm

/-- A place of `F` containing `7` lies over the place `7` of `ℚ`. -/
theorem liesOver_placeSeven (w : HeightOneSpectrum (𝓞 F)) (hw : ((7 : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    w.asIdeal.LiesOver placeSeven.asIdeal := by
  refine ⟨?_⟩
  rw [eq_span_seven (Ideal.IsPrime.ne_top inferInstance) seven_mem_placeSeven]
  refine (eq_span_seven (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  rw [Ideal.mem_comap]
  exact_mod_cast hw

variable (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver placeSeven.asIdeal]

/-- **At each place over `7` the local degree of `F` is `1`.** -/
theorem finrank_adicCompletion_eq_one :
    Module.finrank (placeSeven.adicCompletion ℚ) (w.adicCompletion F) = 1 := by
  have : w.asIdeal.LiesOver (Ideal.span {((7 : ℕ) : ℤ)}) := by
    have h := Ideal.LiesOver.over (P := w.asIdeal) (p := placeSeven.asIdeal)
    rw [eq_span_seven (Ideal.IsPrime.ne_top inferInstance) seven_mem_placeSeven] at h
    exact ⟨by push_cast; exact h⟩
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have h73 : ¬ 7 ∣ 3 := by norm_num
  rw [finrank_adicCompletion,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd 7 F w.asIdeal h73,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd 7 F w.asIdeal h73]
  have h : ((7 : ℕ) : ZMod 3) = 1 := by decide
  rw [h, orderOf_one]

/-- **At each place over `7` the completion map from `ℚ_7` to `F_w` is bijective.** -/
theorem bijective_adicCompletionExtension :
    Function.Bijective (adicCompletionExtension ℚ F placeSeven w) := by
  rw [← algebraMap_adicCompletionExtensionAlgebra]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.1 (finrank_adicCompletion_eq_one w)

omit [w.asIdeal.LiesOver placeSeven.asIdeal] in
/-- **At each place over `7` the completion of `F` is `ℚ₇`.** -/
theorem nonempty_ringEquiv_padic (hw : ((7 : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    Nonempty (w.adicCompletion F ≃+* ℚ_[7]) := by
  have := liesOver_placeSeven w hw
  exact ⟨(RingEquiv.ofBijective _ (bijective_adicCompletionExtension w)).symm.trans
    (RingEquivClass.toRingEquiv (Padic.adicCompletionEquiv ℤ ⟨7, Nat.prime_seven⟩)).symm⟩

end TauCeti.Examples.CyclotomicCompletionSevenPadic
