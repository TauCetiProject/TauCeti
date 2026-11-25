/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Cyclotomic.ResidueDegree
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Completely split primes after adjoining roots of unity

If a rational prime `q` splits completely in `F` and is one modulo `m`, it still splits
completely in `F(μₘ)`. At each prime of `F` above `q`, the residue degree in the cyclotomic
extension is the order of `q` modulo `m`. The ramification index is one since `q` is prime to
the level. These local computations apply even when `F` is not Galois over the rationals.
-/

public section

open NumberField Ideal Module IsCyclotomicExtension

/-- A completely split prime congruent to one modulo `m` remains completely split after
adjoining the `m`-th roots of unity. -/
theorem IsCyclotomicExtension.ncard_primesOver_eq_finrank_of_modEq_one
    {F : Type*} [Field F] [NumberField F] (E : Type*) [Field E] [NumberField E] [Algebra F E]
    {m q : ℕ} [IsCyclotomicExtension {m} F E] [hq : Fact q.Prime]
    (hsplit : ((span {(q : ℤ)}).primesOver (𝓞 F)).ncard = finrank ℚ F)
    (hmod : q ≡ 1 [MOD m]) :
    ((span {(q : ℤ)}).primesOver (𝓞 E)).ncard = finrank ℚ E := by
  have hcop : q.Coprime m := Nat.coprime_of_mul_modEq_one 1 (by simpa using hmod)
  have : NeZero m := ⟨fun hm ↦ hq.out.ne_one (by simpa [hm] using hcop)⟩
  have : IsGalois F E := isGalois {m} F E
  rw [← RingOfIntegers.rank,
    ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one]
  rintro Q ⟨hQ, hover⟩
  have hQ0 := ne_bot_of_liesOver_of_ne_bot (p := span {(q : ℤ)}) (by simpa using hq.out.ne_zero) Q
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨Q.under (𝓞 F), inferInstance, Ideal.IsIntegral.under_ne_bot _ hQ0⟩
  have : Q.LiesOver P.asIdeal := Ideal.over_under Q
  have hn : absNorm P.asIdeal = q :=
    absNorm_eq_of_ncard_primesOver_eq_finrank (Q.under (𝓞 F)) hsplit
  have hm : (m : 𝓞 F) ∉ P.asIdeal :=
    natCast_notMem_of_coprime_absNorm P.isPrime.ne_top (hn ▸ hcop.symm)
  have := isUnramifiedAt_of_natCast_notMem E m hm Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt F Q hQ0
  have hf := (zeta_spec m F E).inertiaDeg_eq_orderOf_of_val_eq_absNorm P hm Q hσ 1
    (by simpa [hn] using ((ZMod.natCast_eq_natCast_iff q 1 m).mpr hmod).symm)
  obtain ⟨he₀, hf₀⟩ := ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
    (span {(q : ℤ)}) (Q.under (𝓞 F)) (by rwa [RingOfIntegers.rank])
  rw [ramificationIdx_tower (Q.under (𝓞 F)) Q, inertiaDeg_tower (Q.under (𝓞 F)) Q,
    he₀, hf₀, hf, Q.ramificationIdx_eq_one (𝓞 F), orderOf_one]
  simp
