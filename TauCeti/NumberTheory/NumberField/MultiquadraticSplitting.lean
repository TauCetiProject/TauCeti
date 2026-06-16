/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import TauCeti.NumberTheory.Multiquadratic.Galois
import TauCeti.NumberTheory.NumberField.SplitsCompletely

/-!
# The prime-splitting law for a multiquadratic field

For a multiquadratic number field `K = ℚ(√d₁, …, √dₙ)` and an odd prime `p` dividing none of the
radicands, `p` splits completely in `K` if and only if every `dᵢ` is a quadratic residue mod `p`.

This is the general (compositum) case; the base case `n = 1` is `ncard_primesOver_quadratic_iff`.
The reduction to the residue field of a single prime `Q` above `p` rests on the decomposition-group
criterion `ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot`.
-/

open Polynomial NumberField Ideal Module MulAction
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The multiquadratic splitting law.** For `K = ℚ(√d₁, …, √dₙ)` generated over `ℚ` by square
roots `r i` of integers `d i`, and an odd prime `p` dividing none of the `d i`, `p` splits
completely in `K` iff every `d i` is a quadratic residue mod `p`. -/
theorem ncard_primesOver_multiquadratic_iff {ι : Type*} [Finite ι] (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔
      ∀ i, legendreSym p (d i) = 1 := by
  -- `K` is Galois over `ℚ`: transport the multiquadratic `isGalois` along `htop`.
  have hr' : ∀ i, r i ^ 2 = algebraMap ℚ K ((d i : ℚ)) := by
    intro i; rw [hr i]; simp
  haveI : IsGalois ℚ K := by
    have hg := TauCeti.Multiquadratic.isGalois (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr'
    rw [htop] at hg
    exact isGalois_iff_isGalois_top.mp hg
  -- Fix a prime `Q` of `𝓞 K` above `p`.
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp Fact.out))
      (by simpa [Ideal.span_singleton_eq_bot] using hpne)
  obtain ⟨Q, hQp, hQo⟩ : ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧ Q.LiesOver (span {(p : ℤ)}) := by
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 K)))
    exact ⟨Q, hQ⟩
  haveI := hQp
  haveI := hQo
  -- Each `r i` is integral (a root of the monic `X² - d i`), so it lifts to `R i : 𝓞 K`.
  have hintr : ∀ i, IsIntegral ℤ (r i) := fun i =>
    ⟨X ^ 2 - C (d i), monic_X_pow_sub_C (d i) (by norm_num), by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr i, sub_self]⟩
  set R : ι → 𝓞 K := fun i => ⟨r i, hintr i⟩ with hRdef
  -- `R i` is `r i` under `𝓞 K ↪ K` (definitionally), so `(R i)² = d i` in `𝓞 K`.
  have hRK : ∀ i, algebraMap (𝓞 K) K (R i) = r i := fun _ => rfl
  have hRsq : ∀ i, R i ^ 2 = algebraMap ℤ (𝓞 K) (d i) := fun i => by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_pow, hRK i, hr i, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  -- `Q` lies over `span {p}`, so `algebraMap m ∈ Q ↔ p ∣ m` (`Q.under ℤ = span {p}` definitionally
  -- unfolds the left side to membership in the comap).
  have hmemQ : ∀ m : ℤ, algebraMap ℤ (𝓞 K) m ∈ Q ↔ (p : ℤ) ∣ m := fun m => by
    have hunder : Q.under ℤ = span {(p : ℤ)} := by symm; exact hQo.over
    change m ∈ Q.under ℤ ↔ (p : ℤ) ∣ m
    rw [hunder, Ideal.mem_span_singleton]
  refine ⟨fun hsplit i => ?_, fun hqr => ?_⟩
  · -- Forward: complete splitting forces residue degree `1`, so `𝓞 K ⧸ Q` is the prime field.
    rw [ncard_primesOver_eq_finrank_iff K p] at hsplit
    have hfQ : finrank (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) = 1 := by
      rw [← Ideal.inertiaDeg_algebraMap (p := span {(p : ℤ)}) (P := Q),
        ← Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) Q (K ≃ₐ[ℚ] K)]
      exact hsplit.2
    letI fld : Field (ℤ ⧸ span {(p : ℤ)}) := Ideal.Quotient.field _
    -- A one-dimensional algebra over a field is free, so `finrank = 1 ⟹ algebraMap` is bijective.
    haveI : Module.Free (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) :=
      @Module.Free.of_divisionRing _ _ fld.toDivisionRing _ _
    have hbij := (Algebra.finrank_eq_one_iff_bijective_algebraMap
      (F := ℤ ⧸ span {(p : ℤ)}) (E := 𝓞 K ⧸ Q)).mp hfQ
    -- Lift the residue of `R i` to an integer `a`, so `R i ≡ a (mod Q)`.
    obtain ⟨c, hc⟩ := hbij.surjective (Ideal.Quotient.mk Q (R i))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    -- The algebra map `ℤ ⧸ (p) → 𝓞 K ⧸ Q` is `Ideal.quotientMap`, which sends `mk a` to
    -- `mk (algebraMap ℤ (𝓞 K) a)`.
    have hcompat : algebraMap (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) (Ideal.Quotient.mk _ a)
        = Ideal.Quotient.mk Q (algebraMap ℤ (𝓞 K) a) := Ideal.quotientMap_mk
    rw [hcompat] at hc
    have hdiff : algebraMap ℤ (𝓞 K) a - R i ∈ Q := Ideal.Quotient.eq.mp hc
    -- `(algebraMap a - R i)(algebraMap a + R i) = algebraMap (a² - d i) ∈ Q`, so `p ∣ a² - d i`.
    have hpd : (p : ℤ) ∣ a ^ 2 - d i := by
      rw [← hmemQ]
      have hfac : algebraMap ℤ (𝓞 K) (a ^ 2 - d i) =
          (algebraMap ℤ (𝓞 K) a - R i) * (algebraMap ℤ (𝓞 K) a + R i) := by
        rw [map_sub, map_pow, ← hRsq i]; ring
      rw [hfac]
      exact Ideal.mul_mem_right _ _ hdiff
    rw [legendreSym.eq_one_iff p (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop i)]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpd
    push_cast at hpd
    exact ⟨(a : ZMod p), by linear_combination -hpd⟩
  · -- Backward: every element `σ` of the decomposition group of `Q` is the identity.
    rw [ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot K Q, eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    -- The Galois action on `𝓞 K` is the restriction of the action on `K`, so it lifts `σ`
    -- (its coercion is `σ` of the coercion, definitionally) and fixes `Q` setwise.
    have hact : ∀ x : 𝓞 K, algebraMap (𝓞 K) K (σ • x) = σ (algebraMap (𝓞 K) K x) :=
      fun _ => rfl
    have hstab : σ • Q = Q := mem_stabilizer_iff.mp hσ
    have hmapQ : ∀ x ∈ Q, σ • x ∈ Q := by
      intro x hx; rw [← hstab]; exact Ideal.smul_mem_pointwise_smul σ x Q hx
    -- `σ` fixes every generator `r i`: `σ (r i) = ± r i`, and the `-` sign forces `p ∣ d i`.
    have hfix : ∀ i, σ (r i) = r i := by
      intro i
      have h2 : σ (r i) ^ 2 = r i ^ 2 := by rw [← map_pow, hr' i, AlgEquiv.commutes]
      have hfac : (σ (r i) - r i) * (σ (r i) + r i) = 0 := by
        have h1 : (σ (r i) - r i) * (σ (r i) + r i) = σ (r i) ^ 2 - r i ^ 2 := by ring
        rw [h1, h2, sub_self]
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exfalso
        have hflip : σ (r i) = - r i := eq_neg_of_add_eq_zero_left h
        -- `d i` is a residue: `a² ≡ d i (mod p)` with `p ∤ a`.
        obtain ⟨b, hb⟩ := (legendreSym.eq_one_iff p (by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop i)).mp (hqr i)
        obtain ⟨a, rfl⟩ := ZMod.intCast_surjective b
        have hpa : (p : ℤ) ∣ a ^ 2 - d i := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hb]; ring
        have hpa' : ¬ (p : ℤ) ∣ a := fun hd => hcop i (by
          have h2a : (p : ℤ) ∣ a ^ 2 := dvd_pow hd (by norm_num)
          have h3 := dvd_sub h2a hpa
          rwa [show a ^ 2 - (a ^ 2 - d i) = d i by ring] at h3)
        set A : 𝓞 K := algebraMap ℤ (𝓞 K) a with hAdef
        -- `(R i - A)(R i + A) = d i - a² ∈ Q`, so one factor lies in the prime `Q`.
        have hAsq : A ^ 2 = algebraMap ℤ (𝓞 K) (a ^ 2) := by rw [hAdef, ← map_pow]
        have heq : (R i - A) * (R i + A) = algebraMap ℤ (𝓞 K) (d i - a ^ 2) := by
          have h1 : (R i - A) * (R i + A) = R i ^ 2 - A ^ 2 := by ring
          rw [h1, hRsq i, hAsq, ← map_sub]
        have hfacQ : (R i - A) * (R i + A) ∈ Q := by
          rw [heq]; exact (hmemQ _).mpr (dvd_sub_comm.mp hpa)
        -- `σ` sends `R i ↦ -R i` and fixes the integer `A`.
        have hsR : σ • R i = - R i := by
          apply FaithfulSMul.algebraMap_injective (𝓞 K) K
          rw [hact, map_neg, hRK, hflip]
        have hsA : σ • A = A := by
          apply FaithfulSMul.algebraMap_injective (𝓞 K) K
          rw [hact, hAdef, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
            IsScalarTower.algebraMap_apply ℤ ℚ K, AlgEquiv.commutes]
        -- Applying `σ` to whichever factor lies in `Q` and adding the two gives `2 A ∈ Q`.
        have h2A : (2 : 𝓞 K) * A ∈ Q := by
          rcases hQp.mem_or_mem hfacQ with hca | hca
          · have h1 : σ • (R i - A) ∈ Q := hmapQ _ hca
            rw [smul_sub, hsR, hsA] at h1
            have hs := Q.add_mem hca h1
            rw [show (R i - A) + (-R i - A) = -(2 * A) by ring] at hs
            exact neg_mem_iff.mp hs
          · have h1 : σ • (R i + A) ∈ Q := hmapQ _ hca
            rw [smul_add, hsR, hsA] at h1
            have hs := Q.add_mem hca h1
            rw [show (R i + A) + (-R i + A) = 2 * A by ring] at hs
            exact hs
        -- `2 A = algebraMap (2 a) ∈ Q` forces `p ∣ 2 a`, hence (as `p` is odd) `p ∣ a` — absurd.
        have h2a : algebraMap ℤ (𝓞 K) (2 * a) ∈ Q := by
          rw [map_mul, show algebraMap ℤ (𝓞 K) 2 = 2 by norm_num, ← hAdef]; exact h2A
        have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
        rcases hpint.dvd_mul.mp ((hmemQ _).mp h2a) with h2 | ha
        · exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h2))
        · exact hpa' ha
    -- `σ` fixes `ℚ` and every `r i`, which generate `K = ℚ(rᵢ)`, so `σ = 1`.
    refine AlgEquiv.ext fun x => ?_
    rw [AlgEquiv.one_apply]
    have hx : x ∈ (⊤ : IntermediateField ℚ K) := IntermediateField.mem_top
    rw [← htop] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hfix i
    | algebraMap q => exact AlgEquiv.commutes σ q
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

end TauCeti.NumberField
