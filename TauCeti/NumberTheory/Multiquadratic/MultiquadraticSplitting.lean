/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import TauCeti.NumberTheory.Multiquadratic.Galois
public import TauCeti.NumberTheory.NumberField.SplitsCompletely

/-!
# The prime-splitting law for a multiquadratic field

For a multiquadratic number field `K = ℚ(√d₁, …, √dₙ)` and an odd prime `p` dividing none of the
radicands, `p` splits completely in `K` if and only if every `dᵢ` is a quadratic residue mod `p`.

This is the general (compositum) case; the base case `n = 1` is `ncard_primesOver_quadratic_iff`.

## Main results

* `TauCeti.NumberField.ncard_primesOver_multiquadratic_iff`: the multiquadratic prime-splitting
  law — `p` splits completely in `K = ℚ(√d₁, …, √dₙ)` iff every `dᵢ` is a quadratic residue
  mod `p`.
-/

open Polynomial NumberField Ideal Module MulAction
open scoped Pointwise

namespace TauCeti.NumberField

public section

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Each generator `r i` is integral over `ℤ`. -/
private theorem mq_isIntegral_gen {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (i : ι) : IsIntegral ℤ (r i) :=
  -- `r i` is a root of the monic `X² - d i`.
  ⟨X ^ 2 - C (d i), monic_X_pow_sub_C (d i) (by norm_num), by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr i, sub_self]⟩

/-- The generator `r i`, as an element of the ring of integers `𝓞 K`. -/
private noncomputable def ringGen {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (i : ι) : 𝓞 K :=
  ⟨r i, mq_isIntegral_gen d r hr i⟩

omit [NumberField K] in
/-- Under `𝓞 K ↪ K`, `ringGen d r hr i` maps to the generator `r i`. -/
private theorem algebraMap_ringGen {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (i : ι) :
    algebraMap (𝓞 K) K (ringGen d r hr i) = r i :=
  -- `ringGen d r hr i = ⟨r i, _⟩`, so its image is the definitional coercion back to `K`
  -- (cf. `RingOfIntegers.coe_mk`).
  rfl

omit [NumberField K] in
/-- `ringGen` squares to the radicand `d i` in `𝓞 K`. -/
private theorem ringGen_sq {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (i : ι) :
    ringGen d r hr i ^ 2 = algebraMap ℤ (𝓞 K) (d i) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_pow, algebraMap_ringGen, hr i, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]

omit [NumberField K] in
/-- For an ideal `Q` lying over the integer ideal `(a)`, an integer `m` maps into `Q` under
`algebraMap ℤ (𝓞 K)` iff `a ∣ m`. -/
private theorem algebraMap_int_mem_iff_dvd_of_liesOver {a : ℤ}
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {a})] (m : ℤ) :
    algebraMap ℤ (𝓞 K) m ∈ Q ↔ a ∣ m :=
  (Ideal.mem_of_liesOver Q (span {a}) m).symm.trans Ideal.mem_span_singleton

/-- Forward direction (pointwise): for `K` Galois over `ℚ`, if `p` splits completely
(`#{primes over p} = [K : ℚ]`) and `p ∤ d i`, then `d i` is a quadratic residue mod `p`. -/
private theorem legendreSym_eq_one_of_ncard_primesOver_eq_finrank {ι : Type*} (d : ι → ℤ)
    (r : ι → K) (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) [IsGalois ℚ K]
    {p : ℕ} [Fact p.Prime] {i : ι} (hcop_i : ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (hsplit : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K) :
    legendreSym p (d i) = 1 := by
  -- Complete splitting forces residue degree `1`, so `𝓞 K ⧸ Q` is the prime field `ℤ ⧸ (p)`;
  -- lifting the residue of `r i` to an integer `a` gives `a² ≡ d i (mod p)`.
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp Fact.out))
      (by simpa [Ideal.span_singleton_eq_bot] using hpne)
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (span {(p : ℤ)})
  let R : ι → 𝓞 K := ringGen d r hr
  rw [ncard_primesOver_eq_finrank_iff K p] at hsplit
  have hfQ : finrank (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) = 1 := by
    rw [← Ideal.inertiaDeg'_eq_of_isMaximal (p := span {(p : ℤ)}) (q := Q),
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
    rw [← algebraMap_int_mem_iff_dvd_of_liesOver Q]
    have hfac : algebraMap ℤ (𝓞 K) (a ^ 2 - d i) =
        (algebraMap ℤ (𝓞 K) a - R i) * (algebraMap ℤ (𝓞 K) a + R i) := by
      rw [map_sub, map_pow, ← ringGen_sq d r hr i]; ring
    rw [hfac]
    exact Ideal.mul_mem_right _ _ hdiff
  rw [legendreSym.eq_one_iff p (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop_i)]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpd
  push_cast at hpd
  exact ⟨(a : ZMod p), by linear_combination -hpd⟩

/-- Backward core (pointwise): for `K` Galois over `ℚ`, if `p` is odd, `p ∤ d i`, and `d i` is a
quadratic residue mod `p`, then every `σ` in the decomposition group of `Q` fixes the generator
`r i`. -/
private theorem decompositionGroup_fixes_gen {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) [IsGalois ℚ K]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {i : ι} (hcop_i : ¬ (p : ℤ) ∣ d i)
    (hqr_i : legendreSym p (d i) = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ stabilizer (K ≃ₐ[ℚ] K) Q) : σ (r i) = r i := by
  -- From `σ (r i)² = r i²` we get `σ (r i) = ± r i`; the `-` sign, combined with a residue
  -- `a² ≡ d i (mod p)`, would force `2 a ∈ Q` and hence `p ∣ 2 a`, contradicting `p` odd and
  -- `p ∤ a`.
  have hr' : ∀ i, r i ^ 2 = algebraMap ℚ K ((d i : ℚ)) := by
    intro i; rw [hr i]; simp
  let R : ι → 𝓞 K := ringGen d r hr
  -- The Galois action on `𝓞 K` is the restriction of the action on `K`: it agrees with
  -- `galRestrict ℤ ℚ K (𝓞 K) σ` (both restrict `σ` and are pinned by injectivity of the algebra
  -- map), so compatibility is `algebraMap_galRestrict_apply`.
  have hgal : ∀ x : 𝓞 K, galRestrict ℤ ℚ K (𝓞 K) σ x = σ • x := fun x => by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [algebraMap_galRestrict_apply (A := ℤ) σ x]
    -- The remaining equality is the definitional agreement between the integral-closure action
    -- `σ • x = ⟨σ • (x : K), _⟩` and `σ` acting on `K`; `integralClosure.coe_smul` names it.
    exact (integralClosure.coe_smul σ x).symm
  have hact : ∀ x : 𝓞 K, algebraMap (𝓞 K) K (σ • x) = σ (algebraMap (𝓞 K) K x) := fun x => by
    rw [← hgal x, algebraMap_galRestrict_apply (A := ℤ) σ x]
  have hstab : σ • Q = Q := mem_stabilizer_iff.mp hσ
  have hmapQ : ∀ x ∈ Q, σ • x ∈ Q := by
    intro x hx; rw [← hstab]; exact Ideal.smul_mem_pointwise_smul σ x Q hx
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
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop_i)).mp hqr_i
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective b
    have hpa : (p : ℤ) ∣ a ^ 2 - d i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hb]; ring
    have hpa' : ¬ (p : ℤ) ∣ a := fun hd => hcop_i (by
      have h2a : (p : ℤ) ∣ a ^ 2 := dvd_pow hd (by norm_num)
      have h3 := dvd_sub h2a hpa
      -- `a² - (a² - d i) = d i`, so `p ∣ d i`, contradicting `hcop_i`.
      have hdiff : a ^ 2 - (a ^ 2 - d i) = d i := by ring
      rwa [hdiff] at h3)
    set A : 𝓞 K := algebraMap ℤ (𝓞 K) a with hAdef
    -- `(R i - A)(R i + A) = d i - a² ∈ Q`, so one factor lies in the prime `Q`.
    have hAsq : A ^ 2 = algebraMap ℤ (𝓞 K) (a ^ 2) := by rw [hAdef, ← map_pow]
    have heq : (R i - A) * (R i + A) = algebraMap ℤ (𝓞 K) (d i - a ^ 2) := by
      have h1 : (R i - A) * (R i + A) = R i ^ 2 - A ^ 2 := by ring
      rw [h1, ringGen_sq d r hr i, hAsq, ← map_sub]
    have hfacQ : (R i - A) * (R i + A) ∈ Q := by
      rw [heq]; exact (algebraMap_int_mem_iff_dvd_of_liesOver Q _).mpr (dvd_sub_comm.mp hpa)
    -- `σ` sends `R i ↦ -R i` and fixes the integer `A`.
    have hsR : σ • R i = - R i := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [hact, map_neg, algebraMap_ringGen, hflip]
    have hsA : σ • A = A := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [hact, hAdef, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
        IsScalarTower.algebraMap_apply ℤ ℚ K, AlgEquiv.commutes]
    -- Applying `σ` to whichever factor lies in `Q` and adding the two gives `2 A ∈ Q`.
    have h2A : (2 : 𝓞 K) * A ∈ Q := by
      rcases (‹Q.IsPrime›).mem_or_mem hfacQ with hca | hca
      · have h1 : σ • (R i - A) ∈ Q := hmapQ _ hca
        rw [smul_sub, hsR, hsA] at h1
        have hs := Q.add_mem hca h1
        -- Adding the factor `R i - A` and its image `-R i - A` cancels `R i`, leaving `-(2 A)`.
        have hsum : (R i - A) + (-R i - A) = -(2 * A) := by ring
        rw [hsum] at hs
        exact neg_mem_iff.mp hs
      · have h1 : σ • (R i + A) ∈ Q := hmapQ _ hca
        rw [smul_add, hsR, hsA] at h1
        have hs := Q.add_mem hca h1
        -- Adding the factor `R i + A` and its image `-R i + A` cancels `R i`, leaving `2 A`.
        have hsum : (R i + A) + (-R i + A) = 2 * A := by ring
        rw [hsum] at hs
        exact hs
    -- `2 A = algebraMap (2 a) ∈ Q` forces `p ∣ 2 a`, hence (as `p` is odd) `p ∣ a` — absurd.
    have h2a : algebraMap ℤ (𝓞 K) (2 * a) ∈ Q := by
      -- `algebraMap ℤ (𝓞 K) 2` is the numeral `2` in `𝓞 K`, so `2 A = algebraMap (2 a)`.
      have halg_two : algebraMap ℤ (𝓞 K) 2 = 2 := by norm_num
      rw [map_mul, halg_two, ← hAdef]
      exact h2A
    have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    rcases hpint.dvd_mul.mp ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h2a) with h2 | ha
    · exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h2))
    · exact hpa' ha

/-- Backward wrapper: for `K` Galois over `ℚ` generated by the `r i` (`ℚ(rᵢ) = K`), if `p` is odd,
`p ∤ d i` for every `i`, and every `d i` is a quadratic residue mod `p`, then the decomposition
group of `Q` is trivial. -/
private theorem stabilizer_eq_bot_of_forall_legendreSym_eq_one {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) [IsGalois ℚ K]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (hqr : ∀ i, legendreSym p (d i) = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    stabilizer (K ≃ₐ[ℚ] K) Q = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  -- Each `σ` in the stabilizer fixes every generator `r i`, and these generate `K = ℚ(rᵢ)`,
  -- so `σ = 1` by an adjoin induction.
  have hfix : ∀ i, σ (r i) = r i :=
    fun i => decompositionGroup_fixes_gen d r hr hodd (hcop i) (hqr i) Q hσ
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
  refine ⟨fun hsplit i =>
    legendreSym_eq_one_of_ncard_primesOver_eq_finrank d r hr (hcop i) Q hsplit, fun hqr => ?_⟩
  rw [ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot K Q]
  exact stabilizer_eq_bot_of_forall_legendreSym_eq_one d r hr htop hodd hcop hqr Q

end

end TauCeti.NumberField
