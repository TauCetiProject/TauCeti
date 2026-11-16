/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import TauCeti.NumberTheory.NumberField.Units.Torsion

/-!
# The Hasse unit index of a prime-power cyclotomic field

For a CM number field `K` with maximal real subfield `K⁺`, the Hasse unit index
`Q_K = [(𝓞 K)ˣ : (𝓞 K⁺)ˣ · μ(K)]` (`NumberField.IsCMField.indexRealUnits K`) is `1` or `2`
(`NumberField.IsCMField.indexRealUnits_eq_one_or_two`). When `K` is a cyclotomic field of
prime-power conductor `p ^ a` over `ℚ` (for any prime `p` and any `a : ℕ`, including `p = 2` and
the rational cases `a = 0` and `p ^ a = 2`), this index is `1`, so every unit of `𝓞 K` is a root
of unity times a real unit: `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · μ(K)`.

The proof rests on the congruence `x - x̄ ∈ (ζ² - 1)` for every `x ∈ 𝓞 K` in an `n`-th cyclotomic
CM field, obtained because `𝓞 K = ℤ[ζ]` and `ζ - ζ⁻¹ = ζ⁻¹ (ζ² - 1)`. If `Q_K = 2`, Mathlib's
`NumberField.IsCMField.indexRealUnits_eq_two_iff` yields a unit `u` such that `u / ū` generates
`μ(K)`:

* For odd `p`, `μ(K)` has order `2 p ^ a`, so `v = u ^ (p ^ a)` satisfies `v̄ = -v`; hence
  `2 v = v - v̄ ∈ (ζ - 1)`, forcing `p ∣ 2`, a contradiction.
* For `p = 2` and `a ≥ 2`, `μ(K)` has order `2 ^ a`, so `ζ' = u / ū` is itself a primitive
  `2 ^ a`-th root of unity; then `ζ' - 1 ∣ 2` gives
  `(ζ' - 1)² ∣ (ζ'² - 1) ∣ (u - ū) = u ζ'⁻¹ (ζ' - 1)`, forcing the prime `ζ' - 1` to divide the
  unit `u ζ'⁻¹`, a contradiction.

For composite conductors the index can be `2` (for example in `ℚ(ζ₁₂)`, where `1 - ζ₁₂` is a unit
whose quotient by its conjugate is `-ζ₁₂`, generating `μ(ℚ(ζ₁₂))`).

As a consequence, whenever `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · H` for a subgroup `H ≤ (𝓞 K)ˣ` (in particular, when
`indexRealUnits K = 1` and `μ(K) ≤ H`), the inclusion `(𝓞 K⁺)ˣ →* (𝓞 K)ˣ` induces
`(𝓞 K⁺)ˣ ⧸ H⁺ ≃* (𝓞 K)ˣ ⧸ H` and `[ (𝓞 K)ˣ : H ] = [ (𝓞 K⁺)ˣ : H⁺ ]`.

## Main results

* `TauCeti.NumberField.mem_realUnits_iff_coe_mem_maximalRealSubfield`: an integral unit of `K`
  lies in `realUnits K` if and only if its value in `K` lies in `K⁺`.
* `TauCeti.NumberField.eq_one_or_neg_one_of_mem_torsion_of_mem_realUnits`: a root of unity lying in
  `realUnits K` is `1` or `-1`.
* `TauCeti.NumberField.IsTotallyReal.realUnits_eq_top` and
  `TauCeti.NumberField.IsTotallyReal.indexRealUnits_eq_one`: a totally real field has all units
  real and Hasse unit index `1`.
* `TauCeti.NumberField.quotientRealUnitsEquiv` and
  `TauCeti.NumberField.index_eq_index_comap_realUnits`: when `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · H`,
  `(𝓞 K⁺)ˣ ⧸ H⁺ ≃* (𝓞 K)ˣ ⧸ H` and `H.index = H⁺.index`.
* `TauCeti.IsCyclotomicExtension.Rat.sub_ringOfIntegersComplexConj_mem_span_sq_sub_one`:
  in any `n`-th cyclotomic CM field, `x - x̄ ∈ (ζ² - 1)` for every `x ∈ 𝓞 K`.
* `TauCeti.IsCyclotomicExtension.Rat.indexRealUnits_eq_one`: the Hasse unit index of every
  prime-power cyclotomic field over `ℚ` is `1`.
* `TauCeti.IsCyclotomicExtension.Rat.realUnits_sup_torsion_eq_top`: for a prime-power cyclotomic
  field `K` over `ℚ`, `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · μ(K)`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer (1997), Corollary 4.13.
* R. Sharifi, *Iwasawa Theory*, Lemma 4.2.17.
-/

public section

open NumberField NumberField.Units NumberField.IsCMField

open scoped NumberField

namespace TauCeti.NumberField

section RealUnits

variable {K : Type*} [Field K]

/-- An integral unit of `K` lies in `realUnits K` if and only if its value in `K` lies in the
maximal real subfield `K⁺`. -/
theorem mem_realUnits_iff_coe_mem_maximalRealSubfield (u : (𝓞 K)ˣ) :
    u ∈ realUnits K ↔ ((u : 𝓞 K) : K) ∈ maximalRealSubfield K := by
  rw [mem_realUnits_iff]
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨v, hv⟩
    have hval : ((u : 𝓞 K) : K) = (algebraMap (𝓞 (maximalRealSubfield K)) K) (v : 𝓞 _) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield K)) (𝓞 K) K, hv]
    rw [hval, IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield K)) (maximalRealSubfield K) K]
    exact SetLike.coe_mem _
  · have hu_inv : (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈ maximalRealSubfield K := by
      have hinv : (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = ((u : 𝓞 K) : K)⁻¹ := by simp
      rw [hinv]
      exact inv_mem hu
    have hint : IsIntegral ℤ (⟨((u : 𝓞 K) : K), hu⟩ : maximalRealSubfield K) :=
      isIntegral_algebraMap_iff.mp u.val.isIntegral_coe
    have hint_inv :
        IsIntegral ℤ (⟨(((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K), hu_inv⟩ : maximalRealSubfield K) :=
      isIntegral_algebraMap_iff.mp (u⁻¹ : (𝓞 K)ˣ).val.isIntegral_coe
    let val' : 𝓞 (maximalRealSubfield K) := ⟨⟨((u : 𝓞 K) : K), hu⟩, hint⟩
    let inv' : 𝓞 (maximalRealSubfield K) := ⟨⟨(((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K), hu_inv⟩, hint_inv⟩
    have hval' : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) val' = u := RingOfIntegers.ext rfl
    have hinv' : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) inv' = (u⁻¹ : (𝓞 K)ˣ) :=
      RingOfIntegers.ext rfl
    refine ⟨⟨val', inv', ?_, ?_⟩, hval'⟩
    · exact FaithfulSMul.algebraMap_injective _ (𝓞 K)
        (by rw [map_mul, hval', hinv', u.mul_inv, map_one])
    · exact FaithfulSMul.algebraMap_injective _ (𝓞 K)
        (by rw [map_mul, hinv', hval', u.inv_mul, map_one])

/-- A root of unity in `K` that lies in `realUnits K` is `1` or `-1`. -/
theorem eq_one_or_neg_one_of_mem_torsion_of_mem_realUnits [NumberField K] {μ : (𝓞 K)ˣ}
    (hμ : μ ∈ torsion K) (hreal : μ ∈ realUnits K) :
    μ = 1 ∨ μ = -1 := by
  obtain ⟨v, hv⟩ := (mem_realUnits_iff K μ).mp hreal
  have hv_tors : v ∈ torsion (maximalRealSubfield K) := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hμ ⊢
    obtain ⟨n, hn, hpow⟩ := hμ
    refine ⟨n, hn, Units.ext <| FaithfulSMul.algebraMap_injective _ (𝓞 K) ?_⟩
    rw [Units.val_one, map_one, Units.val_pow_eq_pow_val, map_pow, hv, ← Units.val_pow_eq_pow_val,
      hpow, Units.val_one]
  let w : InfinitePlace (maximalRealSubfield K) := Classical.choice inferInstance
  have hv1_or : v = 1 ∨ v = -1 :=
    TauCeti.NumberField.Units.torsion_eq_one_or_neg_one_of_isReal (IsTotallyReal.isReal w)
      ⟨v, hv_tors⟩
  rcases hv1_or with rfl | rfl
  · exact .inl (Units.ext (by simp [← hv]))
  · exact .inr (Units.ext (by simp [← hv]))

/-- When `K` is totally real, every unit of `𝓞 K` is a real unit. -/
theorem IsTotallyReal.realUnits_eq_top [IsTotallyReal K] : realUnits K = ⊤ := by
  ext u
  simp [mem_realUnits_iff_coe_mem_maximalRealSubfield,
    _root_.NumberField.IsTotallyReal.maximalRealSubfield_eq_top]

/-- When `K` is totally real, the Hasse unit index is `1`. -/
theorem IsTotallyReal.indexRealUnits_eq_one [IsTotallyReal K] : indexRealUnits K = 1 := by
  rw [indexRealUnits, IsTotallyReal.realUnits_eq_top, top_sup_eq, Subgroup.index_top]

end RealUnits

section QuotientEquiv

variable {K : Type*} [Field K]

/-- When `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · H` for a subgroup `H ≤ (𝓞 K)ˣ` (in particular, when the Hasse unit
index is `1` and `μ(K) ≤ H`), the inclusion `(𝓞 K⁺)ˣ →* (𝓞 K)ˣ` induces a multiplicative
isomorphism `(𝓞 K⁺)ˣ ⧸ H⁺ ≃* (𝓞 K)ˣ ⧸ H`, where `H⁺` is the preimage of `H` in `(𝓞 K⁺)ˣ`. -/
noncomputable def quotientRealUnitsEquiv {H : Subgroup (𝓞 K)ˣ} (h : realUnits K ⊔ H = ⊤) :
    (𝓞 (maximalRealSubfield K))ˣ ⧸
        H.comap (Units.map (↑(algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)))) ≃*
      (𝓞 K)ˣ ⧸ H :=
  let i : (𝓞 (maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
    Units.map (↑(algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)))
  let φ : (𝓞 (maximalRealSubfield K))ˣ →* (𝓞 K)ˣ ⧸ H := (QuotientGroup.mk' H).comp i
  have hker : φ.ker = H.comap i := by
    ext u
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    have hx : x ∈ realUnits K ⊔ H := h.symm ▸ Subgroup.mem_top x
    obtain ⟨r, hr, t, ht, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := hr
    refine ⟨u, ?_⟩
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa [i] using ht
  (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

@[simp]
theorem quotientRealUnitsEquiv_mk {H : Subgroup (𝓞 K)ˣ} (h : realUnits K ⊔ H = ⊤)
    (u : (𝓞 (maximalRealSubfield K))ˣ) :
    quotientRealUnitsEquiv h (QuotientGroup.mk u) =
      QuotientGroup.mk
        (Units.map (↑(algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))) u) := by
  rfl

/-- When `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · H`, `H` and its real preimage `H⁺` have the same index. -/
theorem index_eq_index_comap_realUnits {H : Subgroup (𝓞 K)ˣ} (h : realUnits K ⊔ H = ⊤) :
    H.index =
      (H.comap (Units.map
        (↑(algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) :
          𝓞 (maximalRealSubfield K) →* 𝓞 K))).index := by
  simpa [Subgroup.index] using (Nat.card_congr (quotientRealUnitsEquiv h).toEquiv).symm

end QuotientEquiv

end TauCeti.NumberField

namespace TauCeti.IsCyclotomicExtension.Rat

section GeneralConductor

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [_root_.IsCyclotomicExtension {n} ℚ K]

/-- In an `n`-th cyclotomic CM field, `x - x̄` is divisible by `ζ² - 1` for every algebraic
integer `x ∈ 𝓞 K` and every primitive `n`-th root of unity `ζ`. -/
theorem sub_ringOfIntegersComplexConj_mem_span_sq_sub_one [IsCMField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (x : 𝓞 K) :
    x - ringOfIntegersComplexConj K x ∈ Ideal.span {hζ.toInteger ^ 2 - 1} := by
  set I : Ideal (𝓞 K) := Ideal.span {hζ.toInteger ^ 2 - 1}
  suffices h : (Ideal.Quotient.mk I).comp (ringOfIntegersComplexConj K).toRingHom =
      Ideal.Quotient.mk I by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact (RingHom.congr_fun h x).symm
  -- Both homomorphisms are `ℤ`-algebra maps from `𝓞 K = ℤ[ζ]`, so checking on `ζ` suffices.
  have halg : ((Ideal.Quotient.mk I).comp (ringOfIntegersComplexConj K).toRingHom).toIntAlgHom =
      (Ideal.Quotient.mk I).toIntAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (_root_.IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ)
      ?_
    rintro _ rfl
    simp only [RingHom.toIntAlgHom_apply, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
    have hζu : IsUnit hζ.toInteger := hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne n)
    set invζ : 𝓞 K := (hζu.unit⁻¹).val
    have hconj : ringOfIntegersComplexConj K hζ.toInteger = invζ := by
      have hmem : hζu.unit ∈ torsion K := by
        rw [NumberField.Units.torsion, CommGroup.mem_torsion]
        exact ⟨n, NeZero.pos n, by
          rw [isPeriodicPt_mul_iff_pow_eq_one]
          exact Units.ext (by simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one)⟩
      have h1 := unitsComplexConj_torsion (K := K) ⟨hζu.unit, hmem⟩
      rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj]
      have h2 := congrArg (fun u : (𝓞 K)ˣ ↦ ((u : 𝓞 K) : K)) h1
      simpa [unitsComplexConj, invζ] using h2
    rw [hconj, Ideal.mem_span_singleton]
    refine ⟨-invζ, ?_⟩
    have hmul : invζ * hζ.toInteger = 1 := by simp [invζ]
    calc invζ - hζ.toInteger
        = invζ - 1 * hζ.toInteger := by rw [one_mul]
      _ = invζ - (invζ * hζ.toInteger) * hζ.toInteger := by rw [hmul]
      _ = (hζ.toInteger ^ 2 - 1) * -invζ := by ring
  exact RingHom.ext fun y ↦ AlgHom.congr_fun halg y

/-- In an `n`-th cyclotomic CM field, `x - x̄` is divisible by `ζ - 1` for every `x ∈ 𝓞 K`
and every primitive `n`-th root of unity `ζ`. -/
theorem sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one [IsCMField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (x : 𝓞 K) :
    x - ringOfIntegersComplexConj K x ∈ Ideal.span {hζ.toInteger - 1} := by
  have hmem := sub_ringOfIntegersComplexConj_mem_span_sq_sub_one hζ x
  rw [Ideal.mem_span_singleton] at hmem ⊢
  exact dvd_trans ⟨hζ.toInteger + 1, by ring⟩ hmem

end GeneralConductor

section PrimePower

/-- In a `2 ^ (k + 2)`-th cyclotomic field, `x - x̄` is divisible by `(ζ - 1) ^ 2` for every
`x ∈ 𝓞 K` and every primitive `2 ^ (k + 2)`-th root of unity `ζ`. -/
theorem sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one_sq {k : ℕ}
    {K : Type*} [Field K] [NumberField K] [_root_.IsCyclotomicExtension {2 ^ (k + 2)} ℚ K]
    [IsCMField K] {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) (x : 𝓞 K) :
    x - ringOfIntegersComplexConj K x ∈ Ideal.span {(hζ.toInteger - 1) ^ 2} := by
  have hmem := sub_ringOfIntegersComplexConj_mem_span_sq_sub_one hζ x
  rw [Ideal.mem_span_singleton] at hmem ⊢
  have hdvd2 : hζ.toInteger - 1 ∣ (2 : 𝓞 K) := by
    have := (_root_.IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff (p := 2) (k := k + 1)
      hζ (n := 2)).mpr dvd_rfl
    simpa using this
  have hdvd_add : hζ.toInteger - 1 ∣ hζ.toInteger + 1 := by
    have hEq : hζ.toInteger + 1 = (hζ.toInteger - 1) + 2 := by ring
    rw [hEq]
    exact dvd_add dvd_rfl hdvd2
  have hdvd_sq : (hζ.toInteger - 1) ^ 2 ∣ hζ.toInteger ^ 2 - 1 := by
    have hEq : hζ.toInteger ^ 2 - 1 = (hζ.toInteger - 1) * (hζ.toInteger + 1) := by ring
    rw [sq, hEq]
    exact mul_dvd_mul_left _ hdvd_add
  exact dvd_trans hdvd_sq hmem

/-- For odd `p` and `a = k + 1`, the Hasse unit index cannot be `2`. -/
private theorem indexRealUnits_ne_two_of_odd (p : ℕ) [hp : Fact p.Prime] (hodd : p ≠ 2) {k : ℕ}
    {K : Type*} [Field K] [NumberField K] [_root_.IsCyclotomicExtension {p ^ (k + 1)} ℚ K] :
    indexRealUnits K ≠ 2 := by
  have hp3 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)
  have hgt : 2 < p ^ (k + 1) := lt_of_lt_of_le hp3 (Nat.le_self_pow (Nat.succ_ne_zero k) p)
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : IsCMField K :=
    _root_.IsCyclotomicExtension.Rat.isCMField K (S := {p ^ (k + 1)}) ⟨p ^ (k + 1), rfl, hgt⟩
  intro h2
  obtain ⟨u, hu⟩ := (indexRealUnits_eq_two_iff K).mp h2
  set g : torsion K := unitsMulComplexConjInv K u
  have hord : orderOf g = 2 * p ^ (k + 1) := by
    have hcard : Nat.card (torsion K) = 2 * p ^ (k + 1) := by
      rw [← torsionOrder,
        _root_.IsCyclotomicExtension.Rat.torsionOrder_eq (n := p ^ (k + 1)) (K := K)]
      have hnotEven : ¬ Even (p ^ (k + 1)) := by
        rw [Nat.even_pow, not_and_or]
        left
        exact Nat.not_even_iff_odd.mpr (hp.out.odd_of_ne_two hodd)
      simp [hnotEven]
    rw [← hcard, ← Subgroup.card_top, ← hu, Nat.card_zpowers]
  -- `g ^ (p ^ (k + 1))` has order `2`, hence equals `-1`.
  have hg_pow_sq : (g ^ p ^ (k + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hg_pow_ne : g ^ p ^ (k + 1) ≠ 1 := by
    intro h1
    have hdvd : orderOf g ∣ p ^ (k + 1) := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have hpos : 0 < p ^ (k + 1) := pow_pos hp.out.pos _
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  have hg_pow_eq : ((g ^ p ^ (k + 1) : torsion K) : (𝓞 K)ˣ) = -1 := by
    have hsq : (((g ^ p ^ (k + 1) : torsion K) : (𝓞 K)ˣ) : 𝓞 K) ^ 2 = 1 := by
      simpa using congrArg (fun z : torsion K ↦ ((z : (𝓞 K)ˣ) : 𝓞 K)) hg_pow_sq
    rcases sq_eq_one_iff.mp hsq with h1 | hneg
    · exact absurd (Subtype.ext (Units.ext h1)) hg_pow_ne
    · exact Units.ext hneg
  -- Set `v = u ^ (p ^ (k + 1))`. Then `v / v̄ = -1`, so `v̄ = -v` and `2 v = v - v̄ ∈ (ζ - 1)`.
  set v : (𝓞 K)ˣ := u ^ p ^ (k + 1)
  have hv_conj : unitsComplexConj K v = -v := by
    have hmul : (unitsMulComplexConjInv K v : (𝓞 K)ˣ) = -1 := by
      rw [map_pow]
      exact hg_pow_eq
    rw [unitsMulComplexConjInv_apply] at hmul
    have h1 : v = -(unitsComplexConj K v) := by
      calc v = (v * (unitsComplexConj K v)⁻¹) * unitsComplexConj K v := by simp
        _ = (-1) * unitsComplexConj K v := by rw [hmul]
        _ = -(unitsComplexConj K v) := by simp
    exact (neg_eq_iff_eq_neg.mpr h1).symm
  have hζ := _root_.IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K
  have hmem := sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one hζ (v : 𝓞 K)
  have hv_coe : ringOfIntegersComplexConj K (v : 𝓞 K) = -(v : 𝓞 K) := by
    rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj]
    simpa [unitsComplexConj] using congrArg (fun w : (𝓞 K)ˣ ↦ ((w : 𝓞 K) : K)) hv_conj
  rw [hv_coe, sub_neg_eq_add, ← two_mul, Ideal.mem_span_singleton] at hmem
  have hdvd2 : hζ.toInteger - 1 ∣ (2 : 𝓞 K) := by
    have h1 : hζ.toInteger - 1 ∣ (2 : 𝓞 K) * (v : 𝓞 K) * (v⁻¹ : (𝓞 K)ˣ) :=
      dvd_mul_of_dvd_left hmem _
    simpa [mul_assoc] using h1
  have hp2 : (p : ℤ) ∣ 2 :=
    (_root_.IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff (p := p) (k := k) hζ
      (n := 2)).mp (by simpa using hdvd2)
  have hp2' : p ∣ 2 := Int.ofNat_dvd.mp hp2
  have := Nat.le_of_dvd (by omega) hp2'
  omega

/-- For `p = 2` and `a = k + 2`, the Hasse unit index cannot be `2`. -/
private theorem indexRealUnits_ne_two_of_two_pow {k : ℕ}
    {K : Type*} [Field K] [NumberField K] [_root_.IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] :
    indexRealUnits K ≠ 2 := by
  have hgt : 2 < 2 ^ (k + 2) := by
    have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have : NeZero (2 ^ (k + 2)) := ⟨pow_ne_zero _ (by omega)⟩
  have : IsCMField K :=
    _root_.IsCyclotomicExtension.Rat.isCMField K (S := {2 ^ (k + 2)}) ⟨2 ^ (k + 2), rfl, hgt⟩
  intro h2
  obtain ⟨u, hu⟩ := (indexRealUnits_eq_two_iff K).mp h2
  set g : torsion K := unitsMulComplexConjInv K u
  have hord : orderOf g = 2 ^ (k + 2) := by
    have hcard : Nat.card (torsion K) = 2 ^ (k + 2) := by
      rw [← torsionOrder,
        _root_.IsCyclotomicExtension.Rat.torsionOrder_eq (n := 2 ^ (k + 2)) (K := K)]
      have hEven : Even (2 ^ (k + 2)) := Even.pow_of_ne_zero even_two (by omega)
      simp [hEven]
    rw [← hcard, ← Subgroup.card_top, ← hu, Nat.card_zpowers]
  -- Thus `ζ' = (g : K)` is a primitive `2 ^ (k + 2)`-th root of unity in `K`.
  set ζ' : K := (((g : (𝓞 K)ˣ) : 𝓞 K) : K)
  have hζ' : IsPrimitiveRoot ζ' (2 ^ (k + 2)) := by
    have h1 : IsPrimitiveRoot g (2 ^ (k + 2)) := IsPrimitiveRoot.iff_orderOf.mpr hord
    have h2' : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (2 ^ (k + 2)) :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.coe_submonoidClass_iff.mpr h1)
    exact h2'.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hζ'_toInt : hζ'.toInteger = ((g : (𝓞 K)ˣ) : 𝓞 K) := by
    ext
    rfl
  -- By the dyadic congruence, `(ζ' - 1) ^ 2 ∣ u - ū`.
  have hmem := sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one_sq hζ' (u : 𝓞 K)
  rw [Ideal.mem_span_singleton] at hmem
  -- On the other hand, `u - ū = u * ζ'⁻¹ * (ζ' - 1)` because `u * ū⁻¹ = ζ'`.
  have hconj : unitsComplexConj K u = u * (g : (𝓞 K)ˣ)⁻¹ := by
    have hg : (g : (𝓞 K)ˣ) = u * (unitsComplexConj K u)⁻¹ := unitsMulComplexConjInv_apply K u
    simp [hg]
  have hsub : (u : 𝓞 K) - ringOfIntegersComplexConj K (u : 𝓞 K) =
      (u : 𝓞 K) * ((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) * (hζ'.toInteger - 1) := by
    have huc : ringOfIntegersComplexConj K (u : 𝓞 K) =
        (u : 𝓞 K) * ((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) := by
      rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj]
      simpa [unitsComplexConj] using congrArg (fun w : (𝓞 K)ˣ ↦ ((w : 𝓞 K) : K)) hconj
    rw [huc, hζ'_toInt]
    have hmul : (((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((g : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
      simp
    calc (u : 𝓞 K) - (u : 𝓞 K) * (((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
        = (u : 𝓞 K) * ((((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((g : (𝓞 K)ˣ) : 𝓞 K)) -
            (u : 𝓞 K) * (((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [hmul, mul_one]
      _ = (u : 𝓞 K) * (((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (((g : (𝓞 K)ˣ) : 𝓞 K) - 1) := by ring
  rw [hsub, sq] at hmem
  have hprime : Prime (hζ'.toInteger - 1) := hζ'.zeta_sub_one_prime
  have hdvd_unit : hζ'.toInteger - 1 ∣ (u : 𝓞 K) * ((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) := by
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    exact mul_right_cancel₀ hprime.ne_zero (by rw [hc]; ring)
  have hisUnit : IsUnit ((u : 𝓞 K) * ((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ)) :=
    u.isUnit.mul ((g : (𝓞 K)ˣ)⁻¹).isUnit
  exact hprime.not_isUnit (isUnit_of_dvd_unit hdvd_unit hisUnit)

/-- **The Hasse unit index of a prime-power cyclotomic field is `1`.** For every prime `p` and
every `a : ℕ`, if `K` is a `p ^ a`-th cyclotomic extension of `ℚ` (including `p = 2` and the
rational cases `a = 0` and `p ^ a = 2`), then `NumberField.IsCMField.indexRealUnits K = 1`. -/
theorem indexRealUnits_eq_one (p a : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K]
    [NumberField K] [_root_.IsCyclotomicExtension {p ^ a} ℚ K] :
    indexRealUnits K = 1 := by
  by_cases hle : p ^ a ≤ 2
  · have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.out.ne_zero⟩
    have hpos : 0 < p ^ a := pow_pos hp.out.pos a
    have : IsTotallyReal K := nrComplexPlaces_eq_zero_iff.mp <| by
      rw [_root_.IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (p ^ a) K]
      rcases (by omega : p ^ a = 1 ∨ p ^ a = 2) with h | h <;> simp [h]
    exact TauCeti.NumberField.IsTotallyReal.indexRealUnits_eq_one
  · push Not at hle
    have : IsCMField K :=
      _root_.IsCyclotomicExtension.Rat.isCMField K (S := {p ^ a}) ⟨p ^ a, rfl, hle⟩
    rcases indexRealUnits_eq_one_or_two K with h1 | h2
    · exact h1
    · exfalso
      rcases a with _ | k
      · simp at hle
      · by_cases hp2 : p = 2
        · subst hp2
          rcases k with _ | k
          · simp at hle
          · exact indexRealUnits_ne_two_of_two_pow (k := k) h2
        · exact indexRealUnits_ne_two_of_odd p hp2 (k := k) h2

/-- **Every unit of a prime-power cyclotomic field is a root of unity times a real unit.** -/
theorem realUnits_sup_torsion_eq_top (p a : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [NumberField K] [_root_.IsCyclotomicExtension {p ^ a} ℚ K] :
    realUnits K ⊔ torsion K = ⊤ :=
  Subgroup.index_eq_one.mp (indexRealUnits_eq_one p a K)

end PrimePower

end TauCeti.IsCyclotomicExtension.Rat
