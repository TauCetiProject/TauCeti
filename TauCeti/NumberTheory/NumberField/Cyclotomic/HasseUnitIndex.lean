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
`Q_K = [(𝓞 K)ˣ : (𝓞 K⁺)ˣ · μ(K)]` (`NumberField.IsCMField.indexRealUnits K`) is `1` or `2`. When
`K / ℚ` is a cyclotomic field of prime-power conductor `p ^ a` (any prime `p`, any `a : ℕ`,
including `p = 2` and `p ^ a ≤ 2`), we prove `Q_K = 1`, i.e., `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · μ(K)`.

The key input is `x - conj x ∈ (ζ² - 1)` for every `x ∈ 𝓞 K` in an `n`-th cyclotomic CM field
(since `𝓞 K = ℤ[ζ]` and `ζ⁻¹ - ζ = -(ζ² - 1) ζ⁻¹`). If `Q_K = 2`, `indexRealUnits_eq_two_iff`
yields a unit `u` whose quotient `u / conj u` generates `μ(K)`:
* for odd `p`, `v = u ^ (p ^ a)` satisfies `conj v = -v`, so `2 v ∈ (ζ - 1)` and `p ∣ 2`;
* for `p = 2` and `a ≥ 2`, `ζ' = u / conj u` is a primitive `2 ^ a`-th root of unity and
  `(ζ' - 1)² ∣ (ζ'² - 1) ∣ u - conj u = u ζ'⁻¹ (ζ' - 1)`, contradicting `Prime (ζ' - 1)`.

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

local notation3 "K⁺" => maximalRealSubfield K

/-- An integral unit of `K` lies in `realUnits K` if and only if its value in `K` lies in the
maximal real subfield `K⁺`. -/
theorem mem_realUnits_iff_coe_mem_maximalRealSubfield (u : (𝓞 K)ˣ) :
    u ∈ realUnits K ↔ ((u : 𝓞 K) : K) ∈ K⁺ := by
  rw [mem_realUnits_iff]
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨v, hv⟩
    have hval : ((u : 𝓞 K) : K) = (algebraMap (𝓞 K⁺) K) (v : 𝓞 _) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K⁺) (𝓞 K) K, hv]
    rw [hval, IsScalarTower.algebraMap_apply (𝓞 K⁺) K⁺ K]
    exact SetLike.coe_mem _
  · have hu_inv : (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈ K⁺ := by simpa using inv_mem hu
    let val' : 𝓞 K⁺ := ⟨⟨_, hu⟩, isIntegral_algebraMap_iff.mp u.val.isIntegral_coe⟩
    let inv' : 𝓞 K⁺ := ⟨⟨_, hu_inv⟩, isIntegral_algebraMap_iff.mp (u⁻¹ : (𝓞 K)ˣ).val.isIntegral_coe⟩
    have hval' : algebraMap (𝓞 K⁺) (𝓞 K) val' = u := RingOfIntegers.ext rfl
    have hinv' : algebraMap (𝓞 K⁺) (𝓞 K) inv' = (u⁻¹ : (𝓞 K)ˣ) := RingOfIntegers.ext rfl
    refine ⟨⟨val', inv', ?_, ?_⟩, hval'⟩ <;>
      exact FaithfulSMul.algebraMap_injective _ (𝓞 K) (by simp [map_mul, hval', hinv'])

/-- A root of unity in `K` that lies in `realUnits K` is `1` or `-1`. -/
theorem eq_one_or_neg_one_of_mem_torsion_of_mem_realUnits [NumberField K] {μ : (𝓞 K)ˣ}
    (hμ : μ ∈ torsion K) (hreal : μ ∈ realUnits K) : μ = 1 ∨ μ = -1 := by
  obtain ⟨v, hv⟩ := (mem_realUnits_iff K μ).mp hreal
  have hv_tors : v ∈ torsion K⁺ := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hμ ⊢
    obtain ⟨n, hn, hpow⟩ := hμ
    refine ⟨n, hn, Units.ext <| FaithfulSMul.algebraMap_injective _ (𝓞 K) ?_⟩
    rw [Units.val_one, map_one, Units.val_pow_eq_pow_val, map_pow, hv, ← Units.val_pow_eq_pow_val,
      hpow, Units.val_one]
  let w : InfinitePlace K⁺ := Classical.choice inferInstance
  rcases TauCeti.NumberField.Units.torsion_eq_one_or_neg_one_of_isReal (IsTotallyReal.isReal w)
      ⟨v, hv_tors⟩ with rfl | rfl
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

local notation3 "K⁺" => maximalRealSubfield K

/-- When `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · H` for a subgroup `H ≤ (𝓞 K)ˣ` (in particular, when the Hasse unit
index is `1` and `μ(K) ≤ H`), the inclusion `(𝓞 K⁺)ˣ →* (𝓞 K)ˣ` induces a multiplicative
isomorphism `(𝓞 K⁺)ˣ ⧸ H⁺ ≃* (𝓞 K)ˣ ⧸ H`, where `H⁺` is the preimage of `H` in `(𝓞 K⁺)ˣ`. -/
noncomputable def quotientRealUnitsEquiv {H : Subgroup (𝓞 K)ˣ} (h : realUnits K ⊔ H = ⊤) :
    (𝓞 K⁺)ˣ ⧸ H.comap (Units.map (↑(algebraMap (𝓞 K⁺) (𝓞 K)))) ≃* (𝓞 K)ˣ ⧸ H :=
  let i : (𝓞 K⁺)ˣ →* (𝓞 K)ˣ := Units.map (↑(algebraMap (𝓞 K⁺) (𝓞 K)))
  let φ : (𝓞 K⁺)ˣ →* (𝓞 K)ˣ ⧸ H := (QuotientGroup.mk' H).comp i
  have hker : φ.ker = H.comap i := by
    ext u; simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective φ := fun q ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨r, ⟨u, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.mp (h.symm ▸ Subgroup.mem_top x)
    refine ⟨u, ?_⟩
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa [i] using ht
  (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

@[simp]
theorem quotientRealUnitsEquiv_mk {H : Subgroup (𝓞 K)ˣ} (h : realUnits K ⊔ H = ⊤)
    (u : (𝓞 K⁺)ˣ) :
    quotientRealUnitsEquiv h (QuotientGroup.mk u) =
      QuotientGroup.mk (Units.map (↑(algebraMap (𝓞 K⁺) (𝓞 K))) u) := by rfl

/-- When `(𝓞 K)ˣ = (𝓞 K⁺)ˣ · H`, `H` and its real preimage `H⁺` have the same index. -/
theorem index_eq_index_comap_realUnits {H : Subgroup (𝓞 K)ˣ} (h : realUnits K ⊔ H = ⊤) :
    H.index = (H.comap (Units.map (↑(algebraMap (𝓞 K⁺) (𝓞 K)) : 𝓞 K⁺ →* 𝓞 K))).index := by
  simpa [Subgroup.index] using (Nat.card_congr (quotientRealUnitsEquiv h).toEquiv).symm

end QuotientEquiv

end TauCeti.NumberField

namespace TauCeti.IsCyclotomicExtension.Rat

section GeneralConductor

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [_root_.IsCyclotomicExtension {n} ℚ K]

/-- In an `n`-th cyclotomic CM field, `x - ringOfIntegersComplexConj K x` is divisible by `ζ² - 1`
for every algebraic integer `x ∈ 𝓞 K` and every primitive `n`-th root of unity `ζ`. -/
theorem sub_ringOfIntegersComplexConj_mem_span_sq_sub_one [IsCMField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (x : 𝓞 K) :
    x - ringOfIntegersComplexConj K x ∈ Ideal.span {hζ.toInteger ^ 2 - 1} := by
  set I : Ideal (𝓞 K) := Ideal.span {hζ.toInteger ^ 2 - 1}
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
      have hmem : hζu.unit ∈ torsion K := ⟨n, NeZero.pos n, by
        rw [isPeriodicPt_mul_iff_pow_eq_one]
        exact Units.ext (by simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one)⟩
      rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj]
      simpa [unitsComplexConj, invζ] using congrArg (fun u : (𝓞 K)ˣ ↦ ((u : 𝓞 K) : K))
        (unitsComplexConj_torsion (K := K) ⟨hζu.unit, hmem⟩)
    rw [hconj, Ideal.mem_span_singleton]
    have hmul : invζ * hζ.toInteger = 1 := by simp [invζ]
    exact ⟨-invζ, by linear_combination hζ.toInteger * hmul⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact (AlgHom.congr_fun halg x).symm

/-- In an `n`-th cyclotomic CM field, `x - ringOfIntegersComplexConj K x` is divisible by `ζ - 1`
for every `x ∈ 𝓞 K` and every primitive `n`-th root of unity `ζ`. -/
theorem sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one [IsCMField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (x : 𝓞 K) :
    x - ringOfIntegersComplexConj K x ∈ Ideal.span {hζ.toInteger - 1} := by
  have hmem := Ideal.mem_span_singleton.mp (sub_ringOfIntegersComplexConj_mem_span_sq_sub_one hζ x)
  exact Ideal.mem_span_singleton.mpr (dvd_trans ⟨hζ.toInteger + 1, by ring⟩ hmem)

end GeneralConductor

section PrimePower

/-- In a `2 ^ (k + 2)`-th cyclotomic field, `x - ringOfIntegersComplexConj K x` is divisible by
`(ζ - 1) ^ 2` for every `x ∈ 𝓞 K` and every primitive `2 ^ (k + 2)`-th root of unity `ζ`. -/
theorem sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one_sq {k : ℕ}
    {K : Type*} [Field K] [NumberField K] [_root_.IsCyclotomicExtension {2 ^ (k + 2)} ℚ K]
    [IsCMField K] {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) (x : 𝓞 K) :
    x - ringOfIntegersComplexConj K x ∈ Ideal.span {(hζ.toInteger - 1) ^ 2} := by
  have hmem := Ideal.mem_span_singleton.mp (sub_ringOfIntegersComplexConj_mem_span_sq_sub_one hζ x)
  have hdvd2 : hζ.toInteger - 1 ∣ (2 : 𝓞 K) := by
    simpa using (_root_.IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff (p := 2) (k := k + 1)
      hζ (n := 2)).mpr dvd_rfl
  have hdvd_add : hζ.toInteger - 1 ∣ hζ.toInteger + 1 := by
    simpa [show hζ.toInteger + 1 = (hζ.toInteger - 1) + 2 by ring] using dvd_add dvd_rfl hdvd2
  refine Ideal.mem_span_singleton.mpr (dvd_trans ?_ hmem)
  rw [sq, show hζ.toInteger ^ 2 - 1 = (hζ.toInteger - 1) * (hζ.toInteger + 1) by ring]
  exact mul_dvd_mul_left _ hdvd_add

private theorem ringOfIntegersComplexConj_val_unit {K : Type*} [Field K] [NumberField K]
    [IsCMField K] (v : (𝓞 K)ˣ) :
    ringOfIntegersComplexConj K (v : 𝓞 K) = ((unitsComplexConj K v : (𝓞 K)ˣ) : 𝓞 K) := by
  rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj]; rfl

/-- For odd `p` and `a = k + 1`, the Hasse unit index cannot be `2`. -/
private theorem indexRealUnits_ne_two_of_odd (p : ℕ) [hp : Fact p.Prime] (hodd : p ≠ 2) {k : ℕ}
    {K : Type*} [Field K] [NumberField K] [_root_.IsCyclotomicExtension {p ^ (k + 1)} ℚ K] :
    indexRealUnits K ≠ 2 := by
  have hgt : 2 < p ^ (k + 1) := lt_of_lt_of_le (lt_of_le_of_ne hp.out.two_le (Ne.symm hodd))
    (Nat.le_self_pow (Nat.succ_ne_zero k) p)
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : IsCMField K :=
    _root_.IsCyclotomicExtension.Rat.isCMField K (S := {p ^ (k + 1)}) ⟨p ^ (k + 1), rfl, hgt⟩
  intro h2
  obtain ⟨u, hu⟩ := (indexRealUnits_eq_two_iff K).mp h2
  set g : torsion K := unitsMulComplexConjInv K u
  have hord : orderOf g = 2 * p ^ (k + 1) := by
    have hnotEven : ¬ Even (p ^ (k + 1)) :=
      Nat.not_even_iff_odd.mpr (hp.out.odd_of_ne_two hodd).pow
    rw [← Nat.card_zpowers, hu, Subgroup.card_top, ← torsionOrder,
      _root_.IsCyclotomicExtension.Rat.torsionOrder_eq (n := p ^ (k + 1)) (K := K)]
    simp [hnotEven]
  have hg_pow_ne : g ^ p ^ (k + 1) ≠ 1 := fun h1 ↦ by
    have hle := Nat.le_of_dvd (pow_pos hp.out.pos _) (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  have hg_pow_eq : ((g ^ p ^ (k + 1) : torsion K) : (𝓞 K)ˣ) = -1 := by
    have hsq : (((g ^ p ^ (k + 1) : torsion K) : (𝓞 K)ˣ) : 𝓞 K) ^ 2 = 1 := by
      have : (g ^ p ^ (k + 1)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
      simpa using congrArg (fun z : torsion K ↦ ((z : (𝓞 K)ˣ) : 𝓞 K)) this
    rcases sq_eq_one_iff.mp hsq with h1 | hneg
    · exact absurd (Subtype.ext (Units.ext h1)) hg_pow_ne
    · exact Units.ext hneg
  set v : (𝓞 K)ˣ := u ^ p ^ (k + 1)
  have hv_conj : unitsComplexConj K v = -v := by
    have hmul : v * (unitsComplexConj K v)⁻¹ = -1 := by
      rw [← unitsMulComplexConjInv_apply, map_pow]; exact hg_pow_eq
    have h1 : v = -(unitsComplexConj K v) := by simpa using eq_mul_of_mul_inv_eq hmul
    exact (neg_eq_iff_eq_neg.mpr h1).symm
  have hζ := _root_.IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K
  have hmem := sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one hζ (v : 𝓞 K)
  rw [ringOfIntegersComplexConj_val_unit, hv_conj, Units.val_neg, sub_neg_eq_add, ← two_mul,
    Ideal.mem_span_singleton] at hmem
  have hdvd2 : hζ.toInteger - 1 ∣ (2 : 𝓞 K) := by
    simpa [mul_assoc] using dvd_mul_of_dvd_left hmem (v⁻¹ : (𝓞 K)ˣ).val
  have hp2 : p ∣ 2 := Int.ofNat_dvd.mp <|
    (_root_.IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff (p := p) (k := k) hζ
      (n := 2)).mp (by simpa using hdvd2)
  have := hp.out.two_le; have := Nat.le_of_dvd (by omega) hp2; omega

/-- For `p = 2` and `a = k + 2`, the Hasse unit index cannot be `2`. -/
private theorem indexRealUnits_ne_two_of_two_pow {k : ℕ}
    {K : Type*} [Field K] [NumberField K] [_root_.IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] :
    indexRealUnits K ≠ 2 := by
  have hgt : 2 < 2 ^ (k + 2) := lt_of_lt_of_le (by omega : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by omega) (by omega))
  have : NeZero (2 ^ (k + 2)) := ⟨pow_ne_zero _ (by omega)⟩
  have : IsCMField K :=
    _root_.IsCyclotomicExtension.Rat.isCMField K (S := {2 ^ (k + 2)}) ⟨2 ^ (k + 2), rfl, hgt⟩
  intro h2
  obtain ⟨u, hu⟩ := (indexRealUnits_eq_two_iff K).mp h2
  set g : torsion K := unitsMulComplexConjInv K u
  have hord : orderOf g = 2 ^ (k + 2) := by
    have hEven : Even (2 ^ (k + 2)) := Even.pow_of_ne_zero even_two (by omega)
    rw [← Nat.card_zpowers, hu, Subgroup.card_top, ← torsionOrder,
      _root_.IsCyclotomicExtension.Rat.torsionOrder_eq (n := 2 ^ (k + 2)) (K := K)]
    simp [hEven]
  set ζ' : K := (((g : (𝓞 K)ˣ) : 𝓞 K) : K)
  have hζ' : IsPrimitiveRoot ζ' (2 ^ (k + 2)) :=
    (IsPrimitiveRoot.coe_units_iff.mpr <| IsPrimitiveRoot.coe_submonoidClass_iff.mpr <|
      IsPrimitiveRoot.iff_orderOf.mpr hord).map_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hmem := Ideal.mem_span_singleton.mp <|
    sub_ringOfIntegersComplexConj_mem_span_zeta_sub_one_sq hζ' (u : 𝓞 K)
  have hconj : unitsComplexConj K u = u * (g : (𝓞 K)ˣ)⁻¹ := by
    simp [g, unitsMulComplexConjInv_apply]
  have hmul : (((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * hζ'.toInteger = 1 := by
    have : hζ'.toInteger = ((g : (𝓞 K)ˣ) : 𝓞 K) := RingOfIntegers.ext rfl
    simp [this]
  have hsub : (u : 𝓞 K) - ringOfIntegersComplexConj K (u : 𝓞 K) =
      (u : 𝓞 K) * ((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) * (hζ'.toInteger - 1) := by
    rw [ringOfIntegersComplexConj_val_unit, hconj, Units.val_mul]
    linear_combination -(u : 𝓞 K) * hmul
  rw [hsub, sq] at hmem
  have hprime : Prime (hζ'.toInteger - 1) := hζ'.zeta_sub_one_prime
  obtain ⟨c, hc⟩ := hmem
  have hdvd_unit : hζ'.toInteger - 1 ∣ (u : 𝓞 K) * ((g : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) :=
    ⟨c, mul_right_cancel₀ hprime.ne_zero (by rw [hc]; ring)⟩
  exact hprime.not_isUnit (isUnit_of_dvd_unit hdvd_unit (u.isUnit.mul ((g : (𝓞 K)ˣ)⁻¹).isUnit))

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
