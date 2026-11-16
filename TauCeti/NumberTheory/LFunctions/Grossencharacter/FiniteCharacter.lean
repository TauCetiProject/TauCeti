/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility

/-!
# Hecke's finite character of a presentation

Let `χ` be a presentation at the modulus `𝔪` of an algebraic Hecke character, with unitary
weight `χ_u`, ideal-side shift `σ` and algebraic infinity type `n`. Hecke's theta series of `χ`
is a sum over the elements `a` of an ideal, weighted by a function of `a` rather than of the
principal ideal `(a)`. That function is the **finite character**

`χ_f(a) = χ_u((a)) * N(a) ^ σ * χ_∞(a)`  (`Grossencharacter.finiteCharacter`),

where `χ_∞` is the **archimedean value** (`Grossencharacter.archimedeanValue`): the monomial
`∏_τ τ(a) ^ (n τ)` of the infinity type, times at each real place `w` the sign of `a` there to the
power `ε_w - n_w`, the difference between the sign parity `ε_w` of the archimedean restriction of
`χ` and the parity `n_w` of its algebraic exponent. On `Kˣ` it is the archimedean component of the
idele class character (`Grossencharacter.archimedeanValue_eq_prod_infiniteComponent`). The signs
are not visible to the infinity type: the odd character modulo `4∞` of `ℚ` has exponent `0` and
parity `1`, and its finite character is `-1` at `-1`.

The finite character is completely multiplicative and vanishes exactly at the elements not prime
to `𝔪` (`Grossencharacter.finiteCharacter_eq_zero_iff`). At an element `a` prime to `𝔪` it is the
inverse of the product of the local components of `χ` at `a` over the primes dividing the finite
conductor (`Grossencharacter.finiteCharacter_eq_prod_finiteComponent_inv`), because the principal
idele of `a` is trivial for `χ`. Those components are trivial on the units congruent to `1`
modulo the conductor, so on nonzero elements the finite character depends only on the residue
modulo the finite part `𝔪₀` of `𝔪` (`Grossencharacter.finiteCharacter_eq_of_sub_mem`); no
positivity at the real places is needed, because the signs are part of `χ_∞`.

It therefore descends to a Dirichlet character of `𝓞 / 𝔪₀`, the **residue character**
(`Grossencharacter.residueCharacter`), the unique `MulChar` agreeing with `χ_f` at every nonzero
element (`Grossencharacter.existsUnique_residueCharacter`). The finite character does not descend
through `0`: it vanishes at `0`, while if `𝔪₀ = 𝓞` the residue ring has one element, a unit, where
the residue character is `1`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue`: the archimedean value `χ_∞`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: Hecke's finite character `χ_f`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: the Dirichlet character of `𝓞 / 𝔪₀`
  induced by `χ_f`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_zero_iff`: `χ_f` vanishes exactly off
  the elements prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_of_sub_mem`: on nonzero elements, `χ_f`
  depends only on the residue modulo `𝔪₀`, and `finiteCharacter_eq_one_of_sub_one_mem` is the case
  of the residue `1`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter_mk` and
  `TauCeti.LFunctions.Grossencharacter.existsUnique_residueCharacter`: the residue character is
  the unique Dirichlet character of `𝓞 / 𝔪₀` agreeing with `χ_f` at the nonzero elements.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1) and §7.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

namespace Grossencharacter

/-! ### The archimedean value -/

open scoped Classical in
/-- **The archimedean value** `χ_∞` of a presentation `χ` with algebraic infinity type `n`: the
monomial `∏_τ τ(a) ^ (n τ)`, times at each real place `w` the sign of `a` there to the power
`ε_w - n_w`, where `ε_w` is the sign parity of the archimedean restriction of `χ` and `n_w` the
parity of its algebraic exponent at `w`. The sign factors are trivial at the real places outside
`𝔪` (`Grossencharacter.realParity_eq`). On `Kˣ` this is the archimedean component of `χ`
(`archimedeanValue_eq_prod_infiniteComponent`). -/
def archimedeanValue (χ : Grossencharacter K 𝔪) : K →* ℂ where
  toFun a := (∏ τ : K →+* ℂ, τ a ^ χ.infinityType τ) *
    ∏ w : {w : InfinitePlace K // w.IsReal},
      (SignType.sign (InfinitePlace.embedding_of_isReal w.2 a) : ℂ) ^
        (χ.toHeckeCharacter.infinityType.realParity w -
          (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w).val
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_zpow, Finset.prod_mul_distrib, sign_mul, SignType.coe_mul, mul_pow]
    ring

open scoped Classical in
/-- The defining equation of the archimedean value. -/
theorem archimedeanValue_apply (χ : Grossencharacter K 𝔪) (a : K) :
    χ.archimedeanValue a = (∏ τ : K →+* ℂ, τ a ^ χ.infinityType τ) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 a) : ℂ) ^
          (χ.toHeckeCharacter.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w).val :=
  (rfl)

/-- **The archimedean value is the archimedean component of the idele class character**: on
`x ∈ Kˣ` it is the product over the infinite places `w` of the component of `χ` at the image of `x`
in `K_w`. -/
theorem archimedeanValue_eq_prod_infiniteComponent (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.archimedeanValue x = ∏ w : InfinitePlace K, (χ.toHeckeCharacter.infiniteComponent w
      (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ) := by
  rw [χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign χ.infinityType
    χ.agreesOnIdentityComponent, AlgebraicInfinityType.coe_embeddingCharacter_apply,
    archimedeanValue_apply]

/-- The archimedean value of a nonzero element is nonzero. -/
theorem archimedeanValue_ne_zero (χ : Grossencharacter K 𝔪) {a : K} (ha : a ≠ 0) :
    χ.archimedeanValue a ≠ 0 := by
  rw [← Units.val_mk0 ha, archimedeanValue_eq_prod_infiniteComponent]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ Units.ne_zero _

/-! ### The finite character -/

/-- **Hecke's finite character** `χ_f(a) = χ_u((a)) * N(a) ^ σ * χ_∞(a)` of a presentation `χ`
with unitary weight `χ_u`, ideal-side shift `σ` and archimedean value `χ_∞`. It is completely
multiplicative, vanishes exactly at the elements not prime to `𝔪`
(`finiteCharacter_eq_zero_iff`), and on nonzero elements depends only on the residue modulo the
finite part of `𝔪` (`finiteCharacter_eq_of_sub_mem`). -/
def finiteCharacter (χ : Grossencharacter K 𝔪) : 𝓞 K →*₀ ℂ where
  toFun a := χ.unitaryWeight.1 (Ideal.span {a}) *
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
      χ.archimedeanValue (algebraMap (𝓞 K) K a)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    simp only [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring

/-- The defining equation of the finite character. -/
theorem finiteCharacter_apply (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacter a = χ.unitaryWeight.1 (Ideal.span {a}) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
        χ.archimedeanValue (algebraMap (𝓞 K) K a) :=
  (rfl)

/-- **The finite character vanishes exactly at the elements not prime to the modulus.** -/
theorem finiteCharacter_eq_zero_iff (χ : Grossencharacter K 𝔪) {a : 𝓞 K} :
    χ.finiteCharacter a = 0 ↔ ¬ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  refine ⟨fun h hI ↦ ?_, fun hI ↦ by
    rw [finiteCharacter_apply, χ.unitaryWeight_eq_zero _ hI, zero_mul, zero_mul]⟩
  have hspan : Ideal.span {a} ≠ ⊥ := (Modulus.isCoprimeTo_iff.mp hI).1
  have ha : a ≠ 0 := fun ha ↦ hspan (Ideal.span_singleton_eq_bot.mpr ha)
  rw [finiteCharacter_apply] at h
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (χ.archimedeanValue_ne_zero ?_) h
  · exact norm_ne_zero_iff.mp
      ((χ.norm_unitaryWeight_apply_of_isCoprimeTo hI).trans_ne one_ne_zero)
  · refine Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr ?_))
    exact (Ideal.absNorm_eq_zero_iff.not).mpr hspan
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha

/-- **At an element prime to the modulus, the finite character is the inverse of the product of
the local components** of `χ` at that element over the primes dividing the finite conductor of
`χ`: the principal idele of the element is trivial for `χ`, its archimedean components make up
the archimedean value, and its components at the other primes make up `χ_u((a)) * N(a) ^ σ`. -/
theorem finiteCharacter_eq_prod_finiteComponent_inv (χ : Grossencharacter K 𝔪) (x : Kˣ)
    {a : 𝓞 K} (ha : algebraMap (𝓞 K) K a = x) (hI : 𝔪.IsCoprimeTo (Ideal.span {a})) :
    χ.finiteCharacter a = ((∏ v ∈ (⟨χ.toHeckeCharacter.finiteConductor,
        χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ : Modulus K).support,
      χ.toHeckeCharacter.finiteComponent v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x))⁻¹ : ℂˣ) := by
  set ψ := χ.toHeckeCharacter
  set 𝔣 : Modulus K := ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩
  have h𝔣 : 𝔣 ∣ 𝔪 :=
    Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, Finset.empty_subset _⟩
  let J : integralIdealsPrimeTo 𝔪 := ⟨Ideal.span {a}, Modulus.mem_integralIdealsPrimeTo.mpr hI⟩
  -- The ideal `(a)`, read prime to the conductor, is the principal fractional ideal of `x`.
  have hcoe : NumberFieldArithmetic.integralIdealsAwayHom K 𝔣.support
      (integralIdealsPrimeToInclusion h𝔣 J) = (toPrincipalIdeal (𝓞 K) K x : _) :=
    Units.ext (by
      rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, coe_integralIdealsPrimeToInclusion,
        coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, ha])
  have hmem : toPrincipalIdeal (𝓞 K) K x ∈ idealsPrimeTo 𝔣 :=
    hcoe ▸ (NumberFieldArithmetic.integralIdealsAwayHom K 𝔣.support _).2
  have hideal : NumberFieldArithmetic.integralIdealsAwayHom K 𝔣.support
      (integralIdealsPrimeToInclusion h𝔣 J) = ⟨_, hmem⟩ := Subtype.ext hcoe
  have hfinite := χ.coe_idealCharacter_integralIdealsAwayHom h𝔣 J
  rw [hideal, ψ.idealCharacter_apply_toPrincipalIdeal_eq_inv x hmem] at hfinite
  rw [finiteCharacter_apply, ← hfinite, ha, archimedeanValue_eq_prod_infiniteComponent,
    ← Units.coe_prod, ← Units.val_mul, mul_inv, mul_right_comm, inv_mul_cancel, one_mul]

/-- An element congruent modulo the finite part of `𝔪` to an element prime to `𝔪`, if nonzero,
is itself prime to `𝔪`. -/
private theorem isCoprimeTo_span_of_sub_mem {a b : 𝓞 K}
    (ha : 𝔪.IsCoprimeTo (Ideal.span {a})) (hab : a - b ∈ 𝔪.finitePart) (hb : b ≠ 0) :
    𝔪.IsCoprimeTo (Ideal.span {b}) := by
  refine Modulus.isCoprimeTo_iff.mpr ⟨by simpa using hb, fun v hv hvb ↦ ?_⟩
  have hvm : 𝔪.finitePart ≤ v.asIdeal := Ideal.le_of_dvd ((𝔪.mem_support_iff v).mp hv)
  refine (Modulus.isCoprimeTo_iff.mp ha).2 v hv (Ideal.dvd_span_singleton.mpr ?_)
  simpa using add_mem (hvm hab) (Ideal.dvd_span_singleton.mp hvb)

/-- **On nonzero elements, the finite character depends only on the residue modulo the finite
part of `𝔪`.** No positivity at the real places is needed: the signs there are part of the
archimedean value. -/
theorem finiteCharacter_eq_of_sub_mem (χ : Grossencharacter K 𝔪) {a b : 𝓞 K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ∈ 𝔪.finitePart) : χ.finiteCharacter a = χ.finiteCharacter b := by
  by_cases hI : 𝔪.IsCoprimeTo (Ideal.span {a})
  swap
  · have hba : b - a ∈ 𝔪.finitePart := by simpa using neg_mem hab
    rw [χ.finiteCharacter_eq_zero_iff.mpr hI, χ.finiteCharacter_eq_zero_iff.mpr
      fun hJ ↦ hI (isCoprimeTo_span_of_sub_mem hJ hba ha)]
  have hJ := isCoprimeTo_span_of_sub_mem hI hab hb
  set ψ := χ.toHeckeCharacter
  set 𝔣 : Modulus K := ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩
  have h𝔣 : 𝔣 ∣ 𝔪 :=
    Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, Finset.empty_subset _⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  let xa := Units.mk0 (algebraMap (𝓞 K) K a) ((map_ne_zero_iff _ hinj).mpr ha)
  let xb := Units.mk0 (algebraMap (𝓞 K) K b) ((map_ne_zero_iff _ hinj).mpr hb)
  rw [χ.finiteCharacter_eq_prod_finiteComponent_inv xa rfl hI,
    χ.finiteCharacter_eq_prod_finiteComponent_inv xb rfl hJ]
  congr 2
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  -- The quotient `a / b` is congruent to `1` modulo the conductor, so `χ` is trivial on it there.
  have hc : IsCongrOne 𝔣 (xb⁻¹ * xa) := by
    refine isCongrOne_iff.mpr ⟨fun v hv ↦ ?_, fun w hw ↦ absurd hw (Finset.notMem_empty w)⟩
    have hv𝔪 : v.asIdeal ∣ 𝔪.finitePart := hv.trans (Modulus.dvd_iff.mp h𝔣).1
    have hbv : b ∉ v.asIdeal := fun hbv ↦ (Modulus.isCoprimeTo_iff.mp hJ).2 v
      ((𝔪.mem_support_iff v).mpr hv𝔪) (Ideal.dvd_span_singleton.mpr hbv)
    have hsub : ((xb⁻¹ * xa : Kˣ) : K) - 1 =
        algebraMap (𝓞 K) K (a - b) * (algebraMap (𝓞 K) K b)⁻¹ := by
      have hb' : algebraMap (𝓞 K) K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
      simp only [xa, xb, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_sub]
      field_simp
    rw [hsub, map_mul, map_inv₀, v.valuation_eq_one_iff_notMem.mpr hbv, inv_one, mul_one,
      HeightOneSpectrum.valuation_of_algebraMap]
    refine ((v.intValuation_le_pow_iff_mem _ _).mpr
      (Ideal.le_of_dvd (𝔪.pow_exponent_dvd_finitePart v) hab)).trans ?_
    exact WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr (Modulus.exponent_mono h𝔣 v)))
  rw [← mul_inv_cancel_left xb xa, map_mul, map_mul,
    ψ.finiteComponent_eq_one_of_isCongrOne _ hc v hv, mul_one]

/-- **The finite character is `1` at the nonzero elements congruent to `1` modulo the finite
part of `𝔪`**, whatever their signs at the real places. -/
theorem finiteCharacter_eq_one_of_sub_one_mem (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0)
    (h : a - 1 ∈ 𝔪.finitePart) : χ.finiteCharacter a = 1 := by
  rw [χ.finiteCharacter_eq_of_sub_mem ha one_ne_zero h, map_one]

/-! ### The residue character -/

/-- Every residue class modulo the finite part of a modulus has a nonzero representative, since
the finite part is a nonzero ideal. -/
private theorem exists_ne_zero_mk_eq (𝔪 : Modulus K) (r : 𝓞 K ⧸ 𝔪.finitePart) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.Quotient.mk 𝔪.finitePart a = r := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  by_cases ha : a = 0
  · obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔪.finitePart_ne_bot
    exact ⟨m, hm0, by rw [ha, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hm⟩
  · exact ⟨a, ha, rfl⟩

/-- The residue of an element prime to the modulus is a unit of `𝓞 / 𝔪₀`. -/
private theorem isUnit_mk_of_isCoprimeTo {a : 𝓞 K} (h : 𝔪.IsCoprimeTo (Ideal.span {a})) :
    IsUnit (Ideal.Quotient.mk 𝔪.finitePart a) := by
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {a} ⊔ 𝔪.finitePart := by
    rw [(Modulus.isCoprimeTo_iff_sup_eq_top.mp h).2]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ c) ?_
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪.finitePart), Ideal.Quotient.eq]
  have : a * c - 1 = -z := by linear_combination hyz
  rw [this]
  exact neg_mem hz

/-- **The residue character** of a presentation `χ` at the modulus `𝔪`: the Dirichlet character of
`𝓞 / 𝔪₀`, `𝔪₀` the finite part of `𝔪`, whose value at a residue class is the finite character
`χ_f` at any nonzero representative (`residueCharacter_mk`). It is the unique such character
(`existsUnique_residueCharacter`). If `𝔪₀ = 𝓞` the residue ring has one element, a unit, where the
residue character is `1`, although `χ_f` vanishes at the representative `0`. -/
def residueCharacter (χ : Grossencharacter K 𝔪) : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ where
  toFun r := χ.finiteCharacter (exists_ne_zero_mk_eq 𝔪 r).choose
  map_one' := by
    obtain ⟨h0, h1⟩ := (exists_ne_zero_mk_eq 𝔪 1).choose_spec
    exact χ.finiteCharacter_eq_one_of_sub_one_mem h0
      (Ideal.Quotient.eq.mp (h1.trans (map_one _).symm))
  map_mul' r s := by
    obtain ⟨hr0, hr⟩ := (exists_ne_zero_mk_eq 𝔪 r).choose_spec
    obtain ⟨hs0, hs⟩ := (exists_ne_zero_mk_eq 𝔪 s).choose_spec
    obtain ⟨hrs0, hrs⟩ := (exists_ne_zero_mk_eq 𝔪 (r * s)).choose_spec
    rw [← map_mul χ.finiteCharacter]
    exact χ.finiteCharacter_eq_of_sub_mem hrs0 (mul_ne_zero hr0 hs0)
      (Ideal.Quotient.eq.mp (by rw [hrs, map_mul, hr, hs]))
  map_nonunit' r hr := by
    obtain ⟨-, hmk⟩ := (exists_ne_zero_mk_eq 𝔪 r).choose_spec
    exact χ.finiteCharacter_eq_zero_iff.mpr fun hI ↦ hr (hmk ▸ isUnit_mk_of_isCoprimeTo hI)

/-- **The residue character at the residue of a nonzero element is the finite character.** -/
@[simp]
theorem residueCharacter_mk (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0) :
    χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  obtain ⟨h0, hmk⟩ := (exists_ne_zero_mk_eq 𝔪 (Ideal.Quotient.mk 𝔪.finitePart a)).choose_spec
  exact χ.finiteCharacter_eq_of_sub_mem h0 ha (Ideal.Quotient.eq.mp hmk)

/-- **The residue character is the unique Dirichlet character of `𝓞 / 𝔪₀` agreeing with the
finite character at every nonzero element**: every residue class has a nonzero representative. -/
theorem existsUnique_residueCharacter (χ : Grossencharacter K 𝔪) :
    ∃! ψ : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ,
      ∀ a : 𝓞 K, a ≠ 0 → ψ (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a :=
  ⟨χ.residueCharacter, fun _ ↦ χ.residueCharacter_mk, fun ψ hψ ↦ MulChar.ext' fun r ↦ by
    obtain ⟨a, ha, rfl⟩ := exists_ne_zero_mk_eq 𝔪 r
    rw [hψ a ha, χ.residueCharacter_mk ha]⟩

end Grossencharacter

end TauCeti.LFunctions
