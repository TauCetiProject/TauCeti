/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Prime
import TauCeti.FieldTheory.Galois.SquareRoot
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.NumberTheory.LegendreSymbol.Five
import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Global Artin symbols in `ℚ(√5)` and in the fifth cyclotomic field

The quadratic subfield of `ℚ(ζ₅)` is `ℚ(√5)`. This file computes the global Artin symbols of
primes in both fields and checks that they are compatible under restriction.

For `ℚ(√5)`, given by a generator `s` with `s² = 5`, the global Artin symbol of a prime `ℓ ≠ 5`
fixes `s` when `ℓ ≡ ±1 (mod 5)` and negates it when `ℓ ≡ ±2 (mod 5)`
(`globalArtinMap_Qsqrt5_prime_apply`, `globalArtinMap_Qsqrt5_prime`). In particular it is trivial
exactly at the primes `ℓ ≡ ±1 (mod 5)` (`globalArtinMap_Qsqrt5_prime_eq_zero_iff`). The symbol is
an arithmetic Frobenius by `globalArtinMap_isArithFrobAt`. At an odd prime, a Frobenius
multiplies `s` by the Legendre symbol `(5/ℓ)`, and quadratic reciprocity turns `(5/ℓ) = 1` into
`ℓ ≡ ±1 (mod 5)`. At `ℓ = 2` it negates `s`, since `5 ≡ 5 (mod 8)`. The prime `2` is unramified
because `5 ≡ 1 (mod 4)`.

For `ℚ(ζ₅)`, the symbol of `ℓ ≠ 5` is the automorphism with cyclotomic coordinate `ℓ mod 5`
(`galEquivZMod_globalArtinMap_prime`). It fixes the quadratic subfield exactly when `ℓ` is a
square modulo `5`, that is, when `ℓ ≡ ±1 (mod 5)` (`globalArtinMap_zeta5_restrict_Qsqrt5`). The
proof is group-theoretic. The quadratic subfield is fixed by a subgroup of index two in the cyclic
group `Gal(ℚ(ζ₅)/ℚ) ≃ (ℤ/5ℤ)ˣ` of order four, and that subgroup consists of the squares.

The two computations give the same answer. This is the compatibility of the global Artin map with
restriction to a subfield. A geometric normalization would give the same answers here, since the
symbol in `ℚ(√5)` is an involution and squares in `(ℤ/5ℤ)ˣ` are closed under inversion. The
non-involutive check is `globalArtinMap_zeta5_two`.

## Main results

* `TauCeti.ClassFieldTheory.globalArtinMap_Qsqrt5_prime`: the Artin symbol of `ℓ ≠ 5` in
  `ℚ(√5)` is trivial if `ℓ ≡ ±1 (mod 5)` and negates `√5` if `ℓ ≡ ±2 (mod 5)`.
* `TauCeti.ClassFieldTheory.globalArtinMap_Qsqrt5_prime_apply`: the action of the Artin symbol of
  `ℓ ≠ 5` on `√5`.
* `TauCeti.ClassFieldTheory.globalArtinMap_Qsqrt5_prime_eq_zero_iff`: the Artin symbol of `ℓ ≠ 5`
  in `ℚ(√5)` is trivial exactly when `ℓ ≡ ±1 (mod 5)`.
* `TauCeti.ClassFieldTheory.globalArtinMap_zeta5_restrict_Qsqrt5`: an automorphism representing
  the Artin symbol of `ℓ ≠ 5` in `ℚ(ζ₅)` fixes the quadratic subfield exactly when
  `ℓ ≡ ±1 (mod 5)`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3, and Chapter VII, Example 8.2.
* D. A. Cox, *Primes of the Form x² + ny²*, §5.A.
-/

public noncomputable section

open IsDedekindDomain NumberField IsCyclotomicExtension
open scoped IsMulCommutative

namespace TauCeti.ClassFieldTheory

section Sqrt5

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {s : E}

/-- An automorphism representing the Artin symbol of a prime `ℓ ≠ 5` in `ℚ(√5)` fixes `√5`
exactly when `ℓ ≡ ±1 (mod 5)`. -/
private lemma globalArtinMap_Qsqrt5_prime_apply_eq_self_iff (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    (hs : s ^ 2 = 5) (hgen : IntermediateField.adjoin ℚ {s} = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) = .ofMul (Abelianization.of σ)) :
    σ s = s ↔ Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 := by
  have hr : ∀ _ : Unit, s ^ 2 = algebraMap ℤ E 5 := fun _ ↦ by simpa using hs
  have htop : IntermediateField.adjoin ℚ (Set.range fun _ : Unit ↦ s) = ⊤ := by
    rwa [Set.range_const]
  have := Multiquadratic.isMulCommutative_of_adjoin_eq_top (d := fun _ : Unit ↦ (5 : ℚ))
    (fun _ ↦ by rw [hs, map_ofNat]) htop
  obtain ⟨p, hpv⟩ : ∃ p, Ideal.absNorm v.asIdeal = p := ⟨_, rfl⟩
  have : Fact p.Prime := ⟨by
    rw [← hpv, Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hp5 : ¬ (p : ℤ) ∣ 5 := by
    have := mt (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd v (n := 5)).mpr
      (by exact_mod_cast hv)
    rw [hpv] at this
    exact_mod_cast this
  -- A prime of `ℚ(√5)` above `v`, read as a prime above the rational prime `p`.
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hpv ▸ Rat.HeightOneSpectrum.liesOver_span_absNorm v Q
  rw [hpv]
  by_cases hodd : p = 2
  · subst hodd
    have := Multiquadratic.isUnramifiedAt_of_forall_mod_four_eq_one hr htop (by norm_num) Q
    have hF := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q).mp
      (globalArtinMap_isArithFrobAt E ι v Q hσ)
    rw [isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight (hr ()) (by norm_num) Q hF]
    norm_num
  · have := Multiquadratic.isUnramifiedAt_of_forall_not_dvd hr htop hodd (fun _ ↦ hp5) Q
    have hF := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q).mp
      (globalArtinMap_isArithFrobAt E ι v Q hσ)
    rw [NumberField.isArithFrobAt_apply_sqrt_eq_self_iff hodd hp5 (hr ()) Q hF,
      legendreSym_five_eq_one_iff hodd]

/-- **The global Artin symbol in `ℚ(√5)`.** Let `s` generate `E` over `ℚ` with `s² = 5`. Any
automorphism representing the Artin symbol of a prime `ℓ ≠ 5` fixes `s` if `ℓ ≡ ±1 (mod 5)`, and
negates it otherwise. -/
theorem globalArtinMap_Qsqrt5_prime_apply (ι : E →ₐ[ℚ] SeparableClosure ℚ) (hs : s ^ 2 = 5)
    (hgen : IntermediateField.adjoin ℚ {s} = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) = .ofMul (Abelianization.of σ)) :
    σ s = if Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 then s else -s := by
  have h := globalArtinMap_Qsqrt5_prime_apply_eq_self_iff ι hs hgen v hv hσ
  split_ifs with hc
  · exact h.mpr hc
  · exact (σ.apply_eq_or_eq_neg_of_sq_eq (c := (5 : ℚ)) (by rw [hs, map_ofNat])).resolve_left
      (mt h.mp hc)

/-- **The global Artin symbol in `ℚ(√5)`.** Let `s` generate `E` over `ℚ` with `s² = 5`. Any
automorphism representing the Artin symbol of a prime `ℓ ≠ 5` is the identity if
`ℓ ≡ ±1 (mod 5)`, and negates `s` if `ℓ ≡ ±2 (mod 5)`. -/
theorem globalArtinMap_Qsqrt5_prime (ι : E →ₐ[ℚ] SeparableClosure ℚ) (hs : s ^ 2 = 5)
    (hgen : IntermediateField.adjoin ℚ {s} = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) = .ofMul (Abelianization.of σ)) :
    (Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 → σ = 1) ∧
      (Ideal.absNorm v.asIdeal % 5 = 2 ∨ Ideal.absNorm v.asIdeal % 5 = 3 → σ s = -s) := by
  have h := globalArtinMap_Qsqrt5_prime_apply ι hs hgen v hv hσ
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · rw [ite_eq_left hc] at h
    exact TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top hgen fun x hx ↦
      Set.mem_singleton_iff.mp hx ▸ h
  · rwa [ite_eq_right (by omega)] at h

/-- The global Artin symbol of a prime `ℓ ≠ 5` in `ℚ(√5)` is trivial exactly when
`ℓ ≡ ±1 (mod 5)`. -/
theorem globalArtinMap_Qsqrt5_prime_eq_zero_iff (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    (hs : s ^ 2 = 5) (hgen : IntermediateField.adjoin ℚ {s} = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) :
    globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) = 0 ↔
      Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 := by
  refine ⟨fun h ↦ (globalArtinMap_Qsqrt5_prime_apply_eq_self_iff ι hs hgen v hv (σ := 1)
    (by rw [h, map_one, ofMul_one])).mp rfl, fun hc ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := Abelianization.exists_eq_ofMul_of
    (globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)))
  rw [hσ, (globalArtinMap_Qsqrt5_prime ι hs hgen v hv hσ).1 hc, map_one, ofMul_one]

end Sqrt5

section Zeta5

variable {E : Type} [Field E] [NumberField E] [IsCyclotomicExtension {5} ℚ E]

local instance isGalois_zeta5 : IsGalois ℚ E := IsCyclotomicExtension.isGalois {5} ℚ E

/-- **Restricting the Artin symbol of `ℚ(ζ₅)` to `ℚ(√5)`.** Let `M` be the quadratic subfield of
the fifth cyclotomic field. An automorphism representing the global Artin symbol of a prime
`ℓ ≠ 5` fixes `M` exactly when `ℓ` is a square modulo `5`, that is, when `ℓ ≡ ±1 (mod 5)`. -/
theorem globalArtinMap_zeta5_restrict_Qsqrt5 (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    {M : IntermediateField ℚ E} (hM : Module.finrank ℚ M = 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (5 : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) = .ofMul (Abelianization.of σ)) :
    (∀ x ∈ M, σ x = x) ↔ Ideal.absNorm v.asIdeal % 5 = 1 ∨ Ideal.absNorm v.asIdeal % 5 = 4 := by
  rw [← IntermediateField.mem_fixingSubgroup_iff]
  have hH : M.fixingSubgroup.index = 2 :=
    (IntermediateField.finrank_eq_fixingSubgroup_index E M).symm.trans hM
  have hval : (Rat.galEquivZMod 5 E σ : ZMod 5).val = Ideal.absNorm v.asIdeal % 5 := by
    rw [galEquivZMod_globalArtinMap_prime ι v hv hσ, ZMod.val_natCast]
  rw [← hval, ← (by decide : ∀ c : (ZMod 5)ˣ,
    (c = 1 ∨ c = -1) ↔ ((c : ZMod 5).val = 1 ∨ (c : ZMod 5).val = 4)) _]
  constructor
  · -- An element of `(ℤ/5ℤ)ˣ` other than `±1` generates it, so the fixing group would be
    -- everything, of index one.
    intro hσH
    by_contra hc
    rw [not_or] at hc
    have hgen : ∀ d : (ZMod 5)ˣ, ∃ k < 4, d = Rat.galEquivZMod 5 E σ ^ k :=
      (by decide : ∀ c : (ZMod 5)ˣ, c ≠ 1 → c ≠ -1 → ∀ d, ∃ k < 4, d = c ^ k) _ hc.1 hc.2
    have htop : M.fixingSubgroup = ⊤ := (Subgroup.eq_top_iff' _).mpr fun τ ↦ by
      obtain ⟨k, -, hk⟩ := hgen (Rat.galEquivZMod 5 E τ)
      have hτ : τ = σ ^ k := (Rat.galEquivZMod 5 E).injective (by rw [map_pow]; exact hk)
      exact hτ ▸ pow_mem hσH k
    rw [htop, Subgroup.index_top] at hH
    exact absurd hH (by norm_num)
  · -- `±1` are squares in `(ℤ/5ℤ)ˣ`, and a subgroup of index two contains every square.
    intro hc
    obtain ⟨d, hd⟩ := (by decide : ∀ c : (ZMod 5)ˣ, c = 1 ∨ c = -1 → ∃ d : (ZMod 5)ˣ, c = d ^ 2)
      _ hc
    have hσd : σ = ((Rat.galEquivZMod 5 E).symm d) ^ 2 := (Rat.galEquivZMod 5 E).injective
      (by rw [map_pow, MulEquiv.apply_symm_apply]; exact hd)
    exact hσd ▸ Subgroup.sq_mem_of_index_two hH _

end Zeta5

end TauCeti.ClassFieldTheory
