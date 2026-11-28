/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.ResidueDegree.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Residue degrees after adjoining roots of unity

In a tower of number fields `K ⊆ L ⊆ L(μₘ)`, let `𝔭` be a prime of `K` away from `m`.
If a prime of `L` above `𝔭` has residue degree `f`, the relative Frobenius after adjoining
`μₘ` acts by the `N(𝔭)^f`-power map. Consequently the residue degree over `K` is
`lcm(f, ordₘ(N(𝔭)))`. The step `L/K` need not be Galois or unramified.

For the cyclotomic extension of a quadratic field, this gives the norm of a prime over an
inert rational prime `p` in terms of the order of `−p` modulo `m`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §§9–10.
* The inert-prime norm normalization in `New.Parameters.q_eq_pow_lcm_of_inert`,
  lsernau/grh-lean, `grh/src/New/Derivatives/Field/PrimeDecomposition.lean` (commit `72fead1`).
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace Ideal

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The residue degree over `K` after adjoining the `m`-th roots of unity to `L` is the least
common multiple of the residue degree in `L/K` and the order of the base prime's norm modulo
`m`, provided the base prime does not divide `m`. -/
theorem inertiaDeg_eq_lcm_of_isCyclotomicExtension {m : ℕ} [IsCyclotomicExtension {m} L M]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] (𝔭 : HeightOneSpectrum (𝓞 K)) [Q.LiesOver 𝔭.asIdeal]
    (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    Q.inertiaDeg (𝓞 K) =
      ((Q.under (𝓞 L)).inertiaDeg (𝓞 K)).lcm (orderOf (absNorm 𝔭.asIdeal : ZMod m)) := by
  let : NeZero m := ⟨fun h ↦ hm (by simp [h])⟩
  let : NumberField M := IsCyclotomicExtension.numberField {m} L M
  let : IsGalois L M := IsCyclotomicExtension.isGalois {m} L M
  have hQ : Q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  let : Finite (𝓞 M ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQ
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨Q.under (𝓞 L), inferInstance, IsIntegral.under_ne_bot (𝓞 L) hQ⟩
  let : Q.LiesOver P.asIdeal := over_under Q
  let : P.asIdeal.LiesOver 𝔭.asIdeal := LiesOver.tower_bot Q P.asIdeal 𝔭.asIdeal
  have hmP : (m : 𝓞 L) ∉ P.asIdeal := fun h ↦
    hm ((mem_of_liesOver P.asIdeal 𝔭.asIdeal (m : 𝓞 K)).mpr (by simpa only [map_natCast] using h))
  let σ := arithFrobAt (𝓞 L) (M ≃ₐ[L] M) Q
  have hσ : IsArithFrobAt (𝓞 L) σ Q := IsArithFrobAt.arithFrobAt _ _ _
  have hζ := IsCyclotomicExtension.zeta_spec m L M
  have hnorm := hσ.autToPow_eq_absNorm hζ P hmP Q
  have hrel := hζ.inertiaDeg_eq_orderOf_of_val_eq_absNorm P hmP Q hσ _ hnorm
  have hreldeg : Q.inertiaDeg (𝓞 L) = orderOf ((absNorm 𝔭.asIdeal : ZMod m) ^
      P.asIdeal.inertiaDeg (𝓞 K)) := by
    rw [hrel, ← orderOf_units, hnorm, ← absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal, Nat.cast_pow]
  let f := P.asIdeal.inertiaDeg (𝓞 K)
  let a : ZMod m := absNorm 𝔭.asIdeal
  have hf : f ≠ 0 := (inertiaDeg_pos (R := 𝓞 K) (q := P.asIdeal)).ne'
  calc
    Q.inertiaDeg (𝓞 K) = f * orderOf (a ^ f) := (inertiaDeg_tower P.asIdeal Q).trans
      (congrArg (f * ·) hreldeg)
    _ = f.lcm (orderOf a) := by
      rw [orderOf_pow' _ hf, Nat.lcm_eq_mul_div, Nat.gcd_comm (orderOf a),
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

section Rational

variable {F E : Type*} [Field F] [NumberField F] [Field E] [Algebra F E]
  {m p : ℕ} [IsCyclotomicExtension {m} F E]

/-- Over a rational prime `p` coprime to `m`, the residue degree after adjoining the `m`-th
roots of unity is the least common multiple of the degree in the original field and the
order of `p` modulo `m`. -/
theorem inertiaDeg_eq_lcm_of_isCyclotomicExtension_rat
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (hp : p.Prime) (hpm : p.Coprime m) :
    Q.inertiaDeg ℤ = ((Q.under (𝓞 F)).inertiaDeg ℤ).lcm (orderOf (p : ZMod m)) := by
  let : NumberField E := IsCyclotomicExtension.numberField {m} F E
  obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
  have hspan : Q.LiesOver (span {((absNorm v.asIdeal : ℕ) : ℤ)}) := by
    simpa only [hv] using (inferInstance : Q.LiesOver (span {(p : ℤ)}))
  let : Q.LiesOver v.asIdeal := Rat.HeightOneSpectrum.liesOver_of_liesOver_span_absNorm v Q
  have hm : (m : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd, hv]
    exact hp.coprime_iff_not_dvd.mp hpm
  simpa only [inertiaDeg_ringOfIntegers_rat_eq_int, hv] using
    (Q.inertiaDeg_eq_lcm_of_isCyclotomicExtension (L := F) v hm)

/-- If the prime below `Q` has residue degree two over `p`, as for an inert prime in a
quadratic field, the norm of `Q` is `p ^ lcm(2, ordₘ(−p))` after adjoining the `m`-th roots
of unity, for `p` coprime to `m`. -/
theorem absNorm_eq_pow_lcm_orderOf_neg_of_inertiaDeg_eq_two [NumberField E]
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (hp : p.Prime) (hpm : p.Coprime m) (hf : (Q.under (𝓞 F)).inertiaDeg ℤ = 2) :
    absNorm Q = p ^ (2 : ℕ).lcm (orderOf (-(p : ZMod m))) := by
  have hdeg := Q.inertiaDeg_eq_lcm_of_isCyclotomicExtension_rat (F := F) hp hpm
  rw [← natAbs_pow_inertiaDeg (p : ℤ) Q, Int.natAbs_natCast, hdeg, hf]
  congr 1
  -- The two least common multiples divide exactly the same exponents.
  apply Nat.dvd_right_iff_eq.mp
  intro n
  simp only [Nat.lcm_dvd_iff, orderOf_dvd_iff_pow_eq_one]
  by_cases hn : 2 ∣ n
  · rw [(even_iff_two_dvd.mpr hn).neg_pow]
  · simp [hn]

end Rational

end Ideal
