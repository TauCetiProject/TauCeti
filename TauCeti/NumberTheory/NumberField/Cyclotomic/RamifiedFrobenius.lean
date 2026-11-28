/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Inertia
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Quadratic.RamifiedGenerator
import TauCeti.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.Int
public import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Frobenius congruences at ramified cyclotomic primes

In a subfield of a cyclotomic field of level `pᵏ m` containing the `m`-th roots of unity,
the action on a primitive `m`-th root determines the residue Frobenius power at every prime
above `p`. In a cyclotomic extension of a quadratic field containing `√−p`, with level
prime to `p`, these congruences combine into a congruence modulo `√−p`.

The ramified congruence is the arithmetic input in `New.Parameters.norm_pow_sub_conj_partner_le`
in lsernau/grh-lean, `New/Derivatives/FormalGroup/ThetaProducts.lean` at `72fead1`. Here the
proof uses cyclotomic inertia in an ambient field rather than generators of the integers of
the subfield.
-/

public section

open Ideal NumberField

namespace IsCyclotomicExtension.Rat

/-- A prescribed action on the prime-to-`p` roots of unity gives a Frobenius congruence
modulo the radical of `(p)` in a normal cyclotomic subfield. -/
theorem sub_pow_mem_radical_span_of_apply_eq_pow {L : Type*} [Field L] [NumberField L]
    {n p m k : ℕ} [Fact p.Prime] [IsCyclotomicExtension {n} ℚ L]
    (hn : n = p ^ k * m) (hm : p.Coprime m) (E : IntermediateField ℚ L)
    {ζ : E} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(E/ℚ)) (i : ℕ) (hσ : σ ζ = ζ ^ (p ^ i))
    (x : 𝓞 E) : σ • x - x ^ (p ^ i) ∈ (span {(p : 𝓞 E)}).radical := by
  have hp : p.Prime := Fact.out
  have hm₀ : m ≠ 0 := by
    rintro rfl
    simp [hp.ne_one] at hm
  have : NeZero m := ⟨hm₀⟩
  have : NeZero n := ⟨hn ▸ mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm₀⟩
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {n} ℚ L
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  have hτ' : τ.restrictNormal E = σ := hτ
  let j : E →+* L := algebraMap E L
  have hz := hζ.map_of_injective (RingHom.injective j)
  have ha : τ (j ζ) = j ζ ^ (p ^ i) := by
    rw [← τ.restrictNormal_commutes E, hτ', hσ, map_pow]
  have he := hz.autToPow_spec ℚ τ
  rw [ha, (hz.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq, ← hz.eq_orderOf] at he
  have hunit : ZMod.unitsMap (Dvd.intro_left _ hn.symm) (galEquivZMod n L τ) =
      ZMod.unitOfCoprime p hm ^ i := by
    rw [← hz.autToPow_eq_unitsMap_galEquivZMod (Dvd.intro_left _ hn.symm)]
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow,
      ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff _ _ _).2 he
  rw [radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  have : P.IsPrime := hP
  have hpmem : (p : 𝓞 E) ∈ P := hle (mem_span_singleton_self _)
  have hPb : P ≠ ⊥ := fun h ↦ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (h ▸ hpmem)
  have : P.IsMaximal := hP.isMaximal hPb
  obtain ⟨Q, hQ, hQP⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  have : Q.IsMaximal := hQ
  have : Q.LiesOver P := hQP
  have : Q.LiesOver (span {(p : ℤ)}) := ⟨(Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (IsPrime.ne_top' (I := Q.under ℤ)) (span_le.mpr (Set.singleton_subset_iff.mpr (by
      exact (Ideal.mem_under (P := Q) (A := ℤ)).mpr (by
        rw [map_natCast]
        exact (mem_of_liesOver Q P (p : 𝓞 E)).mp hpmem))))⟩
  have hres := image_unitsMap_fiber_eq_setOf_forall_quotient_mk_smul_eq_pow hn hm E Q i
  rw [← Q.over_def P] at hres
  have hres' : σ ∈ {γ : Gal(E/ℚ) | ∀ y : 𝓞 E,
      Ideal.Quotient.mk P (γ • y) = Ideal.Quotient.mk P y ^ (p ^ i)} :=
    hres ▸ ⟨galEquivZMod n L τ, hunit, by simpa only [MulEquiv.symm_apply_apply] using hτ'⟩
  exact Ideal.Quotient.eq.mp ((hres' x).trans (map_pow _ _ _).symm)

end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

/-- In the cyclotomic compositum of a quadratic field containing `π = √−p` with the
`m`-th roots of unity (`p ∤ m`), an automorphism acting by the exponent `p^i` on those roots
agrees with the `i`-th power of Frobenius modulo `π`. The automorphism need not fix the
quadratic field. -/
theorem dvd_smul_sub_pow_of_sq_eq_neg_prime {L K : Type*} [Field L] [NumberField L]
    [Field K] [NumberField K] {p m : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p * m} ℚ L] (hm : p.Coprime m)
    (E : IntermediateField ℚ L) [Algebra K E] [IsCyclotomicExtension {m} K E]
    (hK : Module.finrank ℚ K = 2) {π : 𝓞 K} (hπ : π ^ 2 = -(p : 𝓞 K))
    {ζ : E} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(E/ℚ)) (i : ℕ) (hσ : σ ζ = ζ ^ (p ^ i))
    (x : 𝓞 E) : algebraMap (𝓞 K) (𝓞 E) π ∣ σ • x - x ^ (p ^ i) := by
  let P : Ideal (𝓞 K) := span {π}
  have hp : p.Prime := Fact.out
  have hPnorm : P.absNorm = p := NumberField.absNorm_span_singleton_of_sq_eq_neg_natCast hK hπ
  have : P.IsPrime := isPrime_of_irreducible_absNorm (hPnorm ▸ hp)
  have hP₀ : P ≠ ⊥ := by
    intro h
    simp [h] at hPnorm
    exact hp.ne_zero hPnorm.symm
  have : P.IsMaximal := IsPrime.isMaximal inferInstance hP₀
  have hmP : (m : 𝓞 K) ∉ P := by
    have hpP : (p : 𝓞 K) ∈ P := by
      rw [← neg_neg (p : 𝓞 K), ← hπ]
      exact P.neg_mem (P.pow_mem_of_mem (mem_span_singleton_self _) _ (by decide))
    have hover : P.LiesOver (span {(p : ℤ)}) := ⟨(Int.ideal_span_isMaximal_of_prime p).eq_of_le
      (IsPrime.ne_top' (I := P.under ℤ)) (span_le.mpr (Set.singleton_subset_iff.mpr (by
        exact (Ideal.mem_under (P := P) (A := ℤ)).mpr (by rwa [map_natCast]))))⟩
    intro hmem
    have hh := (mem_of_liesOver P (span {(p : ℤ)}) (m : ℤ)).mpr (by simpa using hmem)
    exact (hp.coprime_iff_not_dvd.mp hm) (Int.natCast_dvd_natCast.mp (mem_span_singleton.mp hh))
  have hunr : Algebra.IsUnramifiedIn (𝓞 E) P := fun Q _ _ ↦
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E m hmP Q
  have hrad := hunr.isRadical_map
  have hmap : P.map (algebraMap (𝓞 K) (𝓞 E)) = span {algebraMap (𝓞 K) (𝓞 E) π} := by
    simp [P, map_span]
  have hsq : (P.map (algebraMap (𝓞 K) (𝓞 E))) ^ 2 = span {(p : 𝓞 E)} := by
    rw [hmap, Ideal.span_singleton_pow, ← map_pow, hπ, map_neg, map_natCast,
      Ideal.span_singleton_neg]
  have h := sub_pow_mem_radical_span_of_apply_eq_pow (k := 1) (by rw [pow_one]) hm E hζ σ i hσ x
  rw [← hsq, radical_pow _ (by decide : (2 : ℕ) ≠ 0), hrad.radical, hmap,
    mem_span_singleton] at h
  exact h

/-- At any nonarchimedean embedding of the compositum, conjugation after the signed
cyclotomic action `ζ ↦ ζ^(-p^i)` agrees with the `p^i`-th power on algebraic integers
up to an error of norm at most the norm of `√−p`. -/
theorem norm_pow_sub_conj_apply_le_of_sq_eq_neg_prime {L K F : Type*} [Field L] [NumberField L]
    [Field K] [NumberField K] [NormedField F] [IsUltrametricDist F]
    {p m : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p * m} ℚ L]
    (hm : p.Coprime m) (E : IntermediateField ℚ L) [IsCMField E]
    [Algebra K E] [IsCyclotomicExtension {m} K E]
    (hK : Module.finrank ℚ K = 2) {π : 𝓞 K} (hπ : π ^ 2 = -(p : 𝓞 K))
    {ζ : E} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(E/ℚ)) (i : ℕ)
    (hσ : σ ζ = (ζ ^ (p ^ i))⁻¹) (e : E →+* F) (x : 𝓞 E) :
    ‖(e (x : E)) ^ (p ^ i) - e (IsCMField.complexConj E (σ (x : E)))‖ ≤
      ‖e (algebraMap K E (π : K))‖ := by
  let c := (IsCMField.complexConj E).restrictScalars ℚ
  have hm₀ : m ≠ 0 := by
    rintro rfl
    simp [(Fact.out : p.Prime).ne_one] at hm
  let ι : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  have hc : c ζ = ζ⁻¹ := by
    apply ι.injective
    have hconj : ι (c ζ) = (starRingEnd ℂ) (ι ζ) :=
      IsCMField.complexEmbedding_complexConj E ι ζ
    rw [hconj, map_inv₀]
    have hz : (ι ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hm₀)).symm
  have hact : (c * σ) ζ = ζ ^ (p ^ i) := by
    simp [AlgEquiv.mul_apply, hσ, hc]
  obtain ⟨y, hy⟩ := dvd_smul_sub_pow_of_sq_eq_neg_prime hm E hK hπ hζ (c * σ) i hact x
  have hπmap : algebraMap (𝓞 E) E (algebraMap (𝓞 K) (𝓞 E) π) =
      algebraMap K E (π : K) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K E,
      ← RingOfIntegers.coe_eq_algebraMap]
  have hsub : e (IsCMField.complexConj E (σ (x : E))) - e (x : E) ^ (p ^ i) =
      e (algebraMap K E (π : K)) * e (y : E) := by
    simpa only [RingHom.comp_apply, map_sub, map_pow, map_mul, algebraMap_smul_eq_apply,
      AlgEquiv.mul_apply, hπmap, ← RingOfIntegers.coe_eq_algebraMap, c,
      AlgEquiv.restrictScalars_apply] using congrArg (e.comp (algebraMap (𝓞 E) E)) hy
  have hy₁ : ‖e (y : E)‖ ≤ 1 :=
    IsUltrametricDist.norm_le_one_of_isIntegral (fun _ _ _ ↦ norm_pow _ _)
      (y.isIntegral_coe.map e.toIntAlgHom)
  rw [norm_sub_rev, hsub, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hy₁

end IsCyclotomicExtension.Rat
