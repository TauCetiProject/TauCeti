/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.DirichletCharacter.FrobeniusCoset
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.CMField
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius.Coset
import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction

/-!
# Excluding complex conjugation at the ramified auxiliary prime

At the second auxiliary prime `d`, the odd quadratic character modulo `q` detects complex
conjugation and forces a Frobenius exponent to be odd. The real cyclotomic residue then excludes
that odd exponent: `d` reduces to a nonsign involution at the appropriate dyadic level. These
arguments take place on the prime-to-`d` part of the cyclotomic modulus, so they apply even when
`d` ramifies in the host.

For the cyclotomic description of Frobenius, see Washington, *Introduction to Cyclotomic
Fields*, Chapter 2.
-/

public section

namespace MonoidHom

variable {N q d m : ℕ} [NeZero N] {G : Type*} [Group G]

/-- Suppose the kernel of a cyclotomic quotient is trivial under the odd quadratic character
modulo `q` and reduces to signs modulo `m`. If `d` has quadratic character `-1` modulo `q`
and is a nonsign involution modulo `m`, no Frobenius coset at `d` contains the image of complex
conjugation. The auxiliary modulus `m` need not be a power of two, and the exponent includes
zero (the inertia coset). -/
theorem map_neg_one_notMem_frobeniusCoset_of_quadraticChar [Fact q.Prime]
    (f : (ZMod N)ˣ →* G) (hd : d.Prime) (hq : q ∣ ordCompl[d] N) (hm : m ∣ ordCompl[d] N)
    (hqodd : quadraticChar (ZMod q) (-1) = -1) (hqd : quadraticChar (ZMod q) (d : ZMod q) = -1)
    (hdm : (d : ZMod m) ^ 2 = 1) (hdm₁ : (d : ZMod m) ≠ 1) (hdm₂ : (d : ZMod m) ≠ -1)
    (hχ : ∀ u ∈ f.ker, quadraticChar (ZMod q) (ZMod.unitsMap (hq.trans (Nat.ordCompl_dvd N d)) u :
      ZMod q) = 1)
    (hsign : ∀ u ∈ f.ker, let v := (ZMod.unitsMap (hm.trans (Nat.ordCompl_dvd N d)) u : ZMod m)
      v = 1 ∨ v = -1) (i : ℕ) : f (-1) ∉ f.frobeniusCoset hd i := by
  intro hmem
  obtain ⟨u, hu, hfu⟩ := (f.mem_frobeniusCoset_iff hd).mp hmem
  have hker : (-1) * u ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, hfu, ← map_mul]
    simp
  have hreduce {k : ℕ} (hk : k ∣ ordCompl[d] N) :
      (ZMod.unitsMap (hk.trans (Nat.ordCompl_dvd N d)) ((-1) * u) : ZMod k) =
        -(d : ZMod k) ^ i := by
    rw [← ZMod.unitsMap_comp hk (Nat.ordCompl_dvd N d), MonoidHom.comp_apply, map_mul, hu,
      map_mul, map_pow]
    simp [ZMod.unitsMap_val, ZMod.cast_neg (Nat.ordCompl_dvd N d),
      ZMod.cast_neg hk, ZMod.cast_one (Nat.ordCompl_dvd N d), ZMod.cast_one hk,
      ZMod.cast_natCast hk]
  have hparity := hχ _ hker
  rw [hreduce hq, ← neg_one_mul, map_mul, map_pow, hqodd, hqd, neg_one_mul, neg_eq_iff_eq_neg]
    at hparity
  have hi : Odd i := (neg_one_pow_eq_neg_one_iff_odd (by decide)).mp hparity
  have hp : (d : ZMod m) ^ i = d := by
    obtain ⟨j, rfl⟩ := hi
    rw [pow_succ, pow_mul, hdm, one_pow, one_mul]
  have h := hsign _ hker
  dsimp only at h
  rw [hreduce hm, hp] at h
  rcases h with h | h
  · exact hdm₂ (neg_eq_iff_eq_neg.mp h)
  · exact hdm₁ (neg_injective h)

end MonoidHom

open IsCyclotomicExtension.Rat NumberField NumberField.IsCMField
open scoped NumberField Pointwise

namespace Ideal

/-- At the auxiliary prime `d ≡ 7 mod 16`, a CM subfield of a cyclotomic field splits above its
maximal real subfield if its fixing group reduces to signs modulo `16` and to squares modulo
`q`, where `q ≡ 3 mod 4` is a prime dividing `d + 1`. The criterion works at any ambient level
divisible by `16q`; in particular the ambient extension may ramify at `d`. -/
theorem ncard_primesOver_eq_two_of_auxiliary_congruences {N q d : ℕ} [NeZero N] [Fact q.Prime]
    {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]
    (E : IntermediateField ℚ L) [IsCMField E]
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(d : ℤ)})]
    (hd : d.Prime) (hqN : q ∣ N) (h16N : 16 ∣ N) (hq4 : q % 4 = 3) (hd16 : d % 16 = 7)
    (hqd : q ∣ d + 1)
    (hχ : ∀ σ ∈ E.fixingSubgroup,
      quadraticChar (ZMod q) (ZMod.unitsMap hqN (galEquivZMod N L σ) : ZMod q) = 1)
    (hsign : ∀ σ ∈ E.fixingSubgroup,
      let v := (ZMod.unitsMap h16N (galEquivZMod N L σ) : ZMod 16)
      v = 1 ∨ v = -1) :
    ((P.under (𝓞 (maximalRealSubfield E))).primesOver (𝓞 E)).ncard = 2 := by
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {N} ℚ L
  let r := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := L) E
  let f := r.comp (galEquivZMod N L).symm.toMonoidHom
  have hq : q ∣ ordCompl[d] N := Nat.dvd_ordCompl_of_dvd_not_dvd hqN fun h ↦ by
    have hdq : d = q := (Nat.dvd_prime (Fact.out : q.Prime)).mp h |>.resolve_left hd.ne_one
    exact hd.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl d)).mpr (hdq.symm ▸ hqd))
  have h16 : 16 ∣ ordCompl[d] N := Nat.dvd_ordCompl_of_dvd_not_dvd h16N fun h ↦ by
    have h2 : d ∣ 2 := hd.dvd_of_dvd_pow (n := 4) (by norm_num [h])
    have : d = 2 := (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hd.ne_one
    omega
  have hodd : quadraticChar (ZMod q) (-1) = -1 :=
    (quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; omega)).trans
      (by simpa only [ZMod.card] using ZMod.χ₄_nat_three_mod_four hq4)
  have hdq : (d : ZMod q) = -1 := by
    have hz : (↑(d + 1) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hqd
    exact eq_neg_of_add_eq_zero_left (by simpa using hz)
  have hdm : (d : ZMod 16) = 7 := (ZMod.natCast_eq_natCast_iff' d 7 16).2 hd16
  have hker (u : (ZMod N)ˣ) (hu : u ∈ f.ker) :
      (galEquivZMod N L).symm u ∈ E.fixingSubgroup := by
    simpa only [← E.restrictNormalHom_ker, MonoidHom.mem_ker, f, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom] using hu
  have hconj : f (-1) = (complexConj E).restrictScalars ℚ := by
    let φ : L →+* ℂ := Classical.choice inferInstance
    refine AlgEquiv.ext fun x ↦ (φ.comp E.val.toRingHom).injective ?_
    rw [AlgEquiv.restrictScalars_apply, complexEmbedding_complexConj]
    have heq : E.val (f (-1) x) = (galEquivZMod N L).symm (-1) (E.val x) :=
      AlgEquiv.restrictNormal_commutes ((galEquivZMod N L).symm (-1)) E x
    exact (congrArg φ heq).trans
      (TauCeti.IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply
        N φ (E.val x))
  rw [P.ncard_primesOver_eq_two_iff_complexConj_notMem_stabilizer]
  intro h
  obtain ⟨Q, hQprime, hQover⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 L))).some
  have : Q.IsPrime := hQprime
  have : Q.LiesOver P := hQover
  have : Q.LiesOver (Ideal.span {(d : ℤ)}) := LiesOver.trans Q P _
  have hstab : (complexConj E).restrictScalars ℚ ∈ MulAction.stabilizer (E ≃ₐ[ℚ] E)
      (Q.under (𝓞 E)) := by
    rw [← Q.over_def P, MulAction.mem_stabilizer_iff, restrictScalars_smul_ideal]
    exact MulAction.mem_stabilizer_iff.mp h
  obtain ⟨i, hi⟩ := Q.exists_mem_frobeniusCoset_of_mem_stabilizer (N := N) hd E hstab
  exact f.map_neg_one_notMem_frobeniusCoset_of_quadraticChar hd hq h16 hodd (hdq ▸ hodd)
    (hdm ▸ by decide) (hdm ▸ by decide) (hdm ▸ by decide)
    (fun u hu ↦ by simpa using hχ _ (hker u hu))
    (fun u hu ↦ by simpa using hsign _ (hker u hu)) i (hconj ▸ hi)

end Ideal
