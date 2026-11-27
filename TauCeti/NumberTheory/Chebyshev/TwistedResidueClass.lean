/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import TauCeti.NumberTheory.Chebyshev.ResidueClass
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Summatory errors for twisted von Mangoldt weights

A prime number theorem in reduced residue classes gives a summatory estimate for any
periodic weight supported on those classes. For a nonprincipal twist of coprime modulus,
the Chinese remainder theorem makes the weighted main term zero. In particular, the
signed weight `Λ(n) * (1 - χ(n))` restricted to a reduced progression has the same main
term as the untwisted weight. This is the summatory-error input for partial summation
of the corresponding normalized Riesz remainder.

For the prime number theorem in progressions, see Davenport, *Multiplicative Number
Theory*, 3rd ed., Chapter 20.
-/

public section

open Asymptotics ArithmeticFunction Filter Finset

namespace Chebyshev

/-- Transfer a common progression error bound to a weighted von Mangoldt sum. The main
term is the ordinary progression main term times the sum of the weights on reduced
classes (equivalently, on all classes, since the remaining weights vanish). -/
theorem isBigO_sum_vonMangoldt_smul_sub {q : ℕ} [NeZero q] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (w : ZMod q → E)
    (hw : ∀ a, ¬ IsUnit a → w a = 0) {g : ℝ → ℝ}
    (hψ : ∀ a : ZMod q, IsUnit a → (fun x ↦ psiAP q a x - x / q.totient) =O[atTop] g) :
    (fun x ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt n • w n) -
      (x / q.totient : ℝ) • ∑ a, w a) =O[atTop] g := by
  classical
  have h (a : ZMod q) :
      (fun x ↦ (psiAP q a x - x / q.totient) • w a) =O[atTop] g := by
    by_cases ha : IsUnit a
    · exact ((hψ a ha).smul (isBigO_const_const (w a) one_ne_zero atTop)).congr_right
        (fun x ↦ mul_one (g x))
    · simpa only [hw a ha, smul_zero] using (isBigO_zero (E' := E) g atTop)
  refine (IsBigO.fun_sum (s := univ) (fun a _ ↦ h a)).congr_left fun x ↦ ?_
  simp_rw [sub_smul, sum_sub_distrib, sum_psiAP_smul, smul_sum]

/-- A nonprincipal character of coprime modulus contributes only a summatory error in
any reduced progression. The progression estimates are taken at the product modulus. -/
theorem isBigO_sum_residueClass_smul_char {q d : ℕ}
    {R : Type*} [SeminormedCommRing R] [NormedSpace ℝ R] [IsDomain R]
    {a : ZMod q} (ha : IsUnit a) (hqd : q.Coprime d) (χ : DirichletCharacter R d) (hχ : χ ≠ 1)
    {g : ℝ → ℝ} (hψ : ∀ b : ZMod (q * d), IsUnit b →
      (fun x ↦ psiAP (q * d) b x - x / (q * d).totient) =O[atTop] g) :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt.residueClass a n • χ (n : ZMod d)) =O[atTop] g := by
  have hq : NeZero q := ⟨fun hq ↦ hχ <| DirichletCharacter.level_one' χ (by simpa [hq] using hqd)⟩
  by_cases hd : d = 0
  · subst d
    -- At modulus zero, all positive indices other than one are nonunits.
    refine (isBigO_zero (E' := R) g atTop).congr_left fun x ↦ (sum_eq_zero fun n _ ↦ ?_).symm
    by_cases hn : n = 1
    · simp [hn, vonMangoldt.residueClass, Set.indicator_apply]
    · rw [MulChar.map_nonunit χ (by simpa [ZMod.isUnit_iff_coprime] using hn), smul_zero]
  let : NeZero d := ⟨hd⟩
  let e := ZMod.chineseRemainder hqd
  let w (b : ZMod (q * d)) : R := if (e b).1 = a then χ (e b).2 else 0
  have hw (b) (hb : ¬ IsUnit b) : w b = 0 := by
    by_cases hba : (e b).1 = a
    · have h₂ : ¬ IsUnit (e b).2 := fun hu ↦ hb <| (MulEquiv.isUnit_map e.toMulEquiv).mp <|
        Prod.isUnit_iff.mpr ⟨hba ▸ ha, hu⟩
      simp [w, hba, MulChar.map_nonunit _ h₂]
    · simp [w, hba]
  have hs : ∑ b, w b = 0 := by
    rw [← e.symm.toEquiv.sum_comp w, Fintype.sum_prod_type]
    simp only [w, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, RingEquiv.apply_symm_apply]
    exact sum_eq_zero fun b _ ↦ by
      by_cases hb : b = a <;> simp [hb, χ.sum_eq_zero_of_ne_one hχ]
  refine (isBigO_sum_vonMangoldt_smul_sub w hw hψ).congr_left fun x ↦ ?_
  rw [hs, smul_zero, sub_zero]
  refine sum_congr rfl fun n _ ↦ ?_
  have hn : e (n : ZMod (q * d)) = ((n : ZMod q), (n : ZMod d)) := map_natCast e n
  simp [w, hn, vonMangoldt.residueClass, Set.indicator_apply, smul_ite]

/-- If the progression estimates hold at `q` and `q * d`, multiplying the progression
weight by `1 - χ(n)` preserves its main term when `χ` is nonprincipal modulo `d` and
`q` and `d` are coprime. -/
theorem isBigO_sum_residueClass_smul_one_sub_char {q d : ℕ}
    {R : Type*} [SeminormedCommRing R] [NormedSpace ℝ R] [IsDomain R]
    {a : ZMod q} (ha : IsUnit a) (hqd : q.Coprime d) (χ : DirichletCharacter R d) (hχ : χ ≠ 1)
    {g : ℝ → ℝ} (haψ : (fun x ↦ psiAP q a x - x / q.totient) =O[atTop] g)
    (hψ : ∀ b : ZMod (q * d), IsUnit b →
      (fun x ↦ psiAP (q * d) b x - x / (q * d).totient) =O[atTop] g) :
    (fun x ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt.residueClass a n • (1 - χ (n : ZMod d))) -
      (x / q.totient : ℝ) • (1 : R)) =O[atTop] g := by
  have h₁ : (fun x ↦ (psiAP q a x - x / q.totient) • (1 : R)) =O[atTop] g := by
    exact (haψ.smul (isBigO_const_const (1 : R) one_ne_zero atTop)).congr_right
      (fun x ↦ mul_one (g x))
  refine (h₁.sub (isBigO_sum_residueClass_smul_char ha hqd χ hχ hψ)).congr_left fun x ↦ ?_
  simp only [smul_sub, sum_sub_distrib, ← sum_smul, ← psiAP_eq_sum_residueClass,
    sub_smul, sub_right_comm]

end Chebyshev
