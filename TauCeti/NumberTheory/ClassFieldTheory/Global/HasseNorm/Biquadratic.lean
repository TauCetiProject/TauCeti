/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.ExponentNorms
public import TauCeti.RingTheory.Norm.Units
import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Padic
import TauCeti.NumberTheory.Multiquadratic.CoprimeSquarefree
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula
import TauCeti.RingTheory.Norm.Quadratic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

/-!
# The Hasse norm principle fails for `ℚ(√13, √17)`

The cyclic Hasse norm theorem `TauCeti.ClassFieldTheory.isGlobalNorm_iff_isLocalNormEverywhere`
says that for a cyclic extension a local norm everywhere is a global norm. This file records the
standard counterexample showing that the cyclic hypothesis cannot be dropped: for the biquadratic
field `L = ℚ(√13, √17)`, whose Galois group is `(ℤ/2)²`, the number `25` is a local norm everywhere
(`isLocalNormEverywhere_twentyFive`) but not a norm from `L` (`twentyFive_notMem_normGroup`).

The local half holds because `Gal(L/ℚ)` has exponent two, so every square of `ℚˣ`, and in
particular `25 = 5²`, is a local norm everywhere by
`TauCeti.ClassFieldTheory.isLocalNormEverywhere_pow_of_exponent_dvd`.

The global half is proved by Hilbert reciprocity over `ℚ`. Let `F = ℚ(√13)` and suppose that
`25 = N_{L/ℚ}(x)`. Then `y = N_{L/F}(x)` has norm `25` from `F`, so Hilbert's Theorem 90 for `F/ℚ`,
made explicit, writes `y m = 5 z²` with `z ∈ F` and `m = c² - 13 d²` a nonzero norm from `F`.
Hence `q = 5 m` is a norm from `L = F(√17)` down to `F`, say `q = α² - 17 β²` with `α, β ∈ F`.
At every place `ℓ` where `13` is a square, an embedding of `F` into `ℚ_ℓ` turns this into a
solution of `q = x² - 17 y²`, so the Hilbert symbol `(17, q)_ℓ` is `1`. At the remaining places
the symbol is computed from Legendre symbols: there `(13, m)_ℓ = 1` forces `(17, m)_ℓ = 1`, so
`(17, q)_ℓ = (17, 5)_ℓ`, which is `1` except at `ℓ = 5`, where it is `(17 / 5) = -1`. So the
product of the symbols `(17, q)_v` over all places is `-1`, contradicting Hilbert's product
formula `TauCeti.finprod_hilbertSymbol_padic_mul_hilbertSymbol_real_eq_one`.

The field is described by square roots `s` of `13` and `t` of `17` that generate it; no
particular model of `ℚ(√13, √17)` is chosen.

## Main results

* `TauCeti.ClassFieldTheory.isLocalNormEverywhere_twentyFive`: `25` is a norm at every place of
  `ℚ` from the local étale algebras of `ℚ(√13, √17)`.
* `TauCeti.ClassFieldTheory.twentyFive_notMem_normGroup`: `25` is not a norm from `ℚ(√13, √17)`.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Exercise 5.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §2 (Hilbert's product formula).
-/

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

/-! ### The local computation behind the global half -/

section Symbols

variable {a₁ a₂ b₁ b₂ c d : ℚ}

/-- The rational coordinates of a solution of `q = α² - 17 β²` over `ℚ(√13)`, read in a field in
which `13` has a square root `r`, give a solution of `q = x² - 17 y²` there. -/
private theorem exists_eq_sq_sub_seventeen_mul_sq {E : Type*} [Field E] [Algebra ℚ E] {r : E}
    (hr : r ^ 2 = 13) (h₁ : a₁ * a₂ = 17 * (b₁ * b₂))
    (h₂ : 5 * (c ^ 2 - 13 * d ^ 2) = a₁ ^ 2 + 13 * a₂ ^ 2 - 17 * b₁ ^ 2 - 221 * b₂ ^ 2) :
    ∃ x y : E, algebraMap ℚ E (5 * (c ^ 2 - 13 * d ^ 2)) = x ^ 2 - 17 * y ^ 2 := by
  refine ⟨algebraMap ℚ E a₁ + algebraMap ℚ E a₂ * r, algebraMap ℚ E b₁ + algebraMap ℚ E b₂ * r, ?_⟩
  have h₁' := congrArg (algebraMap ℚ E) h₁
  have h₂' := congrArg (algebraMap ℚ E) h₂
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat] at h₁' h₂' ⊢
  linear_combination h₂' - (algebraMap ℚ E a₂ ^ 2 - 17 * algebraMap ℚ E b₂ ^ 2) * hr - 2 * r * h₁'

/-- A prime `p` different from the prime `ℓ` is not divisible by `ℓ` in `ℤ`. -/
private theorem not_natCast_dvd_of_ne {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (h : ℓ ≠ p) :
    ¬ (ℓ : ℤ) ∣ p := fun hdvd ↦ h ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (by exact_mod_cast hdvd))

/-- At an odd prime `ℓ` at which `13` is not a square, the symbol `(17, m)_ℓ` is trivial as soon as
`(13, m)_ℓ` is: either `17` or `13 · 17` is then a square in `ℚ_ℓ`. -/
private theorem hilbertSymbol_seventeen_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (h13 : legendreSym ℓ 13 = -1) (h17 : ¬ (ℓ : ℤ) ∣ 17) {m : ℚ_[ℓ]ˣ}
    (hm : hilbertSymbol (Units.mk0 (13 : ℚ_[ℓ]) (by norm_num)) m = 1) :
    hilbertSymbol (Units.mk0 (17 : ℚ_[ℓ]) (by norm_num)) m = 1 := by
  have hsq {n : ℤ} {u : ℚ_[ℓ]ˣ} (hn : ¬ (ℓ : ℤ) ∣ n) (h : legendreSym ℓ n = 1)
      (hu : (u : ℚ_[ℓ]) = n) : hilbertSymbol u m = 1 :=
    hilbertSymbol_eq_one_of_isSquare_left (Units.isSquare_coe_iff.mp
      (hu ▸ (Padic.isSquare_intCast_iff_legendreSym_eq_one hℓ hn).2 h)) m
  rcases legendreSym.eq_one_or_neg_one ℓ (a := 17)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd 17 ℓ).not.2 h17) with h | h
  · exact hsq h17 h (by simp)
  · -- Here `13 · 17` is a square modulo `ℓ`, and the symbol is multiplicative in its first entry.
    have h13' : ¬ (ℓ : ℤ) ∣ 13 := fun hdvd ↦ by
      rw [(legendreSym.eq_zero_iff ℓ 13).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd 13 ℓ).2 hdvd)] at h13
      norm_num at h13
    have h221 : hilbertSymbol (Units.mk0 (13 : ℚ_[ℓ]) (by norm_num) *
        Units.mk0 (17 : ℚ_[ℓ]) (by norm_num)) m = 1 :=
      hsq (n := 13 * 17)
        (fun hdvd ↦ ((Nat.prime_iff_prime_int.mp Fact.out).dvd_mul.mp hdvd).elim h13' h17)
        (by rw [legendreSym.mul, h13, h]; norm_num) (by norm_num)
    rwa [hilbertSymbol_mul_left two_ne_zero, hm, one_mul] at h221

/-- At an odd prime `ℓ` at which `13` is not a square, the symbol `(17, q)_ℓ` with
`q = 5 (c² - 13 d²)` is `(17, 5)_ℓ`, which is `-1` at `ℓ = 5` and `1` otherwise. -/
private theorem hilbertSymbol_seventeen_five_mul {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (h13 : legendreSym ℓ 13 = -1) (hm : c ^ 2 - 13 * d ^ 2 ≠ 0) {q : ℚ_[ℓ]ˣ}
    (hq : (q : ℚ_[ℓ]) = ((5 * (c ^ 2 - 13 * d ^ 2) : ℚ) : ℚ_[ℓ])) :
    hilbertSymbol (Units.mk0 (17 : ℚ_[ℓ]) (by norm_num)) q = if ℓ = 5 then -1 else 1 := by
  have hp : ℓ.Prime := Fact.out
  have h17 : ¬ (ℓ : ℤ) ∣ 17 :=
    not_natCast_dvd_of_ne hp (by norm_num) (by rintro rfl; norm_num at h13)
  have hm' : (((c ^ 2 - 13 * d ^ 2 : ℚ)) : ℚ_[ℓ]) ≠ 0 := Rat.cast_ne_zero.2 hm
  have hsplit : q = Units.mk0 (5 : ℚ_[ℓ]) (by norm_num) * Units.mk0 _ hm' :=
    Units.ext (by simp [hq])
  -- `(13, c² - 13 d²)_ℓ = 1` forces `(17, c² - 13 d²)_ℓ = 1`.
  have h13m : hilbertSymbol (Units.mk0 (13 : ℚ_[ℓ]) (by norm_num)) (Units.mk0 _ hm') = 1 :=
    (hilbertSymbol_eq_one_iff _ _).2 ⟨c, d, by simp only [Units.val_mk0]; push_cast; ring⟩
  rw [hsplit, hilbertSymbol_mul_right two_ne_zero, hilbertSymbol_seventeen_eq_one hℓ h13 h17 h13m,
    mul_one]
  rcases eq_or_ne ℓ 5 with rfl | h5
  · have h := Padic.hilbertSymbol_intCast_self_eq_legendreSym (p := 5) (n := 17) (by norm_num)
      (by norm_num)
    rw [show legendreSym 5 17 = -1 by norm_num] at h
    rw [ite_eq_left_iff.2 fun h ↦ (h rfl).elim]
    apply Units.ext
    rw [Units.val_neg, Units.val_one, ← h]
    simp
  · rw [ite_eq_right h5]
    convert Padic.hilbertSymbol_intCast_intCast_eq_one hℓ h17
      (not_natCast_dvd_of_ne hp (by norm_num) h5) using 2 <;> ext <;> simp

/-- **The local symbols of `17` and `q = 5 (c² - 13 d²)`.** If `q = α² - 17 β²` with `α, β`
in `ℚ(√13)`, written in rational coordinates, then the Hilbert symbol `(17, q)_ℓ` over `ℚ_ℓ` is
`-1` at `ℓ = 5` and `1` at every other prime. -/
private theorem hilbertSymbol_seventeen_padic (ℓ : ℕ) [Fact ℓ.Prime] (hm : c ^ 2 - 13 * d ^ 2 ≠ 0)
    {q : ℚ_[ℓ]ˣ} (hq : (q : ℚ_[ℓ]) = ((5 * (c ^ 2 - 13 * d ^ 2) : ℚ) : ℚ_[ℓ]))
    (h₁ : a₁ * a₂ = 17 * (b₁ * b₂))
    (h₂ : 5 * (c ^ 2 - 13 * d ^ 2) = a₁ ^ 2 + 13 * a₂ ^ 2 - 17 * b₁ ^ 2 - 221 * b₂ ^ 2) :
    hilbertSymbol (Units.mk0 (17 : ℚ_[ℓ]) (by norm_num)) q = if ℓ = 5 then -1 else 1 := by
  have hp : ℓ.Prime := Fact.out
  -- Where `17` is a square in `ℚ_ℓ`, the symbol is trivial.
  have hsq17 (h : IsSquare (17 : ℚ_[ℓ])) (h5 : ℓ ≠ 5) :
      hilbertSymbol (Units.mk0 (17 : ℚ_[ℓ]) (by norm_num)) q = if ℓ = 5 then -1 else 1 := by
    rw [ite_eq_right h5]
    exact hilbertSymbol_eq_one_of_isSquare_left (Units.isSquare_coe_iff.mp (by simpa using h)) _
  rcases eq_or_ne ℓ 2 with rfl | h2
  · -- `17` is a square in `ℚ_2`, being `1` modulo `8`.
    have hu : IsUnit (17 : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff]
      exact_mod_cast PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)
    have h := (isSquare_coe_iff_mem_unitsPrincipal_three hu.unit).2
      (mem_unitsPrincipal_iff_toZModPow.2 (by rw [IsUnit.unit_spec, map_ofNat]; decide))
    rw [IsUnit.unit_spec] at h
    exact hsq17 (by exact_mod_cast h) (by norm_num)
  rcases eq_or_ne ℓ 13 with rfl | h13
  · -- `17` is a square in `ℚ_13`, being `2²` modulo `13`.
    have h := (Padic.isSquare_intCast_iff_legendreSym_eq_one (p := 13) (n := 17) (by norm_num)
      (by norm_num)).2 (by norm_num)
    exact hsq17 (by exact_mod_cast h) (by norm_num)
  have h13' : ¬ (ℓ : ℤ) ∣ 13 := not_natCast_dvd_of_ne hp (by norm_num) h13
  rcases legendreSym.eq_one_or_neg_one ℓ ((ZMod.intCast_zmod_eq_zero_iff_dvd 13 ℓ).not.2 h13')
    with hχ | hχ
  · -- If `13` is a square in `ℚ_ℓ`, the norm equation over `ℚ(√13)` descends to `ℚ_ℓ`.
    have h5 : ℓ ≠ 5 := by rintro rfl; norm_num at hχ
    obtain ⟨r, hr⟩ := (Padic.isSquare_intCast_iff_legendreSym_eq_one h2 h13').2 hχ
    obtain ⟨x, y, hxy⟩ := exists_eq_sq_sub_seventeen_mul_sq (E := ℚ_[ℓ]) (r := r)
      (by rw [pow_two, ← hr]; norm_num) h₁ h₂
    rw [ite_eq_right h5, hilbertSymbol_eq_one_iff]
    exact ⟨x, y, by simpa [hq] using hxy⟩
  · exact hilbertSymbol_seventeen_five_mul h2 hχ hm hq

/-- **Hilbert reciprocity rules out the norm equation.** There is no solution in rational
coordinates of `5 (c² - 13 d²) = α² - 17 β²` over `ℚ(√13)` with `c² - 13 d² ≠ 0`: the Hilbert
symbols of `17` and `5 (c² - 13 d²)` would have product `-1` over all places of `ℚ`. -/
private theorem false_of_sq_sub_seventeen_mul_sq (hm : c ^ 2 - 13 * d ^ 2 ≠ 0)
    (h₁ : a₁ * a₂ = 17 * (b₁ * b₂))
    (h₂ : 5 * (c ^ 2 - 13 * d ^ 2) = a₁ ^ 2 + 13 * a₂ ^ 2 - 17 * b₁ ^ 2 - 221 * b₂ ^ 2) :
    False := by
  let a : ℚˣ := Units.mk0 17 (by norm_num)
  let q : ℚˣ := Units.mk0 (5 * (c ^ 2 - 13 * d ^ 2)) (mul_ne_zero (by norm_num) hm)
  have hloc (ℓ : Nat.Primes) : hilbertSymbol (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)
      (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom q) = if (ℓ : ℕ) = 5 then -1 else 1 := by
    rw [← hilbertSymbol_seventeen_padic ℓ hm (q := Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom q)
      (by simp [q]) h₁ h₂]
    congr 1
    ext
    simp [a]
  -- At the real place `17` is a square.
  have hreal : hilbertSymbol (Units.map (algebraMap ℚ ℝ).toMonoidHom a)
      (Units.map (algebraMap ℚ ℝ).toMonoidHom q) = 1 :=
    hilbertSymbol_eq_one_of_isSquare_left (Units.isSquare_coe_iff.mp
      ⟨√17, by simp [a, Real.mul_self_sqrt]⟩) _
  have h := finprod_hilbertSymbol_padic_mul_hilbertSymbol_real_eq_one a q
  rw [hreal, mul_one, finprod_congr hloc,
    finprod_eq_single (fun ℓ : Nat.Primes ↦ if (ℓ : ℕ) = 5 then (-1 : ℤˣ) else 1)
      ⟨5, Nat.prime_five⟩ fun ℓ hℓ ↦ ite_eq_right fun h ↦ hℓ (Subtype.ext h)] at h
  simp at h

end Symbols

/-! ### Computations in `ℚ(√13)` -/

section Quadratic

variable {F : Type*} [Field F] [Algebra ℚ F] {σ : F}

/-- **Theorem 90 for `ℚ(√13)`, made explicit.** If `y = u + v √13` has norm `u² - 13 v² = 25`,
then `y (c² - 13 d²) = 5 z²` for some `z` and some rational `c, d` with `c² - 13 d² ≠ 0`. -/
private theorem exists_mul_eq_five_mul_sq (hσ2 : σ ^ 2 = 13) {u v : ℚ}
    (huv : u ^ 2 - v ^ 2 * 13 = 25) :
    ∃ (z : F) (c d : ℚ), c ^ 2 - 13 * d ^ 2 ≠ 0 ∧
      (algebraMap ℚ F u + algebraMap ℚ F v * σ) * algebraMap ℚ F (c ^ 2 - 13 * d ^ 2) =
        5 * z ^ 2 := by
  rcases eq_or_ne u (-5) with rfl | hu
  · -- Then `y = -5`, and `z = √13` works with `c² - 13 d² = -13`.
    have hv : v = 0 := by nlinarith
    refine ⟨σ, 0, 1, by norm_num, ?_⟩
    rw [hv, map_zero, zero_mul, add_zero, show (0 : ℚ) ^ 2 - 13 * 1 ^ 2 = -13 by norm_num, hσ2]
    simp only [map_neg, map_ofNat]
    ring
  · -- Otherwise `z = (u + 5) + v √13` has `z² = 2 (u + 5) y` and norm `10 (u + 5)`.
    refine ⟨algebraMap ℚ F (u + 5) + algebraMap ℚ F v * σ, u + 5, v,
      fun h0 ↦ hu (by nlinarith), ?_⟩
    have huv' := congrArg (algebraMap ℚ F) huv
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at huv' ⊢
    linear_combination (5 + algebraMap ℚ F u + algebraMap ℚ F v * σ) * huv' -
      5 * algebraMap ℚ F v ^ 2 * hσ2

/-- **Comparing coefficients in the basis `1, √13`.** If a rational number `q` equals
`α² - 17 β²` with `α = a₁ + a₂ √13` and `β = b₁ + b₂ √13`, then the coefficient of `√13`
vanishes and `q` is the rational part. -/
private theorem eq_of_algebraMap_eq_sq_sub_seventeen_mul_sq
    (hσ : σ ∉ Set.range (algebraMap ℚ F)) (hσ2 : σ ^ 2 = 13) {q a₁ a₂ b₁ b₂ : ℚ}
    (h : algebraMap ℚ F q = (algebraMap ℚ F a₁ + algebraMap ℚ F a₂ * σ) ^ 2 -
      17 * (algebraMap ℚ F b₁ + algebraMap ℚ F b₂ * σ) ^ 2) :
    a₁ * a₂ = 17 * (b₁ * b₂) ∧ q = a₁ ^ 2 + 13 * a₂ ^ 2 - 17 * b₁ ^ 2 - 221 * b₂ ^ 2 := by
  have key : algebraMap ℚ F (q - (a₁ ^ 2 + 13 * a₂ ^ 2 - 17 * b₁ ^ 2 - 221 * b₂ ^ 2)) =
      algebraMap ℚ F (2 * (a₁ * a₂ - 17 * (b₁ * b₂))) * σ := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h ⊢
    linear_combination h + (algebraMap ℚ F a₂ ^ 2 - 17 * algebraMap ℚ F b₂ ^ 2) * hσ2
  have hcoef : 2 * (a₁ * a₂ - 17 * (b₁ * b₂)) = 0 := by
    by_contra h0
    refine hσ ⟨(q - (a₁ ^ 2 + 13 * a₂ ^ 2 - 17 * b₁ ^ 2 - 221 * b₂ ^ 2)) /
      (2 * (a₁ * a₂ - 17 * (b₁ * b₂))), ?_⟩
    rw [map_div₀, key, mul_div_cancel_left₀ _ ((map_ne_zero _).2 h0)]
  rw [hcoef, map_zero, zero_mul, map_eq_zero_iff _ (algebraMap ℚ F).injective] at key
  constructor <;> linarith

end Quadratic

/-! ### The counterexample -/

variable {L : Type*} [Field L] [NumberField L] {s t : L}

/-- The generators `s` and `t`, as a family indexed by `Fin 2`, are square roots of `13`
and `17`. -/
private theorem sq_vecCons (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) :
    ∀ i, (![s, t] : Fin 2 → L) i ^ 2 = algebraMap ℚ L ((![13, 17] : Fin 2 → ℤ) i) := by
  intro i
  fin_cases i <;> simp [hs, ht]

private theorem adjoin_range_vecCons (hst : ℚ⟮s, t⟯ = ⊤) :
    IntermediateField.adjoin ℚ (Set.range (![s, t] : Fin 2 → L)) = ⊤ := by
  rw [← hst]
  congr 1
  ext x
  simp [eq_comm, or_comm]

/-- `ℚ(√13)` has degree two over `ℚ`. -/
private theorem finrank_adjoin_simple_eq_two (hs : s ^ 2 = 13) : Module.finrank ℚ ℚ⟮s⟯ = 2 := by
  have h := Multiquadratic.finrank_adjoin_range_of_coprime_squarefree (L := L) ![13] ![s]
    (fun i ↦ by fin_cases i; simp [hs]) (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim)
    (fun i ↦ by fin_cases i; exact (Int.prime_iff_natAbs_prime.2 (by norm_num)).squarefree)
    (fun i ↦ by fin_cases i; simp [Int.isUnit_iff])
  rw [show Set.range ![s] = {s} by simp] at h
  simpa using h

/-- `ℚ(√13, √17)` has degree four over `ℚ`. -/
private theorem finrank_eq_four (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) (hst : ℚ⟮s, t⟯ = ⊤) :
    Module.finrank ℚ L = 4 := by
  have hcop : Pairwise (Function.onFun IsCoprime (![13, 17] : Fin 2 → ℤ)) := by
    have h : IsCoprime (13 : ℤ) 17 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Function.onFun, h.symm]
  have h := Multiquadratic.finrank_adjoin_range_of_coprime_squarefree (L := L) ![13, 17] ![s, t]
    (sq_vecCons hs ht) hcop
    (fun i ↦ by fin_cases i <;> exact (Int.prime_iff_natAbs_prime.2 (by norm_num)).squarefree)
    (fun i ↦ by fin_cases i <;> simp [Int.isUnit_iff])
  rw [adjoin_range_vecCons hst] at h
  simpa using h

/-- `ℚ(√13, √17)` has degree two over `ℚ(√13)`. -/
private theorem finrank_adjoin_simple_left_eq_two (hs : s ^ 2 = 13) (ht : t ^ 2 = 17)
    (hst : ℚ⟮s, t⟯ = ⊤) : Module.finrank ℚ⟮s⟯ L = 2 := by
  have h := Module.finrank_mul_finrank ℚ ℚ⟮s⟯ L
  rw [finrank_adjoin_simple_eq_two hs, finrank_eq_four hs ht hst] at h
  omega

/-- `√13` is not rational. -/
private theorem gen_notMem_range_algebraMap (hs : s ^ 2 = 13) :
    AdjoinSimple.gen ℚ s ∉ Set.range (algebraMap ℚ ℚ⟮s⟯) := by
  rintro ⟨a, ha⟩
  have hF := finrank_adjoin_simple_eq_two hs
  rw [adjoin_simple_eq_bot_iff.2 ⟨a, by simpa using congrArg Subtype.val ha⟩,
    IntermediateField.finrank_bot] at hF
  omega

/-- `√17` does not lie in `ℚ(√13)`. -/
private theorem notMem_range_algebraMap_adjoin_simple (hs : s ^ 2 = 13) (ht : t ^ 2 = 17)
    (hst : ℚ⟮s, t⟯ = ⊤) : t ∉ Set.range (algebraMap ℚ⟮s⟯ L) := by
  rintro ⟨f, hf⟩
  have htop : ℚ⟮s⟯ = ⊤ := by
    rw [eq_top_iff, ← hst, adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_adjoin_simple_self ℚ s, hf ▸ f.2⟩
  have hF := finrank_adjoin_simple_eq_two hs
  rw [htop, IntermediateField.finrank_top', finrank_eq_four hs ht hst] at hF
  omega

/-- **`25` is a local norm everywhere from `ℚ(√13, √17)`.** If `L` is generated over `ℚ` by
square roots `s` of `13` and `t` of `17`, then `25` is a norm from the local étale algebra
`ℚ_v ⊗[ℚ] L` at every finite and infinite place `v` of `ℚ`. -/
theorem isLocalNormEverywhere_twentyFive (hs : s ^ 2 = 13) (ht : t ^ 2 = 17)
    (hst : ℚ⟮s, t⟯ = ⊤) :
    GlobalNumberFields.IsLocalNormEverywhere ℚ L (Units.mk0 (25 : ℚ) (by norm_num)) := by
  have : IsGalois ℚ L := Multiquadratic.isGalois_of_adjoin_eq_top
    (d := fun i ↦ ((![13, 17] : Fin 2 → ℤ) i : ℚ)) (sq_vecCons hs ht) (adjoin_range_vecCons hst)
  have hexp : Monoid.exponent Gal(L/ℚ) ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one
    (Multiquadratic.aut_pow_two_eq_one_of_adjoin_eq_top
      (d := fun i ↦ ((![13, 17] : Fin 2 → ℤ) i : ℚ)) (sq_vecCons hs ht) (adjoin_range_vecCons hst))
  convert isLocalNormEverywhere_pow_of_exponent_dvd ℚ L hexp (Units.mk0 (5 : ℚ) (by norm_num))
  ext
  norm_num

/-- **`25` is not a norm from `ℚ(√13, √17)`.** If `L` is generated over `ℚ` by square roots `s`
of `13` and `t` of `17`, then `25` is not the norm of an element of `L`. Together with
`isLocalNormEverywhere_twentyFive` this shows that the Hasse norm principle fails for the
biquadratic extension `L/ℚ`. -/
theorem twentyFive_notMem_normGroup (hs : s ^ 2 = 13) (ht : t ^ 2 = 17) (hst : ℚ⟮s, t⟯ = ⊤) :
    Units.mk0 (25 : ℚ) (by norm_num) ∉ normGroup ℚ L := by
  intro h25
  obtain ⟨x, hx⟩ := mem_normGroup_iff.1 h25
  -- The tower `ℚ ⊆ F = ℚ(√13) ⊆ L` consists of two quadratic steps, generated by `√13` and `√17`.
  have hFL := finrank_adjoin_simple_left_eq_two hs ht hst
  have : Algebra.IsQuadraticExtension ℚ ℚ⟮s⟯ := ⟨finrank_adjoin_simple_eq_two hs⟩
  have : Algebra.IsQuadraticExtension ℚ⟮s⟯ L := ⟨hFL⟩
  have hσ2 : AdjoinSimple.gen ℚ s ^ 2 = 13 := Subtype.ext (by simp [hs]; norm_cast)
  have hσ := gen_notMem_range_algebraMap hs
  have ht' := notMem_range_algebraMap_adjoin_simple hs ht hst
  -- `y = N_{L/F}(x) = u + v √13` has norm `u² - 13 v² = 25`, so `y (c² - 13 d²) = 5 z²`.
  obtain ⟨v, u, hy⟩ := Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul
    (K := ℚ) (L := ℚ⟮s⟯) hσ (Algebra.norm ℚ⟮s⟯ (x : L))
  have huv : u ^ 2 - v ^ 2 * 13 = 25 := by
    have h : Algebra.norm ℚ (Algebra.norm ℚ⟮s⟯ (x : L)) = Algebra.norm ℚ (x : L) :=
      Algebra.norm_norm
    rwa [hy, Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul_of_sq_eq (d := 13) hσ
      (by rw [hσ2, map_ofNat]), hx, Units.val_mk0] at h
  obtain ⟨z, c, d, hm, hyz⟩ := exists_mul_eq_five_mul_sq hσ2 huv
  rw [← hy] at hyz
  -- Hence `q = 5 (c² - 13 d²) = N_{L/F}(5 z / x)`, so `q = α² - 17 β²` with `α, β ∈ F`.
  have hy0 : Algebra.norm ℚ⟮s⟯ (x : L) ≠ 0 := Algebra.norm_ne_zero_iff.2 x.ne_zero
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero, mul_eq_zero,
      map_eq_zero_iff _ (algebraMap ℚ ℚ⟮s⟯).injective] at hyz
    exact hyz.elim hy0 hm
  have hq0 : algebraMap ℚ ℚ⟮s⟯ (5 * (c ^ 2 - 13 * d ^ 2)) ≠ 0 :=
    (map_ne_zero _).2 (mul_ne_zero (by norm_num) hm)
  have hq : Units.mk0 _ hq0 ∈ normGroup ℚ⟮s⟯ L := by
    have h5z : algebraMap ℚ⟮s⟯ L (5 * z) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero (by norm_num) hz0)
    refine mem_normGroup_iff.2 ⟨Units.mk0 _ h5z * x⁻¹, mul_right_cancel₀ hy0 ?_⟩
    rw [← map_mul]
    simp only [Units.val_mul, Units.val_mk0, mul_assoc, Units.inv_mul, mul_one,
      Algebra.norm_algebraMap, hFL]
    simp only [map_mul, map_ofNat] at hyz ⊢
    linear_combination -5 * hyz
  obtain ⟨α, β, hαβ⟩ := (mem_normGroup_iff_exists_sq_sub_mul_sq L ht' (a := 17)
    (by rw [ht, map_ofNat]) _).1 hq
  -- In rational coordinates this is excluded by Hilbert reciprocity.
  obtain ⟨a₂, a₁, rfl⟩ := Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul
    (K := ℚ) (L := ℚ⟮s⟯) hσ α
  obtain ⟨b₂, b₁, rfl⟩ := Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul
    (K := ℚ) (L := ℚ⟮s⟯) hσ β
  obtain ⟨h₁, h₂⟩ := eq_of_algebraMap_eq_sq_sub_seventeen_mul_sq hσ hσ2 hαβ
  exact false_of_sq_sub_seventeen_mul_sq hm h₁ h₂

end TauCeti.ClassFieldTheory
