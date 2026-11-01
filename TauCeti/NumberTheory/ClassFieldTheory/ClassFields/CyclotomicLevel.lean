/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.NumberTheory.Cyclotomic.OddLevel
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The least cyclotomic field containing an abelian extension of `ℚ`

By the Kronecker–Weber theorem every finite abelian extension `E/ℚ` embeds in some cyclotomic
field `ℚ(ζ_n)`. This file determines exactly which `n` occur, in terms of the conductor
`abelianConductor ℚ E`. The norm group of `ℚ(ζ_n)` is the ray subgroup of `(n)·∞`, and norm groups
detect embeddings of abelian extensions, so `E` embeds in `ℚ(ζ_n)` exactly when `(n)·∞` is
admissible for `E/ℚ`, that is, when the conductor divides `(n)·∞`
(`nonempty_algHom_iff_abelianConductor_dvd_ratModulus`). The real place imposes no condition, so
this happens exactly when the absolute norm `f` of the finite part of the conductor divides `n`
(`nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd`). In particular `f` is the least
cyclotomic level of `E` (`isLeast_absNorm_abelianConductor_finitePart`).

The level `f` is never `2` modulo `4` (`absNorm_abelianConductor_finitePart_mod_four_ne_two`):
for odd `m` the fields `ℚ(ζ_{2m})` and `ℚ(ζ_m)` coincide, so a level `2m` can always be halved.

For the cyclotomic field `F = ℚ(ζ_n)` itself, comparing degrees `φ(f) ≥ φ(n)` with `f ∣ n` shows
that `f = n` when `n` is not `2` modulo `4`; the real place lies in the conductor as soon as
`n > 2`, because `F` then contains a root of unity of prime-power order greater than `2`. Hence the
conductor of `ℚ(ζ_n)/ℚ` is `(n)·∞` for `n > 2` with `n ≢ 2 mod 4`
(`abelianConductor_eq_ratModulus`), and `(n / 2)·∞` for `n > 2` with `n ≡ 2 mod 4`
(`abelianConductor_eq_ratModulus_of_mod_four_eq_two`).

## Main results

* `TauCeti.ClassFieldTheory.nonempty_algHom_iff_abelianConductor_dvd_ratModulus`: a finite abelian
  extension `E/ℚ` embeds in `ℚ(ζ_n)` exactly when its conductor divides `(n)·∞`.
* `TauCeti.ClassFieldTheory.nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd`: it embeds
  in `ℚ(ζ_n)` exactly when the absolute norm of the finite part of its conductor divides `n`.
* `TauCeti.ClassFieldTheory.isLeast_absNorm_abelianConductor_finitePart`: that absolute norm is the
  least cyclotomic level of `E`.
* `TauCeti.ClassFieldTheory.absNorm_abelianConductor_finitePart_mod_four_ne_two`: the least
  cyclotomic level is not `2` modulo `4`.
* `TauCeti.ClassFieldTheory.abelianConductor_eq_ratModulus` and
  `TauCeti.ClassFieldTheory.abelianConductor_eq_ratModulus_of_mod_four_eq_two`: the conductor of
  `ℚ(ζ_n)/ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 (the conductor of an abelian extension)
  and Chapter VI, Corollary 7.8.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 3 (the conductor of an abelian
  number field as its least cyclotomic level).
-/

public section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields Polynomial

/-! ### The cyclotomic fields containing an abelian extension -/

section Level

variable (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E]
  (n : ℕ) [NeZero n] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- **A finite abelian extension `E/ℚ` embeds in `ℚ(ζ_n)` exactly when its conductor divides
`(n)·∞`.** -/
theorem nonempty_algHom_iff_abelianConductor_dvd_ratModulus :
    Nonempty (E →ₐ[ℚ] F) ↔ abelianConductor ℚ E ∣ ratModulus n (NeZero.ne n) := by
  have := IsCyclotomicExtension.isGalois {n} ℚ F
  rw [← range_ideleClassNormMap_le_iff_nonempty_algHom,
    range_ideleClassNormMap_eq_raySubgroup_ratModulus n F, ← isAdmissibleModulus_iff,
    isAdmissibleModulus_iff_abelianConductor_dvd]

/-- **A finite abelian extension `E/ℚ` embeds in `ℚ(ζ_n)` exactly when the absolute norm of the
finite part of its conductor divides `n`.** -/
theorem nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd :
    Nonempty (E →ₐ[ℚ] F) ↔ Ideal.absNorm (abelianConductor ℚ E).finitePart ∣ n := by
  rw [nonempty_algHom_iff_abelianConductor_dvd_ratModulus E n F, dvd_ratModulus_iff]

end Level

section LeastLevel

variable (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E]

/-- **The least cyclotomic level of a finite abelian extension `E/ℚ`** is the absolute norm of the
finite part of its conductor: it is the least `n ≠ 0` such that `E` embeds in `ℚ(ζ_n)`. -/
theorem isLeast_absNorm_abelianConductor_finitePart :
    IsLeast {n : ℕ | n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)}
      (Ideal.absNorm (abelianConductor ℚ E).finitePart) := by
  -- Instance search finds `Algebra ℚ (CyclotomicField n ℚ)` through the `ℚ`-algebra structure of
  -- a characteristic-zero field, so the cyclotomic instances are supplied explicitly.
  have hf := Ideal.absNorm_eq_zero_iff.not.mpr (abelianConductor ℚ E).finitePart_ne_bot
  refine ⟨⟨hf, ?_⟩, fun n ⟨hn, hE⟩ ↦ ?_⟩
  · have : NeZero (Ideal.absNorm (abelianConductor ℚ E).finitePart) := ⟨hf⟩
    have : IsCyclotomicExtension {Ideal.absNorm (abelianConductor ℚ E).finitePart} ℚ
        (CyclotomicField (Ideal.absNorm (abelianConductor ℚ E).finitePart) ℚ) :=
      CyclotomicField.isCyclotomicExtension _ ℚ
    exact (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd E _ _).mpr dvd_rfl
  · have : NeZero n := ⟨hn⟩
    have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
      CyclotomicField.isCyclotomicExtension n ℚ
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      ((nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd E n _).mp hE)

/-- **The least cyclotomic level of a finite abelian extension of `ℚ` is not `2` modulo `4`**: for
odd `m` the cyclotomic field `ℚ(ζ_{2m})` is also `ℚ(ζ_m)`. -/
theorem absNorm_abelianConductor_finitePart_mod_four_ne_two :
    Ideal.absNorm (abelianConductor ℚ E).finitePart % 4 ≠ 2 := by
  generalize hf : Ideal.absNorm (abelianConductor ℚ E).finitePart = f
  intro h4
  have : NeZero f := ⟨by omega⟩
  have : NeZero (f / 2) := ⟨by omega⟩
  have : IsCyclotomicExtension {f} ℚ (CyclotomicField f ℚ) :=
    CyclotomicField.isCyclotomicExtension f ℚ
  -- `ℚ(ζ_f)` contains `E`, and it is also the cyclotomic field of level `f / 2`.
  have hE := (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd E f
    (CyclotomicField f ℚ)).mpr hf.dvd
  have : IsCyclotomicExtension {f / 2} ℚ (CyclotomicField f ℚ) :=
    IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two h4
  have hdvd := (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd E (f / 2)
    (CyclotomicField f ℚ)).mp hE
  rw [hf] at hdvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

end LeastLevel

/-! ### The conductor of `ℚ(ζ_n)/ℚ` -/

section Cyclotomic

variable (n : ℕ) [NeZero n] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- For `n` not `2` modulo `4`, the finite part of the conductor of `ℚ(ζ_n)/ℚ` has absolute norm
`n`: it divides `n`, and `ℚ(ζ_n)` embeds in the cyclotomic field of that level, whose degree is
then at least `φ(n)`. -/
private theorem absNorm_abelianConductor_finitePart_eq (h4 : n % 4 ≠ 2) :
    Ideal.absNorm (abelianConductor ℚ F).finitePart = n := by
  have := IsCyclotomicExtension.isAbelianGalois {n} ℚ F
  generalize hf : Ideal.absNorm (abelianConductor ℚ F).finitePart = f
  have : NeZero f :=
    ⟨hf ▸ Ideal.absNorm_eq_zero_iff.not.mpr (abelianConductor ℚ F).finitePart_ne_bot⟩
  have : IsCyclotomicExtension {f} ℚ (CyclotomicField f ℚ) :=
    CyclotomicField.isCyclotomicExtension f ℚ
  have hfn : f ∣ n := hf ▸
    (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd F n F).mp ⟨AlgHom.id ℚ F⟩
  obtain ⟨g⟩ := (nonempty_algHom_iff_absNorm_abelianConductor_finitePart_dvd F f
    (CyclotomicField f ℚ)).mpr hf.dvd
  have hle : n.totient ≤ f.totient := by
    rw [← IsCyclotomicExtension.finrank F (cyclotomic.irreducible_rat (NeZero.pos n)),
      ← IsCyclotomicExtension.finrank (CyclotomicField f ℚ)
        (cyclotomic.irreducible_rat (NeZero.pos f))]
    exact g.toLinearMap.finrank_le_finrank_of_injective g.injective
  have hφ : f.totient = n.totient :=
    le_antisymm (Nat.le_of_dvd (Nat.totient_pos.mpr (NeZero.pos n)) (Nat.totient_dvd_of_dvd hfn))
      hle
  -- `φ(f) = φ(n)` with `f ∣ n` forces `f = n` or `n = 2f`. In the second case `f` is even by
  -- `h4`, and then `φ(2f) = 2φ(f)` forces `f = n` after all.
  rcases Nat.eq_or_eq_of_totient_eq_totient hfn hφ with h | h
  · exact h
  · exact Even.eq_of_totient_eq_totient hfn (Nat.even_iff.mpr (by omega)) hφ

/-- **The conductor of `ℚ(ζ_n)/ℚ` is `(n)·∞`** for `n > 2` not equal to `2` modulo `4`. -/
theorem abelianConductor_eq_ratModulus (h2 : 2 < n) (h4 : n % 4 ≠ 2) :
    abelianConductor ℚ F = ratModulus n (NeZero.ne n) := by
  refine Modulus.ext ?_ ?_
  · rw [← Rat.RingOfIntegers.ideal_span_absNorm_eq_self (abelianConductor ℚ F).finitePart,
      absNorm_abelianConductor_finitePart_eq n F h4, ratModulus_finitePart]
  -- The real place lies in the conductor: `F` contains a primitive `p ^ k`-th root of unity with
  -- `p ^ k > 2`, namely of order `4` if `4 ∣ n`, and of odd prime order otherwise.
  obtain ⟨p, k, hp, hpk, hdvd⟩ : ∃ p k : ℕ, p.Prime ∧ 2 < p ^ k ∧ p ^ k ∣ n := by
    by_cases h : 4 ∣ n
    · exact ⟨2, 2, Nat.prime_two, by norm_num, h⟩
    · refine ⟨n.minFac, 1, Nat.minFac_prime (by omega), ?_, by simpa using Nat.minFac_dvd n⟩
      have h2n : n.minFac ≠ 2 := fun h2 ↦ by
        have := h2 ▸ Nat.minFac_dvd n
        omega
      have := (Nat.minFac_prime (show n ≠ 1 by omega)).two_le
      rw [pow_one]
      omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hdvd
  have hζ := (IsCyclotomicExtension.zeta_spec n ℚ F).pow (NeZero.pos n) (hm.trans (mul_comm _ _))
  rw [ratModulus_infinitePart]
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_abelianConductor_infinitePart p _ hζ hpk,
    fun w _ ↦ Subtype.ext (Subsingleton.elim (α := InfinitePlace ℚ) _ _)⟩

omit [NeZero n] in
/-- **The conductor of `ℚ(ζ_n)/ℚ` is `(n / 2)·∞`** for `n > 2` equal to `2` modulo `4`, as
`ℚ(ζ_n) = ℚ(ζ_{n / 2})`. -/
theorem abelianConductor_eq_ratModulus_of_mod_four_eq_two (h2 : 2 < n) (h4 : n % 4 = 2) :
    abelianConductor ℚ F = ratModulus (n / 2) (by omega) := by
  have : NeZero (n / 2) := ⟨by omega⟩
  have : IsCyclotomicExtension {n / 2} ℚ F :=
    IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two h4
  exact abelianConductor_eq_ratModulus (n / 2) F (by omega) (by omega)

end Cyclotomic

end TauCeti.ClassFieldTheory
