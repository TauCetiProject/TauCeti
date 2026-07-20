/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.FieldTheory.IntermediateField.AdjoinEqTop
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic

/-!
# The Frobenius acts on multiquadratic generators by Legendre symbols

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of
integers `d i`, and let `p` be an odd prime dividing none of the `d i`. The multiquadratic
roadmap's Layer 1 states the splitting law in two forms: `p` splits completely iff every `d i`
is a quadratic residue mod `p` (`TauCeti.NumberField.ncard_primesOver_multiquadratic_iff`),
and, more precisely, the Frobenius at `p` acts on the generators by the Legendre symbols. This
file supplies the second, finer form. An arithmetic Frobenius exists at every prime `Q` of
`𝓞 K` above `p` and acts on each generator by the corresponding symbol,

`σ (r i) = legendreSym p (d i) • r i`

(`TauCeti.NumberField.exists_isArithFrobAt_multiquadratic`, combining the existence and
square-root lemmas of `TauCeti.NumberTheory.NumberField.Frobenius`), and the Frobenius is
trivial iff every symbol is `1` (`isArithFrobAt_multiquadratic_eq_one_iff`). Because an
automorphism of a multiquadratic field is determined by its signs on the generators
(`TauCeti.Multiquadratic.signPattern_injective`), these generator-wise signs determine the
Frobenius completely; the resulting sign-vector description under the identification
`Gal(K/ℚ) ≅ (ℤ/2)ⁿ` of `TauCeti.Multiquadratic.galoisGroupEquiv` follows by combining the two,
which this file does not carry out.

## Main results

* `TauCeti.NumberField.exists_isArithFrobAt_multiquadratic`: at every prime `Q` over `p` there
  is a Frobenius, and it sends each generator `r i` to `legendreSym p (d i) • r i`.
* `TauCeti.NumberField.isArithFrobAt_multiquadratic_eq_one_iff`: a Frobenius at `Q` is the
  identity iff every `d i` is a quadratic residue mod `p`.
-/

public section

open NumberField Ideal

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}
  {p : ℕ} [Fact p.Prime]

/-- **A multiquadratic Frobenius is trivial iff every radicand is a residue.** Let
`K = ℚ(√d₁, …, √dₙ)` be generated over `ℚ` by the square roots `r i` of the integers `d i`,
let `p` be an odd prime with `p ∤ d i` for all `i`, and let `σ` be an arithmetic Frobenius at
a prime `Q` of `𝓞 K` above `p`. Then `σ = 1` iff every `d i` is a quadratic residue mod `p`.
Combined with the splitting law, this is the Frobenius-theoretic reading of complete
splitting. -/
theorem isArithFrobAt_multiquadratic_eq_one_iff (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ = 1 ↔ ∀ i, legendreSym p (d i) = 1 := by
  constructor
  · rintro rfl i
    -- The identity fixes `r i`, so the symbol cannot be `-1`: that would force `r i = -r i`.
    have hfix : r i = legendreSym p (d i) • r i := by
      simpa using isArithFrobAt_apply_sqrt hodd (hcop i) (hr i) Q hσ
    have hne : r i ≠ 0 := by
      intro h0
      apply hcop i
      have hzero : algebraMap ℤ K (d i) = 0 := by rw [← hr i, h0]; ring
      have hdi : d i = 0 := by
        rw [eq_intCast] at hzero
        exact_mod_cast hzero
      simp [hdi]
    rcases legendreSym.eq_one_or_neg_one p (a := d i) (by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop i) with h1 | h1
    · exact h1
    · exfalso
      rw [h1, neg_smul, one_smul] at hfix
      apply hne
      have h2 : (2 : K) * r i = 0 := by linear_combination hfix
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
  · intro hqr
    -- `σ` fixes each generator, and the generators generate `K` over `ℚ`.
    refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
    rintro x ⟨i, rfl⟩
    rw [isArithFrobAt_apply_sqrt hodd (hcop i) (hr i) Q hσ, hqr i, one_smul]

/-- **The Frobenius of a multiquadratic field acts by the Legendre sign pattern.** For
`K = ℚ(√d₁, …, √dₙ)` generated over `ℚ` by the square roots `r i` of the integers `d i`, an
odd prime `p` with `p ∤ d i` for all `i`, and any prime `Q` of `𝓞 K` above `p`, there is an
arithmetic Frobenius `σ ∈ Gal(K/ℚ)` at `Q`, and it sends each generator to the corresponding
Legendre multiple: `σ (r i) = legendreSym p (d i) • r i`. This is the roadmap's Frobenius form
of the multiquadratic splitting law, generator by generator. -/
theorem exists_isArithFrobAt_multiquadratic [Finite ι] (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q ∧
      ∀ i, σ (r i) = legendreSym p (d i) • r i := by
  -- `K` is Galois over `ℚ`: transport the multiquadratic `isGalois` along `htop`.
  have hr' : ∀ i, r i ^ 2 = algebraMap ℚ K ((d i : ℚ)) := by
    intro i; rw [hr i]; simp
  haveI : IsGalois ℚ K := by
    have hg := TauCeti.Multiquadratic.isGalois (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr'
    rw [htop] at hg
    exact isGalois_iff_isGalois_top.mp hg
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt (p := p) Q
  exact ⟨σ, hσ, fun i => isArithFrobAt_apply_sqrt hodd (hcop i) (hr i) Q hσ⟩

end TauCeti.NumberField
