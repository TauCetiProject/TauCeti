/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Global Artin symbols of primes in quadratic extensions of `ℚ`

Let `E = ℚ(r)` be a number field generated over `ℚ` by a square root `r` of an integer `d : ℤ`,
assumed abelian Galois over `ℚ` (as supplied by `TauCeti.Multiquadratic.isGalois_of_adjoin_eq_top`
and `TauCeti.Multiquadratic.isMulCommutative_of_adjoin_eq_top`, or
`TauCeti.Multiquadratic.isAbelianGalois` for an intermediate field). For a finite place `v` of `ℚ`
unramified in `E`, the finite global Artin symbol `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` is
an arithmetic Frobenius at every prime `Q` of `𝓞 E` above `v` (`ideleClassArtinMap_isArithFrobAt`).

Evaluating that Frobenius on the generator `r` yields the classical quadratic splitting criteria:

* at an odd rational prime `p ∤ d` with `N(v) = p`, `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)
  = 1` if and only if `legendreSym p d = 1` (`ideleClassArtinMap_sqrt_prime_odd_eq_one_iff`);
* when `d ≡ 1 (mod 4)` and `v` is the dyadic prime (`N(v) = 2`),
  `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1` if and only if `d ≡ 1 (mod 8)`
  (`ideleClassArtinMap_sqrt_prime_two_eq_one_iff`).

Both evaluations are also provided directly for an intermediate field `ℚ⟮r⟯` inside a larger number
field `L` (`ideleClassArtinMap_adjoin_sqrt_prime_odd_eq_one_iff` and
`ideleClassArtinMap_adjoin_sqrt_prime_two_eq_one_iff`).

## Main results

* `TauCeti.ClassFieldTheory.ideleClassArtinMap_sqrt_prime_odd_eq_one_iff`: Legendre-symbol
  criterion for `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1` at an odd prime `p ∤ d`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_sqrt_prime_two_eq_one_iff`: mod-`8` criterion for
  `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1` at `p = 2` when `d ≡ 1 (mod 4)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_adjoin_sqrt_prime_odd_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_adjoin_sqrt_prime_two_eq_one_iff`: the same
  evaluations for `ℚ⟮r⟯` inside an ambient number field `L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §5.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField _root_.IntermediateField

section Generated

variable {E : Type} [Field E] [NumberField E] [IsAbelianGalois ℚ E]

/-- **Global Artin symbol of an odd prime in `ℚ(√d)`.** For `E` generated over `ℚ` by `r` with
`r² = d` (`d : ℤ`) and an odd rational prime `p ∤ d` represented by `v` (`N(v) = p`), the Artin
symbol `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` is trivial if and only if
`legendreSym p d = 1`. -/
theorem ideleClassArtinMap_sqrt_prime_odd_eq_one_iff {r : E} {d : ℤ}
    (hr : r ^ 2 = algebraMap ℤ E d) (hgen : IntermediateField.adjoin ℚ {r} = ⊤)
    (v : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} [Fact p.Prime]
    (hpv : Ideal.absNorm v.asIdeal = p) (hodd : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1 ↔ legendreSym p d = 1 := by
  have hr' : ∀ _ : Unit, r ^ 2 = algebraMap ℤ E d := fun _ ↦ hr
  have htop : IntermediateField.adjoin ℚ (Set.range fun _ : Unit ↦ r) = ⊤ := by
    rwa [Set.range_const]
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    hpv ▸ _root_.Rat.HeightOneSpectrum.liesOver_span_absNorm v Q
  have := Multiquadratic.isUnramifiedAt_of_forall_not_dvd hr' htop hodd (fun _ ↦ hpd) Q
  rw [TauCeti.IntermediateField.algEquiv_eq_one_iff_of_adjoin_eq_top hgen]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact NumberField.isArithFrobAt_apply_sqrt_eq_self_iff hodd hpd hr Q
    ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ Q).mp (ideleClassArtinMap_isArithFrobAt E v Q))

/-- **Global Artin symbol at `2` in `ℚ(√d)` when `d ≡ 1 (mod 4)`.** For `E` generated over `ℚ` by
`r` with `r² = d` (`d : ℤ`, `d % 4 = 1`) and the dyadic prime `v` of `ℚ` (`N(v) = 2`), the Artin
symbol `ideleClassArtinMap ℚ E (primeIdeleClass ℚ v)` is trivial if and only if `d % 8 = 1`. -/
theorem ideleClassArtinMap_sqrt_prime_two_eq_one_iff {r : E} {d : ℤ}
    (hr : r ^ 2 = algebraMap ℤ E d) (hgen : IntermediateField.adjoin ℚ {r} = ⊤) (hd4 : d % 4 = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Ideal.absNorm v.asIdeal = 2) :
    ideleClassArtinMap ℚ E (primeIdeleClass ℚ v) = 1 ↔ d % 8 = 1 := by
  have hr' : ∀ _ : Unit, r ^ 2 = algebraMap ℤ E d := fun _ ↦ hr
  have htop : IntermediateField.adjoin ℚ (Set.range fun _ : Unit ↦ r) = ⊤ := by
    rwa [Set.range_const]
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  have : Q.LiesOver (Ideal.span {(2 : ℤ)}) := by
    have h := _root_.Rat.HeightOneSpectrum.liesOver_span_absNorm v Q
    rwa [hv, Nat.cast_ofNat] at h
  have := Multiquadratic.isUnramifiedAt_of_forall_mod_four_eq_one hr' htop (fun _ ↦ hd4) Q
  rw [TauCeti.IntermediateField.algEquiv_eq_one_iff_of_adjoin_eq_top hgen]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hr hd4 Q
    ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ Q).mp (ideleClassArtinMap_isArithFrobAt E v Q))

end Generated

section AdjoinSimple

variable {L : Type} [Field L] [NumberField L]

/-- For `r ∈ L` with `r² = d` (`d : ℤ`) and an odd rational prime `p ∤ d` represented by `v`
(`N(v) = p`), the quadratic Artin symbol `ideleClassArtinMap ℚ ℚ⟮r⟯ (primeIdeleClass ℚ v)` is
trivial if and only if `legendreSym p d = 1`. -/
theorem ideleClassArtinMap_adjoin_sqrt_prime_odd_eq_one_iff {r : L} [IsAbelianGalois ℚ ℚ⟮r⟯]
    {d : ℤ} (hr : r ^ 2 = algebraMap ℤ L d) (v : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} [Fact p.Prime]
    (hpv : Ideal.absNorm v.asIdeal = p) (hodd : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    ideleClassArtinMap ℚ ℚ⟮r⟯ (primeIdeleClass ℚ v) = 1 ↔ legendreSym p d = 1 :=
  ideleClassArtinMap_sqrt_prime_odd_eq_one_iff (r := AdjoinSimple.gen ℚ r)
    (Subtype.ext (by simpa using hr)) (IntermediateField.adjoin_adjoinSimple_gen_eq_top r)
    v hpv hodd hpd

/-- For `r ∈ L` with `r² = d` (`d : ℤ`, `d % 4 = 1`) and the dyadic prime `v` of `ℚ` (`N(v) = 2`),
the quadratic Artin symbol `ideleClassArtinMap ℚ ℚ⟮r⟯ (primeIdeleClass ℚ v)` is trivial if and only
if `d % 8 = 1`. -/
theorem ideleClassArtinMap_adjoin_sqrt_prime_two_eq_one_iff {r : L} [IsAbelianGalois ℚ ℚ⟮r⟯]
    {d : ℤ} (hr : r ^ 2 = algebraMap ℤ L d) (hd4 : d % 4 = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Ideal.absNorm v.asIdeal = 2) :
    ideleClassArtinMap ℚ ℚ⟮r⟯ (primeIdeleClass ℚ v) = 1 ↔ d % 8 = 1 :=
  ideleClassArtinMap_sqrt_prime_two_eq_one_iff (r := AdjoinSimple.gen ℚ r)
    (Subtype.ext (by simpa using hr)) (IntermediateField.adjoin_adjoinSimple_gen_eq_top r)
    hd4 v hv

end AdjoinSimple

end TauCeti.ClassFieldTheory
