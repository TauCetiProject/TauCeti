/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check
public import TauCeti.FieldTheory.GaloisGroups.Symmetric.Basic

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.GaloisGroups.Certificate.Examples
import TauCeti.FieldTheory.GaloisGroups.Certificate.Frobenius
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees

/-!
# Solvability and prime-degree symmetric Galois-group certificates

This module turns finite arithmetic data on a monic integral polynomial `f : ℤ[X]` into a sound
verdict on `Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal` and, in prime degree, on
`Polynomial.HasFullSymmetricGaloisGroup (f.map (Int.castRingHom ℚ))`.

Three families of evidence are combined under `TauCeti.SolvabilityCertificate`:

1. **Degree at most four (`smallDegree`).** Every polynomial of degree at most four has a solvable
   Galois group (`TauCeti.isSolvable_gal_of_natDegree_le_four`), without irreducibility or
   separability assumptions.
2. **Quintic transitive-group labels (`quintic`).** A verified `TauCeti.QuinticCertificate`
   determines the LMFDB label `5T1`–`5T5` of `f` over `ℚ`; `5T1`, `5T2`, and `5T3` are solvable
   whereas `5T4 = A₅` and `5T5 = S₅` are not (`TauCeti.QuinticCertificate.Verifies.isSolvable_iff`).
3. **Prime-degree Frobenius cycle types (`primeSymmetric` / `primeLinearQuadratic`).** For a prime
   degree `d`, an irreducible reduction modulo a good prime `p` (factor degrees `{d}`) proves
   irreducibility over `ℚ` and exhibits a `d`-cycle, while a good prime `q` whose factor degrees
   have a single `2` and odd remaining degrees — in particular `{1, …, 1, 2}` with `d - 2` linear
   factors and one irreducible quadratic factor — exhibits a transposition. Together they force the
   full symmetric group `S_d` (`hasFullSymmetricGaloisGroup_of_prime_factorDegrees`), which is
   non-solvable whenever `5 ≤ d` (`Polynomial.HasFullSymmetricGaloisGroup.not_isSolvable`).

Crucially, every certificate route that claims `isSolvable = false` also certifies irreducibility
of `f` over `ℚ` (`SolvabilityCertificate.Verifies.irreducible_map_rat_of_isSolvable_eq_false`).
Downstream consumers — such as Galois-closure certification for modular-form coefficient fields —
can therefore identify `f.map (Int.castRingHom ℚ)` as the minimal polynomial of any root directly
from `cert.check f = true` and `cert.isSolvable = false`.

## Main definitions and results

* `TauCeti.QuinticCertificate.isSolvable`,
  `TauCeti.QuinticCertificate.Verifies.isSolvable_iff`,
  `TauCeti.QuinticCertificate.check_isSolvable_iff`: solvability verdicts for quintic certificates.
* `TauCeti.hasFullSymmetricGaloisGroup_of_prime_factorDegrees`,
  `TauCeti.hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two`: full symmetric Galois
  group in prime degree from two good-prime factor-degree patterns.
* `TauCeti.SolvabilityCertificate`, `Verifies`, `check`, `isSolvable`, and `check_sound`: unified
  certificate type and Boolean checker for polynomial Galois-group solvability.
* Worked witnesses covering every constructor: `X + 24`, `X ^ 5 - 2`, `X ^ 5 - X - 1`, and the
  `{5}` + `{1, 1, 1, 2}` Frobenius-cycle certificate on `X ^ 5 - X + 3`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics 138,
  Springer, 1993, §6.3.
* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), 387–401.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

/-! ### Solvability verdicts for `QuinticCertificate` -/

namespace QuinticCertificate

/-- Whether the transitive-group label claimed by a quintic certificate is solvable: `true` for
`5T1` (`cyclic`), `5T2` (`dihedral`), and `5T3` (`frobeniusF20`), and `false` for `5T4`
(`alternating`) and `5T5` (`symmetric`). -/
def isSolvable : QuinticCertificate → Bool
  | cyclic .. => true
  | dihedral .. => true
  | frobeniusF20 .. => true
  | alternating .. => false
  | symmetric .. => false

/-- Cyclic quintic certificates claim a solvable Galois group (`5T1`). -/
@[simp] theorem isSolvable_cyclic (p : ℕ) (b : ℚ[X]) : (cyclic p b).isSolvable = true := (rfl)

/-- Dihedral quintic certificates claim a solvable Galois group (`5T2`). -/
@[simp] theorem isSolvable_dihedral (p q : ℕ) (s a : ℤ) :
    (dihedral p q s a).isSolvable = true := (rfl)

/-- Frobenius `F₂₀` quintic certificates claim a solvable Galois group (`5T3`). -/
@[simp] theorem isSolvable_frobeniusF20 (p : ℕ) (a : ℤ) :
    (frobeniusF20 p a).isSolvable = true := (rfl)

/-- Alternating quintic certificates claim a non-solvable Galois group (`5T4`). -/
@[simp] theorem isSolvable_alternating (p q : ℕ) (s : ℤ) :
    (alternating p q s).isSolvable = false := (rfl)

/-- Symmetric quintic certificates claim a non-solvable Galois group (`5T5`). -/
@[simp] theorem isSolvable_symmetric (p q : ℕ) : (symmetric p q).isSolvable = false := (rfl)

/-- `cert.isSolvable` agrees with `(cert.label : ℕ) < 3`, the solvability column of degree five. -/
theorem isSolvable_eq_true_iff (cert : QuinticCertificate) :
    cert.isSolvable = true ↔ (cert.label : ℕ) < 3 := by
  cases cert <;> simp

/-- Every verified quintic certificate proves irreducibility over `ℚ`. -/
theorem Verifies.irreducible_map_rat {cert : QuinticCertificate} {f : ℤ[X]} (hf : f.Monic)
    (h : cert.Verifies f) :
    Irreducible (f.map (Int.castRingHom ℚ)) :=
  (h.hasGaloisLabel hf).irreducible

/-- Every verified quintic certificate forces `f.natDegree = 5`. -/
theorem Verifies.natDegree_eq_five {cert : QuinticCertificate} {f : ℤ[X]} (hf : f.Monic)
    (h : cert.Verifies f) :
    f.natDegree = 5 := by
  have hdeg := (h.hasGaloisLabel hf).natDegree_eq
  rwa [hf.natDegree_map] at hdeg

/-- **Solvability soundness of `QuinticCertificate`.** If `cert.Verifies f` for a monic integral
polynomial `f`, then `(f.map (Int.castRingHom ℚ)).Gal` is solvable if and only if
`cert.isSolvable = true`. -/
theorem Verifies.isSolvable_iff {cert : QuinticCertificate} {f : ℤ[X]} (hf : f.Monic)
    (h : cert.Verifies f) :
    Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal ↔ cert.isSolvable = true := by
  rw [(h.hasGaloisLabel hf).isSolvable_iff_ne_five_or_lt_three, isSolvable_eq_true_iff]
  simp

/-- Boolean form of `QuinticCertificate.Verifies.isSolvable_iff`. -/
theorem check_isSolvable_iff {cert : QuinticCertificate} {f : ℤ[X]} (hf : f.Monic)
    (h : cert.check f = true) :
    Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal ↔ cert.isSolvable = true :=
  (check_eq_true_iff.mp h).isSolvable_iff hf

end QuinticCertificate

/-! ### Prime-degree symmetric Galois-group certificates from Frobenius cycle types -/

section PrimeDegreeSymmetric

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- **Full symmetric Galois group in prime degree from two good-prime factor-degree patterns.**
Let `f : ℤ[X]` be monic and `d` be prime. If `f` is irreducible modulo a good prime `p`
(`HasFactorDegrees f p {d}`) and modulo a good prime `q` has factor degrees `t` with a single `2`
and all other entries odd (`HasFactorDegrees f q t`), then `f.map (Int.castRingHom ℚ)` has full
symmetric Galois group `S_d`. -/
theorem hasFullSymmetricGaloisGroup_of_prime_factorDegrees {f : ℤ[X]} (hf : f.Monic)
    {d p q : ℕ} {t : Multiset ℕ} (hd : d.Prime)
    (hp : HasFactorDegrees f p {d}) (hq : HasFactorDegrees f q t)
    (htwo : t.count 2 = 1) (hodd : ∀ k ∈ t, k ≠ 2 → Odd k) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup := by
  have hirr : Irreducible (f.map (Int.castRingHom ℚ)) := hp.irreducible_map_rat hf
  have hdeg : f.natDegree = d := by simpa using (hp.sum_eq_natDegree hf).symm
  obtain ⟨hq_fact, hq_good, hq_fac⟩ := hq.exists_fact
  let _ := hq_fact
  rw [hasFullSymmetricGaloisGroup_iff_separable_and_surjective_galActionHom ℂ]
  refine ⟨hirr.separable, surjective_galActionHom_of_prime_natDegree hf hirr
    (hdeg ▸ hd) q ((isGoodPrime_iff f q).mp hq_good) ?_ ?_⟩
  · rwa [hq_fac]
  · rwa [hq_fac]

/-- **The `{d}` + `{1, …, 1, 2}` Frobenius-cycle certificate in prime degree.** If a monic
polynomial `f : ℤ[X]` is irreducible of prime degree `d` modulo a good prime `p` and splits modulo
a good prime `q` into `d - 2` linear factors and one irreducible quadratic factor, then
`f.map (Int.castRingHom ℚ)` has full symmetric Galois group `S_d`. -/
theorem hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two {f : ℤ[X]} (hf : f.Monic)
    {d p q : ℕ} (hd : d.Prime) (hp : HasFactorDegrees f p {d})
    (hq : HasFactorDegrees f q (Multiset.replicate (d - 2) 1 + {2})) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup := by
  refine hasFullSymmetricGaloisGroup_of_prime_factorDegrees hf hd hp hq ?_ ?_
  · simp [Multiset.count_replicate]
  · intro k hk hk2
    rcases Multiset.mem_add.mp hk with hk1 | hk2'
    · rw [Multiset.eq_of_mem_replicate hk1]
      exact odd_one
    · exact absurd (Multiset.mem_singleton.mp hk2') hk2

/-- For a prime `d ≥ 5`, the `{d}` + `{1, …, 1, 2}` Frobenius-cycle certificate proves that the
Galois group of `f` over `ℚ` is not solvable. -/
theorem not_isSolvable_gal_of_prime_and_replicate_one_add_two {f : ℤ[X]} (hf : f.Monic)
    {d p q : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hp : HasFactorDegrees f p {d})
    (hq : HasFactorDegrees f q (Multiset.replicate (d - 2) 1 + {2})) :
    ¬ Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal := by
  have hdeg : (f.map (Int.castRingHom ℚ)).natDegree = d := by
    rw [hf.natDegree_map]
    simpa using (hp.sum_eq_natDegree hf).symm
  exact (hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two hf hd hp hq).not_isSolvable
    (hdeg ▸ hd5)

end PrimeDegreeSymmetric

/-! ### Unified solvability certificate -/

/-- A finite certificate deciding whether the Galois group of a monic integral polynomial `f : ℤ[X]`
over `ℚ` is solvable:
* `smallDegree`: `f.natDegree ≤ 4` (always solvable);
* `quintic cert`: `cert : QuinticCertificate` verifies for `f` (solvable for `5T1`–`5T3`,
  non-solvable for `5T4`–`5T5`);
* `primeSymmetric d p q t`: `d ≥ 5` is prime, `f` has factor degrees `{d}` at `p` and factor
  degrees `t` at `q` with a single `2` and odd remaining degrees (non-solvable, full symmetric
  group `S_d`). -/
inductive SolvabilityCertificate : Type
  /-- Degree at most four: `Gal(f/ℚ)` embeds in `S_n` with `n ≤ 4`, hence is solvable. -/
  | smallDegree
  /-- Degree five: certified by a `QuinticCertificate`. -/
  | quintic (cert : QuinticCertificate)
  /-- Prime degree `d ≥ 5` with Frobenius cycle types `{d}` at `p` and `t` at `q` exhibiting a
  `d`-cycle and a transposition, certifying `Gal(f/ℚ) ≅ S_d`. -/
  | primeSymmetric (d p q : ℕ) (t : Multiset ℕ)

namespace SolvabilityCertificate

/-- Smart constructor for the classical `{d}` + `{1, …, 1, 2}` Frobenius-cycle certificate in prime
degree `d ≥ 5`: irreducible modulo `p`, and `d - 2` linear factors plus one quadratic factor modulo
`q`. -/
def primeLinearQuadratic (d p q : ℕ) : SolvabilityCertificate :=
  primeSymmetric d p q (Multiset.replicate (d - 2) 1 + {2})

/-- Unfolding lemma for `primeLinearQuadratic`. -/
theorem primeLinearQuadratic_def (d p q : ℕ) :
    primeLinearQuadratic d p q = primeSymmetric d p q (Multiset.replicate (d - 2) 1 + {2}) :=
  (rfl)

/-- The solvability verdict claimed by a `SolvabilityCertificate`. -/
def isSolvable : SolvabilityCertificate → Bool
  | smallDegree => true
  | quintic cert => cert.isSolvable
  | primeSymmetric .. => false

/-- Small-degree certificates claim a solvable Galois group. -/
@[simp] theorem isSolvable_smallDegree : smallDegree.isSolvable = true := (rfl)

/-- Quintic solvability certificates delegate `isSolvable` to `QuinticCertificate.isSolvable`. -/
@[simp] theorem isSolvable_quintic (cert : QuinticCertificate) :
    (quintic cert).isSolvable = cert.isSolvable := (rfl)

/-- Prime-degree symmetric certificates claim a non-solvable Galois group. -/
@[simp] theorem isSolvable_primeSymmetric (d p q : ℕ) (t : Multiset ℕ) :
    (primeSymmetric d p q t).isSolvable = false := (rfl)

/-- `primeLinearQuadratic` certificates claim a non-solvable Galois group. -/
@[simp] theorem isSolvable_primeLinearQuadratic (d p q : ℕ) :
    (primeLinearQuadratic d p q).isSolvable = false := (rfl)

/-- Verification conditions for a `SolvabilityCertificate` on a polynomial `f : ℤ[X]`. -/
def Verifies : SolvabilityCertificate → ℤ[X] → Prop
  | smallDegree, f => f.natDegree ≤ 4
  | quintic cert, f => cert.Verifies f
  | primeSymmetric d p q t, f =>
      d.Prime ∧ 5 ≤ d ∧ HasFactorDegrees f p {d} ∧ HasFactorDegrees f q t ∧
        t.count 2 = 1 ∧ ∀ k ∈ t, k ≠ 2 → Odd k

open scoped Classical in
/-- Boolean verdict on the verification conditions of a `SolvabilityCertificate`. -/
def check (cert : SolvabilityCertificate) (f : ℤ[X]) : Bool :=
  decide (cert.Verifies f)

/-- Verification condition of `smallDegree`. -/
@[simp] theorem verifies_smallDegree_iff {f : ℤ[X]} :
    smallDegree.Verifies f ↔ f.natDegree ≤ 4 := (Iff.rfl)

/-- Verification condition of `quintic`. -/
@[simp] theorem verifies_quintic_iff {cert : QuinticCertificate} {f : ℤ[X]} :
    (quintic cert).Verifies f ↔ cert.Verifies f := (Iff.rfl)

/-- Verification condition of `primeSymmetric`. -/
@[simp] theorem verifies_primeSymmetric_iff {d p q : ℕ} {t : Multiset ℕ} {f : ℤ[X]} :
    (primeSymmetric d p q t).Verifies f ↔
      d.Prime ∧ 5 ≤ d ∧ HasFactorDegrees f p {d} ∧ HasFactorDegrees f q t ∧
        t.count 2 = 1 ∧ ∀ k ∈ t, k ≠ 2 → Odd k := (Iff.rfl)

/-- Simplified verification condition of `primeLinearQuadratic`. -/
@[simp] theorem verifies_primeLinearQuadratic_iff {d p q : ℕ} {f : ℤ[X]} :
    (primeLinearQuadratic d p q).Verifies f ↔
      d.Prime ∧ 5 ≤ d ∧ HasFactorDegrees f p {d} ∧
        HasFactorDegrees f q (Multiset.replicate (d - 2) 1 + {2}) := by
  rw [primeLinearQuadratic_def, verifies_primeSymmetric_iff]
  refine ⟨fun ⟨hd, hd5, hp, hq, _, _⟩ ↦ ⟨hd, hd5, hp, hq⟩,
    fun ⟨hd, hd5, hp, hq⟩ ↦ ⟨hd, hd5, hp, hq, by simp [Multiset.count_replicate], ?_⟩⟩
  intro k hk hk2
  rcases Multiset.mem_add.mp hk with hk1 | hk2'
  · rw [Multiset.eq_of_mem_replicate hk1]
    exact odd_one
  · exact absurd (Multiset.mem_singleton.mp hk2') hk2

/-- `cert.check f = true` holds if and only if `cert.Verifies f`. -/
@[simp] theorem check_eq_true_iff {cert : SolvabilityCertificate} {f : ℤ[X]} :
    cert.check f = true ↔ cert.Verifies f := by
  simp only [check, decide_eq_true_eq]

/-- A verified `primeSymmetric` certificate proves that `f` has degree `d`. -/
theorem Verifies.natDegree_eq_of_primeSymmetric {d p q : ℕ} {t : Multiset ℕ} {f : ℤ[X]}
    (hf : f.Monic) (h : (primeSymmetric d p q t).Verifies f) :
    f.natDegree = d := by
  obtain ⟨-, -, hp, -⟩ := h
  simpa using (hp.sum_eq_natDegree hf).symm

/-- A verified `primeSymmetric` certificate proves `HasFullSymmetricGaloisGroup` over `ℚ`. -/
theorem Verifies.hasFullSymmetricGaloisGroup_of_primeSymmetric {d p q : ℕ} {t : Multiset ℕ}
    {f : ℤ[X]} (hf : f.Monic) (h : (primeSymmetric d p q t).Verifies f) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup := by
  obtain ⟨hd, -, hp, hq, htwo, hodd⟩ := h
  exact hasFullSymmetricGaloisGroup_of_prime_factorDegrees hf hd hp hq htwo hodd

/-- **Soundness of `SolvabilityCertificate`.** If `cert.Verifies f` for a monic polynomial
`f : ℤ[X]`, then `(f.map (Int.castRingHom ℚ)).Gal` is solvable if and only if
`cert.isSolvable = true`. -/
theorem Verifies.isSolvable_iff {cert : SolvabilityCertificate} {f : ℤ[X]} (hf : f.Monic)
    (h : cert.Verifies f) :
    Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal ↔ cert.isSolvable = true := by
  cases cert with
  | smallDegree =>
    simp only [isSolvable_smallDegree, iff_true]
    exact isSolvable_gal_of_natDegree_le_four (hf.natDegree_map (Int.castRingHom ℚ) ▸ h)
  | quintic qcert =>
    exact QuinticCertificate.Verifies.isSolvable_iff hf h
  | primeSymmetric d p q t =>
    simp only [isSolvable_primeSymmetric, Bool.false_eq_true, iff_false]
    have hsym := h.hasFullSymmetricGaloisGroup_of_primeSymmetric hf
    have hdeg : (f.map (Int.castRingHom ℚ)).natDegree = d := by
      rw [hf.natDegree_map, h.natDegree_eq_of_primeSymmetric hf]
    exact hsym.not_isSolvable (hdeg ▸ h.2.1)

/-- **Soundness of the Boolean solvability checker.** -/
theorem check_sound {cert : SolvabilityCertificate} {f : ℤ[X]} (hf : f.Monic)
    (h : cert.check f = true) :
    Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal ↔ cert.isSolvable = true :=
  (check_eq_true_iff.mp h).isSolvable_iff hf

/-- A certificate with `check = true` and `isSolvable = true` proves solvability of
`(f.map (Int.castRingHom ℚ)).Gal`. -/
theorem check_isSolvable {cert : SolvabilityCertificate} {f : ℤ[X]} (hf : f.Monic)
    (hcheck : cert.check f = true) (hsolv : cert.isSolvable = true) :
    Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal :=
  (check_sound hf hcheck).mpr hsolv

/-- A certificate with `check = true` and `isSolvable = false` refutes solvability of
`(f.map (Int.castRingHom ℚ)).Gal`. -/
theorem check_not_isSolvable {cert : SolvabilityCertificate} {f : ℤ[X]} (hf : f.Monic)
    (hcheck : cert.check f = true) (hns : cert.isSolvable = false) :
    ¬ Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal := by
  rw [check_sound hf hcheck, hns]
  exact Bool.false_ne_true

/-- Every verified certificate that claims non-solvability (`isSolvable = false`) also proves
irreducibility of `f` over `ℚ`: both `quintic` and `primeSymmetric` carry singleton factor-degree
evidence at a good prime. -/
theorem Verifies.irreducible_map_rat_of_isSolvable_eq_false {cert : SolvabilityCertificate}
    {f : ℤ[X]} (hf : f.Monic) (h : cert.Verifies f) (hns : cert.isSolvable = false) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  cases cert with
  | smallDegree => simp at hns
  | quintic qcert => exact QuinticCertificate.Verifies.irreducible_map_rat hf h
  | primeSymmetric d p q t => exact h.2.2.1.irreducible_map_rat hf

/-- Boolean form of `Verifies.irreducible_map_rat_of_isSolvable_eq_false`. -/
theorem check_irreducible_map_rat_of_isSolvable_eq_false {cert : SolvabilityCertificate}
    {f : ℤ[X]} (hf : f.Monic) (hcheck : cert.check f = true) (hns : cert.isSolvable = false) :
    Irreducible (f.map (Int.castRingHom ℚ)) :=
  (check_eq_true_iff.mp hcheck).irreducible_map_rat_of_isSolvable_eq_false hf hns

/-- A verified `primeLinearQuadratic d p q` certificate proves full symmetric Galois group `S_d`.
-/
theorem check_hasFullSymmetricGaloisGroup_of_primeLinearQuadratic {d p q : ℕ} {f : ℤ[X]}
    (hf : f.Monic) (hcheck : (primeLinearQuadratic d p q).check f = true) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup := by
  have hv := check_eq_true_iff.mp hcheck
  rw [primeLinearQuadratic_def] at hv
  exact hv.hasFullSymmetricGaloisGroup_of_primeSymmetric hf

/-- A verified `primeLinearQuadratic d p q` certificate proves `f.natDegree = d`. -/
theorem check_natDegree_eq_of_primeLinearQuadratic {d p q : ℕ} {f : ℤ[X]}
    (hf : f.Monic) (hcheck : (primeLinearQuadratic d p q).check f = true) :
    f.natDegree = d := by
  have hv := check_eq_true_iff.mp hcheck
  rw [primeLinearQuadratic_def] at hv
  exact hv.natDegree_eq_of_primeSymmetric hf

/-! ### Worked examples covering every `SolvabilityCertificate` constructor -/

/-- `smallDegree` checks on `X + 24` (the Hecke polynomial `X - τ(2)` of the Ramanujan Δ-form at
`p = 2`), certifying solvability. -/
theorem check_smallDegree_X_add_twenty_four :
    smallDegree.check (X + 24 : ℤ[X]) = true := by
  rw [check_eq_true_iff, verifies_smallDegree_iff]
  compute_degree!

/-- `quintic (.frobeniusF20 11 0)` checks on the Kummer quintic `X ^ 5 - 2`, certifying solvability
of its `F₂₀` Galois group. -/
theorem check_quintic_X_pow_five_sub_two :
    (quintic (.frobeniusF20 11 0)).check (X ^ 5 - 2) = true := by
  rw [check_eq_true_iff, verifies_quintic_iff, ← QuinticCertificate.check_eq_true_iff]
  exact QuinticCertificate.check_X_pow_five_sub_two

/-- `quintic (.symmetric 5 2)` checks on `X ^ 5 - X - 1`, certifying non-solvability via `{5}` mod
`5` and `{2, 3}` mod `2`. -/
theorem check_quintic_X_pow_five_sub_X_sub_one :
    (quintic (.symmetric 5 2)).check (X ^ 5 - X - 1) = true := by
  rw [check_eq_true_iff, verifies_quintic_iff, ← QuinticCertificate.check_eq_true_iff]
  exact QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one

end SolvabilityCertificate

/-! ### Worked example for `primeLinearQuadratic`: `X ^ 5 - X + 3` at `p = 5` and `q = 3` -/

section PrimeLinearQuadraticExample

local instance factPrimeFiveSolvable : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `X ^ 5 - X + 3` is monic over `ℤ`. -/
theorem monic_X_pow_five_sub_X_add_three : (X ^ 5 - X + 3 : ℤ[X]).Monic := by
  have h : (X ^ 5 - X + 3 : ℤ[X]) = X ^ 5 - (X - 3) := by ring
  rw [h]
  exact monic_X_pow_sub (by compute_degree!)

/-- The discriminant of `X ^ 5 - X + 3` is `5⁵ · 3⁴ - 4⁴ = 252869`. -/
theorem discr_X_pow_five_sub_X_add_three : (X ^ 5 - X + 3 : ℤ[X]).discr = 252869 := by
  have h : (X ^ 5 - X + 3 : ℤ[X]) = X ^ 5 + C (-1 : ℤ) * X + C (3 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [h, discr_X_pow_five_add_C_mul_X_add_C]
  norm_num

/-- `X ^ 5 - X + 3` is an Artin–Schreier quintic modulo `5` and is therefore irreducible over
`ZMod 5`. -/
theorem irreducible_X_pow_five_sub_X_add_three_zmod_five :
    Irreducible (X ^ 5 - X + 3 : (ZMod 5)[X]) := by
  have h : (X ^ 5 - X + 3 : (ZMod 5)[X]) = X ^ 5 + C (-1) * X + C 3 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [h]
  exact irreducible_X_pow_five_add_C_mul_X_add_C (by decide) (by decide)

/-- `X ^ 5 - X + 3` has factor degrees `{5}` modulo `5`. -/
theorem factorDegrees_X_pow_five_sub_X_add_three_five :
    (X ^ 5 - X + 3 : ℤ[X]).factorDegrees 5 = {5} := by
  rw [Polynomial.factorDegrees_eq_singleton_iff]
  have hmap : (X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom (ZMod 5)) = X ^ 5 - X + 3 := by
    simp
  rw [hmap]
  refine ⟨irreducible_X_pow_five_sub_X_add_three_zmod_five, ?_⟩
  have h : (X ^ 5 - X + 3 : (ZMod 5)[X]) = X ^ 5 - (X - 3) := by ring
  rw [h]
  compute_degree!

/-- `X ^ 2 + 1` is irreducible over `ZMod 3`: `-1` is not a square modulo `3`. -/
theorem irreducible_X_sq_add_one_zmod_three : Irreducible (X ^ 2 + 1 : (ZMod 3)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    rw [hdeg]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- Modulo `3`, `X ^ 5 - X + 3` reduces to `X ^ 5 - X = X * (X - 1) * (X + 1) * (X ^ 2 + 1)`, so
its factor degrees are `{1, 1, 1, 2}`. -/
theorem factorDegrees_X_pow_five_sub_X_add_three_three :
    (X ^ 5 - X + 3 : ℤ[X]).factorDegrees 3 = {1, 1, 1, 2} := by
  let s : Multiset (ZMod 3)[X] := {X, X - C 1, X - C (-1), X ^ 2 + 1}
  have hs : ∀ q ∈ s, Irreducible q := by
    intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact irreducible_X
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact irreducible_X_sub_C 1
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact irreducible_X_sub_C (-1)
    · rw [Multiset.mem_singleton.mp hq]
      exact irreducible_X_sq_add_one_zmod_three
  have hmap : (X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom (ZMod 3)) = s.prod := by
    have h3 : (3 : (ZMod 3)[X]) = 0 := by simpa using CharP.cast_eq_zero (ZMod 3)[X] 3
    dsimp [s]
    simp only [Multiset.prod_cons, Multiset.prod_singleton,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, C_1, map_neg, h3]
    ring
  rw [Polynomial.factorDegrees_eq_map_natDegree_of_map_eq_prod hs hmap]
  have hd2 : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
  simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    natDegree_X, natDegree_X_sub_C, hd2]

/-- The `{5}` + `{1, 1, 1, 2}` Frobenius-cycle certificate `primeLinearQuadratic 5 5 3` checks on
`X ^ 5 - X + 3`. -/
theorem SolvabilityCertificate.check_primeLinearQuadratic_X_pow_five_sub_X_add_three :
    (SolvabilityCertificate.primeLinearQuadratic 5 5 3).check (X ^ 5 - X + 3) = true := by
  have hgood5 : IsGoodPrime (X ^ 5 - X + 3) 5 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  have hgood3 : IsGoodPrime (X ^ 5 - X + 3) 3 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  rw [SolvabilityCertificate.check_eq_true_iff,
    SolvabilityCertificate.verifies_primeLinearQuadratic_iff]
  refine ⟨Nat.prime_five, le_rfl,
    HasFactorDegrees.mk hgood5 factorDegrees_X_pow_five_sub_X_add_three_five,
    HasFactorDegrees.mk hgood3 ?_⟩
  rw [factorDegrees_X_pow_five_sub_X_add_three_three]
  decide

/-- `X ^ 5 - X + 3` has full symmetric Galois group `S₅` over `ℚ`. -/
theorem hasFullSymmetricGaloisGroup_X_pow_five_sub_X_add_three :
    ((X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup :=
  SolvabilityCertificate.check_hasFullSymmetricGaloisGroup_of_primeLinearQuadratic
    monic_X_pow_five_sub_X_add_three
    SolvabilityCertificate.check_primeLinearQuadratic_X_pow_five_sub_X_add_three

/-- The Galois group of `X ^ 5 - X + 3` over `ℚ` is not solvable. -/
theorem not_isSolvable_gal_X_pow_five_sub_X_add_three :
    ¬ Group.IsSolvable ((X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom ℚ)).Gal :=
  SolvabilityCertificate.check_not_isSolvable monic_X_pow_five_sub_X_add_three
    SolvabilityCertificate.check_primeLinearQuadratic_X_pow_five_sub_X_add_three rfl

end PrimeLinearQuadraticExample

end TauCeti
