/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check
public import TauCeti.FieldTheory.GaloisGroups.Certificate.Generic
public import TauCeti.FieldTheory.GaloisGroups.NormalClosure
public import TauCeti.FieldTheory.GaloisGroups.Symmetric.Basic

import Mathlib.Tactic.ComputeDegree
import TauCeti.FieldTheory.GaloisGroups.Certificate.Examples
import TauCeti.FieldTheory.GaloisGroups.Certificate.Frobenius
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.Minpoly

/-!
# Solvability certificates for polynomial Galois groups and Galois closures

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
   degree `d ≥ 5`, an irreducible reduction modulo a good prime `p` (factor degrees `{d}`) proves
   irreducibility over `ℚ` and exhibits a `d`-cycle, while a good prime `q` whose factor degrees
   `t` have a single `2` and odd remaining degrees — in particular `{1, …, 1, 2}` with `d - 2`
   linear factors and one irreducible quadratic factor (`primeLinearQuadratic d p q`) — exhibits a
   transposition. Together they force the full symmetric group `S_d` and refute solvability
   (`TauCeti.hasFullSymmetricGaloisGroup_of_prime_factorDegrees` and
   `TauCeti.not_isSolvable_gal_of_prime_factorDegrees` in
   `TauCeti.FieldTheory.GaloisGroups.Certificate.Generic`).

Crucially, every certificate route that claims `isSolvable = false` also certifies irreducibility
of `f` over `ℚ` (`SolvabilityCertificate.Verifies.irreducible_map_rat_of_isSolvable_eq_false`),
hence identifies `f.map (Int.castRingHom ℚ)` as the minimal polynomial of any root
(`SolvabilityCertificate.check_minpoly_eq_map_rat_of_isSolvable_eq_false`). Combining this with
`TauCeti.FieldTheory.GaloisGroups.NormalClosure` yields general certificate-driven solvability,
single-element generation, and Galois-group order theorems for
`IntermediateField.normalClosure ℚ K Ω` of any algebraic or finite-dimensional intermediate field
`K / ℚ` inside `[IsAlgClosed Ω]`.

## Main definitions and results

* `TauCeti.QuinticCertificate.isSolvable`,
  `TauCeti.QuinticCertificate.Verifies.isSolvable_iff`,
  `TauCeti.QuinticCertificate.check_isSolvable_iff`: solvability verdicts for quintic certificates.
* `TauCeti.SolvabilityCertificate`, `Verifies`, `check`, `isSolvable`, and `check_sound`: unified
  certificate type and Boolean checker for polynomial Galois-group solvability.
* `TauCeti.SolvabilityCertificate.check_hasFullSymmetricGaloisGroup_of_primeSymmetric`,
  `TauCeti.SolvabilityCertificate.check_natDegree_eq_of_primeSymmetric`: full symmetric group `S_d`
  and degree `d` from any verified `primeSymmetric d p q t` certificate.
* `TauCeti.SolvabilityCertificate.check_minpoly_eq_map_rat_of_isSolvable_eq_false`,
  `TauCeti.SolvabilityCertificate.not_isSolvable_gal_normalClosure_of_check_eq_true`,
  `TauCeti.SolvabilityCertificate.isSolvable_gal_normalClosure_iff_of_check_eq_true`,
  `TauCeti.SolvabilityCertificate.adjoin_simple_eq_of_primeSymmetric`,
  `TauCeti.SolvabilityCertificate.natCard_gal_normalClosure_of_primeSymmetric`:
  certificate-to-Galois-closure transfer for intermediate fields `K : IntermediateField ℚ Ω`.
* Worked `check` witnesses covering every constructor: `X + 24`, `X ^ 5 - 2`, `X ^ 5 - X - 1`, and
  the `{5}` + `{1, 1, 1, 2}` Frobenius-cycle certificate on `X ^ 5 - X + 3`.

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
  have ⟨htwo, hodd⟩ := count_two_and_odd_replicate_one_add_two (d - 2)
  exact ⟨fun ⟨hd, hd5, hp, hq, _, _⟩ ↦ ⟨hd, hd5, hp, hq⟩,
    fun ⟨hd, hd5, hp, hq⟩ ↦ ⟨hd, hd5, hp, hq, htwo, hodd⟩⟩

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
    exact not_isSolvable_gal_of_prime_factorDegrees hf h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2

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

/-- Any root `α` in a nontrivial `ℚ`-algebra of a monic polynomial `f : ℤ[X]` certified with
`cert.check f = true` and `cert.isSolvable = false` has minimal polynomial
`f.map (Int.castRingHom ℚ)`. -/
theorem check_minpoly_eq_map_rat_of_isSolvable_eq_false {E : Type*} [Ring E] [Nontrivial E]
    [Algebra ℚ E] {cert : SolvabilityCertificate} {f : ℤ[X]} {α : E} (hf : f.Monic)
    (hroot : aeval α f = 0) (hcheck : cert.check f = true) (hns : cert.isSolvable = false) :
    minpoly ℚ α = f.map (Int.castRingHom ℚ) :=
  minpoly_eq_map_intCastRingHom_of_aeval_eq_zero hf
    (check_irreducible_map_rat_of_isSolvable_eq_false hf hcheck hns) hroot

/-- A verified `primeSymmetric d p q t` certificate proves full symmetric Galois group `S_d`.
Because `primeLinearQuadratic d p q` is definitionally a `primeSymmetric` certificate, this applies
directly to `primeLinearQuadratic` witnesses as well. -/
theorem check_hasFullSymmetricGaloisGroup_of_primeSymmetric {d p q : ℕ} {t : Multiset ℕ}
    {f : ℤ[X]} (hf : f.Monic) (hcheck : (primeSymmetric d p q t).check f = true) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup :=
  (check_eq_true_iff.mp hcheck).hasFullSymmetricGaloisGroup_of_primeSymmetric hf

/-- A verified `primeSymmetric d p q t` certificate proves `f.natDegree = d`. -/
theorem check_natDegree_eq_of_primeSymmetric {d p q : ℕ} {t : Multiset ℕ} {f : ℤ[X]}
    (hf : f.Monic) (hcheck : (primeSymmetric d p q t).check f = true) :
    f.natDegree = d :=
  (check_eq_true_iff.mp hcheck).natDegree_eq_of_primeSymmetric hf

/-! ### Certificate transfer to Galois closures of intermediate fields -/

section NormalClosure

open _root_.IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {K : IntermediateField ℚ Ω}

/-- If `α ∈ K` for an algebraic intermediate field `K / ℚ` inside `[IsAlgClosed Ω]` is a root of a
monic polynomial `P : ℤ[X]` certified by `cert.check P = true` with `cert.isSolvable = false`, then
`Gal(normalClosure ℚ K Ω/ℚ)` is not solvable. -/
theorem not_isSolvable_gal_normalClosure_of_check_eq_true [IsAlgClosed Ω]
    [Algebra.IsAlgebraic ℚ K] {α : Ω} (hα : α ∈ K) {P : ℤ[X]} (hP : P.Monic)
    (hroot : aeval α P = 0) {cert : SolvabilityCertificate} (hcheck : cert.check P = true)
    (hns : cert.isSolvable = false) :
    ¬ Group.IsSolvable Gal(normalClosure ℚ K Ω/ℚ) := by
  refine not_isSolvable_gal_normalClosure_of_mem (fun _ ↦ IsAlgClosed.splits _) hα ?_
  rw [check_minpoly_eq_map_rat_of_isSolvable_eq_false hP hroot hcheck hns]
  exact check_not_isSolvable hP hcheck hns

/-- If `α ∈ K` for a finite-dimensional intermediate field `K / ℚ` inside `[IsAlgClosed Ω]` is a
root of a monic polynomial `P : ℤ[X]` irreducible over `ℚ` with `Module.finrank ℚ K ≤ P.natDegree`,
then any certificate `cert` with `cert.check P = true` decides solvability of
`Gal(normalClosure ℚ K Ω/ℚ)`. -/
theorem isSolvable_gal_normalClosure_iff_of_check_eq_true [IsAlgClosed Ω]
    [FiniteDimensional ℚ K] {α : Ω} (hα : α ∈ K) {P : ℤ[X]} (hP : P.Monic)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ))) (hroot : aeval α P = 0)
    (hdeg : Module.finrank ℚ K ≤ P.natDegree) {cert : SolvabilityCertificate}
    (hcheck : cert.check P = true) :
    Group.IsSolvable Gal(normalClosure ℚ K Ω/ℚ) ↔ cert.isSolvable = true := by
  have hmin : minpoly ℚ α = P.map (Int.castRingHom ℚ) :=
    minpoly_eq_map_intCastRingHom_of_aeval_eq_zero hP hirr hroot
  have hα_int : IsIntegral ℚ α :=
    IntermediateField.isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨α, hα⟩ : K))
  have hadj : ℚ⟮α⟯ = K :=
    TauCeti.IntermediateField.adjoin_simple_eq_of_finrank_le_natDegree_minpoly hα
      (by rwa [hmin, hP.natDegree_map])
  rw [isSolvable_gal_normalClosure_iff_of_adjoin_eq hα_int (IsAlgClosed.splits _) hadj, hmin]
  exact check_sound hP hcheck

/-- If `α ∈ K` for a finite-dimensional intermediate field `K / ℚ` is a root of a monic polynomial
`P : ℤ[X]` on which `primeSymmetric d p q t` checks and `Module.finrank ℚ K ≤ d`, then
`ℚ⟮α⟯ = K`. -/
theorem adjoin_simple_eq_of_primeSymmetric [FiniteDimensional ℚ K] {α : Ω} (hα : α ∈ K)
    {P : ℤ[X]} (hP : P.Monic) (hroot : aeval α P = 0) {d p q : ℕ} {t : Multiset ℕ}
    (hcheck : (primeSymmetric d p q t).check P = true) (hdeg : Module.finrank ℚ K ≤ d) :
    ℚ⟮α⟯ = K := by
  have hmin : minpoly ℚ α = P.map (Int.castRingHom ℚ) :=
    check_minpoly_eq_map_rat_of_isSolvable_eq_false hP hroot hcheck
      (isSolvable_primeSymmetric d p q t)
  refine TauCeti.IntermediateField.adjoin_simple_eq_of_finrank_le_natDegree_minpoly hα ?_
  rw [hmin, hP.natDegree_map, check_natDegree_eq_of_primeSymmetric hP hcheck]
  exact hdeg

/-- If `α ∈ K` for a finite-dimensional intermediate field `K / ℚ` inside `[IsAlgClosed Ω]` is a
root of a monic polynomial `P : ℤ[X]` on which `primeSymmetric d p q t` checks and
`Module.finrank ℚ K ≤ d`, then `Nat.card Gal(normalClosure ℚ K Ω/ℚ) = d.factorial`. -/
theorem natCard_gal_normalClosure_of_primeSymmetric [IsAlgClosed Ω]
    [FiniteDimensional ℚ K] {α : Ω} (hα : α ∈ K) {P : ℤ[X]} (hP : P.Monic)
    (hroot : aeval α P = 0) {d p q : ℕ} {t : Multiset ℕ}
    (hcheck : (primeSymmetric d p q t).check P = true) (hdeg : Module.finrank ℚ K ≤ d) :
    Nat.card Gal(normalClosure ℚ K Ω/ℚ) = d.factorial := by
  have hsym := check_hasFullSymmetricGaloisGroup_of_primeSymmetric hP hcheck
  have hα_int : IsIntegral ℚ α :=
    IntermediateField.isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨α, hα⟩ : K))
  have hadj : ℚ⟮α⟯ = K := adjoin_simple_eq_of_primeSymmetric hα hP hroot hcheck hdeg
  have hmin : minpoly ℚ α = P.map (Int.castRingHom ℚ) :=
    check_minpoly_eq_map_rat_of_isSolvable_eq_false hP hroot hcheck
      (isSolvable_primeSymmetric d p q t)
  rw [natCard_gal_normalClosure_eq_of_adjoin_eq hα_int (IsAlgClosed.splits _) hadj, hmin,
    (hasFullSymmetricGaloisGroup_iff_natCard_gal_eq_factorial_natDegree hsym.separable).mp hsym,
    hP.natDegree_map, check_natDegree_eq_of_primeSymmetric hP hcheck]

end NormalClosure

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

/-- The `{5}` + `{1, 1, 1, 2}` Frobenius-cycle certificate `primeLinearQuadratic 5 5 3` checks on
`X ^ 5 - X + 3`. -/
theorem check_primeLinearQuadratic_X_pow_five_sub_X_add_three :
    (primeLinearQuadratic 5 5 3).check (X ^ 5 - X + 3) = true := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hgood5 : IsGoodPrime (X ^ 5 - X + 3) 5 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  have hgood3 : IsGoodPrime (X ^ 5 - X + 3) 3 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  rw [check_eq_true_iff, verifies_primeLinearQuadratic_iff]
  refine ⟨Nat.prime_five, le_rfl,
    HasFactorDegrees.mk hgood5 factorDegrees_X_pow_five_sub_X_add_three_five,
    HasFactorDegrees.mk hgood3 ?_⟩
  rw [factorDegrees_X_pow_five_sub_X_add_three_three]
  decide

end SolvabilityCertificate

end TauCeti
