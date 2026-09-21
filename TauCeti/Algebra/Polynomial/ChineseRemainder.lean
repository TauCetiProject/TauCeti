/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.FinCases

/-!
# Monic polynomials with prescribed reductions

A finite family of monic polynomials of the same degree, over pairwise coprime residue rings,
lifts simultaneously to a monic integer polynomial of that degree. In particular, one can
prescribe reductions modulo 2, 3, and 5 independently. This is the coefficient-gluing step in
the three-prime construction of polynomials with symmetric Galois group.

The Chinese remainder equivalence is Mathlib's `ZMod.prodEquivPi`. The lifted coefficients
are assembled by `TauCeti.Polynomial.monicOfCoeff`, which fixes the leading term to be `X ^ n`.
No primality or nonzero-degree hypothesis is needed.
-/

public section

open Polynomial

namespace TauCeti

/-- Monic polynomials of a common degree over pairwise coprime residue rings have a simultaneous
monic lift to `ℤ` of the same degree. The index type may be empty, and the moduli need not
be prime. -/
theorem exists_monic_int_polynomial_map_zmod_eq {ι : Type*} [Finite ι]
    (m : ι → ℕ) (hcop : Pairwise fun i j ↦ (m i).Coprime (m j)) (n : ℕ)
    (g : (i : ι) → (ZMod (m i))[X]) (hmonic : ∀ i, (g i).Monic)
    (hdegree : ∀ i, (g i).natDegree = n) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree = n ∧
      ∀ i, f.map (Int.castRingHom (ZMod (m i))) = g i := by
  classical
  let := Fintype.ofFinite ι
  have hcoeff (k : ℕ) : ∃ a : ℤ, ∀ i, (a : ZMod (m i)) = (g i).coeff k := by
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective
      ((ZMod.prodEquivPi m hcop).symm (fun i ↦ (g i).coeff k))
    refine ⟨a, ?_⟩
    have h := congrArg (ZMod.prodEquivPi m hcop) ha
    rw [RingEquiv.apply_symm_apply] at h
    simpa only [map_intCast, Pi.intCast_apply] using congrFun h
  choose a ha using hcoeff
  refine ⟨Polynomial.monicOfCoeff (fun k : Fin n ↦ a k),
    Polynomial.monic_monicOfCoeff _, Polynomial.natDegree_monicOfCoeff _, ?_⟩
  intro i
  rcases subsingleton_or_nontrivial (ZMod (m i)) with h | h
  · exact Subsingleton.elim _ _
  rw [Polynomial.map_monicOfCoeff]
  simp only [eq_intCast, ha]
  exact Polynomial.monicOfCoeff_coeff (hmonic i) (hdegree i)

/-- Prescribed monic reductions modulo 2, 3, and 5 lift to one monic integer polynomial of the
same degree. -/
theorem exists_monic_int_polynomial_map_two_three_five_eq (n : ℕ)
    (g2 : (ZMod 2)[X]) (g3 : (ZMod 3)[X]) (g5 : (ZMod 5)[X])
    (h2 : g2.Monic) (h3 : g3.Monic) (h5 : g5.Monic)
    (d2 : g2.natDegree = n) (d3 : g3.natDegree = n) (d5 : g5.natDegree = n) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree = n ∧
      f.map (Int.castRingHom (ZMod 2)) = g2 ∧
      f.map (Int.castRingHom (ZMod 3)) = g3 ∧
      f.map (Int.castRingHom (ZMod 5)) = g5 := by
  let m : Fin 3 → ℕ := ![2, 3, 5]
  let g : (i : Fin 3) → (ZMod (m i))[X] :=
    Fin.cases g2 (Fin.cases g3 (Fin.cases g5 (fun i ↦ Fin.elim0 i)))
  have hcop : Pairwise fun i j ↦ (m i).Coprime (m j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  obtain ⟨f, hf, hd, hg⟩ := exists_monic_int_polynomial_map_zmod_eq m hcop n g
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
  exact ⟨f, hf, hd, hg 0, hg 1, hg 2⟩

end TauCeti
