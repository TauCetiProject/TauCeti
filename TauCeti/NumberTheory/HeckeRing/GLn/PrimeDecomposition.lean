/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.CoprimeMul
-- supplies the `NonAssocRing (IntegralHeckeRing n)` instance used by `pLocalSubring` below;
-- `CoprimeMul` no longer re-exports it
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution

import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime decomposition of diagonal Hecke operators

The `p`-adic decomposition of the diagonal Hecke operators: every `T(a₁,...,aₙ)` splits off
its `p`-power part, `T(a) = T(p-part) · T(p-free part)`, by the coprime product theorem, and
the `p`-power operators generate the `p`-local Hecke subring `R_p` (Shimura's `R_p`).

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PrimeDecomposition.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GLn.ppowDiag`: the `p`-power diagonal `i ↦ p ^ e i`.
* `HeckeRing.GLn.pComponent`: the entrywise `p`-adic valuation of a diagonal.
* `HeckeRing.GLn.removePrime`: the entrywise `p`-free part of a diagonal.
* `HeckeRing.GLn.pLocalSubring`: the `p`-local Hecke subring `R_p`.

## Main results

* `HeckeRing.GLn.diagElem_split_prime`: `T(a) = T(p-part) · T(p-free part)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2.
-/

public section

open Matrix HeckeRing DoubleCoset Finset

namespace HeckeRing.GLn

variable (n : ℕ)

section PPow

/-- The `p`-power diagonal: entries are `p ^ e i`. -/
def ppowDiag (p : ℕ) (e : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ p ^ e i

/-- Defining equation for the sealed definition `ppowDiag`. -/
@[simp]
lemma ppowDiag_apply (p : ℕ) (e : Fin n → ℕ) (i : Fin n) :
    ppowDiag n p e i = p ^ e i := (rfl)

lemma ppowDiag_pos (p : ℕ) (hp : 0 < p) (e : Fin n → ℕ) :
    ∀ i, 0 < ppowDiag n p e i :=
  fun _ ↦ pow_pos hp _

/-- Monotone exponents give a divisibility chain of `p`-power diagonals. -/
lemma isDvdChain_ppowDiag (p : ℕ) (e : Fin n → ℕ) (hmono : Monotone e) :
    IsDvdChain (ppowDiag n p e) :=
  isDvdChain_iff.mpr fun _ _ hij ↦ Nat.pow_dvd_pow p (hmono hij)

/-- The entrywise `p`-adic valuation of a diagonal. -/
def pComponent (p : ℕ) (a : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ (a i).factorization p

/-- Defining equation for the sealed `pComponent`. -/
@[simp]
lemma pComponent_apply (p : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    pComponent n p a i = (a i).factorization p := (rfl)

/-- The `p`-component of a divisibility chain is monotone. -/
lemma pComponent_monotone (a : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (ha : IsDvdChain a) (p : ℕ) :
    Monotone (pComponent n p a) := fun i j hij ↦
  (Nat.factorization_le_iff_dvd (ha_pos i).ne' (ha_pos j).ne').mpr
    (isDvdChain_iff.mp ha hij) p

end PPow

section RemovePrime

/-- The entrywise `p`-free part of a diagonal: `a i ↦ a i / p ^ (v_p (a i))`. -/
noncomputable def removePrime (p : ℕ) (a : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ ordCompl[p] (a i)

/-- Defining equation for the sealed `removePrime`. -/
@[simp]
lemma removePrime_apply (p : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    removePrime n p a i = ordCompl[p] (a i) := (rfl)

lemma removePrime_pos (p : ℕ) (a : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) :
    ∀ i, 0 < removePrime n p a i :=
  fun i ↦ Nat.ordCompl_pos p (ha_pos i).ne'

/-- The `p`-free part preserves divisibility chains. -/
lemma isDvdChain_removePrime (p : ℕ) (a : Fin n → ℕ) (ha : IsDvdChain a) :
    IsDvdChain (removePrime n p a) := by
  exact isDvdChain_iff.mpr fun i j hij ↦
    Nat.ordCompl_dvd_ordCompl_of_dvd (isDvdChain_iff.mp ha hij) p

/-- The pointwise product of the `p`-part and the `p`-free part recovers the diagonal. -/
@[simp]
lemma ppowDiag_mul_removePrime (p : ℕ) (a : Fin n → ℕ) :
    ppowDiag n p (pComponent n p a) * removePrime n p a = a :=
  funext fun i ↦ Nat.ordProj_mul_ordCompl_eq_self (a i) p

/-- The determinant of a `p`-power diagonal is a power of `p`. -/
@[simp]
lemma prod_ppowDiag (p : ℕ) (e : Fin n → ℕ) :
    ∏ i, ppowDiag n p e i = p ^ (∑ i, e i) := by
  simp [ppowDiag, Finset.prod_pow_eq_pow_sum]

/-- The `p`-part and `p`-free-part determinants are coprime. -/
lemma coprime_prod_ppowDiag_removePrime (p : ℕ) (hp : p.Prime)
    (a : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) :
    Nat.Coprime (∏ i, ppowDiag n p (pComponent n p a) i) (∏ i, removePrime n p a i) := by
  rw [prod_ppowDiag]
  exact (Nat.Coprime.prod_right fun i _ ↦ Nat.coprime_ordCompl hp (ha_pos i).ne').pow_left _

end RemovePrime

variable [NeZero n]

/-- **Binary prime splitting** (Shimura, §3.2): every diagonal Hecke operator factors into
its `p`-power component and its `p`-free component, for any prime `p`. -/
theorem diagElem_split_prime (a : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) (p : ℕ)
    (hp : p.Prime) :
    diagElem a =
      diagElem (ppowDiag n p (pComponent n p a)) * diagElem (removePrime n p a) := by
  conv_lhs => rw [← ppowDiag_mul_removePrime n p a]
  exact (diagElem_mul_of_coprime n _ _ (ppowDiag_pos n p hp.pos _) (removePrime_pos n p a ha_pos)
    (coprime_prod_ppowDiag_removePrime n p hp a ha_pos)).symm

/-- The `p`-local Hecke subring `R_p`: generated by the diagonal Hecke operators with
`p`-power entries (Shimura's `R_p`). -/
noncomputable def pLocalSubring (p : ℕ) : Subring (IntegralHeckeRing n) :=
  Subring.closure
    {f | ∃ (e : Fin n → ℕ) (_ : Monotone e), f = diagElem (ppowDiag n p e)}

/-- Defining equation for the sealed definition `pLocalSubring`. -/
lemma pLocalSubring_def (p : ℕ) :
    pLocalSubring n p = Subring.closure
      {f | ∃ (e : Fin n → ℕ) (_ : Monotone e), f = diagElem (ppowDiag n p e)} := (rfl)

/-- A diagonal Hecke operator with `p`-power entries lies in `R_p`. -/
lemma diagElem_ppowDiag_mem_pLocalSubring (p : ℕ) (e : Fin n → ℕ)
    (hmono : Monotone e) : diagElem (ppowDiag n p e) ∈ pLocalSubring n p :=
  Subring.subset_closure ⟨e, hmono, rfl⟩

end HeckeRing.GLn
