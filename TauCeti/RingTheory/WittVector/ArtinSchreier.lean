/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.WittVector.PadicConstants

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Scalar Artin–Schreier–Witt equations

Over an algebraically closed field of characteristic `p`, every equation `φ(y) - s * y = a`
has a solution in the full Witt ring and modulo every power of `p`. At finite level the kernel
of `φ - 1` is the canonical copy of `ℤ/p^n`. These are the scalar equations used in integral
Frobenius descent.

## Provenance

`WittVector.surjective_map_sub_mul_map` and `WittVector.surjective_frobenius_sub_mul` are
adapted from `New.Period.Witt.exists_map_sub_mul_map_eq` and
`New.Period.Witt.artin_schreier_witt` (file `src/Lib/PadicHodge/PeriodRings/Ainf.lean`)
in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC). The lifting proof uses Mathlib's adic surjectivity criterion;
the finite-level exact sequence is developed here using the canonical p-adic constants.
The polynomial-root step also follows `New.Variety.IsAbsIntegrallyClosed.exists_pow_sub_mul_eq`
(file `src/Lib/General/Algebra/AbsIntegrallyClosed.lean`), using native algebraic closedness.

## References

* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry* (2020),
  Theorem 12.3.4 and its proof, for the integral Frobenius descent application.
-/

public section

noncomputable section

open scoped Polynomial

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

/-- An additive equation between two Witt maps over a perfect ring is solvable whenever its
reduction modulo `p` is solvable. -/
theorem surjective_map_sub_mul_map (s : WittVector p k) (F G : k →+* k)
    (h : Function.Surjective fun x ↦ F x - constantCoeff s * G x) :
    Function.Surjective fun b : WittVector p k ↦ map F b - s * map G b := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI : I.map (algebraMap ℤ (WittVector p k)) = Ideal.span {(p : WittVector p k)} := by
    simp [I, Ideal.map_span]
  have : IsAdicComplete I (WittVector p k) :=
    (IsAdicComplete.map_algebraMap_iff (R := ℤ) (S := WittVector p k) I (WittVector p k)).mp
      (hI ▸ inferInstance)
  let f : WittVector p k →ₗ[ℤ] WittVector p k :=
    ((map F).toAddMonoidHom -
      (AddMonoidHom.mulLeft s).comp (map G).toAddMonoidHom).toIntLinearMap
  apply surjective_of_mkQ_comp_surjective (I := I) (f := f)
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • ⊤) y
  obtain ⟨t, ht⟩ := h (constantCoeff x)
  refine ⟨teichmuller p t, ?_⟩
  apply (Submodule.Quotient.eq _).2
  rw [Ideal.smul_top_eq_map, hI]
  simp only [Submodule.restrictScalars_mem]
  rw [← ker_constantCoeff, RingHom.mem_ker]
  simpa [f, map_sub, map_mul, sub_eq_zero] using ht

section Field

variable {K : Type*} [Field K] [CharP K p] [IsAlgClosed K]

/-- Every scalar Artin–Schreier–Witt equation over an algebraically closed field is solvable. -/
theorem surjective_frobenius_sub_mul (s : WittVector p K) :
    Function.Surjective fun y : WittVector p K ↦ frobenius y - s * y := by
  classical
  rw [frobenius_eq_map_frobenius]
  apply surjective_map_sub_mul_map s (_root_.frobenius K p) (RingHom.id K)
  intro a
  let P : K[X] := Polynomial.X ^ p - (Polynomial.C (constantCoeff s) * Polynomial.X +
    Polynomial.C a)
  have hP : P.IsMonicOfDegree p :=
    (Polynomial.isMonicOfDegree_X_pow K p).sub
      (Polynomial.natDegree_linear_le.trans_lt (Fact.out : p.Prime).one_lt)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P
    (Polynomial.natDegree_pos_iff_degree_pos.mp
      ((Fact.out : p.Prime).pos.trans_eq hP.natDegree_eq.symm)).ne'
  exact ⟨x, by
    simpa [P, Polynomial.IsRoot, frobenius_def, sub_eq_zero, sub_add_eq_sub_sub] using hx⟩

end Field

end WittVector

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k]

local notation "W" => _root_.WittVector p k

/-- The additive Artin–Schreier–Witt operator `φ - 1` on `W(k)/p^n`. -/
def artinSchreierMod (n : ℕ) :
    W ⧸ Ideal.span {(p : W) ^ n} →+ W ⧸ Ideal.span {(p : W) ^ n} :=
  (frobeniusMod p k n).toAddMonoidHom - AddMonoidHom.id _

/-- The finite Artin–Schreier–Witt operator is Frobenius minus the identity. -/
@[simp]
theorem artinSchreierMod_apply (n : ℕ) (x : W ⧸ Ideal.span {(p : W) ^ n}) :
    artinSchreierMod (p := p) (k := k) n x = frobeniusMod p k n x - x := (rfl)

variable {p k} [CharP k p] [PerfectRing k p]

/-- In a perfect domain, every Frobenius-fixed class modulo `p^n` is a finite constant. -/
theorem frobeniusMod_eq_self_iff [IsDomain k] (n : ℕ)
    (x : W ⧸ Ideal.span {(p : W) ^ n}) :
    frobeniusMod p k n x = x ↔ x ∈ Set.range (constantsMod p k n) := by
  constructor
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    intro hx
    have hcoeff : ∀ i < n, (frobenius x).coeff i = x.coeff i := by
      rw [frobeniusMod_mk, Ideal.Quotient.eq, mem_span_p_pow_iff_le_coeff_eq_zero,
        ← le_coeff_eq_iff_le_sub_coeff_eq_zero] at hx
      exact hx
    let y : W := mk p (fun i ↦ if i < n then x.coeff i else 0)
    have hy : frobenius y = y := by
      rw [frobenius_eq_self_iff_forall_coeff]
      intro i
      by_cases hi : i < n
      · simpa [y, hi, coeff_frobenius_charP] using hcoeff i hi
      · simp [y, hi, (Fact.out : p.Prime).ne_zero]
    obtain ⟨z, hz⟩ := frobenius_eq_self_iff.mp hy
    refine ⟨PadicInt.toZModPow n z, ?_⟩
    rw [constantsMod_toZModPow, hz, Ideal.Quotient.eq,
      mem_span_p_pow_iff_le_coeff_eq_zero, ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    simp [y, hi]
  · rintro ⟨z, rfl⟩
    exact frobeniusMod_constantsMod p k n z

/-- The finite Artin–Schreier–Witt sequence is exact at `W(k)/p^n` over a perfect domain. -/
theorem exact_constantsMod_artinSchreierMod [IsDomain k] (n : ℕ) :
    Function.Exact (constantsMod p k n) (artinSchreierMod (p := p) (k := k) n) := by
  intro x
  simpa only [artinSchreierMod_apply, sub_eq_zero] using frobeniusMod_eq_self_iff n x

end TauCeti.WittVector

namespace WittVector

open TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime]

/-- Every scalar equation remains solvable after reduction modulo any power of `p`. -/
theorem surjective_frobeniusMod_sub_mul {K : Type*} [Field K] [CharP K p] [IsAlgClosed K]
    (n : ℕ) (s : _root_.WittVector p K ⧸ Ideal.span {(p : _root_.WittVector p K) ^ n}) :
    Function.Surjective fun y ↦ frobeniusMod p K n y - s * y := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, hy⟩ := _root_.WittVector.surjective_frobenius_sub_mul s a
  exact ⟨Ideal.Quotient.mk _ y, by simp [← map_mul, ← map_sub, hy]⟩

end WittVector

namespace TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime]

/-- Over an algebraically closed field the finite Artin–Schreier–Witt operator is surjective,
completing `0 → ℤ/p^n → W(k)/p^n → W(k)/p^n → 0`. -/
theorem artinSchreierMod_surjective {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] (n : ℕ) :
    Function.Surjective (artinSchreierMod (p := p) (k := K) n) := by
  intro a
  obtain ⟨y, hy⟩ := _root_.WittVector.surjective_frobeniusMod_sub_mul (p := p) (K := K) n 1 a
  exact ⟨y, by simpa only [artinSchreierMod_apply, one_mul] using hy⟩

end TauCeti.WittVector
