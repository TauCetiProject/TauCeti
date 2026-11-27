/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import TauCeti.RingTheory.WittVector.PadicConstants

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Scalar Artin–Schreier–Witt equations

Let `k` be a perfect ring of characteristic `p` that is absolutely integrally closed: every monic
polynomial of positive degree over `k` has a root in `k` (`TauCeti.IsAbsolutelyIntegrallyClosed`).
Examples are algebraically closed fields of characteristic `p` and the tilt `O_C♭` of the valuation
ring of a complete algebraically closed nonarchimedean field `C`
(`PreTilt.instIsAbsolutelyIntegrallyClosed`). Then every equation `φ(y) - s * y = a` has a
solution in `W(k)` and modulo every power of `p`; for `k = O_C♭` and `s = ξ ^ n` this solves
`φ(c) - ξ ^ n * c = x` in `A_inf = W(O_C♭)`. Over a perfect domain the kernel of `φ - 1` at finite
level is the canonical copy of `ℤ/p^n`. These are the scalar equations used in integral Frobenius
descent.

## Provenance

`WittVector.surjective_map_sub_mul_map` and `WittVector.surjective_frobenius_sub_mul` are
adapted from `New.Period.Witt.exists_map_sub_mul_map_eq` and
`New.Period.Witt.artin_schreier_witt` (file `src/Lib/PadicHodge/PeriodRings/Ainf.lean`)
in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC). The lifting proof uses Mathlib's adic surjectivity criterion;
the finite-level exact sequence is developed here using the canonical p-adic constants.
The generalisation to absolutely integrally closed perfect rings follows grh-lean: the
polynomial-root step follows `New.Variety.IsAbsIntegrallyClosed.exists_pow_sub_mul_eq`
(file `src/Lib/General/Algebra/AbsIntegrallyClosed.lean`), taking the root from
`TauCeti.IsAbsolutelyIntegrallyClosed.exists_root`. The application to `φ(c) - ξ ^ n * c = x` in
`A_inf` follows `New.Period.Ainf.exists_frobEnd_sub_xi_pow_mul_eq` (file
`src/Lib/PadicHodge/PeriodRings/Ainf.lean`).

## References

* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry* (2020),
  Theorem 12.3.4 and its proof, for the integral Frobenius descent application.
-/

public section

noncomputable section

open scoped Polynomial

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

/-- Over a perfect ring of characteristic `p`, the map `b ↦ W(F) b - s * W(G) b` is surjective
on `W(k)` whenever `x ↦ F x - s₀ * G x` is surjective on `k`, where `s₀` is the constant
coefficient of `s`. -/
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

/-- Every scalar Artin–Schreier–Witt equation `φ(y) - s * y = a` is solvable over a perfect
ring of characteristic `p` in which every monic polynomial of positive degree has a root, for
instance an algebraically closed field or the tilt `O_C♭`. -/
theorem surjective_frobenius_sub_mul [TauCeti.IsAbsolutelyIntegrallyClosed k]
    (s : WittVector p k) :
    Function.Surjective fun y : WittVector p k ↦ frobenius y - s * y := by
  classical
  -- over the zero ring every Witt vector is zero
  cases subsingleton_or_nontrivial k
  · exact fun a ↦ ⟨a, WittVector.ext fun _ ↦ Subsingleton.elim _ _⟩
  rw [frobenius_eq_map_frobenius]
  apply surjective_map_sub_mul_map s (_root_.frobenius k p) (RingHom.id k)
  intro a
  -- a root of the monic polynomial `X ^ p - s₀ X - a` of degree `p` solves the equation mod `p`
  let P : k[X] := Polynomial.X ^ p - (Polynomial.C (constantCoeff s) * Polynomial.X +
    Polynomial.C a)
  have hP : P.IsMonicOfDegree p :=
    (Polynomial.isMonicOfDegree_X_pow k p).sub
      (Polynomial.natDegree_linear_le.trans_lt (Fact.out : p.Prime).one_lt)
  obtain ⟨x, hx⟩ := TauCeti.IsAbsolutelyIntegrallyClosed.exists_root P hP.monic
    (hP.natDegree_eq ▸ (Fact.out : p.Prime).pos)
  exact ⟨x, by
    simpa [P, Polynomial.IsRoot, frobenius_def, sub_eq_zero, sub_add_eq_sub_sub] using hx⟩

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
      rwa [frobeniusMod_mk, mk_eq_mk_iff_forall_coeff_eq] at hx
    let y : W := mk p (fun i ↦ if i < n then x.coeff i else 0)
    have hy : frobenius y = y := by
      rw [frobenius_eq_self_iff_forall_coeff]
      intro i
      by_cases hi : i < n
      · simpa [y, hi, coeff_frobenius_charP] using hcoeff i hi
      · simp [y, hi, (Fact.out : p.Prime).ne_zero]
    obtain ⟨z, hz⟩ := frobenius_eq_self_iff.mp hy
    refine ⟨PadicInt.toZModPow n z, ?_⟩
    rw [constantsMod_toZModPow, hz, mk_eq_mk_iff_forall_coeff_eq]
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

/-- Over a perfect ring of characteristic `p` in which every monic polynomial of positive degree
has a root, every scalar equation remains solvable after reduction modulo any power of `p`. -/
theorem surjective_frobeniusMod_sub_mul {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
    [TauCeti.IsAbsolutelyIntegrallyClosed k]
    (n : ℕ) (s : _root_.WittVector p k ⧸ Ideal.span {(p : _root_.WittVector p k) ^ n}) :
    Function.Surjective fun y ↦ frobeniusMod p k n y - s * y := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, hy⟩ := _root_.WittVector.surjective_frobenius_sub_mul s a
  exact ⟨Ideal.Quotient.mk _ y, by simp [← map_mul, ← map_sub, hy]⟩

end WittVector

namespace TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime]

/-- Over a perfect ring of characteristic `p` in which every monic polynomial of positive degree
has a root, the finite Artin–Schreier–Witt operator is surjective. Over an algebraically closed
field this completes `0 → ℤ/p^n → W(k)/p^n → W(k)/p^n → 0`. -/
theorem artinSchreierMod_surjective {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
    [IsAbsolutelyIntegrallyClosed k] (n : ℕ) :
    Function.Surjective (artinSchreierMod (p := p) (k := k) n) := by
  intro a
  obtain ⟨y, hy⟩ := _root_.WittVector.surjective_frobeniusMod_sub_mul (p := p) (k := k) n 1 a
  exact ⟨y, by simpa only [artinSchreierMod_apply, one_mul] using hy⟩

end TauCeti.WittVector
