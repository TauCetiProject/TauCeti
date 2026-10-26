/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Analysis.Normed.Group.Int

/-!
# Irreducibility from a single root outside the open unit disc

A nonconstant monic integer polynomial with nonzero constant coefficient has a complex root
of norm at least one: otherwise the product of its root norms would be less than one, while
the norm of its constant coefficient is at least one.

Consequently, if exactly one complex root of a monic integer polynomial with nonzero constant
coefficient lies outside the open unit disc, counted with multiplicity, the polynomial is
irreducible. Every nonconstant monic factor would contribute an outer root, and multiplicities
add under multiplication. This is the algebraic step shared by the strict and equality forms
of Perron's criterion.

## References

* V. V. Prasolov, *Polynomials* (Russian edition, 2003), Chapter 2, §7.2, Theorem 7.2(a),
  integral-factor argument, pp. 68–69.
-/

public section

namespace Polynomial

/-- A nonconstant monic integer polynomial with nonzero constant coefficient has a complex
root outside the open unit disc. -/
theorem Monic.exists_mem_roots_one_le_norm {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 ≠ 0) :
    ∃ z ∈ (f.map (Int.castRingHom ℂ)).roots, 1 ≤ ‖z‖ := by
  classical
  let F := f.map (Int.castRingHom ℂ)
  have hF : F.Monic := hf.map _
  have hFzero : F.coeff 0 ≠ 0 := by simpa [F] using hzero
  have hroots : F.roots ≠ 0 := by
    intro h
    have hcard := IsAlgClosed.card_roots_eq_natDegree (p := F)
    simp only [h, Multiset.card_zero] at hcard
    have hdegF : 0 < F.natDegree := by simpa [F, hf.natDegree_map] using hdeg
    exact (Nat.ne_of_gt hdegF) hcard.symm
  by_contra! h
  have hprod : (F.roots.map fun z ↦ ‖z‖).prod < 1 := by
    have hpos : ∀ z ∈ F.roots, 0 < ‖z‖ := by
      intro z hz
      apply norm_pos_iff.mpr
      intro hz0
      subst z
      exact hFzero (by simpa [IsRoot, coeff_zero_eq_eval_zero] using
        (mem_roots hF.ne_zero).mp hz)
    simpa using Multiset.prod_map_lt_prod_map hroots (fun z ↦ ‖z‖) (fun _ ↦ (1 : ℝ))
      hpos h
  have hconstant := (IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF
  have hnorm : ‖(f.coeff 0 : ℂ)‖ = (F.roots.map fun z ↦ ‖z‖).prod := by
    simpa [F, norm_mul, norm_pow, Multiset.norm_prod] using congrArg norm hconstant
  have hone : (1 : ℝ) ≤ ‖(f.coeff 0 : ℂ)‖ := by
    simpa [Complex.norm_intCast, Int.norm_eq_abs, ← Int.cast_abs] using
      (Int.cast_le (R := ℝ)).mpr (Int.one_le_abs hzero)
  linarith

/-- A monic integer polynomial with nonzero constant coefficient is irreducible if precisely
one complex root lies outside the open unit disc, counted with multiplicity.

The root-count hypothesis already implies positive degree. In particular, this applies to
degree-one polynomials, and counts repeated roots with their full multiplicity. -/
theorem Monic.irreducible_of_card_outer_roots_eq_one {f : ℤ[X]} (hf : f.Monic)
    (hzero : f.coeff 0 ≠ 0)
    (hcount : ((f.map (Int.castRingHom ℂ)).roots.filter fun z ↦ 1 ≤ ‖z‖).card = 1) :
    Irreducible f := by
  classical
  apply hf.irreducible_iff_natDegree.mpr
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp at hcount
  · intro g h hg hh hmul
    by_contra! hdeg
    have hgzero : g.coeff 0 ≠ 0 := by
      intro hg0
      apply hzero
      rw [← hmul, mul_coeff_zero, hg0, zero_mul]
    have hhzero : h.coeff 0 ≠ 0 := by
      intro hh0
      apply hzero
      rw [← hmul, mul_coeff_zero, hh0, mul_zero]
    obtain ⟨z, hz, hznorm⟩ := hg.exists_mem_roots_one_le_norm (Nat.pos_of_ne_zero hdeg.1)
      hgzero
    obtain ⟨w, hw, hwnorm⟩ := hh.exists_mem_roots_one_le_norm (Nat.pos_of_ne_zero hdeg.2)
      hhzero
    have hgcount : 0 < ((g.map (Int.castRingHom ℂ)).roots.filter fun z ↦ 1 ≤ ‖z‖).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨z, Multiset.mem_filter.mpr ⟨hz, hznorm⟩⟩
    have hhcount : 0 < ((h.map (Int.castRingHom ℂ)).roots.filter fun z ↦ 1 ≤ ‖z‖).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨w, Multiset.mem_filter.mpr ⟨hw, hwnorm⟩⟩
    rw [← hmul, Polynomial.map_mul, roots_mul ((hg.map _).mul (hh.map _)).ne_zero,
      Multiset.filter_add, Multiset.card_add] at hcount
    omega

end Polynomial
