/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Polynomial.Homogenize

import TauCeti.RingTheory.Polynomial.Radical

/-!
# Square-free divisors of integer binary forms

Let `F ∈ ℤ[X₀, X₁]` be a binary form and let `L` be an algebraically closed field of
characteristic zero. If `F(X, 1)` has `r` distinct zeros in `L`, then `F` has a divisor
`G ∈ ℤ[X₀, X₁]` which is a binary form of degree `r` without squared linear factors over `L`:
the homogenization of the radical of `F(X, 1)` in `ℤ[X]`.

Results on binary forms without squared linear factors, such as the Thue–Roth inequality
`MvPolynomial.IsHomogeneous.exists_pos_mul_max_abs_rpow_le_abs_eval`, thus apply to a divisor of
an arbitrary integer binary form. If `F(X, 1)` has at least three distinct complex zeros, the
divisor has degree at least `3`; since `G(x, y)` divides `F(x, y)`, solutions of the Thue equation
`F(x, y) = m ≠ 0` are solutions of `G(x, y) = m'` for one of the finitely many divisors `m'`
of `m`.

## Main results

* `MvPolynomial.IsHomogeneous.exists_dvd_isHomogeneous_not_sq_dvd`: an integer binary form has
  a divisor which is a binary form without squared linear factors over `L`, of degree the number
  of distinct zeros of `F(X, 1)` in `L`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Corollary 6.4.
-/

public section

open Polynomial UniqueFactorizationMonoid

namespace MvPolynomial

/-- **Square-free divisors of integer binary forms** (Evertse, proof of Corollary 6.4). Let
`F ∈ ℤ[X₀, X₁]` be a binary form and `L` an algebraically closed field of characteristic zero.
Then `F` is divisible by a binary form `G ∈ ℤ[X₀, X₁]` whose degree is the number of distinct
zeros of `F(X, 1)` in `L`, and which has no squared linear factor `(a X₀ + b X₁) ^ 2` over `L`. -/
theorem IsHomogeneous.exists_dvd_isHomogeneous_not_sq_dvd {F : MvPolynomial (Fin 2) ℤ} {d : ℕ}
    (hF : F.IsHomogeneous d) (L : Type*) [Field L] [CharZero L] [IsAlgClosed L]
    [DecidableEq L] :
    ∃ G : MvPolynomial (Fin 2) ℤ, G ∣ F ∧
      G.IsHomogeneous ((MvPolynomial.aeval ![Polynomial.X, 1] F : ℤ[X]).map
        (Int.castRingHom L)).roots.toFinset.card ∧
      ∀ a b : L, (a, b) ≠ (0, 0) → ¬(C a * X 0 + C b * X 1) ^ 2 ∣ G.map (Int.castRingHom L) := by
  set f : ℤ[X] := MvPolynomial.aeval ![Polynomial.X, 1] F
  set φ := Int.castRingHom L
  have hfd : f.natDegree ≤ d := hF.natDegree_aeval_le fun i ↦ by fin_cases i <;> simp
  have hFf : f.homogenize d = F := homogenize_eq_of_isHomogeneous hF rfl
  -- The radical `g` of `f` in `ℤ[X]` divides `f`, and is separable over `ℚ`, hence over `L`.
  set g : ℤ[X] := radical f
  have hgf : g ∣ f := radical_dvd_self
  have hsep : (g.map φ).Separable := separable_map_radical ℚ L f
  have hdeg : (g.map φ).natDegree = g.natDegree :=
    natDegree_map_eq_of_injective (RingHom.injective_int φ) g
  -- `f` and `g` have the same zeros in `L`, as `g ∣ f ∣ g ^ n`.
  have hroots : (g.map φ).roots.toFinset = (f.map φ).roots.toFinset :=
    roots_toFinset_map_radical φ f
  have hcard : g.natDegree = ((f.map φ).roots.toFinset).card := by
    rw [← hroots, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hdeg]
  refine ⟨g.homogenize g.natDegree, ?_, hcard ▸ isHomogeneous_homogenize g, fun a b _ ↦ ?_⟩
  · rw [← hFf, homogenize_eq_X_pow_mul_homogenize_natDegree hfd]
    exact (homogenize_dvd hgf).mul_left _
  · rw [← homogenize_map, ← hdeg]
    exact (PerfectField.separable_iff_squarefree.1 hsep).not_sq_dvd_homogenize_natDegree

end MvPolynomial
