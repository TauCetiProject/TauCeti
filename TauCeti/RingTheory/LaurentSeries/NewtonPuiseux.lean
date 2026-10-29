/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.LaurentSeries.SlopeNormalization
import TauCeti.RingTheory.PowerSeries.Hensel

/-!
# The Newton–Puiseux theorem over a Laurent-series field

Let `K` be an algebraically closed field of characteristic zero. This file proves that every
nonconstant polynomial `P` over `K⸨X⸩` has a root after a finite ramification `X ↦ X ^ n`: there
are `n > 0` and `y ∈ K⸨X⸩` with `P(X ^ n)(y) = 0`, where `P(X ^ n)` applies `LaurentSeries.expand`
to the coefficients of `P`. Equivalently, `P` has a root in the level-`n` copy `K⸨t ^ (1 / n)⸩`
of the Puiseux series field.

The proof is the classical Newton–Puiseux algorithm, by induction on the degree `m` of `P`,
which may be assumed monic.

1. Translating the variable by `-a / m`, where `a` is the coefficient of `Y ^ (m - 1)`, removes
   that coefficient (`Polynomial.nextCoeff_taylor`).
2. If the translated polynomial is `Y ^ m`, then `0` is a root. Otherwise choose the smallest
   slope `ord (P.coeff j) / (m - j)` over the nonzero coefficients with `j < m`, attained at
   `j₀`, and put `q = m - j₀` and `v = ord (P.coeff j₀)`. Ramifying `X ↦ X ^ q` and rescaling
   `Y ↦ X ^ v * Y`, then dividing by `X ^ (v * m)`, produces a monic polynomial over `K⟦X⟧`
   (`Polynomial.Monic.exists_map_expand_eq_scaleRoots_of_nextCoeff_eq_zero`). Its reduction
   modulo `X` still has no term of degree `m - 1`, and its coefficient of `Y ^ j₀` is nonzero, so
   the reduction is not `Y ^ m`.
3. In characteristic zero such a reduction is not a power `(Y - b) ^ m`, so it splits into
   coprime monic factors of positive degree, and Hensel's lemma lifts this splitting to the
   rescaled polynomial (`Polynomial.Monic.exists_monic_mul_eq_of_nextCoeff_map_eq_zero`).
4. By induction the factor of degree `r` has a root after some ramification `X ↦ X ^ n`. Undoing
   the rescaling and the translation gives a root of `P` after the ramification `X ↦ X ^ (n * q)`.

Through the level embeddings, the root theorem gives a root of `P` in the Puiseux field lying in a
single ramified level. It is the input for the algebraic closedness of the Puiseux field.

## Main results

* `TauCeti.LaurentSeries.exists_isRoot_map_expand`: a nonconstant polynomial over `K⸨X⸩` has a
  root after a finite ramification `X ↦ X ^ n`.
* `TauCeti.puiseuxField.exists_isRoot_map_levelEmbedding`: a nonconstant polynomial over `K⸨X⸩`,
  embedded at any level, has a root in the Puiseux field lying in a single ramified level.

## References

* H. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, arXiv:1304.6770, §1, for the
  proof by Tschirnhaus translation, ramification along the smallest slope, and Hensel splitting.
-/

public section

open HahnSeries
open Polynomial hiding expand coeff_expand_mul
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

open _root_.LaurentSeries

variable {K : Type*} [Field K]

/-- Undoing a rescaling: if the ramification `X ↦ X ^ q` of `P` is the root scaling by `s` of a
monic polynomial `Q`, and `Q` has a root after a further ramification `X ↦ X ^ n`, then `P` has a
root after the ramification `X ↦ X ^ (n * q)`. -/
private theorem exists_isRoot_map_expand_mul {P Q : K⸨X⸩[X]} (hQ : Q.Monic) {q n : ℕ+}
    {s : K⸨X⸩} (hPQ : P.map (expand K q : K⸨X⸩ →+* K⸨X⸩) = Q.scaleRoots s) {y : K⸨X⸩}
    (hy : (Q.map (expand K n)).IsRoot y) :
    ∃ z : K⸨X⸩, (P.map (expand K (n * q))).IsRoot z := by
  have hmap : (P.map (expand K q : K⸨X⸩ →+* K⸨X⸩)).map (expand K n : K⸨X⸩ →+* K⸨X⸩) =
      P.map (expand K (n * q) : K⸨X⸩ →+* K⸨X⸩) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun f ↦ expand_expand n q f
  refine ⟨expand K n s * y, ?_⟩
  rw [← hmap, hPQ, map_scaleRoots _ _ _ (by simp [hQ.leadingCoeff]), IsRoot, RingHom.coe_coe,
    scaleRoots_eval_mul, hy.eq_zero, mul_zero]

variable [IsAlgClosed K] [CharZero K]

/-- The monic case of `exists_isRoot_map_expand`, by strong induction on the degree. -/
private theorem exists_isRoot_map_expand_of_monic (m : ℕ) :
    ∀ P : K⸨X⸩[X], P.Monic → P.natDegree = m → 0 < m →
      ∃ (n : ℕ+) (y : K⸨X⸩), (P.map (expand K n)).IsRoot y := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P hP hPm hm
  have : CharZero K⸨X⸩ := charZero_of_injective_algebraMap (algebraMap K K⸨X⸩).injective
  have hm' : (m : K⸨X⸩) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  -- Translate the variable to remove the term of degree `m - 1`.
  set c := -(P.nextCoeff / m)
  set P₁ := taylor c P
  have hP₁ : P₁.Monic := by rw [Monic, leadingCoeff_taylor, hP.leadingCoeff]
  have hP₁m : P₁.natDegree = m := by rw [natDegree_taylor, hPm]
  have hnext : P₁.nextCoeff = 0 := by
    rw [nextCoeff_taylor, hPm, hP.leadingCoeff, mul_one, mul_neg, mul_div_cancel₀ _ hm',
      add_neg_cancel]
  suffices ∃ (n : ℕ+) (y : K⸨X⸩), (P₁.map (expand K n)).IsRoot y by
    obtain ⟨n, y, hy⟩ := this
    refine ⟨n, y + expand K n c, ?_⟩
    rwa [IsRoot, map_taylor, taylor_eval, RingHom.coe_coe] at hy
  by_cases hX : P₁ = X ^ m
  · exact ⟨1, 0, by simp [hX, hm.ne']⟩
  -- Ramify and rescale to a monic polynomial over `K⟦X⟧` whose reduction is not `Y ^ m`, and
  -- split off a monic factor `G` of smaller positive degree.
  obtain ⟨q, v, Q, hQ, hQm, hPQ, hQnext, hQX⟩ :=
    hP₁.exists_map_expand_eq_scaleRoots_of_nextCoeff_eq_zero hnext (hP₁m ▸ hX)
  rw [hP₁m] at hQm
  obtain ⟨G, H, hG, hH, hGH, hG0, hH0⟩ := hQ.exists_monic_mul_eq_of_nextCoeff_map_eq_zero
    (IsAlgClosed.splits _) (by rw [hQm]; exact_mod_cast hm.ne') hQnext hQX
  have hGm : G.natDegree < m := by
    rw [← hQm, ← hGH, hG.natDegree_mul hH]
    omega
  -- By induction, `G` has a root after a ramification `X ↦ X ^ n`, hence so does the rescaled
  -- polynomial.
  obtain ⟨n, y, hy⟩ := ih _ hGm (G.map (ofPowerSeries ℤ K)) (hG.map _)
    (hG.natDegree_map _) hG0
  obtain ⟨z, hz⟩ := exists_isRoot_map_expand_mul (hQ.map _) hPQ (n := n) (y := y) (by
    rw [← hGH, Polynomial.map_mul, Polynomial.map_mul, IsRoot, eval_mul, hy.eq_zero, zero_mul])
  exact ⟨n * q, z, hz⟩

/-- **Newton–Puiseux theorem.** Over an algebraically closed field `K` of characteristic zero,
every nonconstant polynomial `P` over `K⸨X⸩` has a root after a finite ramification: for some
`n > 0`, the polynomial `P(X ^ n)` obtained by substituting `X ↦ X ^ n` in its coefficients has a
root in `K⸨X⸩`. -/
theorem exists_isRoot_map_expand {P : K⸨X⸩[X]} (hP : P.degree ≠ 0) :
    ∃ (n : ℕ+) (y : K⸨X⸩), (P.map (expand K n)).IsRoot y := by
  rcases eq_or_ne P 0 with rfl | hP0
  · exact ⟨1, 0, by simp⟩
  have hc : P.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 hP0)
  have hdeg : 0 < (P * C P.leadingCoeff⁻¹).natDegree := by
    rw [natDegree_mul_C hc, natDegree_pos_iff_degree_pos]
    exact (zero_le_degree_iff.2 hP0).lt_of_ne' hP
  obtain ⟨n, y, hy⟩ := exists_isRoot_map_expand_of_monic _ _ (monic_mul_leadingCoeff_inv hP0)
    rfl hdeg
  refine ⟨n, y, ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_C, IsRoot, eval_mul, eval_C, mul_eq_zero] at hy
  exact hy.resolve_right (by simpa using hc)

end TauCeti.LaurentSeries

namespace TauCeti.puiseuxField

open _root_.LaurentSeries

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- Over an algebraically closed field `K` of characteristic zero, the image of a nonconstant
polynomial over `K⸨X⸩` under the level-`n` embedding `X ↦ t ^ (1 / n)` has a root in the Puiseux
field lying in a single level `n * m`. For `n = 1` the image is the polynomial over the Puiseux
field obtained through the `K⸨X⸩`-algebra structure. -/
theorem exists_isRoot_map_levelEmbedding (n : ℕ+) {P : K⸨X⸩[X]} (hP : P.degree ≠ 0) :
    ∃ (m : ℕ+) (y : K⸨X⸩),
      (P.map (levelEmbedding K n : K⸨X⸩ →+* puiseuxField K)).IsRoot
        (levelEmbedding K (n * m) y) := by
  obtain ⟨m, y, hy⟩ := LaurentSeries.exists_isRoot_map_expand hP
  refine ⟨m, y, ?_⟩
  have hmap : P.map (levelEmbedding K n : K⸨X⸩ →+* puiseuxField K) =
      (P.map (expand K m : K⸨X⸩ →+* K⸨X⸩)).map
        (levelEmbedding K (n * m) : K⸨X⸩ →+* puiseuxField K) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun f ↦ (levelEmbedding_expand n m f).symm
  rw [hmap]
  exact hy.map _

end TauCeti.puiseuxField
