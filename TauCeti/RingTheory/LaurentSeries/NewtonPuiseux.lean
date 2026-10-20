/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic
import TauCeti.Algebra.Polynomial.LinearFactor
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.LaurentSeries.Basic
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
   (`TauCeti.LaurentSeries.exists_monic_map_eq_scaleRoots_map_expand`). Its reduction modulo `X`
   still has no term of degree `m - 1`, and its coefficient of `Y ^ j₀` is nonzero, so the
   reduction is not `Y ^ m`.
3. In characteristic zero such a reduction is not a power `(Y - b) ^ m`, so at any of its roots
   it splits into coprime monic factors of degrees `0 < r < m`
   (`Polynomial.Monic.exists_eq_X_sub_C_pow_mul_of_nextCoeff_eq_zero`). Hensel's lemma lifts
   this splitting to the rescaled polynomial (`Polynomial.Monic.exists_monic_mul_eq_of_isCoprime`).
4. By induction the factor of degree `r` has a root after some ramification `X ↦ X ^ n`. Undoing
   the rescaling and the translation gives a root of `P` after the ramification `X ↦ X ^ (n * q)`.

The ramification and rescaling step uses only the order of the coefficients, and holds over any
commutative ring. Through the level embeddings, the root theorem gives a root of `P` in the
Puiseux field lying in a single ramified level. It is the input for the algebraic closedness of
the Puiseux field.

## Main results

* `TauCeti.LaurentSeries.exists_monic_map_eq_scaleRoots_map_expand`: ramification and rescaling
  along the smallest slope make a monic polynomial without term of degree `m - 1`, other than
  `Y ^ m`, integral over `R⟦X⟧`, with reduction other than `Y ^ m`.
* `TauCeti.LaurentSeries.exists_isRoot_map_expand`: a nonconstant polynomial over `K⸨X⸩` has a
  root after a finite ramification `X ↦ X ^ n`.
* `TauCeti.puiseuxField.exists_isRoot_levelEmbedding`: a nonconstant polynomial over `K⸨X⸩` has
  a root in the Puiseux field lying in a single ramified level.

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

variable {R : Type*} [CommSemiring R]

/-- A monic polynomial `P` of degree `m`, other than `X ^ m`, has a coefficient `P.coeff j₀ ≠ 0`
with `j₀ < m` attaining the smallest slope `ord (P.coeff j) / (m - j)` among its nonzero
coefficients, stated with denominators cleared. -/
private theorem exists_slope_le {P : R⸨X⸩[X]} (hP : P.Monic) (hX : P ≠ X ^ P.natDegree) :
    ∃ j₀ < P.natDegree, P.coeff j₀ ≠ 0 ∧ ∀ j ≤ P.natDegree, P.coeff j ≠ 0 →
      ((P.natDegree - j : ℕ) : ℤ) * (P.coeff j₀).order ≤
        (P.natDegree - j₀ : ℕ) * (P.coeff j).order := by
  classical
  set m := P.natDegree with hm
  -- The exponents of the nonzero coefficients below the leading one.
  set S := (Finset.range m).filter fun j ↦ P.coeff j ≠ 0
  have hS : S.Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hS
    refine hX (Polynomial.ext fun j ↦ ?_)
    rw [coeff_X_pow]
    rcases lt_trichotomy j m with hj | rfl | hj
    · simpa [hj.ne] using hS (Finset.mem_range.2 hj)
    · rw [hm, hP.coeff_natDegree]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt hj]
      simp [hj.ne']
  obtain ⟨j₀, hj₀, hmin⟩ := S.exists_min_image
    (fun j ↦ ((P.coeff j).order : ℚ) / ((m - j : ℕ) : ℚ)) hS
  rw [Finset.mem_filter, Finset.mem_range] at hj₀
  refine ⟨j₀, hj₀.1, hj₀.2, fun j hj hc ↦ ?_⟩
  rcases hj.lt_or_eq with hj | rfl
  · have := hmin j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hc⟩)
    rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < m - j₀))
      (by exact_mod_cast (by omega : 0 < m - j))] at this
    rw [mul_comm (((m - j : ℕ) : ℤ)), mul_comm (((m - j₀ : ℕ) : ℤ))]
    exact_mod_cast this
  · simp [hm, hP.coeff_natDegree]

/-- Let `P` be a monic polynomial of degree `m` over `R⸨X⸩`, without term of degree `m - 1` and
other than `Y ^ m`. After the ramification `X ↦ X ^ q` and the rescaling
`P(Y) ↦ X ^ (-v * m) * P(X ^ v * Y)` along the smallest slope of `P`, it becomes the image of a
monic polynomial `Q` of degree `m` over `R⟦X⟧`, whose reduction modulo `X` still has no term of
degree `m - 1` and is not `Y ^ m`. -/
theorem exists_monic_map_eq_scaleRoots_map_expand {P : R⸨X⸩[X]} (hP : P.Monic)
    (hnext : P.nextCoeff = 0) (hX : P ≠ X ^ P.natDegree) :
    ∃ (q : ℕ+) (v : ℤ) (Q : R⟦X⟧[X]), Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.map (ofPowerSeries ℤ R) = (P.map (expand R q)).scaleRoots (single (-v) 1) ∧
      (Q.map PowerSeries.constantCoeff).nextCoeff = 0 ∧
      Q.map PowerSeries.constantCoeff ≠ X ^ P.natDegree := by
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hX (Subsingleton.elim _ _)
  set m := P.natDegree with hm
  obtain ⟨j₀, hj₀m, hj₀, hslope⟩ := exists_slope_le hP hX
  set q : ℕ+ := ⟨m - j₀, by omega⟩
  have hq : ((q : ℕ) : ℤ) = ((m - j₀ : ℕ) : ℤ) := congrArg _ (PNat.mk_coe _ _)
  set v := (P.coeff j₀).order
  -- The coefficients of the ramified and rescaled polynomial `T`.
  set T := (P.map (expand R q)).scaleRoots (single (-v) 1 : R⸨X⸩)
  have hT : ∀ j, T.coeff j = single (-((m - j : ℕ) * v)) 1 * expand R q (P.coeff j) := by
    intro j
    rw [coeff_scaleRoots, coeff_map, hP.natDegree_map, single_pow, one_pow, ← hm, nsmul_eq_mul,
      mul_neg, RingHom.coe_coe]
    exact mul_comm _ _
  have hlifts : T ∈ lifts (ofPowerSeries ℤ R) := by
    refine (lifts_iff_coeff_lifts T).2 fun j ↦ mem_range_ofPowerSeries_iff.2 fun n hn ↦ ?_
    rw [hT]
    by_cases hj : j ≤ m
    · exact coeff_single_mul_expand_eq_zero (hq ▸ hslope j hj) hn
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hj)]
      simp
  obtain ⟨Q, hQT, hQm, hQ⟩ := lifts_and_natDegree_eq_and_monic hlifts
    ((monic_scaleRoots_iff _).2 (hP.map _))
  -- The reduction of `Q` modulo `X` reads off the constant coefficients of `T`.
  have hred : ∀ j, (Q.map PowerSeries.constantCoeff).coeff j = (T.coeff j).coeff 0 := by
    intro j
    rw [coeff_map, ← hQT, coeff_map, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← coeff_coe_powerSeries, Nat.cast_zero]
  have hQdeg : Q.natDegree = m := by rw [hQm, natDegree_scaleRoots, hP.natDegree_map]
  have hgm : (Q.map PowerSeries.constantCoeff).natDegree = m := by rw [hQ.natDegree_map, hQdeg]
  refine ⟨q, v, Q, hQ, hQdeg, hQT, ?_, fun h ↦ ?_⟩
  · rw [nextCoeff_of_natDegree_pos (by omega), hgm, hred, hT,
      ← nextCoeff_of_natDegree_pos (by omega), hnext]
    simp
  · -- The coefficient of `Y ^ j₀` in the reduction is the leading coefficient of `P.coeff j₀`.
    have h₀ := congrArg (fun p : R[X] ↦ p.coeff j₀) h
    simp only [hred, hT, coeff_X_pow] at h₀
    split_ifs at h₀ with hj
    · omega
    rw [coeff_single_mul, one_mul, zero_sub, neg_neg, ← hq, coeff_expand_mul,
      coeff_order_eq_zero] at h₀
    exact hj₀ h₀

variable {K : Type*} [Field K]

/-- A monic polynomial of positive degree `m` over `K⟦X⟧`, whose reduction modulo `X` has no term
of degree `m - 1` and is not `Y ^ m`, has a monic factor of degree strictly between `0` and `m`:
the reduction splits at a root into coprime factors, and Hensel's lemma lifts the splitting. -/
private theorem exists_monic_mul_eq_of_nextCoeff_map_eq_zero [IsAlgClosed K] [CharZero K]
    {Q : K⟦X⟧[X]} (hQ : Q.Monic) (hm : 0 < Q.natDegree)
    (hnext : (Q.map PowerSeries.constantCoeff).nextCoeff = 0)
    (hX : Q.map PowerSeries.constantCoeff ≠ X ^ Q.natDegree) :
    ∃ G H : K⟦X⟧[X], G.Monic ∧ G * H = Q ∧ 0 < G.natDegree ∧ G.natDegree < Q.natDegree := by
  have hgm := hQ.natDegree_map PowerSeries.constantCoeff
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (Q.map PowerSeries.constantCoeff)
    (by rw [degree_eq_natDegree (hQ.map _).ne_zero, hgm]; exact_mod_cast hm.ne')
  obtain ⟨r, h, hr, hrm, -, hcop, hgh⟩ :=
    (hQ.map _).exists_eq_X_sub_C_pow_mul_of_nextCoeff_eq_zero
      (by rw [hgm]; exact_mod_cast hm.ne') hnext (by rwa [hgm]) ha
  obtain ⟨G, H, hG, -, hGg, -, hGH⟩ :=
    hQ.exists_monic_mul_eq_of_isCoprime ((monic_X_sub_C a).pow r) hcop hgh
  have hGr : G.natDegree = r := by
    rw [← hG.natDegree_map PowerSeries.constantCoeff, hGg, (monic_X_sub_C a).natDegree_pow,
      natDegree_X_sub_C, mul_one]
  exact ⟨G, H, hG, hGH, hGr ▸ hr, hGr ▸ hgm ▸ hrm⟩

/-- Undoing a rescaling: if the polynomial obtained from monic `P` by the ramification
`X ↦ X ^ q`, the rescaling by `X ^ (-v)` and a further ramification `X ↦ X ^ n` has a root,
then `P` has a root after the ramification `X ↦ X ^ (n * q)`. -/
private theorem exists_isRoot_map_expand_mul {P : K⸨X⸩[X]} (hP : P.Monic) {q n : ℕ+} {v : ℤ}
    {y : K⸨X⸩}
    (hy : (((P.map (expand K q)).scaleRoots (single (-v) 1 : K⸨X⸩)).map (expand K n)).IsRoot y) :
    ∃ z : K⸨X⸩, (P.map (expand K (n * q))).IsRoot z := by
  have hmap : (P.map (expand K q : K⸨X⸩ →+* K⸨X⸩)).map (expand K n : K⸨X⸩ →+* K⸨X⸩) =
      P.map (expand K (n * q) : K⸨X⸩ →+* K⸨X⸩) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun f ↦ expand_expand n q f
  rw [map_scaleRoots _ _ _ (by simp [(hP.map _).leadingCoeff]), hmap] at hy
  set s := (expand K n : K⸨X⸩ →+* K⸨X⸩) (single (-v) 1)
  have hs : s ≠ 0 := by simp [s]
  refine ⟨s⁻¹ * y, ?_⟩
  have := scaleRoots_eval_mul (P.map (expand K (n * q) : K⸨X⸩ →+* K⸨X⸩)) (s⁻¹ * y) s
  rw [mul_inv_cancel_left₀ hs, hy.eq_zero, eq_comm, mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hs)

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
  obtain ⟨q, v, Q, hQ, hQm, hQT, hQnext, hQX⟩ :=
    exists_monic_map_eq_scaleRoots_map_expand hP₁ hnext (hP₁m ▸ hX)
  rw [hP₁m] at hQm
  obtain ⟨G, H, hG, hGH, hG0, hGm⟩ := exists_monic_mul_eq_of_nextCoeff_map_eq_zero hQ
    (hQm ▸ hm) hQnext (by rwa [hQm, ← hP₁m])
  -- By induction, `G` has a root after a ramification `X ↦ X ^ n`, hence so does the rescaled
  -- polynomial.
  obtain ⟨n, y, hy⟩ := ih _ (hQm ▸ hGm) (G.map (ofPowerSeries ℤ K)) (hG.map _)
    (hG.natDegree_map _) hG0
  obtain ⟨z, hz⟩ := exists_isRoot_map_expand_mul hP₁ (n := n) (y := y) (by
    rw [← hQT, ← hGH, Polynomial.map_mul, Polynomial.map_mul, IsRoot, eval_mul, hy.eq_zero,
      zero_mul])
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

/-- Over an algebraically closed field `K` of characteristic zero, every nonconstant polynomial
over `K⸨X⸩` has a root in the Puiseux field, lying in a single ramified level. -/
theorem exists_isRoot_levelEmbedding {P : K⸨X⸩[X]} (hP : P.degree ≠ 0) :
    ∃ (n : ℕ+) (y : K⸨X⸩),
      (P.map (algebraMap K⸨X⸩ (puiseuxField K))).IsRoot (levelEmbedding K n y) := by
  obtain ⟨n, y, hy⟩ := LaurentSeries.exists_isRoot_map_expand hP
  refine ⟨n, y, ?_⟩
  have hmap : P.map (algebraMap K⸨X⸩ (puiseuxField K)) =
      (P.map (expand K n : K⸨X⸩ →+* K⸨X⸩)).map (levelEmbedding K n : K⸨X⸩ →+* puiseuxField K) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun f ↦ (levelEmbedding_expand_self n f).symm
  rw [hmap]
  exact hy.map _

end TauCeti.puiseuxField
