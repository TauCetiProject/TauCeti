/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT
import TauCeti.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Division with remainder by a monic polynomial, against `degreeLT`

Mathlib's `Polynomial.degreeLT R n` is the submodule `R[X]_n` of polynomials of degree `< n`, and
`p %ₘ g` / `p /ₘ g` are division with remainder by a monic `g`. Mathlib relates the two only for
`g = X ^ m`, through `Polynomial.degreeLT.addLinearEquiv`; this file records the general monic
statements: that `%ₘ g` lands in `R[X]_(g.natDegree)`, that `/ₘ g` drops the degree bound by
`g.natDegree`, and how both read off `g * v + u`.

Together they say that `q ↦ (q %ₘ g, q /ₘ g)` inverts `(u, v) ↦ g * v + u`, which is the
`p = 1` case of the Sylvester map. `TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot` turns
that into a linear equivalence and uses it to identify a norm with a resultant.

For `g` monic and coprime to `h`, the same division solves the Bézout equation
`g * b + h * a = c` within the degree bounds `deg a < deg g` and `deg b < deg h`, whenever
`deg c < deg g + deg h`, and the solution is unique: writing `u * g + v * h = 1`, it is
`a = (v * c) %ₘ g` and `b = u * c + h * ((v * c) /ₘ g)`. This is the bijectivity of the Sylvester
map of `g` and `h` on these degree bounds, in the explicit form consumed by Hensel's lemma
(`TauCeti.RingTheory.PowerSeries.Hensel`).

## Main results

* `Polynomial.mem_degreeLT_natDegree_iff`: membership in `R[X]_(g.natDegree)` is `degree < degree`.
* `Polynomial.mem_degreeLT_succ_iff_natDegree_le`: membership in `R[X]_(n + 1)` is
  `natDegree ≤ n`.
* `Polynomial.modByMonic_mem_degreeLT`, `Polynomial.divByMonic_mem_degreeLT`: where `%ₘ` and `/ₘ`
  land.
* `Polynomial.Monic.modByMonic_mul_add`, `Polynomial.Monic.divByMonic_mul_add`: division with
  remainder reads off `g * v + u`.
* `Polynomial.map_mem_degreeLT`: a change of coefficients preserves membership in `R[X]_n`.
* `Polynomial.finrank_degreeLT`: `R[X]_n` has rank `n`.
* `Polynomial.finite_setOf_monic_natDegree_eq`, `Polynomial.ncard_setOf_monic_natDegree_eq`:
  over a finite coefficient ring there are finitely many monic polynomials of degree `d`, and over
  a nontrivial one there are `#R ^ d` of them, since `Polynomial.monicEquivDegreeLT` matches them
  with `R[X]_d`.
* `Polynomial.Monic.sub_mem_degreeLT`: the difference of two monic polynomials of the same degree
  `n` has degree `< n`.
* `Polynomial.Monic.mul_add_mul_eq_iff`: given a Bézout relation `u * g + v * h = 1`, the
  solution of `g * b + h * a = c` with `deg a < deg g` is `a = (v * c) %ₘ g` and
  `b = u * c + h * ((v * c) /ₘ g)`.
* `IsCoprime.exists_mem_degreeLT_mul_add_mul_eq`, `IsCoprime.eq_zero_of_mul_add_mul_eq_zero`:
  existence and uniqueness of degree-bounded solutions of `g * b + h * a = c`.

Stated over an arbitrary commutative ring, with the trivial ring dispatched by `nontriviality`
rather than excluded by hypothesis; `mem_degreeLT_natDegree_iff` and
`mem_degreeLT_succ_iff_natDegree_le` need only a semiring, `finrank_degreeLT` a semiring with the
strong rank condition, and `Monic.sub_mem_degreeLT` and `divByMonic_mem_degreeLT` only a ring.

## Provenance

The division lemmas are adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file `EllipticCurves/Mathlib/Basic.lean` lines
629-690, where these are collected as Mathlib-bound prerequisites of the resultant description of
the norm on `AdjoinRoot`. The source targets Lean `v4.32.0`; this is a forward port, and the
proofs of `Monic.modByMonic_mul_add` and `Monic.divByMonic_mul_add` are restated over Mathlib's
current `Polynomial.add_modByMonic` and `Polynomial.self_mul_modByMonic` rather than over the
source's shared `div_modByMonic_unique` helper.
-/

public section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] {g q : R[X]}

theorem mem_degreeLT_natDegree_iff (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]

/-- Membership in `R[X]_(n + 1)` is the bound `natDegree ≤ n`. -/
theorem mem_degreeLT_succ_iff_natDegree_le {n : ℕ} {p : R[X]} :
    p ∈ degreeLT R (n + 1) ↔ p.natDegree ≤ n := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE, natDegree_le_iff_degree_le]

/-- A change of coefficients preserves the degree bound. -/
theorem map_mem_degreeLT {S : Type*} [Semiring S] (φ : R →+* S) {n : ℕ} {f : R[X]}
    (hf : f ∈ degreeLT R n) : f.map φ ∈ degreeLT S n :=
  mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 hf))

/-- The polynomials of degree `< n` form a free module of rank `n`. -/
@[simp]
theorem finrank_degreeLT [StrongRankCondition R] (n : ℕ) : Module.finrank R (degreeLT R n) = n := by
  rw [Module.finrank_eq_card_basis (degreeLT.basis R n), Fintype.card_fin]

variable (R)

/-- Over a finite semiring there are finitely many monic polynomials of each degree: such a
polynomial is determined by its lower coefficients. -/
theorem finite_setOf_monic_natDegree_eq [Finite R] (d : ℕ) :
    {g : R[X] | g.Monic ∧ g.natDegree = d}.Finite := by
  nontriviality R
  have : Finite (degreeLT R d) := .of_equiv _ (degreeLTEquiv R d).toEquiv.symm
  exact Set.finite_coe_iff.mp (.of_equiv _ (monicEquivDegreeLT d).symm)

/-- Over a nontrivial semiring `R` there are `#R ^ d` monic polynomials of degree `d`, one for each
choice of the `d` lower coefficients. For infinite `R` (and `d ≥ 1`) both sides are `0`. -/
theorem ncard_setOf_monic_natDegree_eq [Nontrivial R] (d : ℕ) :
    {g : R[X] | g.Monic ∧ g.natDegree = d}.ncard = Nat.card R ^ d := by
  rw [← Nat.card_coe_set_eq, Set.coe_ofPred,
    Nat.card_congr ((monicEquivDegreeLT d).trans (degreeLTEquiv R d).toEquiv), Nat.card_fun,
    Nat.card_fin]

/-- A predicate implying monicity partitions the monic polynomials of degree `d` into those
satisfying it and those not satisfying it. -/
theorem ncard_monic_pred_add_ncard_monic_not_pred [Finite R] [Nontrivial R] (d : ℕ)
    (P : R[X] → Prop) (hP : ∀ f, P f → f.Monic) :
    {f : R[X] | f.natDegree = d ∧ P f}.ncard +
      {f : R[X] | f.Monic ∧ f.natDegree = d ∧ ¬P f}.ncard = Nat.card R ^ d := by
  have hdisj : Disjoint {f : R[X] | f.natDegree = d ∧ P f}
      {f : R[X] | f.Monic ∧ f.natDegree = d ∧ ¬P f} :=
    Set.disjoint_left.mpr fun _ hf hf' ↦ hf'.2.2 hf.2
  have hA : {f : R[X] | f.natDegree = d ∧ P f}.Finite :=
    (finite_setOf_monic_natDegree_eq R d).subset fun f hf ↦ ⟨hP f hf.2, hf.1⟩
  have hB : {f : R[X] | f.Monic ∧ f.natDegree = d ∧ ¬P f}.Finite :=
    (finite_setOf_monic_natDegree_eq R d).subset fun _ hf ↦ ⟨hf.1, hf.2.1⟩
  rw [← ncard_setOf_monic_natDegree_eq R d, ← Set.ncard_union_eq hdisj hA hB]
  congr 1
  ext f
  by_cases h : P f
  · simp [h, hP f h]
  · simp [h]

end Semiring

section Ring

variable {R : Type*} [Ring R]

/-- The difference of two monic polynomials of the same degree `n` has degree `< n`. -/
theorem Monic.sub_mem_degreeLT {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P.natDegree = Q.natDegree) : P - Q ∈ degreeLT R P.natDegree := by
  nontriviality R
  rw [mem_degreeLT, ← degree_eq_natDegree hP.ne_zero]
  refine degree_sub_lt_left ?_ hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
  rw [degree_eq_natDegree hP.ne_zero, degree_eq_natDegree hQ.ne_zero, hPQ]

variable {g q : R[X]} {n : ℕ} in
/-- If `q` has degree `< g.natDegree + n`, then `q /ₘ g` has degree `< n`. This holds for every
`g`: when `g` is not monic, `q /ₘ g` is zero by convention. -/
theorem divByMonic_mem_degreeLT (hq : q ∈ degreeLT R (g.natDegree + n)) :
    q /ₘ g ∈ degreeLT R n := by
  nontriviality R
  by_cases hg : g.Monic
  swap
  · simp [divByMonic_eq_of_not_monic _ hg]
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

end Ring

variable {R : Type*} [CommRing R] {g q : R[X]} {n : ℕ}

@[simp]
theorem Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g := by
  rw [add_modByMonic, self_mul_modByMonic hg, zero_add]

theorem modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree := by
  nontriviality R
  exact (mem_degreeLT_natDegree_iff hg.ne_zero).mpr (degree_modByMonic_lt q hg)

theorem Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g := by
  nontriviality R
  refine (div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩).1
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

/-- **Bézout and division solve `g * b + h * a = c`.** If `u * g + v * h = 1` with `g` monic
and `a` of degree `< g.natDegree`, then `g * b + h * a = c` holds exactly when `a` is the
remainder of `v * c` on division by `g` and `b = u * c + h * ((v * c) /ₘ g)`. No degree bound on
`c` is needed. -/
theorem Monic.mul_add_mul_eq_iff {g h u v a b c : R[X]} (hg : g.Monic) (huv : u * g + v * h = 1)
    (ha : a ∈ degreeLT R g.natDegree) :
    g * b + h * a = c ↔ a = (v * c) %ₘ g ∧ b = u * c + h * ((v * c) /ₘ g) := by
  nontriviality R
  refine ⟨fun hab ↦ ?_, fun ⟨hav, hbv⟩ ↦ ?_⟩
  · have hdeg := (mem_degreeLT_natDegree_iff hg.ne_zero).mp ha
    have hvc : v * c = g * (v * b - u * a) + a := by linear_combination (-v) * hab + a * huv
    rw [hvc, hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr hdeg, hg.divByMonic_mul_add,
      (divByMonic_eq_zero_iff hg).mpr hdeg, add_zero]
    exact ⟨rfl, by linear_combination (-b) * huv + u * hab⟩
  · rw [hav, hbv]
    linear_combination c * huv + h * modByMonic_add_div (v * c) g

/-- For `g` monic and coprime to `h`, every `c` of degree `< g.natDegree + h.natDegree` is
`g * b + h * a` with `a` of degree `< g.natDegree` and `b` of degree `< h.natDegree`. Writing
`u * g + v * h = 1`, one may take `a = (v * c) %ₘ g`, by `Polynomial.Monic.mul_add_mul_eq_iff`. -/
theorem _root_.IsCoprime.exists_mem_degreeLT_mul_add_mul_eq {g h c : R[X]} (hgh : IsCoprime g h)
    (hg : g.Monic) (hc : c ∈ degreeLT R (g.natDegree + h.natDegree)) :
    ∃ a b, a ∈ degreeLT R g.natDegree ∧ b ∈ degreeLT R h.natDegree ∧ g * b + h * a = c := by
  obtain ⟨u, v, huv⟩ := hgh
  have ha := modByMonic_mem_degreeLT hg (v * c)
  have hab := (hg.mul_add_mul_eq_iff huv ha (b := u * c + h * ((v * c) /ₘ g))).mpr ⟨rfl, rfl⟩
  refine ⟨_, _, ha, ?_, hab⟩
  have hgb : g * (u * c + h * ((v * c) /ₘ g)) ∈ degreeLT R (g.natDegree + h.natDegree) := by
    rw [eq_sub_of_add_eq hab]
    exact sub_mem hc (mul_comm ((v * c) %ₘ g) h ▸ mem_degreeLT.mpr
      (degree_mul_lt_of_degree_lt_of_natDegree_le (mem_degreeLT.mp ha) le_rfl))
  simpa [mul_divByMonic_cancel_left _ hg] using divByMonic_mem_degreeLT hgb

/-- Uniqueness in `IsCoprime.exists_mem_degreeLT_mul_add_mul_eq`: if `g` is monic and coprime to
`h`, and `a` has degree `< g.natDegree`, then `g * b + h * a = 0` forces `a = 0` and `b = 0`. -/
theorem _root_.IsCoprime.eq_zero_of_mul_add_mul_eq_zero {g h a b : R[X]} (hgh : IsCoprime g h)
    (hg : g.Monic) (ha : a ∈ degreeLT R g.natDegree) (hab : g * b + h * a = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨u, v, huv⟩ := hgh
  simpa using (hg.mul_add_mul_eq_iff huv ha).mp hab

end Polynomial
