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
`deg c < deg g + deg h`, and the solution is unique. This is the bijectivity of the Sylvester map
of `g` and `h` on these degree bounds, in the explicit form consumed by Hensel's lemma
(`TauCeti.RingTheory.PowerSeries.Hensel`).

## Main results

* `Polynomial.mem_degreeLT_natDegree_iff`: membership in `R[X]_(g.natDegree)` is `degree < degree`.
* `Polynomial.modByMonic_mem_degreeLT`, `Polynomial.divByMonic_mem_degreeLT`: where `%ₘ` and `/ₘ`
  land.
* `Polynomial.Monic.modByMonic_mul_add`, `Polynomial.Monic.divByMonic_mul_add`: division with
  remainder reads off `g * v + u`.
* `Polynomial.Monic.sub_mem_degreeLT`: the difference of two monic polynomials of the same degree
  `n` has degree `< n`.
* `IsCoprime.exists_mem_degreeLT_mul_add_mul_eq`, `IsCoprime.eq_zero_of_mul_add_mul_eq_zero`:
  existence and uniqueness of degree-bounded solutions of `g * b + h * a = c`.

Stated over an arbitrary commutative ring, with the trivial ring dispatched by `nontriviality`
rather than excluded by hypothesis; `mem_degreeLT_natDegree_iff` needs only a semiring, and
`Monic.sub_mem_degreeLT` only a ring.

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

theorem divByMonic_mem_degreeLT (hg : g.Monic) (hq : q ∈ degreeLT R (g.natDegree + n)) :
    q /ₘ g ∈ degreeLT R n := by
  nontriviality R
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

theorem Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g := by
  nontriviality R
  refine (div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩).1
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

/-- For `g` monic and coprime to `h`, every `c` of degree `< g.natDegree + h.natDegree` is
`g * b + h * a` with `a` of degree `< g.natDegree` and `b` of degree `< h.natDegree`. Writing
`u * g + v * h = 1`, one may take `a = (v * c) %ₘ g`. -/
theorem _root_.IsCoprime.exists_mem_degreeLT_mul_add_mul_eq {g h c : R[X]} (hgh : IsCoprime g h)
    (hg : g.Monic) (hc : c ∈ degreeLT R (g.natDegree + h.natDegree)) :
    ∃ a b, a ∈ degreeLT R g.natDegree ∧ b ∈ degreeLT R h.natDegree ∧ g * b + h * a = c := by
  obtain ⟨u, v, huv⟩ := hgh
  have hdiv := modByMonic_add_div (v * c) g
  set a := (v * c) %ₘ g
  have ha : a ∈ degreeLT R g.natDegree := modByMonic_mem_degreeLT hg _
  have hab : g * (u * c + h * ((v * c) /ₘ g)) + h * a = c := by
    linear_combination c * huv + h * hdiv
  refine ⟨a, _, ha, ?_, hab⟩
  have hgb : g * (u * c + h * ((v * c) /ₘ g)) ∈ degreeLT R (g.natDegree + h.natDegree) := by
    rw [eq_sub_of_add_eq hab]
    exact sub_mem hc (mul_comm a h ▸ mem_degreeLT.mpr
      (degree_mul_lt_of_degree_lt_of_natDegree_le (mem_degreeLT.mp ha) le_rfl))
  simpa [mul_divByMonic_cancel_left _ hg] using divByMonic_mem_degreeLT hg hgb

/-- Uniqueness in `IsCoprime.exists_mem_degreeLT_mul_add_mul_eq`: if `g` is monic and coprime to
`h`, and `a` has degree `< g.natDegree`, then `g * b + h * a = 0` forces `a = 0` and `b = 0`. -/
theorem _root_.IsCoprime.eq_zero_of_mul_add_mul_eq_zero {g h a b : R[X]} (hgh : IsCoprime g h)
    (hg : g.Monic) (ha : a ∈ degreeLT R g.natDegree) (hab : g * b + h * a = 0) :
    a = 0 ∧ b = 0 := by
  nontriviality R
  have hga : g ∣ a := hgh.dvd_of_dvd_mul_left ⟨-b, by linear_combination hab⟩
  have ha0 : a = 0 := by
    rw [← (modByMonic_eq_self_iff hg).mpr ((mem_degreeLT_natDegree_iff hg.ne_zero).mp ha),
      (modByMonic_eq_zero_iff_dvd hg).mpr hga]
  subst ha0
  exact ⟨rfl, hg.mul_right_eq_zero_iff.mp (by simpa using hab)⟩

end Polynomial
