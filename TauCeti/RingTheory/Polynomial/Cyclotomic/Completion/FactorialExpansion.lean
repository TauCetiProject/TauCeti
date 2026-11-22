/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.Map
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Factorial

import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Normalized factorial expansions in the full cyclotomic completion

Every element `x` of the full cyclotomic completion `R[q]^{ℕ_{>0}} = CycloCompletion R {n | 0 < n}`,
the classical Habiro ring of `R`, has a unique expansion
`x = ∑_{n ≥ 0} a_n(q) P_n(q)`, `deg a_n ≤ n`,
in the factorial polynomials `P_n = (1 - q) ⋯ (1 - q ^ n)`, converging modulo every cyclotomic
index. This holds over every commutative ring `R`, with no domain or torsion-freeness hypothesis.

The digits are computed at finite precision. The monic associates `(-1) ^ N P_N` are cofinal
cyclotomic indices (`TauCeti.factorialIndex`), and the first `N` normalized factorial digits
`Polynomial.factorialDigit` of a polynomial depend only on its class modulo `P_N`. So the `n`th
digit of `x` is the `n`th digit of any polynomial representing `x` modulo `P_{n + 1}`.

## Main definitions

* `TauCeti.CycloCompletion.factorialDigit x n`: the `n`th normalized factorial digit of `x`.

## Main results

* `TauCeti.CycloCompletion.factorialDigit_eq_of_proj_eq_mk`: the digits of `x` below `N` are those
  of any polynomial representing `x` modulo `P_N`.
* `TauCeti.CycloCompletion.proj_factorialIndex`: modulo `P_N`, `x` is `∑_{n < N} a_n P_n`.
* `TauCeti.CycloCompletion.tendsto_fromPoly_sum_factorialDigit`: the factorial partial sums
  converge to `x`.
* `TauCeti.CycloCompletion.existsUnique_factorialExpansion`: existence and uniqueness of the
  normalized factorial expansion.
* `TauCeti.CycloCompletion.factorialDigit_injective`: an element is determined by its digits.
* `TauCeti.CycloCompletion.factorialDigit_add`, `TauCeti.CycloCompletion.factorialDigit_smul`,
  `TauCeti.CycloCompletion.factorialDigit_map`: digits are `R`-linear and commute with coefficient
  change.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §1.
* K. Habiro, *Cyclotomic completions of polynomial rings*, arXiv:math/0209324v1, §1 and the
  proof of Lemma 3.1.
-/

public section

open Filter Finset Polynomial
open scoped Topology

namespace TauCeti

namespace CycloCompletion

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R']

/-- The `n`th normalized factorial digit of an element `x` of the full cyclotomic completion:
the `n`th factorial digit of any polynomial representing `x` modulo `P_{n + 1}`. The digits are
the unique polynomials `a_n`, `deg a_n ≤ n`, with `x = ∑_{n ≥ 0} a_n P_n`. -/
noncomputable def factorialDigit (x : CycloCompletion R {n | 0 < n}) (n : ℕ) : R[X] :=
  (AdjoinRoot.modByMonicHom (cycloIndex.monic (factorialIndex R (n + 1)))
    (proj (factorialIndex R (n + 1)) x)).factorialDigit n

/-- The digits of `x` below `N` are those of any polynomial representing `x` modulo `P_N`. -/
theorem factorialDigit_eq_of_proj_eq_mk {x : CycloCompletion R {n | 0 < n}} {N : ℕ} {p : R[X]}
    (hp : proj (factorialIndex R N) x = AdjoinRoot.mk _ p) {n : ℕ} (hn : n < N) :
    x.factorialDigit n = p.factorialDigit n := by
  have hf := cycloIndex.monic (factorialIndex R (n + 1))
  have hrep : AdjoinRoot.mk (factorialIndex R (n + 1) : R[X])
      (AdjoinRoot.modByMonicHom hf (proj (factorialIndex R (n + 1)) x)) =
        AdjoinRoot.mk (factorialIndex R (n + 1) : R[X]) p := by
    rw [AdjoinRoot.mk_leftInverse hf]
    exact proj_eq_mk_of_dvd (factorialIndex_dvd_factorialIndex hn) hp
  rw [AdjoinRoot.mk_eq_mk, factorialIndex_dvd_iff] at hrep
  exact Polynomial.factorialDigit_eq_of_dvd_sub hrep n.lt_add_one

/-- The `n`th factorial digit has degree at most `n`. -/
theorem degree_factorialDigit_le (x : CycloCompletion R {n | 0 < n}) (n : ℕ) :
    (x.factorialDigit n).degree ≤ n :=
  Polynomial.degree_factorialDigit_le _ n

/-- The digits of a polynomial in the full completion are its polynomial factorial digits. -/
@[simp]
theorem factorialDigit_fromPoly (g : R[X]) (n : ℕ) :
    (fromPoly R {n | 0 < n} g).factorialDigit n = g.factorialDigit n :=
  factorialDigit_eq_of_proj_eq_mk (proj_fromPoly _ g) n.lt_add_one

/-- The zero element has all factorial digits zero. -/
@[simp]
theorem factorialDigit_zero (n : ℕ) : (0 : CycloCompletion R {n | 0 < n}).factorialDigit n = 0 := by
  rw [← map_zero (fromPoly R {n | 0 < n}), factorialDigit_fromPoly, Polynomial.factorialDigit_zero]

/-- **Finite factorial expansion.** Modulo `P_N`, an element of the full completion is the sum
`∑_{n < N} a_n P_n` of its first `N` factorial digits. -/
theorem proj_factorialIndex (x : CycloCompletion R {n | 0 < n}) (N : ℕ) :
    proj (factorialIndex R N) x =
      AdjoinRoot.mk _ (∑ n ∈ range N, x.factorialDigit n * factorialPoly R n) := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj (factorialIndex R N) x)
  rw [← hp, sum_congr rfl fun n hn ↦ by
    rw [factorialDigit_eq_of_proj_eq_mk hp.symm (mem_range.mp hn)], AdjoinRoot.mk_eq_mk,
    factorialIndex_dvd_iff]
  exact ⟨p.factorialResidual N,
    sub_eq_iff_eq_add'.mpr (p.sum_factorialDigit_mul_add_mul_factorialResidual N).symm⟩

/-- The factorial partial sums of `x` agree with `x` modulo every index, from some precision on. -/
theorem eventually_mk_sum_factorialDigit_eq_proj (x : CycloCompletion R {n | 0 < n})
    (f : cycloIndex R {n | 0 < n}) :
    ∀ᶠ N in atTop, AdjoinRoot.mk (f : R[X]) (∑ n ∈ range N, x.factorialDigit n * factorialPoly R n)
      = proj f x := by
  filter_upwards [eventually_dvd_factorialIndex f] with N hN
  exact (proj_eq_mk_of_dvd hN (proj_factorialIndex x N)).symm

/-- **Factorial expansion.** The factorial partial sums `∑_{n < N} a_n P_n` of `x` converge to
`x` in the inverse-limit topology. -/
theorem tendsto_fromPoly_sum_factorialDigit (x : CycloCompletion R {n | 0 < n}) :
    Tendsto (fun N ↦ fromPoly R {n | 0 < n}
      (∑ n ∈ range N, x.factorialDigit n * factorialPoly R n)) atTop (𝓝 x) := by
  rw [← tendsto_sub_nhds_zero_iff, (hasBasis_nhds_zero R _).tendsto_right_iff]
  intro f _
  filter_upwards [eventually_mk_sum_factorialDigit_eq_proj x f] with N hN
  rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, proj_fromPoly, hN, sub_self]

/-- **Uniqueness of factorial digits.** Polynomials `a_n` with `deg a_n ≤ n` whose partial sums
`∑_{m < M} a_m P_m` eventually agree with `x` modulo each `P_N` are the factorial digits of `x`. -/
theorem factorialDigit_eq_of_eventually {x : CycloCompletion R {n | 0 < n}} {a : ℕ → R[X]}
    (ha : ∀ n, (a n).degree ≤ n)
    (h : ∀ N, ∀ᶠ M in atTop, AdjoinRoot.mk (factorialIndex R N : R[X])
      (∑ m ∈ range M, a m * factorialPoly R m) = proj (factorialIndex R N) x) :
    x.factorialDigit = a := by
  funext n
  obtain ⟨N, hN, hnN⟩ := ((h (n + 1)).and (eventually_gt_atTop n)).exists
  rw [factorialDigit_eq_of_proj_eq_mk hN.symm n.lt_add_one,
    factorialDigit_sum_mul_factorialPoly fun m _ ↦ ha m]
  simp [hnN]

/-- **Existence and uniqueness of normalized factorial expansions.** Every element of the full
cyclotomic completion has a unique expansion `x = ∑_{n ≥ 0} a_n P_n` with `deg a_n ≤ n`,
converging modulo every index. -/
theorem existsUnique_factorialExpansion (x : CycloCompletion R {n | 0 < n}) :
    ∃! a : ℕ → R[X], (∀ n, (a n).degree ≤ n) ∧
      ∀ f : cycloIndex R {n | 0 < n}, ∀ᶠ N in atTop,
        AdjoinRoot.mk (f : R[X]) (∑ n ∈ range N, a n * factorialPoly R n) = proj f x :=
  ⟨x.factorialDigit, ⟨x.degree_factorialDigit_le, x.eventually_mk_sum_factorialDigit_eq_proj⟩,
    fun _ ha ↦ (factorialDigit_eq_of_eventually ha.1 fun _ ↦ ha.2 _).symm⟩

/-- An element of the full completion is determined by its factorial digits. -/
theorem factorialDigit_injective :
    Function.Injective (factorialDigit : CycloCompletion R {n | 0 < n} → ℕ → R[X]) := by
  intro x y h
  ext f
  obtain ⟨N, hN⟩ := (eventually_dvd_factorialIndex f).exists
  rw [proj_eq_mk_of_dvd hN (proj_factorialIndex x N),
    proj_eq_mk_of_dvd hN (proj_factorialIndex y N), h]

/-- Factorial digits are additive. -/
@[simp]
theorem factorialDigit_add (x y : CycloCompletion R {n | 0 < n}) (n : ℕ) :
    (x + y).factorialDigit n = x.factorialDigit n + y.factorialDigit n := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj (factorialIndex R (n + 1)) x)
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (proj (factorialIndex R (n + 1)) y)
  rw [factorialDigit_eq_of_proj_eq_mk hp.symm n.lt_add_one,
    factorialDigit_eq_of_proj_eq_mk hq.symm n.lt_add_one,
    factorialDigit_eq_of_proj_eq_mk (p := p + q) (by rw [map_add, ← hp, ← hq, map_add])
      n.lt_add_one, Polynomial.factorialDigit_add]

/-- Factorial digits commute with scalar multiplication. -/
@[simp]
theorem factorialDigit_smul (r : R) (x : CycloCompletion R {n | 0 < n}) (n : ℕ) :
    (r • x).factorialDigit n = r • x.factorialDigit n := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj (factorialIndex R (n + 1)) x)
  rw [factorialDigit_eq_of_proj_eq_mk hp.symm n.lt_add_one,
    factorialDigit_eq_of_proj_eq_mk (p := r • p) (by rw [map_smul, ← hp, AdjoinRoot.smul_mk])
      n.lt_add_one, Polynomial.factorialDigit_smul]

/-- Factorial digits commute with coefficient change. -/
@[simp]
theorem factorialDigit_map (φ : R →+* R') (x : CycloCompletion R {n | 0 < n}) (n : ℕ) :
    (map φ {n | 0 < n} x).factorialDigit n = (x.factorialDigit n).map φ := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj (factorialIndex R (n + 1)) x)
  have hdvd : (factorialIndex R' (n + 1) : R'[X]) ∣ (factorialIndex R (n + 1) : R[X]).map φ := by
    simp
  rw [factorialDigit_eq_of_proj_eq_mk hp.symm n.lt_add_one, ← Polynomial.factorialDigit_map,
    factorialDigit_eq_of_proj_eq_mk (p := p.map φ) (by rw [proj_map φ hdvd, ← hp,
      AdjoinRoot.map_mk]) n.lt_add_one]

end CycloCompletion

/-! ### Reference values -/

open CycloCompletion

/-- In the full completion, `q` has factorial digits `1, -1, 0, …`. -/
example : (fromPoly ℤ {n | 0 < n} X).factorialDigit 0 = 1 ∧
    (fromPoly ℤ {n | 0 < n} X).factorialDigit 1 = -1 ∧
    (fromPoly ℤ {n | 0 < n} X).factorialDigit 2 = 0 := by
  have h : ∑ i ∈ range 2, (if i = 0 then 1 else -1 : ℤ[X]) * factorialPoly ℤ i = X := by
    simp [sum_range_succ]
  have hd (n : ℕ) := factorialDigit_sum_mul_factorialPoly
    (a := fun i ↦ if i = 0 then (1 : ℤ[X]) else -1) (N := 2)
    (fun m hm ↦ by interval_cases m <;> simp) n
  simp only [h] at hd
  simp [hd]

/-- Over the torsion ring `ZMod 2`, `2 q = 0` has all digits zero while `q` keeps the digit
`-1 = 1` at index one. -/
example : (fromPoly (ZMod 2) {n | 0 < n} (2 * X)).factorialDigit 1 = 0 ∧
    (fromPoly (ZMod 2) {n | 0 < n} X).factorialDigit 1 = 1 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
  have h : ∑ i ∈ range 2, (1 : (ZMod 2)[X]) * factorialPoly (ZMod 2) i = X := by
    simp only [sum_range_succ, range_zero, sum_empty, factorialPoly_zero, factorialPoly_one,
      one_mul]
    linear_combination (1 - X) * h2
  have hd := factorialDigit_sum_mul_factorialPoly (a := fun _ ↦ (1 : (ZMod 2)[X])) (N := 2)
    (fun m hm ↦ by interval_cases m <;> simp) 1
  rw [h] at hd
  simp [h2, hd]

end TauCeti
