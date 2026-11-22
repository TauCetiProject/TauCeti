/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
import TauCeti.LinearAlgebra.Finsupp.LSum

/-!
# Positivity of atomic traces

Let `R` be a commutative star ring and `q : Rˣ` a self-adjoint parameter, so that the type-A
Hecke algebras carry the real-parameter involution fixing every generator `T i`
(`TauCeti.Algebra.TypeAHeckeAlgebra.Star`). Let `ι` be a linearly ordered alphabet of positive
and negative letters, with weights `p : ι → R`. The atomic trace
`TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n` is `x ↦ tr (ρ(x) * D)`, where `ρ` is the signed
checked representation on the word space and `D` is the diagonal product density of the weights.

The matrix of the signed checked R-matrix in the word basis is symmetric and its entries are
polynomials in `q`, so for self-adjoint `q` the generators act by self-adjoint matrices
(`TauCeti.isSelfAdjoint_signedCheckedR_single_apply`). Hence `ρ` carries the involution to the
conjugate transpose in the word basis (`TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply`).
Consequently, without assuming finiteness of `ι`, the diagonal coefficient of `star x * x` at a
word `w` is `∑ u ∈ (ρ(x) w).support, star (ρ(x) w u) * ρ(x) w u`, writing `ρ(x) w u` for the
coefficient of the word `u` in the image of `w`
(`TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_self_single_apply`). Over a commutative
star-ordered ring without zero divisors, vanishing of that diagonal forces the entire column
`ρ(x) w` to vanish
(`TauCeti.TypeAHeckeAlgebra.signedChecked_single_apply_eq_zero_of_star_mul_self`).

For finite alphabets over a commutative star-ordered ring, such as `ℝ`, or `ℂ` with the order
`ComplexOrder`, `atomicTrace (star x * x)` is nonnegative as soon as every weight is nonnegative
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`). No normalization of the weights
and no Markov condition is needed.

When the weights sum to `1` and satisfy the slice condition, the atomic traces are the
restrictions of the Ocneanu trace `tr_z` to the finite stages
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace`). So `tr_z` is then a positive trace on
the whole infinite Hecke algebra: `0 ≤ tr_z (star x * x)` for every `x`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_of_atomic`, a case of
`TauCeti.InfiniteTypeAHeckeAlgebra.map_star_mul_self_nonneg_of_eq_atomicTrace` for any linear
functional restricting to atomic traces on the finite stages). For the
geometric models on `r + 1` positive letters with weights proportional to `1, Q, …, Q ^ r`,
`Q = q ^ 2`, this shows that the Ocneanu trace with projection parameter `a_(r + 1)(Q)`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_geometric`) is positive
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_geometric`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_star_single_apply`: the signed checked representation
  carries the real-parameter involution to the conjugate transpose in the word basis.
* `TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_single_apply`: the matrix coefficients of
  `star x * y` in the word basis as Hermitian pairings.
* `TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_self_single_apply`,
  `TauCeti.TypeAHeckeAlgebra.signedChecked_star_mul_self_single_apply_nonneg`, and
  `TauCeti.TypeAHeckeAlgebra.signedChecked_single_apply_eq_zero_of_star_mul_self`: diagonal
  sum-of-squares formula, nonnegativity, and column vanishing without finiteness of the alphabet.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star` and `TauCeti.TypeAHeckeAlgebra.star_atomicTrace`:
  star compatibility of finite atomic traces.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg`: **positivity of atomic traces**
  with nonnegative weights.
* `TauCeti.InfiniteTypeAHeckeAlgebra.map_star_mul_self_nonneg_of_eq_atomicTrace`: a linear
  functional on the infinite algebra restricting to atomic traces with nonnegative weights is
  positive.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_of_atomic`: an Ocneanu
  trace realized by an atomic model with nonnegative weights is positive.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg_geometric`: the Ocneanu
  traces of the geometric atomic models are positive.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the signed product model.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3,
  for the positive Markov traces with parameters `a_k(Q)`.

The positivity argument, a star representation on matrices followed by `tr (D * Aᴴ * A) ≥ 0` for
a nonnegative diagonal density `D`, follows the one for the Temperley–Lieb spin models in
`TauCeti.Algebra.TemperleyLieb.SpinPositivity`.
-/

public section

open Finsupp

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R] {ι : Type*} [LinearOrder ι] {n : ℕ}

namespace TypeAHeckeAlgebra

variable (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) [hq : Fact (IsSelfAdjoint (q : R))]

/-- **The signed checked representation is a star representation.** For a self-adjoint parameter,
the coefficient of the word `u` in the image of the word `w` under `star x` is the conjugate of
the coefficient of `w` in the image of `u` under `x`: in the word basis, `star x` acts by the
conjugate transpose of the matrix of `x`. -/
@[simp]
theorem signedChecked_star_single_apply (x : TypeAHeckeAlgebra R q n) (w u : Fin n → ι) :
    signedChecked pos q (star x) (single w 1) u = star (signedChecked pos q x (single u 1) w) := by
  classical
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction generalizing w u with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have hinv : IsSelfAdjoint ((q⁻¹ : Rˣ) : R) := by
      simpa only [Ring.inverse_unit] using hq.out.ringInverse
    simp only [star_T, signedChecked_T, LinearMap.smul_apply, coe_smul, Pi.smul_apply, smul_eq_mul,
      star_mul', hinv.star_eq, Units.mul_right_inj]
    rw [(isSelfAdjoint_signedCheckedR_single_apply pos hq.out _ _ _ _).star_eq,
      signedCheckedR_single_apply_comm]
  | algebraMap r =>
    by_cases h : w = u <;> simp [← algebraMap_star_comm, Module.algebraMap_end_apply, h]
  | add y z _ _ hy hz =>
    simp only [star_add, map_add, LinearMap.add_apply, Finsupp.add_apply, hy, hz]
  | mul y z _ _ hy hz =>
    set s := (signedChecked pos q (star y) (single w 1)).support ∪
      (signedChecked pos q z (single u 1)).support
    rw [star_mul, map_mul, mul_apply_eq_comp, map_mul, mul_apply_eq_comp,
      LinearMap.apply_apply_eq_finsuppSum_mul, LinearMap.apply_apply_eq_finsuppSum_mul,
      sum_of_support_subset _ Finset.subset_union_left _ (by simp),
      sum_of_support_subset (s := s) _ Finset.subset_union_right _ (by simp), star_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [hy, hz, RingHom.id_apply, RingHom.id_apply, star_mul', mul_comm]

variable (p : ι → R)

/-- The coefficient of the word `w` in the image of the word `v` under `star x * y` is the
Hermitian pairing `∑ u, star (ρ(x) w u) * ρ(y) v u` of the images of `w` under `x` and of `v`
under `y`, writing `ρ(x) w u` for the coefficient of `u` in the image of `w` under `x`. -/
theorem signedChecked_star_mul_single_apply [Fintype ι] (x y : TypeAHeckeAlgebra R q n)
    (v w : Fin n → ι) :
    signedChecked pos q (star x * y) (single v 1) w =
      ∑ u, star (signedChecked pos q x (single w 1) u) * signedChecked pos q y (single v 1) u := by
  rw [map_mul, mul_apply_eq_comp, LinearMap.apply_apply_eq_finsuppSum_mul,
    sum_fintype _ _ (by simp)]
  simp only [RingHom.id_apply, signedChecked_star_single_apply, mul_comm]

/-- **Diagonal sum-of-squares formula** for `signedChecked pos q (star x * x)`, without assuming a
finite alphabet. -/
theorem signedChecked_star_mul_self_single_apply (x : TypeAHeckeAlgebra R q n) (w : Fin n → ι) :
    signedChecked pos q (star x * x) (single w 1) w =
      ∑ u ∈ (signedChecked pos q x (single w 1)).support,
        star (signedChecked pos q x (single w 1) u) *
          signedChecked pos q x (single w 1) u := by
  rw [map_mul, mul_apply_eq_comp, LinearMap.apply_apply_eq_finsuppSum_mul, Finsupp.sum]
  exact Finset.sum_congr rfl fun u _ ↦ by
    rw [RingHom.id_apply, signedChecked_star_single_apply, mul_comm]

/-- Every diagonal entry of `signedChecked pos q (star x * x)` is nonnegative. -/
theorem signedChecked_star_mul_self_single_apply_nonneg [PartialOrder R] [StarOrderedRing R]
    (x : TypeAHeckeAlgebra R q n) (w : Fin n → ι) :
    0 ≤ signedChecked pos q (star x * x) (single w 1) w := by
  rw [signedChecked_star_mul_self_single_apply]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- If the diagonal coefficient of `star x * x` at a word `w` vanishes over a `StarOrderedRing`
without zero divisors, then every entry `signedChecked pos q x (single w 1) u` in that column
vanishes. -/
theorem signedChecked_single_apply_eq_zero_of_star_mul_self [PartialOrder R] [StarOrderedRing R]
    [NoZeroDivisors R] (x : TypeAHeckeAlgebra R q n) {w : Fin n → ι}
    (hdiag : signedChecked pos q (star x * x) (single w 1) w = 0) (u : Fin n → ι) :
    signedChecked pos q x (single w 1) u = 0 := by
  rw [signedChecked_star_mul_self_single_apply] at hdiag
  have hcol := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ star_mul_self_nonneg _).mp hdiag
  by_contra hne
  exact hne ((mul_eq_zero.mp (hcol u (Finsupp.mem_support_iff.mpr hne))).elim star_eq_zero.mp id)

/-- For self-adjoint weights, the atomic trace commutes with the involution. -/
@[simp]
theorem atomicTrace_star [Finite ι] (hp : ∀ a, IsSelfAdjoint (p a)) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x) = star (atomicTrace pos q p n x) := by
  have := Fintype.ofFinite ι
  simp only [atomicTrace_eq_sum, signedChecked_star_single_apply, star_sum, star_mul',
    star_prod, (hp _).star_eq]

/-- Conjugating `atomicTrace` conjugates both the weights and the argument. -/
theorem star_atomicTrace [Finite ι] (x : TypeAHeckeAlgebra R q n) :
    star (atomicTrace pos q p n x) = atomicTrace pos q (star ∘ p) n (star x) := by
  cases nonempty_fintype ι
  rw [atomicTrace_eq_sum, atomicTrace_eq_sum, star_sum]
  exact Finset.sum_congr rfl fun w _ ↦ by
    rw [star_mul, mul_comm, star_prod, signedChecked_star_single_apply]; rfl

/-- **Positivity of atomic traces.** Over a commutative star-ordered ring, for a self-adjoint
parameter and nonnegative weights, the atomic trace of `star x * x` is nonnegative. -/
theorem atomicTrace_star_mul_self_nonneg [Finite ι] [PartialOrder R] [StarOrderedRing R]
    (hp : ∀ a, 0 ≤ p a) (x : TypeAHeckeAlgebra R q n) :
    0 ≤ atomicTrace pos q p n (star x * x) := by
  have := Fintype.ofFinite ι
  rw [atomicTrace_eq_sum]
  refine Finset.sum_nonneg fun w _ ↦ mul_nonneg ?_ (Finset.prod_nonneg fun i _ ↦ hp (w i))
  rw [signedChecked_star_mul_single_apply]
  exact Finset.sum_nonneg fun u _ ↦ star_mul_self_nonneg _

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

variable [PartialOrder R] [StarOrderedRing R] {q : Rˣ} [hq : Fact (IsSelfAdjoint (q : R))]

/-- A linear functional on the infinite Hecke algebra that restricts on every finite stage to the
atomic trace of nonnegative weights is positive. -/
theorem map_star_mul_self_nonneg_of_eq_atomicTrace [Finite ι] (pos : ι → Prop)
    [DecidablePred pos] {p : ι → R} (hp₀ : ∀ a, 0 ≤ p a)
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (h : ∀ m (y : TypeAHeckeAlgebra R q m), TypeAHeckeAlgebra.atomicTrace pos q p m y =
      τ (TypeAHeckeAlgebra.toInfinite R q m y))
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ τ (star x * x) := by
  obtain ⟨m, hm⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite] at hm
  obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).1 hm
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul, ← h]
  exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg pos q p hp₀ _

/-- **Positivity of the Ocneanu traces of atomic models.** If the Ocneanu trace `tr_z` is realized
by an atomic model with nonnegative weights, that is, if the weights sum to `1` and the right
slice `(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (c > b), p c` equals `q * z` for
every letter `b`, then `tr_z` is positive for the real-parameter involution. -/
theorem ocneanuTrace_star_mul_self_nonneg_of_atomic [Fintype ι] (pos : ι → Prop) [DecidablePred pos]
    {p : ι → R} (hp₀ : ∀ a, 0 ≤ p a) (hp : ∑ a, p a = 1) {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ c with b < c, p c = q * z) (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q z (star x * x) :=
  map_star_mul_self_nonneg_of_eq_atomicTrace pos hp₀
    (fun _ ↦ TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace pos q p hp hz) x

/-- **Positivity of the geometric Ocneanu traces.** Let `Q = q ^ 2` and `c * [r + 1]_Q = 1`. The
Ocneanu trace with parameter `z = c * q ^ (2 * r + 1)`, whose projection parameter is
`a_(r + 1)(Q)` (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_geometric`),
is positive for the real-parameter involution. -/
theorem ocneanuTrace_star_mul_self_nonneg_geometric {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q (c * (q : R) ^ (2 * r + 1)) (star x * x) := by
  have hQ : 0 ≤ (q : R) ^ 2 := hq.out.sq_nonneg
  set S := ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ ↦ pow_nonneg hQ a
  -- `star c * S * c = star c * (c * S) = star c` is nonnegative since `S` is.
  have hc₀ : 0 ≤ c := by
    have := star_left_conjugate_nonneg hS c
    rwa [mul_assoc, mul_comm S c, hc, mul_one, star_nonneg_iff] at this
  exact map_star_mul_self_nonneg_of_eq_atomicTrace (fun _ : Fin (r + 1) ↦ True)
    (fun a ↦ mul_nonneg hc₀ (pow_nonneg hQ _))
    (fun _ ↦ TypeAHeckeAlgebra.atomicTrace_geometric_eq q hc) x

end InfiniteTypeAHeckeAlgebra

end TauCeti
