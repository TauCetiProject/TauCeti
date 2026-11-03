/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic

/-!
# The norm-two shell of the Cartan matrix of type `D`

Let `B = CartanMatrix.D n`, `n ≥ 4`, be the Cartan matrix of type `Dₙ` on the simple-root lattice
`Q = Fin n → ℤ`. In the classical coordinates `eₘ` of `ℤⁿ` the Bourbaki simple roots are
`αₖ = eₖ - eₖ₊₁` for `k ≤ n - 2` and the fork root `α_(n-1) = e_(n-2) + e_(n-1)`
(`TauCeti.DynkinType.typeDSimpleRoot`, with zero-based indices). The matrix
`TauCeti.typeDSimpleRootMatrix n hn` has these roots as its columns, so it sends a vector `a` of `Q`
to its classical coordinates `∑ₖ aₖ αₖ`, and `B = Dᵀ D` for that matrix `D`
(`TauCeti.transpose_typeDSimpleRootMatrix_mul_self`): the Gram pairing of `Q` is the standard dot
product of the classical coordinates.

The main result is that the classical coordinates identify the norm-two shell of `B`, the roots of
`Dₙ`, with the integral vectors of squared length two, the classical roots `±eₚ ± e_q`, `p ≠ q`
(`TauCeti.typeDNormTwoShellEquiv`). The inverse reads off the coefficients of a classical root in
the simple roots, so the composite with the root enumeration of the pinned root datum
`TauCeti.DynkinType.typeDSimplyConnectedRootDatum n hn` sends each root index to its coroot
(`TauCeti.coe_typeDNormTwoShellEquiv_typeDRootEquiv`).

The file also evaluates the ordered sign form `Matrix.orderedSignForm B` of the ordered sign
cover of `B`. For the order of `Fin n`, the nonzero strictly lower entries of `B` are the `-1`s of
the chain bonds `(k + 1, k)` for `k + 3 < n` and of the two fork bonds `(n - 2, n - 3)` and
`(n - 1, n - 3)` (`TauCeti.orderedSignForm_cartanMatrix_D`, which holds for every `n`). Writing
`Sₖ(u) = ∑_{m ≤ k} uₘ` for the partial sums of classical coordinates, the simple-root coefficients
of a vector are `aₖ = Sₖ(D a)` for `k ≤ n - 3`, and the two fork coefficients add up to
`S_(n-2)(D a)`. Hence the ordered form of `a` and `b` is
`-∑_{k < n - 2} S_(k+1)(D a) Sₖ(D b)` (`TauCeti.orderedSignForm_cartanMatrix_D_eq_sum_range`),
with no division by `2`, although the simple-root coefficients of a classical vector involve
halving. Expanding the partial sums, the coefficient of `(D a)ₚ (D b)_q` in minus the ordered form
is `n - 2 - max (p - 1) q`, truncated at zero
(`TauCeti.orderedSignForm_cartanMatrix_D_eq_sum_sum`); by bilinearity this evaluates the ordered
sign on any two classical roots.

## Main definitions

* `TauCeti.typeDSimpleRootMatrix`: the simple roots of `Dₙ` as columns in `ℤⁿ`.
* `TauCeti.typeDNormTwoShellEquiv`: the classical roots of `Dₙ` enumerate the norm-two shell of
  `CartanMatrix.D n`.

## Main results

* `TauCeti.dotProduct_cartanMatrix_D_mulVec`: the Gram pairing of `CartanMatrix.D n` is the dot
  product of the classical coordinates.
* `TauCeti.mem_normTwoShell_cartanMatrix_D_iff`: a vector is a root exactly when its classical
  coordinates have squared length two.
* `TauCeti.coe_typeDNormTwoShellEquiv_typeDRootEquiv`: the shell vector of the classical root with
  index `k` is the coroot of the pinned root datum with index `k`.
* `TauCeti.sum_filter_typeDSimpleRootMatrix_mulVec_of_add_two_lt` and
  `TauCeti.sum_filter_typeDSimpleRootMatrix_mulVec_fork`: the partial sums of the classical
  coordinates recover the simple-root coefficients.
* `TauCeti.orderedSignForm_cartanMatrix_D_eq_sum_range` and
  `TauCeti.orderedSignForm_cartanMatrix_D_eq_sum_sum`: the ordered sign form in classical
  coordinates.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* I. B. Frenkel and V. G. Kac, *Basic representations of affine Lie algebras and dual resonance
  models*, Invent. Math. **62** (1980), 23--66.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.8.
-/

public section

namespace TauCeti

open _root_.Matrix DynkinType

variable {n : ℕ} (hn : 4 ≤ n)

/-! ### Classical coordinates -/

/-- The simple roots of type `Dₙ` in the standard coordinates `eₘ` of `ℤⁿ`: the column at the
vertex `k` is the Bourbaki simple root `TauCeti.DynkinType.typeDSimpleRoot n hn k`, that is
`eₖ - eₖ₊₁` for `k + 1 < n` and `e_(n-2) + e_(n-1)` at the fork vertex `n - 1`. -/
def typeDSimpleRootMatrix (n : ℕ) (hn : 4 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  (Matrix.of (typeDSimpleRoot n hn))ᵀ

@[simp]
theorem typeDSimpleRootMatrix_apply (m k : Fin n) :
    typeDSimpleRootMatrix n hn m k = typeDSimpleRoot n hn k m :=
  (rfl)

/-- The classical coordinates of a vector of `Q` are the combination `∑ₖ aₖ αₖ` of the simple
roots. -/
theorem typeDSimpleRootMatrix_mulVec (a : Fin n → ℤ) :
    typeDSimpleRootMatrix n hn *ᵥ a = ∑ k, a k • typeDSimpleRoot n hn k := by
  rw [typeDSimpleRootMatrix, mulVec_transpose, vecMul_eq_sum]
  rfl

/-- The classical coordinates of the simple root `αₖ` of `Q`. -/
theorem typeDSimpleRootMatrix_mulVec_single (k : Fin n) :
    typeDSimpleRootMatrix n hn *ᵥ Pi.single k 1 = typeDSimpleRoot n hn k := by
  ext m
  rw [mulVec_single_one, col_apply, typeDSimpleRootMatrix_apply]

/-- **The Cartan matrix of type `Dₙ` is the Gram matrix of the simple roots.** -/
theorem transpose_typeDSimpleRootMatrix_mul_self :
    (typeDSimpleRootMatrix n hn)ᵀ * typeDSimpleRootMatrix n hn = CartanMatrix.D n := by
  rw [typeDSimpleRootMatrix, transpose_transpose, typeDSimpleRoot_mul_transpose_self hn]

/-- The Gram pairing of `CartanMatrix.D n` is the dot product of the classical coordinates. -/
theorem dotProduct_cartanMatrix_D_mulVec (a b : Fin n → ℤ) :
    a ⬝ᵥ CartanMatrix.D n *ᵥ b =
      (typeDSimpleRootMatrix n hn *ᵥ a) ⬝ᵥ (typeDSimpleRootMatrix n hn *ᵥ b) := by
  rw [← transpose_typeDSimpleRootMatrix_mul_self hn, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- The simple-root coefficients of the classical coordinates of `a` are `a`. -/
@[simp]
theorem typeDSimpleRootCoordinates_typeDSimpleRootMatrix_mulVec (a : Fin n → ℤ) :
    typeDSimpleRootCoordinates n hn (typeDSimpleRootMatrix n hn *ᵥ a) = a :=
  typeDSimpleRootCoordinates_eq_of_sum_smul_eq hn (typeDSimpleRootMatrix_mulVec hn a).symm

/-- A classical vector of even coordinate sum is the classical coordinate vector of its simple-root
coefficients. -/
theorem typeDSimpleRootMatrix_mulVec_typeDSimpleRootCoordinates {v : Fin n → ℤ}
    (hv : Even (∑ m, v m)) :
    typeDSimpleRootMatrix n hn *ᵥ typeDSimpleRootCoordinates n hn v = v := by
  rw [typeDSimpleRootMatrix_mulVec]
  exact sum_smul_typeDSimpleRootCoordinates hn hv

/-- The classical coordinates determine the vector: `a ↦ D *ᵥ a` is injective. -/
theorem typeDSimpleRootMatrix_mulVec_injective :
    Function.Injective (typeDSimpleRootMatrix n hn).mulVec :=
  Function.LeftInverse.injective (g := typeDSimpleRootCoordinates n hn)
    (typeDSimpleRootCoordinates_typeDSimpleRootMatrix_mulVec hn)

/-! ### The roots -/

/-- **A vector of `Q` is a root of `Dₙ` exactly when its classical coordinates have squared
length two.** -/
theorem mem_normTwoShell_cartanMatrix_D_iff {a : Fin n → ℤ} :
    a ∈ (CartanMatrix.D n).normTwoShell ↔
      (typeDSimpleRootMatrix n hn *ᵥ a) ⬝ᵥ (typeDSimpleRootMatrix n hn *ᵥ a) = 2 := by
  rw [mem_normTwoShell, dotProduct_cartanMatrix_D_mulVec hn]

/-- **The roots of type `Dₙ` are the classical roots** `±eₚ ± e_q`, `p ≠ q`, the integral vectors of
squared length two: a classical root corresponds to its coefficients in the simple roots, and a
vector of the norm-two shell of `CartanMatrix.D n` to its classical coordinates. -/
def typeDNormTwoShellEquiv : TypeDRoot n ≃ (CartanMatrix.D n).normTwoShell where
  toFun x := ⟨typeDSimpleRootCoordinates n hn x.1, by
    rw [mem_normTwoShell_cartanMatrix_D_iff hn,
      typeDSimpleRootMatrix_mulVec_typeDSimpleRootCoordinates hn (even_sum_typeDRoot x)]
    exact x.2⟩
  invFun a := ⟨typeDSimpleRootMatrix n hn *ᵥ a.1, (mem_normTwoShell_cartanMatrix_D_iff hn).mp a.2⟩
  left_inv x :=
    Subtype.ext (typeDSimpleRootMatrix_mulVec_typeDSimpleRootCoordinates hn (even_sum_typeDRoot x))
  right_inv a := Subtype.ext (typeDSimpleRootCoordinates_typeDSimpleRootMatrix_mulVec hn a.1)

@[simp]
theorem coe_typeDNormTwoShellEquiv_apply (x : TypeDRoot n) :
    (typeDNormTwoShellEquiv hn x : Fin n → ℤ) = typeDSimpleRootCoordinates n hn x.1 :=
  (rfl)

@[simp]
theorem coe_typeDNormTwoShellEquiv_symm_apply (a : (CartanMatrix.D n).normTwoShell) :
    ((typeDNormTwoShellEquiv hn).symm a : Fin n → ℤ) = typeDSimpleRootMatrix n hn *ᵥ a.1 :=
  (rfl)

/-- **The root of `Dₙ` with index `k` is the coroot with index `k` of the pinned root datum**
`TauCeti.DynkinType.typeDSimplyConnectedRootDatum n hn`, in simple-coroot coordinates; the Cartan
matrix being symmetric, this is also the `k`-th classical root in simple-root coordinates. -/
theorem coe_typeDNormTwoShellEquiv_typeDRootEquiv (k : Fin (2 * n * (n - 1))) :
    (typeDNormTwoShellEquiv hn (typeDRootEquiv n hn k) : Fin n → ℤ) =
      (typeDSimplyConnectedRootDatum n hn).coroot k := by
  rw [coe_typeDNormTwoShellEquiv_apply, coroot_typeDSimplyConnectedRootDatum]

/-! ### Partial sums of classical coordinates -/

/-- The partial sum `∑_{m ≤ K} (αⱼ)ₘ` of the classical coordinates of the simple root `αⱼ`
(`TauCeti.sum_filter_typeDSimpleRoot`): the chain root `eⱼ - eⱼ₊₁` contributes `1` exactly at
`K = j`, and each of the two coordinates of the fork root `e_(n-2) + e_(n-1)` contributes `1` once
`K` reaches it. -/
private def typeDSimpleRootPartialSum (n : ℕ) (j : Fin n) (K : ℕ) : ℤ :=
  if j.val + 1 < n then (if j.val = K then 1 else 0)
  else (if n ≤ K + 2 then 1 else 0) + (if n ≤ K + 1 then 1 else 0)

private theorem sum_filter_typeDSimpleRoot (j : Fin n) (K : ℕ) :
    ∑ m : Fin n with m.val ≤ K, typeDSimpleRoot n hn j m = typeDSimpleRootPartialSum n j K := by
  unfold typeDSimpleRootPartialSum
  by_cases hj : j.val + 1 < n
  · simp only [typeDSimpleRoot_of_add_one_lt hn hj, hj, ↓reduceIte, Pi.sub_apply,
      Finset.sum_sub_distrib, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
      Finset.mem_univ, true_and]
    split_ifs <;> omega
  · simp only [typeDSimpleRoot_of_not_add_one_lt hn hj, hj, ↓reduceIte, Pi.add_apply,
      Finset.sum_add_distrib, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
      Finset.mem_univ, true_and]
    split_ifs <;> omega

/-- The partial sums of the classical coordinates of a vector `a` of `Q`, in terms of its
simple-root coefficients. -/
private theorem sum_filter_typeDSimpleRootMatrix_mulVec (a : Fin n → ℤ) (K : ℕ) :
    ∑ m : Fin n with m.val ≤ K, (typeDSimpleRootMatrix n hn *ᵥ a) m =
      ∑ j, a j * typeDSimpleRootPartialSum n j K := by
  simp only [← sum_filter_typeDSimpleRoot hn, typeDSimpleRootMatrix_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Away from the fork, the partial sums of the classical coordinates are the simple-root
coefficients**: `∑_{m ≤ K} (D a)ₘ = a_K` for `K ≤ n - 3`. -/
theorem sum_filter_typeDSimpleRootMatrix_mulVec_of_add_two_lt (a : Fin n → ℤ) {K : ℕ}
    (hK : K + 2 < n) :
    ∑ m : Fin n with m.val ≤ K, (typeDSimpleRootMatrix n hn *ᵥ a) m = a ⟨K, by omega⟩ := by
  rw [sum_filter_typeDSimpleRootMatrix_mulVec, Finset.sum_eq_single ⟨K, by omega⟩]
  · simp [typeDSimpleRootPartialSum, show K + 1 < n by omega]
  · intro j _ hj
    have : j.val ≠ K := fun h ↦ hj (Fin.ext h)
    simp only [typeDSimpleRootPartialSum]
    split_ifs <;> omega
  · simp

/-- **At the fork, the partial sum of the classical coordinates is the sum of the two fork
coefficients**: `∑_{m ≤ n - 2} (D a)ₘ = a_(n-2) + a_(n-1)`. -/
theorem sum_filter_typeDSimpleRootMatrix_mulVec_fork (a : Fin n → ℤ) :
    ∑ m : Fin n with m.val ≤ n - 2, (typeDSimpleRootMatrix n hn *ᵥ a) m =
      a ⟨n - 2, by omega⟩ + a ⟨n - 1, by omega⟩ := by
  rw [sum_filter_typeDSimpleRootMatrix_mulVec, Finset.sum_eq_add ⟨n - 2, by omega⟩
    ⟨n - 1, by omega⟩ (by simp only [ne_eq, Fin.ext_iff]; omega)]
  · simp only [typeDSimpleRootPartialSum]
    split_ifs <;> omega
  · intro j _ hj
    simp only [ne_eq, Fin.ext_iff] at hj
    simp only [typeDSimpleRootPartialSum]
    split_ifs <;> omega
  · simp
  · simp

/-! ### The ordered sign form -/

/-- **The ordered form of `CartanMatrix.D n`**: its nonzero strictly lower entries are the `-1`s of
the chain bonds `(k + 1, k)` with `k + 3 < n` and of the two fork bonds `(n - 2, n - 3)` and
`(n - 1, n - 3)`. -/
theorem orderedSignForm_cartanMatrix_D (a b : Fin n → ℤ) :
    orderedSignForm (CartanMatrix.D n) a b =
      -∑ i : Fin n, ∑ j : Fin n,
        if j.val + 1 = i.val ∧ i.val + 2 < n ∨ j.val + 3 = n ∧ n ≤ i.val + 2 then a i * b j
        else 0 := by
  simp only [orderedSignForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [CartanMatrix.D, of_apply, Fin.ext_iff, Fin.lt_def]
  split_ifs <;> first | omega | ring

/-- The coefficients of the ordered form in partial sums: summed over `k < n - 2`, the products of
the partial sums `∑_{m ≤ k + 1} (αᵢ)ₘ` and `∑_{m ≤ k} (αⱼ)ₘ` of two simple roots
(`TauCeti.typeDSimpleRootPartialSum`) pair the chain vertex `j ≤ n - 3` with the next vertex
`j + 1`, and also with the fork vertex `n - 1` when `j = n - 3`. -/
private theorem sum_range_partialSum_mul_partialSum (i j : Fin n) :
    ∑ k ∈ Finset.range (n - 2),
        typeDSimpleRootPartialSum n i (k + 1) * typeDSimpleRootPartialSum n j k =
      if j.val + 1 = i.val ∧ i.val + 2 < n ∨ j.val + 3 = n ∧ n ≤ i.val + 2 then (1 : ℤ)
      else 0 := by
  unfold typeDSimpleRootPartialSum
  by_cases hj : j.val + 3 ≤ n
  · rw [Finset.sum_eq_single j.val]
    · split_ifs <;> omega
    · intro k hk hkj
      rw [Finset.mem_range] at hk
      split_ifs <;> omega
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Finset.sum_eq_zero fun k hk ↦ by rw [Finset.mem_range] at hk; split_ifs <;> omega]
    split_ifs <;> omega

/-- **The ordered form of `CartanMatrix.D n` in classical coordinates.** Writing
`Sₖ(u) = ∑_{m ≤ k} uₘ` for the partial sums of the classical coordinates, the ordered form of `a`
and `b` is `-∑_{k < n - 2} S_(k+1)(D a) Sₖ(D b)`. -/
theorem orderedSignForm_cartanMatrix_D_eq_sum_range (a b : Fin n → ℤ) :
    orderedSignForm (CartanMatrix.D n) a b =
      -∑ k ∈ Finset.range (n - 2),
        (∑ m : Fin n with m.val ≤ k + 1, (typeDSimpleRootMatrix n hn *ᵥ a) m) *
          ∑ m : Fin n with m.val ≤ k, (typeDSimpleRootMatrix n hn *ᵥ b) m := by
  rw [orderedSignForm_cartanMatrix_D, neg_inj]
  -- Expand both partial sums in the simple-root coefficients and collect the coefficient of
  -- `a i * b j`.
  simp only [sum_filter_typeDSimpleRootMatrix_mulVec, Finset.sum_mul_sum]
  rw [Finset.sum_comm (s := Finset.range (n - 2))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm (s := Finset.range (n - 2))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mul_mul_mul_comm (a i), ← Finset.mul_sum, sum_range_partialSum_mul_partialSum]
  split_ifs <;> ring

/-- **The ordered form of `CartanMatrix.D n` in classical coordinates, coefficientwise.** The
coefficient of `(D a)ₚ (D b)_q` in `-orderedSignForm (CartanMatrix.D n) a b` is the number
`n - 2 - max (p - 1) q` (truncated at zero) of indices `k < n - 2` with `p ≤ k + 1` and `q ≤ k`. -/
theorem orderedSignForm_cartanMatrix_D_eq_sum_sum (a b : Fin n → ℤ) :
    orderedSignForm (CartanMatrix.D n) a b =
      -∑ p : Fin n, ∑ q : Fin n, (typeDSimpleRootMatrix n hn *ᵥ a) p *
        (typeDSimpleRootMatrix n hn *ᵥ b) q * ((n - 2 - max (p.val - 1) q.val : ℕ) : ℤ) := by
  rw [orderedSignForm_cartanMatrix_D_eq_sum_range hn, neg_inj]
  simp only [Finset.sum_filter, Finset.sum_mul_sum]
  rw [Finset.sum_comm (s := Finset.range (n - 2))]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_comm (s := Finset.range (n - 2))]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- The indices `k < n - 2` with `p ≤ k + 1` and `q ≤ k` form the interval from
  -- `max (p - 1) q` to `n - 2`.
  have hcard : {k ∈ Finset.range (n - 2) | p.val ≤ k + 1 ∧ q.val ≤ k}.card =
      n - 2 - max (p.val - 1) q.val := by
    rw [← Nat.card_Ico (max (p.val - 1) q.val) (n - 2)]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← hcard, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hp : p.val ≤ k + 1 <;> by_cases hq : q.val ≤ k <;> simp [hp, hq]

end TauCeti
