/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import TauCeti.Algebra.BigOperators.Multiset.DivStable
import TauCeti.LinearAlgebra.BilinearForm.BaseChange
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Charpoly.Roots
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.Eigenspace.Pairing
import TauCeti.LinearAlgebra.PerfectPairing.BaseChange

/-!
# The determinant of a similitude of a bilinear form

Let `B` be a perfect (equivalently, nondegenerate) bilinear form on a finite-dimensional vector
space `V` of dimension `b` over a field `K`, and let `φ` be a *similitude* of `B` with multiplier
`c`: `B (φ x) (φ y) = c * B x y`, written `B.compl₁₂ φ φ = c • B`. Fix `s` with `s * s = c`, and let
`m₊` and `m₋` be the algebraic multiplicities of `s` and `-s` as eigenvalues of `φ`, that is the
dimensions of the maximal generalized eigenspaces. No semisimplicity of `φ` is assumed.

* `det φ = (-1) ^ m₋ * s ^ b`
  (`LinearMap.BilinForm.det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul`). The form need not be
  symmetric or alternating, `c` may be zero, and no assumption on the characteristic is made. When
  `s` only exists in an extension `L` of `K`, the multiplicities are taken for the scalar extension
  of `φ` to `L`
  (`LinearMap.BilinForm.algebraMap_det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul`).
* If `2 ≠ 0` and `c ≠ 0`, then `b - m₊ - m₋` is even
  (`LinearMap.BilinForm.even_finrank_sub_finrank_maxGenEigenspace_of_compl₁₂_self_eq_smul`), so
  also `det φ = (-1) ^ (b - m₊) * s ^ b`
  (`LinearMap.BilinForm.det_eq_neg_one_pow_finrank_sub_mul_pow_of_compl₁₂_self_eq_smul`). This
  second sign formula holds without assumptions on `2` or `c`: if `2 = 0` then `-1 = 1`, and if
  `c = 0` both sides vanish in positive dimension.
* If `B` is alternating and `c ≠ 0`, the generalized eigenspaces at the square roots of `c` have
  even dimension
  (`LinearMap.BilinForm.even_finrank_maxGenEigenspace_of_isAlt_of_compl₁₂_self_eq_smul`), and
  `det φ = c ^ (b / 2)` for every `c`
  (`LinearMap.BilinForm.det_eq_pow_of_isAlt_of_compl₁₂_self_eq_smul`).

The sign is not determined by the form alone: on `K` with `B x y = x * y`, the similitude `φ = -s`
has multiplier `c = s * s`, `m₋ = 1` and `det φ = -s`. In characteristic two the parity statement
fails for the same example, where `s = -s` and `b - m₊ - m₋ = -1`. It also fails for `c = 0`: on
`K³` with the form `x₁ y₃ + x₂ y₂ + x₃ y₁`, the projection onto the isotropic line spanned by the
first basis vector along the span of the other two is a similitude with multiplier `0`,
`m₊ = m₋ = 2` and `b = 3`.

The proof extends scalars to an algebraic closure, where the characteristic polynomial of `φ`
splits. Its roots, counted with multiplicity, are stable under `x ↦ c / x`
(`LinearMap.roots_charpoly_eq_map_div_of_compl₁₂_eq_smul`), so the roots other than `±s` pair off
into pairs of product `c = s * s`
(`Multiset.prod_eq_neg_one_pow_count_mul_pow_card_of_map_div_eq`).
For an alternating form, `B` restricts to perfect alternating pairings on the generalized
eigenspaces at `±s` (`LinearMap.isPerfPair_domRestrict₁₂_maxGenEigenspace_of_compl₁₂_eq_smul`),
which therefore have even dimension.

The determinant `det φ * det φ = c ^ b` of a similitude of a general perfect pairing is
`LinearMap.det_mul_det_eq_of_compl₁₂_eq_smul`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (2.6).
* J. S. Milne, *Lectures on Étale Cohomology*, Remark 27.13 and Summary 27.14.
-/

public section

open Module Module.End Polynomial

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {φ : End K V} {c s : K}

/-- The degenerate case `c = 0`: a similitude with multiplier `0` of a perfect form has
`det φ = (-1) ^ m * 0 ^ b` for every `m ≤ b`, since both sides vanish in positive dimension and are
`1` in dimension zero. -/
private theorem det_eq_neg_one_pow_mul_zero_pow_of_compl₁₂_self_eq_zero (B : BilinForm K V)
    [B.IsPerfPair] (h : B.compl₁₂ φ φ = (0 : K) • B) {m : ℕ} (hm : m ≤ finrank K V) :
    LinearMap.det φ = (-1) ^ m * 0 ^ finrank K V := by
  have hdet := LinearMap.det_mul_det_eq_of_compl₁₂_eq_smul B (IsPerfPair.bijective_right B) h
  rcases eq_or_ne (finrank K V) 0 with hV | hV
  · simp [hV, Nat.eq_zero_of_le_zero (hV ▸ hm), det_eq_one_of_finrank_eq_zero hV]
  · rw [zero_pow hV, mul_self_eq_zero] at hdet
    rw [hdet, zero_pow hV, mul_zero]

/-- The determinant formula when the characteristic polynomial of `φ` splits. -/
private theorem det_eq_neg_one_pow_mul_pow_of_splits (B : BilinForm K V) [B.IsPerfPair]
    (h : B.compl₁₂ φ φ = c • B) (hs : s * s = c) (hsplit : φ.charpoly.Splits) :
    LinearMap.det φ = (-1) ^ finrank K (φ.maxGenEigenspace (-s)) * s ^ finrank K V := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · obtain rfl : s = 0 := mul_self_eq_zero.1 hs
    exact det_eq_neg_one_pow_mul_zero_pow_of_compl₁₂_self_eq_zero B h (Submodule.finrank_le _)
  have hmap := (LinearMap.roots_charpoly_eq_map_div_of_compl₁₂_eq_smul B h hc).symm
  have h0 := LinearMap.zero_notMem_roots_charpoly_of_compl₁₂_eq_smul B h hc
  rw [det_eq_prod_roots_charpoly_of_splits hsplit, LinearMap.finrank_maxGenEigenspace_eq,
    ← count_roots, ← φ.charpoly_natDegree, hsplit.natDegree_eq_card_roots]
  exact Multiset.prod_eq_neg_one_pow_count_mul_pow_card_of_map_div_eq hs hmap h0

/-- The parity of `b - m₊ - m₋` when the characteristic polynomial of `φ` splits. -/
private theorem even_finrank_sub_of_splits (B : BilinForm K V) [B.IsPerfPair]
    (h2 : (2 : K) ≠ 0) (h : B.compl₁₂ φ φ = c • B) (hc : c ≠ 0) (hs : s * s = c)
    (hsplit : φ.charpoly.Splits) :
    Even ((finrank K V : ℤ) - finrank K (φ.maxGenEigenspace s) -
      finrank K (φ.maxGenEigenspace (-s))) := by
  classical
  have hmap := (LinearMap.roots_charpoly_eq_map_div_of_compl₁₂_eq_smul B h hc).symm
  have h0 := LinearMap.zero_notMem_roots_charpoly_of_compl₁₂_eq_smul B h hc
  rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.finrank_maxGenEigenspace_eq, ← count_roots,
    ← count_roots, ← φ.charpoly_natDegree, hsplit.natDegree_eq_card_roots]
  exact Multiset.even_card_sub_count_sub_count_of_map_div_eq h2 hs hmap h0

/-- **The determinant of a similitude.** If `φ` is a similitude with multiplier `c` of a
perfect bilinear form `B` and `s * s = c`, then `det φ = (-1) ^ m₋ * s ^ b`, where `b` is the
dimension and `m₋` is the algebraic multiplicity of `-s` as an eigenvalue of `φ`. The form need not
be symmetric, and `φ` need not be semisimple. -/
theorem det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul (B : BilinForm K V)
    [B.IsPerfPair] (h : B.compl₁₂ φ φ = c • B) (hs : s * s = c) :
    LinearMap.det φ = (-1) ^ finrank K (φ.maxGenEigenspace (-s)) * s ^ finrank K V := by
  let L := AlgebraicClosure K
  apply (algebraMap K L).injective
  have hL := compl₁₂_baseChange_eq_smul (A := L) h
  rw [← LinearMap.det_baseChange, det_eq_neg_one_pow_mul_pow_of_splits _ hL
    (s := algebraMap K L s) (by rw [← map_mul, hs]) (IsAlgClosed.splits _), ← map_neg,
    LinearMap.finrank_maxGenEigenspace_baseChange_algebraMap, finrank_baseChange]
  simp

/-- **The determinant of a similitude, after extension of scalars.** If `φ` is a similitude with
multiplier `c` of a perfect bilinear form `B` over `K`, and `s` is a square root of `c` in a
field `L` containing `K`, then `det φ = (-1) ^ m₋ * s ^ b` in `L`, where `m₋` is the algebraic
multiplicity of `-s` as an eigenvalue of the extension of `φ` to `L`. -/
theorem algebraMap_det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul {L : Type*} [Field L]
    [Algebra K L] (B : BilinForm K V) [B.IsPerfPair] (h : B.compl₁₂ φ φ = c • B) {s : L}
    (hs : s * s = algebraMap K L c) :
    algebraMap K L (LinearMap.det φ) =
      (-1) ^ finrank L (maxGenEigenspace (φ.baseChange L) (-s)) * s ^ finrank K V := by
  rw [← LinearMap.det_baseChange, ← finrank_baseChange (R := L) (M' := V)]
  exact det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul _
    (compl₁₂_baseChange_eq_smul h) hs

/-- **Parity of the multiplicities of the square roots of the multiplier.** If `φ` is a similitude
with multiplier `c ≠ 0` of a perfect bilinear form, `s * s = c` and `2 ≠ 0`, then
`b - m₊ - m₋` is even, where `b` is the dimension and `m₊`, `m₋` are the algebraic multiplicities
of `s` and `-s` as eigenvalues of `φ`. -/
theorem even_finrank_sub_finrank_maxGenEigenspace_of_compl₁₂_self_eq_smul (B : BilinForm K V)
    [B.IsPerfPair] (h2 : (2 : K) ≠ 0) (h : B.compl₁₂ φ φ = c • B) (hc : c ≠ 0)
    (hs : s * s = c) :
    Even ((finrank K V : ℤ) - finrank K (φ.maxGenEigenspace s) -
      finrank K (φ.maxGenEigenspace (-s))) := by
  let L := AlgebraicClosure K
  have hL := compl₁₂_baseChange_eq_smul (A := L) h
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (_root_.map_ne_zero _).2 h2
  have := even_finrank_sub_of_splits _ h2L hL
    (by simpa using hc) (s := algebraMap K L s) (by rw [← map_mul, hs]) (IsAlgClosed.splits _)
  rwa [← map_neg, LinearMap.finrank_maxGenEigenspace_baseChange_algebraMap,
    LinearMap.finrank_maxGenEigenspace_baseChange_algebraMap,
    finrank_baseChange] at this

/-- **The determinant of a similitude, through the multiplicity of `s`.** If `φ` is a similitude
with multiplier `c` of a perfect bilinear form and `s * s = c`, then
`det φ = (-1) ^ (b - m₊) * s ^ b`, where `b` is the dimension and `m₊` is the algebraic
multiplicity of `s` as an eigenvalue of `φ`. -/
theorem det_eq_neg_one_pow_finrank_sub_mul_pow_of_compl₁₂_self_eq_smul (B : BilinForm K V)
    [B.IsPerfPair] (h : B.compl₁₂ φ φ = c • B) (hs : s * s = c) :
    LinearMap.det φ =
      (-1) ^ (finrank K V - finrank K (φ.maxGenEigenspace s)) * s ^ finrank K V := by
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · have h1 : (-1 : K) = 1 := by linear_combination -h2
    rw [det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul B h hs, h1, one_pow, one_pow]
  rcases eq_or_ne c 0 with rfl | hc
  · obtain rfl : s = 0 := mul_self_eq_zero.1 hs
    exact det_eq_neg_one_pow_mul_zero_pow_of_compl₁₂_self_eq_zero B h (Nat.sub_le _ _)
  rw [det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul B h hs]
  have hle := Submodule.finrank_le (φ.maxGenEigenspace s)
  have he : Even (finrank K V - finrank K (φ.maxGenEigenspace s) +
      finrank K (φ.maxGenEigenspace (-s))) := by
    have := (even_finrank_sub_finrank_maxGenEigenspace_of_compl₁₂_self_eq_smul B h2 h hc
      hs).add (even_two_mul (finrank K (φ.maxGenEigenspace (-s)) : ℤ))
    rw [← Int.even_natCast]
    push_cast [Nat.cast_sub hle]
    convert this using 1
    ring
  have he' := Nat.even_iff.1 he
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (_ - _)]
  congr 2
  omega

/-- **Generalized eigenspaces of a similitude of an alternating form at the square roots of the
multiplier have even dimension.** If `φ` is a similitude with multiplier `c ≠ 0` of a
perfect alternating form and `α * α = c`, then the algebraic multiplicity of `α` as an
eigenvalue of `φ` is even. -/
theorem even_finrank_maxGenEigenspace_of_isAlt_of_compl₁₂_self_eq_smul (B : BilinForm K V)
    [B.IsPerfPair] (halt : B.IsAlt) (h : B.compl₁₂ φ φ = c • B) (hc : c ≠ 0) {α : K}
    (hα : α * α = c) : Even (finrank K (φ.maxGenEigenspace α)) := by
  have hP := LinearMap.isPerfPair_domRestrict₁₂_maxGenEigenspace_of_compl₁₂_eq_smul B h hc hα
  exact IsAlt.even_finrank (B := B.domRestrict₁₂ (φ.maxGenEigenspace α) (φ.maxGenEigenspace α))
    (fun x ↦ by rw [LinearMap.domRestrict₁₂_apply]; exact halt.self_eq_zero _) hP.nondegenerate

/-- **The determinant of a similitude of an alternating form.** If `φ` is a similitude with
multiplier `c` of a perfect alternating form on a space of dimension `b`, then
`det φ = c ^ (b / 2)`; the dimension `b` is even. No square root of `c` is needed in `K`. -/
theorem det_eq_pow_of_isAlt_of_compl₁₂_self_eq_smul (B : BilinForm K V) [B.IsPerfPair]
    (halt : B.IsAlt) (h : B.compl₁₂ φ φ = c • B) :
    LinearMap.det φ = c ^ (finrank K V / 2) := by
  obtain ⟨k, hk⟩ := IsAlt.even_finrank halt (IsPerfPair.nondegenerate inferInstance)
  rcases eq_or_ne c 0 with rfl | hc
  · rw [det_eq_neg_one_pow_mul_zero_pow_of_compl₁₂_self_eq_zero B h (Nat.zero_le _), pow_zero,
      one_mul, hk, ← two_mul, Nat.mul_div_cancel_left _ two_pos, pow_mul, zero_pow two_ne_zero]
  let L := AlgebraicClosure K
  obtain ⟨t, ht⟩ := IsAlgClosed.isSquare (algebraMap K L c)
  apply (algebraMap K L).injective
  have hL := compl₁₂_baseChange_eq_smul (A := L) h
  have hm := even_finrank_maxGenEigenspace_of_isAlt_of_compl₁₂_self_eq_smul _
    halt.baseChange hL (by simpa using hc) (α := -t) (by rw [neg_mul_neg, ht])
  rw [algebraMap_det_eq_neg_one_pow_mul_pow_of_compl₁₂_self_eq_smul B h ht.symm,
    hm.neg_one_pow, one_mul, hk, map_pow, ht, ← two_mul, Nat.mul_div_cancel_left _ two_pos]
  ring

end LinearMap.BilinForm
