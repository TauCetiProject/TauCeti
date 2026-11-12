/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Ext.Finite
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic
public import TauCeti.Algebra.Homology.Ext.GradedDualNumbers

/-!
# The graded dual numbers: internally finite but not `Ext`-bounded

Let `k` be a field, grade the dual numbers `A = k[ε]` with `ε` in degree two, and let `S = A/(ε)`
be the graded residue field. The bigraded `Ext` groups of the pair `(S, S)` are

```text
dim_k Ext^{n,j}(S, S) = dim_k Extⁿ(S, S{j}) = 1 if j = 2n, and 0 otherwise
```

(`TauCeti.finrank_ext_dualNumberGradedResidue_shiftObj`). Hence every cohomological degree has
finite Laurent support, its target-shift graded dimension being the single monomial `q⁻²ⁿ`, so
`TauCeti.IsGradedExtInternallyFinite` holds. But no cohomological degree vanishes, so
`TauCeti.IsGradedExtBounded` fails: the truncated q-Euler sums are the partial sums
`∑ n < N, (-1)ⁿ q⁻²ⁿ`, which never stabilize. This separates the two halves of
`TauCeti.IsGradedEulerAdmissible` in the graded setting, as `TauCeti.isExtFinite_dualNumberResidue`
and `TauCeti.not_isExtBounded_dualNumberResidue` do in the ungraded one. Because
`TauCeti.gradedExtEuler` consumes a proof of admissibility, no q-Euler value of `(S, S)` is defined.

## Main results

* `TauCeti.finrank_gradedExt_dualNumberGradedResidue`: `dim_k Ext^{n,j}(S, S)` is `1` if `j = 2n`
  and `0` otherwise.
* `TauCeti.isGradedExtInternallyFinite_dualNumberGradedResidue`: each cohomological degree has
  finite internal support.
* `TauCeti.gradedExtDimension_dualNumberGradedResidue`: the graded dimension of `Extⁿ` is `q⁻²ⁿ`.
* `TauCeti.truncatedGradedExtEuler_dualNumberGradedResidue`: the truncated q-Euler sums are
  `∑ n < N, (-1)ⁿ q⁻²ⁿ`.
* `TauCeti.not_isGradedExtBounded_dualNumberGradedResidue`: no cohomological degree bounds the
  support of `(S, S)`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5 and Chapter 4.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for the bigraded Ext-Euler form.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w u

attribute [local instance] dualNumberIntegerGradedAlgebra

variable (k : Type u) [Field k] [HasExt.{w} (GradedModuleCat.{u} (dualNumberIntegerGrade k))]

/-- **`dim_k Ext^{n,j}(S, S)` is `1` if `j = 2n` and `0` otherwise**, for the graded residue field
`S` of the dual numbers with `ε` in degree two. -/
theorem finrank_gradedExt_dualNumberGradedResidue (n : ℕ) (j : ℤ) :
    Module.finrank k (GradedExt.{w} (GradedModuleCat.shift (dualNumberIntegerGrade k))
        (dualNumberGradedResidue k) (dualNumberGradedResidue k) n j) =
      if j = 2 * n then 1 else 0 := by
  rw [(extLinearEquivOfIso k (Iso.refl _)
      ((GradedModuleCat.shiftPowIso (dualNumberIntegerGrade k) j).app
        (dualNumberGradedResidue k)) n).finrank_eq,
    GradedModuleCat.shiftFunctor_obj, finrank_ext_dualNumberGradedResidue_shiftObj]

/-- Every bigraded `Ext` group of the graded residue field of `k[ε]` against itself is
finite-dimensional, and each cohomological degree has finite internal support. -/
theorem isGradedExtInternallyFinite_dualNumberGradedResidue :
    IsGradedExtInternallyFinite.{w} k (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (dualNumberGradedResidue k) (dualNumberGradedResidue k) :=
  GradedModuleCat.isGradedExtInternallyFinite_of_finite _ _

/-- Off the internal degree `2n`, the bigraded group `Ext^{n,j}(S, S)` vanishes. -/
theorem subsingleton_gradedExt_dualNumberGradedResidue {n : ℕ} {j : ℤ} (hj : j ≠ 2 * n) :
    Subsingleton (GradedExt.{w} (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (dualNumberGradedResidue k) (dualNumberGradedResidue k) n j) := by
  have := ((isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k).finiteLaurentSupport
    n).finiteDimensional j
  rw [← Module.finrank_zero_iff (R := k), finrank_gradedExt_dualNumberGradedResidue]
  simp [hj]

/-- **The graded dimension of `Extⁿ(S, S)` is the single monomial `q⁻²ⁿ`**, for the graded residue
field `S` of `k[ε]` with `ε` in degree two. -/
theorem gradedExtDimension_dualNumberGradedResidue (n : ℕ) :
    gradedExtDimension k (GradedModuleCat.shift (dualNumberIntegerGrade k))
        ((isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k).finiteLaurentSupport n) =
      T (-(2 * n : ℤ)) := by
  rw [gradedExtDimension_eq_targetShiftGradedDimension,
    targetShiftGradedDimension_eq_sum _ {(2 * n : ℤ)} fun j hj =>
      subsingleton_gradedExt_dualNumberGradedResidue k (Finset.notMem_singleton.1 hj),
    Finset.sum_singleton, finrank_gradedExt_dualNumberGradedResidue]
  simp

/-- **The truncated q-Euler sums of `(S, S)` are `∑ n < N, (-1)ⁿ q⁻²ⁿ`**: each cohomological degree
contributes a new monomial, so the truncations never stabilize. -/
theorem truncatedGradedExtEuler_dualNumberGradedResidue (N : ℕ) :
    truncatedGradedExtEuler k (GradedModuleCat.shift (dualNumberIntegerGrade k))
        (isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k) N =
      ∑ n ∈ Finset.range N, ((-1 : ℤ) ^ n) • T (-(2 * n : ℤ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [truncatedGradedExtEuler_succ, ih, gradedExtDimension_dualNumberGradedResidue,
      Finset.sum_range_succ]

/-- No cohomological degree is a uniform vanishing bound for the bigraded `Ext` groups of the
graded residue field of `k[ε]` against itself: `Ext^{N,2N}(S, S)` is one-dimensional. -/
theorem not_isGradedExtBoundedBy_dualNumberGradedResidue (N : ℕ) :
    ¬ IsGradedExtBoundedBy.{w} (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (dualNumberGradedResidue k) (dualNumberGradedResidue k) N := fun h => by
  have := h.subsingleton le_rfl (2 * N)
  have h1 := finrank_gradedExt_dualNumberGradedResidue.{w} k N (2 * N)
  rw [Module.finrank_zero_of_subsingleton] at h1
  simp at h1

/-- **The graded dual-numbers rejection, cohomological half.** The bigraded `Ext` groups of the
graded residue field `S` of `k[ε]` against itself never vanish, so `(S, S)` is not graded
`Ext`-bounded, although it is internally finite
(`TauCeti.isGradedExtInternallyFinite_dualNumberGradedResidue`). -/
theorem not_isGradedExtBounded_dualNumberGradedResidue :
    ¬ IsGradedExtBounded.{w} (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (dualNumberGradedResidue k) (dualNumberGradedResidue k) := fun ⟨N, hN⟩ =>
  not_isGradedExtBoundedBy_dualNumberGradedResidue k N hN

end TauCeti
