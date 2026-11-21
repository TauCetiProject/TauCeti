/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.Algebra.Star.SelfAdjoint.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Complex
import TauCeti.LinearAlgebra.Matrix.Kronecker.MulLeftMulRight

/-!
# The congruence action on hermitian matrices over a quadratic algebra

Let `E` be a commutative algebra over a field `F` with an involution `star` whose fixed ring is
`F`, and which has a unit `t` with `star t = -t`; for instance a quadratic étale algebra `E / F`
in characteristic different from `2` with its nontrivial involution. A matrix `C : Matrix n n E`
acts on the hermitian matrices, and on the skew-hermitian matrices, by the congruence
`Y ↦ C * Y * Cᴴ`. These are `F`-vector spaces of dimension `n ^ 2`
(`Matrix.finrank_selfAdjoint_submodule`, `Matrix.finrank_skewAdjoint_submodule`), and the
congruence has `F`-determinant `N_{E/F}(det C) ^ n` on both
(`Matrix.det_selfAdjointConjugate`, `Matrix.det_skewAdjointConjugate`).

This is the determinant that computes the modulus character of the Siegel parabolic subgroup of a
unitary group in `2 n` variables: the unipotent radical is a space of `n × n` hermitian (or
skew-hermitian) matrices, and the Levi factor acts on it by `Y ↦ λ • C * Y * Cᴴ`, with
`F`-determinant `λ ^ (n ^ 2) * N_{E/F}(det C) ^ n` (`Matrix.det_smul_selfAdjointConjugate`).
Over `ℂ / ℝ` the norm is `Complex.normSq` (`Matrix.det_selfAdjointConjugate_complex`).

## References

* E. Eischen, M. Harris, J.-S. Li, C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), §4.1.
-/

public section

open scoped Matrix

open Module (finrank)

namespace Matrix

variable {F E : Type*} [Field F] [StarMul F] [TrivialStar F] [CommRing E] [StarRing E]
  [Algebra F E] [StarModule F E] {n : Type*} [Fintype n]

/-- The congruence `Y ↦ C * Y * Cᴴ` commutes with conjugate transposition. -/
theorem mulLeft_comp_mulRight_conjTranspose_star (C Y : Matrix n n E) :
    (LinearMap.mulLeft E C ∘ₗ LinearMap.mulRight E Cᴴ) (star Y) =
      star ((LinearMap.mulLeft E C ∘ₗ LinearMap.mulRight E Cᴴ) Y) := by
  simp [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

variable (F) in
/-- The congruence action `Y ↦ C * Y * Cᴴ` of a matrix `C` over `E` on the hermitian matrices,
as an `F`-linear map. -/
def selfAdjointConjugate (C : Matrix n n E) :
    selfAdjoint.submodule F (Matrix n n E) →ₗ[F] selfAdjoint.submodule F (Matrix n n E) :=
  (LinearMap.mulLeft E C ∘ₗ LinearMap.mulRight E Cᴴ).restrictSelfAdjoint F
    (mulLeft_comp_mulRight_conjTranspose_star C)

@[simp]
theorem coe_selfAdjointConjugate_apply (C : Matrix n n E)
    (Y : selfAdjoint.submodule F (Matrix n n E)) :
    (selfAdjointConjugate F C Y : Matrix n n E) = C * Y * Cᴴ := by
  simp [selfAdjointConjugate, Matrix.mul_assoc]

variable (F) in
/-- The congruence action `Y ↦ C * Y * Cᴴ` of a matrix `C` over `E` on the skew-hermitian
matrices, as an `F`-linear map. -/
def skewAdjointConjugate (C : Matrix n n E) :
    skewAdjoint.submodule F (Matrix n n E) →ₗ[F] skewAdjoint.submodule F (Matrix n n E) :=
  (LinearMap.mulLeft E C ∘ₗ LinearMap.mulRight E Cᴴ).restrictSkewAdjoint F
    (mulLeft_comp_mulRight_conjTranspose_star C)

@[simp]
theorem coe_skewAdjointConjugate_apply (C : Matrix n n E)
    (Y : skewAdjoint.submodule F (Matrix n n E)) :
    (skewAdjointConjugate F C Y : Matrix n n E) = C * Y * Cᴴ := by
  simp [skewAdjointConjugate, Matrix.mul_assoc]

section Dimension

variable [Nontrivial E] {t : Eˣ}

variable (F E n) in
/-- The hermitian `n × n` matrices over `E` form an `F`-vector space of dimension `n ^ 2`. -/
theorem finrank_selfAdjoint_submodule [Invertible (2 : F)]
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) :
    finrank F (selfAdjoint.submodule F (Matrix n n E)) = Fintype.card n ^ 2 := by
  rw [TauCeti.finrank_selfAdjoint_submodule_eq F (Matrix n n E) hfix ht, Module.finrank_matrix,
    Module.finrank_self, mul_one, sq]

variable (F E n) in
/-- The skew-hermitian `n × n` matrices over `E` form an `F`-vector space of dimension `n ^ 2`. -/
theorem finrank_skewAdjoint_submodule [Invertible (2 : F)]
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) :
    finrank F (skewAdjoint.submodule F (Matrix n n E)) = Fintype.card n ^ 2 := by
  rw [(TauCeti.skewAdjointEquivSelfAdjoint t ht).finrank_eq,
    finrank_selfAdjoint_submodule F E n hfix ht]

end Dimension

section Determinant

variable [DecidableEq n] [Invertible (2 : F)] {t : Eˣ}

/-- **The determinant of the congruence action on hermitian matrices**: `Y ↦ C * Y * Cᴴ` has
`F`-determinant `N_{E/F}(det C) ^ n`. -/
theorem det_selfAdjointConjugate
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (C : Matrix n n E) :
    LinearMap.det (selfAdjointConjugate F C) = Algebra.norm F C.det ^ Fintype.card n := by
  cases subsingleton_or_nontrivial E
  · rw [LinearMap.det_eq_one_of_subsingleton, Subsingleton.elim C.det 1, map_one, one_pow]
  refine (algebraMap F E).injective ?_
  rw [selfAdjointConjugate, LinearMap.algebraMap_det_restrictSelfAdjoint hfix ht,
    det_mulLeft_comp_mulRight, det_conjTranspose, map_pow,
    TauCeti.algebraMap_norm_eq_star_mul_self hfix ht, mul_pow, mul_comm]

/-- **The determinant of the congruence action on skew-hermitian matrices**: `Y ↦ C * Y * Cᴴ`
has `F`-determinant `N_{E/F}(det C) ^ n`. -/
theorem det_skewAdjointConjugate
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (C : Matrix n n E) :
    LinearMap.det (skewAdjointConjugate F C) = Algebra.norm F C.det ^ Fintype.card n := by
  rw [skewAdjointConjugate, LinearMap.det_restrictSkewAdjoint ht, ← selfAdjointConjugate,
    det_selfAdjointConjugate hfix ht]

/-- **The modulus of the Siegel Levi action**: the scaled congruence `Y ↦ a • (C * Y * Cᴴ)`
on hermitian matrices has `F`-determinant `a ^ (n ^ 2) * N_{E/F}(det C) ^ n`. -/
theorem det_smul_selfAdjointConjugate [Nontrivial E]
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (a : F) (C : Matrix n n E) :
    LinearMap.det (a • selfAdjointConjugate F C) =
      a ^ Fintype.card n ^ 2 * Algebra.norm F C.det ^ Fintype.card n := by
  rw [LinearMap.det_smul, finrank_selfAdjoint_submodule F E n hfix ht,
    det_selfAdjointConjugate hfix ht]

/-- **The modulus of the Siegel Levi action on skew-hermitian matrices**: the scaled congruence
`Y ↦ a • (C * Y * Cᴴ)` has `F`-determinant `a ^ (n ^ 2) * N_{E/F}(det C) ^ n`. -/
theorem det_smul_skewAdjointConjugate [Nontrivial E]
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (a : F) (C : Matrix n n E) :
    LinearMap.det (a • skewAdjointConjugate F C) =
      a ^ Fintype.card n ^ 2 * Algebra.norm F C.det ^ Fintype.card n := by
  rw [LinearMap.det_smul, finrank_skewAdjoint_submodule F E n hfix ht,
    det_skewAdjointConjugate hfix ht]

end Determinant

/-- **The congruence action on complex hermitian matrices**: over `ℂ / ℝ`, `Y ↦ C * Y * Cᴴ` has
real determinant `|det C| ^ (2 n)`, written `normSq (det C) ^ n`. -/
theorem det_selfAdjointConjugate_complex [DecidableEq n] (C : Matrix n n ℂ) :
    LinearMap.det (selfAdjointConjugate ℝ C) = Complex.normSq C.det ^ Fintype.card n := by
  rw [← Algebra.norm_complex_apply]
  refine det_selfAdjointConjugate (fun c hc ↦ ⟨c.re, Complex.conj_eq_iff_re.mp hc⟩)
    (t := Units.mk0 Complex.I Complex.I_ne_zero) ?_ C
  simp [skewAdjoint.mem_iff]

end Matrix
