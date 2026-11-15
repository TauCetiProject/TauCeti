/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Operator
import Mathlib.Data.Fin.Tuple.Reflection
import TauCeti.LinearAlgebra.Multilinear.CurvatureDimThree

/-!
# The Ricci–Weyl decomposition of algebraic curvature tensors

On a finite-dimensional real inner product space `V` of dimension `n := Module.finrank ℝ V`,
`algebraicCurvatureSubmodule V` splits into three pairwise orthogonal, `O(V)`-invariant subspaces
(`scalarPart r + tracelessRicciPart r + weyl r = r`):
* `scalarPart r = (scalar r / (n (n - 1))) • constantCurvature V`, acting on `⋀[ℝ]^2 V` as
  `(scalar r / (n (n - 1))) • Id`;
* `tracelessRicciPart r = (n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)`, carrying
  `tracelessRicci r = ricci r - (scalar r / n) • innerₗ V` and acting on `⋀[ℝ]^2 V` as
  `(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`;
* `weyl r = r - scalarPart r - tracelessRicciPart r`, Ricci- and scalar-flat in all dimensions,
  equal to `r - kulkarniNomizu (schouten r) (innerₗ V)` for `n ≠ 2`, and zero for `n ≤ 3`.

For `n ≥ 4` these `O(V)`-subspaces are irreducible (`weyl` splitting further only under `SO(4)` at
`n = 4`), diagonalizing quadratic curvature norms and Ricci-flow reaction terms; for `n ≤ 3` the
vanishing of `weyl` shows curvature is determined by Ricci curvature. Via `0⁻¹ = 0` in `ℝ`,
`scalarPart`, `tracelessRicciPart`, and `weyl` need no dimension hypotheses and remain valid on
algebraic curvature tensors for all `n`, whereas `schouten` is the `n ≥ 3` Schouten tensor that
evaluates to `0` at `n = 2` (and drops its scalar term at `n = 1`), explaining why `weyl` is built
from `scalarPart` and `tracelessRicciPart`.

## Main definitions

* `TauCeti.FourTensor.ricciEnd`: Riesz endomorphism representing `ricci r`.
* `TauCeti.FourTensor.tracelessRicci`, `TauCeti.FourTensor.tracelessRicciEnd`: trace-free Ricci form
  `Ric(r) - (Scal(r) / n) g` and its Riesz endomorphism.
* `TauCeti.FourTensor.scalarPart`, `TauCeti.FourTensor.tracelessRicciPart`,
  `TauCeti.FourTensor.weyl`: scalar, trace-free Ricci, and Weyl curvature components.
* `TauCeti.FourTensor.schouten`: Schouten form `(n - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (n - 1))) g)`.

## Main statements

* `TauCeti.FourTensor.scalarPart_add_tracelessRicciPart_add_weyl`: additive splitting
  `scalarPart r + tracelessRicciPart r + weyl r = r`.
* `TauCeti.FourTensor.curvatureOperator_scalarPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_tracelessRicciPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_eq`: bivector operator decomposition.
* `TauCeti.FourTensor.ricci_weyl`, `TauCeti.FourTensor.scalar_weyl`, `TauCeti.FourTensor.weyl_weyl`,
  `TauCeti.FourTensor.weyl_kulkarniNomizu_innerₗ`,
  `TauCeti.FourTensor.weyl_eq_sub_kulkarniNomizu_schouten`: trace-freeness, idempotence, vanishing
  on `h ⊙ g`, and Schouten formula for `weyl`.
* `TauCeti.FourTensor.weyl_eq_zero_of_finrank_le_three`,
  `TauCeti.FourTensor.eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three`: vanishing of `weyl`
  and recovery of `r` from Ricci curvature when `Module.finrank ℝ V ≤ 3`.
* `TauCeti.FourTensor.scalarPart_compContinuousLinearMap_linearIsometryEquiv`,
  `TauCeti.FourTensor.tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv`,
  `TauCeti.FourTensor.weyl_compContinuousLinearMap_linearIsometryEquiv` (and companions for
  `ricciEnd`, `tracelessRicci`, `tracelessRicciEnd`, `schouten`): `O(V)`-equivariance under
  `W ≃ₗᵢ[ℝ] V`.
* `TauCeti.FourTensor.sum_kulkarniNomizu_innerₗ_mul`, `TauCeti.FourTensor.sum_sq_eq_add`,
  `TauCeti.FourTensor.sum_sq_eq_scalar_add_tracelessRicci_add_weyl`: contraction adjointness and
  orthogonal Pythagorean norm decomposition.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G, Propositions 1.116–1.120.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. (2) 167 (2008), 1079–1097, Section 1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7, Theorem 7.30.
* I. M. Singer and J. A. Thorpe, *The curvature of 4-dimensional Einstein spaces*, in *Global
  Analysis (Papers in Honor of K. Kodaira)*, Princeton Univ. Press (1969), 355–365.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem finrank_sub_one_ne_zero (h : Module.finrank ℝ V ≠ 1) :
    (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)

omit [FiniteDimensional ℝ V] in
private theorem finrank_sub_two_ne_zero (h : Module.finrank ℝ V ≠ 2) :
    (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)

private theorem eq_zero_of_finrank_eq_zero (hn : Module.finrank ℝ V = 0) (r : FourTensor V) :
    r = 0 := by
  have := Module.finrank_zero_iff.mp hn
  ext m; exact r.map_coord_zero (0 : Fin 4) (Subsingleton.elim (m 0) 0)

private theorem bilinForm_eq_zero_of_finrank_eq_zero (hn : Module.finrank ℝ V = 0)
    (B : BilinForm ℝ V) : B = 0 := by
  have := Module.finrank_zero_iff.mp hn; ext u v; rw [Subsingleton.elim u 0]; simp

omit [FiniteDimensional ℝ V] in
private theorem end_ext_innerₗ {A B : Module.End ℝ V} (h : innerₗ V ∘ₗ A = innerₗ V ∘ₗ B) :
    A = B := LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ congr($h u v)

/-! ### The Ricci and trace-free Ricci endomorphisms -/

/-- The Ricci endomorphism on `V` associated with a four-tensor `r`, characterized by
`⟪ricciEnd r u, v⟫ = ricci r u v`. -/
def ricciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V where
  toFun r := (ricci r).symmCompOfNondegenerate (innerₗ V) TauCeti.nondegenerate_inner
  map_add' _ _ := LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp [inner_add_left, ← innerₗ_apply_apply]
  map_smul' _ _ := LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by simp [← innerₗ_apply_apply]

@[simp] theorem inner_ricciEnd_left (r : FourTensor V) (u v : V) :
    ⟪ricciEnd r u, v⟫ = ricci r u v :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (ricci r) TauCeti.nondegenerate_inner v u
@[simp] theorem innerₗ_comp_ricciEnd (r : FourTensor V) : innerₗ V ∘ₗ ricciEnd r = ricci r :=
  LinearMap.ext₂ (inner_ricciEnd_left r)
@[simp] theorem ricciEnd_eq_zero_iff {r : FourTensor V} : ricciEnd r = 0 ↔ ricci r = 0 :=
  ⟨fun h ↦ by simp [← innerₗ_comp_ricciEnd, h], fun h ↦ end_ext_innerₗ (by simp [h])⟩

/-- For an algebraic curvature tensor `r`, `ricciEnd r` is symmetric on `V`. -/
theorem IsAlgebraicCurvature.isSymmetric_ricciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (ricciEnd r).IsSymmetric := fun u v ↦ by
  rw [inner_ricciEnd_left, real_inner_comm, inner_ricciEnd_left, hr.isSymm_ricci.eq]
theorem IsAlgebraicCurvature.inner_ricciEnd_right {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v : V) : ⟪u, ricciEnd r v⟫ = ricci r u v := by
  rw [← hr.isSymmetric_ricciEnd u v, inner_ricciEnd_left]

/-- The operator trace of `ricciEnd r` equals the scalar contraction `scalar r`. -/
@[simp] theorem trace_ricciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (ricciEnd r) = scalar r := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, scalar_apply, bilinFormTrace_eq_sum _ b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, inner_ricciEnd_left]

@[simp] theorem ricciEnd_constantCurvature :
    ricciEnd (constantCurvature V) = ((Module.finrank ℝ V : ℝ) - 1) • LinearMap.id :=
  end_ext_innerₗ (by ext; simp [ricci_constantCurvature])

/-- The trace-free Ricci bilinear form `Ric₀(r) = Ric(r) - (Scal(r) / n) g`. -/
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ricci (V := V) + ((-((Module.finrank ℝ V : ℝ)⁻¹ • scalar (V := V))).smulRight (innerₗ V) :
    FourTensor V →ₗ[ℝ] BilinForm ℝ V)

theorem tracelessRicci_apply (r : FourTensor V) :
    tracelessRicci r = ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V := by
  ext; simp only [tracelessRicci, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.neg_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
@[simp] theorem tracelessRicci_apply_apply (r : FourTensor V) (u v : V) :
    tracelessRicci r u v = ricci r u v - scalar r / Module.finrank ℝ V * ⟪u, v⟫ := by
  simp [tracelessRicci_apply]

/-- The metric trace of `tracelessRicci r` vanishes for every four-tensor `r`. -/
@[simp] theorem bilinFormTrace_tracelessRicci (r : FourTensor V) :
    bilinFormTrace (tracelessRicci r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · rw [bilinForm_eq_zero_of_finrank_eq_zero hn (tracelessRicci r), map_zero]
  · let b := stdOrthonormalBasis ℝ V
    rw [bilinFormTrace_eq_sum _ b]
    simp [Finset.sum_sub_distrib, ← bilinFormTrace_eq_sum (ricci r) b, ← scalar_apply,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn : (Module.finrank ℝ V : ℝ) ≠ 0)]

/-- For an algebraic curvature tensor `r`, `tracelessRicci r` is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm :=
  ⟨fun u v ↦ by simp [hr.isSymm_ricci.eq u v, real_inner_comm u v]⟩

@[simp] theorem tracelessRicci_constantCurvature : tracelessRicci (constantCurvature V) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn | hn
  · exact bilinForm_eq_zero_of_finrank_eq_zero hn _
  · ext u v; simp [ricci_constantCurvature, scalar_constantCurvature,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn : (Module.finrank ℝ V : ℝ) ≠ 0)]

/-- The trace-free Ricci endomorphism `ricciEnd r - (scalar r / n) • Id` on `V`. -/
def tracelessRicciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  ricciEnd (V := V) - ((Module.finrank ℝ V : ℝ)⁻¹ • scalar (V := V)).smulRight LinearMap.id

theorem tracelessRicciEnd_apply (r : FourTensor V) :
    tracelessRicciEnd r = ricciEnd r - (scalar r / Module.finrank ℝ V) • LinearMap.id := by
  ext u; simp [tracelessRicciEnd, div_eq_inv_mul]
theorem tracelessRicciEnd_apply_apply (r : FourTensor V) (u : V) :
    tracelessRicciEnd r u = ricciEnd r u - (scalar r / Module.finrank ℝ V) • u := by
  simp [tracelessRicciEnd_apply]

@[simp] theorem inner_tracelessRicciEnd_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEnd r u, v⟫ = tracelessRicci r u v := by
  simp [tracelessRicciEnd_apply, inner_sub_left, real_inner_smul_left]
@[simp] theorem innerₗ_comp_tracelessRicciEnd (r : FourTensor V) :
    innerₗ V ∘ₗ tracelessRicciEnd r = tracelessRicci r :=
  LinearMap.ext₂ (inner_tracelessRicciEnd_left r)
@[simp] theorem tracelessRicciEnd_eq_zero_iff {r : FourTensor V} :
    tracelessRicciEnd r = 0 ↔ tracelessRicci r = 0 :=
  ⟨fun h ↦ by simp [← innerₗ_comp_tracelessRicciEnd, h], fun h ↦ end_ext_innerₗ (by simp [h])⟩

/-- For an algebraic curvature tensor `r`, `tracelessRicciEnd r` is symmetric on `V`. -/
theorem IsAlgebraicCurvature.isSymmetric_tracelessRicciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicciEnd r).IsSymmetric := fun u v ↦ by
  rw [inner_tracelessRicciEnd_left, real_inner_comm, inner_tracelessRicciEnd_left,
    hr.isSymm_tracelessRicci.eq]
theorem IsAlgebraicCurvature.inner_tracelessRicciEnd_right {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v : V) :
    ⟪u, tracelessRicciEnd r v⟫ = tracelessRicci r u v := by
  rw [← hr.isSymmetric_tracelessRicciEnd u v, inner_tracelessRicciEnd_left]

/-- The operator trace of `tracelessRicciEnd r` vanishes for every four-tensor `r`. -/
@[simp] theorem trace_tracelessRicciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (tracelessRicciEnd r) = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, ← bilinFormTrace_tracelessRicci r,
    bilinFormTrace_eq_sum _ b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, inner_tracelessRicciEnd_left]
@[simp] theorem tracelessRicciEnd_constantCurvature : tracelessRicciEnd (constantCurvature V) = 0 :=
  tracelessRicciEnd_eq_zero_iff.mpr tracelessRicci_constantCurvature

/-! ### The scalar, trace-free Ricci, Schouten, and Weyl components -/

/-- The scalar curvature component `(scalar r / (n (n - 1))) • constantCurvature V`. When `n ≤ 1`,
`0⁻¹ = 0` gives `scalarPart r = 0`, matching the vanishing of skew-pair tensors for `n ≤ 1`. -/
def scalarPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  (((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar (V := V)).smulRight
    (constantCurvature V)

theorem scalarPart_apply (r : FourTensor V) :
    scalarPart r = (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
      constantCurvature V := by ext; simp [scalarPart, div_eq_inv_mul]

/-- `scalarPart r` is an algebraic curvature tensor for every four-tensor `r`. -/
theorem isAlgebraicCurvature_scalarPart (r : FourTensor V) : IsAlgebraicCurvature (scalarPart r) :=
  scalarPart_apply r ▸ mem_algebraicCurvatureSubmodule.mp ((algebraicCurvatureSubmodule V).smul_mem
    _ (mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature))

/-- The trace-free Ricci component `(n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)`. When
`n = 2`, `(2 - 2)⁻¹ = 0` gives `tracelessRicciPart r = 0`, matching `tracelessRicci r = 0`. -/
def tracelessRicciPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (kulkarniNomizu.flip (innerₗ V) ∘ₗ tracelessRicci (V := V))

theorem tracelessRicciPart_apply (r : FourTensor V) :
    tracelessRicciPart r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V) := (rfl)

/-- `tracelessRicciPart r` is an algebraic curvature tensor whenever `r` is. -/
theorem IsAlgebraicCurvature.tracelessRicciPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
  mem_algebraicCurvatureSubmodule.mp ((algebraicCurvatureSubmodule V).smul_mem _
    (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_kulkarniNomizu
      hr.isSymm_tracelessRicci (BilinForm.isSymm_iff.mpr isSymm_inner))))

/-- `tracelessRicciPart r` is antisymmetric in its first two arguments for every four-tensor `r`. -/
theorem tracelessRicciPart_antisymm_first (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![v, u, z, w] := by
  rw [tracelessRicciPart_apply, smul_apply, smul_apply, kulkarniNomizu_antisymm_first, smul_neg]

/-- `tracelessRicciPart r` is antisymmetric in its last two arguments for every four-tensor `r`. -/
theorem tracelessRicciPart_antisymm_last (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![u, v, w, z] := by
  rw [tracelessRicciPart_apply, smul_apply, smul_apply, kulkarniNomizu_antisymm_last, smul_neg]

/-- The Schouten bilinear form `P(r) = (n - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (n - 1))) g)`.
This is the classical `n ≥ 3` Schouten tensor; because `0⁻¹ = 0` in `ℝ`, `schouten r` evaluates to
`0` when `n = 2` (even for `constantCurvature V`) and drops its scalar term when `n = 1`. -/
def schouten : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (ricci (V := V) +
    ((-((2 * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar (V := V))).smulRight (innerₗ V) :
      FourTensor V →ₗ[ℝ] BilinForm ℝ V))

theorem schouten_apply (r : FourTensor V) :
    schouten r = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
      (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V) := by
  ext; simp only [schouten, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.neg_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
@[simp] theorem schouten_apply_apply (r : FourTensor V) (u v : V) :
    schouten r u v = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ *
      (ricci r u v - scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) * ⟪u, v⟫) := by
  simp [schouten_apply]

/-- For an algebraic curvature tensor `r`, `schouten r` is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_schouten {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (schouten r).IsSymm := ⟨fun u v ↦ by simp [hr.isSymm_ricci.eq u v, real_inner_comm u v]⟩

/-- The Weyl component `r - scalarPart r - tracelessRicciPart r`. Defining `weyl` from `scalarPart`
and `tracelessRicciPart` (rather than `schouten`) keeps `weyl r` Ricci- and scalar-flat on algebraic
curvature tensors in every dimension, including `n = 2`. -/
def weyl : FourTensor V →ₗ[ℝ] FourTensor V := LinearMap.id - scalarPart - tracelessRicciPart

theorem weyl_apply (r : FourTensor V) : weyl r = r - scalarPart r - tracelessRicciPart r := (rfl)

/-- **Ricci–Weyl decomposition**: every four-tensor is the sum of its scalar, trace-free Ricci, and
Weyl parts. -/
theorem scalarPart_add_tracelessRicciPart_add_weyl (r : FourTensor V) :
    scalarPart r + tracelessRicciPart r + weyl r = r := by rw [weyl_apply]; abel

/-- The Weyl component of an algebraic curvature tensor is an algebraic curvature tensor. -/
theorem IsAlgebraicCurvature.weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.weyl r) :=
  mem_algebraicCurvatureSubmodule.mp ((algebraicCurvatureSubmodule V).sub_mem
    ((algebraicCurvatureSubmodule V).sub_mem (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)))
    (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart))

theorem weyl_antisymm_first {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) (u v z w : V) :
    weyl r ![u, v, z, w] = -weyl r ![v, u, z, w] := by
  simp only [weyl_apply, sub_apply, hr₁ u v z w,
    (isAlgebraicCurvature_scalarPart r).antisymm_first u v z w,
    tracelessRicciPart_antisymm_first r u v z w]; ring
theorem weyl_antisymm_last {r : FourTensor V}
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    weyl r ![u, v, z, w] = -weyl r ![u, v, w, z] := by
  simp only [weyl_apply, sub_apply, hr₂ u v z w,
    (isAlgebraicCurvature_scalarPart r).antisymm_last u v z w,
    tracelessRicciPart_antisymm_last r u v z w]; ring

/-! ### Bivector curvature operators of the decomposition pieces -/

/-- The scalar curvature component acts on `⋀[ℝ]^2 V` as `(scalar r / (n (n - 1))) • Id`. -/
@[simp] theorem curvatureOperator_scalarPart (r : FourTensor V) :
    curvatureOperator ⟨scalarPart r, mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_scalarPart r)⟩ =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) • LinearMap.id :=
  ofExteriorEnd_injective <| by simp [scalarPart_apply]

/-- The trace-free Ricci component acts on `⋀[ℝ]^2 V` as
`(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`. -/
theorem IsAlgebraicCurvature.curvatureOperator_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureOperator ⟨FourTensor.tracelessRicciPart r,
      mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart⟩ =
      (2 / ((Module.finrank ℝ V : ℝ) - 2)) • wedgeEnd (tracelessRicciEnd r) LinearMap.id := by
  rw [curvatureOperator_eq_iff]; intro u v z w
  simp only [LinearMap.smul_apply, real_inner_smul_left, inner_wedgeEnd_ιMulti,
    innerₗ_comp_tracelessRicciEnd, LinearMap.comp_id, tracelessRicciPart_apply, smul_apply,
    smul_eq_mul]; ring

/-- **Bivector operator decomposition**: `curvatureOperator r` splits into its scalar multiple of
`Id`, `(2 / (n - 2)) • wedgeEnd (tracelessRicciEnd r) Id`, and the Weyl operator. -/
theorem IsAlgebraicCurvature.curvatureOperator_eq {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureOperator ⟨r, mem_algebraicCurvatureSubmodule.mpr hr⟩ =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) • LinearMap.id +
        (2 / ((Module.finrank ℝ V : ℝ) - 2)) • wedgeEnd (tracelessRicciEnd r) LinearMap.id +
        curvatureOperator ⟨FourTensor.weyl r, mem_algebraicCurvatureSubmodule.mpr hr.weyl⟩ := by
  rw [← curvatureOperator_scalarPart, ← hr.curvatureOperator_tracelessRicciPart, ← map_add,
    ← map_add]
  exact congrArg curvatureOperator (Subtype.ext (scalarPart_add_tracelessRicciPart_add_weyl r).symm)

/-! ### Contractions, idempotence, and mutual annihilation -/

@[simp] theorem scalarPart_constantCurvature :
    scalarPart (constantCurvature V) = constantCurvature V := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · simp [isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hn]
  · rw [scalarPart_apply, scalar_constantCurvature,
      div_self (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
        (finrank_sub_one_ne_zero (by omega))), one_smul]
@[simp] theorem scalarPart_scalarPart (r : FourTensor V) :
    scalarPart (scalarPart r) = scalarPart r := by
  rw [scalarPart_apply r, map_smul, scalarPart_constantCurvature]
@[simp] theorem tracelessRicci_scalarPart (r : FourTensor V) :
    tracelessRicci (scalarPart r) = 0 := by
  rw [scalarPart_apply, map_smul, tracelessRicci_constantCurvature, smul_zero]
@[simp] theorem tracelessRicciEnd_scalarPart (r : FourTensor V) :
    tracelessRicciEnd (scalarPart r) = 0 :=
  tracelessRicciEnd_eq_zero_iff.mpr (tracelessRicci_scalarPart r)
@[simp] theorem tracelessRicciPart_constantCurvature :
    tracelessRicciPart (constantCurvature V) = 0 := by simp [tracelessRicciPart_apply]
@[simp] theorem tracelessRicciPart_scalarPart (r : FourTensor V) :
    tracelessRicciPart (scalarPart r) = 0 := by simp [tracelessRicciPart_apply]

/-- Away from dimension `1`, `ricci (scalarPart r) = (scalar r / n) • innerₗ V`. -/
theorem ricci_scalarPart_of_finrank_ne_one (hn : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn0 | hn0
  · simp [eq_zero_of_finrank_eq_zero hn0 r, bilinForm_eq_zero_of_finrank_eq_zero hn0 (innerₗ V)]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have := finrank_sub_one_ne_zero hn
    rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]; congr 1; field_simp
/-- If `r` is antisymmetric in its first pair, `ricci (scalarPart r) = (scalar r / n) • g`. -/
theorem ricci_scalarPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  rcases eq_or_ne (Module.finrank ℝ V) 1 with hn1 | hn1
  · simp [eq_zero_of_antisymm_first_of_finrank_le_one hn1.le hr₁]
  · exact ricci_scalarPart_of_finrank_ne_one hn1 r
/-- For an algebraic curvature tensor `r`, `ricci (scalarPart r) = (scalar r / n) • innerₗ V`. -/
theorem IsAlgebraicCurvature.ricci_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V :=
  FourTensor.ricci_scalarPart hr.antisymm_first
theorem ricciEnd_scalarPart_of_finrank_ne_one (hn : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    ricciEnd (scalarPart r) = (scalar r / Module.finrank ℝ V) • LinearMap.id :=
  end_ext_innerₗ (by ext; simp [ricci_scalarPart_of_finrank_ne_one hn r])
theorem ricciEnd_scalarPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    ricciEnd (scalarPart r) = (scalar r / Module.finrank ℝ V) • LinearMap.id :=
  end_ext_innerₗ (by ext; simp [ricci_scalarPart hr₁])
theorem IsAlgebraicCurvature.ricciEnd_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricciEnd (scalarPart r) = (scalar r / Module.finrank ℝ V) • LinearMap.id :=
  FourTensor.ricciEnd_scalarPart hr.antisymm_first

/-- Away from dimension `1`, `scalar (scalarPart r) = scalar r` for every four-tensor `r`. -/
theorem scalar_scalarPart_of_finrank_ne_one (hn : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    scalar (scalarPart r) = scalar r := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn0 | hn0
  · simp [eq_zero_of_finrank_eq_zero hn0 r]
  · rw [scalar_apply, ricci_scalarPart_of_finrank_ne_one hn r, map_smul, bilinFormTrace_inner,
      smul_eq_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn0)]
/-- If `r` is antisymmetric in its first two arguments, `scalar (scalarPart r) = scalar r`. -/
theorem scalar_scalarPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) : scalar (scalarPart r) = scalar r := by
  rcases eq_or_ne (Module.finrank ℝ V) 1 with hn1 | hn1
  · simp [eq_zero_of_antisymm_first_of_finrank_le_one hn1.le hr₁]
  · exact scalar_scalarPart_of_finrank_ne_one hn1 r
/-- For an algebraic curvature tensor `r`, `scalar (scalarPart r) = scalar r`. -/
theorem IsAlgebraicCurvature.scalar_scalarPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (scalarPart r) = scalar r := FourTensor.scalar_scalarPart hr.antisymm_first

@[simp] theorem scalar_tracelessRicciPart (r : FourTensor V) :
    scalar (tracelessRicciPart r) = 0 := by
  rw [tracelessRicciPart_apply, map_smul, scalar_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, mul_zero, smul_zero]
@[simp] theorem scalarPart_tracelessRicciPart (r : FourTensor V) :
    scalarPart (tracelessRicciPart r) = 0 := by
  rw [scalarPart_apply, scalar_tracelessRicciPart, zero_div, zero_smul]

/-- Away from dimension `2`, `ricci (tracelessRicciPart r) = tracelessRicci r` for every `r`. -/
theorem ricci_tracelessRicciPart_of_finrank_ne_two (hn : Module.finrank ℝ V ≠ 2)
    (r : FourTensor V) : ricci (tracelessRicciPart r) = tracelessRicci r := by
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, zero_smul, add_zero, smul_smul,
    inv_mul_cancel₀ (finrank_sub_two_ne_zero hn), one_smul]
/-- For any skew-pair four-tensor `r`, `ricci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem ricci_tracelessRicciPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ricci (tracelessRicciPart r) = tracelessRicci r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · have htr : tracelessRicci r = 0 := by
      rw [eq_smul_constantCurvature_of_finrank_eq_two hn2 hr₁ hr₂, map_smul,
        tracelessRicci_constantCurvature, smul_zero]
    rw [tracelessRicciPart_apply, hn2]; norm_num [htr]
  · exact ricci_tracelessRicciPart_of_finrank_ne_two hn2 r
/-- For an algebraic curvature tensor `r`, `ricci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem IsAlgebraicCurvature.ricci_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : ricci (FourTensor.tracelessRicciPart r) = tracelessRicci r :=
  FourTensor.ricci_tracelessRicciPart hr.antisymm_first hr.antisymm_last
/-- Away from dimension `2`, `tracelessRicci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem tracelessRicci_tracelessRicciPart_of_finrank_ne_two (hn : Module.finrank ℝ V ≠ 2)
    (r : FourTensor V) : tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
  ext; simp [ricci_tracelessRicciPart_of_finrank_ne_two hn r]
theorem tracelessRicci_tracelessRicciPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
  ext; simp [ricci_tracelessRicciPart hr₁ hr₂]
theorem IsAlgebraicCurvature.tracelessRicci_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    tracelessRicci (FourTensor.tracelessRicciPart r) = tracelessRicci r :=
  FourTensor.tracelessRicci_tracelessRicciPart hr.antisymm_first hr.antisymm_last
theorem ricciEnd_tracelessRicciPart_of_finrank_ne_two (hn : Module.finrank ℝ V ≠ 2)
    (r : FourTensor V) : ricciEnd (tracelessRicciPart r) = tracelessRicciEnd r :=
  end_ext_innerₗ (by simp [ricci_tracelessRicciPart_of_finrank_ne_two hn r])
theorem ricciEnd_tracelessRicciPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    ricciEnd (tracelessRicciPart r) = tracelessRicciEnd r :=
  end_ext_innerₗ (by simp [ricci_tracelessRicciPart hr₁ hr₂])
theorem IsAlgebraicCurvature.ricciEnd_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ricciEnd (FourTensor.tracelessRicciPart r) = tracelessRicciEnd r :=
  FourTensor.ricciEnd_tracelessRicciPart hr.antisymm_first hr.antisymm_last
theorem tracelessRicciEnd_tracelessRicciPart_of_finrank_ne_two (hn : Module.finrank ℝ V ≠ 2)
    (r : FourTensor V) : tracelessRicciEnd (tracelessRicciPart r) = tracelessRicciEnd r :=
  end_ext_innerₗ (by simp [tracelessRicci_tracelessRicciPart_of_finrank_ne_two hn r])
theorem tracelessRicciEnd_tracelessRicciPart {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    tracelessRicciEnd (tracelessRicciPart r) = tracelessRicciEnd r :=
  end_ext_innerₗ (by simp [tracelessRicci_tracelessRicciPart hr₁ hr₂])
theorem IsAlgebraicCurvature.tracelessRicciEnd_tracelessRicciPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    tracelessRicciEnd (FourTensor.tracelessRicciPart r) = tracelessRicciEnd r :=
  FourTensor.tracelessRicciEnd_tracelessRicciPart hr.antisymm_first hr.antisymm_last

@[simp] theorem tracelessRicciPart_tracelessRicciPart (r : FourTensor V) :
    tracelessRicciPart (tracelessRicciPart r) = tracelessRicciPart r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · rw [tracelessRicciPart_apply (tracelessRicciPart r),
      tracelessRicci_tracelessRicciPart_of_finrank_ne_two hn2 r, ← tracelessRicciPart_apply]

/-- Away from dimension `1`, `scalar (weyl r) = 0` for every four-tensor `r`. -/
theorem scalar_weyl_of_finrank_ne_one (hn : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    scalar (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, scalar_scalarPart_of_finrank_ne_one hn r,
    scalar_tracelessRicciPart, sub_self, sub_zero]
/-- If `r` is antisymmetric in its first two arguments, `scalar (weyl r) = 0`. -/
theorem scalar_weyl {r : FourTensor V} (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    scalar (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, scalar_scalarPart hr₁, scalar_tracelessRicciPart, sub_self,
    sub_zero]
/-- **The Weyl part of every algebraic curvature tensor has zero scalar contraction.** -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := FourTensor.scalar_weyl hr.antisymm_first

/-- Away from dimension `2`, `tracelessRicci (weyl r) = 0` for every four-tensor `r`. -/
theorem tracelessRicci_weyl_of_finrank_ne_two (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    tracelessRicci (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, tracelessRicci_scalarPart,
    tracelessRicci_tracelessRicciPart_of_finrank_ne_two hn r]; abel
theorem tracelessRicciEnd_weyl_of_finrank_ne_two (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    tracelessRicciEnd (weyl r) = 0 :=
  tracelessRicciEnd_eq_zero_iff.mpr (tracelessRicci_weyl_of_finrank_ne_two hn r)

/-- **The Weyl part of any skew-pair four-tensor is Ricci-flat in all dimensions.** -/
theorem ricci_weyl {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : ricci (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, ricci_scalarPart hr₁, ricci_tracelessRicciPart hr₁ hr₂,
    tracelessRicci_apply]; abel
/-- **The Weyl part of every algebraic curvature tensor is Ricci-flat in all dimensions.** -/
theorem IsAlgebraicCurvature.ricci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.weyl r) = 0 := FourTensor.ricci_weyl hr.antisymm_first hr.antisymm_last
theorem ricciEnd_weyl {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : ricciEnd (weyl r) = 0 :=
  ricciEnd_eq_zero_iff.mpr (ricci_weyl hr₁ hr₂)
theorem IsAlgebraicCurvature.ricciEnd_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricciEnd (FourTensor.weyl r) = 0 := FourTensor.ricciEnd_weyl hr.antisymm_first hr.antisymm_last
theorem tracelessRicci_weyl {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : tracelessRicci (weyl r) = 0 := by
  ext; simp [ricci_weyl hr₁ hr₂, scalar_weyl hr₁]
theorem IsAlgebraicCurvature.tracelessRicci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    tracelessRicci (FourTensor.weyl r) = 0 :=
  FourTensor.tracelessRicci_weyl hr.antisymm_first hr.antisymm_last
theorem tracelessRicciEnd_weyl {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : tracelessRicciEnd (weyl r) = 0 :=
  tracelessRicciEnd_eq_zero_iff.mpr (tracelessRicci_weyl hr₁ hr₂)
theorem IsAlgebraicCurvature.tracelessRicciEnd_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : tracelessRicciEnd (FourTensor.weyl r) = 0 :=
  FourTensor.tracelessRicciEnd_weyl hr.antisymm_first hr.antisymm_last

@[simp] theorem scalarPart_weyl (r : FourTensor V) : scalarPart (weyl r) = 0 := by simp [weyl_apply]
@[simp] theorem tracelessRicciPart_weyl (r : FourTensor V) :
    tracelessRicciPart (weyl r) = 0 := by simp [weyl_apply]
/-- **Idempotence of the Weyl projection.** -/
@[simp] theorem weyl_weyl (r : FourTensor V) : weyl (weyl r) = weyl r := by
  rw [weyl_apply (weyl r), scalarPart_weyl, tracelessRicciPart_weyl, sub_zero, sub_zero]
@[simp] theorem weyl_constantCurvature : weyl (constantCurvature V) = 0 := by
  rw [weyl_apply, scalarPart_constantCurvature, tracelessRicciPart_constantCurvature, sub_self,
    sub_zero]
@[simp] theorem weyl_scalarPart (r : FourTensor V) : weyl (scalarPart r) = 0 := by
  rw [scalarPart_apply, map_smul, weyl_constantCurvature, smul_zero]
@[simp] theorem weyl_tracelessRicciPart (r : FourTensor V) : weyl (tracelessRicciPart r) = 0 := by
  rw [weyl_apply, scalarPart_tracelessRicciPart, tracelessRicciPart_tracelessRicciPart, sub_zero,
    sub_self]

/-! ### Comparison with the Schouten tensor and vanishing on `h ⊙ g` -/

/-- In dimension at least `3`, the Schouten bilinear form splits as
`(n - 2)⁻¹ • tracelessRicci r + (scalar r / (2 n (n - 1))) • innerₗ V`. -/
theorem schouten_eq_add_of_three_le_finrank (hn : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    schouten r = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • tracelessRicci r +
      (scalar r / (2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V := by
  have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have := finrank_sub_one_ne_zero (V := V) (by omega)
  have := finrank_sub_two_ne_zero (V := V) (by omega)
  ext u v; simp only [schouten_apply_apply, tracelessRicci_apply_apply, LinearMap.add_apply,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]; field_simp; ring
/-- Away from dimension `2`, `kulkarniNomizu (schouten r) (innerₗ V)` equals
`scalarPart r + tracelessRicciPart r` for every four-tensor `r`. -/
theorem kulkarniNomizu_schouten_innerₗ (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    kulkarniNomizu (schouten r) (innerₗ V) = scalarPart r + tracelessRicciPart r := by
  rcases lt_or_gt_of_ne hn with hnlt | hngt
  · have hkn (h k : BilinForm ℝ V) : kulkarniNomizu h k = 0 :=
      eq_zero_of_antisymm_first_of_finrank_le_one (by omega) (kulkarniNomizu_antisymm_first h k)
    simp [hkn, scalarPart_apply, constantCurvature_eq_smul_kulkarniNomizu, tracelessRicciPart_apply]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := finrank_sub_one_ne_zero (V := V) (by omega)
    rw [schouten_eq_add_of_three_le_finrank hngt r, map_add, LinearMap.add_apply, map_smul,
      map_smul, LinearMap.smul_apply, LinearMap.smul_apply, ← tracelessRicciPart_apply,
      scalarPart_apply, constantCurvature_eq_smul_kulkarniNomizu, smul_smul, add_comm]
    congr 2; field_simp
/-- Away from dimension `2`, `weyl r = r - kulkarniNomizu (schouten r) (innerₗ V)`. -/
theorem weyl_eq_sub_kulkarniNomizu_schouten (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    weyl r = r - kulkarniNomizu (schouten r) (innerₗ V) := by
  rw [kulkarniNomizu_schouten_innerₗ hn r, weyl_apply, sub_sub]

/-- Away from dimensions `1` and `2`, `bilinFormTrace (schouten r) = scalar r / (2 (n - 1))`. -/
theorem bilinFormTrace_schouten_of_finrank_ne_one_of_finrank_ne_two
    (hn₁ : Module.finrank ℝ V ≠ 1) (hn₂ : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    bilinFormTrace (schouten r) = scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn0 | hn0
  · simp [eq_zero_of_finrank_eq_zero hn0 r]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have := finrank_sub_one_ne_zero hn₁
    rw [schouten_eq_add_of_three_le_finrank (by omega) r, map_add, map_smul,
      bilinFormTrace_tracelessRicci, smul_zero, zero_add, map_smul, bilinFormTrace_inner,
      smul_eq_mul]; field_simp
/-- Away from dimension `2`, if `r` is antisymmetric in its first pair,
`bilinFormTrace (schouten r) = scalar r / (2 (n - 1))`. -/
theorem bilinFormTrace_schouten (hn : Module.finrank ℝ V ≠ 2) {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    bilinFormTrace (schouten r) = scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases eq_or_ne (Module.finrank ℝ V) 1 with hn1 | hn1
  · simp [eq_zero_of_antisymm_first_of_finrank_le_one hn1.le hr₁]
  · exact bilinFormTrace_schouten_of_finrank_ne_one_of_finrank_ne_two hn1 hn r
theorem IsAlgebraicCurvature.bilinFormTrace_schouten {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≠ 2) :
    bilinFormTrace (schouten r) = scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) :=
  FourTensor.bilinFormTrace_schouten hn hr.antisymm_first

/-- In dimension at least `3`, `schouten` is a left inverse to `h ↦ kulkarniNomizu h (innerₗ V)`. -/
theorem schouten_kulkarniNomizu_innerₗ_of_three_le_finrank (hn : 3 ≤ Module.finrank ℝ V)
    (h : BilinForm ℝ V) : schouten (kulkarniNomizu h (innerₗ V)) = h := by
  have := finrank_sub_one_ne_zero (V := V) (by omega)
  have := finrank_sub_two_ne_zero (V := V) (by omega)
  ext u v; simp only [schouten_apply_apply, ricci_kulkarniNomizu_innerₗ,
    scalar_kulkarniNomizu_innerₗ, LinearMap.add_apply, LinearMap.smul_apply, innerₗ_apply_apply,
    smul_eq_mul]; field_simp; ring
/-- In dimension at least `3`, `schouten (constantCurvature V) = (1 / 2) • innerₗ V`. -/
theorem schouten_constantCurvature_of_three_le_finrank (hn : 3 ≤ Module.finrank ℝ V) :
    schouten (constantCurvature V) = (1 / 2 : ℝ) • innerₗ V := by
  rw [constantCurvature_eq_smul_kulkarniNomizu, map_smul,
    schouten_kulkarniNomizu_innerₗ_of_three_le_finrank hn]
/-- Away from dimension `1`, `schouten (weyl r) = 0` for every four-tensor `r`. -/
theorem schouten_weyl_of_finrank_ne_one (hn : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    schouten (weyl r) = 0 := by
  rcases (by omega : Module.finrank ℝ V = 0 ∨ Module.finrank ℝ V = 2 ∨ 3 ≤ Module.finrank ℝ V)
    with h0 | h2 | h3
  · simp [eq_zero_of_finrank_eq_zero h0 (weyl r)]
  · ext; simp [h2]
  · rw [schouten_eq_add_of_three_le_finrank h3, tracelessRicci_weyl_of_finrank_ne_two (by omega) r,
      scalar_weyl_of_finrank_ne_one hn r]; simp
/-- If `r` is antisymmetric in its first pair, `schouten (weyl r) = 0` in all dimensions. -/
theorem schouten_weyl {r : FourTensor V} (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    schouten (weyl r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 1 with hn1 | hn1
  · simp [eq_zero_of_antisymm_first_of_finrank_le_one hn1.le hr₁]
  · exact schouten_weyl_of_finrank_ne_one hn1 r
theorem IsAlgebraicCurvature.schouten_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    schouten (FourTensor.weyl r) = 0 := FourTensor.schouten_weyl hr.antisymm_first
/-- In every dimension, `weyl (kulkarniNomizu h (innerₗ V)) = 0` for every bilinear form `h`. -/
@[simp] theorem weyl_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    weyl (kulkarniNomizu h (innerₗ V)) = 0 := by
  rcases (by omega : Module.finrank ℝ V ≤ 1 ∨ Module.finrank ℝ V = 2 ∨ 3 ≤ Module.finrank ℝ V)
    with h1 | h2 | h3
  · rw [eq_zero_of_antisymm_first_of_finrank_le_one h1 (kulkarniNomizu_antisymm_first h (innerₗ V)),
      map_zero]
  · rw [eq_smul_constantCurvature_of_finrank_eq_two h2 (kulkarniNomizu_antisymm_first h (innerₗ V))
      (kulkarniNomizu_antisymm_last h (innerₗ V)), map_smul, weyl_constantCurvature, smul_zero]
  · rw [weyl_eq_sub_kulkarniNomizu_schouten (by omega),
      schouten_kulkarniNomizu_innerₗ_of_three_le_finrank h3, sub_self]

/-! ### Vanishing of the Weyl tensor in dimension at most three -/

/-- **In dimension `3`, the Weyl part of any skew-pair four-tensor vanishes.** -/
theorem weyl_eq_zero_of_finrank_eq_three (hn : Module.finrank ℝ V = 3) {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : weyl r = 0 := by
  apply toLinearMap₄_injective; rw [map_zero]
  let b := stdOrthonormalBasis ℝ V
  refine LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
    (fun _ _ hxy ↦ by simp only [smul_eq_mul] at hxy; linarith) b.toBasis (by simp [hn])
    (fun x y z w ↦ by simp [weyl_antisymm_first hr₁ x y z w])
    (fun x y z w ↦ by simp [weyl_antisymm_last hr₂ x y z w]) fun y z ↦ ?_
  have hsum : ∑ i, weyl r ![b i, y, z, b i] = -ricci (weyl r) y z := by
    rw [ricci_apply_orthonormalBasis b, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ weyl_antisymm_last hr₂ (b i) y z (b i)
  simp [OrthonormalBasis.coe_toBasis, hsum, ricci_weyl hr₁ hr₂]
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_eq_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V = 3) : FourTensor.weyl r = 0 :=
  FourTensor.weyl_eq_zero_of_finrank_eq_three hn hr.antisymm_first hr.antisymm_last
/-- **In dimension at most `3`, the Weyl part of any skew-pair four-tensor vanishes.** -/
theorem weyl_eq_zero_of_finrank_le_three (hn : Module.finrank ℝ V ≤ 3) {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : weyl r = 0 := by
  rcases (by omega : Module.finrank ℝ V ≤ 1 ∨ Module.finrank ℝ V = 2 ∨ Module.finrank ℝ V = 3)
    with h1 | h2 | h3
  · rw [eq_zero_of_antisymm_first_of_finrank_le_one h1 hr₁, map_zero]
  · rw [eq_smul_constantCurvature_of_finrank_eq_two h2 hr₁ hr₂, map_smul, weyl_constantCurvature,
      smul_zero]
  · exact weyl_eq_zero_of_finrank_eq_three h3 hr₁ hr₂
/-- **In dimension at most `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 3) : FourTensor.weyl r = 0 :=
  FourTensor.weyl_eq_zero_of_finrank_le_three hn hr.antisymm_first hr.antisymm_last
/-- In dimension at most `3`, every skew-pair four-tensor equals
`scalarPart r + tracelessRicciPart r`. -/
theorem eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three (hn : Module.finrank ℝ V ≤ 3)
    {r : FourTensor V} (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    r = scalarPart r + tracelessRicciPart r := by
  simpa [weyl_eq_zero_of_finrank_le_three hn hr₁ hr₂] using
    (scalarPart_add_tracelessRicciPart_add_weyl r).symm
theorem IsAlgebraicCurvature.eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≤ 3) :
    r = scalarPart r + FourTensor.tracelessRicciPart r :=
  FourTensor.eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three hn hr.antisymm_first
    hr.antisymm_last

/-! ### Equivariance under linear isometric equivalences -/

section Equivariance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Orthogonal equivariance of `tracelessRicci` under a linear isometric equivalence `e`. -/
theorem tracelessRicci_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
      u v = tracelessRicci r (e u) (e v) := by
  simp [ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]
/-- Pulling back along `e : W ≃ₗᵢ[ℝ] V` conjugates `ricciEnd r` via `e.toLinearEquiv.symm.conj`. -/
theorem ricciEnd_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    ricciEnd (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      e.toLinearEquiv.symm.conj (ricciEnd r) :=
  LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    rw [inner_ricciEnd_left, ricci_compContinuousLinearMap_linearIsometryEquiv]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← e.inner_map_map, e.apply_symm_apply, inner_ricciEnd_left, e.symm_symm]
/-- Pulling back along `e : W ≃ₗᵢ[ℝ] V` conjugates `tracelessRicciEnd r` via
`e.toLinearEquiv.symm.conj`. -/
theorem tracelessRicciEnd_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciEnd (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      e.toLinearEquiv.symm.conj (tracelessRicciEnd r) := by
  rw [tracelessRicciEnd_apply, tracelessRicciEnd_apply, map_sub, map_smul, LinearEquiv.conj_id,
    ricciEnd_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]
/-- Orthogonal equivariance of `scalarPart` under pullback along `e : W ≃ₗᵢ[ℝ] V`. -/
theorem scalarPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    scalarPart (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (scalarPart r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m; have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, compContinuousLinearMap_apply_vec]
  simp [scalarPart_apply, scalar_compContinuousLinearMap_linearIsometryEquiv,
    e.toLinearEquiv.finrank_eq]
/-- Orthogonal equivariance of `tracelessRicciPart` under pullback along `e : W ≃ₗᵢ[ℝ] V`. -/
theorem tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciPart
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap := by
  ext m; have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, compContinuousLinearMap_apply_vec, tracelessRicciPart_apply,
    tracelessRicciPart_apply, smul_apply, smul_apply, e.toLinearEquiv.finrank_eq]
  congr 1; simp [ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]
/-- Orthogonal equivariance of `schouten` under a linear isometric equivalence `e : W ≃ₗᵢ[ℝ] V`. -/
theorem schouten_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    schouten (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) u v =
      schouten r (e u) (e v) := by
  simp [ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq]
/-- Orthogonal equivariance of `weyl` under pullback along `e : W ≃ₗᵢ[ℝ] V`. -/
theorem weyl_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m; simp [weyl_apply, scalarPart_compContinuousLinearMap_linearIsometryEquiv e r,
    tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv e r]

end Equivariance

/-! ### Contraction adjointness, pairwise orthogonality, and the Pythagorean identity -/

section Orthogonality

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ V] in
private theorem sum_inner_mul_apply (b : OrthonormalBasis ι ℝ V) (d : ι) (F : ι → ℝ) :
    (∑ e, ⟪b d, b e⟫ * F e) = F d := by classical simp [orthonormal_iff_ite.mp b.orthonormal]
omit [FiniteDimensional ℝ V] in
private theorem sum_smul_mul (c : ℝ) (f g : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, (c • f) ![b i, b j, b k, b l] * g ![b i, b j, b k, b l]) =
      c * ∑ i, ∑ j, ∑ k, ∑ l, f ![b i, b j, b k, b l] * g ![b i, b j, b k, b l] := by
  simp_rw [smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

private theorem sum_kn_term₂ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) (q : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
      ∑ j, ∑ l, h (b j) (b l) * ricci q (b j) (b l) := by
  have hl (i j : ι) : (∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
      ∑ l, h (b j) (b l) * q ![b i, b j, b i, b l] := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp_rw [show ∀ k, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] =
      ⟪b i, b k⟫ * (h (b j) (b l) * q ![b i, b j, b k, b l]) by intros; ring, sum_inner_mul_apply]
  simp_rw [hl, ricci_apply_orthonormalBasis b, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
private theorem sum_kn_term₃ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l]) =
      -∑ i, ∑ l, h (b i) (b l) * ricci q (b i) (b l) := by
  rw [Finset.sum_comm, ← sum_kn_term₂ b h q]; simp_rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [hq₁]; ring
private theorem sum_kn_term₄ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) {q : FourTensor V}
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b k) * ⟪b i, b l⟫ * q ![b i, b j, b k, b l]) =
      -∑ j, ∑ k, h (b j) (b k) * ricci q (b j) (b k) := by
  have hk (i j : ι) : (∑ k, ∑ l, h (b j) (b k) * ⟪b i, b l⟫ * q ![b i, b j, b k, b l]) =
      -∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [hq₂]; ring
  simp_rw [hk, Finset.sum_neg_distrib, sum_kn_term₂]
private theorem sum_kn_term₁ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) {q : FourTensor V}
    (hq₁₂ : ∀ u v z w, q ![u, v, z, w] = q ![v, u, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b i) (b k) * ⟪b j, b l⟫ * q ![b i, b j, b k, b l]) =
      ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) := by
  rw [Finset.sum_comm]
  have hk (j i : ι) : (∑ k, ∑ l, h (b i) (b k) * ⟪b j, b l⟫ * q ![b i, b j, b k, b l]) =
      ∑ k, ∑ l, h (b i) (b l) * ⟪b j, b k⟫ * q ![b j, b i, b k, b l] := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [hq₁₂]
  simp_rw [hk, sum_kn_term₂]

/-- **Adjointness of `h ↦ h ⊙ g` and `ricci`**: componentwise pairing of
`kulkarniNomizu h (innerₗ V)` with a skew-pair `q` equals `4 * ∑ h (b i) (b k) * ricci q ..`. -/
theorem sum_kulkarniNomizu_innerₗ_mul (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      kulkarniNomizu h (innerₗ V) ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      4 * ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) := by
  have hq₁₂ (u v z w : V) : q ![u, v, z, w] = q ![v, u, w, z] := by
    rw [hq₁ u v z w, hq₂ v u z w, neg_neg]
  simp only [kulkarniNomizu_apply, innerₗ_apply_apply, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_kn_term₁ b h hq₁₂, sum_kn_term₂ b h q, sum_kn_term₃ b h hq₁,
    sum_kn_term₄ b h hq₂]; ring
theorem IsAlgebraicCurvature.sum_kulkarniNomizu_innerₗ_mul {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      kulkarniNomizu h (innerₗ V) ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      4 * ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) :=
  FourTensor.sum_kulkarniNomizu_innerₗ_mul b h hq.antisymm_first hq.antisymm_last

/-- Pairing `constantCurvature V` against `q` antisymmetric in its first pair gives
`2 * scalar q`. -/
theorem sum_constantCurvature_mul (b : OrthonormalBasis ι ℝ V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) :
    (∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      2 * scalar q := by
  have hc (i j k l : ι) : constantCurvature V ![b i, b j, b k, b l] * q ![b i, b j, b k, b l] =
      innerₗ V (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] -
        innerₗ V (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l] := by
    simp only [constantCurvature_apply, innerₗ_apply_apply]; ring
  simp_rw [hc, Finset.sum_sub_distrib]
  rw [sum_kn_term₂ b (innerₗ V) q, sum_kn_term₃ b (innerₗ V) hq₁]
  simp only [innerₗ_apply_apply, sum_inner_mul_apply, ← bilinFormTrace_eq_sum (ricci q) b,
    ← scalar_apply]; ring
/-- The squared component norm of `constantCurvature V` in an orthonormal basis is `2 n (n - 1)`. -/
theorem sum_constantCurvature_sq (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] ^ 2) =
      2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) := by
  simp only [sq]
  rw [sum_constantCurvature_mul b isAlgebraicCurvature_constantCurvature.antisymm_first,
    scalar_constantCurvature, mul_assoc]
/-- The squared component norm of `scalarPart r` is `2 * scalar r ^ 2 / (n (n - 1))`. -/
theorem sum_scalarPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · interval_cases h : Module.finrank ℝ V <;> simp [scalarPart_apply, h]
  · have : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have := finrank_sub_one_ne_zero (V := V) (by omega)
    have hsmul (c : ℝ) (f : FourTensor V) :
        (∑ i, ∑ j, ∑ k, ∑ l, (c • f) ![b i, b j, b k, b l] ^ 2) =
          c ^ 2 * ∑ i, ∑ j, ∑ k, ∑ l, f ![b i, b j, b k, b l] ^ 2 := by
      simp_rw [smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [scalarPart_apply, hsmul, sum_constantCurvature_sq b]; field_simp
/-- The squared component norm of `tracelessRicciPart r` is `(4 / (n - 2)) * ∑ |Ric₀(r)|²`. -/
theorem sum_tracelessRicciPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) =
      (4 / ((Module.finrank ℝ V : ℝ) - 2)) * ∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2 := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · simp_rw [sq]
    conv_lhs => enter [2, i, 2, j, 2, k, 2, l, 1]; rw [tracelessRicciPart_apply]
    rw [sum_smul_mul, sum_kulkarniNomizu_innerₗ_mul b (tracelessRicci r)
      (tracelessRicciPart_antisymm_first r) (tracelessRicciPart_antisymm_last r),
      ricci_tracelessRicciPart_of_finrank_ne_two hn2 r]; ring

/-- `scalarPart r` and `tracelessRicciPart q` are orthogonal for all four-tensors `r, q`. -/
theorem sum_scalarPart_mul_tracelessRicciPart (r q : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] *
      tracelessRicciPart q ![b i, b j, b k, b l]) = 0 := by
  rw [scalarPart_apply, sum_smul_mul, sum_constantCurvature_mul b
    (tracelessRicciPart_antisymm_first q), scalar_tracelessRicciPart, mul_zero, mul_zero]
/-- `scalarPart r` is orthogonal to `weyl q` whenever `q` is antisymmetric in its first pair. -/
theorem sum_scalarPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      scalarPart r ![b i, b j, b k, b l] * weyl q ![b i, b j, b k, b l]) = 0 := by
  rw [scalarPart_apply, sum_smul_mul, sum_constantCurvature_mul b (weyl_antisymm_first hq₁),
    scalar_weyl hq₁, mul_zero, mul_zero]
theorem IsAlgebraicCurvature.sum_scalarPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      scalarPart r ![b i, b j, b k, b l] * FourTensor.weyl q ![b i, b j, b k, b l]) = 0 :=
  FourTensor.sum_scalarPart_mul_weyl r hq.antisymm_first b
/-- `tracelessRicciPart r` is orthogonal to `weyl q` for any skew-pair four-tensor `q`. -/
theorem sum_tracelessRicciPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      tracelessRicciPart r ![b i, b j, b k, b l] * weyl q ![b i, b j, b k, b l]) = 0 := by
  rw [tracelessRicciPart_apply, sum_smul_mul,
    sum_kulkarniNomizu_innerₗ_mul b (tracelessRicci r) (weyl_antisymm_first hq₁)
      (weyl_antisymm_last hq₂), ricci_weyl hq₁ hq₂]; simp
theorem IsAlgebraicCurvature.sum_tracelessRicciPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] *
      FourTensor.weyl q ![b i, b j, b k, b l]) = 0 :=
  FourTensor.sum_tracelessRicciPart_mul_weyl r hq.antisymm_first hq.antisymm_last b

/-- **Pythagorean decomposition of any skew-pair four-tensor** into scalar, trace-free Ricci, and
Weyl component norms. -/
theorem sum_sq_eq_add {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, weyl r ![b i, b j, b k, b l] ^ 2) := by
  have hmul2 (F : ι → ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * F i j k l) = 2 * ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    simp_rw [← Finset.mul_sum]
  have hsq (a c d : ℝ) :
      (a + c + d) ^ 2 = a ^ 2 + c ^ 2 + d ^ 2 + 2 * (a * c) + 2 * (a * d) + 2 * (c * d) := by ring
  conv_lhs =>
    enter [2, i, 2, j, 2, k, 2, l, 1]; rw [← scalarPart_add_tracelessRicciPart_add_weyl r]
  simp only [add_apply, hsq, Finset.sum_add_distrib, hmul2,
    sum_scalarPart_mul_tracelessRicciPart r r b, sum_scalarPart_mul_weyl r hr₁ b,
    sum_tracelessRicciPart_mul_weyl r hr₁ hr₂ b, mul_zero, add_zero]
/-- **Pythagorean decomposition of an algebraic curvature tensor.** -/
theorem IsAlgebraicCurvature.sum_sq_eq_add {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) :=
  FourTensor.sum_sq_eq_add hr.antisymm_first hr.antisymm_last b
/-- **Explicit norm-squared identity for skew-pair four-tensors**:
`∑ |r|² = (2 / (n (n - 1))) Scal(r)² + (4 / (n - 2)) ∑ |Ric₀(r)|² + ∑ |Weyl(r)|²`. -/
theorem sum_sq_eq_scalar_add_tracelessRicci_add_weyl {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) +
        (4 / ((Module.finrank ℝ V : ℝ) - 2)) * (∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, weyl r ![b i, b j, b k, b l] ^ 2) := by
  rw [sum_sq_eq_add hr₁ hr₂ b, sum_scalarPart_sq r b, sum_tracelessRicciPart_sq r b]
/-- **Explicit norm-squared identity for algebraic curvature tensors.** -/
theorem IsAlgebraicCurvature.sum_sq_eq_scalar_add_tracelessRicci_add_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) +
        (4 / ((Module.finrank ℝ V : ℝ) - 2)) * (∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) :=
  FourTensor.sum_sq_eq_scalar_add_tracelessRicci_add_weyl hr.antisymm_first hr.antisymm_last b

end Orthogonality

end TauCeti.FourTensor
