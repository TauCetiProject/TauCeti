/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Multilinear.CurvatureDimThree

/-!
# Orthogonal Ricci–Weyl decomposition of algebraic curvature tensors

On a finite-dimensional real inner product space `V` of dimension `n`, every `r : FourTensor V`
splits as `r = weyl r + tracelessRicciPart r + scalarPart r`, with `scalarPart r = (scalar r /
(n (n - 1))) • constantCurvature V`, `tracelessRicciPart r = (n - 2)⁻¹ • kulkarniNomizu
(tracelessRicci r) (innerₗ V)`, and `weyl r = r - scalarPart r - tracelessRicciPart r`.

In every dimension, `scalarPart`, `tracelessRicciPart`, and `weyl` are mutually annihilating
idempotent `O(n)`-equivariant projections preserving `algebraicCurvatureSubmodule V`. For general
four-tensors, `scalar (weyl r) = 0` (`n ≠ 1`), `tracelessRicci (weyl r) = 0` (`n ≠ 2`), and
`ricci (weyl r) = 0` (`n ≠ 1, 2`); for pair-antisymmetric four-tensors (in particular algebraic
curvature tensors), `weyl r` is trace-free in every dimension and vanishes for `n ≤ 3`.

Via `curvatureEndomorphism`, this gives the operator-wedge splitting of Böhm–Wilking (2008,
Section 2): `(scalar r / (n (n - 1))) • (id ∧ id) + (2 / (n - 2)) • (Ric₀♯ ∧ id) + W`. Under the
trace pairing `(A, B) ↦ tr (A ∘ₗ B)` on `End(⋀[ℝ]^2 V)` (which coincides with the Hilbert–Schmidt
inner product `tr (A† ∘ₗ B)` whenever at least one factor is self-adjoint, in particular for
`scalarPart` and for algebraic curvature tensors), the trace-free Ricci and scalar summands are
orthogonal for all four-tensors, and the Weyl summand of any pair-antisymmetric four-tensor is
orthogonal to both in every dimension.

## Main definitions

* `TauCeti.FourTensor.tracelessRicci`, `TauCeti.FourTensor.ricciEndomorphism`,
  `TauCeti.FourTensor.tracelessRicciEndomorphism`, `TauCeti.FourTensor.scalarPart`,
  `TauCeti.FourTensor.tracelessRicciPart`, `TauCeti.FourTensor.schouten`, and
  `TauCeti.FourTensor.weyl`.

## Main results

* `TauCeti.FourTensor.weyl_add_tracelessRicciPart_add_scalarPart`, the nine unconditional
  projection laws, `TauCeti.FourTensor.ricci_weyl_of_antisymm`,
  `TauCeti.FourTensor.weyl_eq_sub_kulkarniNomizu_schouten`,
  `TauCeti.FourTensor.weyl_kulkarniNomizu_innerₗ`,
  `TauCeti.FourTensor.curvatureEndomorphism_eq_add`, trace-pairing orthogonality (coinciding with
  Hilbert–Schmidt orthogonality when at least one factor is self-adjoint),
  `TauCeti.FourTensor.sum_kulkarniNomizu_innerₗ_mul_of_antisymm`,
  `TauCeti.FourTensor.sum_sq_eq_scalar_sq_add_sum_tracelessRicci_sq_add_sum_weyl_sq_of_antisymm`,
  and
  `TauCeti.FourTensor.weyl_eq_zero_of_finrank_le_three_of_antisymm`.

## References

* I. M. Singer and J. A. Thorpe, *The curvature of 4-dimensional Einstein spaces* (1969), for the
  `O(n)`-invariant orthogonal decomposition into scalar, trace-free Ricci, and Weyl components.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G, Propositions 1.116–1.120.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7, Theorem 7.30.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Trace-free Ricci form and Ricci endomorphisms -/

/-- The trace-free Ricci contraction `Ric₀ = Ric - (Scal / n) g` of a four-tensor. -/
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ricci (V := V) + (-((Module.finrank ℝ V : ℝ)⁻¹ • scalar (V := V))).smulRight (innerₗ V)

/-- Definition of `tracelessRicci`. -/
theorem tracelessRicci_apply (r : FourTensor V) :
    tracelessRicci r = ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V := by
  ext; simp [tracelessRicci, div_eq_inv_mul, sub_eq_add_neg]

/-- The trace-free Ricci contraction has zero metric trace in every dimension. -/
@[simp] theorem metricTrace_tracelessRicci (r : FourTensor V) :
    LinearMap.BilinMap.metricTrace (tracelessRicci r) = 0 := by
  by_cases hn : Module.finrank ℝ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp hn
    simp [Subsingleton.elim (tracelessRicci r) 0]
  · have hsub := map_sub LinearMap.BilinMap.metricTrace (ricci r)
      ((scalar r / Module.finrank ℝ V) • innerₗ V)
    rw [tracelessRicci_apply, hsub, map_smul, LinearMap.BilinMap.metricTrace_inner, ← scalar_apply,
      smul_eq_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn), sub_self]

/-- On a space of dimension at most `1`, `tracelessRicci r = 0` for every four-tensor `r`. -/
theorem tracelessRicci_eq_zero_of_finrank_le_one (r : FourTensor V)
    (hdim : Module.finrank ℝ V ≤ 1) : tracelessRicci r = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdim with h0 | h1
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0; ext u _; simp [Subsingleton.elim u 0]
  · let b : OrthonormalBasis (Fin 1) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr h1)
    refine b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦ ?_
    rcases Fin.eq_zero i with rfl; rcases Fin.eq_zero j with rfl
    simp [tracelessRicci_apply, scalar_apply, LinearMap.BilinMap.metricTrace_eq_sum _ b, h1]

/-- `tracelessRicci r` is symmetric iff `ricci r` is symmetric. -/
@[simp] theorem isSymm_tracelessRicci_iff {r : FourTensor V} :
    (tracelessRicci r).IsSymm ↔ (ricci r).IsSymm := by
  have hinner : BilinForm.IsSymm ((scalar r / Module.finrank ℝ V) • innerₗ V) :=
    (BilinForm.isSymm_iff.mpr (isSymm_inner (E := V))).smul _
  rw [tracelessRicci_apply]
  exact ⟨fun h ↦ by convert h.add hinner; abel, fun h ↦ h.sub hinner⟩

/-- `tracelessRicci r` is symmetric for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.isSymm_tracelessRicci {r : FourTensor V} (hr : IsBivectorSymmetric r) :
    (tracelessRicci r).IsSymm := isSymm_tracelessRicci_iff.mpr hr.isSymm_ricci

/-- `tracelessRicci r` is symmetric for an algebraic curvature tensor `r`. -/
theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm :=
  isSymm_tracelessRicci_iff.mpr hr.isSymm_ricci

/-- The metric-raised Ricci endomorphism `Ric♯ : V →ₗ[ℝ] V`, with `⟪Ric♯ u, v⟫ = ricci r u v`. -/
def ricciEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  bilinFormToEnd.toLinearMap.comp ricci

/-- Definition of `ricciEndomorphism r`. -/
theorem ricciEndomorphism_apply (r : FourTensor V) :
    ricciEndomorphism r = bilinFormToEnd (ricci r) := (rfl)

/-- Pairing `ricciEndomorphism r u` with `v` recovers `ricci r u v`. -/
@[simp] theorem inner_ricciEndomorphism_left (r : FourTensor V) (u v : V) :
    ⟪ricciEndomorphism r u, v⟫ = ricci r u v := (ricci r).inner_bilinFormToEnd_left u v

/-- Lowering `ricciEndomorphism r` with `innerₗ V` recovers `ricci r`. -/
@[simp] theorem innerₗ_comp_ricciEndomorphism (r : FourTensor V) :
    (innerₗ V).comp (ricciEndomorphism r) = ricci r := (ricci r).innerₗ_comp_bilinFormToEnd

/-- The operator trace of `ricciEndomorphism r` equals `scalar r`. -/
@[simp] theorem trace_ricciEndomorphism (r : FourTensor V) :
    LinearMap.trace ℝ V (ricciEndomorphism r) = scalar r :=
  (ricci r).trace_bilinFormToEnd.trans (scalar_apply r).symm

/-- `ricciEndomorphism r` is symmetric iff `ricci r` is symmetric. -/
@[simp] theorem isSymmetric_ricciEndomorphism_iff {r : FourTensor V} :
    (ricciEndomorphism r).IsSymmetric ↔ (ricci r).IsSymm := isSymmetric_bilinFormToEnd_iff

/-- `ricciEndomorphism r` is symmetric for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.isSymmetric_ricciEndomorphism {r : FourTensor V}
    (hr : IsBivectorSymmetric r) : (ricciEndomorphism r).IsSymmetric :=
  isSymmetric_ricciEndomorphism_iff.mpr hr.isSymm_ricci

/-- `ricciEndomorphism r` is symmetric for an algebraic curvature tensor `r`. -/
theorem IsAlgebraicCurvature.isSymmetric_ricciEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (ricciEndomorphism r).IsSymmetric :=
  isSymmetric_ricciEndomorphism_iff.mpr hr.isSymm_ricci

/-- The metric-raised trace-free Ricci endomorphism `Ric₀♯ : V →ₗ[ℝ] V`. -/
def tracelessRicciEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  bilinFormToEnd.toLinearMap.comp tracelessRicci

/-- Definition of `tracelessRicciEndomorphism r`. -/
theorem tracelessRicciEndomorphism_apply (r : FourTensor V) :
    tracelessRicciEndomorphism r = bilinFormToEnd (tracelessRicci r) := (rfl)

/-- Pairing `tracelessRicciEndomorphism r u` with `v` recovers `tracelessRicci r u v`. -/
@[simp] theorem inner_tracelessRicciEndomorphism_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEndomorphism r u, v⟫ = tracelessRicci r u v :=
  (tracelessRicci r).inner_bilinFormToEnd_left u v

/-- Lowering `tracelessRicciEndomorphism r` with `innerₗ V` recovers `tracelessRicci r`. -/
@[simp] theorem innerₗ_comp_tracelessRicciEndomorphism (r : FourTensor V) :
    (innerₗ V).comp (tracelessRicciEndomorphism r) = tracelessRicci r :=
  (tracelessRicci r).innerₗ_comp_bilinFormToEnd

/-- `tracelessRicciEndomorphism r = ricciEndomorphism r - (scalar r / n) • LinearMap.id`. -/
theorem tracelessRicciEndomorphism_eq (r : FourTensor V) :
    tracelessRicciEndomorphism r =
      ricciEndomorphism r - (scalar r / Module.finrank ℝ V) • LinearMap.id := by
  rw [tracelessRicciEndomorphism_apply, tracelessRicci_apply,
    map_sub (bilinFormToEnd (E := V)) (ricci r) ((scalar r / Module.finrank ℝ V) • innerₗ V),
    map_smul, bilinFormToEnd_innerₗ, ricciEndomorphism_apply]

/-- `tracelessRicciEndomorphism r` is symmetric iff `ricci r` is symmetric. -/
@[simp] theorem isSymmetric_tracelessRicciEndomorphism_iff {r : FourTensor V} :
    (tracelessRicciEndomorphism r).IsSymmetric ↔ (ricci r).IsSymm :=
  isSymmetric_bilinFormToEnd_iff.trans isSymm_tracelessRicci_iff

/-- `tracelessRicciEndomorphism r` is symmetric for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.isSymmetric_tracelessRicciEndomorphism {r : FourTensor V}
    (hr : IsBivectorSymmetric r) : (tracelessRicciEndomorphism r).IsSymmetric :=
  isSymmetric_tracelessRicciEndomorphism_iff.mpr hr.isSymm_ricci

/-- `tracelessRicciEndomorphism r` is symmetric for an algebraic curvature tensor `r`. -/
theorem IsAlgebraicCurvature.isSymmetric_tracelessRicciEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicciEndomorphism r).IsSymmetric :=
  isSymmetric_tracelessRicciEndomorphism_iff.mpr hr.isSymm_ricci

/-- The trace of `tracelessRicciEndomorphism r` vanishes in every dimension. -/
@[simp] theorem trace_tracelessRicciEndomorphism (r : FourTensor V) :
    LinearMap.trace ℝ V (tracelessRicciEndomorphism r) = 0 :=
  (tracelessRicci r).trace_bilinFormToEnd.trans (metricTrace_tracelessRicci r)

/-! ### Scalar, trace-free Ricci, and Weyl curvature parts -/

/-- The scalar curvature part `(Scal / (n (n - 1))) • constantCurvature V` of a four-tensor. -/
def scalarPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar).smulRight
    (constantCurvature V)

/-- Definition of `scalarPart r`. -/
theorem scalarPart_apply (r : FourTensor V) :
    scalarPart r = (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
      constantCurvature V := by
  simp [scalarPart, div_eq_inv_mul]

/-- The trace-free Ricci curvature part `(n - 2)⁻¹ • (Ric₀ ⊙ g)` of a four-tensor. -/
def tracelessRicciPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (kulkarniNomizu.flip (innerₗ V)).comp tracelessRicci

/-- Definition of `tracelessRicciPart r`. -/
theorem tracelessRicciPart_apply (r : FourTensor V) :
    tracelessRicciPart r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V) := (rfl)

/-- The Weyl curvature part `W = r - scalarPart r - tracelessRicciPart r` of a four-tensor. -/
def weyl : FourTensor V →ₗ[ℝ] FourTensor V := LinearMap.id - scalarPart - tracelessRicciPart

/-- Definition of `weyl r`. -/
theorem weyl_apply (r : FourTensor V) : weyl r = r - scalarPart r - tracelessRicciPart r := (rfl)

/-- Every four-tensor decomposes as `weyl r + tracelessRicciPart r + scalarPart r`. -/
theorem weyl_add_tracelessRicciPart_add_scalarPart (r : FourTensor V) :
    weyl r + tracelessRicciPart r + scalarPart r = r := by rw [weyl_apply]; abel

/-- `scalarPart r` is always an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_scalarPart (r : FourTensor V) : IsAlgebraicCurvature (scalarPart r) :=
  mem_algebraicCurvatureSubmodule.mp <| Submodule.smul_mem _ _
    (mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature)

/-- Whenever `ricci r` is symmetric, `tracelessRicciPart r` is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_tracelessRicciPart_of_isSymm_ricci {r : FourTensor V}
    (h : (ricci r).IsSymm) : IsAlgebraicCurvature (tracelessRicciPart r) :=
  mem_algebraicCurvatureSubmodule.mp <| Submodule.smul_mem _ _
    (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_kulkarniNomizu
      (isSymm_tracelessRicci_iff.mpr h) isSymm_innerₗ))

/-- `tracelessRicciPart r` is an algebraic curvature tensor for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.isAlgebraicCurvature_tracelessRicciPart {r : FourTensor V}
    (hr : IsBivectorSymmetric r) : IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
  isAlgebraicCurvature_tracelessRicciPart_of_isSymm_ricci hr.isSymm_ricci

/-- `tracelessRicciPart r` is an algebraic curvature tensor for algebraic curvature `r`. -/
theorem IsAlgebraicCurvature.tracelessRicciPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
  isAlgebraicCurvature_tracelessRicciPart_of_isSymm_ricci hr.isSymm_ricci

/-- `weyl r` is an algebraic curvature tensor for algebraic curvature `r`. -/
theorem IsAlgebraicCurvature.weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.weyl r) :=
  mem_algebraicCurvatureSubmodule.mp <| (algebraicCurvatureSubmodule V).sub_mem
    ((algebraicCurvatureSubmodule V).sub_mem (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)))
    (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart)

private theorem tracelessRicciPart_antisymm_first (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![v, u, z, w] := by
  simp [tracelessRicciPart_apply]; ring

private theorem tracelessRicciPart_antisymm_last (r : FourTensor V) (u v z w : V) :
    tracelessRicciPart r ![u, v, z, w] = -tracelessRicciPart r ![u, v, w, z] := by
  simp [tracelessRicciPart_apply]; ring

private theorem weyl_antisymm_first {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) (u v z w : V) :
    weyl r ![u, v, z, w] = -weyl r ![v, u, z, w] := by
  simp only [weyl_apply, sub_apply, h₁ u v z w, tracelessRicciPart_antisymm_first r u v z w,
    (isAlgebraicCurvature_scalarPart r).antisymm_first u v z w]; ring

private theorem weyl_antisymm_last {r : FourTensor V}
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    weyl r ![u, v, z, w] = -weyl r ![u, v, w, z] := by
  simp only [weyl_apply, sub_apply, h₂ u v z w, tracelessRicciPart_antisymm_last r u v z w,
    (isAlgebraicCurvature_scalarPart r).antisymm_last u v z w]; ring

private theorem scalarPart_eq_zero_of_finrank_le_one (hdim : Module.finrank ℝ V ≤ 1)
    (r : FourTensor V) : scalarPart r = 0 := by
  simp [scalarPart_apply, isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hdim]

private theorem tracelessRicciPart_eq_zero_of_finrank_eq_two (hdim : Module.finrank ℝ V = 2)
    (r : FourTensor V) : tracelessRicciPart r = 0 := by
  rw [tracelessRicciPart_apply, hdim]; norm_num

omit [FiniteDimensional ℝ V] in
private theorem finrank_cast_ne_zero (hn : Module.finrank ℝ V ≠ 0) :
    (Module.finrank ℝ V : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr hn

omit [FiniteDimensional ℝ V] in
private theorem finrank_sub_one_ne_zero (hn : Module.finrank ℝ V ≠ 1) :
    (Module.finrank ℝ V : ℝ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast hn)

omit [FiniteDimensional ℝ V] in
private theorem finrank_sub_two_ne_zero (hn : Module.finrank ℝ V ≠ 2) :
    (Module.finrank ℝ V : ℝ) - 2 ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast hn)

/-- For `finrank ℝ V ≠ 1`, `ricci (scalarPart r) = (scalar r / n) • g`. -/
theorem ricci_scalarPart (hdim : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  by_cases h0 : Module.finrank ℝ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0; ext u _; simp [Subsingleton.elim u 0]
  · rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]
    congr 1; field_simp [finrank_sub_one_ne_zero hdim]

/-- For `finrank ℝ V ≠ 1`, `scalarPart` preserves the scalar contraction. -/
theorem scalar_scalarPart (hdim : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    scalar (scalarPart r) = scalar r := by
  by_cases h0 : Module.finrank ℝ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    rw [scalar_apply, scalar_apply, Subsingleton.elim (ricci r) 0, Subsingleton.elim (ricci _) 0]
  · rw [scalarPart_apply, map_smul, scalar_constantCurvature, smul_eq_mul,
      div_mul_cancel₀ _ (mul_ne_zero (finrank_cast_ne_zero h0) (finrank_sub_one_ne_zero hdim))]

/-- `scalarPart r` has vanishing trace-free Ricci contraction in every dimension. -/
@[simp] theorem tracelessRicci_scalarPart (r : FourTensor V) : tracelessRicci (scalarPart r) = 0 :=
  if h1 : Module.finrank ℝ V = 1 then tracelessRicci_eq_zero_of_finrank_le_one _ h1.le else by
    rw [tracelessRicci_apply, ricci_scalarPart h1, scalar_scalarPart h1]; ext; simp

/-- `tracelessRicciPart r` has zero scalar contraction in every dimension. -/
@[simp] theorem scalar_tracelessRicciPart (r : FourTensor V) :
    scalar (tracelessRicciPart r) = 0 := by
  rw [tracelessRicciPart_apply, map_smul, scalar_kulkarniNomizu_innerₗ,
    metricTrace_tracelessRicci, mul_zero, smul_zero]

/-- For `finrank ℝ V ≠ 2`, `ricci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem ricci_tracelessRicciPart (hdim : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    ricci (tracelessRicciPart r) = tracelessRicci r := by
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    metricTrace_tracelessRicci, zero_smul, add_zero,
    inv_smul_smul₀ (finrank_sub_two_ne_zero hdim)]

/-- For `finrank ℝ V ≠ 2`, `tracelessRicci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem tracelessRicci_tracelessRicciPart (hdim : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
  rw [tracelessRicci_apply, ricci_tracelessRicciPart hdim, scalar_tracelessRicciPart]; ext; simp

/-- For `finrank ℝ V ≠ 1`, `weyl r` has zero scalar contraction. -/
theorem scalar_weyl (hdim : Module.finrank ℝ V ≠ 1) (r : FourTensor V) : scalar (weyl r) = 0 := by
  simp [weyl_apply, scalar_scalarPart hdim]

/-- For `finrank ℝ V ≠ 1` and `finrank ℝ V ≠ 2`, `weyl r` has zero Ricci contraction. -/
theorem ricci_weyl (h1 : Module.finrank ℝ V ≠ 1) (h2 : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    ricci (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, ricci_scalarPart h1, ricci_tracelessRicciPart h2,
    tracelessRicci_apply]; ext; simp

/-- For `finrank ℝ V ≠ 2`, `weyl r` has zero trace-free Ricci contraction. -/
theorem tracelessRicci_weyl (hdim : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    tracelessRicci (weyl r) = 0 :=
  if h1 : Module.finrank ℝ V = 1 then tracelessRicci_eq_zero_of_finrank_le_one _ h1.le else by
    rw [tracelessRicci_apply, ricci_weyl h1 hdim, scalar_weyl h1]; ext; simp

/-- `scalarPart` is idempotent in every dimension. -/
@[simp] theorem scalarPart_scalarPart (r : FourTensor V) :
    scalarPart (scalarPart r) = scalarPart r := by
  by_cases h1 : Module.finrank ℝ V = 1
  · rw [scalarPart_eq_zero_of_finrank_le_one h1.le, scalarPart_eq_zero_of_finrank_le_one h1.le]
  · rw [scalarPart_apply, scalar_scalarPart h1, ← scalarPart_apply]

/-- `tracelessRicciPart` is idempotent in every dimension. -/
@[simp] theorem tracelessRicciPart_tracelessRicciPart (r : FourTensor V) :
    tracelessRicciPart (tracelessRicciPart r) = tracelessRicciPart r := by
  by_cases h2 : Module.finrank ℝ V = 2
  · simp [tracelessRicciPart_eq_zero_of_finrank_eq_two h2]
  · rw [tracelessRicciPart_apply, tracelessRicci_tracelessRicciPart h2, ← tracelessRicciPart_apply]

/-- `scalarPart` annihilates `tracelessRicciPart` in every dimension. -/
@[simp] theorem scalarPart_tracelessRicciPart (r : FourTensor V) :
    scalarPart (tracelessRicciPart r) = 0 := by simp [scalarPart_apply]

/-- `tracelessRicciPart` annihilates `scalarPart` in every dimension. -/
@[simp] theorem tracelessRicciPart_scalarPart (r : FourTensor V) :
    tracelessRicciPart (scalarPart r) = 0 := by simp [tracelessRicciPart_apply]

/-- `scalarPart` annihilates `weyl` in every dimension. -/
@[simp] theorem scalarPart_weyl (r : FourTensor V) : scalarPart (weyl r) = 0 :=
  if h1 : Module.finrank ℝ V = 1 then scalarPart_eq_zero_of_finrank_le_one h1.le _ else by
    rw [scalarPart_apply, scalar_weyl h1, zero_div, zero_smul]

/-- `tracelessRicciPart` annihilates `weyl` in every dimension. -/
@[simp] theorem tracelessRicciPart_weyl (r : FourTensor V) : tracelessRicciPart (weyl r) = 0 :=
  if h2 : Module.finrank ℝ V = 2 then tracelessRicciPart_eq_zero_of_finrank_eq_two h2 _ else by
    rw [tracelessRicciPart_apply, tracelessRicci_weyl h2, map_zero, LinearMap.zero_apply, smul_zero]

/-- `weyl` annihilates `scalarPart` in every dimension. -/
@[simp] theorem weyl_scalarPart (r : FourTensor V) : weyl (scalarPart r) = 0 := by
  simp [weyl_apply]

/-- `weyl` annihilates `tracelessRicciPart` in every dimension. -/
@[simp] theorem weyl_tracelessRicciPart (r : FourTensor V) : weyl (tracelessRicciPart r) = 0 := by
  simp [weyl_apply]

/-- `weyl` is idempotent in every dimension. -/
@[simp] theorem weyl_weyl (r : FourTensor V) : weyl (weyl r) = weyl r := by simp [weyl_apply]

/-- In dimension at most `2`, every pair-antisymmetric four-tensor has `tracelessRicci r = 0`. -/
theorem tracelessRicci_eq_zero_of_finrank_le_two_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V ≤ 2)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    tracelessRicci r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · exact tracelessRicci_eq_zero_of_finrank_le_one r h1
  · have hdim2 : Module.finrank ℝ V = 2 := by omega
    rw [tracelessRicci_apply, ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two_of_antisymm
      hdim2 h₁ h₂, hdim2]; ext; simp

/-- In dimension at most `2`, every algebraic curvature tensor has `tracelessRicci r = 0`. -/
theorem IsAlgebraicCurvature.tracelessRicci_eq_zero_of_finrank_le_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 2) : tracelessRicci r = 0 :=
  tracelessRicci_eq_zero_of_finrank_le_two_of_antisymm hdim hr.antisymm_first hr.antisymm_last

private theorem weyl_eq_zero_of_finrank_le_two_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V ≤ 2)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    weyl r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · rw [eq_zero_of_finrank_le_one_of_antisymm_first h1 h₁, map_zero]
  · have hdim2 : Module.finrank ℝ V = 2 := by omega
    rw [weyl_apply, tracelessRicciPart_eq_zero_of_finrank_eq_two hdim2, sub_zero, sub_eq_zero,
      scalarPart_apply, hdim2]
    conv_lhs => rw [eq_smul_constantCurvature_of_finrank_eq_two_of_antisymm hdim2 h₁ h₂]
    norm_num

/-- For a first-pair antisymmetric four-tensor `r`, `scalar (weyl r) = 0` in every dimension. -/
theorem scalar_weyl_of_antisymm_first {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) : scalar (weyl r) = 0 := by
  by_cases h1 : Module.finrank ℝ V = 1
  · rw [eq_zero_of_finrank_le_one_of_antisymm_first h1.le h₁, map_zero, map_zero]
  · exact scalar_weyl h1 r

/-- For an algebraic curvature tensor `r`, `scalar (weyl r) = 0` in every dimension. -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := scalar_weyl_of_antisymm_first hr.antisymm_first

/-- For a pair-antisymmetric four-tensor `r`, `ricci (weyl r) = 0` in every dimension. -/
theorem ricci_weyl_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : ricci (weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 2 with h2 | h3
  · rw [weyl_eq_zero_of_finrank_le_two_of_antisymm h2 h₁ h₂, map_zero]
  · exact ricci_weyl (by omega) (by omega) r

/-- For an algebraic curvature tensor `r`, `ricci (weyl r) = 0` in every dimension. -/
theorem IsAlgebraicCurvature.ricci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.weyl r) = 0 := ricci_weyl_of_antisymm hr.antisymm_first hr.antisymm_last

/-- For a pair-antisymmetric four-tensor `r`, `tracelessRicci (weyl r) = 0` in every dimension. -/
theorem tracelessRicci_weyl_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : tracelessRicci (weyl r) = 0 := by
  rw [tracelessRicci_apply, ricci_weyl_of_antisymm h₁ h₂, scalar_weyl_of_antisymm_first h₁]
  ext; simp

/-- For an algebraic curvature tensor `r`, `tracelessRicci (weyl r) = 0` in every dimension. -/
theorem IsAlgebraicCurvature.tracelessRicci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    tracelessRicci (FourTensor.weyl r) = 0 :=
  tracelessRicci_weyl_of_antisymm hr.antisymm_first hr.antisymm_last

/-! ### Comparison with the Schouten tensor and vanishing on `h ⊙ g` -/

/-- The Schouten bilinear form `P(r) = (n - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (n - 1))) g)`.
This is the classical `n ≥ 3` Schouten tensor; because `0⁻¹ = 0` in `ℝ`, `schouten r` evaluates to
`0` when `n = 2` (even for `constantCurvature V`) and drops its scalar term when `n = 1`. -/
def schouten : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (ricci (V := V) +
    ((-((2 * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar (V := V))).smulRight (innerₗ V) :
      FourTensor V →ₗ[ℝ] BilinForm ℝ V))

/-- Definition of `schouten r`. -/
theorem schouten_apply (r : FourTensor V) :
    schouten r = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
      (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V) := by
  ext; simp only [schouten, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.neg_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring

/-- Pointwise evaluation of `schouten r u v`. -/
theorem schouten_apply_apply (r : FourTensor V) (u v : V) :
    schouten r u v = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ *
      (ricci r u v - scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) * ⟪u, v⟫) := by
  simp [schouten_apply]

/-- `schouten r` is symmetric whenever `ricci r` is symmetric. -/
theorem isSymm_schouten {r : FourTensor V} (hr : (ricci r).IsSymm) : (schouten r).IsSymm :=
  ⟨fun u v ↦ by simp [schouten_apply_apply, hr.eq u v, real_inner_comm u v]⟩

/-- For a bivector-symmetric four-tensor `r`, `schouten r` is symmetric. -/
theorem IsBivectorSymmetric.isSymm_schouten {r : FourTensor V} (hr : IsBivectorSymmetric r) :
    (schouten r).IsSymm := FourTensor.isSymm_schouten hr.isSymm_ricci

/-- For an algebraic curvature tensor `r`, `schouten r` is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_schouten {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (schouten r).IsSymm := FourTensor.isSymm_schouten hr.isSymm_ricci

/-- In dimension `2`, the Schouten bilinear form vanishes for every four-tensor `r`. -/
@[simp] theorem schouten_eq_zero_of_finrank_eq_two (hdim : Module.finrank ℝ V = 2)
    (r : FourTensor V) : schouten r = 0 := by
  ext; simp [schouten_apply_apply, hdim]

/-- In dimension at least `3`, the Schouten bilinear form splits as
`(n - 2)⁻¹ • tracelessRicci r + (scalar r / (2 n (n - 1))) • innerₗ V`. -/
theorem schouten_eq_add_of_three_le_finrank (hn : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    schouten r = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • tracelessRicci r +
      (scalar r / (2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V := by
  ext u v; simp only [schouten_apply_apply, tracelessRicci_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  field_simp [finrank_cast_ne_zero (V := V) (by omega), finrank_sub_one_ne_zero (V := V) (by omega),
    finrank_sub_two_ne_zero (V := V) (by omega)]
  ring

/-- Away from dimension `2`, `kulkarniNomizu (schouten r) (innerₗ V)` equals
`scalarPart r + tracelessRicciPart r` for every four-tensor `r`. -/
theorem kulkarniNomizu_schouten_innerₗ (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    kulkarniNomizu (schouten r) (innerₗ V) = scalarPart r + tracelessRicciPart r := by
  rcases lt_or_gt_of_ne hn with hnlt | hngt
  · have hkn (h k : BilinForm ℝ V) : kulkarniNomizu h k = 0 :=
      eq_zero_of_finrank_le_one_of_antisymm_first (by omega) (kulkarniNomizu_antisymm_first h k)
    have hcc : constantCurvature V = 0 :=
      isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one (by omega)
    simp [hkn, scalarPart_apply, hcc, tracelessRicciPart_apply]
  · rw [add_comm (scalarPart r), schouten_eq_add_of_three_le_finrank hngt r,
      tracelessRicciPart_apply, scalarPart_apply, constantCurvature_eq_half_smul_kulkarniNomizu]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_smul]
    congr 2
    field_simp [finrank_cast_ne_zero (V := V) (by omega),
      finrank_sub_one_ne_zero (V := V) (by omega)]

/-- Away from dimension `2`, `weyl r = r - kulkarniNomizu (schouten r) (innerₗ V)`. -/
theorem weyl_eq_sub_kulkarniNomizu_schouten (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    weyl r = r - kulkarniNomizu (schouten r) (innerₗ V) := by
  rw [kulkarniNomizu_schouten_innerₗ hn r, weyl_apply, sub_sub]

/-- Away from dimensions `1` and `2`, `metricTrace (schouten r) = scalar r / (2 (n - 1))`. -/
theorem metricTrace_schouten_of_finrank_ne_one_of_finrank_ne_two
    (hn₁ : Module.finrank ℝ V ≠ 1) (hn₂ : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    LinearMap.BilinMap.metricTrace (schouten r) =
      scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with hn0 | hn0
  · have : Subsingleton V := Module.finrank_zero_iff.mp hn0
    rw [Subsingleton.elim (schouten r) 0, scalar_apply, Subsingleton.elim (ricci r) 0]
    simp
  · simp [schouten_eq_add_of_three_le_finrank (by omega) r]
    field_simp [finrank_cast_ne_zero hn0, finrank_sub_one_ne_zero hn₁]

/-- Away from dimension `2`, if `r` is antisymmetric in its first pair,
`metricTrace (schouten r) = scalar r / (2 (n - 1))`. -/
theorem metricTrace_schouten_of_antisymm_first (hn : Module.finrank ℝ V ≠ 2) {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) :
    LinearMap.BilinMap.metricTrace (schouten r) =
      scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases eq_or_ne (Module.finrank ℝ V) 1 with hn1 | hn1
  · simp [eq_zero_of_finrank_le_one_of_antisymm_first hn1.le hr₁]
  · exact metricTrace_schouten_of_finrank_ne_one_of_finrank_ne_two hn1 hn r

/-- Away from dimension `2`, `metricTrace (schouten r) = scalar r / (2 (n - 1))` for every
algebraic curvature tensor `r`. -/
theorem IsAlgebraicCurvature.metricTrace_schouten {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : Module.finrank ℝ V ≠ 2) :
    LinearMap.BilinMap.metricTrace (schouten r) =
      scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) :=
  FourTensor.metricTrace_schouten_of_antisymm_first hn hr.antisymm_first

/-- In dimension at least `3`, `schouten` is a left inverse to `h ↦ kulkarniNomizu h (innerₗ V)`. -/
@[simp] theorem schouten_kulkarniNomizu_innerₗ_of_three_le_finrank (hn : 3 ≤ Module.finrank ℝ V)
    (h : BilinForm ℝ V) : schouten (kulkarniNomizu h (innerₗ V)) = h := by
  ext u v; simp only [schouten_apply_apply, ricci_kulkarniNomizu_innerₗ,
    scalar_kulkarniNomizu_innerₗ, LinearMap.add_apply, LinearMap.smul_apply, innerₗ_apply_apply,
    smul_eq_mul]
  field_simp [finrank_sub_one_ne_zero (V := V) (by omega),
    finrank_sub_two_ne_zero (V := V) (by omega)]
  ring

/-- In dimension at least `3`, `schouten (constantCurvature V) = (1 / 2) • innerₗ V`. -/
@[simp] theorem schouten_constantCurvature_of_three_le_finrank (hn : 3 ≤ Module.finrank ℝ V) :
    schouten (constantCurvature V) = (1 / 2 : ℝ) • innerₗ V := by
  rw [constantCurvature_eq_half_smul_kulkarniNomizu, map_smul,
    schouten_kulkarniNomizu_innerₗ_of_three_le_finrank hn]

/-- Away from dimension `1`, `schouten (weyl r) = 0` for every four-tensor `r`. -/
@[simp] theorem schouten_weyl_of_finrank_ne_one (hn : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    schouten (weyl r) = 0 := by
  rcases (by omega : Module.finrank ℝ V = 0 ∨ Module.finrank ℝ V = 2 ∨ 3 ≤ Module.finrank ℝ V)
    with h0 | h2 | h3
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    ext u _; simp [Subsingleton.elim u 0]
  · exact schouten_eq_zero_of_finrank_eq_two h2 (weyl r)
  · rw [schouten_eq_add_of_three_le_finrank h3, tracelessRicci_weyl (by omega) r,
      scalar_weyl hn r]; simp

/-- If `r` is antisymmetric in its first pair, `schouten (weyl r) = 0` in all dimensions. -/
theorem schouten_weyl_of_antisymm_first {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) : schouten (weyl r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 1 with hn1 | hn1
  · simp [eq_zero_of_finrank_le_one_of_antisymm_first hn1.le hr₁]
  · exact schouten_weyl_of_finrank_ne_one hn1 r

/-- For an algebraic curvature tensor `r`, `schouten (weyl r) = 0` in all dimensions. -/
@[simp] theorem IsAlgebraicCurvature.schouten_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : schouten (FourTensor.weyl r) = 0 :=
  FourTensor.schouten_weyl_of_antisymm_first hr.antisymm_first

/-- In every dimension, `weyl (kulkarniNomizu h (innerₗ V)) = 0` for every bilinear form `h`. -/
@[simp] theorem weyl_kulkarniNomizu_innerₗ (h : BilinForm ℝ V) :
    weyl (kulkarniNomizu h (innerₗ V)) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 2 with hle | hgt
  · exact weyl_eq_zero_of_finrank_le_two_of_antisymm hle
      (kulkarniNomizu_antisymm_first h (innerₗ V)) (kulkarniNomizu_antisymm_last h (innerₗ V))
  · rw [weyl_eq_sub_kulkarniNomizu_schouten (by omega),
      schouten_kulkarniNomizu_innerₗ_of_three_le_finrank hgt, sub_self]

/-! ### Operator form and trace-pairing orthogonality on bivectors -/

/-- On `⋀[ℝ]^2 V`, `scalarPart r` acts as `(Scal / (n (n - 1))) • symmMap₂ id id`. -/
theorem curvatureEndomorphism_scalarPart (r : FourTensor V) :
    curvatureEndomorphism (scalarPart r) =
      (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
        exteriorPower.symmMap₂ LinearMap.id LinearMap.id := by
  rw [scalarPart_apply, map_smul, curvatureEndomorphism_constantCurvature,
    exteriorPower.symmMap₂_self, exteriorPower.map_id]

/-- On `⋀[ℝ]^2 V`, `tracelessRicciPart r` acts as `(2 / (n - 2)) • symmMap₂ Ric₀♯ id`. -/
theorem curvatureEndomorphism_tracelessRicciPart (r : FourTensor V) :
    curvatureEndomorphism (tracelessRicciPart r) =
      (2 / ((Module.finrank ℝ V : ℝ) - 2)) •
        exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) LinearMap.id := by
  rw [tracelessRicciPart_apply, map_smul, curvatureEndomorphism_kulkarniNomizu,
    bilinFormToEnd_innerₗ, ← tracelessRicciEndomorphism_apply, smul_smul, inv_mul_eq_div]

/-- **Bivector operator decomposition** of `curvatureEndomorphism r` on `⋀[ℝ]^2 V`. -/
theorem curvatureEndomorphism_eq_add (r : FourTensor V) :
    curvatureEndomorphism r =
      (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
          exteriorPower.symmMap₂ LinearMap.id LinearMap.id +
        (2 / ((Module.finrank ℝ V : ℝ) - 2)) •
          exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) LinearMap.id +
        curvatureEndomorphism (weyl r) := by
  conv_lhs => rw [← weyl_add_tracelessRicciPart_add_scalarPart r]
  rw [map_add, map_add, curvatureEndomorphism_tracelessRicciPart, curvatureEndomorphism_scalarPart]
  abel

private theorem trace_curvatureEndomorphism_comp_scalarPart_eq_zero {r₁ : FourTensor V}
    (h₁ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![v, u, z, w])
    (h₂ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![u, v, w, z])
    (hscal : scalar r₁ = 0) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism r₁ ∘ₗ curvatureEndomorphism (scalarPart r₂)) = 0 := by
  rw [curvatureEndomorphism_scalarPart, exteriorPower.symmMap₂_self, exteriorPower.map_id,
    LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]
  have htr := scalar_eq_two_mul_trace_curvatureEndomorphism_of_antisymm h₁ h₂
  rw [hscal] at htr; exact mul_eq_zero_of_right _ (by linarith)

/-- `tracelessRicciPart r₁` and `scalarPart r₂` are orthogonal under the trace pairing (and hence
Hilbert–Schmidt orthogonal, since `curvatureEndomorphism (scalarPart r₂)` is self-adjoint). -/
theorem trace_curvatureEndomorphism_tracelessRicciPart_comp_scalarPart (r₁ r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (tracelessRicciPart r₁) ∘ₗ
          curvatureEndomorphism (scalarPart r₂)) = 0 :=
  trace_curvatureEndomorphism_comp_scalarPart_eq_zero (tracelessRicciPart_antisymm_first r₁)
    (tracelessRicciPart_antisymm_last r₁) (scalar_tracelessRicciPart r₁) r₂

/-- For pair-antisymmetric `r₁`, `weyl r₁` and `scalarPart r₂` are orthogonal under the trace
pairing (and hence Hilbert–Schmidt orthogonal, since `curvatureEndomorphism (scalarPart r₂)` is
self-adjoint). -/
theorem trace_curvatureEndomorphism_weyl_comp_scalarPart_of_antisymm {r₁ : FourTensor V}
    (h₁ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![v, u, z, w])
    (h₂ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![u, v, w, z]) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (weyl r₁) ∘ₗ curvatureEndomorphism (scalarPart r₂)) = 0 :=
  trace_curvatureEndomorphism_comp_scalarPart_eq_zero (weyl_antisymm_first h₁)
    (weyl_antisymm_last h₂) (scalar_weyl_of_antisymm_first h₁) r₂

/-- For algebraic curvature `r₁`, `weyl r₁` and `scalarPart r₂` are orthogonal under the trace
pairing and Hilbert–Schmidt inner product. -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_scalarPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ curvatureEndomorphism (scalarPart r₂)) = 0 :=
  trace_curvatureEndomorphism_weyl_comp_scalarPart_of_antisymm hr₁.antisymm_first hr₁.antisymm_last
      r₂

/-- For pair-antisymmetric `r₁`, `weyl r₁` and `tracelessRicciPart r₂` are orthogonal under the
trace pairing `(A, B) ↦ tr (A ∘ₗ B)` (which coincides with the Hilbert–Schmidt inner product
`tr (A† ∘ₗ B)` whenever at least one factor is self-adjoint). -/
theorem trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart_of_antisymm {r₁ : FourTensor V}
    (h₁ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![v, u, z, w])
    (h₂ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![u, v, w, z]) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (weyl r₁) ∘ₗ curvatureEndomorphism (tracelessRicciPart r₂)) = 0 := by
  rw [curvatureEndomorphism_tracelessRicciPart, LinearMap.comp_smul, map_smul, smul_eq_mul]
  have htr := two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id_of_antisymm
    (weyl_antisymm_first h₁) (weyl_antisymm_last h₂) (tracelessRicciEndomorphism r₂)
  have hcomp : (ricci (weyl r₁)).compLeft (tracelessRicciEndomorphism r₂) = 0 := by
    rw [ricci_weyl_of_antisymm h₁ h₂]; ext; simp
  rw [hcomp, map_zero] at htr; exact mul_eq_zero_of_right _ (by linarith)

/-- For algebraic curvature `r₁`, `weyl r₁` and `tracelessRicciPart r₂` are orthogonal under the
trace pairing `tr (A ∘ₗ B)` (and Hilbert–Schmidt inner product, since `curvatureEndomorphism
(weyl r₁)` is self-adjoint). -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ
          curvatureEndomorphism (FourTensor.tracelessRicciPart r₂)) = 0 :=
  trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart_of_antisymm hr₁.antisymm_first
      hr₁.antisymm_last r₂

/-! ### Low dimensions and orthogonal equivariance -/

private theorem weyl_eq_zero_of_finrank_eq_three_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V = 3)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    weyl r = 0 := by
  let b := stdOrthonormalBasis ℝ V
  refine toLinearMap₄_injective <| by
    rw [map_zero]
    refine LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
      ((two_ne_zero (α := ℝ)).isUnit.isSMulRegular ℝ) b.toBasis (by rw [Fintype.card_fin, hdim])
      (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using weyl_antisymm_first h₁ ..)
      (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using weyl_antisymm_last h₂ ..)
      fun u v ↦ ?_
    have h := congr($(ricci_weyl_of_antisymm h₁ h₂) u v)
    simp only [ricci_apply_orthonormalBasis b, LinearMap.zero_apply] at h
    simpa [weyl_antisymm_last h₂ _ u v] using h

/-- **In dimension at most `3`, the Weyl part of every pair-antisymmetric four-tensor vanishes.** -/
theorem weyl_eq_zero_of_finrank_le_three_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V ≤ 3)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    weyl r = 0 :=
  (lt_or_eq_of_le hdim).elim (fun h ↦ weyl_eq_zero_of_finrank_le_two_of_antisymm (by omega) h₁ h₂)
    (fun h ↦ weyl_eq_zero_of_finrank_eq_three_of_antisymm h h₁ h₂)

/-- **In dimension at most `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 3) : FourTensor.weyl r = 0 :=
  weyl_eq_zero_of_finrank_le_three_of_antisymm hdim hr.antisymm_first hr.antisymm_last

/-- For `finrank ℝ V ≤ 3`, pair-antisymmetric `r` equals `tracelessRicciPart r + scalarPart r`. -/
theorem eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three_of_antisymm {r : FourTensor V}
    (hdim : Module.finrank ℝ V ≤ 3)
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    r = tracelessRicciPart r + scalarPart r := by
  simpa [weyl_eq_zero_of_finrank_le_three_of_antisymm hdim h₁ h₂] using
    (weyl_add_tracelessRicciPart_add_scalarPart r).symm

/-- For `finrank ℝ V ≤ 3`, algebraic curvature `r` equals `tracelessRicciPart r + scalarPart r`. -/
theorem IsAlgebraicCurvature.eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 3) :
    r = FourTensor.tracelessRicciPart r + scalarPart r :=
  eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three_of_antisymm hdim hr.antisymm_first
      hr.antisymm_last

/-! ### Contraction adjointness, pairwise orthogonality, and the Pythagorean identity -/

section Orthogonality

variable {ι : Type*} [Fintype ι]

private theorem sum_kn_term₂ (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) (q : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
      ∑ j, ∑ l, h (b j) (b l) * ricci q (b j) (b l) := by
  have hl (i j : ι) : (∑ k, ∑ l, h (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l]) =
      ∑ l, h (b j) (b l) * q ![b i, b j, b i, b l] := by
    classical
    rw [Finset.sum_comm]
    simp [orthonormal_iff_ite.mp b.orthonormal]
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
theorem sum_kulkarniNomizu_innerₗ_mul_of_antisymm (b : OrthonormalBasis ι ℝ V)
    (h : BilinForm ℝ V) {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      kulkarniNomizu h (innerₗ V) ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      4 * ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) := by
  have hq₁₂ (u v z w : V) : q ![u, v, z, w] = q ![v, u, w, z] := by
    rw [hq₁ u v z w, hq₂ v u z w, neg_neg]
  simp only [kulkarniNomizu_apply, innerₗ_apply_apply, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_kn_term₁ b h hq₁₂, sum_kn_term₂ b h q, sum_kn_term₃ b h hq₁,
    sum_kn_term₄ b h hq₂]; ring

/-- **Adjointness of `h ↦ h ⊙ g` and `ricci`** for algebraic curvature tensors. -/
theorem IsAlgebraicCurvature.sum_kulkarniNomizu_innerₗ_mul {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) (h : BilinForm ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      kulkarniNomizu h (innerₗ V) ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      4 * ∑ i, ∑ k, h (b i) (b k) * ricci q (b i) (b k) :=
  FourTensor.sum_kulkarniNomizu_innerₗ_mul_of_antisymm b h hq.antisymm_first hq.antisymm_last

/-- Pairing `constantCurvature V` against `q` antisymmetric in its first pair gives
`2 * scalar q`. -/
theorem sum_constantCurvature_mul_of_antisymm_first (b : OrthonormalBasis ι ℝ V)
    {q : FourTensor V} (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) :
    (∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] * q ![b i, b j, b k, b l]) =
      2 * scalar q := by
  have hc (i j k l : ι) : constantCurvature V ![b i, b j, b k, b l] * q ![b i, b j, b k, b l] =
      innerₗ V (b j) (b l) * ⟪b i, b k⟫ * q ![b i, b j, b k, b l] -
        innerₗ V (b i) (b l) * ⟪b j, b k⟫ * q ![b i, b j, b k, b l] := by
    simp only [constantCurvature_apply, innerₗ_apply_apply]; ring
  simp_rw [hc, Finset.sum_sub_distrib]
  classical
  rw [sum_kn_term₂ b (innerₗ V) q, sum_kn_term₃ b (innerₗ V) hq₁]
  simp [orthonormal_iff_ite.mp b.orthonormal, ← LinearMap.BilinMap.metricTrace_eq_sum (ricci q) b,
    ← scalar_apply]
  ring

/-- The squared component norm of `constantCurvature V` in an orthonormal basis is `2 n (n - 1)`. -/
theorem sum_constantCurvature_sq (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, constantCurvature V ![b i, b j, b k, b l] ^ 2) =
      2 * (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) := by
  simp only [sq]
  rw [sum_constantCurvature_mul_of_antisymm_first b
      isAlgebraicCurvature_constantCurvature.antisymm_first,
    scalar_constantCurvature, mul_assoc]

/-- The squared component norm of `scalarPart r` is `2 * scalar r ^ 2 / (n (n - 1))`. -/
theorem sum_scalarPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with hn | hn
  · interval_cases h : Module.finrank ℝ V <;> simp [scalarPart_apply, h]
  · rw [scalarPart_apply]
    simp_rw [_root_.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, sum_constantCurvature_sq b]
    field_simp [finrank_cast_ne_zero (V := V) (by omega),
      finrank_sub_one_ne_zero (V := V) (by omega)]

/-- The squared component norm of `tracelessRicciPart r` is `(4 / (n - 2)) * ∑ |Ric₀(r)|²`. -/
theorem sum_tracelessRicciPart_sq (r : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) =
      (4 / ((Module.finrank ℝ V : ℝ) - 2)) * ∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2 := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with hn2 | hn2
  · simp [tracelessRicciPart_apply, hn2]
  · simp_rw [sq]; nth_rw 1 [tracelessRicciPart_apply]
    simp_rw [_root_.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [sum_kulkarniNomizu_innerₗ_mul_of_antisymm b (tracelessRicci r)
      (tracelessRicciPart_antisymm_first r) (tracelessRicciPart_antisymm_last r),
      ricci_tracelessRicciPart hn2 r]; ring

/-- `scalarPart r` and `tracelessRicciPart q` are orthogonal for all four-tensors `r, q`. -/
theorem sum_scalarPart_mul_tracelessRicciPart (r q : FourTensor V) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] *
      tracelessRicciPart q ![b i, b j, b k, b l]) = 0 := by
  rw [scalarPart_apply]
  simp_rw [_root_.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [sum_constantCurvature_mul_of_antisymm_first b (tracelessRicciPart_antisymm_first q),
    scalar_tracelessRicciPart, mul_zero, mul_zero]

/-- `scalarPart r` is orthogonal to `weyl q` whenever `q` is antisymmetric in its first pair. -/
theorem sum_scalarPart_mul_weyl_of_antisymm_first (r : FourTensor V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      scalarPart r ![b i, b j, b k, b l] * weyl q ![b i, b j, b k, b l]) = 0 := by
  rw [scalarPart_apply]
  simp_rw [_root_.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [sum_constantCurvature_mul_of_antisymm_first b (weyl_antisymm_first hq₁),
    scalar_weyl_of_antisymm_first hq₁, mul_zero, mul_zero]

/-- `scalarPart r` is orthogonal to `weyl q` for any algebraic curvature tensor `q`. -/
theorem IsAlgebraicCurvature.sum_scalarPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      scalarPart r ![b i, b j, b k, b l] * FourTensor.weyl q ![b i, b j, b k, b l]) = 0 :=
  FourTensor.sum_scalarPart_mul_weyl_of_antisymm_first r hq.antisymm_first b

/-- `tracelessRicciPart r` is orthogonal to `weyl q` for any skew-pair four-tensor `q`. -/
theorem sum_tracelessRicciPart_mul_weyl_of_antisymm (r : FourTensor V) {q : FourTensor V}
    (hq₁ : ∀ u v z w, q ![u, v, z, w] = -q ![v, u, z, w])
    (hq₂ : ∀ u v z w, q ![u, v, z, w] = -q ![u, v, w, z]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      tracelessRicciPart r ![b i, b j, b k, b l] * weyl q ![b i, b j, b k, b l]) = 0 := by
  rw [tracelessRicciPart_apply]
  simp_rw [_root_.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [sum_kulkarniNomizu_innerₗ_mul_of_antisymm b (tracelessRicci r)
    (weyl_antisymm_first hq₁) (weyl_antisymm_last hq₂), ricci_weyl_of_antisymm hq₁ hq₂]
  simp

/-- `tracelessRicciPart r` is orthogonal to `weyl q` for any algebraic curvature tensor `q`. -/
theorem IsAlgebraicCurvature.sum_tracelessRicciPart_mul_weyl (r : FourTensor V) {q : FourTensor V}
    (hq : IsAlgebraicCurvature q) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] *
      FourTensor.weyl q ![b i, b j, b k, b l]) = 0 :=
  FourTensor.sum_tracelessRicciPart_mul_weyl_of_antisymm r hq.antisymm_first hq.antisymm_last b

/-- **Pythagorean decomposition of any skew-pair four-tensor** into scalar, trace-free Ricci, and
Weyl component norms. -/
theorem sum_sq_eq_add_of_antisymm {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, weyl r ![b i, b j, b k, b l] ^ 2) := by
  have hmul2 (F : ι → ι → ι → ι → ℝ) : (∑ i, ∑ j, ∑ k, ∑ l, 2 * F i j k l) =
      2 * ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by simp_rw [← Finset.mul_sum]
  have hsq (a c d : ℝ) :
      (a + c + d) ^ 2 = a ^ 2 + c ^ 2 + d ^ 2 + 2 * (a * c) + 2 * (a * d) + 2 * (c * d) := by ring
  conv_lhs => rw [← weyl_add_tracelessRicciPart_add_scalarPart r]
  simp only [add_apply, hsq, Finset.sum_add_distrib, hmul2]
  have hwt (i j k l : ι) :
      weyl r ![b i, b j, b k, b l] * tracelessRicciPart r ![b i, b j, b k, b l] =
        tracelessRicciPart r ![b i, b j, b k, b l] * weyl r ![b i, b j, b k, b l] := mul_comm _ _
  have hws (i j k l : ι) :
      weyl r ![b i, b j, b k, b l] * scalarPart r ![b i, b j, b k, b l] =
        scalarPart r ![b i, b j, b k, b l] * weyl r ![b i, b j, b k, b l] := mul_comm _ _
  have hts (i j k l : ι) :
      tracelessRicciPart r ![b i, b j, b k, b l] * scalarPart r ![b i, b j, b k, b l] =
        scalarPart r ![b i, b j, b k, b l] * tracelessRicciPart r ![b i, b j, b k, b l] :=
    mul_comm _ _
  simp_rw [hwt, hws, hts, sum_scalarPart_mul_tracelessRicciPart r r b,
    sum_scalarPart_mul_weyl_of_antisymm_first r hr₁ b,
    sum_tracelessRicciPart_mul_weyl_of_antisymm r hr₁ hr₂ b]
  ring

/-- **Pythagorean decomposition of an algebraic curvature tensor.** -/
theorem IsAlgebraicCurvature.sum_sq_eq_add {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      (∑ i, ∑ j, ∑ k, ∑ l, scalarPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.tracelessRicciPart r ![b i, b j, b k, b l] ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) :=
  FourTensor.sum_sq_eq_add_of_antisymm hr.antisymm_first hr.antisymm_last b

/-- **Explicit norm-squared identity for skew-pair four-tensors**:
`∑ |r|² = (2 / (n (n - 1))) Scal(r)² + (4 / (n - 2)) ∑ |Ric₀(r)|² + ∑ |Weyl(r)|²`. -/
theorem sum_sq_eq_scalar_sq_add_sum_tracelessRicci_sq_add_sum_weyl_sq_of_antisymm
    {r : FourTensor V}
    (hr₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hr₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) +
        (4 / ((Module.finrank ℝ V : ℝ) - 2)) * (∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, weyl r ![b i, b j, b k, b l] ^ 2) := by
  rw [sum_sq_eq_add_of_antisymm hr₁ hr₂ b, sum_scalarPart_sq r b, sum_tracelessRicciPart_sq r b]

/-- **Explicit norm-squared identity for algebraic curvature tensors.** -/
theorem IsAlgebraicCurvature.sum_sq_eq_scalar_sq_add_sum_tracelessRicci_sq_add_sum_weyl_sq
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis ι ℝ V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] ^ 2) =
      2 * scalar r ^ 2 / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1)) +
        (4 / ((Module.finrank ℝ V : ℝ) - 2)) * (∑ i, ∑ k, tracelessRicci r (b i) (b k) ^ 2) +
        (∑ i, ∑ j, ∑ k, ∑ l, FourTensor.weyl r ![b i, b j, b k, b l] ^ 2) :=
  FourTensor.sum_sq_eq_scalar_sq_add_sum_tracelessRicci_sq_add_sum_weyl_sq_of_antisymm
    hr.antisymm_first hr.antisymm_last b

end Orthogonality

end TauCeti.FourTensor

namespace LinearIsometryEquiv

open TauCeti TauCeti.FourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `tracelessRicci` is equivariant under linear isometric equivalences. -/
theorem tracelessRicci_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        u v = tracelessRicci r (e u) (e v) := by
  simp only [tracelessRicci_apply, LinearMap.sub_apply, LinearMap.smul_apply, innerₗ_apply_apply,
    smul_eq_mul, ricci_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.inner_map_map]

/-- `ricciEndomorphism` is equivariant under linear isometric equivalences. -/
theorem comp_ricciEndomorphism_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    e.toLinearIsometry.toLinearMap ∘ₗ ricciEndomorphism
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      ricciEndomorphism r ∘ₗ e.toLinearIsometry.toLinearMap :=
  e.comp_bilinFormToEnd_of_eq (ricci_compContinuousLinearMap_linearIsometryEquiv e r)

/-- `tracelessRicciEndomorphism` is equivariant under linear isometric equivalences. -/
theorem comp_tracelessRicciEndomorphism_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    e.toLinearIsometry.toLinearMap ∘ₗ tracelessRicciEndomorphism
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      tracelessRicciEndomorphism r ∘ₗ e.toLinearIsometry.toLinearMap :=
  e.comp_bilinFormToEnd_of_eq (e.tracelessRicci_compContinuousLinearMap r)

/-- `scalarPart` is equivariant under linear isometric equivalences. -/
theorem scalarPart_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    scalarPart (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (scalarPart r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  toLinearMap₄_injective <| by
    ext u v z w; simp only [toLinearMap₄_apply, scalarPart_apply, _root_.smul_apply,
      compContinuousLinearMap_apply_vec, scalar_compContinuousLinearMap_linearIsometryEquiv,
      constantCurvature_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, e.toLinearEquiv.finrank_eq, e.inner_map_map]

/-- `tracelessRicciPart` is equivariant under linear isometric equivalences. -/
theorem tracelessRicciPart_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    tracelessRicciPart (r.compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap :=
  toLinearMap₄_injective <| by
    ext u v z w; simp only [toLinearMap₄_apply, tracelessRicciPart_apply, _root_.smul_apply,
      compContinuousLinearMap_apply_vec, kulkarniNomizu_apply, innerₗ_apply_apply,
      e.tracelessRicci_compContinuousLinearMap, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, e.toLinearEquiv.finrank_eq, e.inner_map_map]

/-- `schouten` is equivariant under linear isometric equivalences. -/
theorem schouten_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    schouten (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (schouten r).comp e.toLinearIsometry.toLinearMap e.toLinearIsometry.toLinearMap := by
  ext u v
  simp only [LinearMap.BilinForm.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, schouten_apply_apply,
    ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq,
    e.inner_map_map]

/-- `weyl` is equivariant under linear isometric equivalences. -/
theorem weyl_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  simp [weyl_apply, e.scalarPart_compContinuousLinearMap,
    e.tracelessRicciPart_compContinuousLinearMap]

end LinearIsometryEquiv
