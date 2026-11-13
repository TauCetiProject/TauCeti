/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.ExteriorSquare
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Multilinear.CurvatureDimThree

/-!
# Orthogonal Ricci–Weyl decomposition of algebraic curvature tensors

On a finite-dimensional real inner product space `V` of dimension `n`, every four-tensor
`r : FourTensor V` splits canonically as

`r = weyl r + tracelessRicciPart r + scalarPart r`,

where:
* `scalarPart r = (scalar r / (n (n - 1))) • constantCurvature V` carries the scalar curvature;
* `tracelessRicciPart r = (n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)`, built from the
  trace-free Ricci form `tracelessRicci r = ricci r - (scalar r / n) • innerₗ V`, carries the
  trace-free Ricci curvature;
* `weyl r = r - scalarPart r - tracelessRicciPart r` is the Weyl four-tensor.

Each of the three maps preserves `algebraicCurvatureSubmodule V` and is `O(n)`-equivariant. For
`n ≥ 3`, their Ricci and scalar contractions show that `scalarPart`, `tracelessRicciPart`, and
`weyl` are mutually annihilating idempotent projections, and `weyl r` is completely trace-free
(`ricci (weyl r) = 0`, `scalar (weyl r) = 0`).

Passing to `⋀[ℝ]^2 V` via `curvatureEndomorphism` expresses the decomposition in Hamilton's
bivector-operator form

`curvatureEndomorphism r =
  (scalar r / (n (n - 1))) • exteriorPower.symmMap₂ LinearMap.id LinearMap.id +
  (2 / (n - 2)) • exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) LinearMap.id +
  curvatureEndomorphism (weyl r)`,

and proves that the three summands are pairwise orthogonal under the Hilbert–Schmidt trace pairing
`(L₁, L₂) ↦ tr (L₁ ∘ L₂)` on `End(⋀[ℝ]^2 V)` in every dimension. Finally, in dimension at most
`3` the Weyl part of every algebraic curvature tensor vanishes (`weyl r = 0`), so
`r = tracelessRicciPart r + scalarPart r` is completely determined by its Ricci contraction.

## Main definitions

* `TauCeti.FourTensor.tracelessRicci`: the trace-free Ricci bilinear form `Ric - (Scal / n) g`.
* `TauCeti.FourTensor.ricciEndomorphism` and `TauCeti.FourTensor.tracelessRicciEndomorphism`: the
  metric-raised Ricci and trace-free Ricci endomorphisms of `V`.
* `TauCeti.FourTensor.scalarPart`, `TauCeti.FourTensor.tracelessRicciPart`, and
  `TauCeti.FourTensor.weyl`: the three linear projections on `FourTensor V`.

## Main results

* `TauCeti.FourTensor.bilinFormTrace_tracelessRicci`: `tracelessRicci r` has zero metric trace in
  every dimension.
* `TauCeti.FourTensor.weyl_add_tracelessRicciPart_add_scalarPart`:
  `weyl r + tracelessRicciPart r + scalarPart r = r`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_weyl` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_weyl`: for an algebraic curvature tensor `r`,
  `weyl r` is trace-free in every dimension.
* `TauCeti.FourTensor.curvatureEndomorphism_eq_add` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_scalarPart` /
  `IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart`:
  operator decomposition on `⋀[ℝ]^2 V` and Hilbert–Schmidt orthogonality of its three pieces.
* `TauCeti.FourTensor.IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three`: `weyl r = 0` when
  `finrank ℝ V ≤ 3`.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Trace-free Ricci form and Ricci endomorphisms -/

/-- The trace-free Ricci contraction `Ric₀ = Ric - (Scal / n) g` of a four-tensor. -/
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V
  map_add' r q := by
    ext u v
    simp only [map_add, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, add_div]
    ring
  map_smul' c r := by
    ext u v
    simp only [map_smul, RingHom.id_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, mul_div_assoc]
    ring

/-- Definition of `tracelessRicci`. -/
theorem tracelessRicci_apply (r : FourTensor V) :
    tracelessRicci r = ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V :=
  (rfl)

/-- The trace-free Ricci contraction has zero metric trace in every dimension. -/
@[simp]
theorem bilinFormTrace_tracelessRicci (r : FourTensor V) :
    bilinFormTrace (tracelessRicci r) = 0 := by
  by_cases hn : Module.finrank ℝ V = 0
  · rw [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V)]
    exact Finset.sum_eq_zero fun i _ ↦ (Nat.not_lt_zero i.1 (hn ▸ i.2)).elim
  · have hn' : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hsub := map_sub bilinFormTrace (ricci r) ((scalar r / Module.finrank ℝ V) • innerₗ V)
    rw [tracelessRicci_apply, hsub, map_smul, bilinFormTrace_inner, ← scalar_apply, smul_eq_mul,
      div_mul_cancel₀ _ hn', sub_self]

/-- The trace-free Ricci contraction of an algebraic curvature tensor is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm :=
  ⟨fun u v ↦ by
    simp only [tracelessRicci_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, hr.isSymm_ricci.eq u v, real_inner_comm v u]⟩

/-- The metric-raised Ricci endomorphism `Ric♯ : V →ₗ[ℝ] V`, characterized by
`⟪ricciEndomorphism r u, v⟫ = ricci r u v`. -/
def ricciEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  ((LinearEquiv.refl ℝ V).arrowCongr
    (LinearMap.toContinuousLinearMap ≪≫ₗ
      (InnerProductSpace.toDual ℝ V).symm.toLinearEquiv)).toLinearMap.comp ricci

/-- Pairing `ricciEndomorphism r u` with `v` recovers `ricci r u v`. -/
@[simp]
theorem inner_ricciEndomorphism_left (r : FourTensor V) (u v : V) :
    ⟪ricciEndomorphism r u, v⟫ = ricci r u v := by
  simp [ricciEndomorphism, InnerProductSpace.toDual_symm_apply]

/-- Lowering `ricciEndomorphism r` with `innerₗ V` recovers `ricci r`. -/
@[simp]
theorem innerₗ_comp_ricciEndomorphism (r : FourTensor V) :
    (innerₗ V).comp (ricciEndomorphism r) = ricci r := by
  ext u v; exact inner_ricciEndomorphism_left r u v

/-- For an algebraic curvature tensor `r`, `ricciEndomorphism r` is symmetric. -/
theorem IsAlgebraicCurvature.isSymmetric_ricciEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (ricciEndomorphism r).IsSymmetric := fun u v ↦ by
  rw [inner_ricciEndomorphism_left, real_inner_comm (ricciEndomorphism r v) u,
    inner_ricciEndomorphism_left]
  exact hr.isSymm_ricci.eq u v

/-- The metric-raised trace-free Ricci endomorphism `Ric₀♯ : V →ₗ[ℝ] V`, characterized by
`⟪tracelessRicciEndomorphism r u, v⟫ = tracelessRicci r u v`. -/
def tracelessRicciEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  ((LinearEquiv.refl ℝ V).arrowCongr
    (LinearMap.toContinuousLinearMap ≪≫ₗ
      (InnerProductSpace.toDual ℝ V).symm.toLinearEquiv)).toLinearMap.comp tracelessRicci

/-- Pairing `tracelessRicciEndomorphism r u` with `v` recovers `tracelessRicci r u v`. -/
@[simp]
theorem inner_tracelessRicciEndomorphism_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEndomorphism r u, v⟫ = tracelessRicci r u v := by
  simp [tracelessRicciEndomorphism, InnerProductSpace.toDual_symm_apply]

/-- Lowering `tracelessRicciEndomorphism r` with `innerₗ V` recovers `tracelessRicci r`. -/
@[simp]
theorem innerₗ_comp_tracelessRicciEndomorphism (r : FourTensor V) :
    (innerₗ V).comp (tracelessRicciEndomorphism r) = tracelessRicci r := by
  ext u v; exact inner_tracelessRicciEndomorphism_left r u v

/-- For an algebraic curvature tensor `r`, `tracelessRicciEndomorphism r` is symmetric. -/
theorem IsAlgebraicCurvature.isSymmetric_tracelessRicciEndomorphism {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicciEndomorphism r).IsSymmetric := fun u v ↦ by
  rw [inner_tracelessRicciEndomorphism_left, real_inner_comm (tracelessRicciEndomorphism r v) u,
    inner_tracelessRicciEndomorphism_left]
  exact hr.isSymm_tracelessRicci.eq u v

/-- The trace of `tracelessRicciEndomorphism r` vanishes in every dimension. -/
@[simp]
theorem trace_tracelessRicciEndomorphism (r : FourTensor V) :
    LinearMap.trace ℝ V (tracelessRicciEndomorphism r) = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b]
  have hsum : (∑ i, ⟪b i, tracelessRicciEndomorphism r (b i)⟫) =
      bilinFormTrace (tracelessRicci r) := by
    rw [bilinFormTrace_eq_sum _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm (tracelessRicciEndomorphism r (b i)) (b i),
      inner_tracelessRicciEndomorphism_left]
  rw [hsum, bilinFormTrace_tracelessRicci]

/-! ### Scalar, trace-free Ricci, and Weyl curvature parts -/

/-- The scalar curvature part `(Scal / (n (n - 1))) • constantCurvature V` of a four-tensor. -/
def scalarPart : FourTensor V →ₗ[ℝ] FourTensor V where
  toFun r :=
    (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) • constantCurvature V
  map_add' r q := by rw [map_add, add_div, add_smul]
  map_smul' c r := by rw [map_smul, RingHom.id_apply, smul_eq_mul, mul_div_assoc, mul_smul]

/-- Definition of `scalarPart r`. -/
theorem scalarPart_apply (r : FourTensor V) :
    scalarPart r =
      (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) • constantCurvature V :=
  (rfl)

/-- The trace-free Ricci curvature part `(n - 2)⁻¹ • (Ric₀ ⊙ g)` of a four-tensor. -/
def tracelessRicciPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
    (kulkarniNomizu.flip (innerₗ V)).comp tracelessRicci

/-- Definition of `tracelessRicciPart r`. -/
theorem tracelessRicciPart_apply (r : FourTensor V) :
    tracelessRicciPart r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V) :=
  (rfl)

/-- The Weyl curvature part `W = r - scalarPart r - tracelessRicciPart r` of a four-tensor. -/
def weyl : FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.id - scalarPart - tracelessRicciPart

/-- Definition of `weyl r`. -/
theorem weyl_apply (r : FourTensor V) :
    weyl r = r - scalarPart r - tracelessRicciPart r :=
  (rfl)

/-- Every four-tensor decomposes as `weyl r + tracelessRicciPart r + scalarPart r`. -/
theorem weyl_add_tracelessRicciPart_add_scalarPart (r : FourTensor V) :
    weyl r + tracelessRicciPart r + scalarPart r = r := by
  rw [weyl_apply]; abel

/-- `scalarPart r` is always an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_scalarPart (r : FourTensor V) :
    IsAlgebraicCurvature (scalarPart r) :=
  mem_algebraicCurvatureSubmodule.mp <| Submodule.smul_mem _ _
    (mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature)

/-- For an algebraic curvature tensor `r`, `tracelessRicciPart r` is an algebraic curvature
tensor. -/
theorem IsAlgebraicCurvature.tracelessRicciPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
  have hg : LinearMap.BilinForm.IsSymm (innerₗ V) := ⟨fun u v ↦ real_inner_comm v u⟩
  mem_algebraicCurvatureSubmodule.mp <| Submodule.smul_mem _ _
    (mem_algebraicCurvatureSubmodule.mpr
      (isAlgebraicCurvature_kulkarniNomizu hr.isSymm_tracelessRicci hg))

/-- For an algebraic curvature tensor `r`, `weyl r` is an algebraic curvature tensor. -/
theorem IsAlgebraicCurvature.weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.weyl r) := by
  rw [weyl_apply]
  exact mem_algebraicCurvatureSubmodule.mp <| Submodule.sub_mem _
    (Submodule.sub_mem _ (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r)))
    (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart)

/-- For `2 ≤ finrank ℝ V`, `ricci (scalarPart r) = (scalar r / n) • g`. -/
theorem ricci_scalarPart (hdim : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  have hn1 : ((Module.finrank ℝ V : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hdim
    linarith
  rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]
  congr 1
  field_simp [hn1]

/-- For `2 ≤ finrank ℝ V`, `scalarPart` preserves the scalar contraction. -/
theorem scalar_scalarPart (hdim : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    scalar (scalarPart r) = scalar r := by
  have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : ((Module.finrank ℝ V : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hdim
    linarith
  rw [scalarPart_apply, map_smul, scalar_constantCurvature, smul_eq_mul,
    div_mul_cancel₀ _ (mul_ne_zero hn0 hn1)]

/-- For `2 ≤ finrank ℝ V`, `scalarPart r` has vanishing trace-free Ricci contraction. -/
theorem tracelessRicci_scalarPart (hdim : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    tracelessRicci (scalarPart r) = 0 := by
  rw [tracelessRicci_apply, ricci_scalarPart hdim, scalar_scalarPart hdim]
  ext; simp

/-- `tracelessRicciPart r` has zero scalar contraction in every dimension. -/
@[simp]
theorem scalar_tracelessRicciPart (r : FourTensor V) :
    scalar (tracelessRicciPart r) = 0 := by
  rw [tracelessRicciPart_apply, map_smul, scalar_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, mul_zero, smul_zero]

/-- For `3 ≤ finrank ℝ V`, `ricci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem ricci_tracelessRicciPart (hdim : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ricci (tracelessRicciPart r) = tracelessRicci r := by
  have hn2 : ((Module.finrank ℝ V : ℝ) - 2) ≠ 0 := by
    have : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hdim
    linarith
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, zero_smul, add_zero, inv_smul_smul₀ hn2]

/-- For `3 ≤ finrank ℝ V`, `tracelessRicci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem tracelessRicci_tracelessRicciPart (hdim : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
  rw [tracelessRicci_apply, ricci_tracelessRicciPart hdim, scalar_tracelessRicciPart]
  ext; simp

/-- For `2 ≤ finrank ℝ V`, `weyl r` has zero scalar contraction. -/
theorem scalar_weyl (hdim : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    scalar (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, scalar_scalarPart hdim, scalar_tracelessRicciPart, sub_self,
    sub_zero]

/-- For `3 ≤ finrank ℝ V`, `weyl r` has zero Ricci contraction. -/
theorem ricci_weyl (hdim : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ricci (weyl r) = 0 := by
  have hsub₁ := map_sub ricci (r - scalarPart r) (tracelessRicciPart r)
  have hsub₂ := map_sub ricci r (scalarPart r)
  rw [weyl_apply, hsub₁, hsub₂, ricci_scalarPart (by omega), ricci_tracelessRicciPart hdim,
    tracelessRicci_apply]
  ext; simp

/-- For `3 ≤ finrank ℝ V`, `weyl r` has zero trace-free Ricci contraction. -/
theorem tracelessRicci_weyl (hdim : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    tracelessRicci (weyl r) = 0 := by
  rw [tracelessRicci_apply, ricci_weyl hdim, scalar_weyl (by omega)]
  ext; simp

/-- `scalarPart` is idempotent for `2 ≤ finrank ℝ V`. -/
theorem scalarPart_scalarPart (hdim : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    scalarPart (scalarPart r) = scalarPart r := by
  rw [scalarPart_apply, scalar_scalarPart hdim, ← scalarPart_apply]

/-- `tracelessRicciPart` is idempotent for `3 ≤ finrank ℝ V`. -/
theorem tracelessRicciPart_tracelessRicciPart (hdim : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    tracelessRicciPart (tracelessRicciPart r) = tracelessRicciPart r := by
  rw [tracelessRicciPart_apply, tracelessRicci_tracelessRicciPart hdim, ← tracelessRicciPart_apply]

/-- `weyl` is idempotent for `3 ≤ finrank ℝ V`. -/
theorem weyl_weyl (hdim : 3 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    weyl (weyl r) = weyl r := by
  rw [weyl_apply, scalarPart_apply, scalar_weyl (by omega), zero_div, zero_smul,
    tracelessRicciPart_apply, tracelessRicci_weyl hdim, map_zero, LinearMap.zero_apply, smul_zero,
    sub_zero, sub_zero]

/-- In dimension at most `2`, every algebraic curvature tensor has vanishing trace-free Ricci
contraction. -/
theorem IsAlgebraicCurvature.tracelessRicci_eq_zero_of_finrank_le_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 2) :
    tracelessRicci r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · rw [hr.eq_zero_of_finrank_le_one h1, map_zero]
  · have hdim2 : Module.finrank ℝ V = 2 := by omega
    rw [tracelessRicci_apply, hr.ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two hdim2, hdim2]
    ext; simp

private theorem weyl_eq_zero_of_finrank_le_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 2) :
    FourTensor.weyl r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · rw [hr.eq_zero_of_finrank_le_one h1, map_zero]
  · have hdim2 : Module.finrank ℝ V = 2 := by omega
    have hs : scalarPart r = r := by
      rw [scalarPart_apply, hdim2]
      conv_rhs => rw [hr.eq_smul_constantCurvature_of_finrank_eq_two hdim2]
      congr 1; norm_num
    rw [weyl_apply, hs, sub_self, tracelessRicciPart_apply,
      hr.tracelessRicci_eq_zero_of_finrank_le_two hdim, map_zero, LinearMap.zero_apply,
      smul_zero, sub_zero]

/-- For an algebraic curvature tensor `r`, `weyl r` has zero scalar contraction in every
dimension. -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · rw [hr.eq_zero_of_finrank_le_one h1, map_zero, map_zero]
  · exact FourTensor.scalar_weyl h2 r

/-- For an algebraic curvature tensor `r`, `weyl r` has zero Ricci contraction in every
dimension. -/
theorem IsAlgebraicCurvature.ricci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 2 with h2 | h3
  · rw [weyl_eq_zero_of_finrank_le_two hr h2, map_zero]
  · exact FourTensor.ricci_weyl h3 r

/-- For an algebraic curvature tensor `r`, `weyl r` has zero trace-free Ricci contraction in every
dimension. -/
theorem IsAlgebraicCurvature.tracelessRicci_weyl {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    tracelessRicci (FourTensor.weyl r) = 0 := by
  rw [tracelessRicci_apply, hr.ricci_weyl, hr.scalar_weyl]
  ext; simp

/-! ### Operator form and Hilbert–Schmidt orthogonality on bivectors -/

/-- On `⋀[ℝ]^2 V`, `scalarPart r` acts as `(Scal / (n (n - 1))) • symmMap₂ id id`. -/
theorem curvatureEndomorphism_scalarPart (r : FourTensor V) :
    curvatureEndomorphism (scalarPart r) =
      (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
        exteriorPower.symmMap₂ LinearMap.id LinearMap.id := by
  rw [scalarPart_apply, map_smul, curvatureEndomorphism_constantCurvature,
    exteriorPower.symmMap₂_id]

/-- On `⋀[ℝ]^2 V`, `tracelessRicciPart r` acts as
`(2 / (n - 2)) • symmMap₂ (tracelessRicciEndomorphism r) id`. -/
theorem curvatureEndomorphism_tracelessRicciPart (r : FourTensor V) :
    curvatureEndomorphism (tracelessRicciPart r) =
      (2 / ((Module.finrank ℝ V : ℝ) - 2)) •
        exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) LinearMap.id := by
  have hk : kulkarniNomizu (tracelessRicci r) (innerₗ V) =
      kulkarniNomizu ((innerₗ V).comp (tracelessRicciEndomorphism r))
        ((innerₗ V).comp LinearMap.id) := by
    rw [innerₗ_comp_tracelessRicciEndomorphism, LinearMap.comp_id]
  rw [tracelessRicciPart_apply, hk, map_smul, curvatureEndomorphism_kulkarniNomizu, smul_smul,
    inv_mul_eq_div]

/-- **Bivector operator decomposition**: `curvatureEndomorphism r` splits into its scalar,
trace-free Ricci, and Weyl endomorphisms on `⋀[ℝ]^2 V`. -/
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

/-- The trace-free Ricci and scalar bivector operators are Hilbert–Schmidt orthogonal in every
dimension. -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_tracelessRicciPart_comp_scalarPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.tracelessRicciPart r₁) ∘ₗ
          curvatureEndomorphism (scalarPart r₂)) = 0 := by
  rw [curvatureEndomorphism_scalarPart, exteriorPower.symmMap₂_id, LinearMap.comp_smul,
    LinearMap.comp_id, map_smul, smul_eq_mul]
  have htr := hr₁.tracelessRicciPart.scalar_eq_two_mul_trace_curvatureEndomorphism
  rw [scalar_tracelessRicciPart] at htr
  have h0 : LinearMap.trace ℝ (⋀[ℝ]^2 V)
      (curvatureEndomorphism (FourTensor.tracelessRicciPart r₁)) = 0 := by linarith
  rw [h0, mul_zero]

/-- The Weyl and scalar bivector operators are Hilbert–Schmidt orthogonal in every dimension. -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_scalarPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ
          curvatureEndomorphism (scalarPart r₂)) = 0 := by
  rw [curvatureEndomorphism_scalarPart, exteriorPower.symmMap₂_id, LinearMap.comp_smul,
    LinearMap.comp_id, map_smul, smul_eq_mul]
  have htr := hr₁.weyl.scalar_eq_two_mul_trace_curvatureEndomorphism
  rw [hr₁.scalar_weyl] at htr
  have h0 : LinearMap.trace ℝ (⋀[ℝ]^2 V)
      (curvatureEndomorphism (FourTensor.weyl r₁)) = 0 := by linarith
  rw [h0, mul_zero]

/-- The Weyl and trace-free Ricci bivector operators are Hilbert–Schmidt orthogonal in every
dimension. -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ
          curvatureEndomorphism (FourTensor.tracelessRicciPart r₂)) = 0 := by
  rw [curvatureEndomorphism_tracelessRicciPart, LinearMap.comp_smul, map_smul, smul_eq_mul]
  have htr := hr₁.weyl.isPairSymmetric.two_mul_trace_curvatureEndomorphism_comp_symmMap₂_id
    (stdOrthonormalBasis ℝ V) (tracelessRicciEndomorphism r₂)
  rw [hr₁.ricci_weyl] at htr
  simp only [LinearMap.zero_apply, Finset.sum_const_zero] at htr
  have h0 : LinearMap.trace ℝ (⋀[ℝ]^2 V)
      (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ
        exteriorPower.symmMap₂ (tracelessRicciEndomorphism r₂) LinearMap.id) = 0 := by linarith
  rw [h0, mul_zero]

/-! ### Low dimensions and orthogonal equivariance -/

/-- **In dimension `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_eq_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V = 3) :
    FourTensor.weyl r = 0 := by
  let b := stdOrthonormalBasis ℝ V
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = 3 := by rw [Fintype.card_fin, hdim]
  refine toLinearMap₄_injective ?_
  rw [map_zero]
  refine LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
    ((two_ne_zero (α := ℝ)).isUnit.isSMulRegular ℝ) b.toBasis hcard
    (fun x y z w ↦ by simp only [toLinearMap₄_apply]; exact hr.weyl.antisymm_first x y z w)
    (fun x y z w ↦ by simp only [toLinearMap₄_apply]; exact hr.weyl.antisymm_last x y z w)
    fun u v ↦ ?_
  have hsum : (∑ i, toLinearMap₄ (FourTensor.weyl r) (b.toBasis i) u v (b.toBasis i)) =
      -ricci (FourTensor.weyl r) u v := by
    rw [ricci_apply_orthonormalBasis b, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [OrthonormalBasis.coe_toBasis, toLinearMap₄_apply]
    exact hr.weyl.antisymm_last (b i) u v (b i)
  rw [hsum, hr.ricci_weyl, LinearMap.zero_apply, LinearMap.zero_apply, neg_zero]

/-- **In dimension at most `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 3) :
    FourTensor.weyl r = 0 := by
  rcases lt_or_eq_of_le hdim with hlt | heq
  · exact weyl_eq_zero_of_finrank_le_two hr (by omega)
  · exact hr.weyl_eq_zero_of_finrank_eq_three heq

/-- In dimension at most `3`, every algebraic curvature tensor equals the sum of its trace-free
Ricci and scalar parts. -/
theorem IsAlgebraicCurvature.eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 3) :
    r = FourTensor.tracelessRicciPart r + scalarPart r := by
  simpa [hr.weyl_eq_zero_of_finrank_le_three hdim] using
    (weyl_add_tracelessRicciPart_add_scalarPart r).symm

section Equivariance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `tracelessRicci` is equivariant under linear isometric equivalences. -/
theorem tracelessRicci_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        u v =
      tracelessRicci r (e u) (e v) := by
  have hdim : Module.finrank ℝ W = Module.finrank ℝ V := e.toLinearEquiv.finrank_eq
  simp only [tracelessRicci_apply, LinearMap.sub_apply, LinearMap.smul_apply, innerₗ_apply_apply,
    smul_eq_mul, ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, hdim, e.inner_map_map]

/-- `scalarPart` is equivariant under linear isometric equivalences. -/
theorem scalarPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    scalarPart (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (scalarPart r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  have hdim : Module.finrank ℝ W = Module.finrank ℝ V := e.toLinearEquiv.finrank_eq
  refine toLinearMap₄_injective ?_
  ext u v z w
  simp only [toLinearMap₄_apply, scalarPart_apply, smul_apply, compContinuousLinearMap_apply_vec,
    scalar_compContinuousLinearMap_linearIsometryEquiv, constantCurvature_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, hdim,
    e.inner_map_map]

/-- `tracelessRicciPart` is equivariant under linear isometric equivalences. -/
theorem tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciPart
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  have hdim : Module.finrank ℝ W = Module.finrank ℝ V := e.toLinearEquiv.finrank_eq
  refine toLinearMap₄_injective ?_
  ext u v z w
  simp only [toLinearMap₄_apply, tracelessRicciPart_apply, smul_apply,
    compContinuousLinearMap_apply_vec, kulkarniNomizu_apply, innerₗ_apply_apply, smul_eq_mul,
    tracelessRicci_compContinuousLinearMap_linearIsometryEquiv,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, hdim,
    e.inner_map_map]

/-- `weyl` is equivariant under linear isometric equivalences. -/
theorem weyl_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  refine toLinearMap₄_injective ?_
  ext u v z w
  simp only [toLinearMap₄_apply, weyl_apply, sub_apply, compContinuousLinearMap_apply_vec,
    scalarPart_compContinuousLinearMap_linearIsometryEquiv,
    tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv]

end Equivariance

end TauCeti.FourTensor
