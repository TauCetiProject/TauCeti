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
splits as `r = weyl r + tracelessRicciPart r + scalarPart r`, with
`scalarPart r = (scalar r / (n (n - 1))) • constantCurvature V`,
`tracelessRicciPart r = (n - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V)`, and
`weyl r = r - scalarPart r - tracelessRicciPart r`.

In every dimension, `scalarPart`, `tracelessRicciPart`, and `weyl` are mutually annihilating
idempotent `O(n)`-equivariant projections preserving `algebraicCurvatureSubmodule V`. For general
four-tensors, `scalar (weyl r) = 0` (`n ≠ 1`), `tracelessRicci (weyl r) = 0` (`n ≠ 2`), and
`ricci (weyl r) = 0` (`n ≠ 1, 2`); for pair-antisymmetric four-tensors (in particular algebraic
curvature tensors), `weyl r` is trace-free in every dimension and vanishes for `n ≤ 3`.

Via `curvatureEndomorphism`, this gives the operator-wedge splitting of Böhm–Wilking (2008,
Section 2): `(scalar r / (n (n - 1))) • (id ∧ id) + (2 / (n - 2)) • (Ric₀♯ ∧ id) + W`. Under the
Hilbert–Schmidt trace pairing on `End(⋀[ℝ]^2 V)`, the trace-free Ricci and scalar summands are
orthogonal for all four-tensors, and the Weyl summand of any pair-antisymmetric four-tensor is
orthogonal to both in every dimension.

## Main definitions

* `TauCeti.FourTensor.tracelessRicci`, `TauCeti.FourTensor.ricciEndomorphism`,
  `TauCeti.FourTensor.tracelessRicciEndomorphism`, `TauCeti.FourTensor.scalarPart`,
  `TauCeti.FourTensor.tracelessRicciPart`, and `TauCeti.FourTensor.weyl`.

## Main results

* `TauCeti.FourTensor.weyl_add_tracelessRicciPart_add_scalarPart`, the nine unconditional
  projection laws, `TauCeti.FourTensor.ricci_weyl_of_antisymm`,
  `TauCeti.FourTensor.curvatureEndomorphism_eq_add`, Hilbert–Schmidt trace orthogonality, and
  `TauCeti.FourTensor.weyl_eq_zero_of_finrank_le_three_of_antisymm`.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
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
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V where
  toFun r := ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V
  map_add' _ _ := LinearMap.ext₂ fun _ _ ↦ by
    simp only [map_add, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, add_div]; ring
  map_smul' _ _ := LinearMap.ext₂ fun _ _ ↦ by
    simp only [map_smul, RingHom.id_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, mul_div_assoc]; ring

/-- Definition of `tracelessRicci`. -/
theorem tracelessRicci_apply (r : FourTensor V) :
    tracelessRicci r = ricci r - (scalar r / Module.finrank ℝ V) • innerₗ V := (rfl)

/-- The trace-free Ricci contraction has zero metric trace in every dimension. -/
@[simp] theorem bilinFormTrace_tracelessRicci (r : FourTensor V) :
    bilinFormTrace (tracelessRicci r) = 0 := by
  by_cases hn : Module.finrank ℝ V = 0
  · rw [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V)]
    exact Finset.sum_eq_zero fun i _ ↦ (Nat.not_lt_zero i.1 (hn ▸ i.2)).elim
  · have hsub := map_sub bilinFormTrace (ricci r) ((scalar r / Module.finrank ℝ V) • innerₗ V)
    rw [tracelessRicci_apply, hsub, map_smul, bilinFormTrace_inner, ← scalar_apply, smul_eq_mul,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn), sub_self]

/-- On a space of dimension at most `1`, `tracelessRicci r = 0` for every four-tensor `r`. -/
theorem tracelessRicci_eq_zero_of_finrank_le_one (r : FourTensor V)
    (hdim : Module.finrank ℝ V ≤ 1) : tracelessRicci r = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdim with h0 | h1
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    ext u _; simp [Subsingleton.elim u 0]
  · let b : OrthonormalBasis (Fin 1) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr h1)
    refine b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦ ?_
    rcases Fin.eq_zero i with rfl; rcases Fin.eq_zero j with rfl
    simp only [OrthonormalBasis.coe_toBasis, tracelessRicci_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, innerₗ_apply_apply, LinearMap.zero_apply, smul_eq_mul, h1,
      Nat.cast_one, div_one, scalar_apply, bilinFormTrace_eq_sum _ b, Fin.sum_univ_one,
      real_inner_self_eq_norm_sq, b.orthonormal.1 0, one_pow, mul_one, sub_self]

/-- `tracelessRicci r` is symmetric iff `ricci r` is symmetric. -/
@[simp] theorem isSymm_tracelessRicci_iff {r : FourTensor V} :
    (tracelessRicci r).IsSymm ↔ (ricci r).IsSymm :=
  ⟨fun h ↦ ⟨fun u v ↦ by
    have huv := h.eq u v
    simp only [tracelessRicci_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, real_inner_comm v u] at huv; linarith⟩,
   fun h ↦ ⟨fun u v ↦ by
    simp only [tracelessRicci_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      innerₗ_apply_apply, smul_eq_mul, h.eq u v, real_inner_comm v u]⟩⟩

/-- `tracelessRicci r` is symmetric for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.isSymm_tracelessRicci {r : FourTensor V} (hr : IsBivectorSymmetric r) :
    (tracelessRicci r).IsSymm := isSymm_tracelessRicci_iff.mpr hr.isSymm_ricci

/-- `tracelessRicci r` is symmetric for an algebraic curvature tensor `r`. -/
theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm :=
  isSymm_tracelessRicci_iff.mpr hr.isSymm_ricci

/-- The metric-raised Ricci endomorphism `Ric♯ : V →ₗ[ℝ] V`, with `⟪Ric♯ u, v⟫ = ricci r u v`. -/
def ricciEndomorphism : FourTensor V →ₗ[ℝ] Module.End ℝ V := bilinFormToEnd.comp ricci

/-- Pairing `ricciEndomorphism r u` with `v` recovers `ricci r u v`. -/
@[simp] theorem inner_ricciEndomorphism_left (r : FourTensor V) (u v : V) :
    ⟪ricciEndomorphism r u, v⟫ = ricci r u v := inner_bilinFormToEnd_left (ricci r) u v

/-- Lowering `ricciEndomorphism r` with `innerₗ V` recovers `ricci r`. -/
@[simp] theorem innerₗ_comp_ricciEndomorphism (r : FourTensor V) :
    (innerₗ V).comp (ricciEndomorphism r) = ricci r := innerₗ_comp_bilinFormToEnd (ricci r)

/-- The operator trace of `ricciEndomorphism r` equals `scalar r`. -/
@[simp] theorem trace_ricciEndomorphism (r : FourTensor V) :
    LinearMap.trace ℝ V (ricciEndomorphism r) = scalar r :=
  (trace_bilinFormToEnd (ricci r)).trans (scalar_apply r).symm

/-- `ricciEndomorphism r` is symmetric iff `ricci r` is symmetric. -/
theorem isSymmetric_ricciEndomorphism_iff {r : FourTensor V} :
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
  bilinFormToEnd.comp tracelessRicci

/-- Pairing `tracelessRicciEndomorphism r u` with `v` recovers `tracelessRicci r u v`. -/
@[simp] theorem inner_tracelessRicciEndomorphism_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEndomorphism r u, v⟫ = tracelessRicci r u v :=
  inner_bilinFormToEnd_left (tracelessRicci r) u v

/-- Lowering `tracelessRicciEndomorphism r` with `innerₗ V` recovers `tracelessRicci r`. -/
@[simp] theorem innerₗ_comp_tracelessRicciEndomorphism (r : FourTensor V) :
    (innerₗ V).comp (tracelessRicciEndomorphism r) = tracelessRicci r :=
  innerₗ_comp_bilinFormToEnd (tracelessRicci r)

/-- `tracelessRicciEndomorphism r = ricciEndomorphism r - (scalar r / n) • LinearMap.id`. -/
theorem tracelessRicciEndomorphism_eq (r : FourTensor V) :
    tracelessRicciEndomorphism r =
      ricciEndomorphism r - (scalar r / Module.finrank ℝ V) • LinearMap.id := by
  change bilinFormToEnd (tracelessRicci r) = _
  have hsub := map_sub bilinFormToEnd (ricci r) ((scalar r / Module.finrank ℝ V) • innerₗ V)
  rw [tracelessRicci_apply, hsub, map_smul, bilinFormToEnd_innerₗ]; rfl

/-- `tracelessRicciEndomorphism r` is symmetric iff `ricci r` is symmetric. -/
theorem isSymmetric_tracelessRicciEndomorphism_iff {r : FourTensor V} :
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
  (trace_bilinFormToEnd (tracelessRicci r)).trans (bilinFormTrace_tracelessRicci r)

/-! ### Scalar, trace-free Ricci, and Weyl curvature parts -/

/-- The scalar curvature part `(Scal / (n (n - 1))) • constantCurvature V` of a four-tensor. -/
def scalarPart : FourTensor V →ₗ[ℝ] FourTensor V where
  toFun r := (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
    constantCurvature V
  map_add' _ _ := by rw [map_add, add_div, add_smul]
  map_smul' _ _ := by rw [map_smul, RingHom.id_apply, smul_eq_mul, mul_div_assoc, mul_smul]

/-- Definition of `scalarPart r`. -/
theorem scalarPart_apply (r : FourTensor V) :
    scalarPart r = (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
      constantCurvature V := (rfl)

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
      (isSymm_tracelessRicci_iff.mpr h) ⟨fun u v ↦ real_inner_comm v u⟩))

/-- `tracelessRicciPart r` is an algebraic curvature tensor for bivector-symmetric `r`. -/
theorem IsBivectorSymmetric.tracelessRicciPart {r : FourTensor V} (hr : IsBivectorSymmetric r) :
    IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
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
  simp only [weyl_apply, sub_apply]
  rw [h₁ u v z w, (isAlgebraicCurvature_scalarPart r).antisymm_first u v z w,
    tracelessRicciPart_antisymm_first r u v z w]; ring

private theorem weyl_antisymm_last {r : FourTensor V}
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (u v z w : V) :
    weyl r ![u, v, z, w] = -weyl r ![u, v, w, z] := by
  simp only [weyl_apply, sub_apply]
  rw [h₂ u v z w, (isAlgebraicCurvature_scalarPart r).antisymm_last u v z w,
    tracelessRicciPart_antisymm_last r u v z w]; ring

private theorem scalarPart_eq_zero_of_finrank_le_one (hdim : Module.finrank ℝ V ≤ 1)
    (r : FourTensor V) : scalarPart r = 0 := by
  simp [scalarPart_apply, isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one hdim]

private theorem tracelessRicciPart_eq_zero_of_finrank_eq_two (hdim : Module.finrank ℝ V = 2)
    (r : FourTensor V) : tracelessRicciPart r = 0 := by
  rw [tracelessRicciPart_apply, hdim]; norm_num

/-- For `finrank ℝ V ≠ 1`, `ricci (scalarPart r) = (scalar r / n) • g`. -/
theorem ricci_scalarPart (hdim : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    ricci (scalarPart r) = (scalar r / Module.finrank ℝ V) • innerₗ V := by
  by_cases h0 : Module.finrank ℝ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    ext u _; simp [Subsingleton.elim u 0]
  · have hn1 : ((Module.finrank ℝ V : ℝ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hdim)
    rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]; congr 1; field_simp [hn1]

/-- For `finrank ℝ V ≠ 1`, `scalarPart` preserves the scalar contraction. -/
theorem scalar_scalarPart (hdim : Module.finrank ℝ V ≠ 1) (r : FourTensor V) :
    scalar (scalarPart r) = scalar r := by
  by_cases h0 : Module.finrank ℝ V = 0
  · have hscal (q : FourTensor V) : scalar q = 0 := by
      rw [scalar_apply, bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V)]
      exact Finset.sum_eq_zero fun i _ ↦ (Nat.not_lt_zero i.1 (h0 ▸ i.2)).elim
    rw [hscal, hscal]
  · have hn1 : ((Module.finrank ℝ V : ℝ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hdim)
    rw [scalarPart_apply, map_smul, scalar_constantCurvature, smul_eq_mul,
      div_mul_cancel₀ _ (mul_ne_zero (Nat.cast_ne_zero.mpr h0) hn1)]

/-- `scalarPart r` has vanishing trace-free Ricci contraction in every dimension. -/
@[simp] theorem tracelessRicci_scalarPart (r : FourTensor V) : tracelessRicci (scalarPart r) = 0 :=
  if h1 : Module.finrank ℝ V = 1 then tracelessRicci_eq_zero_of_finrank_le_one _ h1.le else by
    rw [tracelessRicci_apply, ricci_scalarPart h1, scalar_scalarPart h1]; ext; simp

/-- `tracelessRicciPart r` has zero scalar contraction in every dimension. -/
@[simp] theorem scalar_tracelessRicciPart (r : FourTensor V) :
    scalar (tracelessRicciPart r) = 0 := by
  rw [tracelessRicciPart_apply, map_smul, scalar_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, mul_zero, smul_zero]

/-- For `finrank ℝ V ≠ 2`, `ricci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem ricci_tracelessRicciPart (hdim : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    ricci (tracelessRicciPart r) = tracelessRicci r := by
  have hn2 : ((Module.finrank ℝ V : ℝ) - 2) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hdim)
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, zero_smul, add_zero, inv_smul_smul₀ hn2]

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
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (hdim : Module.finrank ℝ V ≤ 2) :
    tracelessRicci r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · exact tracelessRicci_eq_zero_of_finrank_le_one r h1
  · have hdim2 : Module.finrank ℝ V = 2 := by omega
    rw [tracelessRicci_apply, ricci_eq_half_scalar_smul_innerₗ_of_finrank_eq_two_of_antisymm
      h₁ h₂ hdim2, hdim2]; ext; simp

/-- In dimension at most `2`, every algebraic curvature tensor has `tracelessRicci r = 0`. -/
theorem IsAlgebraicCurvature.tracelessRicci_eq_zero_of_finrank_le_two {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 2) : tracelessRicci r = 0 :=
  tracelessRicci_eq_zero_of_finrank_le_two_of_antisymm hr.antisymm_first hr.antisymm_last hdim

private theorem weyl_eq_zero_of_finrank_le_two_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (hdim : Module.finrank ℝ V ≤ 2) :
    weyl r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h2
  · rw [eq_zero_of_finrank_le_one_of_antisymm_first h₁ h1, map_zero]
  · have hdim2 : Module.finrank ℝ V = 2 := by omega
    have hs : scalarPart r = r := by
      rw [scalarPart_apply, hdim2]
      conv_rhs => rw [eq_smul_constantCurvature_of_finrank_eq_two_of_antisymm h₁ h₂ hdim2]
      congr 1; norm_num
    rw [weyl_apply, hs, sub_self, tracelessRicciPart_eq_zero_of_finrank_eq_two hdim2, sub_zero]

/-- For a first-pair antisymmetric four-tensor `r`, `scalar (weyl r) = 0` in every dimension. -/
theorem scalar_weyl_of_antisymm_first {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) : scalar (weyl r) = 0 := by
  by_cases h1 : Module.finrank ℝ V = 1
  · rw [eq_zero_of_finrank_le_one_of_antisymm_first h₁ h1.le, map_zero, map_zero]
  · exact scalar_weyl h1 r

/-- For an algebraic curvature tensor `r`, `scalar (weyl r) = 0` in every dimension. -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := scalar_weyl_of_antisymm_first hr.antisymm_first

/-- For a pair-antisymmetric four-tensor `r`, `ricci (weyl r) = 0` in every dimension. -/
theorem ricci_weyl_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) : ricci (weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 2 with h2 | h3
  · rw [weyl_eq_zero_of_finrank_le_two_of_antisymm h₁ h₂ h2, map_zero]
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

/-! ### Operator form and Hilbert–Schmidt orthogonality on bivectors -/

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
    bilinFormToEnd_innerₗ, smul_smul, inv_mul_eq_div]; rfl

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

/-- `tracelessRicciPart` and `scalarPart` are Hilbert–Schmidt orthogonal for all four-tensors. -/
theorem trace_curvatureEndomorphism_tracelessRicciPart_comp_scalarPart (r₁ r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (tracelessRicciPart r₁) ∘ₗ
          curvatureEndomorphism (scalarPart r₂)) = 0 :=
  trace_curvatureEndomorphism_comp_scalarPart_eq_zero (tracelessRicciPart_antisymm_first r₁)
    (tracelessRicciPart_antisymm_last r₁) (scalar_tracelessRicciPart r₁) r₂

/-- For pair-antisymmetric `r₁`, `weyl r₁` and `scalarPart r₂` are Hilbert–Schmidt orthogonal. -/
theorem trace_curvatureEndomorphism_weyl_comp_scalarPart_of_antisymm {r₁ : FourTensor V}
    (h₁ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![v, u, z, w])
    (h₂ : ∀ u v z w, r₁ ![u, v, z, w] = -r₁ ![u, v, w, z]) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (weyl r₁) ∘ₗ curvatureEndomorphism (scalarPart r₂)) = 0 :=
  trace_curvatureEndomorphism_comp_scalarPart_eq_zero (weyl_antisymm_first h₁)
    (weyl_antisymm_last h₂) (scalar_weyl_of_antisymm_first h₁) r₂

/-- For algebraic curvature `r₁`, `weyl r₁` and `scalarPart r₂` are Hilbert–Schmidt orthogonal. -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_scalarPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ curvatureEndomorphism (scalarPart r₂)) = 0 :=
  trace_curvatureEndomorphism_weyl_comp_scalarPart_of_antisymm hr₁.antisymm_first hr₁.antisymm_last
    r₂

/-- For pair-antisymmetric `r₁`, `weyl r₁` and `tracelessRicciPart r₂` are orthogonal. -/
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

/-- For algebraic curvature `r₁`, `weyl r₁` and `tracelessRicciPart r₂` are orthogonal. -/
theorem IsAlgebraicCurvature.trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart
    {r₁ : FourTensor V} (hr₁ : IsAlgebraicCurvature r₁) (r₂ : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureEndomorphism (FourTensor.weyl r₁) ∘ₗ
          curvatureEndomorphism (FourTensor.tracelessRicciPart r₂)) = 0 :=
  trace_curvatureEndomorphism_weyl_comp_tracelessRicciPart_of_antisymm hr₁.antisymm_first
    hr₁.antisymm_last r₂

/-! ### Low dimensions and orthogonal equivariance -/

/-- **In dimension `3`, the Weyl part of every pair-antisymmetric four-tensor vanishes.** -/
theorem weyl_eq_zero_of_finrank_eq_three_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (hdim : Module.finrank ℝ V = 3) :
    weyl r = 0 := by
  let b := stdOrthonormalBasis ℝ V
  refine toLinearMap₄_injective <| by
    rw [map_zero]
    refine LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
      ((two_ne_zero (α := ℝ)).isUnit.isSMulRegular ℝ) b.toBasis (by rw [Fintype.card_fin, hdim])
      (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using weyl_antisymm_first h₁ ..)
      (fun _ _ _ _ ↦ by simpa only [toLinearMap₄_apply] using weyl_antisymm_last h₂ ..)
      fun u v ↦ ?_
    have hsum :
        (∑ i, toLinearMap₄ (weyl r) (b.toBasis i) u v (b.toBasis i)) = -ricci (weyl r) u v := by
      rw [ricci_apply_orthonormalBasis b, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by
        simpa only [toLinearMap₄_apply, OrthonormalBasis.coe_toBasis] using
          weyl_antisymm_last h₂ (b i) u v (b i)
    rw [hsum, ricci_weyl_of_antisymm h₁ h₂, LinearMap.zero_apply, LinearMap.zero_apply, neg_zero]

/-- **In dimension `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_eq_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V = 3) : FourTensor.weyl r = 0 :=
  weyl_eq_zero_of_finrank_eq_three_of_antisymm hr.antisymm_first hr.antisymm_last hdim

/-- **In dimension at most `3`, the Weyl part of every pair-antisymmetric four-tensor vanishes.** -/
theorem weyl_eq_zero_of_finrank_le_three_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (hdim : Module.finrank ℝ V ≤ 3) :
    weyl r = 0 :=
  (lt_or_eq_of_le hdim).elim (fun h ↦ weyl_eq_zero_of_finrank_le_two_of_antisymm h₁ h₂ (by omega))
    (weyl_eq_zero_of_finrank_eq_three_of_antisymm h₁ h₂)

/-- **In dimension at most `3`, the Weyl part of every algebraic curvature tensor vanishes.** -/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 3) : FourTensor.weyl r = 0 :=
  weyl_eq_zero_of_finrank_le_three_of_antisymm hr.antisymm_first hr.antisymm_last hdim

/-- For `finrank ℝ V ≤ 3`, pair-antisymmetric `r` equals `tracelessRicciPart r + scalarPart r`. -/
theorem eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (hdim : Module.finrank ℝ V ≤ 3) :
    r = tracelessRicciPart r + scalarPart r := by
  simpa [weyl_eq_zero_of_finrank_le_three_of_antisymm h₁ h₂ hdim] using
    (weyl_add_tracelessRicciPart_add_scalarPart r).symm

/-- For `finrank ℝ V ≤ 3`, algebraic curvature `r` equals `tracelessRicciPart r + scalarPart r`. -/
theorem IsAlgebraicCurvature.eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (hdim : Module.finrank ℝ V ≤ 3) :
    r = FourTensor.tracelessRicciPart r + scalarPart r :=
  eq_tracelessRicciPart_add_scalarPart_of_finrank_le_three_of_antisymm hr.antisymm_first
    hr.antisymm_last hdim

section Equivariance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `tracelessRicci` is equivariant under linear isometric equivalences. -/
theorem tracelessRicci_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        u v = tracelessRicci r (e u) (e v) := by
  have hdim : Module.finrank ℝ W = Module.finrank ℝ V := e.toLinearEquiv.finrank_eq
  simp only [tracelessRicci_apply, LinearMap.sub_apply, LinearMap.smul_apply, innerₗ_apply_apply,
    smul_eq_mul, ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, hdim, e.inner_map_map]

private theorem linearIsometryEquiv_comp_bilinFormToEnd_of_eq (e : W ≃ₗᵢ[ℝ] V)
    {B₁ : BilinForm ℝ W} {B₂ : BilinForm ℝ V} (h : ∀ u v, B₁ u v = B₂ (e u) (e v)) :
    e.toLinearIsometry.toLinearMap ∘ₗ bilinFormToEnd B₁ =
      bilinFormToEnd B₂ ∘ₗ e.toLinearIsometry.toLinearMap := by
  rw [show B₁ = B₂.compl₁₂ e.toLinearIsometry.toLinearMap e.toLinearIsometry.toLinearMap from
    LinearMap.ext₂ h]
  exact linearIsometryEquiv_comp_bilinFormToEnd_compl₁₂ e B₂

/-- `ricciEndomorphism` is equivariant under linear isometric equivalences. -/
theorem linearIsometryEquiv_comp_ricciEndomorphism_compContinuousLinearMap
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    e.toLinearIsometry.toLinearMap ∘ₗ ricciEndomorphism
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      ricciEndomorphism r ∘ₗ e.toLinearIsometry.toLinearMap :=
  linearIsometryEquiv_comp_bilinFormToEnd_of_eq e
    (ricci_compContinuousLinearMap_linearIsometryEquiv e r)

/-- `tracelessRicciEndomorphism` is equivariant under linear isometric equivalences. -/
theorem linearIsometryEquiv_comp_tracelessRicciEndomorphism_compContinuousLinearMap
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    e.toLinearIsometry.toLinearMap ∘ₗ tracelessRicciEndomorphism
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      tracelessRicciEndomorphism r ∘ₗ e.toLinearIsometry.toLinearMap :=
  linearIsometryEquiv_comp_bilinFormToEnd_of_eq e
    (tracelessRicci_compContinuousLinearMap_linearIsometryEquiv e r)

/-- `scalarPart` is equivariant under linear isometric equivalences. -/
theorem scalarPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    scalarPart (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (scalarPart r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  toLinearMap₄_injective <| by
    have hdim : Module.finrank ℝ W = Module.finrank ℝ V := e.toLinearEquiv.finrank_eq
    ext u v z w; simp only [toLinearMap₄_apply, scalarPart_apply, smul_apply,
      compContinuousLinearMap_apply_vec, scalar_compContinuousLinearMap_linearIsometryEquiv,
      constantCurvature_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, hdim, e.inner_map_map]

/-- `tracelessRicciPart` is equivariant under linear isometric equivalences. -/
theorem tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V)
    (r : FourTensor V) :
    tracelessRicciPart (r.compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap :=
  toLinearMap₄_injective <| by
    have hdim : Module.finrank ℝ W = Module.finrank ℝ V := e.toLinearEquiv.finrank_eq
    ext u v z w; simp only [toLinearMap₄_apply, tracelessRicciPart_apply, smul_apply,
      compContinuousLinearMap_apply_vec, kulkarniNomizu_apply, innerₗ_apply_apply,
      tracelessRicci_compContinuousLinearMap_linearIsometryEquiv,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, hdim,
      e.inner_map_map]

/-- `weyl` is equivariant under linear isometric equivalences. -/
theorem weyl_compContinuousLinearMap_linearIsometryEquiv (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  rw [weyl_apply, scalarPart_compContinuousLinearMap_linearIsometryEquiv,
    tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv]; ext m; rfl

end Equivariance

end TauCeti.FourTensor
