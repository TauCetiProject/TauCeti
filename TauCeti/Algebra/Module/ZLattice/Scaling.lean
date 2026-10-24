/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.Algebra.Module.ZLattice.Determinant

/-!
# Scaling a lattice

For a `ℤ`-submodule `L` of a real vector space `E` and `c : ℝ`, the *scaled lattice* `c • L` is the
image of `L` under multiplication by `c`, Mathlib's pointwise action of `ℝ` on `Submodule ℤ E`.
This file records how the dual, the covolume, the determinant and the integrality, evenness and
unimodularity of a lattice in a real inner product space behave under scaling.

For `c ≠ 0` the lattice `c • L` is the pullback of `L` along the linear automorphism `c⁻¹ • ·`
(`ZLattice.smul_eq_comap`), so a full lattice scales to a full lattice, with dual
`(c • L)^∨ = c⁻¹ • L^∨`, covolume `|c|ⁿ covolume L` and determinant `c²ⁿ det L` in dimension `n`.
A negative scalar gives the same lattice as its absolute value (`Submodule.neg_smul_eq_smul`).

Scaling is not an invariance of any of the three predicates. The lattice `c • L` is integral
exactly when `c² ⟪x, y⟫ ∈ ℤ` for all `x, y ∈ L` (`ZLattice.isIntegral_smul_iff`), and even exactly
when `c² ‖x‖² ∈ 2ℤ` for all `x ∈ L` (`ZLattice.isEven_smul_iff`). In particular, scaling by `√m`
for a natural number `m` preserves integrality: `√m • L` is integral when `L` is, and even when `L`
is even or when `L` is integral and `m` is even, with `det (√m • L) = mⁿ det L`. Thus `√2 • E₈` is
even and integral.

In positive dimension, scaling an integral lattice by `|c| > 1` never produces a unimodular
lattice, since its determinant is `c²ⁿ det L ≥ c²ⁿ > 1`; in particular `√m • L` is not unimodular
for `m > 1`, so `√2 • E₈` is not unimodular. A unimodular lattice scaled by `|c| ≠ 1` is never
unimodular. Positive dimension is needed: the zero lattice of the zero space is even, unimodular
and fixed by every scaling. Scaling *down* can create unimodularity, `(1/√2) • (√2 ℤ) = ℤ`, so the
first statement does not extend to `|c| < 1`.

## Main statements

* `ZLattice.smul_eq_comap`: for `c ≠ 0`, `c • L` is the pullback of `L` along `c⁻¹ • ·`.
* `ZLattice.dual_smul`: `(c • L)^∨ = c⁻¹ • L^∨` for `c ≠ 0`.
* `ZLattice.covolume_smul`, `ZLattice.det_smul`: `covolume (c • L) = |c|ⁿ covolume L` and
  `det (c • L) = c²ⁿ det L` for `c ≠ 0`.
* `ZLattice.isIntegral_smul_iff`, `ZLattice.isEven_smul_iff`: the exact criteria for `c • L` to be
  integral or even.
* `ZLattice.IsIntegral.sqrt_smul`, `ZLattice.IsEven.sqrt_smul`,
  `ZLattice.IsIntegral.isEven_sqrt_smul`: `√m • L` is integral when `L` is, and even when `L` is
  even or when `L` is integral and `m` is even.
* `ZLattice.det_sqrt_smul`: `det (√m • L) = mⁿ det L` for `m ≠ 0`.
* `ZLattice.IsIntegral.not_isUnimodular_smul`, `ZLattice.IsIntegral.not_isUnimodular_sqrt_smul`,
  `ZLattice.IsUnimodular.not_isUnimodular_smul`: in positive dimension, scaling an integral lattice
  by `|c| > 1`, or a unimodular lattice by `|c| ≠ 1`, does not give a unimodular lattice.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 1.
* J. H. Conway, N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer, 1999,
  Chapter 2, §2.
-/

public section

open Module Submodule MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace ZLattice

/-! ### Evenness -/

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)

/-- The scaled lattice `c • L` is even exactly when `c² ‖x‖² ∈ 2ℤ` for every `x ∈ L`. -/
theorem isEven_smul_iff (c : ℝ) :
    IsEven (c • L) ↔ ∀ x ∈ L, ∃ m : ℤ, c ^ 2 * ‖x‖ ^ 2 = 2 * m := by
  simp only [isEven_iff, mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

variable {L}

/-- Scaling an even lattice by the square root of a natural number gives an even lattice. -/
theorem IsEven.sqrt_smul (h : IsEven L) (m : ℕ) : IsEven (√(m : ℝ) • L) := by
  refine (isEven_smul_iff L _).mpr fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := isEven_iff.mp h x hx
  exact ⟨m * a, by rw [Real.sq_sqrt m.cast_nonneg, ha]; push_cast; ring⟩

end Seminormed

/-! ### Scaling as a change of variables -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)

/-- For `c ≠ 0`, the scaled lattice `c • L` is the pullback of `L` along the linear automorphism
`x ↦ c⁻¹ • x`. -/
theorem smul_eq_comap {c : ℝ} (hc : c ≠ 0) :
    c • L = ZLattice.comap ℝ L
      (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹ : E ≃L[ℝ] E).toLinearMap := by
  ext x
  rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set_iff_inv_smul_mem₀ hc,
    ← SetLike.mem_coe, coe_comap]
  simp [Units.smul_def]

instance [DiscreteTopology L] (c : ℝ) [NeZero c] : DiscreteTopology (c • L : Submodule ℤ E) := by
  rw [smul_eq_comap L (NeZero.ne c)]
  infer_instance

instance [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) [NeZero c] : IsZLattice ℝ (c • L) where
  span_top := by
    rw [smul_eq_comap L (NeZero.ne c)]
    exact IsZLattice.span_top

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]

/-- Scaling a full lattice by `c ≠ 0` multiplies its covolume by `|c|ⁿ`, where `n` is the dimension
of the space, for any Haar measure. -/
@[simp]
theorem covolume_smul {c : ℝ} (hc : c ≠ 0) (μ : Measure E := by volume_tac)
    [μ.IsAddHaarMeasure] :
    covolume (c • L) μ = |c| ^ finrank ℝ E * covolume L μ := by
  have hA : ((ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹ : E ≃L[ℝ] E) : E →ₗ[ℝ] E) =
      c⁻¹ • LinearMap.id := by
    ext x
    simp [Units.smul_def]
  rw [smul_eq_comap L hc, covolume_comap_continuousLinearEquiv L _ μ, hA, LinearMap.det_smul,
    LinearMap.det_id, mul_one, abs_pow, abs_inv, inv_pow, inv_inv]

end Normed

/-! ### Duality, integrality and the determinant -/

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : Submodule ℤ E)

/-- The dual of the scaled lattice `c • L` is `c⁻¹ • L^∨`, for `c ≠ 0`. -/
@[simp]
theorem dual_smul {c : ℝ} (hc : c ≠ 0) : dual (c • L) = c⁻¹ • dual L := by
  ext x
  refine Iff.trans ?_ (Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc) (dual L : Set E) x).symm
  rw [inv_inv, SetLike.mem_coe]
  simp only [mem_dual, mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, real_inner_smul_left, real_inner_smul_right]

/-- The scaled lattice `c • L` is integral exactly when `c² ⟪x, y⟫ ∈ ℤ` for all `x, y ∈ L`. -/
theorem isIntegral_smul_iff (c : ℝ) :
    IsIntegral (c • L) ↔ ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, c ^ 2 * ⟪x, y⟫ = m := by
  simp only [isIntegral_iff, mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, sq]

variable {L}

/-- Scaling an integral lattice by the square root of a natural number gives an integral
lattice. -/
theorem IsIntegral.sqrt_smul (h : IsIntegral L) (m : ℕ) : IsIntegral (√(m : ℝ) • L) := by
  refine (isIntegral_smul_iff L _).mpr fun x hx y hy ↦ ?_
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx y hy
  exact ⟨m * a, by rw [Real.sq_sqrt m.cast_nonneg, ha]; push_cast; ring⟩

/-- Scaling an integral lattice by the square root of an even natural number gives an even
lattice. -/
theorem IsIntegral.isEven_sqrt_smul (h : IsIntegral L) {m : ℕ} (hm : Even m) :
    IsEven (√(m : ℝ) • L) := by
  refine (isEven_smul_iff L _).mpr fun x hx ↦ ?_
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx x hx
  rw [real_inner_self_eq_norm_sq] at ha
  exact ⟨k * a, by rw [Real.sq_sqrt (k + k).cast_nonneg, ha]; push_cast; ring⟩

variable (L) [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]

/-- Scaling a full lattice by `c ≠ 0` multiplies its determinant by `c²ⁿ`, where `n` is the
dimension of the space. -/
@[simp]
theorem det_smul {c : ℝ} (hc : c ≠ 0) : det (c • L) = c ^ (2 * finrank ℝ E) * det L := by
  rw [det_def, det_def, covolume_smul L hc volume, mul_pow, ← pow_mul, mul_comm (finrank ℝ E),
    pow_mul, pow_mul, sq_abs]

/-- Scaling a full lattice by `√m`, for a nonzero natural number `m`, multiplies its determinant by
`mⁿ`, where `n` is the dimension of the space. -/
theorem det_sqrt_smul {m : ℕ} (hm : m ≠ 0) : det (√(m : ℝ) • L) = m ^ finrank ℝ E * det L := by
  rw [det_smul L (Real.sqrt_ne_zero'.mpr (by positivity)), pow_mul, Real.sq_sqrt m.cast_nonneg]

variable {L}

/-- In positive dimension, scaling a full integral lattice by `c` with `1 < |c|` never gives a
unimodular lattice: the determinant becomes `c²ⁿ det L > 1`. -/
theorem IsIntegral.not_isUnimodular_smul [Nontrivial E] (h : IsIntegral L) {c : ℝ}
    (hc : 1 < |c|) : ¬ IsUnimodular (c • L) := by
  have hc0 : c ≠ 0 := abs_pos.mp (one_pos.trans hc)
  have : NeZero c := ⟨hc0⟩
  intro hu
  have hdet := hu.det_eq_one
  rw [det_smul L hc0, pow_mul, ← sq_abs, ← pow_mul] at hdet
  have hlt : 1 < |c| ^ (2 * finrank ℝ E) :=
    one_lt_pow₀ hc (mul_ne_zero two_ne_zero finrank_pos.ne')
  nlinarith [h.one_le_det]

/-- In positive dimension, scaling a full integral lattice by `√m` for a natural number `m > 1`
never gives a unimodular lattice. For instance `√2 • E₈` is even and integral but not
unimodular. -/
theorem IsIntegral.not_isUnimodular_sqrt_smul [Nontrivial E] (h : IsIntegral L) {m : ℕ}
    (hm : 1 < m) : ¬ IsUnimodular (√(m : ℝ) • L) :=
  h.not_isUnimodular_smul <| by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.lt_sqrt zero_le_one, one_pow]
    exact_mod_cast hm

/-- In positive dimension, scaling a unimodular lattice by `c` with `|c| ≠ 1` never gives a
unimodular lattice. -/
theorem IsUnimodular.not_isUnimodular_smul [Nontrivial E] (h : IsUnimodular L) {c : ℝ}
    (hc : |c| ≠ 1) : ¬ IsUnimodular (c • L) := by
  intro hu
  rcases eq_or_ne c 0 with rfl | hc0
  · -- The lattice `0 • L` is zero, and the dual of the zero lattice is the whole space.
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hxd : x ∈ dual ((0 : ℝ) • L) := mem_dual.mpr fun y hy ↦ ⟨0, by simp_all⟩
    rw [← isUnimodular_iff_eq_dual.mp hu, zero_smul, zero_eq_bot, mem_bot] at hxd
    exact hx hxd
  · have : NeZero c := ⟨hc0⟩
    have hdet := hu.det_eq_one
    rw [det_smul L hc0, h.det_eq_one, mul_one, pow_mul, ← sq_abs, ← pow_mul,
      pow_eq_one_iff_of_nonneg (abs_nonneg c) (mul_ne_zero two_ne_zero finrank_pos.ne')] at hdet
    exact hc hdet

end InnerProductSpace

end ZLattice
