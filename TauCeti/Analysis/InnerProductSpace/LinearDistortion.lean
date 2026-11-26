/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.OrientedJacobian
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import TauCeti.Algebra.Module.LinearMap.Defs
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Outer and inner distortion of a linear map

Let `V` and `W` be oriented real inner product spaces of the same finite dimension `n`, with
orientations `oV` and `oW`, and let `A : V →ₗ[ℝ] W` be linear, with operator norm `‖A‖`, minimal
stretch `ℓ(A)` (`LinearMap.minimalStretch`) and oriented Jacobian `J(A)`
(`Orientation.orientedJacobian`). The **outer distortion** `q_O(A) ∈ [0, ∞]` and the **inner
distortion** `q_I(A) ∈ [0, ∞)` are

    q_O(A) = ‖A‖ⁿ / J(A)   if J(A) > 0,     q_O(A) = 0   if A = 0 and J(A) ≤ 0,
    q_O(A) = ∞             if A ≠ 0 and J(A) ≤ 0;
    q_I(A) = J(A) / ℓ(A)ⁿ  if J(A) > 0,     q_I(A) = 0   if J(A) ≤ 0.

They are the pointwise quotients whose essential suprema are the outer and inner dilatations of a
quasiregular map. In positive dimension `J(0) = 0`, so `q_O(0) = 0`: the quotient `0 / 0` counts
as `0`, which makes constant maps `1`-quasiregular. An orientation-reversing or singular nonzero
map has `q_O = ∞` and `q_I = 0`; for instance the reflection `diag(-1, 1)` of `ℝ²` has
`‖R‖² / J(R) = -1`, while `q_O(R) = ∞`.

When `J(A) > 0` all singular values `σ₁ ≥ ⋯ ≥ σₙ` of `A` are positive, `J(A) = σ₁ ⋯ σₙ`, and

    q_O(A) = σ₁ⁿ / (σ₁ ⋯ σₙ),     q_I(A) = (σ₁ ⋯ σₙ) / σₙⁿ,

both at least `σ₁ / σₙ = ‖A‖ / ℓ(A) ≥ 1`.

## Main declarations

* `Orientation.outerDistortion`, `Orientation.innerDistortion`: `q_O(A)` and `q_I(A)`.
* `Orientation.outerDistortion_eq_top_iff`, `Orientation.outerDistortion_eq_zero_iff`: when
  `q_O(A)` is infinite or zero.
* `Orientation.innerDistortion_eq_zero_iff`, `Orientation.innerDistortion_pos_iff`: `q_I(A)`
  vanishes exactly when `J(A) ≤ 0`.
* `Orientation.outerDistortion_eq_ofReal_prod_singularValues`,
  `Orientation.innerDistortion_eq_prod_singularValues`: the singular-value formulas.
* `Orientation.ofReal_norm_div_minimalStretch_le_outerDistortion`,
  `Orientation.norm_div_minimalStretch_le_innerDistortion`: the outer distortion is always at
  least `‖A‖ / ℓ(A)`, and so is the inner distortion when `J(A) > 0`.
* `Orientation.one_le_outerDistortion`, `Orientation.one_le_innerDistortion`: both distortions are
  at least `1` when `J(A) > 0`.
* `Orientation.outerDistortion_linearIsometry_comp`,
  `Orientation.outerDistortion_comp_linearIsometryEquiv`, `Orientation.outerDistortion_smul`
  and their inner analogues: invariance under orientation-preserving isometries on either side and
  under scalars `c` with `cⁿ > 0`.
* `Orientation.outerDistortion_smul_of_pow_neg`, `Orientation.innerDistortion_smul_of_pow_neg`:
  scaling a map with `J(A) ≥ 0` by `c` with `cⁿ < 0` (a negative scalar in odd dimension) makes
  `q_I = 0`, and also makes `q_O = ∞` when `A ≠ 0`.
* `Orientation.outerDistortion_neg_neg`, `Orientation.innerDistortion_neg_neg`: reversing both
  orientations changes neither distortion.
* `Orientation.outerDistortion_id`: the identity has outer distortion `1`.
* `Orientation.outerDistortion_linearIsometry`, `Orientation.outerDistortion_smul_linearIsometry`:
  a linear isometry `U` of oriented Jacobian `1`, and any multiple `c • U` with `cⁿ > 0`, has outer
  distortion `1`.
* `Orientation.outerDistortion_linearIsometryEquiv`,
  `Orientation.outerDistortion_linearIsometryEquiv_of_neg`: an isometric isomorphism has outer
  distortion `1` if it preserves orientation, and (in positive dimension) `∞` if it reverses
  orientation.

## References

* O. Martio, S. Rickman and J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), Section 2, (2.21)–(2.22).
-/

public section

noncomputable section

open Module
open scoped ENNReal

namespace Orientation

variable {V W X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] [Fact (finrank ℝ X = n)]

/-- The **outer distortion** `q_O(A) ∈ [0, ∞]` of a linear map `A` between oriented real inner
product spaces of the same dimension `n`: `‖A‖ⁿ / J(A)` when the oriented Jacobian `J(A)` is
positive, `0` for the zero map when `J(A) ≤ 0` (in positive dimension this is every zero map), and
`∞` for a nonzero map with `J(A) ≤ 0`. -/
def outerDistortion (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : ℝ≥0∞ :=
  open Classical in
  if 0 < oV.orientedJacobian oW A then
    ENNReal.ofReal (‖LinearMap.toContinuousLinearMap A‖ ^ n / oV.orientedJacobian oW A)
  else if A = 0 then 0 else ⊤

variable (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
  (oX : Orientation ℝ X (Fin n))

open Classical in
/-- The defining case split of the outer distortion. -/
theorem outerDistortion_def (A : V →ₗ[ℝ] W) :
    oV.outerDistortion oW A =
      if 0 < oV.orientedJacobian oW A then
        ENNReal.ofReal (‖LinearMap.toContinuousLinearMap A‖ ^ n / oV.orientedJacobian oW A)
      else if A = 0 then 0 else ⊤ :=
  (rfl)

/-! ### The three cases -/

theorem outerDistortion_of_pos {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A =
      ENNReal.ofReal (‖LinearMap.toContinuousLinearMap A‖ ^ n / oV.orientedJacobian oW A) := by
  simp [outerDistortion_def, h]

theorem outerDistortion_of_nonpos {A : V →ₗ[ℝ] W} (h : oV.orientedJacobian oW A ≤ 0)
    (hA : A ≠ 0) : oV.outerDistortion oW A = ⊤ := by
  simp [outerDistortion_def, h.not_gt, hA]

/-- In positive dimension the zero map has outer distortion `0`. In dimension `0` and for
orientations of the same sign it is `1` instead. -/
@[simp]
theorem outerDistortion_zero (hn : 0 < n) : oV.outerDistortion oW 0 = 0 := by
  simp [outerDistortion_def, oV.orientedJacobian_zero_of_pos oW hn]

/-- The zero map has outer distortion `0` when `J(0) ≤ 0`. -/
theorem outerDistortion_zero_of_nonpos (h : oV.orientedJacobian oW (0 : V →ₗ[ℝ] W) ≤ 0) :
    oV.outerDistortion oW 0 = 0 := by
  simp [outerDistortion_def, h.not_gt]

theorem outerDistortion_ne_top_of_pos {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A ≠ ⊤ := by
  simp [oV.outerDistortion_of_pos oW h]

/-- The outer distortion is infinite exactly for the nonzero maps with `J(A) ≤ 0`. -/
theorem outerDistortion_eq_top_iff {A : V →ₗ[ℝ] W} :
    oV.outerDistortion oW A = ⊤ ↔ A ≠ 0 ∧ oV.orientedJacobian oW A ≤ 0 := by
  rw [outerDistortion_def]
  split_ifs with h hA
  · simp [h.not_ge]
  · simp [hA]
  · simp [hA, not_lt.mp h]

/-- In positive dimension the outer distortion vanishes exactly at the zero map. -/
theorem outerDistortion_eq_zero_iff (hn : 0 < n) {A : V →ₗ[ℝ] W} :
    oV.outerDistortion oW A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ oV.outerDistortion_zero oW hn⟩
  by_contra hA
  rw [outerDistortion_def] at h
  split_ifs at h with hJ
  · rw [ENNReal.ofReal_eq_zero, div_nonpos_iff] at h
    rcases h with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact hJ.not_ge h₂
    · exact (pow_pos (LinearMap.norm_toContinuousLinearMap_pos hA) n).not_ge h₁
  · exact ENNReal.top_ne_zero h

/-- A nonzero linear map has nonzero outer distortion. -/
theorem outerDistortion_ne_zero {A : V →ₗ[ℝ] W} (hA : A ≠ 0) :
    oV.outerDistortion oW A ≠ 0 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
    exact absurd (LinearMap.ext fun x ↦ by simp [Subsingleton.elim x 0]) hA
  exact fun h ↦ hA ((oV.outerDistortion_eq_zero_iff oW hn).mp h)

/-- A map of finite nonzero outer distortion has positive oriented Jacobian. -/
theorem orientedJacobian_pos_of_outerDistortion_ne_zero_of_ne_top {A : V →ₗ[ℝ] W}
    (h0 : oV.outerDistortion oW A ≠ 0) (htop : oV.outerDistortion oW A ≠ ⊤) :
    0 < oV.orientedJacobian oW A := by
  by_contra hJ
  by_cases hA : A = 0
  · subst hA
    exact h0 (oV.outerDistortion_zero_of_nonpos oW (not_lt.mp hJ))
  · exact htop ((oV.outerDistortion_eq_top_iff oW).mpr ⟨hA, not_lt.mp hJ⟩)

/-- When `J(A) > 0`, the outer distortion is at least `1`: Hadamard's inequality
`J(A) ≤ ‖A‖ⁿ`. -/
theorem one_le_outerDistortion {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    1 ≤ oV.outerDistortion oW A := by
  rw [oV.outerDistortion_of_pos oW h, ENNReal.one_le_ofReal, one_le_div h]
  exact (le_abs_self _).trans (oV.abs_orientedJacobian_le oW A)

/-- Reversing both orientations changes no outer distortion. -/
@[simp]
theorem outerDistortion_neg_neg (A : V →ₗ[ℝ] W) :
    (-oV).outerDistortion (-oW) A = oV.outerDistortion oW A := by
  simp [outerDistortion_def]

/-! ### The inner distortion -/

variable [FiniteDimensional ℝ W] [FiniteDimensional ℝ X]

/-- The **inner distortion** `q_I(A) ∈ [0, ∞)` of a linear map `A` between oriented real inner
product spaces of the same dimension `n`: `J(A) / ℓ(A)ⁿ` when the oriented Jacobian `J(A)` is
positive, where `ℓ(A)` is the minimal stretch, and `0` otherwise. -/
def innerDistortion (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : ℝ :=
  if 0 < oV.orientedJacobian oW A then
    oV.orientedJacobian oW A / A.minimalStretch ^ n
  else 0

/-- The defining case split of the inner distortion. -/
theorem innerDistortion_def (A : V →ₗ[ℝ] W) :
    oV.innerDistortion oW A =
      if 0 < oV.orientedJacobian oW A then
        oV.orientedJacobian oW A / A.minimalStretch ^ n
      else 0 :=
  (rfl)

/-- Reversing both orientations changes no inner distortion. -/
@[simp]
theorem innerDistortion_neg_neg (A : V →ₗ[ℝ] W) :
    (-oV).innerDistortion (-oW) A = oV.innerDistortion oW A := by
  simp [innerDistortion_def]

theorem innerDistortion_of_pos {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    oV.innerDistortion oW A = oV.orientedJacobian oW A / A.minimalStretch ^ n := by
  simp [innerDistortion_def, h]

theorem innerDistortion_of_nonpos {A : V →ₗ[ℝ] W} (h : oV.orientedJacobian oW A ≤ 0) :
    oV.innerDistortion oW A = 0 := by
  simp [innerDistortion_def, h.not_gt]

/-- In positive dimension the zero map has inner distortion `0`. -/
@[simp]
theorem innerDistortion_zero (hn : 0 < n) : oV.innerDistortion oW 0 = 0 :=
  oV.innerDistortion_of_nonpos oW (oV.orientedJacobian_zero_of_pos oW hn).le

theorem innerDistortion_nonneg (A : V →ₗ[ℝ] W) : 0 ≤ oV.innerDistortion oW A := by
  rw [innerDistortion_def]
  split_ifs with h
  · exact div_nonneg h.le (pow_nonneg A.minimalStretch_nonneg n)
  · exact le_rfl

/-! ### Singular-value formulas and lower bounds -/

/-- The outer distortion of a map with `J(A) > 0` is `σ₁ⁿ / (σ₁ ⋯ σₙ)`. -/
theorem outerDistortion_eq_ofReal_prod_singularValues {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A =
      ENNReal.ofReal (A.singularValues 0 ^ n / ∏ i ∈ Finset.range n, A.singularValues i) := by
  rw [oV.outerDistortion_of_pos oW h, A.norm_toContinuousLinearMap_eq_singularValues_zero,
    oV.orientedJacobian_eq_prod_singularValues_of_nonneg oW h.le]

/-- The inner distortion of a map with `J(A) > 0` is `(σ₁ ⋯ σₙ) / σₙⁿ`. -/
theorem innerDistortion_eq_prod_singularValues {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.innerDistortion oW A =
      (∏ i ∈ Finset.range n, A.singularValues i) / A.singularValues (n - 1) ^ n := by
  rw [oV.innerDistortion_of_pos oW h, A.minimalStretch_def,
    oV.orientedJacobian_eq_prod_singularValues_of_nonneg oW h.le, (Fact.out : finrank ℝ V = n)]

/-- When `J(A) ≠ 0` in positive dimension, the minimal stretch is positive. -/
theorem minimalStretch_pos_of_orientedJacobian_ne_zero (hn : 0 < n) {A : V →ₗ[ℝ] W}
    (h : oV.orientedJacobian oW A ≠ 0) : 0 < A.minimalStretch :=
  A.minimalStretch_pos_of_normDet_ne_zero ((Fact.out : finrank ℝ V = n) ▸ hn)
    (oV.normDet_ne_zero_of_orientedJacobian_ne_zero oW h)

/-- When `J(A) ≠ 0`, the power `ℓ(A)ⁿ` is positive (in dimension `0` it is `1`). -/
theorem minimalStretch_pow_pos_of_orientedJacobian_ne_zero {A : V →ₗ[ℝ] W}
    (h : oV.orientedJacobian oW A ≠ 0) : 0 < A.minimalStretch ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact pow_pos (oV.minimalStretch_pos_of_orientedJacobian_ne_zero oW hn h) n

/-- In positive dimension, `‖A‖ ^ (n - 1) * ℓ(A)` bounds the oriented Jacobian from above:
`σ₁ ⋯ σₙ ≤ σ₁ⁿ⁻¹ σₙ` (`LinearMap.normDet_le_norm_pow_mul_minimalStretch`). In dimension `0` the
right side is `0` while `J(A) = ±1`. -/
theorem orientedJacobian_le_norm_pow_mul_minimalStretch (hn : 0 < n) (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A ≤
      ‖LinearMap.toContinuousLinearMap A‖ ^ (n - 1) * A.minimalStretch := by
  have hA := A.normDet_le_norm_pow_mul_minimalStretch ((Fact.out : finrank ℝ V = n) ▸ hn)
  rw [(Fact.out : finrank ℝ V = n)] at hA
  exact (oV.orientedJacobian_le_normDet oW A).trans hA

/-- When `J(A) ≥ 0`, `‖A‖ * ℓ(A) ^ (n - 1)` bounds the oriented Jacobian from below:
`σ₁ σₙⁿ⁻¹ ≤ σ₁ ⋯ σₙ` (`LinearMap.norm_mul_minimalStretch_pow_le_normDet`). -/
theorem norm_mul_minimalStretch_pow_le_orientedJacobian {A : V →ₗ[ℝ] W}
    (h : 0 ≤ oV.orientedJacobian oW A) :
    ‖LinearMap.toContinuousLinearMap A‖ * A.minimalStretch ^ (n - 1) ≤
      oV.orientedJacobian oW A := by
  have hA := A.norm_mul_minimalStretch_pow_le_normDet
  rwa [(Fact.out : finrank ℝ V = n), ← oV.orientedJacobian_eq_normDet_of_nonneg oW h] at hA

/-- The outer distortion is at least `‖A‖ / ℓ(A)`, which is `σ₁ / σₙ` when `J(A) > 0`. If
`J(A) ≤ 0`, the bound is trivial: either `A = 0` and the left side vanishes, or `q_O(A) = ∞`. -/
theorem ofReal_norm_div_minimalStretch_le_outerDistortion (A : V →ₗ[ℝ] W) :
    ENNReal.ofReal (‖LinearMap.toContinuousLinearMap A‖ / A.minimalStretch) ≤
      oV.outerDistortion oW A := by
  by_cases h : 0 < oV.orientedJacobian oW A
  swap
  · by_cases hA : A = 0
    · simp [hA]
    · simp [oV.outerDistortion_of_nonpos oW (not_lt.mp h) hA]
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
    simp
  rw [oV.outerDistortion_of_pos oW h]
  refine ENNReal.ofReal_le_ofReal ?_
  have hℓ := oV.minimalStretch_pos_of_orientedJacobian_ne_zero oW hn h.ne'
  have hpow : ‖LinearMap.toContinuousLinearMap A‖ ^ n =
      ‖LinearMap.toContinuousLinearMap A‖ * ‖LinearMap.toContinuousLinearMap A‖ ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  rw [div_le_div_iff₀ hℓ h, hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (oV.orientedJacobian_le_norm_pow_mul_minimalStretch oW hn A)
    (norm_nonneg _)

/-- When `J(A) > 0`, the inner distortion is at least `‖A‖ / ℓ(A) = σ₁ / σₙ`. -/
theorem norm_div_minimalStretch_le_innerDistortion {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    ‖LinearMap.toContinuousLinearMap A‖ / A.minimalStretch ≤ oV.innerDistortion oW A := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
    simpa using oV.innerDistortion_nonneg oW A
  rw [oV.innerDistortion_of_pos oW h]
  have hℓ := oV.minimalStretch_pos_of_orientedJacobian_ne_zero oW hn h.ne'
  have hpow : A.minimalStretch ^ n = A.minimalStretch ^ (n - 1) * A.minimalStretch := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [div_le_div_iff₀ hℓ (pow_pos hℓ n), hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (oV.norm_mul_minimalStretch_pow_le_orientedJacobian oW h.le)
    hℓ.le

/-- When `J(A) > 0`, the inner distortion is at least `1`: `ℓ(A)ⁿ ≤ J(A)`. -/
theorem one_le_innerDistortion {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    1 ≤ oV.innerDistortion oW A := by
  rw [oV.innerDistortion_of_pos oW h,
    one_le_div (oV.minimalStretch_pow_pos_of_orientedJacobian_ne_zero oW h.ne')]
  have := A.minimalStretch_pow_le_normDet
  rwa [(Fact.out : finrank ℝ V = n), ← oV.orientedJacobian_eq_normDet_of_nonneg oW h.le] at this

/-- The inner distortion vanishes exactly when `J(A) ≤ 0`. -/
theorem innerDistortion_eq_zero_iff {A : V →ₗ[ℝ] W} :
    oV.innerDistortion oW A = 0 ↔ oV.orientedJacobian oW A ≤ 0 := by
  refine ⟨fun h ↦ not_lt.mp fun hJ ↦ ?_, oV.innerDistortion_of_nonpos oW⟩
  have := oV.one_le_innerDistortion oW hJ
  rw [h] at this
  exact zero_lt_one.not_ge this

/-- The inner distortion is positive exactly when `J(A) > 0`. -/
theorem innerDistortion_pos_iff {A : V →ₗ[ℝ] W} :
    0 < oV.innerDistortion oW A ↔ 0 < oV.orientedJacobian oW A := by
  rw [(oV.innerDistortion_nonneg oW A).lt_iff_ne', Ne, innerDistortion_eq_zero_iff, not_le]

/-! ### Invariance under isometries and scalars -/

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] in
/-- Postcomposing with a linear isometry of oriented Jacobian `1` (orientation-preserving) changes
no outer distortion. -/
theorem outerDistortion_linearIsometry_comp (U : W →ₗᵢ[ℝ] X)
    (hU : oW.orientedJacobian oX U.toLinearMap = 1) (A : V →ₗ[ℝ] W) :
    oV.outerDistortion oX (U.toLinearMap ∘ₗ A) = oV.outerDistortion oW A := by
  rw [outerDistortion_def, outerDistortion_def, oV.orientedJacobian_comp_of_left_eq_one oW oX hU,
    LinearMap.norm_toContinuousLinearMap_linearIsometry_comp,
    LinearMap.comp_eq_zero_iff_of_injective U.injective]

omit [FiniteDimensional ℝ W] in
/-- Precomposing with an isometric isomorphism of oriented Jacobian `1` (orientation-preserving)
changes no outer distortion. -/
theorem outerDistortion_comp_linearIsometryEquiv (U : X ≃ₗᵢ[ℝ] V)
    (hU : oX.orientedJacobian oV (U : X →ₗ[ℝ] V) = 1) (A : V →ₗ[ℝ] W) :
    oX.outerDistortion oW (A ∘ₗ (U : X →ₗ[ℝ] V)) = oV.outerDistortion oW A := by
  rw [outerDistortion_def, outerDistortion_def, oX.orientedJacobian_comp_of_right_eq_one oV oW hU,
    LinearMap.norm_toContinuousLinearMap_comp_linearIsometryEquiv,
    LinearMap.comp_eq_zero_iff_of_surjective (f := (U : X →ₗ[ℝ] V)) U.surjective]

/-- Postcomposing with a linear isometry of oriented Jacobian `1` (orientation-preserving) changes
no inner distortion. -/
theorem innerDistortion_linearIsometry_comp (U : W →ₗᵢ[ℝ] X)
    (hU : oW.orientedJacobian oX U.toLinearMap = 1) (A : V →ₗ[ℝ] W) :
    oV.innerDistortion oX (U.toLinearMap ∘ₗ A) = oV.innerDistortion oW A := by
  rw [innerDistortion_def, innerDistortion_def, oV.orientedJacobian_comp_of_left_eq_one oW oX hU,
    LinearMap.minimalStretch_linearIsometry_comp]

/-- Precomposing with an isometric isomorphism of oriented Jacobian `1` (orientation-preserving)
changes no inner distortion. -/
theorem innerDistortion_comp_linearIsometryEquiv (U : X ≃ₗᵢ[ℝ] V)
    (hU : oX.orientedJacobian oV (U : X →ₗ[ℝ] V) = 1) (A : V →ₗ[ℝ] W) :
    oX.innerDistortion oW (A ∘ₗ (U : X →ₗ[ℝ] V)) = oV.innerDistortion oW A := by
  rw [innerDistortion_def, innerDistortion_def, oX.orientedJacobian_comp_of_right_eq_one oV oW hU,
    LinearMap.minimalStretch_comp_linearIsometryEquiv]

omit [FiniteDimensional ℝ W] in
/-- Scaling by `c` with `cⁿ > 0` (any `c > 0`, and any `c ≠ 0` in even dimension) changes no outer
distortion. -/
theorem outerDistortion_smul {c : ℝ} (hc : 0 < c ^ n) (A : V →ₗ[ℝ] W) :
    oV.outerDistortion oW (c • A) = oV.outerDistortion oW A := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
    rw [Subsingleton.elim (c • A) A]
  have hc0 : c ≠ 0 := (pow_ne_zero_iff hn.ne').mp hc.ne'
  have hpow : |c| ^ n = c ^ n := by rw [pow_abs, abs_of_pos hc]
  have hzero : c • A = 0 ↔ A = 0 := smul_eq_zero_iff_right hc0
  rw [outerDistortion_def, outerDistortion_def, hzero]
  simp only [oV.orientedJacobian_smul oW, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, hpow,
    mul_div_mul_left _ _ hc.ne', mul_pos_iff_of_pos_left hc]

/-- Scaling by `c` with `cⁿ > 0` (any `c > 0`, and any `c ≠ 0` in even dimension) changes no inner
distortion. -/
theorem innerDistortion_smul {c : ℝ} (hc : 0 < c ^ n) (A : V →ₗ[ℝ] W) :
    oV.innerDistortion oW (c • A) = oV.innerDistortion oW A := by
  have hpow : |c| ^ n = c ^ n := by rw [pow_abs, abs_of_pos hc]
  simp only [innerDistortion_def, oV.orientedJacobian_smul oW, LinearMap.minimalStretch_smul,
    Real.norm_eq_abs, mul_pow, hpow, mul_div_mul_left _ _ hc.ne', mul_pos_iff_of_pos_left hc]

omit [FiniteDimensional ℝ W] in
/-- Scaling a nonzero map with `J(A) ≥ 0` by `c` with `cⁿ < 0` (a negative scalar in odd
dimension) makes the outer distortion infinite. -/
theorem outerDistortion_smul_of_pow_neg {c : ℝ} (hc : c ^ n < 0) {A : V →ₗ[ℝ] W}
    (h : 0 ≤ oV.orientedJacobian oW A) (hA : A ≠ 0) : oV.outerDistortion oW (c • A) = ⊤ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hc)
  have hc0 : c ≠ 0 := (pow_ne_zero_iff hn.ne').mp hc.ne
  refine oV.outerDistortion_of_nonpos oW ?_ (smul_ne_zero hc0 hA)
  rw [oV.orientedJacobian_smul oW]
  exact mul_nonpos_of_nonpos_of_nonneg hc.le h

/-- Scaling a map with `J(A) ≥ 0` by `c` with `cⁿ < 0` (a negative scalar in odd dimension) makes
the inner distortion `0`. -/
theorem innerDistortion_smul_of_pow_neg {c : ℝ} (hc : c ^ n < 0) {A : V →ₗ[ℝ] W}
    (h : 0 ≤ oV.orientedJacobian oW A) : oV.innerDistortion oW (c • A) = 0 := by
  refine oV.innerDistortion_of_nonpos oW ?_
  rw [oV.orientedJacobian_smul oW]
  exact mul_nonpos_of_nonpos_of_nonneg hc.le h

/-! ### Isometries -/

/-- The identity has outer distortion `1`. -/
@[simp]
theorem outerDistortion_id : oV.outerDistortion oV LinearMap.id = 1 := by
  rw [oV.outerDistortion_of_pos oV (by simp)]
  rcases n with - | m
  · simp
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = m + 1)
  have hid : LinearMap.toContinuousLinearMap (LinearMap.id : V →ₗ[ℝ] V) =
      ContinuousLinearMap.id ℝ V :=
    ContinuousLinearMap.ext fun _ ↦ by simp
  simp [hid]

omit [FiniteDimensional ℝ W] in
/-- A linear isometry of oriented Jacobian `1` has outer distortion `1`. -/
theorem outerDistortion_linearIsometry (U : V →ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW U.toLinearMap = 1) :
    oV.outerDistortion oW U.toLinearMap = 1 := by
  have h := oV.outerDistortion_linearIsometry_comp oV oW U hU LinearMap.id
  rw [LinearMap.comp_id] at h
  rw [h, oV.outerDistortion_id]

omit [FiniteDimensional ℝ W] in
/-- An orientation-preserving isometric isomorphism has outer distortion `1`. -/
theorem outerDistortion_linearIsometryEquiv (U : V ≃ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = 1) :
    oV.outerDistortion oW (U : V →ₗ[ℝ] W) = 1 :=
  oV.outerDistortion_linearIsometry oW U.toLinearIsometry hU

omit [FiniteDimensional ℝ W] in
/-- A multiple `c • U` with `cⁿ > 0` (any `c > 0`, and any `c ≠ 0` in even dimension) of a linear
isometry `U` of oriented Jacobian `1` has outer distortion `1`. -/
theorem outerDistortion_smul_linearIsometry {c : ℝ} (hc : 0 < c ^ n) (U : V →ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW U.toLinearMap = 1) :
    oV.outerDistortion oW (c • U.toLinearMap) = 1 :=
  (oV.outerDistortion_smul oW hc _).trans (oV.outerDistortion_linearIsometry oW U hU)

/-- An orientation-preserving isometric isomorphism has inner distortion `1`. -/
theorem innerDistortion_linearIsometryEquiv (U : V ≃ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = 1) :
    oV.innerDistortion oW (U : V →ₗ[ℝ] W) = 1 := by
  have hUc : U.toLinearIsometry.toLinearMap = (U : V →ₗ[ℝ] W) :=
    LinearMap.ext fun _ ↦ by simp
  have hid : oV.innerDistortion oW (U : V →ₗ[ℝ] W) = oV.innerDistortion oV LinearMap.id := by
    simpa [hUc] using
      oV.innerDistortion_linearIsometry_comp oV oW U.toLinearIsometry (by rwa [hUc]) LinearMap.id
  rw [hid, oV.innerDistortion_of_pos oV (by simp)]
  rcases n with - | m
  · simp
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = m + 1)
  simp [LinearMap.minimalStretch_id]

omit [FiniteDimensional ℝ W] in
/-- In positive dimension an orientation-reversing isometric isomorphism, such as the reflection
`diag(-1, 1)` of `ℝ²`, has infinite outer distortion, although `‖U‖ⁿ / J(U) = -1`. -/
theorem outerDistortion_linearIsometryEquiv_of_neg (hn : 0 < n) (U : V ≃ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = -1) :
    oV.outerDistortion oW (U : V →ₗ[ℝ] W) = ⊤ := by
  refine oV.outerDistortion_of_nonpos oW (by rw [hU]; norm_num)
    (oV.ne_zero_of_orientedJacobian_ne_zero oW hn (by rw [hU]; norm_num))

/-- An orientation-reversing isometric isomorphism has inner distortion `0`. -/
theorem innerDistortion_linearIsometryEquiv_of_neg (U : V ≃ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = -1) :
    oV.innerDistortion oW (U : V →ₗ[ℝ] W) = 0 :=
  oV.innerDistortion_of_nonpos oW (by rw [hU]; norm_num)

end Orientation
