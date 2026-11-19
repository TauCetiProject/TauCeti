/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Projectivization.Action
public import TauCeti.Analysis.InnerProductSpace.QuaternionicStructure

/-!
# Transition probability between rays

For an inner product space `E` over `𝕜 = ℝ` or `ℂ`, the points of the projectivization `ℙ 𝕜 E` are
the rays of `E`; when `E` is a complex Hilbert space they are the pure states of quantum
mechanics. The transition probability between the rays of nonzero vectors `v` and `w` is
`‖⟪v, w⟫‖² / (‖v‖² ‖w‖²)`, the squared modulus of the inner product of unit representatives.

It does not depend on the chosen representatives, is symmetric, takes values in `[0, 1]`, equals
`1` exactly on equal rays and `0` exactly on orthogonal rays. Linear isometries, conjugate-linear
isometries and unitary operators preserve it. These are the symmetries of the ray space appearing
in Wigner's theorem, which asserts conversely that every bijection of the rays of a complex
Hilbert space preserving the transition probability comes from a unitary or antiunitary operator.

## Main definitions

* `Projectivization.rayTransitionProbability p q`: the transition probability
  `‖⟪p.rep, q.rep⟫‖² / (‖p.rep‖² ‖q.rep‖²)` between two rays.

## Main results

* `Projectivization.rayTransitionProbability_mk`: the same formula holds for arbitrary nonzero
  representatives.
* `Projectivization.rayTransitionProbability_comm`,
  `Projectivization.rayTransitionProbability_nonneg` and
  `Projectivization.rayTransitionProbability_le_one`: symmetry and values in `[0, 1]`.
* `Projectivization.rayTransitionProbability_eq_one_iff`: the value is `1` exactly for equal rays.
* `Projectivization.rayTransitionProbability_eq_zero_iff`: the value is `0` exactly for
  orthogonal rays.
* `Projectivization.rayTransitionProbability_map_linearIsometry`,
  `Projectivization.rayTransitionProbability_map_conjLinearIsometry` and
  `Projectivization.rayTransitionProbability_unitary_smul`: invariance under linear and
  conjugate-linear isometries and under the action of unitary operators.

## References

* D. S. Freed, *On Wigner's theorem*, Geometry & Topology Monographs 18 (2012), 83–89.
-/

public section

noncomputable section

open scoped InnerProductSpace LinearAlgebra.Projectivization

namespace Projectivization

section Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The transition probability `‖⟪v, w⟫‖² / (‖v‖² ‖w‖²)` between the rays `p = [v]` and `q = [w]`
of an inner product space, computed on the chosen representatives `p.rep` and `q.rep`; see
`Projectivization.rayTransitionProbability_mk` for arbitrary representatives. -/
def rayTransitionProbability (p q : ℙ 𝕜 E) : ℝ :=
  ‖⟪p.rep, q.rep⟫_𝕜‖ ^ 2 / (‖p.rep‖ ^ 2 * ‖q.rep‖ ^ 2)

/-- The transition probability between two rays may be computed on any nonzero representatives. -/
@[simp]
theorem rayTransitionProbability_mk {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    (mk 𝕜 v hv).rayTransitionProbability (mk 𝕜 w hw) =
      ‖⟪v, w⟫_𝕜‖ ^ 2 / (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep 𝕜 v hv
  obtain ⟨b, hb⟩ := exists_smul_eq_mk_rep 𝕜 w hw
  have hab : (‖(a : 𝕜)‖ * ‖(b : 𝕜)‖) ^ 2 ≠ 0 := by simp
  rw [rayTransitionProbability, ← ha, ← hb]
  simp only [Units.smul_def, inner_smul_left, inner_smul_right, norm_mul, RCLike.norm_conj,
    norm_smul]
  rw [← mul_div_mul_left (‖⟪v, w⟫_𝕜‖ ^ 2) (‖v‖ ^ 2 * ‖w‖ ^ 2) hab]
  ring

/-- The transition probability is symmetric. -/
theorem rayTransitionProbability_comm (p q : ℙ 𝕜 E) :
    p.rayTransitionProbability q = q.rayTransitionProbability p := by
  rw [rayTransitionProbability, rayTransitionProbability, norm_inner_symm, mul_comm]

theorem rayTransitionProbability_nonneg (p q : ℙ 𝕜 E) : 0 ≤ p.rayTransitionProbability q := by
  rw [rayTransitionProbability]
  positivity

/-- The transition probability is at most `1`, by the Cauchy–Schwarz inequality. -/
theorem rayTransitionProbability_le_one (p q : ℙ 𝕜 E) : p.rayTransitionProbability q ≤ 1 := by
  rw [rayTransitionProbability, ← mul_pow]
  exact div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2)
    (by positivity)

/-- The transition probability between the rays of `v` and `w` vanishes exactly when `v` and `w`
are orthogonal. -/
theorem rayTransitionProbability_mk_eq_zero_iff {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    (mk 𝕜 v hv).rayTransitionProbability (mk 𝕜 w hw) = 0 ↔ ⟪v, w⟫_𝕜 = 0 := by
  have h₀ : ‖v‖ = 0 ∨ ‖w‖ = 0 → ⟪v, w⟫_𝕜 = 0 := fun h ↦
    norm_le_zero_iff.1 <| (norm_inner_le_norm v w).trans (mul_eq_zero.2 h).le
  rw [rayTransitionProbability_mk]
  simpa using or_iff_left_of_imp h₀

end Seminormed

section Normed

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The transition probability between two rays is `1` exactly when they are equal, by the
equality case of the Cauchy–Schwarz inequality. -/
@[simp]
theorem rayTransitionProbability_eq_one_iff {p q : ℙ 𝕜 E} :
    p.rayTransitionProbability q = 1 ↔ p = q := by
  induction p using ind with | h v hv =>
  induction q using ind with | h w hw =>
  have hvw : 0 < ‖v‖ * ‖w‖ := by positivity
  -- The transition probability is `1` exactly in the equality case of Cauchy–Schwarz.
  have hcs : (mk 𝕜 v hv).rayTransitionProbability (mk 𝕜 w hw) = 1 ↔
      ‖⟪v, w⟫_𝕜‖ = ‖v‖ * ‖w‖ := by
    rw [rayTransitionProbability_mk, ← mul_pow, div_eq_one_iff_eq (by positivity)]
    exact pow_left_inj₀ (norm_nonneg _) hvw.le two_ne_zero
  rw [hcs, norm_inner_eq_norm_iff hv hw, eq_comm, mk_eq_mk_iff']
  refine ⟨fun ⟨r, _, h⟩ ↦ ⟨r, h.symm⟩, fun ⟨a, h⟩ ↦ ⟨a, ?_, h.symm⟩⟩
  rintro rfl
  exact hw (by simpa using h.symm)

@[simp]
theorem rayTransitionProbability_self (p : ℙ 𝕜 E) : p.rayTransitionProbability p = 1 :=
  rayTransitionProbability_eq_one_iff.2 rfl

/-- The transition probability between two rays vanishes exactly when they are orthogonal
lines. -/
theorem rayTransitionProbability_eq_zero_iff {p q : ℙ 𝕜 E} :
    p.rayTransitionProbability q = 0 ↔ p.submodule ⟂ q.submodule := by
  induction p using ind with | h v hv =>
  induction q using ind with | h w hw =>
  rw [rayTransitionProbability_mk_eq_zero_iff, submodule_mk, submodule_mk, Submodule.isOrtho_span]
  simp

/-- A linear isometry preserves the transition probability between rays. -/
@[simp]
theorem rayTransitionProbability_map_linearIsometry (f : E →ₗᵢ[𝕜] F) (p q : ℙ 𝕜 E) :
    (p.map f.toLinearMap f.injective).rayTransitionProbability (q.map f.toLinearMap f.injective) =
      p.rayTransitionProbability q := by
  induction p using ind with | h v hv =>
  induction q using ind with | h w hw =>
  simp [map_mk]

/-- A conjugate-linear isometry preserves the transition probability between rays. -/
@[simp]
theorem rayTransitionProbability_map_conjLinearIsometry (f : E →ₗᵢ⋆[𝕜] F) (p q : ℙ 𝕜 E) :
    (p.map f.toLinearMap f.injective).rayTransitionProbability (q.map f.toLinearMap f.injective) =
      p.rayTransitionProbability q := by
  induction p using ind with | h v hv =>
  induction q using ind with | h w hw =>
  simp only [map_mk, rayTransitionProbability_mk, LinearIsometry.coe_toLinearMap,
    LinearIsometry.inner_map_map_eq_conj, RCLike.norm_conj, LinearIsometry.norm_map]

/-- The unitary operators of a Hilbert space act on its rays preserving the transition
probability. -/
@[simp]
theorem rayTransitionProbability_unitary_smul [CompleteSpace E] (u : unitary (E →L[𝕜] E))
    (p q : ℙ 𝕜 E) :
    (u • p).rayTransitionProbability (u • q) = p.rayTransitionProbability q := by
  induction p using ind with | h v hv =>
  induction q using ind with | h w hw =>
  simp [Submonoid.smul_def, ContinuousLinearMap.smul_def, Unitary.inner_map_map, Unitary.norm_map]

end Normed

end Projectivization
