/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Anisotropic quadratic maps over normed fields are coercive

Let `Q` be a continuous anisotropic quadratic map on a proper normed space `V` over a nontrivially
normed field. Then `Q` is bounded below by a multiple of the squared norm: there is `c > 0` with
`c * ‖x‖ ^ 2 ≤ ‖Q x‖` for every `x`. The constant is the minimum of `‖Q‖` on a compact shell
`‖k‖⁻¹ ≤ ‖x‖ ≤ 1`, where `‖k‖ > 1`, into which every nonzero vector rescales. A shell is used
rather than the unit sphere because over a general nontrivially normed field (for instance a
nonarchimedean one) a nonzero vector need not have a scalar multiple of norm exactly `1`, whereas
`rescale_to_shell` always rescales it into the shell.

Consequently the sublevel sets `{x | ‖Q x‖ ≤ r}` of `Q` are compact. In particular, for an
anisotropic quadratic form on a finite-dimensional space over a locally compact nontrivially normed
field such as `ℝ` or `ℚ_p`, every sublevel set is compact for the module topology. This is the
input that makes the orthogonal group of an anisotropic form compact: an isometry carries each
vector into a level set of `Q`.

## Main results

* `QuadraticMap.Anisotropic.exists_pos_mul_norm_sq_le`: an anisotropic quadratic map on a proper
  normed space is bounded below by a positive multiple of the squared norm.
* `QuadraticMap.Anisotropic.isCompact_setOf_norm_apply_le_of_continuous`: the sublevel sets of
  the norm of a continuous anisotropic quadratic map on a proper normed space are compact.
* `QuadraticMap.Anisotropic.isCompact_setOf_norm_apply_le`: the sublevel sets of the norm of an
  anisotropic quadratic form on a finite-dimensional space over a locally compact field are
  compact.
-/

public section

namespace QuadraticMap

section Normed

variable {K V N : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
  [ProperSpace V] [NormedAddCommGroup N] [NormedSpace K N]

/-- **Anisotropic quadratic maps are coercive.** A continuous anisotropic quadratic map on a proper
normed space over a nontrivially normed field is bounded below by a positive multiple of the
squared norm. -/
theorem Anisotropic.exists_pos_mul_norm_sq_le {Q : QuadraticMap K V N} (hQ : Q.Anisotropic)
    (hcont : Continuous Q) : ∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ ‖Q x‖ := by
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
  -- The shell `‖k‖⁻¹ ≤ ‖x‖ ≤ 1` is compact, and every nonzero vector rescales into it.
  let S : Set V := {x | ‖k‖⁻¹ ≤ ‖x‖} ∩ Metric.closedBall 0 1
  have hS : IsCompact S :=
    (isCompact_closedBall 0 1).inter_left (isClosed_le continuous_const continuous_norm)
  have hresc (x : V) (hx : x ≠ 0) : ∃ d : K, d • x ∈ S ∧ ‖d‖ * ‖x‖ ≤ 1 := by
    obtain ⟨d, -, hlt, hge, -⟩ := rescale_to_shell hk one_pos hx
    exact ⟨d, ⟨by simpa [one_div] using hge, by simpa using hlt.le⟩,
      by simpa [norm_smul] using hlt.le⟩
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · obtain ⟨d, hd, -⟩ := hresc x hx
      simp [hSe] at hd
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hSne (continuous_norm.comp hcont).continuousOn
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact (inv_pos.mpr (one_pos.trans hk)).not_ge (by simpa using hx₀.1)
  refine ⟨‖Q x₀‖, norm_pos_iff.mpr fun h => hx₀0 (hQ x₀ h), fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨d, hdS, hdx⟩ := hresc x hx
  have h₁ : ‖Q x₀‖ ≤ ‖d‖ * ‖d‖ * ‖Q x‖ := by
    simpa [QuadraticMap.map_smul, norm_smul] using hmin hdS
  calc ‖Q x₀‖ * ‖x‖ ^ 2 ≤ ‖d‖ * ‖d‖ * ‖Q x‖ * ‖x‖ ^ 2 := by gcongr
    _ = (‖d‖ * ‖x‖) ^ 2 * ‖Q x‖ := by ring
    _ ≤ 1 * ‖Q x‖ := by gcongr; exact pow_le_one₀ (by positivity) hdx
    _ = ‖Q x‖ := one_mul _

/-- The sublevel sets `{x | ‖Q x‖ ≤ r}` of a continuous anisotropic quadratic map on a proper
normed space over a nontrivially normed field are compact. -/
theorem Anisotropic.isCompact_setOf_norm_apply_le_of_continuous {Q : QuadraticMap K V N}
    (hQ : Q.Anisotropic) (hcont : Continuous Q) (r : ℝ) : IsCompact {x | ‖Q x‖ ≤ r} := by
  obtain ⟨c, hc, hle⟩ := hQ.exists_pos_mul_norm_sq_le hcont
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_norm.comp hcont) continuous_const)
    ((Metric.isBounded_closedBall (x := 0) (r := √(r / c))).subset fun y hy => ?_)
  rw [mem_closedBall_zero_iff, ← abs_of_nonneg (norm_nonneg y)]
  exact Real.abs_le_sqrt ((le_div_iff₀ hc).mpr (by linarith [hle y, hy.out]))

end Normed

section ModuleTopology

variable {K V : Type*} [NontriviallyNormedField K] [WeaklyLocallyCompactSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsModuleTopology K V]

/-- The sublevel sets `{x | ‖Q x‖ ≤ r}` of an anisotropic quadratic form on a finite-dimensional
space over a locally compact nontrivially normed field, such as `ℝ` or `ℚ_p`, are compact for the
module topology. -/
theorem Anisotropic.isCompact_setOf_norm_apply_le {Q : QuadraticForm K V} (hQ : Q.Anisotropic)
    (r : ℝ) : IsCompact {x | ‖Q x‖ ≤ r} := by
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  -- Transport to coordinates, where the sup norm is available.
  let b := Module.finBasis K V
  let e := TauCeti.ModuleTopology.equivFunHomeomorph b
  let Q' : QuadraticForm K (Fin (Module.finrank K V) → K) := Q.comp b.equivFun.symm.toLinearMap
  have hQ' : Q'.Anisotropic := fun y hy => b.equivFun.symm.injective (by
    simpa using hQ _ (by simpa [Q'] using hy))
  have hK := hQ'.isCompact_setOf_norm_apply_le_of_continuous Q'.continuous r
  have hpre : {x | ‖Q x‖ ≤ r} = e ⁻¹' {y | ‖Q' y‖ ≤ r} := by
    ext x
    simp [Q', e]
  rw [hpre]
  exact e.isCompact_preimage.mpr hK

end ModuleTopology

end QuadraticMap
