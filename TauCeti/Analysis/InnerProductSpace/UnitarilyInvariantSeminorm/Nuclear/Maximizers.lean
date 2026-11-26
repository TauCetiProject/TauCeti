/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Frobenius
public import TauCeti.Analysis.InnerProductSpace.Polar.Norm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Basic

/-!
# Maximizers in nuclear-norm trace duality

For a linear map `A` between finite-dimensional inner product spaces, a contraction `D` attains
the nuclear seminorm of `A` in the real trace pairing exactly when `D ∘ |A| = A`. Thus the
maximizing directions extend the canonical polar factor from the orthogonal complement of
`ker A`. The remaining block is a contraction from `ker A` to `(range A)ᗮ`. The maximizer
is unique exactly when `A` is injective or surjective. In every case the canonical polar
factor is the unique maximizer of least Frobenius seminorm.
-/

public section

open LinearMap Module
open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A contraction attains the nuclear seminorm in the real trace pairing exactly when it
factors the map through its modulus. -/
theorem re_trace_adjoint_comp_eq_nuclear_iff {D A : E →ₗ[𝕜] F} (hD : opNorm 𝕜 E F D ≤ 1) :
    RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A ↔ D ∘ₗ A.operatorAbs = A := by
  have hDv (i : Fin (finrank 𝕜 E)) : ‖D (A.rightSingularBasis i)‖ ≤ 1 := by
    have h := D.toContinuousLinearMap.le_opNorm (A.rightSingularBasis i)
    rw [LinearMap.coe_toContinuousLinearMap', A.rightSingularBasis.norm_eq_one, mul_one,
      ← opNorm_apply] at h
    exact h.trans hD
  have hle (i : Fin (finrank 𝕜 E)) :
      RCLike.re ⟪D (A.rightSingularBasis i), A.leftSingularVector i⟫_𝕜 ≤ 1 :=
    (RCLike.re_le_norm _).trans <| (norm_inner_le_norm _ _).trans <|
      (mul_le_mul (hDv i) (A.norm_leftSingularVector_le_one i)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  -- Expand the trace in the singular system of A.
  rw [A.comp_operatorAbs_eq_iff_apply_rightSingularBasis D,
    D.trace_adjoint_comp_eq_sum_singularValues_mul_inner A, map_sum, nuclear_apply,
    ← A.sum_fin_singularValues (fun s ↦ s) rfl]
  simp only [RCLike.re_ofReal_mul]
  -- Each summand is bounded above by its singular value, so equality holds termwise.
  rw [Finset.sum_eq_sum_iff_of_le (fun i _ ↦
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hle i) (A.singularValues_nonneg i))]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : A.singularValues i = 0
  · simp [hi]
  have hu : ‖A.leftSingularVector i‖ = 1 := A.orthonormal_leftSingularVector.1 ⟨i, hi⟩
  constructor
  · intro h _
    refine eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ((hDv i).trans_eq hu.symm) ?_
    rw [hu, one_pow]
    exact mul_left_cancel₀ hi (h.trans (mul_one _).symm)
  · intro h
    rw [h hi, inner_self_eq_norm_sq, hu, one_pow, mul_one]

/-- The nuclear seminorm is the maximum real trace pairing over the operator-norm unit ball.
The canonical polar factor attains it. -/
theorem _root_.LinearMap.isGreatest_re_trace_adjoint_comp (A : E →ₗ[𝕜] F) :
    IsGreatest {r : ℝ | ∃ D : E →ₗ[𝕜] F, opNorm 𝕜 E F D ≤ 1 ∧
      RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = r} (nuclear 𝕜 E F A) := by
  refine ⟨⟨A.polarFactor, A.opNorm_polarFactor_le_one, by simp⟩, ?_⟩
  rintro r ⟨D, hD, rfl⟩
  calc
    _ ≤ ‖trace 𝕜 E (adjoint D ∘ₗ A)‖ := RCLike.re_le_norm _
    _ ≤ opNorm 𝕜 E F D * nuclear 𝕜 E F A := norm_trace_adjoint_comp_le_opNorm_mul_nuclear D A
    _ ≤ nuclear 𝕜 E F A := by simpa using
      mul_le_mul_of_nonneg_right hD (apply_nonneg _ A)

/-- A maximizing contraction is the polar factor plus a contraction from the kernel of the
map to the orthogonal complement of its range, extended by zero on the initial space. -/
theorem opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff {D A : E →ₗ[𝕜] F} :
    opNorm 𝕜 E F D ≤ 1 ∧ RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A ↔
    ∃ T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ, opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1 ∧
      D = A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
        A.ker.orthogonalProjectionOnto.toLinearMap := by
  constructor
  · rintro ⟨hD, ht⟩
    exact A.exists_contraction_on_ker_of_comp_operatorAbs_eq hD
      ((re_trace_adjoint_comp_eq_nuclear_iff hD).mp ht)
  · rintro ⟨T, hT, rfl⟩
    have hD := A.opNorm_le_one_polarFactor_add_ker hT
    refine ⟨hD, (re_trace_adjoint_comp_eq_nuclear_iff hD).mpr
      ((A.comp_operatorAbs_eq_iff_eqOn_polarFactor _).mpr ?_)⟩
    intro x hx
    simp [A.ker.orthogonalProjectionOnto_eq_zero_iff.mpr hx]

/-- The maximizer of the real trace pairing on the operator-norm unit ball is unique exactly
when the map is injective or surjective. -/
theorem _root_.LinearMap.existsUnique_opNorm_le_one_re_trace_adjoint_comp_eq_nuclear_iff
    (A : E →ₗ[𝕜] F) :
    (∃! D : E →ₗ[𝕜] F, opNorm 𝕜 E F D ≤ 1 ∧
      RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A) ↔
      Function.Injective A ∨ Function.Surjective A := by
  have hU : opNorm 𝕜 E F A.polarFactor ≤ 1 ∧
      RCLike.re (trace 𝕜 E (adjoint A.polarFactor ∘ₗ A)) = nuclear 𝕜 E F A :=
    ⟨A.opNorm_polarFactor_le_one, by simp⟩
  constructor
  · rintro ⟨D, _, hD⟩
    by_contra! hA
    let : Nontrivial A.ker := Submodule.nontrivial_iff_ne_bot.mpr
      fun h ↦ hA.1 (LinearMap.ker_eq_bot.mp h)
    let : Nontrivial (LinearMap.range A)ᗮ := Submodule.nontrivial_iff_ne_bot.mpr
      fun h ↦ hA.2 (LinearMap.range_eq_top.mp (Submodule.orthogonal_eq_bot_iff.mp h))
    obtain ⟨⟨v, hv⟩⟩ := NormedSpace.sphere_nonempty_rclike 𝕜 (E := A.ker) (r := 1) zero_le_one
    obtain ⟨⟨w, hw⟩⟩ := NormedSpace.sphere_nonempty_rclike 𝕜
      (E := (LinearMap.range A)ᗮ) (r := 1) zero_le_one
    rw [Metric.mem_sphere, dist_zero_right] at hv hw
    let T := (InnerProductSpace.rankOne 𝕜 w v).toLinearMap
    have hT : opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1 := by
      rw [opNorm_apply]
      dsimp only [T]
      rw [← LinearMap.coe_toContinuousLinearMap_symm, LinearEquiv.apply_symm_apply,
        InnerProductSpace.norm_rankOne, hv, hw, mul_one]
    let D' := A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap
    have hD' := hD D' (opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff.mpr ⟨T, hT, rfl⟩)
    have he := LinearMap.congr_fun (hD'.trans (hD _ hU).symm) (v : E)
    have hw0 : (w : F) = 0 := by simpa [D', T, inner_self_eq_norm_sq_to_K, hv] using he
    simp [← Submodule.norm_coe, hw0] at hw
  · intro h
    refine ⟨A.polarFactor, hU, fun D hD ↦ ?_⟩
    obtain ⟨T, _, rfl⟩ := opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff.mp hD
    have hT : T = 0 := by
      rcases h with h | h
      · let : Subsingleton A.ker :=
          Submodule.subsingleton_iff_eq_bot.mpr (LinearMap.ker_eq_bot.mpr h)
        ext x
        rw [Subsingleton.elim x 0]
        simp
      · let : Subsingleton (LinearMap.range A)ᗮ := Submodule.subsingleton_iff_eq_bot.mpr
          (Submodule.orthogonal_eq_bot_iff.mpr (LinearMap.range_eq_top.mpr h))
        exact LinearMap.ext fun x ↦ Subsingleton.elim (T x) _
    simp [hT]

/-- Every maximizing contraction distinct from the polar factor has strictly greater
Frobenius seminorm. -/
theorem frobenius_polarFactor_lt_of_re_trace_adjoint_comp_eq_nuclear {D A : E →ₗ[𝕜] F}
    (hD : opNorm 𝕜 E F D ≤ 1) (ht : RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A)
    (hDne : D ≠ A.polarFactor) : frobenius 𝕜 E F A.polarFactor < frobenius 𝕜 E F D := by
  obtain ⟨T, _, hDeq⟩ := opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff.mp ⟨hD, ht⟩
  have hTne : T ≠ 0 := by
    intro hT
    exact hDne (by simpa [hT] using hDeq)
  have hTpos : 0 < frobenius 𝕜 A.ker (LinearMap.range A)ᗮ T ^ 2 := by
    rw [frobenius_apply_eq_sqrt_sum_sq_singularValues, Finsupp.sum,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr
      (fun h ↦ hTne ((T.singularValues_eq_zero_iff).mp h))
    exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨i, hi,
      sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)⟩
  apply (sq_lt_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [A.sq_frobenius_polarFactor, hDeq, A.sq_frobenius_polarFactor_add_ker]
  exact lt_add_of_pos_right _ hTpos

end TauCeti.UnitarilyInvariantSeminorm
