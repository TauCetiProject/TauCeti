/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Trace

/-!
# Near isometries in mean square

A linear map `A : S → T` out of a finite-dimensional inner product space is a *near isometry with
error `ε`* if on every subspace `U ⊆ S` its squared Hilbert–Schmidt norm `‖A pr_U‖²` is at least
`dim U - ε dim S`. Here `‖·‖` is the Frobenius (Hilbert–Schmidt) seminorm
`TauCeti.UnitarilyInvariantSeminorm.frobenius` and `pr_U` is the orthogonal projection onto `U`.
An isometry is a near isometry with error `0`. The notion only asks that `A` loses little of the
squared length of an orthonormal basis of each subspace, on average over the basis.

## Main definitions and results

* `LinearMap.IsNearIsometry A ε`: `A` is a near isometry with error `ε`.
* `LinearMap.isNearIsometry_of_sq_frobenius_le`: if `‖A† A - 1‖² ≤ ε² dim S` with `ε ≥ 0`, then `A`
  is a near isometry with error `ε`.
* `LinearMap.IsNearIsometry.comp_of_isSymmetricProjection`: if `pr` is an orthogonal projection of
  the target with `‖(1 - pr) A‖² ≤ δ dim S`, then `pr A` is a near isometry with error `ε + δ`.

## References

These results are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic PBC), file `src/New/Spanning/SecondMoment/FewTranslates.lean`
(`New.IsNearIsometry`, `New.isNearIsometry_of_hilbertSchmidtNorm_le`,
`New.IsNearIsometry.proj_comp`, `New.hilbertSchmidtNorm_one_sub_mul_comp_sq_le`), where they are
stated over `ℂ` with a Hilbert–Schmidt norm of its own; here they are stated over any `RCLike`
field with Tau Ceti's Frobenius seminorm. The underlying idea, rank bounds from second moments of
frames, goes back to L. R. Welch, *Lower bounds on the maximum cross correlation of signals*,
IEEE Trans. Inform. Theory 20 (1974), 397–399.
-/

public section

open Module LinearMap TauCeti TauCeti.UnitarilyInvariantSeminorm

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 S T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S]
  [NormedAddCommGroup T] [InnerProductSpace 𝕜 T]

/-- `A` is a *near isometry with error `ε`*: on every subspace `U` of the source, the squared
Frobenius (Hilbert–Schmidt) seminorm `‖A pr_U‖²` is at least `dim U - ε dim S`. -/
def IsNearIsometry (A : S →ₗ[𝕜] T) (ε : ℝ) : Prop :=
  ∀ U : Submodule 𝕜 S, (finrank 𝕜 U : ℝ) - ε * finrank 𝕜 S ≤
    UnitarilyInvariantSeminorm.frobenius 𝕜 S T (A ∘ₗ (U.starProjection : S →ₗ[𝕜] S)) ^ 2

theorem isNearIsometry_iff {A : S →ₗ[𝕜] T} {ε : ℝ} :
    A.IsNearIsometry ε ↔ ∀ U : Submodule 𝕜 S, (finrank 𝕜 U : ℝ) - ε * finrank 𝕜 S ≤
      UnitarilyInvariantSeminorm.frobenius 𝕜 S T (A ∘ₗ (U.starProjection : S →ₗ[𝕜] S)) ^ 2 :=
  Iff.rfl

/-- A near isometry with error `ε` is one with any larger error. -/
theorem IsNearIsometry.mono {A : S →ₗ[𝕜] T} {ε ε' : ℝ} (hA : A.IsNearIsometry ε) (h : ε ≤ ε') :
    A.IsNearIsometry ε' :=
  fun U ↦ le_trans (by gcongr) (hA U)

/-- Composing a near isometry on the left with a linear isometry keeps a near isometry with the
same error. -/
theorem IsNearIsometry.linearIsometry_comp {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] {A : S →ₗ[𝕜] T} {ε : ℝ} (hA : A.IsNearIsometry ε) (V : T →ₗᵢ[𝕜] G) :
    (V.toLinearMap ∘ₗ A).IsNearIsometry ε := by
  intro U
  rw [comp_assoc, frobenius_linearIsometry_comp]
  exact hA U

/-- A near isometry `A` with error `ε < 1` out of a nonzero space is not zero. -/
theorem IsNearIsometry.ne_zero [Nontrivial S] {A : S →ₗ[𝕜] T} {ε : ℝ} (hA : A.IsNearIsometry ε)
    (hε : ε < 1) : A ≠ 0 := by
  -- The case `U = S` reads `(1 - ε) dim S ≤ ‖A‖²`.
  rintro rfl
  have h_top := hA ⊤
  simp at h_top
  have h_pos : (0 : ℝ) < finrank 𝕜 S := by exact_mod_cast finrank_pos
  nlinarith

variable [FiniteDimensional 𝕜 T]

/-- **Near isometries from a small defect.** If `‖A† A - 1‖² ≤ ε² dim S` with `ε ≥ 0`, then `A` is a
near isometry with error `ε`. -/
theorem isNearIsometry_of_sq_frobenius_le {A : S →ₗ[𝕜] T} {ε : ℝ} (hε : 0 ≤ ε)
    (h : UnitarilyInvariantSeminorm.frobenius 𝕜 S S (A.adjoint ∘ₗ A - 1) ^ 2 ≤
      ε ^ 2 * finrank 𝕜 S) :
    A.IsNearIsometry ε := by
  -- On each subspace `U`, `‖A pr_U‖² - dim U` is the Hilbert–Schmidt inner product of `pr_U` with
  -- `A† A - 1`, and Cauchy–Schwarz bounds it by `√(dim U) · ε √(dim S) ≤ ε dim S`.
  intro U
  set p : S →ₗ[𝕜] S := (U.starProjection : S →ₗ[𝕜] S)
  have h_diff : UnitarilyInvariantSeminorm.frobenius 𝕜 S T (A ∘ₗ p) ^ 2 - finrank 𝕜 U =
      RCLike.re (trace 𝕜 S (p.adjoint ∘ₗ (A.adjoint ∘ₗ A - 1))) := by
    have h_dim : ((UnitarilyInvariantSeminorm.frobenius 𝕜 S S p ^ 2 : ℝ) : 𝕜) =
        trace 𝕜 S (p.adjoint ∘ₗ 1) := by
      simpa [Module.End.one_eq_id] using sq_frobenius_comp_starProjection (1 : S →ₗ[𝕜] S) U
    rw [comp_sub, map_sub, map_sub, ← sq_frobenius_comp_starProjection, ← h_dim,
      sq_frobenius_starProjection, RCLike.ofReal_re, RCLike.ofReal_re]
  set D := UnitarilyInvariantSeminorm.frobenius 𝕜 S S (A.adjoint ∘ₗ A - 1)
  have h_bound : UnitarilyInvariantSeminorm.frobenius 𝕜 S S p * D ≤ ε * finrank 𝕜 S := by
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    calc (UnitarilyInvariantSeminorm.frobenius 𝕜 S S p * D) ^ 2
        ≤ finrank 𝕜 S * (ε ^ 2 * finrank 𝕜 S) := by
          rw [mul_pow, sq_frobenius_starProjection]
          gcongr
          exact_mod_cast U.finrank_le
      _ = (ε * finrank 𝕜 S) ^ 2 := by ring
  have h_cs := (RCLike.abs_re_le_norm _).trans
    ((norm_trace_adjoint_comp_le p (A.adjoint ∘ₗ A - 1)).trans h_bound)
  linarith [(abs_le.1 h_cs).1]

/-- **Projecting a near isometry.** If `A` is a near isometry with error `ε` and the orthogonal
projection `pr` of the target misses at most `δ dim S` of the squared Frobenius seminorm of `A`,
that is `‖(1 - pr) A‖² ≤ δ dim S`, then `pr A` is a near isometry with error `ε + δ`. -/
theorem IsNearIsometry.comp_of_isSymmetricProjection {A : S →ₗ[𝕜] T} {ε δ : ℝ}
    (hA : A.IsNearIsometry ε) {pr : T →ₗ[𝕜] T} (hpr : pr.IsSymmetricProjection)
    (h_rest : UnitarilyInvariantSeminorm.frobenius 𝕜 S T ((1 - pr) ∘ₗ A) ^ 2 ≤
      δ * finrank 𝕜 S) :
    (pr ∘ₗ A).IsNearIsometry (ε + δ) := by
  intro U
  set p : S →ₗ[𝕜] S := (U.starProjection : S →ₗ[𝕜] S)
  have h_split := sq_frobenius_eq_sq_frobenius_add_sq_frobenius hpr (A ∘ₗ p)
  have h_cut : UnitarilyInvariantSeminorm.frobenius 𝕜 S T (((1 - pr) ∘ₗ A) ∘ₗ p) ^ 2 ≤
      UnitarilyInvariantSeminorm.frobenius 𝕜 S T ((1 - pr) ∘ₗ A) ^ 2 :=
    pow_le_pow_left₀ (apply_nonneg _ _) (frobenius_comp_starProjection_le _ U) 2
  rw [comp_assoc] at h_cut ⊢
  linarith [hA U]

end LinearMap
