/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Uniform ellipticity of continuous positive-definite matrix fields on compact sets

A continuous matrix field `a : X → Matrix ι ι ℝ` on a compact set `K` whose quadratic form is
pointwise strictly positive on nonzero vectors is uniformly elliptic on `K`: there is a constant
`λ > 0` with `λ ‖ξ‖² ≤ ξᵀ a(x) ξ` for all `x ∈ K`, and the operator norms of
`matrixBilinearForm (a x)` are bounded on `K`. When `K` is nonempty these come from the positive
minimum of the quadratic form on the compact product `K × Sⁿ⁻¹` and the maximum of an entrywise
bound on `K`. No symmetry of `a` is required
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`); the lower bound is the matrix case of
`IsCompact.exists_pos_forall_mul_norm_sq_le`. In particular, every continuous field of
positive-definite matrices on a compact set is uniformly elliptic
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact_of_posDef`).

## Main results

* `TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`: a continuous matrix field on a compact set
  whose quadratic form is strictly positive away from zero is uniformly elliptic there.
* `TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact_of_posDef`: the symmetric specialization to
  positive-definite matrices (`Matrix.PosDef`).

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), Chapter 3.

## Attribution

Adapted from the positive-definite ellipticity lemma of
[TauCetiProject/TauCeti#40536](https://github.com/TauCetiProject/TauCeti/pull/40536).
-/

public section

open Matrix Set

namespace TauCeti.PDE

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Uniform ellipticity on a compact set.** Let `a : X → Matrix ι ι ℝ` be continuous on a compact
set `K`, and suppose `ξᵀ a(x) ξ > 0` for every `x ∈ K` and every nonzero `ξ`. Then there exist
constants `0 < λ ≤ Λ` such that `a` is uniformly elliptic on `K`. No symmetry of `a` is assumed. -/
theorem exists_uniformlyEllipticOn_of_isCompact {K : Set X} (hK : IsCompact K)
    {a : X → Matrix ι ι ℝ} (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ ι, ξ ≠ 0 → 0 < (a x).toQuadraticForm' ξ) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn K a lam Lam := by
  obtain ⟨lam, hlam, hlow⟩ := hK.exists_pos_forall_mul_norm_sq_le
    (b := fun x ↦ matrixBilinearForm (a x)) (continuous_matrixBilinearForm.comp_continuousOn ha)
    fun x hx ξ hξ ↦ by simpa only [matrixBilinearForm_self] using hpos x hx ξ hξ
  simp only [matrixBilinearForm_self] at hlow
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨lam, lam, uniformlyEllipticOn_iff.2 ⟨hlam, le_rfl, fun _ hx ↦ hx.elim⟩⟩
  -- The sum of absolute values of entries is continuous on `K`, bounding the operator norm.
  let s : X → ℝ := fun x ↦ ∑ i, ∑ j, |a x i j|
  have hs_cont : ContinuousOn s K :=
    (by fun_prop : Continuous fun A : Matrix ι ι ℝ ↦ ∑ i, ∑ j, |A i j|).comp_continuousOn ha
  obtain ⟨x₁, -, hmax⟩ := hK.exists_isMaxOn hKne hs_cont
  refine ⟨lam, max lam (s x₁), uniformlyEllipticOn_iff.2 ⟨hlam, le_max_left _ _,
    fun x hx ↦ ⟨hlow x hx, fun η ξ ↦ ?_⟩⟩⟩
  have hM : ‖matrixBilinearForm (a x)‖ ≤ max lam (s x₁) :=
    (norm_matrixBilinearForm_le_sum_abs (a x)).trans ((hmax hx).trans (le_max_right _ _))
  have h := (matrixBilinearForm (a x)).le_opNorm₂ η ξ
  rw [matrixBilinearForm_apply, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hM (norm_nonneg η)) (norm_nonneg ξ))

/-- **Continuous positive-definite matrix fields on compact sets are uniformly elliptic.** -/
theorem exists_uniformlyEllipticOn_of_isCompact_of_posDef {K : Set X} (hK : IsCompact K)
    {a : X → Matrix ι ι ℝ} (ha : ContinuousOn a K) (hpos : ∀ x ∈ K, (a x).PosDef) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn K a lam Lam := by
  refine exists_uniformlyEllipticOn_of_isCompact hK ha fun x hx ξ hξ ↦ ?_
  have hξ' : ξ.ofLp ≠ 0 := fun h ↦ hξ (by simpa using congrArg (WithLp.toLp 2) h)
  simpa only [Matrix.toQuadraticForm'_apply, star_trivial] using
    (hpos x hx).dotProduct_mulVec_pos hξ'

section CompactPatch
variable {Omega U : TopologicalSpace.Opens (EuclideanSpace ℝ ι)} {lam : ℝ}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
local notation "E" => EuclideanSpace ℝ ι

/-- A positive lower bound for a continuous coefficient field gives uniform ellipticity on
a relatively compact chart patch; compactness supplies the upper bound. -/
theorem exists_uniformlyEllipticOn_inter_of_isCompact_closure {W : TopologicalSpace.Opens E}
    (hW : IsCompact (closure (W : Set E))) (hWU : closure (W : Set E) ⊆ U)
    (hlam : 0 < lam) (ha : ∀ x ∈ (Omega : Set E) ∩ U, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ matrixBilinearForm (a x) v v)
    (hcont : ∀ i j, ContinuousOn (fun x ↦ a x i j) U) :
    ∃ Lam, UniformlyEllipticOn ((Omega : Set E) ∩ W) a lam Lam := by
  classical
  choose C hC using fun i j ↦ hW.exists_bound_of_continuousOn
    ((hcont i j).mono hWU)
  let M := ∑ i, ∑ j, C i j
  refine ⟨max lam M, UniformlyEllipticOn.of_bounds hlam (le_max_left _ _) ?_ ?_⟩
  · intro x hx v
    simpa only [matrixBilinearForm_self] using ha x ⟨hx.1, hWU (subset_closure hx.2)⟩ v
  · intro x hx v w
    have hB : ‖matrixBilinearForm (a x)‖ ≤ M :=
      (norm_matrixBilinearForm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ by
          simpa only [Real.norm_eq_abs] using hC i j x (subset_closure hx.2))
    simpa only [matrixBilinearForm_apply, Real.norm_eq_abs] using
      (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
        (hB.trans (le_max_right lam M)) (le_refl ‖v‖) (le_refl ‖w‖)

end CompactPatch

end TauCeti.PDE
