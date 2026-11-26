/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Domain
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Liouville.Scaling

/-!
# Liouville flows expand volume, and closed manifolds carry no exact symplectic form

Let `σ` be a smooth two-form on a manifold of dimension `2 n` and `Z` a complete `C¹` Liouville
vector field of `σ`, `L_Z σ = σ`, with flow `ψ`. The flow is conformally symplectic,
`ψ_t^* σ = e^t σ`, so it multiplies the Liouville measure `|σⁿ / n!|` by `e^{n t}`: for every set
`s`, the Liouville measure of `ψ_t(s)` is `e^{n t}` times that of `s`
(`TauCeti.IsLiouvilleVectorField.liouvilleMeasure_image_flowOf`). Since `ψ_t` is a bijection of the
whole manifold, in positive dimension the total Liouville measure is then `0` or `∞`
(`TauCeti.IsLiouvilleVectorField.liouvilleMeasure_univ_eq_zero_or_eq_top`).

On a compact manifold without boundary every smooth vector field is complete, and for a
nondegenerate two-form `σ` with a primitive `α`, `dα = σ`, the vector field `Z = (σ♭)⁻¹ α`
contracting to `α` is a smooth Liouville vector field of `σ`. Its Liouville measure is finite, by
compactness, and positive, by nondegeneracy. So a nonempty compact manifold without boundary, of
positive dimension, carries no exact nondegenerate two-form
(`TauCeti.SmoothTwoForm.IsNondegenerate.mextDeriv_ne`): an exact symplectic form forces
`∫ σⁿ = 0`, which a nondegenerate form on a closed manifold cannot satisfy. The argument by the
expanding flow replaces Stokes' theorem and needs no orientation.

Restricted to an open subset, this shows that a nonempty Liouville domain is never open, so that
its boundary is nonempty (`TauCeti.IsLiouvilleDomain.not_isOpen`); in particular a closed
symplectic manifold is not a Liouville domain. In dimension `0` this fails: every finite discrete
manifold is a Liouville domain in itself, with `σ = 0`, `α = 0` and a constant defining
function.

## Main results

* `TauCeti.IsLiouvilleVectorField.liouvilleMeasure_image_flowOf`: the time-`t` map of a Liouville
  flow multiplies the Liouville measure by `e^{n t}`.
* `TauCeti.IsLiouvilleVectorField.liouvilleMeasure_univ_eq_zero_or_eq_top`: a manifold of positive
  dimension with a complete Liouville vector field has Liouville volume `0` or `∞`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mextDeriv_ne`: a nondegenerate two-form on a nonempty
  closed manifold of positive dimension is not exact.
* `TauCeti.IsLiouvilleDomain.not_isOpen`: a nonempty Liouville domain is not open, so it has
  nonempty boundary; a closed symplectic manifold is not a Liouville domain.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 3 (the volume form `ωⁿ / n!` of a symplectic manifold) and Section 3.5 (Liouville
  vector fields and hypersurfaces of contact type).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1 (Liouville domains).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {Z : (x : M) → TangentSpace I x}

/-! ### Liouville flows expand the Liouville measure -/

namespace IsLiouvilleVectorField

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] {n : ℕ}
  [Fact (finrank ℝ E = 2 * n)]
  (hZσ : IsLiouvilleVectorField σ.val Z) (hc : IsCompleteVectorField Z)
  (hZ : ContMDiff I I.tangent 1 (T% Z))
include hZσ hc hZ

/-- **A Liouville flow expands the Liouville measure.** Let `Z` be a complete `C¹` Liouville
vector field of a smooth two-form `σ` on a manifold of dimension `2 n`, `L_Z σ = σ`, with flow
`ψ`. Then for every set `s`, the Liouville measure of `ψ_t(s)` is `e^{n t}` times the Liouville
measure of `s`. -/
theorem liouvilleMeasure_image_flowOf (t : ℝ) (s : Set M) :
    σ.liouvilleMeasure n (flowOf Z t '' s) =
      ENNReal.ofReal (Real.exp (n * t)) * σ.liouvilleMeasure n s := by
  set ψ := globalFlowDiffeomorph hc (n := 1) le_rfl hZ t
  have hψ : ⇑ψ = flowOf Z t := funext fun x ↦ by
    rw [globalFlowDiffeomorph_apply, flowOf_eq_globalFlow hZ hc]
  -- The time-`t` map pulls `σ` back to `e^t σ`, so it carries the Liouville measure of `e^t σ`
  -- to that of `σ`.
  have hpull : mpullback I I ψ σ.val = (Real.exp t • σ).val := by
    rw [hψ, flowOf_eq_globalFlow hZ hc]
    exact hZσ.mpullback_globalFlow_eq_exp_smul hc hZ σ.mdifferentiable t
  have hmp := ψ.toHomeomorph.measurePreserving_liouvilleMeasure (n := n)
    (ψ.mdifferentiable (by simp)) hpull
  rw [Diffeomorph.coe_toHomeomorph] at hmp
  rw [← hψ, ← hmp.measure_preimage_emb ψ.toHomeomorph.measurableEmbedding,
    (EquivLike.injective ψ).preimage_image, SmoothTwoForm.liouvilleMeasure_smul]
  -- What remains is the scalar identity `|e^t|^n = e^{n t}`.
  simp [abs_of_pos (Real.exp_pos t), ← Real.exp_natCast_mul]

/-- **A manifold with a complete Liouville vector field has Liouville volume `0` or `∞`.** In
positive dimension `2 n`, the time-one map of the flow of a complete `C¹` Liouville vector field
of `σ` is a bijection of the manifold multiplying the Liouville measure by `eⁿ ≠ 1`. -/
theorem liouvilleMeasure_univ_eq_zero_or_eq_top (hn : n ≠ 0) :
    σ.liouvilleMeasure n univ = 0 ∨ σ.liouvilleMeasure n univ = ⊤ := by
  have himage : flowOf Z 1 '' univ = univ := by
    rw [flowOf_eq_globalFlow hZ hc, image_univ]
    exact ((globalFlow Z hZ hc).toHomeomorph 1).surjective.range_eq
  have h := hZσ.liouvilleMeasure_image_flowOf (n := n) hc hZ 1 univ
  rw [himage] at h
  by_contra hne
  push Not at hne
  -- Cancelling the finite nonzero total measure leaves `eⁿ = 1`.
  have h1 : ENNReal.ofReal (Real.exp (n * 1)) = 1 :=
    (ENNReal.mul_eq_left hne.1 hne.2).1 (by rw [mul_comm]; exact h.symm)
  rw [ENNReal.ofReal_eq_one, mul_one, Real.exp_eq_one_iff] at h1
  exact hn (by exact_mod_cast h1)

end IsLiouvilleVectorField

/-! ### Closed manifolds carry no exact nondegenerate form -/

namespace SmoothTwoForm

/-- **A closed manifold carries no exact symplectic form.** On a nonempty compact manifold
without boundary, of positive dimension, no nondegenerate two-form `σ` has a primitive: for every
smooth one-form `α`, `dα ≠ σ`. Otherwise the vector field `(σ♭)⁻¹ α`, complete by compactness,
would be a Liouville vector field of `σ`, and its flow would expand the finite positive Liouville
volume of the manifold. -/
theorem IsNondegenerate.mextDeriv_ne [CompactSpace M] [Nonempty M] [Nontrivial E]
    (h : σ.IsNondegenerate) (α : SmoothForm I M ℝ 1) : mextDeriv α.val ≠ σ.val := by
  intro hα
  -- The Liouville field of `α`: the smooth vector field contracting to `α`.
  set Z : (x : M) → TangentSpace I x := fun x ↦ h.interiorEquiv.symm α x
  have hZ : ContMDiff I I.tangent ∞ (T% Z) := (h.interiorEquiv.symm α).contMDiff
  have hZ1 : ContMDiff I I.tangent 1 (T% Z) := hZ.of_le (by simp)
  have hZσ : IsLiouvilleVectorField σ.val Z := by
    have := isLiouvilleVectorField_mextDeriv_of_interior_eq (α.isSmoothForm.of_le (by simp))
      (hZ1.mdifferentiable one_ne_zero) (by rw [hα, h.interior_interiorEquiv_symm])
    rwa [hα] at this
  -- The dimension is `2 n` with `n ≠ 0`, the tangent spaces being symplectic vector spaces.
  obtain ⟨n, hn⟩ : Even (finrank ℝ E) :=
    (h.symplecticFormAt (Classical.arbitrary M)).even_finrank
  have : Fact (finrank ℝ E = 2 * n) := ⟨hn.trans (two_mul n).symm⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (Module.finrank_pos (R := ℝ) (M := E)).ne' (by simpa using hn)
  -- The Liouville measure of the compact manifold is finite and positive.
  borelize M
  have := h.isOpenPosMeasure_liouvilleMeasure (n := n)
  have hfin : σ.liouvilleMeasure n univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have hpos : σ.liouvilleMeasure n univ ≠ 0 := (isOpen_univ.measure_pos _ univ_nonempty).ne'
  rcases hZσ.liouvilleMeasure_univ_eq_zero_or_eq_top (isCompleteVectorField_of_compactSpace hZ1)
    hZ1 hn0 with h0 | htop
  · exact hpos h0
  · exact hfin htop

end SmoothTwoForm

/-! ### Liouville domains have boundary -/

namespace IsLiouvilleDomain

/-- **A nonempty Liouville domain is not open**, so its boundary is nonempty: in a manifold
without boundary, of positive dimension, an open Liouville domain `W` would be a nonempty
compact manifold without boundary carrying the exact nondegenerate form `σ = dα`. Taking `W` to
be the whole manifold, a closed symplectic manifold is not a Liouville domain. In dimension `0`
the statement fails: every finite discrete manifold is a Liouville domain in itself, with
`σ = 0`, `α = 0` and a constant defining function. -/
theorem not_isOpen [Nontrivial E] {α : SmoothForm I M ℝ 1} {W : Set M}
    (h : IsLiouvilleDomain σ α W) (hW : W.Nonempty) : ¬ IsOpen W := by
  intro ho
  -- Restrict everything to the open set `W`, a compact manifold without boundary.
  let U : TopologicalSpace.Opens M := ⟨W, ho⟩
  have : CompactSpace U := isCompact_iff_compactSpace.1 h.isCompact
  have : Nonempty U := hW.to_subtype
  have hι : ContMDiff I I ∞ (Subtype.val : U → M) := contMDiff_subtypeVal
  refine (h.isNondegenerate.isNondegenerate_mpullback_of_isLocalDiffeomorph
    (isLocalDiffeomorph_subtype_val (U := U))).mextDeriv_ne (SmoothForm.mpullback _ hι α) ?_
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← mpullback_mextDeriv (hι.of_le (by simp))
      ((isSmoothBundleForm_def 1 α.val).mpr (α.contMDiff.of_le (by simp))), h.mextDeriv_eq]

end IsLiouvilleDomain

end TauCeti
