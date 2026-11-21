/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Fredholm.SmallPerturbation
import TauCeti.Analysis.Normed.Operator.ClosedRange
import TauCeti.Analysis.Normed.Operator.Compact.Estimate

/-!
# Stability of operators with closed range and finite-dimensional kernel

An operator `T : E →L[𝕜] F` between Banach spaces with closed range and finite-dimensional kernel
is *upper semi-Fredholm*: it is Fredholm exactly when its range moreover has finite codimension.
Elliptic estimates typically produce exactly this property: Peetre's argument turns an estimate
`‖x‖ ≤ C ‖T x‖ + ‖K x‖` with `K` compact into closed range and finite-dimensional kernel
(`ContinuousLinearMap.isClosed_range_of_compact_estimate`), but says nothing about the cokernel.
This file proves that the property is stable under small perturbations, and that along a
connected family of such operators Fredholmness and the index propagate from a single member.

* **Openness.** If `T` has closed range and finite-dimensional kernel, so has every `S` near `T`,
  and `dim ker S ≤ dim ker T`
  (`ContinuousLinearMap.eventually_nhds_finiteDimensional_ker_and_finrank_ker_le`,
  `ContinuousLinearMap.eventually_nhds_isClosed_range`). The a priori estimate
  `‖x‖ ≤ C ‖T x‖ + ‖P x‖` of `T`, with `P` a projection onto `ker T`
  (`ContinuousLinearMap.exists_projection_norm_le`), survives the perturbation as
  `‖x‖ ≤ 2 C ‖S x‖ + 2 ‖P x‖` as soon as `C ‖S - T‖ ≤ 1 / 2`; the finite-rank projection `P` is
  compact, so Peetre's argument applies to `S`, and `P` is injective on `ker S`.
* **Fredholmness is locally constant.** If moreover `F` is a Hilbert space, then every `S` near
  `T` is Fredholm exactly when `T` is (`ContinuousLinearMap.eventually_nhds_isFredholm_iff`).
  Mathlib proves one direction for all Banach spaces
  (`ContinuousLinearMap.IsFredholm.eventually_nhds`). For the other, let `X = ker P`, a closed
  complement of `ker T`. On `X` both `T` and `S` are bounded below, `‖x‖ ≤ 2 C ‖S x‖`, and
  `T X = range T`. A vector `m = S x` of `S X` orthogonal to `range T` satisfies
  `‖m‖² = re ⟪S x - T x, m⟫ ≤ 2 C ‖S - T‖ ‖m‖²`, so it vanishes when `2 C ‖S - T‖ < 1`. Hence
  `(range T)ᗮ` injects into `F ⧸ S X`, which is finite-dimensional when `S` is Fredholm since
  `range S = S X + S (ker T)`. So `range T` has finite codimension and `T` is Fredholm.
* **Connected families.** Along a family `T x` of operators with closed range and
  finite-dimensional kernel, continuous on a preconnected set `s`, Fredholmness is constant on
  `s`: if one member is Fredholm, every member is
  (`ContinuousOn.isFredholm_of_isPreconnected`), since by the previous point the Fredholm members
  form a relatively clopen subset of `s`. The index, locally constant on Fredholm operators, is
  then constant on `s` as well (`ContinuousOn.index_eq_of_isPreconnected`).

With the connected-family statement, the Fredholm property of an elliptic operator can be
obtained from semi-Fredholm estimates without proving the regularity of weak cokernel elements:
it suffices to connect the operator, through operators satisfying such estimates, to one already
known to be Fredholm, for instance an invertible one.

For a Banach target the second point still holds, but the proof needs the gap between closed
subspaces and its duality with annihilators (Kato, IV §4); in a Hilbert space the orthogonal
complement makes the comparison of codimensions elementary.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1
  (stability of the nullity, deficiency and index of semi-Fredholm operators).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

open Filter Module Topology
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

section Banach

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The a priori estimate of an operator with closed range and finite-dimensional kernel, with a
projection `P` into its kernel, persists for every operator `S` near `T`, namely with
`2 C ‖S - T‖ < 1`, at the cost of a factor `2`. -/
private theorem exists_projection_eventually_forall_norm_le {T : E →L[𝕜] F}
    [FiniteDimensional 𝕜 T.ker] (hrange : IsClosed (T.range : Set F)) :
    ∃ (P : E →L[𝕜] E) (C : ℝ), IsIdempotentElem P ∧ (∀ x, P x ∈ T.ker) ∧
      ∀ᶠ S in 𝓝 T, 2 * C * ‖S - T‖ < 1 ∧ ∀ x, ‖x‖ ≤ 2 * C * ‖S x‖ + 2 * ‖P x‖ := by
  obtain ⟨P, C, hC, hP, hPrange, hest⟩ :=
    T.exists_projection_norm_le hrange (Submodule.ClosedComplemented.of_finiteDimensional _)
  refine ⟨P, C, hP, fun x ↦ hPrange ▸ LinearMap.mem_range_self (P : E →ₗ[𝕜] E) x, ?_⟩
  filter_upwards [Metric.ball_mem_nhds T (by positivity : 0 < 1 / (2 * C))] with S hS
  rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ (by positivity)] at hS
  refine ⟨by linarith, fun x ↦ ?_⟩
  have hTx : ‖T x‖ ≤ ‖S x‖ + ‖S - T‖ * ‖x‖ := by
    calc ‖T x‖ = ‖S x - (S - T) x‖ := by rw [sub_apply, sub_sub_cancel]
      _ ≤ ‖S x‖ + ‖(S - T) x‖ := norm_sub_le _ _
      _ ≤ ‖S x‖ + ‖S - T‖ * ‖x‖ := by gcongr; exact (S - T).le_opNorm x
  have h := hest x
  have hx : C * ‖S - T‖ * ‖x‖ ≤ 1 / 2 * ‖x‖ := by gcongr; linarith
  nlinarith

/-- **Openness of the upper semi-Fredholm operators, kernel part.** Near an operator with closed
range and finite-dimensional kernel, every operator has a finite-dimensional kernel, of dimension
at most that of `ker T`. -/
theorem eventually_nhds_finiteDimensional_ker_and_finrank_ker_le {T : E →L[𝕜] F}
    [FiniteDimensional 𝕜 T.ker] (hrange : IsClosed (T.range : Set F)) :
    ∀ᶠ S in 𝓝 T, FiniteDimensional 𝕜 S.ker ∧ finrank 𝕜 S.ker ≤ finrank 𝕜 T.ker := by
  obtain ⟨P, C, -, hP, hest⟩ := exists_projection_eventually_forall_norm_le hrange
  filter_upwards [hest] with S ⟨_, hSx⟩
  -- `P` is injective on `ker S`, since `‖x‖ ≤ 2 ‖P x‖` there.
  have hinj : Function.Injective ((P.codRestrict T.ker hP : E →ₗ[𝕜] T.ker) ∘ₗ S.ker.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : P x = 0 := congr(($hx : E))
    have hSx0 : S x = 0 := x.property
    have := hSx x
    rw [hSx0, h0] at this
    exact Subtype.ext (norm_le_zero_iff.mp (by simpa using this))
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

/-- **Openness of the upper semi-Fredholm operators, range part.** Near an operator with closed
range and finite-dimensional kernel, every operator has closed range. -/
theorem eventually_nhds_isClosed_range {T : E →L[𝕜] F} [FiniteDimensional 𝕜 T.ker]
    (hrange : IsClosed (T.range : Set F)) : ∀ᶠ S in 𝓝 T, IsClosed (S.range : Set F) := by
  obtain ⟨P, C, -, hP, hest⟩ := exists_projection_eventually_forall_norm_le hrange
  filter_upwards [hest] with S ⟨_, hSx⟩
  -- The finite-rank projection, viewed as an operator into `ker T`, is compact.
  refine S.isClosed_range_of_compact_estimate (C := 2 * C)
    (isCompactOperator_of_locallyCompactSpace_dom ((2 : 𝕜) • P.codRestrict T.ker hP))
    fun x ↦ ?_
  rw [smul_apply, norm_smul, RCLike.norm_ofNat, ← Submodule.norm_coe, coe_codRestrict_apply]
  exact hSx x

/-- The operators with closed range and finite-dimensional kernel form an open set. -/
theorem isOpen_setOf_finiteDimensional_ker_and_isClosed_range :
    IsOpen {T : E →L[𝕜] F | FiniteDimensional 𝕜 T.ker ∧ IsClosed (T.range : Set F)} := by
  rw [isOpen_iff_mem_nhds]
  rintro T ⟨hker, hrange⟩
  filter_upwards [eventually_nhds_finiteDimensional_ker_and_finrank_ker_le hrange,
    eventually_nhds_isClosed_range hrange] with S hS hS' using ⟨hS.1, hS'⟩

end Banach

section Hilbert

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The image under `S` of the complement `ker P` of `ker T` meets the orthogonal complement of
`range T` only in `0`, when `S` is close to `T`. -/
private theorem eq_zero_of_mem_orthogonal_range_of_mem_map {T S : E →L[𝕜] F}
    {P : E →L[𝕜] E} {C : ℝ} (hS : 2 * C * ‖S - T‖ < 1)
    (hest : ∀ x, P x = 0 → ‖x‖ ≤ 2 * C * ‖S x‖) {m : F} (hm : m ∈ T.rangeᗮ)
    (hmS : m ∈ (LinearMap.ker (P : E →ₗ[𝕜] E)).map (S : E →ₗ[𝕜] F)) : m = 0 := by
  obtain ⟨x, hx, rfl⟩ := hmS
  have hTx : ⟪T x, S x⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self (T : E →ₗ[𝕜] F) x) hm
  -- `‖S x‖² = re ⟪S x - T x, S x⟫ ≤ ‖S - T‖ ‖x‖ ‖S x‖ ≤ 2 C ‖S - T‖ ‖S x‖²`.
  have h : ‖S x‖ ^ 2 ≤ 2 * C * ‖S - T‖ * ‖S x‖ ^ 2 := by
    calc ‖S x‖ ^ 2 = RCLike.re ⟪(S - T) x, S x⟫_𝕜 := by
          rw [sub_apply, inner_sub_left, hTx, sub_zero, ← @norm_sq_eq_re_inner 𝕜]
      _ ≤ ‖(S - T) x‖ * ‖S x‖ := re_inner_le_norm _ _
      _ ≤ ‖S - T‖ * (2 * C * ‖S x‖) * ‖S x‖ := by
          grw [le_opNorm, hest x hx]
      _ = 2 * C * ‖S - T‖ * ‖S x‖ ^ 2 := by ring
  have h0 : ‖S x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖S x‖]
  simpa using h0

/-- **Fredholmness is locally constant on the upper semi-Fredholm operators** into a Hilbert space.
Near an operator `T` with closed range and finite-dimensional kernel, an operator is Fredholm
exactly when `T` is. -/
theorem eventually_nhds_isFredholm_iff {T : E →L[𝕜] F} [FiniteDimensional 𝕜 T.ker]
    (hrange : IsClosed (T.range : Set F)) : ∀ᶠ S in 𝓝 T, (IsFredholm S ↔ IsFredholm T) := by
  by_cases hT : IsFredholm T
  · filter_upwards [hT.eventually_isFredholm_and_index_eq] with S hS using iff_of_true hS.1 hT
  obtain ⟨P, C, hPi, hP, hest⟩ := exists_projection_eventually_forall_norm_le hrange
  filter_upwards [hest] with S ⟨hS, hSx⟩
  refine iff_of_false (fun hSF ↦ hT ?_) hT
  set M := (LinearMap.ker (P : E →ₗ[𝕜] E)).map (S : E →ₗ[𝕜] F)
  -- `range S = S (ker P) + S (ker T)`, and `S (ker T)` is finite-dimensional.
  have hle : S.range ≤ M ⊔ T.ker.map (S : E →ₗ[𝕜] F) := by
    rintro _ ⟨x, rfl⟩
    have hPPx : P (P x) = P x := congr($(hPi.eq) x)
    have hx : x - P x ∈ LinearMap.ker (P : E →ₗ[𝕜] E) := by simp [hPPx]
    rw [← sub_add_cancel x (P x), map_add]
    exact Submodule.add_mem_sup ⟨_, hx, rfl⟩ ⟨_, hP x, rfl⟩
  have hsup : (M ⊔ T.ker.map (S : E →ₗ[𝕜] F)).CoFG := hSF.finite_coker.of_le hle
  have hMfin : FiniteDimensional 𝕜 (F ⧸ M) :=
    have : Module.Finite 𝕜 ((F ⧸ M) ⧸ (T.ker.map (S : E →ₗ[𝕜] F)).map M.mkQ) :=
      Module.Finite.equiv (Submodule.quotientQuotientEquivQuotientSup _ _).symm
    Module.Finite.of_submodule_quotient ((T.ker.map (S : E →ₗ[𝕜] F)).map M.mkQ)
  -- `(range T)ᗮ` injects into `F ⧸ S (ker P)`.
  have hinj : Function.Injective (M.mkQ ∘ₗ T.rangeᗮ.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have hmM : (m : F) ∈ M := (Submodule.Quotient.mk_eq_zero M).mp hm
    refine Subtype.ext (eq_zero_of_mem_orthogonal_range_of_mem_map hS
        (fun x hx ↦ ?_) m.property hmM)
    simpa [hx] using hSx x
  have : FiniteDimensional 𝕜 T.rangeᗮ := Module.Finite.of_injective _ hinj
  have : CompleteSpace T.range := hrange.completeSpace_coe
  have hcoker : FiniteDimensional 𝕜 (F ⧸ T.range) :=
    Module.Finite.equiv
      (Submodule.quotientEquivOfIsCompl _ _ T.range.isCompl_orthogonal).symm
  exact IsFredholm.of_finite_ker_coker T inferInstance hcoker

end Hilbert

end ContinuousLinearMap

open ContinuousLinearMap in
/-- **Fredholmness along a connected family of upper semi-Fredholm operators.** Let `T x` be
operators from a Banach space to a Hilbert space with closed range and finite-dimensional kernel,
depending continuously on `x` in a preconnected set `s`. If one member `T x₀` is Fredholm, then
every member is. By `ContinuousOn.index_eq_of_isPreconnected` they then all have the same index. -/
theorem ContinuousOn.isFredholm_of_isPreconnected {𝕜 E F X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [TopologicalSpace X]
    {s : Set X} {T : X → E →L[𝕜] F} (hT : ContinuousOn T s)
    (hker : ∀ x ∈ s, FiniteDimensional 𝕜 (T x).ker)
    (hrange : ∀ x ∈ s, IsClosed ((T x).range : Set F)) (hs : IsPreconnected s) {x₀ x : X}
    (hx₀ : x₀ ∈ s) (h₀ : IsFredholm (T x₀)) (hx : x ∈ s) : IsFredholm (T x) := by
  classical
  -- Whether `T y` is Fredholm is locally constant on `s`.
  have hφ : ContinuousOn (fun y ↦ decide (IsFredholm (T y))) s := fun y hy ↦ by
    have := hker y hy
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    filter_upwards [(hT y hy).eventually (eventually_nhds_isFredholm_iff (hrange y hy))] with z hz
    simp [hz]
  simpa [h₀] using hs.constant hφ hx hx₀

end
