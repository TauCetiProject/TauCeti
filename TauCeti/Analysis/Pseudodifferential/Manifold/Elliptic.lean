/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Elliptic classical pseudodifferential operators on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`), with principal symbol `σ_m(P)` on the
cotangent bundle (`TauCeti.classicalPrincipalSymbol`). The operator is **elliptic at** `x`
(`TauCeti.IsClassicalEllipticAt`) when `σ_m(P)(x, ξ) ≠ 0` for every nonzero covector `ξ ∈ T*ₓM`,
and **elliptic** (`TauCeti.IsClassicalElliptic`) when it is elliptic at every point.

Ellipticity only sees the principal symbol, so it is unchanged by adding an operator of order
`m - 1` and by multiplying by a nonzero constant. It is an open condition
(`TauCeti.IsClassicalEllipticAt.eventually`). In positive dimension an operator elliptic at some
point has order `m` and not `m - 1`, while in dimension zero there are no nonzero covectors and
every operator is elliptic.

Ellipticity is read in charts. If `a` is the symbol of a chart compression
`u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` and `φ ψ` does not vanish at `e x`, then `P` is elliptic at `x`
exactly when the principal symbol of `a` is invertible at `e x` at every nonzero frequency
(`TauCeti.isClassicalEllipticAt_iff_forall_isInvertible`). So on an open set `U` where `φ ψ ≠ 0`,
which lies in the chart target since the cutoffs are supported there, the restriction of `a` to `U`
is an elliptic classical symbol on `U` exactly when `P` is elliptic over `U`
(`TauCeti.isElliptic_restrict_iff_forall_isClassicalEllipticAt`). On a compact subset of such a set,
`a` is then elliptic at large frequencies with the inverse bound of order `-m`, and a symbol of
order `-m` inverts `a` at large frequencies near that compact set
(`TauCeti.exists_isEllipticOn_of_forall_isClassicalEllipticAt`,
`TauCeti.exists_comp_eq_id_of_forall_isClassicalEllipticAt`). These are the local inverse symbols
from which a parametrix of an elliptic operator is assembled chart by chart.

The complexification of a real differential operator of order at most `m` is elliptic exactly
where its geometric principal symbol has no nonzero zero covectors
(`TauCeti.isClassicalEllipticAt_complexifyLinearMap_iff`). For example the complexification of an
operator of Laplace type with constant `c`, such as `-Δ`, has principal symbol `c ‖ξ‖²` and is
elliptic of order `2` (`TauCeti.IsLaplaceType.isClassicalElliptic_complexifyLinearMap`).

## Main definitions

* `TauCeti.IsClassicalEllipticAt m P x`: the principal symbol `σ_m(P)(x, ·)` vanishes at no
  nonzero covector.
* `TauCeti.IsClassicalElliptic m P`: `P` is elliptic at every point.

## Main results

* `TauCeti.isClassicalEllipticAt_add_iff`, `TauCeti.isClassicalEllipticAt_smul_iff`: ellipticity
  is unchanged by perturbations of order `m - 1` and by nonzero scalars.
* `TauCeti.IsClassicalEllipticAt.mem`, `TauCeti.IsClassicalEllipticAt.notMem_sub_one`: in positive
  dimension an operator elliptic at a point has order `m` and not `m - 1`.
* `TauCeti.isClassicalEllipticAt_of_subsingleton`: in dimension zero every operator is elliptic.
* `TauCeti.IsClassicalEllipticAt.eventually`, `TauCeti.isOpen_setOf_isClassicalEllipticAt`:
  ellipticity is an open condition.
* `TauCeti.isClassicalEllipticAt_iff_forall_isInvertible`: ellipticity read on the symbol of a chart
  compression.
* `TauCeti.isElliptic_restrict_iff_forall_isClassicalEllipticAt`: the chart symbol restricted to an
  open set where the cutoffs do not vanish is elliptic exactly when `P` is elliptic there.
* `TauCeti.exists_isEllipticOn_of_forall_isClassicalEllipticAt`,
  `TauCeti.exists_comp_eq_id_of_forall_isClassicalEllipticAt`: ellipticity of the chart symbol at
  large frequencies over a compact set, and a local inverse symbol of order `-m`.
* `TauCeti.isClassicalEllipticAt_complexifyLinearMap_iff`: complexified differential operators.
* `TauCeti.IsLaplaceType.classicalPrincipalSymbol_complexifyLinearMap`,
  `TauCeti.IsLaplaceType.isClassicalElliptic_complexifyLinearMap`: operators of Laplace type.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (classical
  pseudodifferential operators on manifolds and their principal symbols).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4 and §8.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Ellipticity at a point -/

variable (m P) in
/-- A classical pseudodifferential operator `P` of order `m` on `M` is **elliptic at** `x` if its
principal symbol `σ_m(P)(x, ξ)` (`TauCeti.classicalPrincipalSymbol`) is nonzero at every nonzero
covector `ξ ∈ T*ₓM`. -/
def IsClassicalEllipticAt (x : M) : Prop :=
  ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
    classicalPrincipalSymbol m P x ξ ≠ 0

variable (m P) in
/-- A classical pseudodifferential operator `P` of order `m` on `M` is **elliptic** if it is
elliptic at every point (`TauCeti.IsClassicalEllipticAt`). -/
def IsClassicalElliptic : Prop :=
  ∀ x : M, IsClassicalEllipticAt m P x

theorem isClassicalEllipticAt_iff {x : M} :
    IsClassicalEllipticAt m P x ↔ ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
      classicalPrincipalSymbol m P x ξ ≠ 0 :=
  Iff.rfl

theorem isClassicalElliptic_iff : IsClassicalElliptic m P ↔ ∀ x : M, IsClassicalEllipticAt m P x :=
  Iff.rfl

/-- **Ellipticity ignores lower order terms.** Adding an operator of order `m - 1` does not change
ellipticity at a point. -/
theorem isClassicalEllipticAt_add_iff (hQ : Q ∈ classicalPseudodifferentialOperators (m - 1))
    {x : M} : IsClassicalEllipticAt m (P + Q) x ↔ IsClassicalEllipticAt m P x :=
  forall₂_congr fun ξ _ ↦ by rw [classicalPrincipalSymbol_add_of_mem_sub_one hQ]

/-- **Ellipticity ignores lower order terms.** Adding an operator of order `m - 1` does not change
ellipticity. -/
theorem isClassicalElliptic_add_iff (hQ : Q ∈ classicalPseudodifferentialOperators (m - 1)) :
    IsClassicalElliptic m (P + Q) ↔ IsClassicalElliptic m P :=
  forall_congr' fun _ ↦ isClassicalEllipticAt_add_iff hQ

/-- Multiplying by a nonzero complex number does not change ellipticity at a point. -/
@[simp]
theorem isClassicalEllipticAt_smul_iff {c : ℂ} (hc : c ≠ 0) {x : M} :
    IsClassicalEllipticAt m (c • P) x ↔ IsClassicalEllipticAt m P x := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  · refine forall₂_congr fun ξ _ ↦ ?_
    rw [classicalPrincipalSymbol_smul hP, mul_ne_zero_iff, and_iff_right hc]
  · -- Neither `P` nor `c • P` is of order `m`, so both principal symbols vanish.
    have hcP : c • P ∉ classicalPseudodifferentialOperators m := fun h ↦ hP <| by
      simpa [smul_smul, inv_mul_cancel₀ hc] using Submodule.smul_mem _ c⁻¹ h
    simp [isClassicalEllipticAt_iff, classicalPrincipalSymbol_of_notMem hP,
      classicalPrincipalSymbol_of_notMem hcP]

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isClassicalElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) :
    IsClassicalElliptic m (c • P) ↔ IsClassicalElliptic m P :=
  forall_congr' fun _ ↦ isClassicalEllipticAt_smul_iff hc

/-- Over a manifold of positive dimension, the principal symbol of an operator elliptic at `x` is
nonzero at some covector at `x`, read in the preferred chart at `x`. -/
private theorem IsClassicalEllipticAt.exists_ne_zero [Nontrivial (CoordinateSpace n)] {x : M}
    (hPx : IsClassicalEllipticAt m P x) :
    ∃ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, classicalPrincipalSymbol m P x ξ ≠ 0 := by
  obtain ⟨η, hη⟩ := exists_ne (0 : CoordinateSpace n)
  have he : chartAt (CoordinateSpace n) x ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  exact ⟨_, hPx _ ((innerSL_comp_mvfderiv_eq_zero_iff
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) (mem_chart_source _ x)).not.2 hη)⟩

/-- **Ellipticity forces the order.** Over a manifold of positive dimension, an operator elliptic
at some point is a classical pseudodifferential operator of order `m`: otherwise its principal
symbol vanishes by convention. -/
theorem IsClassicalEllipticAt.mem [Nontrivial (CoordinateSpace n)] {x : M}
    (hPx : IsClassicalEllipticAt m P x) : P ∈ classicalPseudodifferentialOperators m := by
  by_contra hP
  obtain ⟨ξ, hξ⟩ := hPx.exists_ne_zero
  exact hξ (classicalPrincipalSymbol_of_notMem hP x ξ)

/-- **An elliptic operator has exact order `m`.** Over a manifold of positive dimension, an operator
elliptic at some point is not of order `m - 1`, since its principal symbol would vanish. -/
theorem IsClassicalEllipticAt.notMem_sub_one [Nontrivial (CoordinateSpace n)] {x : M}
    (hPx : IsClassicalEllipticAt m P x) : P ∉ classicalPseudodifferentialOperators (m - 1) := by
  intro hP
  obtain ⟨ξ, hξ⟩ := hPx.exists_ne_zero
  exact hξ (classicalPrincipalSymbol_eq_zero_of_mem_sub_one hP x ξ)

/-- In dimension zero every covector vanishes, so every operator is elliptic at every point. -/
theorem isClassicalEllipticAt_of_subsingleton [Subsingleton (CoordinateSpace n)] (x : M) :
    IsClassicalEllipticAt m P x := fun ξ hξ ↦ by
  -- The tangent space at `x` is `ℝ⁰`.
  have : Subsingleton (TangentSpace 𝓘(ℝ, CoordinateSpace n) x) :=
    inferInstanceAs (Subsingleton (CoordinateSpace n))
  exact absurd (ContinuousLinearMap.ext fun v ↦ by
    simp [Subsingleton.elim v 0]) hξ

/-! ### Ellipticity in a chart -/

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n ℂ ℂ m}

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- The cutoffs `φ ψ` are supported in the chart target, so they can only be jointly nonzero
there. -/
private theorem mem_target_of_mul_ne_zero {y : CoordinateSpace n} (h : φ y * ψ y ≠ 0) :
    y ∈ e.target :=
  φ.tsupport_subset (subset_tsupport _ (left_ne_zero_of_mul h))

/-- **Ellipticity in a chart.** Let `a` be the symbol of the chart compression
`u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` of a classical pseudodifferential operator `P` of order `m`. At a
point `x` of the chart source where `φ ψ` does not vanish, `P` is elliptic exactly when the
principal symbol of `a` is invertible at `e x` at every nonzero frequency. -/
theorem isClassicalEllipticAt_iff_forall_isInvertible
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (hφψ : φ (e x) * ψ (e x) ≠ 0) :
    IsClassicalEllipticAt m P x ↔
      ∀ η : CoordinateSpace n, η ≠ 0 → (a.principal.coefficient (e x, η)).IsInvertible := by
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hc : ((φ (e x) * ψ (e x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hφψ
  simp_rw [coefficient_principal_eq_classicalPrincipalSymbol hP he φ ψ ha hx,
    ContinuousLinearMap.isInvertible_smul_id_iff, mul_ne_zero_iff, and_iff_right hc]
  refine ⟨fun h η hη ↦ h _ ((innerSL_comp_mvfderiv_eq_zero_iff he₁ hx).not.2 hη),
    fun h ξ hξ ↦ ?_⟩
  -- The covector `ξ` is `⟪η, ·⟫ ∘ de_x` for the frequency `η` dual to `ξ ∘ (de_x)⁻¹`.
  have hηξ := innerSL_toDual_symm_comp_inverse_mvfderiv he₁ hx ξ
  refine hηξ ▸ h _ fun hη ↦ hξ ?_
  rw [← hηξ, hη, map_zero, ContinuousLinearMap.zero_comp]

/-- **The chart symbol of an elliptic operator.** Let `a` be the symbol of the chart compression of
`P` by `φ`, `ψ` in a chart `e`, and let `U` be an open set on which `φ ψ` does not vanish (so `U`
lies in the chart target). The restriction of `a` to `U` is an elliptic classical symbol on `U`
exactly when `P` is elliptic at `e⁻¹ y` for every `y ∈ U`. -/
theorem isElliptic_restrict_iff_forall_isClassicalEllipticAt
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {U : TopologicalSpace.Opens (CoordinateSpace n)} (hφψ : ∀ y ∈ U, φ y * ψ y ≠ 0) :
    (ClassicalSymbol.restrict U a).IsElliptic ↔ ∀ y ∈ U, IsClassicalEllipticAt m P (e.symm y) := by
  rw [ClassicalSymbol.isElliptic_restrict_iff]
  refine forall₂_congr fun y hy ↦ ?_
  have hU := mem_target_of_mul_ne_zero (hφψ y hy)
  have hy' := e.right_inv hU
  rw [isClassicalEllipticAt_iff_forall_isInvertible hP ha (e.map_target hU)
    (hy'.symm ▸ hφψ y hy), hy']

/-! ### Openness -/

/-- **Ellipticity is an open condition.** A classical pseudodifferential operator elliptic at `x` is
elliptic at every point near `x`. -/
theorem IsClassicalEllipticAt.eventually {x : M} (hPx : IsClassicalEllipticAt m P x) :
    ∀ᶠ y in 𝓝 x, IsClassicalEllipticAt m P y := by
  -- In dimension zero every operator is elliptic; otherwise `P` has order `m`.
  rcases subsingleton_or_nontrivial (CoordinateSpace n) with hn | hn
  · exact .of_forall isClassicalEllipticAt_of_subsingleton
  have hP := hPx.mem
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  -- A cutoff `χ` equal to `1` near `e x`, and the symbol `a` of the compression by `χ`, `χ`.
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    isCompact_singleton (singleton_subset_iff.2 (e.map_source hx))
  rw [nhdsSet_singleton] at hχ
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  have hinv := (isClassicalEllipticAt_iff_forall_isInvertible hP ha hx
    (by simp [hχ.self_of_nhds])).1 hPx
  -- The principal symbol of `a` is nonzero at `(z, η)` for `z` near `e x` and `‖η‖ = 1`.
  have hS : ∀ᶠ z in 𝓝 (e x), ∀ η ∈ Metric.sphere (0 : CoordinateSpace n) 1,
      a.principal.coefficient (z, η) ≠ 0 := by
    refine (isCompact_sphere _ _).eventually_forall_of_forall_eventually fun η hη ↦ ?_
    have hη0 : η ≠ 0 := Metric.ne_of_mem_sphere hη one_ne_zero
    have hcont : ContinuousAt a.principal.coefficient (e x, η) :=
      a.principal.continuousOn_coefficient.continuousAt
        ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hη0)
    exact hcont.eventually_ne (ContinuousLinearMap.isInvertible_iff_ne_zero.1 (hinv η hη0))
  -- By homogeneity it is invertible at every nonzero frequency.
  have hall : ∀ᶠ z in 𝓝 (e x), χ z = 1 ∧ ∀ η : CoordinateSpace n, η ≠ 0 →
      (a.principal.coefficient (z, η)).IsInvertible := by
    filter_upwards [hχ, hS] with z hz1 hz
    refine ⟨hz1, fun η hη ↦ ?_⟩
    have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have hu : ‖η‖⁻¹ • η ∈ Metric.sphere (0 : CoordinateSpace n) 1 := by
      simp [norm_smul, hn.ne']
    have hscal : a.principal.coefficient (z, η) =
        ((‖η‖ ^ m : ℝ) : ℂ) • a.principal.coefficient (z, ‖η‖⁻¹ • η) := by
      rw [Complex.coe_smul, ← a.principal.homogeneous z _ _ hn, smul_inv_smul₀ hn.ne']
    rw [hscal, ContinuousLinearMap.isInvertible_smul_iff
      (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hn m).ne'),
      ContinuousLinearMap.isInvertible_iff_ne_zero]
    exact hz _ hu
  filter_upwards [e.open_source.mem_nhds hx, (e.continuousAt hx).eventually hall] with y hy hy'
  exact (isClassicalEllipticAt_iff_forall_isInvertible hP ha hy (by simp [hy'.1])).2 hy'.2

variable (m P) in
/-- **Ellipticity is an open condition.** The points at which a classical pseudodifferential
operator is elliptic form an open set. -/
theorem isOpen_setOf_isClassicalEllipticAt :
    IsOpen {x : M | IsClassicalEllipticAt m P x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ hx.eventually

/-! ### Local inverse symbols -/

omit he a in
/-- The points where the cutoffs `φ ψ` do not vanish and over which `P` is elliptic form an open
set. -/
private theorem isOpen_setOf_ellipticChart (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    IsOpen {y | φ y * ψ y ≠ 0 ∧ IsClassicalEllipticAt m P (e.symm y)} :=
  isOpen_iff_mem_nhds.2 fun y ⟨hyφψ, hyP⟩ ↦ by
    filter_upwards [
      ((φ.contDiff.continuous.mul ψ.contDiff.continuous).continuousAt (x := y)).eventually_ne
        hyφψ,
      (e.continuousAt_symm (mem_target_of_mul_ne_zero hyφψ)).eventually hyP.eventually]
      with z hzφψ hzP
    exact ⟨hzφψ, hzP⟩

/-- **Ellipticity of a chart symbol over a compact set.** Let `a` be the symbol of the chart
compression of `P` by `φ`, `ψ` in a chart `e`, and `K` a compact set at whose points `φ ψ` does not
vanish (so `K` lies in the chart target) and over which `P` is elliptic. Then `a` is elliptic over
`K` at all frequencies of norm at least some radius `R`: its value is invertible there, with
`‖a(y, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem exists_isEllipticOn_of_forall_isClassicalEllipticAt
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hKφψ : ∀ y ∈ K, φ y * ψ y ≠ 0) (hKP : ∀ y ∈ K, IsClassicalEllipticAt m P (e.symm y)) :
    ∃ R, a.toSymbol.IsEllipticOn {p | p.1 ∈ K ∧ R ≤ ‖p.2‖} := by
  -- The open set `U` where `φ ψ ≠ 0` and `P` is elliptic contains `K`.
  set U : TopologicalSpace.Opens (CoordinateSpace n) :=
    ⟨{y | φ y * ψ y ≠ 0 ∧ IsClassicalEllipticAt m P (e.symm y)}, isOpen_setOf_ellipticChart φ ψ⟩
  have hKU : K ⊆ U := fun y hy ↦ ⟨hKφψ y hy, hKP y hy⟩
  have hUa : (ClassicalSymbol.restrict U a).IsElliptic :=
    (isElliptic_restrict_iff_forall_isClassicalEllipticAt (U := U) hP ha
      fun _ hy ↦ hy.1).2 fun _ hy ↦ hy.2
  exact hUa.exists_isEllipticOn hKU hK fun y hy ξ ↦ by
    rw [ClassicalSymbol.toLocalSymbol_restrict, Symbol.coefficient_restrict_of_mem _ (hKU hy)]

/-- **Local inverse symbols of an elliptic operator.** Let `a` be the symbol of the chart
compression of `P` by `φ`, `ψ` in a chart `e`, and `K` a compact set at whose points `φ ψ` does not
vanish (so `K` lies in the chart target) and over which `P` is elliptic. Then a symbol `b` of order
`-m` inverts `a` on both sides at all large frequencies and all positions near `K`. -/
theorem exists_comp_eq_id_of_forall_isClassicalEllipticAt
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hKφψ : ∀ y ∈ K, φ y * ψ y ≠ 0) (hKP : ∀ y ∈ K, IsClassicalEllipticAt m P (e.symm y)) :
    ∃ (b : Symbol n ℂ ℂ (-m)) (R : ℝ), ∀ᶠ y in 𝓝ˢ K, ∀ ξ, R ≤ ‖ξ‖ →
      b.coefficient (y, ξ) ∘L a.toSymbol.coefficient (y, ξ) = .id ℂ ℂ ∧
        a.toSymbol.coefficient (y, ξ) ∘L b.coefficient (y, ξ) = .id ℂ ℂ := by
  -- The same conditions hold on a compact neighbourhood `L` of `K`.
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK (isOpen_setOf_ellipticChart φ ψ)
    fun y hy ↦ ⟨hKφψ y hy, hKP y hy⟩
  obtain ⟨R, hR⟩ := exists_isEllipticOn_of_forall_isClassicalEllipticAt hP ha hL
    (fun y hy ↦ (hLU hy).1) fun y hy ↦ (hLU hy).2
  exact (Symbol.exists_mem_nhdsSet_isEllipticOn_iff hK).1
    ⟨L, subset_interior_iff_mem_nhdsSet.1 hKL, R, hR⟩

/-! ### Differential operators -/

/-- **Elliptic differential operators.** The complexification of a differential operator `D` of
order at most `m` on the real-valued smooth functions on `M` is elliptic of order `m` at `x` exactly
when the geometric principal symbol of `D` (`TauCeti.smoothPrincipalSymbol`) vanishes at no nonzero
covector at `x`. -/
theorem isClassicalEllipticAt_complexifyLinearMap_iff {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m) (x : M) :
    IsClassicalEllipticAt m (ContMDiffMap.complexifyLinearMap D) x ↔
      ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
        smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
          ⟨D, hD⟩ ξ ≠ 0 :=
  forall₂_congr fun ξ hξ ↦ by
    rw [classicalPrincipalSymbol_complexifyLinearMap hD x hξ, mul_ne_zero_iff,
      and_iff_right (pow_ne_zero _ Complex.I_ne_zero), Complex.ofReal_ne_zero]

variable [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, CoordinateSpace n) x)]
  {D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ 2} {c : ℝ}

/-- **The principal symbol of an operator of Laplace type.** The complexification of an operator
of Laplace type with constant `c` has principal symbol `c ‖ξ‖²` of order `2`, the norm being the
one the metric induces on `T*ₓM`. -/
theorem IsLaplaceType.classicalPrincipalSymbol_complexifyLinearMap (hD : IsLaplaceType D c)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol 2 (ContMDiffMap.complexifyLinearMap
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)) x ξ =
      c * ‖ξ‖ ^ 2 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have h := TauCeti.classicalPrincipalSymbol_complexifyLinearMap D.property x hξ
  rw [Nat.cast_ofNat] at h
  rw [h, hD.smoothPrincipalSymbol_eq, Complex.I_sq]
  push_cast
  ring

/-- **Operators of Laplace type are elliptic.** The complexification of an operator of Laplace
type, such as `-Δ`, is an elliptic classical pseudodifferential operator of order `2`. -/
theorem IsLaplaceType.isClassicalElliptic_complexifyLinearMap (hD : IsLaplaceType D c) :
    IsClassicalElliptic 2 (ContMDiffMap.complexifyLinearMap
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)) :=
    fun x ξ hξ ↦ by
  rw [hD.classicalPrincipalSymbol_complexifyLinearMap]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hD.pos.ne') (pow_ne_zero _
    (Complex.ofReal_ne_zero.2 fun h ↦ hξ ((ContinuousLinearMap.opNorm_zero_iff ξ).1 h)))

end TauCeti
