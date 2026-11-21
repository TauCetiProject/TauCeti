/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Intertwiner
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Intertwiners, functoriality, regular and discrete formulas for Bochner `L¹` integrated forms

This file complements `TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1` for the Bochner `L¹`
integrated form `CovariantRepresentation.integratedOperatorBochnerL1`:

* **Intertwiners, uniqueness, and commutants**: `comp_integratedOperatorBochnerL1`,
  `topologicalClosure_span_integratedOperatorBochnerL1`,
  `dense_span_integratedOperatorBochnerL1_iff`, `comp_integratedOperatorBochnerL1_iff`,
  `ext_integratedOperatorBochnerL1`, and `centralizer_range_integratedOperatorBochnerL1`.
* **Functoriality and direct sums**: `integratedOperatorBochnerL1_comap` (intertwining with
  `CStarAction.Hom.mapLp`), `integratedOperatorBochnerL1_hilbertSum_apply`, and
  `integratedOperatorBochnerL1_hilbertSum`.
* **Completion extension and regular representation**:
  `integratedOperatorBochnerL1_toL1FromCompletion` (without local compactness) and
  `integratedOperatorBochnerL1_regular_trivial` (identifying the trivial regular representation on
  `L²(G, H)` with `MeasureTheory.Lp.convolutionL`).
* **Discrete groups**: unconditional `ℓ¹` series formulas
  `hasSum_integratedOperatorBochnerL1_count_apply`, `integratedOperatorBochnerL1_count_apply`,
  `hasSum_integratedOperatorBochnerL1_count_toL1`, `integratedOperatorBochnerL1_count_toL1`, and
  `norm_integratedOperatorBochnerL1_count_toL1_le`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory Topology UniformSpace
open scoped CompactlySupported CStarAlgebra ENNReal InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

/-! ### Intertwiners, nondegeneracy, uniqueness, and commutants -/

section Intertwiner

variable {G A H K : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : CStarAction G A}

/-- A bounded operator intertwining two covariant pairs intertwines their
`integratedOperatorBochnerL1` forms. -/
theorem comp_integratedOperatorBochnerL1 [R1Space G] (μ : Measure G) [μ.InnerRegularCompactLTTop]
    {P : CovariantRepresentation α H} {Q : CovariantRepresentation α K} {T : H →L[ℂ] K}
    (hπ : ∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T)
    (hU : ∀ g, T ∘L P.group g = Q.group g ∘L T) (u : Lp A 1 μ) :
    T ∘L P.integratedOperatorBochnerL1 μ u = Q.integratedOperatorBochnerL1 μ u ∘L T := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, integratedOperatorBochnerL1_apply]
  rw [← T.integral_comp_comm (P.integrable_integrand_of_integrable (L1.integrable_coeFn u) v)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  rw [← ContinuousLinearMap.comp_apply T, hπ, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply T, hU, ContinuousLinearMap.comp_apply]

section LocallyCompact

variable [R1Space G] [LocallyCompactSpace G] (P : CovariantRepresentation α H)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsOpenPosMeasure]

/-- `integratedOperatorBochnerL1` generates the closed essential subspace of the coefficient
representation. -/
theorem topologicalClosure_span_integratedOperatorBochnerL1 :
    (Submodule.span ℂ
      (⋃ u : Lp A 1 μ, Set.range (P.integratedOperatorBochnerL1 μ u))).topologicalClosure =
      (Submodule.span ℂ (⋃ a : A, Set.range (P.coefficient a))).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.orthogonal_orthogonal_eq_closure]
  congr 1; ext w
  have hspan (s : Set H) : w ∈ (Submodule.span ℂ s)ᗮ ↔ ∀ x ∈ s, ⟪w, x⟫_ℂ = 0 := by
    rw [Submodule.mem_orthogonal']; exact Submodule.span_le (p := (innerSL ℂ w).ker)
  simp only [hspan, Set.forall_mem_iUnion, Set.forall_mem_range]
  refine ⟨fun h a v => (P.forall_inner_integratedOperator_eq_zero_iff μ w).1 (fun f x => by
      simpa only [integratedOperatorBochnerL1_toLp] using
        h (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) x) a v,
    fun h u v => ?_⟩
  rw [P.inner_integratedOperatorBochnerL1_apply]
  exact integral_eq_zero_of_ae (.of_forall fun g => h (u g) (P.group g v))

/-- Nondegeneracy is preserved and reflected by `integratedOperatorBochnerL1`. -/
theorem dense_span_integratedOperatorBochnerL1_iff :
    Dense (Submodule.span ℂ
      (⋃ u : Lp A 1 μ, Set.range (P.integratedOperatorBochnerL1 μ u)) : Set H) ↔
      P.coefficient.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top,
    P.topologicalClosure_span_integratedOperatorBochnerL1 μ]

end LocallyCompact

section Nondegenerate

variable [IsTopologicalGroup G] [LocallyCompactSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
  [μ.IsOpenPosMeasure]

/-- For a nondegenerate source pair, intertwining `integratedOperatorBochnerL1` is equivalent to
intertwining both the coefficient and group representations. -/
theorem comp_integratedOperatorBochnerL1_iff
    {P : CovariantRepresentation α H} {Q : CovariantRepresentation α K}
    (hP : P.coefficient.IsNondegenerate) {T : H →L[ℂ] K} :
    (∀ u, T ∘L P.integratedOperatorBochnerL1 μ u = Q.integratedOperatorBochnerL1 μ u ∘L T) ↔
      (∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T) ∧
        ∀ g, T ∘L P.group g = Q.group g ∘L T :=
  ⟨fun h => (comp_integratedOperator_iff μ hP).1 fun f => by
    simpa only [integratedOperatorBochnerL1_toLp] using
      h (CompactlySupportedContinuousMap.toLp 1 μ ℂ f),
    fun h => comp_integratedOperatorBochnerL1 μ h.1 h.2⟩

/-- A nondegenerate covariant pair is uniquely determined by `integratedOperatorBochnerL1`. -/
theorem ext_integratedOperatorBochnerL1 {P Q : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate)
    (h : P.integratedOperatorBochnerL1 μ = Q.integratedOperatorBochnerL1 μ) : P = Q :=
  ext_integratedOperator μ hP fun f => by
    simpa only [integratedOperatorBochnerL1_toLp] using
      congrArg (fun L => L (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)) h

/-- For a nondegenerate pair, the commutant of `integratedOperatorBochnerL1` equals the joint
commutant of `P.coefficient` and `P.group`. -/
theorem centralizer_range_integratedOperatorBochnerL1 {P : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate) :
    Set.centralizer (Set.range (P.integratedOperatorBochnerL1 μ)) =
      Set.centralizer (Set.range P.coefficient ∪ Set.range P.group) := by
  ext T
  have h := comp_integratedOperatorBochnerL1_iff μ hP (Q := P) (T := T)
  simp only [← ContinuousLinearMap.mul_def] at h
  simp only [Set.mem_centralizer_iff, Set.mem_union, or_imp, forall_and, Set.forall_mem_range]
  simpa only [eq_comm (a := T * _)] using h

end Nondegenerate

end Intertwiner

/-! ### Functoriality and Hilbert direct sums -/

section Functoriality

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Pulling back a covariant pair along `φ : Hom α β` commutes with
`integratedOperatorBochnerL1`. -/
theorem integratedOperatorBochnerL1_comap (Q : CovariantRepresentation β H) (φ : Hom α β)
    (μ : Measure G) [μ.InnerRegularCompactLTTop] (u : Lp A 1 μ) :
    (Q.comap φ).integratedOperatorBochnerL1 μ u =
      Q.integratedOperatorBochnerL1 μ (φ.mapLp μ 1 u) := by
  ext v
  rw [integratedOperatorBochnerL1_apply, integratedOperatorBochnerL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [φ.coeFn_mapLp u] with g hg
  simp [hg]

section HilbertSum

variable {ι : Type*} {K : ι → Type*} [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (K i)] [∀ i, CompleteSpace (K i)]
  (Q : ∀ i, CovariantRepresentation α (K i)) (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- `integratedOperatorBochnerL1` commutes with evaluation in every summand of a Hilbert direct
sum. -/
@[simp]
theorem integratedOperatorBochnerL1_hilbertSum_apply (u : Lp A 1 μ) (x : lp K 2) (i : ι) :
    (hilbertSum Q).integratedOperatorBochnerL1 μ u x i =
      (Q i).integratedOperatorBochnerL1 μ u (x i) := by
  let ev := lp.evalCLM ℂ K 2 i
  calc
    (hilbertSum Q).integratedOperatorBochnerL1 μ u x i =
        ev ((hilbertSum Q).integratedOperatorBochnerL1 μ u x) :=
      (lp.evalCLM_apply i _).symm
    _ = ev (∫ g, (hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x) ∂μ) :=
      congrArg ev ((hilbertSum Q).integratedOperatorBochnerL1_apply u x)
    _ = ∫ g, ev ((hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x)) ∂μ :=
      (ev.integral_comp_comm
        ((hilbertSum Q).integrable_integrand_of_integrable (L1.integrable_coeFn u) x)).symm
    _ = ∫ g, (Q i).coefficient (u g) ((Q i).group g (x i)) ∂μ :=
      integral_congr_ae (.of_forall fun g => by simp [ev])
    _ = (Q i).integratedOperatorBochnerL1 μ u (x i) :=
      ((Q i).integratedOperatorBochnerL1_apply u (x i)).symm

/-- `integratedOperatorBochnerL1` of a Hilbert direct sum is the direct sum of the component
integrated maps. -/
theorem integratedOperatorBochnerL1_hilbertSum (u : Lp A 1 μ) :
    (hilbertSum Q).integratedOperatorBochnerL1 μ u =
      lp.mapCLM 2 (fun i => (Q i).integratedOperatorBochnerL1 μ u) (norm_nonneg u)
        (fun i => (Q i).norm_integratedOperatorBochnerL1_apply_le u) := by
  ext x i; simp

end HilbertSum

end Functoriality

/-! ### Completion extension without local compactness and regular representation on `L²` -/

section CompletionAndRegular

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- Along `ConvolutionAlgebra.toL1FromCompletion`, `integratedOperatorBochnerL1` agrees with
`integratedOperatorL1` without requiring local compactness of `G`. -/
@[simp]
theorem integratedOperatorBochnerL1_toL1FromCompletion (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorBochnerL1 μ (ConvolutionAlgebra.toL1FromCompletion α μ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.integratedOperatorBochnerL1 μ).continuous.comp
        (ConvolutionAlgebra.toL1FromCompletion α μ).continuous)
      (P.continuous_integratedOperatorL1 μ)
  | ih f => simp

/-- For the trivial action of `G` on `ℂ` acting by scalars on any complex Hilbert space `H`,
`integratedOperatorBochnerL1` of the regular representation on `L²(G, H)` is
`MeasureTheory.Lp.convolutionL`. -/
theorem integratedOperatorBochnerL1_regular_trivial (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] :
    (regular (CStarAction.trivial (G := G) (A := ℂ))
        (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom μ).integratedOperatorBochnerL1 μ =
      Lp.convolutionL μ 2 ENNReal.ofNat_ne_top := by
  let ρ : ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  ext f ξ : 2
  rw [integratedOperatorBochnerL1_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  refine Lp.ext ?_
  filter_upwards [coeFn_regular_coefficient (CStarAction.trivial (G := G) (A := ℂ)) ρ μ (f g)
      ((regular (CStarAction.trivial (G := G) (A := ℂ)) ρ μ).group g ξ),
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ξ,
    Lp.coeFn_smul (f g) (Lp.leftTranslation μ 2 ℂ g ξ),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) g ξ] with r h₁ h₂ h₃ h₄
  rw [h₁, regular_group, h₂, h₃, Pi.smul_apply, h₄]
  simp [ρ, Algebra.algebraMap_eq_smul_one]

end CompletionAndRegular

/-! ### Counting measure on discrete groups -/

section Discrete

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For counting measure on a discrete group, `integratedOperatorBochnerL1` acts on `v` by the
unconditionally convergent series `∑ g, π (u g) (U g v)`. -/
theorem hasSum_integratedOperatorBochnerL1_count_apply
    (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    HasSum (fun g => P.coefficient (u g) (P.group g v))
      (P.integratedOperatorBochnerL1 Measure.count u v) := by
  rw [integratedOperatorBochnerL1_apply]
  have hint := P.integrable_integrand_of_integrable (L1.integrable_coeFn u) v
  unfold Measure.count at hint ⊢
  simpa only [integral_dirac] using hasSum_integral_measure hint

/-- Series formula for `integratedOperatorBochnerL1` with respect to counting measure on a
discrete group. -/
theorem integratedOperatorBochnerL1_count_apply
    (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    P.integratedOperatorBochnerL1 Measure.count u v =
      ∑' g, P.coefficient (u g) (P.group g v) :=
  (P.hasSum_integratedOperatorBochnerL1_count_apply u v).tsum_eq.symm

/-- For an `ℓ¹` family `f : G → A` on a discrete group, `g ↦ π (f g) (U g v)` sums unconditionally
to `integratedOperatorBochnerL1` of `(integrable_count_iff.2 hf).toL1 f`. -/
theorem hasSum_integratedOperatorBochnerL1_count_toL1 {f : G → A} (hf : Summable (‖f ·‖))
    (v : H) :
    HasSum (fun g => P.coefficient (f g) (P.group g v))
      (P.integratedOperatorBochnerL1 Measure.count ((integrable_count_iff.2 hf).toL1 f) v) := by
  have hcoe : ∀ g, ((integrable_count_iff.2 hf).toL1 f : G → A) g = f g :=
    Measure.ae_count_iff.1 (integrable_count_iff.2 hf).coeFn_toL1
  simpa only [hcoe] using
    P.hasSum_integratedOperatorBochnerL1_count_apply ((integrable_count_iff.2 hf).toL1 f) v

/-- For an `ℓ¹` family `f : G → A` on a discrete group, `integratedOperatorBochnerL1` acts by
`∑' g, π (f g) (U g v)`. -/
theorem integratedOperatorBochnerL1_count_toL1 {f : G → A} (hf : Summable (‖f ·‖)) (v : H) :
    P.integratedOperatorBochnerL1 Measure.count ((integrable_count_iff.2 hf).toL1 f) v =
      ∑' g, P.coefficient (f g) (P.group g v) :=
  (P.hasSum_integratedOperatorBochnerL1_count_toL1 hf v).tsum_eq.symm

/-- For an `ℓ¹` family `f : G → A` on a discrete group, the operator norm of
`integratedOperatorBochnerL1` is bounded by `∑' g, ‖f g‖`. -/
theorem norm_integratedOperatorBochnerL1_count_toL1_le {f : G → A} (hf : Summable (‖f ·‖)) :
    ‖P.integratedOperatorBochnerL1 Measure.count ((integrable_count_iff.2 hf).toL1 f)‖ ≤
      ∑' g, ‖f g‖ := by
  refine (P.norm_integratedOperatorBochnerL1_toL1_le Measure.count
    (integrable_count_iff.2 hf)).trans_eq ?_
  have hint := (integrable_count_iff.2 hf).norm
  unfold Measure.count at hint ⊢
  simpa only [integral_dirac] using integral_sum_measure hint

end Discrete

end TauCeti.CStarAction.CovariantRepresentation
