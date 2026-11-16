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
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Bochner `L¹` integrated forms of covariant representations

Let `P = (π, U)` be a covariant representation of a point-norm continuous C⋆-action `α` of a
topological group `G` on a possibly nonunital C⋆-algebra `A` on a complex Hilbert space `H`. This
file constructs the Bochner `L¹` integrated form `CovariantRepresentation.integratedLp` directly on
`Lp A 1 μ` for any inner-regular Borel measure `μ` on an `R₁` group, without operator-norm
continuity of `U`, unitality of `A`, nondegeneracy of `π`, separability of `H`, second countability
of `G`, or σ-finiteness of `μ`. Strong measurability of `g ↦ π (f g) (U g v)` follows from
`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply`.

We establish compatibility with `CovariantRepresentation.integratedOperatorL1` along
`ConvolutionAlgebra.toL1FromCompletion` and `ConvolutionAlgebra.completionEquivLp`, intertwiner
correspondence, nondegeneracy preservation, uniqueness, commutant identification, equivariant
functoriality, Hilbert direct sums, covariance under `CStarAction.translateLp`, multiplicativity
under `CStarAction.convolutionLp`, star preservation under `CStarAction.twistedInvolutionLp`,
scalar comparison with `ContRepresentation.integratedOperatorL1`, identification of the trivial
regular representation on `L²(G, H)` with `MeasureTheory.Lp.convolutionL`, and `ℓ¹` series formulas
for counting measure on discrete groups.

## Main definitions

* `TauCeti.CStarAction.CovariantRepresentation.integratedLp`: contractive continuous linear map
  `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` sending `u` to `v ↦ ∫ g, π (u g) (U g v) dμ(g)`.

## Main statements

* `TauCeti.CStarAction.CovariantRepresentation.exists_integratedOperator`: bounded integrated
  operator of norm at most `∫ g, ‖f g‖ dμ(g)` for any Bochner-integrable `f : G → A`.
* `TauCeti.CStarAction.CovariantRepresentation.comp_integratedLp`,
  `TauCeti.CStarAction.CovariantRepresentation.comp_integratedLp_iff`,
  `TauCeti.CStarAction.CovariantRepresentation.ext_integratedLp`,
  `TauCeti.CStarAction.CovariantRepresentation.centralizer_range_integratedLp`,
  `TauCeti.CStarAction.CovariantRepresentation.dense_span_integratedLp_iff`: intertwiner,
  uniqueness, commutant, and nondegeneracy results for `integratedLp`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedLp_convolutionLp`,
  `TauCeti.CStarAction.CovariantRepresentation.integratedLp_twistedInvolutionLp`: multiplicativity
  and star preservation on Bochner `L¹`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedLp_regular_trivial`: identification of the
  trivial regular representation on `L²(G, H)` with `MeasureTheory.Lp.convolutionL`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedLp_count_toL1`: `ℓ¹` series formula for
  counting measure on discrete groups.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory Topology UniformSpace
open scoped CompactlySupported CStarAlgebra ENNReal InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

/-! ### Direct vector integration on Bochner `L¹` -/

section IntegratedLp

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.InnerRegularCompactLTTop]

omit [MeasurableSpace G] [R1Space G] [BorelSpace G] in
private theorem norm_coefficient_group_le (a : A) (g : G) (v : H) :
    ‖P.coefficient a (P.group g v)‖ ≤ ‖a‖ * ‖v‖ :=
  calc
    ‖P.coefficient a (P.group g v)‖
        ≤ ‖P.coefficient a‖ * ‖P.group g v‖ := (P.coefficient a).le_opNorm _
    _ ≤ ‖a‖ * ‖v‖ := by
      rw [P.isUnitary.norm_map]
      exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

/-- For any Bochner-integrable `f : G → A` and vector `v : H`, the orbit integrand
`g ↦ π (f g) (U g v)` is Bochner-integrable in `H`. Inner regularity of `μ` on finite-measure sets
gives strong measurability without separability of `H` or second countability of `G`. -/
theorem integrable_integrand_of_integrable {f : G → A} (hf : Integrable f μ) (v : H) :
    Integrable (fun g => P.coefficient (f g) (P.group g v)) μ := by
  have hmeas : AEStronglyMeasurable (fun g => P.coefficient (f g) (P.group g v)) μ := by
    simpa only [Function.comp_apply, ContinuousLinearMap.flip_apply,
      NonUnitalStarAlgHom.toContinuousLinearMap_apply] using
      hf.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
        ((NonUnitalStarAlgHom.toContinuousLinearMap P.coefficient).flip.continuous.comp
          (P.continuous_orbit v))
  refine (hf.norm.mul_const ‖v‖).mono' hmeas
    (.of_forall fun g => P.norm_coefficient_group_le (f g) g v)

omit [R1Space G] [BorelSpace G] [μ.InnerRegularCompactLTTop] in
private theorem norm_integral_integrand_le {f : G → A} (hf : Integrable f μ) (v : H) :
    ‖∫ g, P.coefficient (f g) (P.group g v) ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ :=
  calc
    ‖∫ g, P.coefficient (f g) (P.group g v) ∂μ‖ ≤ ∫ g, ‖f g‖ * ‖v‖ ∂μ :=
      norm_integral_le_of_norm_le (hf.norm.mul_const _)
        (.of_forall fun g => P.norm_coefficient_group_le (f g) g v)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖v‖ := integral_mul_const _ _

/-- **The Bochner `L¹` integrated form** of a covariant representation `P = (π, U)`: the contractive
continuous linear map `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` defined pointwise on `v : H` by the Hilbert-space
Bochner integral `∫ g, π (u g) (U g v) dμ(g)`. -/
def integratedLp : Lp A 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (u : Lp A 1 μ) (v : H) => ∫ g, P.coefficient (u g) (P.group g v) ∂μ)
      (fun u₁ u₂ v => by
        rw [← integral_add (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u₁) v)
          (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u₂) v)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u₁ u₂] with g hg
        rw [hg, Pi.add_apply, map_add, add_apply])
      (fun c u v => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with g hg
        rw [hg, Pi.smul_apply, map_smul, smul_apply])
      (fun u v₁ v₂ => by
        rw [← integral_add (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v₁)
          (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v₂)]
        simp_rw [map_add])
      (fun c u v => by
        rw [← integral_smul]
        simp_rw [map_smul]))
    1 fun u v => by
      simpa [L1.norm_eq_integral_norm] using
        P.norm_integral_integrand_le μ (L1.integrable_coeFn u) v

/-- The defining vector integral for `integratedLp`. -/
theorem integratedLp_apply (u : Lp A 1 μ) (v : H) :
    P.integratedLp μ u v = ∫ g, P.coefficient (u g) (P.group g v) ∂μ := (rfl)

/-- On the `L¹` class of an integrable `f : G → A`, `integratedLp` integrates `π (f g) (U g v)`. -/
@[simp]
theorem integratedLp_toL1 {f : G → A} (hf : Integrable f μ) (v : H) :
    P.integratedLp μ (hf.toL1 f) v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ := by
  rw [integratedLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with g hg; rw [hg]

/-- `integratedLp` is a contraction on `Lp A 1 μ`: `‖(π ⋊ U)(u)‖ ≤ ‖u‖`. -/
theorem norm_integratedLp_apply_le (u : Lp A 1 μ) : ‖P.integratedLp μ u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun v => ?_
  simpa [integratedLp_apply, L1.norm_eq_integral_norm] using
    P.norm_integral_integrand_le μ (L1.integrable_coeFn u) v

/-- The operator norm of `integratedLp` is at most one. -/
theorem norm_integratedLp_le : ‖P.integratedLp μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using P.norm_integratedLp_apply_le μ u

/-- For an integrable `f : G → A`, `‖(π ⋊ U)(f)‖ ≤ ∫ g, ‖f g‖ dμ(g)`. -/
theorem norm_integratedLp_toL1_le {f : G → A} (hf : Integrable f μ) :
    ‖P.integratedLp μ (hf.toL1 f)‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun v => ?_
  rw [integratedLp_toL1]; exact P.norm_integral_integrand_le μ hf v

/-- **Existence and `L¹` bound for the integrated operator**: every Bochner-integrable `f : G → A`
defines `T : H →L[ℂ] H` with `T ξ = ∫ g, π (f g) (U g ξ) dμ(g)` and `‖T‖ ≤ ∫ g, ‖f g‖ dμ(g)`. -/
theorem exists_integratedOperator (f : G → A) (hf : Integrable f μ) :
    ∃ T : H →L[ℂ] H,
      (∀ ξ, T ξ = ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ) ∧ ‖T‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  ⟨P.integratedLp μ (hf.toL1 f), P.integratedLp_toL1 μ hf, P.norm_integratedLp_toL1_le μ hf⟩

/-- Matrix coefficients of `integratedLp` are integrals of vector matrix coefficients. -/
theorem inner_integratedLp_apply (u : Lp A 1 μ) (w v : H) :
    ⟪w, P.integratedLp μ u v⟫_ℂ = ∫ g, ⟪w, P.coefficient (u g) (P.group g v)⟫_ℂ ∂μ := by
  rw [integratedLp_apply,
    integral_inner (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v)]

/-- Covariance moves a coefficient operator on the right of `integratedLp` inside the integral. -/
theorem integratedLp_coefficient_apply (u : Lp A 1 μ) (a : A) (v : H) :
    P.integratedLp μ u (P.coefficient a v) = ∫ g, P.coefficient (u g * α g a) (P.group g v) ∂μ := by
  rw [integratedLp_apply]; simp_rw [P.covariance, map_mul, mul_apply_eq_comp]

/-- Left multiplication by `a ∈ A` on `Lp A 1 μ` becomes left multiplication by `π(a)`. -/
@[simp]
theorem integratedLp_mul_compLp (a : A) (u : Lp A 1 μ) :
    P.integratedLp μ ((ContinuousLinearMap.mul ℂ A a).compLp u) =
      P.coefficient a * P.integratedLp μ u := by
  ext v
  rw [mul_apply_eq_comp, integratedLp_apply, integratedLp_apply,
    ← (P.coefficient a).integral_comp_comm
      (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v)]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp u] with g hg
  simp [hg, map_mul]

/-- For the trivial covariant pair of `π`, `integratedLp` applies `π` to `∫ g, u g ∂μ`. -/
@[simp]
theorem integratedLp_trivial (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (u : Lp A 1 μ) :
    (trivial (G := G) π).integratedLp μ u = π (∫ g, u g ∂μ) := by
  ext v
  have h := (trivial (G := G) π).integral_coefficient_apply (L1.integrable_coeFn u) v
  simpa only [integratedLp_apply, trivial_coefficient, trivial_group,
    ContRepresentation.trivial_apply] using h

/-- On compactly supported continuous functions, `integratedLp` agrees with `integratedOperator`. -/
@[simp]
theorem integratedLp_toL1_eq_integratedOperator [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) :
    P.integratedLp μ (f.integrable.toL1 f) = P.integratedOperator μ f := by
  ext v; rw [integratedLp_toL1, integratedOperator_apply]

/-- On `ConvolutionAlgebra α μ`, `integratedLp` composed with `toL1` is `integratedOperator`. -/
@[simp]
theorem integratedLp_convolutionAlgebra_toL1 [IsFiniteMeasureOnCompacts μ]
    (f : ConvolutionAlgebra α μ) :
    P.integratedLp μ (ConvolutionAlgebra.toL1 f) = P.integratedOperator μ f.ofConv := by
  rw [ConvolutionAlgebra.toL1_apply, integratedLp_toL1_eq_integratedOperator]

end IntegratedLp

/-! ### Intertwiners, nondegeneracy, uniqueness, and commutants -/

section Intertwiner

variable {G A H K : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : CStarAction G A}

/-- A bounded operator intertwining two covariant pairs intertwines their `integratedLp` forms. -/
theorem comp_integratedLp [R1Space G] (μ : Measure G) [μ.InnerRegularCompactLTTop]
    {P : CovariantRepresentation α H} {Q : CovariantRepresentation α K} {T : H →L[ℂ] K}
    (hπ : ∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T)
    (hU : ∀ g, T ∘L P.group g = Q.group g ∘L T) (u : Lp A 1 μ) :
    T ∘L P.integratedLp μ u = Q.integratedLp μ u ∘L T := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, integratedLp_apply]
  rw [← T.integral_comp_comm (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  rw [← ContinuousLinearMap.comp_apply T, hπ, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply T, hU, ContinuousLinearMap.comp_apply]

section LocallyCompact

variable [R1Space G] [LocallyCompactSpace G] (P : CovariantRepresentation α H)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsOpenPosMeasure]

/-- `integratedLp` generates the closed essential subspace of the coefficient representation. -/
theorem topologicalClosure_span_integratedLp :
    (Submodule.span ℂ (⋃ u : Lp A 1 μ, Set.range (P.integratedLp μ u))).topologicalClosure =
      (Submodule.span ℂ (⋃ a : A, Set.range (P.coefficient a))).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.orthogonal_orthogonal_eq_closure]
  congr 1; ext w
  have hspan (s : Set H) : w ∈ (Submodule.span ℂ s)ᗮ ↔ ∀ x ∈ s, ⟪w, x⟫_ℂ = 0 := by
    rw [Submodule.mem_orthogonal']; exact Submodule.span_le (p := (innerSL ℂ w).ker)
  simp only [hspan, Set.forall_mem_iUnion, Set.forall_mem_range]
  refine ⟨fun h a v => (P.forall_inner_integratedOperator_eq_zero_iff μ w).1 (fun f x => by
      simpa only [integratedLp_toL1_eq_integratedOperator] using h (f.integrable.toL1 f) x) a v,
    fun h u v => ?_⟩
  rw [P.inner_integratedLp_apply]
  exact integral_eq_zero_of_ae (.of_forall fun g => h (u g) (P.group g v))

/-- Nondegeneracy is preserved and reflected by the Bochner `L¹` integrated form. -/
theorem dense_span_integratedLp_iff :
    Dense (Submodule.span ℂ (⋃ u : Lp A 1 μ, Set.range (P.integratedLp μ u)) : Set H) ↔
      P.coefficient.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top, P.topologicalClosure_span_integratedLp μ]

end LocallyCompact

section Nondegenerate

variable [IsTopologicalGroup G] [LocallyCompactSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
  [μ.IsOpenPosMeasure]

/-- For a nondegenerate source pair, intertwining `integratedLp` is equivalent to intertwining both
the coefficient and group representations. -/
theorem comp_integratedLp_iff {P : CovariantRepresentation α H} {Q : CovariantRepresentation α K}
    (hP : P.coefficient.IsNondegenerate) {T : H →L[ℂ] K} :
    (∀ u, T ∘L P.integratedLp μ u = Q.integratedLp μ u ∘L T) ↔
      (∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T) ∧
        ∀ g, T ∘L P.group g = Q.group g ∘L T :=
  ⟨fun h => (comp_integratedOperator_iff μ hP).1 fun f => by
    simpa only [integratedLp_toL1_eq_integratedOperator] using h (f.integrable.toL1 f),
    fun h => comp_integratedLp μ h.1 h.2⟩

/-- A nondegenerate covariant pair is uniquely determined by its Bochner `L¹` integrated form. -/
theorem ext_integratedLp {P Q : CovariantRepresentation α H} (hP : P.coefficient.IsNondegenerate)
    (h : P.integratedLp μ = Q.integratedLp μ) : P = Q :=
  ext_integratedOperator μ hP fun f => by
    simpa only [integratedLp_toL1_eq_integratedOperator] using
      congrArg (fun L => L (f.integrable.toL1 f)) h

/-- For a nondegenerate pair, the commutant of `integratedLp` equals the joint commutant of
`P.coefficient` and `P.group`. -/
theorem centralizer_range_integratedLp {P : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate) :
    Set.centralizer (Set.range (P.integratedLp μ)) =
      Set.centralizer (Set.range P.coefficient ∪ Set.range P.group) := by
  ext T
  have h := comp_integratedLp_iff μ hP (Q := P) (T := T)
  simp only [← ContinuousLinearMap.mul_def] at h
  simp only [Set.mem_centralizer_iff, Set.mem_union, or_imp, forall_and, Set.forall_mem_range]
  simpa only [eq_comm (a := T * _)] using h

end Nondegenerate

end Intertwiner

/-! ### Functoriality, Hilbert direct sums, and scalar comparison -/

section Functoriality

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Pulling back a covariant pair along `φ : Hom α β` commutes with `integratedLp`. -/
theorem integratedLp_comap (Q : CovariantRepresentation β H) (φ : Hom α β) (μ : Measure G)
    [μ.InnerRegularCompactLTTop] (u : Lp A 1 μ) :
    (Q.comap φ).integratedLp μ u = Q.integratedLp μ (φ.mapLp μ 1 u) := by
  ext v
  rw [integratedLp_apply, integratedLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [φ.coeFn_mapLp u] with g hg
  simp [hg]

section HilbertSum

variable {ι : Type*} {K : ι → Type*} [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (K i)] [∀ i, CompleteSpace (K i)]
  (Q : ∀ i, CovariantRepresentation α (K i)) (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- `integratedLp` commutes with evaluation in every summand of a Hilbert direct sum. -/
@[simp]
theorem integratedLp_hilbertSum_apply (u : Lp A 1 μ) (x : lp K 2) (i : ι) :
    (hilbertSum Q).integratedLp μ u x i = (Q i).integratedLp μ u (x i) := by
  let ev := lp.evalCLM ℂ K 2 i
  calc
    (hilbertSum Q).integratedLp μ u x i = ev ((hilbertSum Q).integratedLp μ u x) :=
      (lp.evalCLM_apply i _).symm
    _ = ev (∫ g, (hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x) ∂μ) :=
      congrArg ev ((hilbertSum Q).integratedLp_apply μ u x)
    _ = ∫ g, ev ((hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x)) ∂μ :=
      (ev.integral_comp_comm
        ((hilbertSum Q).integrable_integrand_of_integrable μ (L1.integrable_coeFn u) x)).symm
    _ = ∫ g, (Q i).coefficient (u g) ((Q i).group g (x i)) ∂μ :=
      integral_congr_ae (.of_forall fun g => by simp [ev])
    _ = (Q i).integratedLp μ u (x i) := ((Q i).integratedLp_apply μ u (x i)).symm

/-- `integratedLp` of a Hilbert direct sum is the direct sum of the component integrated maps. -/
theorem integratedLp_hilbertSum (u : Lp A 1 μ) :
    (hilbertSum Q).integratedLp μ u =
      lp.mapCLM 2 (fun i => (Q i).integratedLp μ u) (norm_nonneg u)
        (fun i => (Q i).norm_integratedLp_apply_le μ u) := by
  ext x i; simp

end HilbertSum

section ScalarComparison

variable (P : CovariantRepresentation α H) (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- Transport the measurable space structure of `G` to `Additive G` as a reducible local instance
so that `(μ : Measure (Additive G))` and `Lp ℂ 1 μ` remain definitionally compatible. -/
@[reducible] local instance : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
local instance : R1Space (Additive G) := ‹R1Space G›
local instance : BorelSpace (Additive G) := ‹BorelSpace G›
local instance : Measure.InnerRegularCompactLTTop (α := Additive G) μ :=
  inferInstanceAs (Measure.InnerRegularCompactLTTop (α := G) μ)

/-- On scalar `L¹` multiples `g ↦ φ g • a`, `integratedLp` factors as `π(a)` composed with
`ContRepresentation.integratedOperatorL1`. -/
theorem integratedLp_toSpanSingleton_compLp (φ : Lp ℂ 1 μ) (a : A) :
    P.integratedLp μ ((ContinuousLinearMap.toSpanSingleton ℂ a).compLp φ) =
      P.coefficient a *
        (P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
          (G := Additive G) (fun v => P.continuous_orbit v)
          (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
          (μ : Measure (Additive G))
          (φ : Lp ℂ 1 (μ : Measure (Additive G))) := by
  ext v
  have hi : Integrable (fun g => φ g • P.group g v) μ := by
    refine ((L1.integrable_coeFn φ).norm.mul_const ‖v‖).mono'
      ((L1.integrable_coeFn φ).aefinStronglyMeasurable.aestronglyMeasurable_smul
        (P.continuous_orbit v)) (.of_forall fun g => ?_)
    rw [norm_smul, P.isUnitary.norm_map]
  calc
    P.integratedLp μ ((ContinuousLinearMap.toSpanSingleton ℂ a).compLp φ) v
        = P.coefficient a (∫ g, φ g • P.group g v ∂μ) := by
          rw [integratedLp_apply, ← (P.coefficient a).integral_comp_comm hi]
          refine integral_congr_ae ?_
          filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ a).coeFn_compLp φ] with g hg
          simp [hg, map_smul]
    _ = _ := congrArg (P.coefficient a)
          (ContRepresentation.integratedOperatorL1_apply (G := Additive G)
            (μ := (μ : Measure (Additive G))) _ v).symm

end ScalarComparison

end Functoriality

/-! ### Equivariance under twisted left translation and multiplicativity on `L¹` -/

section TranslateAndConvolution

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- `integratedLp` intertwines twisted left translation with the unitary group representation. -/
@[simp]
theorem integratedLp_translateLp [MeasurableMul G] [μ.IsMulLeftInvariant]
    (r : G) (u : Lp A 1 μ) :
    P.integratedLp μ (α.translateLp μ 1 r u) = P.group r * P.integratedLp μ u := by
  ext v
  rw [mul_apply_eq_comp, integratedLp_apply, integratedLp_apply,
    ← (P.group r).integral_comp_comm
      (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v),
    ← integral_mul_left_eq_self _ r]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ r).quasiMeasurePreserving.ae
    (α.coeFn_translateLp r u)] with s hs
  simp [hs, P.covariance, map_mul]

/-- Along `ConvolutionAlgebra.toL1FromCompletion`, `integratedLp` agrees with
`integratedOperatorL1`. -/
@[simp]
theorem integratedLp_toL1FromCompletion [IsTopologicalGroup G] [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedLp μ (ConvolutionAlgebra.toL1FromCompletion α μ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.integratedLp μ).continuous.comp (ConvolutionAlgebra.toL1FromCompletion α μ).continuous)
      (P.continuous_integratedOperatorL1 μ)
  | ih f => simp

/-- **Multiplicativity of `integratedLp` under twisted `L¹` convolution**:
`(π ⋊ U)(u ⋆ v) = (π ⋊ U)(u) * (π ⋊ U)(v)`. -/
@[simp]
theorem integratedLp_convolutionLp [IsTopologicalGroup G] [IsLocallyFiniteMeasure μ]
    [μ.IsMulLeftInvariant] (u v : Lp A 1 μ) :
    P.integratedLp μ (α.convolutionLp μ 1 ENNReal.one_ne_top u v) =
      P.integratedLp μ u * P.integratedLp μ v := by
  ext ξ
  let L : Lp A 1 μ →L[ℂ] H := (ContinuousLinearMap.apply ℂ H ξ).comp (P.integratedLp μ)
  have hL (w : Lp A 1 μ) : L w = P.integratedLp μ w ξ := rfl
  have hcomm := L.integral_comp_comm
    (α.integrable_mul_translateLp μ ENNReal.one_ne_top (L1.integrable_coeFn u) v)
  rw [← hL, α.convolutionLp_apply, ← hcomm]
  simp only [hL, P.integratedLp_mul_compLp, P.integratedLp_translateLp, mul_apply_eq_comp]
  exact P.integratedLp_apply μ u (P.integratedLp μ v ξ)

/-- Under `ConvolutionAlgebra.completionEquivLp`, `integratedLp` agrees with
`integratedOperatorL1`. -/
@[simp]
theorem integratedLp_completionEquivLp [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G]
    [μ.Regular] [μ.IsMulLeftInvariant] (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedLp μ (ConvolutionAlgebra.completionEquivLp α μ x) =
      P.integratedOperatorL1 μ x := by
  rw [ConvolutionAlgebra.completionEquivLp_apply, integratedLp_toL1FromCompletion]

/-- Composing `integratedOperatorL1` with `(completionEquivLp α μ).symm` gives `integratedLp`. -/
@[simp]
theorem integratedOperatorL1_completionEquivLp_symm [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [μ.Regular] [μ.IsMulLeftInvariant] (u : Lp A 1 μ) :
    P.integratedOperatorL1 μ ((ConvolutionAlgebra.completionEquivLp α μ).symm u) =
      P.integratedLp μ u := by
  rw [← P.integratedLp_completionEquivLp μ, LinearIsometryEquiv.apply_symm_apply]

/-- For the trivial action of `G` on `ℂ` acting by scalars on any complex Hilbert space `H`,
`integratedLp` of the regular representation on `L²(G, H)` is `MeasureTheory.Lp.convolutionL`. -/
theorem integratedLp_regular_trivial [IsTopologicalGroup G] [IsLocallyFiniteMeasure μ]
    [μ.IsMulLeftInvariant] :
    (regular (CStarAction.trivial (G := G) (A := ℂ))
        (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom μ).integratedLp μ =
      Lp.convolutionL μ 2 ENNReal.ofNat_ne_top := by
  let ρ : ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  ext f ξ : 2
  rw [integratedLp_apply, Lp.convolutionL_apply]
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

end TranslateAndConvolution

/-! ### Star preservation on Bochner `L¹` -/

section Star

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.Regular]

/-- For a regular left-invariant measure on a locally compact group, `integratedLp` sends
`twistedInvolutionLp` to the operator adjoint. -/
@[simp]
theorem integratedLp_twistedInvolutionLp (u : Lp A 1 μ) :
    P.integratedLp μ (α.twistedInvolutionLp μ u) = star (P.integratedLp μ u) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · have hzero (w : Lp A 1 (0 : Measure G)) : P.integratedLp 0 w = 0 := by
      ext v; simp [integratedLp_apply]
    simp [hzero]
  · have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular
    have : μ.IsHaarMeasure := {}
    rw [← P.integratedOperatorL1_completionEquivLp_symm μ (α.twistedInvolutionLp μ u),
      ConvolutionAlgebra.completionEquivLp_symm_twistedInvolutionLp, integratedOperatorL1_star,
      P.integratedOperatorL1_completionEquivLp_symm μ]

end Star

/-! ### Counting measure on discrete groups -/

section Discrete

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For counting measure on a discrete group, `integratedLp` acts on `v` by the unconditionally
convergent series `∑ g, π (u g) (U g v)`. -/
theorem hasSum_integratedLp_count_apply (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    HasSum (fun g => P.coefficient (u g) (P.group g v)) (P.integratedLp Measure.count u v) := by
  rw [integratedLp_apply]
  have hint := P.integrable_integrand_of_integrable Measure.count (L1.integrable_coeFn u) v
  unfold Measure.count at hint ⊢
  simpa only [integral_dirac] using hasSum_integral_measure hint

/-- Series formula for `integratedLp` with respect to counting measure on a discrete group. -/
theorem integratedLp_count_apply (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    P.integratedLp Measure.count u v = ∑' g, P.coefficient (u g) (P.group g v) :=
  (P.hasSum_integratedLp_count_apply u v).tsum_eq.symm

/-- For an `ℓ¹` family `f : G → A` on a discrete group, `g ↦ π (f g) (U g v)` sums unconditionally
to `integratedLp` of `(integrable_count_iff.2 hf).toL1 f`. -/
theorem hasSum_integratedLp_count_toL1 {f : G → A} (hf : Summable (‖f ·‖)) (v : H) :
    HasSum (fun g => P.coefficient (f g) (P.group g v))
      (P.integratedLp Measure.count ((integrable_count_iff.2 hf).toL1 f) v) := by
  have hcoe : ∀ g, ((integrable_count_iff.2 hf).toL1 f : G → A) g = f g :=
    Measure.ae_count_iff.1 (integrable_count_iff.2 hf).coeFn_toL1
  simpa only [hcoe] using P.hasSum_integratedLp_count_apply ((integrable_count_iff.2 hf).toL1 f) v

/-- For an `ℓ¹` family `f : G → A` on a discrete group, `integratedLp` acts by
`∑' g, π (f g) (U g v)`. -/
theorem integratedLp_count_toL1 {f : G → A} (hf : Summable (‖f ·‖)) (v : H) :
    P.integratedLp Measure.count ((integrable_count_iff.2 hf).toL1 f) v =
      ∑' g, P.coefficient (f g) (P.group g v) :=
  (P.hasSum_integratedLp_count_toL1 hf v).tsum_eq.symm

/-- For an `ℓ¹` family `f : G → A` on a discrete group, the operator norm of `integratedLp` is
bounded by `∑' g, ‖f g‖`. -/
theorem norm_integratedLp_count_toL1_le {f : G → A} (hf : Summable (‖f ·‖)) :
    ‖P.integratedLp Measure.count ((integrable_count_iff.2 hf).toL1 f)‖ ≤ ∑' g, ‖f g‖ := by
  refine (P.norm_integratedLp_toL1_le Measure.count (integrable_count_iff.2 hf)).trans_eq ?_
  have hint := (integrable_count_iff.2 hf).norm
  unfold Measure.count at hint ⊢
  simpa only [integral_dirac] using integral_sum_measure hint

end Discrete

end TauCeti.CStarAction.CovariantRepresentation
