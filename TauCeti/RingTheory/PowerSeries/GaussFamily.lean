/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import TauCeti.RingTheory.Huber.Bounded
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.RingTheory.Huber.Normed
import TauCeti.Topology.Algebra.Nonarchimedean.Lattice
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# The Gauss topology of a family of radii

Let `R` be an ultrametric normed ring, `ρ : ι → ℝ` a family of positive radii, and `T` the
subring of power series that are restricted at every radius `ρ i`. Such subrings include the
series on an open disc, where the radii are those below the boundary, and the entire series,
where they are all positive radii. This file develops the topology on `T` given by the Gauss
norms at all the radii `ρ i` once, so that each of these algebras is a specialization.

The subring is described by a membership condition `hT`, and its uniformity by the hypothesis
that restriction to the closed discs of all radii is uniformly inducing (with purely topological
results requiring only that it is topologically inducing). Under these hypotheses,
convergence is convergence in each Gauss norm, and it may be tested at any family of radii that
dominates `ρ`. The resulting uniform ring is a nonarchimedean topological ring in which polynomial
truncations converge. When `ι` is nonempty, restriction is a uniform embedding whose image consists
of the families with the same formal coefficients at every radius. That image is closed, so the
algebra is Hausdorff when `ι` is nonempty and is complete when `R` is complete.

## Main definitions

* `TauCeti.PowerSeries.GaussFamily.restrict`, `TauCeti.PowerSeries.GaussFamily.restrictFamily` and
  `TauCeti.PowerSeries.GaussFamily.restrictSubfamily`: restriction of `T` to a single closed disc,
  to all the radii at once, and along a subfamily.
* `TauCeti.PowerSeries.GaussFamily.constHom`: inclusion of constant power series into `T`.
* `TauCeti.PowerSeries.GaussFamily.uniformSpace`: the uniformity induced by `restrictFamily`.
* `TauCeti.PowerSeries.GaussFamily.compatibleSubring`: the closed subring of compatible
  restricted series along a monotone family of positive radii, with ring and uniform equivalences
  `TauCeti.PowerSeries.GaussFamily.compatibleRingEquiv` and
  `TauCeti.PowerSeries.GaussFamily.compatibleUniformEquiv`.

## Main results

* `TauCeti.PowerSeries.GaussFamily.comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius` and
  `TauCeti.PowerSeries.GaussFamily.comap_restrictSubfamily_eq`: any cofinal subfamily of radii
  induces the same uniformity, so the Gauss uniformity is independent of the chosen cofinal
  family and countably generated whenever a countable cofinal family exists
  (`TauCeti.PowerSeries.GaussFamily.isCountablyGenerated_uniformity`).
* `TauCeti.PowerSeries.GaussFamily.tendsto_iff_of_cofinal_radius`: convergence can be tested at
  any dominating family of radii.
* `TauCeti.PowerSeries.GaussFamily.denseRange_polynomialHom`: polynomials are dense.
* `TauCeti.PowerSeries.GaussFamily.range_restrictFamily` and
  `TauCeti.PowerSeries.GaussFamily.range_restrictSubfamily_eq_compatibleSubring`: the images of
  the full and monotone-cofinal restriction embeddings.
* `TauCeti.PowerSeries.GaussFamily.uniformContinuous_of_norm_le` and
  `TauCeti.PowerSeries.GaussFamily.uniformContinuous_of_norm_restrict_le`: uniform continuity of
  additive maps bounded by a radius Gauss norm.
* `TauCeti.PowerSeries.GaussFamily.isTopologicalRing`,
  `TauCeti.PowerSeries.GaussFamily.nonarchimedeanRing`,
  `TauCeti.PowerSeries.GaussFamily.continuousSMul`, `TauCeti.PowerSeries.GaussFamily.t2Space`, and
  `TauCeti.PowerSeries.GaussFamily.completeSpace`: the nonarchimedean ring structure, scalar-action
  continuity, separation (for nonempty `ι`), and completeness of the Gauss topology.
* `TauCeti.PowerSeries.GaussFamily.norm_restrict`: the norm of a restriction is the Gauss norm at
  that radius.
* `TauCeti.PowerSeries.GaussFamily.hasProd_iff`,
  `TauCeti.PowerSeries.GaussFamily.multipliable_iff`,
  `TauCeti.PowerSeries.GaussFamily.restrict_tprod`,
  `TauCeti.PowerSeries.GaussFamily.hasProd_constantCoeff`,
  `TauCeti.PowerSeries.GaussFamily.constantCoeff_tprod` and
  `TauCeti.PowerSeries.GaussFamily.tendsto_gaussNorm_sub_prod`: convergence, constant-coefficient
  preservation, and Gauss-norm convergence of partial products for unconditional infinite products
  over commutative coefficients.
* `TauCeti.PowerSeries.GaussFamily.not_exists_mem_nhds_zero_forall_exists_constHom_mul_mem`,
  `TauCeti.PowerSeries.GaussFamily.not_isBounded_of_mem_nhds_zero`,
  `TauCeti.PowerSeries.GaussFamily.not_exists_ringSeminorm_toTopologicalSpace_eq`,
  `TauCeti.PowerSeries.GaussFamily.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le`,
  `TauCeti.PowerSeries.GaussFamily.not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le`,
  and `TauCeti.PowerSeries.GaussFamily.not_isNormableSpace`: when `ι` is nonempty and the radii
  have no maximum, `T` admits no bounded zero-neighborhood and no compatible ring seminorm,
  scalar-bounded additive group seminorm, or normable space structure over a nontrivial ultrametric
  normed ring with a unit of norm `< 1` (in particular, over a nontrivially normed ultrametric
  field).
-/

public section

open Filter PowerSeries
open scoped Topology Uniformity Pointwise

namespace TauCeti.PowerSeries.GaussFamily

section Family

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {ι : Type*} {ρ : ι → ℝ}
  {T : Subring R⟦X⟧} (hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i))

/-- Restriction of a series in `T` to the closed disc of the radius `ρ i`. -/
noncomputable def restrict (i : ι) : T →+* IsRestricted.subring (R := R) (ρ i) :=
  Subring.inclusion fun f hf ↦ (hT f).mp hf i

/-- Restriction leaves the underlying formal series unchanged. -/
@[simp]
theorem coe_restrict (i : ι) (f : T) : (restrict hT i f : R⟦X⟧) = f :=
  Subring.coe_inclusion _ f

/-- The norm of the restriction of a series in `T` to `ρ i` is its Gauss norm at `ρ i`. -/
theorem norm_restrict (i : ι) [Fact (0 < ρ i)] (f : T) :
    ‖restrict hT i f‖ = (f : R⟦X⟧).gaussNorm norm (ρ i) := by
  rw [TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict]

omit [IsUltrametricDist R] in
/-- Inclusion of constant power series into `T`. -/
noncomputable def constHom : R →+* T :=
  (PowerSeries.C (R := R)).codRestrict T fun a ↦ (hT _).mpr fun i ↦ isRestricted_C (ρ i) a

omit [IsUltrametricDist R] in
/-- Constant inclusion has underlying formal series `PowerSeries.C a`. -/
@[simp]
theorem coe_constHom (a : R) : (constHom hT a : R⟦X⟧) = PowerSeries.C a :=
  (rfl)

/-- Restriction of a series in `T` to the closed discs of all the radii at once. -/
noncomputable def restrictFamily : T →+* ∀ i, IsRestricted.subring (R := R) (ρ i) :=
  RingHom.pi (restrict hT)

/-- Each component of the family of restrictions is the restriction to that radius. -/
@[simp]
theorem restrictFamily_apply (f : T) (i : ι) : restrictFamily hT f i = restrict hT i f :=
  (rfl)

/-- Restriction of a series in `T` along a subfamily `σ : κ → ι` of radii. -/
noncomputable def restrictSubfamily {κ : Type*} (σ : κ → ι) :
    T →+* ∀ k, IsRestricted.subring (R := R) (ρ (σ k)) :=
  RingHom.pi fun k ↦ restrict hT (σ k)

/-- Each component of the subfamily restriction is the restriction to that radius. -/
@[simp]
theorem restrictSubfamily_apply {κ : Type*} (σ : κ → ι) (f : T) (k : κ) :
    restrictSubfamily hT σ f k = restrict hT (σ k) f :=
  (rfl)

private theorem restrictSubfamily_eq_restrictFamily {κ : Type*} {σ : κ → ι}
    (hT' : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ k, f.IsRestricted (ρ (σ k))) :
    restrictSubfamily hT σ = restrictFamily hT' :=
  RingHom.ext fun f ↦ funext fun k ↦ Subtype.ext <| by
    simp only [restrictSubfamily_apply, restrictFamily_apply, coe_restrict]

/-- Any nonempty subfamily of closed-disc restrictions determines a series in `T`. -/
theorem restrictSubfamily_injective {κ : Type*} [Nonempty κ] (σ : κ → ι) :
    Function.Injective (restrictSubfamily hT σ) := by
  intro f g h
  have hval := congrArg (fun x ↦ (x (Classical.arbitrary κ) : R⟦X⟧)) h
  simp only [restrictSubfamily_apply, coe_restrict] at hval
  exact Subtype.ext hval

/-- The family of closed-disc restrictions determines a series in `T`. -/
theorem restrictFamily_injective [Nonempty ι] : Function.Injective (restrictFamily hT) := by
  rw [← restrictSubfamily_eq_restrictFamily hT (σ := id) hT]
  exact restrictSubfamily_injective hT id

/-- The restriction image consists exactly of families with radius-independent coefficients. -/
theorem range_restrictFamily :
    Set.range (restrictFamily hT) =
      {g | ∀ i j : ι, ∀ n : ℕ, coeff n (g i : R⟦X⟧) = coeff n (g j : R⟦X⟧)} := by
  ext g
  refine ⟨?_, fun hg ↦ ?_⟩
  · rintro ⟨f, rfl⟩
    intro i j n
    simp only [restrictFamily_apply, coe_restrict]
  · rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨0, funext fun i ↦ (hι.false i).elim⟩
    let i₀ := Classical.arbitrary ι
    have heq (i) : (g i : R⟦X⟧) = (g i₀ : R⟦X⟧) := PowerSeries.ext (hg i i₀)
    refine ⟨⟨(g i₀ : R⟦X⟧), (hT _).mpr fun i ↦ ?_⟩, ?_⟩
    · rw [← heq i]
      exact (g i).property
    · funext i
      exact Subtype.ext (heq i).symm

omit [IsUltrametricDist R] in
include hT in
private theorem mem_iff_forall_isRestricted_subfamily {κ : Type*} {σ : κ → ι}
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) (f : R⟦X⟧) :
    f ∈ T ↔ ∀ k, f.IsRestricted (ρ (σ k)) :=
  (hT f).trans ⟨fun hf k ↦ hf (σ k), fun hf i ↦
    let ⟨k, hk⟩ := hσ i
    TauCeti.PowerSeries.isRestricted_of_abs_le (hf k) (abs_le_abs_of_nonneg (hρ i) hk)⟩

/-- Along a cofinal subfamily of nonnegative radii, the restriction image consists of families with
index-independent formal coefficients. -/
theorem range_restrictSubfamily {κ : Type*} {σ : κ → ι} (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    Set.range (restrictSubfamily hT σ) =
      {g | ∀ k l : κ, ∀ n : ℕ, coeff n (g k : R⟦X⟧) = coeff n (g l : R⟦X⟧)} := by
  rw [restrictSubfamily_eq_restrictFamily hT (mem_iff_forall_isRestricted_subfamily hT hρ hσ)]
  exact range_restrictFamily (mem_iff_forall_isRestricted_subfamily hT hρ hσ)

variable [∀ i, Fact (0 < ρ i)]

/-- The uniformity generated by the Gauss norms at all the radii `ρ i`. -/
@[instance_reducible]
noncomputable def uniformSpace : UniformSpace T :=
  UniformSpace.comap (restrictFamily hT)
    (inferInstanceAs (UniformSpace (∀ i, IsRestricted.subring (R := R) (ρ i))))

/-- The uniformity `uniformSpace hT` is induced by the family of closed-disc restrictions. -/
theorem isUniformInducing_restrictFamily_uniformSpace :
    @IsUniformInducing _ _ (uniformSpace hT) _ (restrictFamily hT) :=
  @IsUniformInducing.mk _ _ (uniformSpace hT) _ _ rfl

/-- Coefficient-compatible families form a closed subset of the product of closed-disc algebras. -/
theorem isClosed_range_restrictFamily : IsClosed (Set.range (restrictFamily hT)) := by
  rw [range_restrictFamily]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun n ↦ ?_
  have h (j : ι) : Continuous fun g : (∀ i, IsRestricted.subring (R := R) (ρ i)) ↦
      coeff n (g j : R⟦X⟧) :=
    (TauCeti.PowerSeries.uniformContinuous_coeff n).continuous.comp (continuous_apply j)
  exact isClosed_eq (h i) (h j)

omit [∀ i, Fact (0 < ρ i)] in
/-- Along a cofinal subfamily of positive radii dominating nonnegative radii `ρ`, the image of
`restrictSubfamily` is closed in the corresponding product of closed-disc algebras. -/
theorem isClosed_range_restrictSubfamily {κ : Type*} {σ : κ → ι} [∀ k, Fact (0 < ρ (σ k))]
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    IsClosed (Set.range (restrictSubfamily hT σ)) := by
  rw [restrictSubfamily_eq_restrictFamily hT (mem_iff_forall_isRestricted_subfamily hT hρ hσ)]
  exact isClosed_range_restrictFamily (mem_iff_forall_isRestricted_subfamily hT hρ hσ)

section Inducing

variable {hT} [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT))
include hu

/-- Restriction to the closed disc of each radius is uniformly continuous. -/
theorem uniformContinuous_restrict (i : ι) : UniformContinuous (restrict hT i) :=
  (Pi.uniformContinuous_proj _ i).comp hu.uniformContinuous

/-- Convergence in `T` is convergence in the Gauss norm at every radius `ρ i`. -/
theorem tendsto_iff {κ : Type*} {l : Filter κ} {f : κ → T} {g : T} :
    Tendsto f l (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict hT i (f j)) l (𝓝 (restrict hT i g)) := by
  rw [hu.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- Convergence can be tested at any family of radii `ρ (σ k)` that dominates every radius of the
family. -/
theorem tendsto_iff_of_cofinal_radius {κ μ : Type*} {σ : κ → ι}
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) {F : Filter μ} {f : μ → T} {g : T} :
    Tendsto f F (𝓝 g) ↔
      ∀ k, Tendsto (fun j ↦ restrict hT (σ k) (f j)) F (𝓝 (restrict hT (σ k) g)) := by
  refine ⟨fun h k ↦ (tendsto_iff hu).mp h (σ k), fun h ↦ (tendsto_iff hu).mpr fun i ↦ ?_⟩
  obtain ⟨k, hk⟩ := hσ i
  have hi : 0 ≤ ρ i := (Fact.out : 0 < ρ i).le
  let φ := TauCeti.PowerSeries.restrictedRadiusHom (R := R) hi hk
  have hc : Continuous φ := TauCeti.PowerSeries.continuous_restrictedRadiusHom hi hk
  have heq (a : T) : φ (restrict hT (σ k) a) = restrict hT i a := by
    apply Subtype.ext
    simp only [φ, TauCeti.PowerSeries.coe_restrictedRadiusHom, coe_restrict]
  simpa only [Function.comp_def, heq] using (hc.tendsto (restrict hT (σ k) g)).comp (h k)

/-- Restriction along any cofinal subfamily of radii is uniformly inducing. -/
theorem isUniformInducing_restrictSubfamily {κ : Type*} {σ : κ → ι}
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) : IsUniformInducing (restrictSubfamily hT σ) := by
  choose k hk using hσ
  let g : (∀ j, IsRestricted.subring (R := R) (ρ (σ j))) →
      (∀ i, IsRestricted.subring (R := R) (ρ i)) :=
    fun y i ↦ TauCeti.PowerSeries.restrictedRadiusHom (Fact.out : 0 < ρ i).le (hk i) (y (k i))
  have hf : UniformContinuous (restrictSubfamily hT σ) :=
    uniformContinuous_pi.mpr fun j ↦ uniformContinuous_restrict hu (σ j)
  have hg : UniformContinuous g := uniformContinuous_pi.mpr fun i ↦
    (uniformContinuous_of_continuousAt_zero
      (TauCeti.PowerSeries.restrictedRadiusHom (R := R) (Fact.out : 0 < ρ i).le (hk i))
      (TauCeti.PowerSeries.continuous_restrictedRadiusHom _ _).continuousAt).comp
      (Pi.uniformContinuous_proj _ (k i))
  have hcomp : g ∘ restrictSubfamily hT σ = restrictFamily hT := by
    funext a i
    exact Subtype.ext (by simp [g])
  exact IsUniformInducing.of_comp hf hg (hcomp ▸ hu)

/-- Along a nonempty cofinal subfamily of radii, closed-disc restrictions embed `T` uniformly into
their product. -/
theorem isUniformEmbedding_restrictSubfamily {κ : Type*} [Nonempty κ] {σ : κ → ι}
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) : IsUniformEmbedding (restrictSubfamily hT σ) :=
  ⟨isUniformInducing_restrictSubfamily hu hσ, restrictSubfamily_injective hT σ⟩

/-- Whenever a countable cofinal subfamily of radii exists, the Gauss uniformity on `T` is
countably generated. -/
theorem isCountablyGenerated_uniformity {κ : Type*} [Countable κ] {σ : κ → ι}
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) : (𝓤 T).IsCountablyGenerated := by
  rw [← (isUniformInducing_restrictSubfamily hu hσ).comap_uniformity]
  exact Filter.comap.isCountablyGenerated _ _

/-- A map into `T` is continuous exactly when each restriction is continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → T} :
    Continuous f ↔ ∀ i, Continuous fun x ↦ restrict hT i (f x) := by
  rw [hu.isInducing.continuous_iff, continuous_pi_iff]
  rfl

/-- A map into `T` is uniformly continuous exactly when each restriction is. -/
theorem uniformContinuous_iff {X : Type*} [UniformSpace X] {f : X → T} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x ↦ restrict hT i (f x) := by
  rw [hu.uniformContinuous_iff, uniformContinuous_pi]
  rfl

/-- The Gauss uniformity is compatible with addition. -/
theorem isUniformAddGroup : IsUniformAddGroup T :=
  hu.isUniformAddGroup (restrictFamily hT)

/-- An additive homomorphism out of `T` into a seminormed additive commutative group is uniformly
continuous when it is bounded by a multiple of some radius Gauss norm. -/
theorem uniformContinuous_of_norm_le {M F : Type*} [SeminormedAddCommGroup M]
    [FunLike F T M] [AddMonoidHomClass F T M] (φ : F) (i : ι) (C : ℝ)
    (hφ : ∀ f, ‖φ f‖ ≤ C * ‖restrict hT i f‖) : UniformContinuous φ := by
  have := isUniformAddGroup hu
  refine uniformContinuous_of_continuousAt_zero (AddMonoidHom.ofClass φ) ?_
  rw [ContinuousAt, map_zero]
  have h := (uniformContinuous_restrict hu i).continuous.tendsto 0
  refine squeeze_zero_norm (fun f ↦ hφ f) ?_
  simpa using h.norm.const_mul C

/-- An additive homomorphism between two Gauss-family subrings is uniformly continuous when each
target radius Gauss norm is bounded by a multiple of some source radius Gauss norm. -/
theorem uniformContinuous_of_norm_restrict_le {S : Type*} [NormedRing S] [IsUltrametricDist S]
    {κ : Type*} {σ : κ → ℝ} [∀ j, Fact (0 < σ j)]
    {U : Subring S⟦X⟧} {hU : ∀ g : S⟦X⟧, g ∈ U ↔ ∀ j, g.IsRestricted (σ j)}
    [UniformSpace U] (hv : IsUniformInducing (restrictFamily hU))
    {F : Type*} [FunLike F T U] [AddMonoidHomClass F T U] (φ : F)
    (hφ : ∀ j, ∃ (i : ι) (C : ℝ), ∀ f, ‖restrict hU j (φ f)‖ ≤ C * ‖restrict hT i f‖) :
    UniformContinuous φ :=
  (uniformContinuous_iff hv).mpr fun j ↦ by
    obtain ⟨i, C, hC⟩ := hφ j
    exact uniformContinuous_of_norm_le hu
      ((restrict hU j).toAddMonoidHom.comp (AddMonoidHom.ofClass φ)) i C hC

/-- The Gauss topology makes `T` a topological ring. -/
theorem isTopologicalRing : IsTopologicalRing T :=
  have := isUniformAddGroup hu
  { continuous_mul := (hu.isInducing.continuousMul (restrictFamily hT)).continuous_mul }

/-- The Gauss topology makes `T` a nonarchimedean ring, since open additive subgroups of the
product of closed-disc algebras pull back to open additive subgroups of `T`. -/
theorem nonarchimedeanRing : NonarchimedeanRing T :=
  have := isTopologicalRing hu
  have h : NonarchimedeanAddGroup T :=
    hu.isInducing.eq_induced.symm ▸ TauCeti.nonarchimedeanAddGroup_induced (restrictFamily hT)
  { is_nonarchimedean := h.is_nonarchimedean }

/-- Polynomial truncations converge in the Gauss norms at all the radii simultaneously, for any
inclusion `φ` of the polynomials into `T`. -/
theorem tendsto_polynomialHom_trunc (φ : Polynomial R →+* T) (hφ : ∀ p, (φ p : R⟦X⟧) = p)
    (f : T) : Tendsto (fun n ↦ φ ((f : R⟦X⟧).trunc n)) atTop (𝓝 f) := by
  refine (tendsto_iff hu).mpr fun i ↦ ?_
  convert TauCeti.PowerSeries.tendsto_trunc_atTop (restrict hT i f) using 1
  · ext n : 1
    apply Subtype.ext
    simp only [coe_restrict, hφ]

/-- Polynomials are dense for the Gauss topology of the radii `ρ i`. -/
theorem denseRange_polynomialHom (φ : Polynomial R →+* T) (hφ : ∀ p, (φ p : R⟦X⟧) = p) :
    DenseRange φ :=
  fun f ↦ mem_closure_of_tendsto (tendsto_polynomialHom_trunc hu φ hφ f)
    (.of_forall fun _ ↦ Set.mem_range_self _)

/-- The Gauss topology is complete over complete coefficients. -/
theorem completeSpace [CompleteSpace R] : CompleteSpace T :=
  hu.completeSpace (isClosed_range_restrictFamily hT).isComplete

variable [Nonempty ι]

/-- Closed-disc restrictions embed `T` uniformly into their product. -/
theorem isUniformEmbedding_restrictFamily : IsUniformEmbedding (restrictFamily hT) :=
  ⟨hu, restrictFamily_injective hT⟩

/-- The Gauss topology of a nonempty family of radii is Hausdorff. -/
theorem t2Space : T2Space T :=
  (isUniformEmbedding_restrictFamily hu).isEmbedding.t2Space

/-- Each coefficient is uniformly continuous for the Gauss uniformity. -/
theorem uniformContinuous_coeff (n : ℕ) : UniformContinuous fun f : T ↦ coeff n (f : R⟦X⟧) := by
  have h := TauCeti.PowerSeries.uniformContinuous_coeff (R := R) (c := ρ (Classical.arbitrary ι)) n
  exact h.comp (uniformContinuous_restrict hu (Classical.arbitrary ι))

end Inducing

section TopologicalInducing

variable {hT} [t : TopologicalSpace T] (ht : Topology.IsInducing (restrictFamily hT))
include ht

/-- Constant inclusion `constHom` is continuous for the Gauss topology on `T`. -/
theorem continuous_constHom : Continuous (constHom hT) := by
  rw [ht.continuous_iff, continuous_pi_iff]
  intro i
  simp only [Function.comp_def, restrictFamily_apply]
  let ψ : R →+ IsRestricted.subring (R := R) (ρ i) :=
    ((restrict hT i).comp (constHom hT)).toAddMonoidHom
  refine continuous_of_continuousAt_zero ψ (Metric.continuousAt_iff.mpr fun ε hε ↦ ⟨ε, hε, ?_⟩)
  intro c hc
  have hψc : ψ c = ⟨PowerSeries.C c, isRestricted_C (ρ i) c⟩ := Subtype.ext (by simp [ψ])
  simpa [dist_zero_right, hψc, TauCeti.PowerSeries.norm_C] using hc

/-- Coefficientwise scalar multiplication is continuous for the Gauss topology on `T`. -/
theorem continuousSMul {S : Type*} [Semiring S] [TopologicalSpace S] [Module S R]
    [IsScalarTower S R R] [ContinuousSMul S R] [SMul S T]
    (hsmul : ∀ (s : S) (f : T), ((s • f : T) : R⟦X⟧) = s • (f : R⟦X⟧)) :
    ContinuousSMul S T := by
  have : ContinuousMul T := ht.continuousMul (restrictFamily hT)
  refine ⟨?_⟩
  have heq : (fun p : S × T ↦ p.1 • p.2) = fun p ↦ constHom hT (p.1 • (1 : R)) * p.2 := by
    ext ⟨s, f⟩ : 1
    apply Subtype.ext
    ext n
    rw [hsmul, PowerSeries.coeff_smul, Subring.coe_mul, coe_constHom, PowerSeries.coeff_C_mul,
      smul_mul_assoc, one_mul]
  rw [heq]
  exact ((continuous_constHom ht).comp (continuous_fst.smul continuous_const)).mul continuous_snd

variable [Nonempty ι]

/-- When `ι` is nonempty, every zero-neighborhood for the Gauss topology contains a single
closed-disc Gauss ball. -/
theorem exists_norm_restrict_lt_imp_mem {U : Set T} (hU : U ∈ 𝓝 0) :
    ∃ i₀ : ι, ∃ δ > 0, ∀ f : T, ‖restrict hT i₀ f‖ < δ → f ∈ U := by
  rw [ht.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨s, u, hu, hsuV⟩ := hV
  choose ε hεpos hεu using fun i ↦ Metric.mem_nhds_iff.mp (hu i)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨Classical.arbitrary ι, 1, one_pos, fun f _ ↦ hVU (hsuV ?_)⟩
    simp
  · obtain ⟨i₀, _, hi₀max⟩ := s.exists_max_image ρ hs
    let δ : ℝ := s.inf' hs ε
    have hδpos : 0 < δ := (Finset.lt_inf'_iff hs).mpr fun i _ ↦ hεpos i
    refine ⟨i₀, δ, hδpos, fun f hf ↦ hVU (hsuV fun i hi ↦ hεu i ?_)⟩
    rw [Metric.mem_ball, Pi.zero_apply, dist_zero_right, restrictFamily_apply]
    have hle : ‖restrict hT i f‖ ≤ ‖restrict hT i₀ f‖ := by
      rw [TauCeti.PowerSeries.norm_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm,
        coe_restrict, coe_restrict]
      exact TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le norm_nonneg (Fact.out : 0 < ρ i).le
        (hi₀max i hi) (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted ((hT _).mp f.property i₀))
    exact (hle.trans_lt hf).trans_le (Finset.inf'_le ε hi)

/-- **No zero-neighborhood is absorbed under constant multiplication when `ι` is nonempty and the
radii have no maximum.** Over a nontrivial ultrametric normed ring with a unit `u` of norm `< 1`, if
`ι` is nonempty and every radius `ρ i` is strictly dominated by another radius `ρ j`, then no
zero-neighborhood `U` in `T` satisfies that every zero-neighborhood `V` in `T` absorbs `U` under
left multiplication by a zero-neighborhood of constants in `R`. -/
theorem not_exists_mem_nhds_zero_forall_exists_constHom_mul_mem [Nontrivial R]
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ U ∈ 𝓝 (0 : T), ∀ V ∈ 𝓝 (0 : T), ∃ W ∈ 𝓝 (0 : R),
      ∀ c ∈ W, ∀ f ∈ U, constHom hT c * f ∈ V := by
  rintro ⟨U, hU, habs⟩
  obtain ⟨u, hu1⟩ := hu_unit
  obtain ⟨i₀, δ, hδ, hball⟩ := exists_norm_restrict_lt_imp_mem ht hU
  obtain ⟨i₁, hi₀₁⟩ := hmax i₀
  have ⟨hr0, hr1⟩ : 0 < ρ i₀ ∧ 0 < ρ i₁ := ⟨Fact.out, Fact.out⟩
  have hcont_i₁ : Continuous (restrict hT i₁) := by
    simpa only [Function.comp_def, restrictFamily_apply] using
      (continuous_apply i₁).comp ht.continuous
  obtain ⟨W, hW, hWUV⟩ := habs {f : T | ‖restrict hT i₁ f‖ < 1} <|
    (hcont_i₁.tendsto 0).norm
      (gt_mem_nhds (by simp : ‖restrict hT i₁ (0 : T)‖ < 1))
  obtain ⟨q, hq⟩ := (((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu1).comp
    (tendsto_add_atTop_nat 1)).eventually hW).exists
  let M : ℝ := ‖((u⁻¹ : Rˣ) : R)‖
  have hM : 0 < M := Units.norm_pos u⁻¹
  let B : ℝ := δ / (2 * (M + 1))
  have hB : 0 < B := by positivity
  have hBM : B * M < δ := calc
    B * M < B * (M + 1) := mul_lt_mul_of_pos_left (lt_add_one M) hB
    _ = δ / 2 := by dsimp [B]; field_simp
    _ < δ := half_lt_self hδ
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (M ^ (q + 1) / B) ((one_lt_div hr0).mpr hi₀₁)
  obtain ⟨z, hz_gt, hz_lt⟩ := u.exists_lt_norm_zpow_lt hu1 (by positivity : 0 ≤ B / ρ i₀ ^ m)
    (by rw [div_mul_eq_mul_div]; exact div_lt_div_of_pos_right hBM (pow_pos hr0 m))
  let a : R := ((u ^ z : Rˣ) : R)
  let f : T := ⟨PowerSeries.monomial m a,
    (hT _).mpr fun i ↦ PowerSeries.isRestricted_monomial (ρ i) m a⟩
  have hfU : f ∈ U := hball f <| by
    have h : restrict hT i₀ f = ⟨_, isRestricted_monomial (ρ i₀) m a⟩ := Subtype.ext (by simp [f])
    simpa only [h, TauCeti.PowerSeries.norm_monomial] using (lt_div_iff₀ (pow_pos hr0 m)).mp hz_lt
  have hprod : ‖(u : R) ^ (q + 1) * a‖ * ρ i₁ ^ m < 1 := by
    have hlt : ‖restrict hT i₁ (constHom hT ((u : R) ^ (q + 1)) * f)‖ < 1 := hWUV _ hq f hfU
    have h : restrict hT i₁ (constHom hT ((u : R) ^ (q + 1)) * f) =
        ⟨PowerSeries.monomial m ((u : R) ^ (q + 1) * a),
          PowerSeries.isRestricted_monomial (ρ i₁) m _⟩ := Subtype.ext <| by
      simp only [coe_restrict, Subring.coe_mul, coe_constHom, f,
        PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc, ← map_mul]
    rwa [h, TauCeti.PowerSeries.norm_monomial] at hlt
  have ha_gt : B < ‖a‖ * ρ i₀ ^ m := (div_lt_iff₀ (pow_pos hr0 m)).mp hz_gt
  rw [div_pow, div_lt_div_iff₀ hB (pow_pos hr0 m)] at hm
  have h1 : M ^ (q + 1) < ‖a‖ * ρ i₁ ^ m :=
    lt_of_mul_lt_mul_right (a := ρ i₀ ^ m)
      (hm.trans ((mul_lt_mul_of_pos_left ha_gt (pow_pos hr1 m)).trans_eq (by ring)))
      (pow_nonneg hr0.le m)
  have h2 : ‖a‖ * ρ i₁ ^ m ≤ M ^ (q + 1) * (‖(u : R) ^ (q + 1) * a‖ * ρ i₁ ^ m) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (u.norm_le_norm_inv_pow_mul_norm_pow_mul (q + 1) a) (pow_nonneg hr1.le m)
  exact (h1.trans_le h2).not_gt (mul_lt_of_lt_one_right (pow_pos hM (q + 1)) hprod)

/-- When `ι` is nonempty and the radii have no maximum, no zero-neighborhood in `T` is bounded in
the sense of `TauCeti.Huber.IsBounded` over a nontrivial ultrametric normed ring with a unit of
norm `< 1`. -/
theorem not_isBounded_of_mem_nhds_zero [Nontrivial R] (hmax : ∀ i, ∃ j, ρ i < ρ j)
    (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1) {U : Set T} (hU : U ∈ 𝓝 (0 : T)) :
    ¬ TauCeti.Huber.IsBounded U := by
  rw [TauCeti.Huber.isBounded_iff]
  intro hb
  refine not_exists_mem_nhds_zero_forall_exists_constHom_mul_mem ht hmax hu_unit
    ⟨U, hU, fun V hV ↦ ?_⟩
  obtain ⟨W, hW, hWU⟩ := hb V hV
  refine ⟨constHom hT ⁻¹' W, ?_, fun c hc f hf ↦ hWU (Set.mul_mem_mul hc hf)⟩
  exact (continuous_constHom ht).continuousAt.preimage_mem_nhds (by rwa [map_zero])

/-- **No single ring seminorm represents the Gauss topology when `ι` is nonempty and the radii have
no maximum.** Over a nontrivial ultrametric normed ring with a unit `u` of norm `< 1` (in
particular, over any nontrivially normed ultrametric field), if `ι` is nonempty and every radius
`ρ i` is strictly dominated by another radius `ρ j`, then no ring seminorm on `T` induces its Gauss
topology. -/
theorem not_exists_ringSeminorm_toTopologicalSpace_eq [Nontrivial R]
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ p : RingSeminorm T,
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace = t := by
  rintro ⟨p, htop⟩
  exact not_isBounded_of_mem_nhds_zero ht hmax hu_unit
    (htop ▸ @Metric.closedBall_mem_nhds T p.toSeminormedRing.toPseudoMetricSpace 0 1 one_pos)
    (htop ▸ @TauCeti.Huber.isBounded_closedBall_zero T p.toSeminormedRing 1)

/-- **No scalar-bounded group seminorm represents the Gauss topology when `ι` is nonempty and the
radii have no maximum.** Over a nontrivial ultrametric normed ring with a unit `u` of norm `< 1`, if
`ι` is nonempty and every radius `ρ i` is strictly dominated by another radius `ρ j`, then for any
constant inclusion `φ : R → T`, no additive group seminorm `p` on `T` in which left multiplication
by `φ c` is bounded by `C * ‖c‖` induces the Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le [Nontrivial R]
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1)
    {φ : R → T} (hφ : ∀ c, (φ c : R⟦X⟧) = PowerSeries.C c) :
    ¬ ∃ (p : AddGroupSeminorm T) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace = t ∧
      ∀ (c : R) (f : T), p (φ c * f) ≤ C * ‖c‖ * p f := by
  rintro ⟨p, C, htop, hsmul⟩
  have hbasis : (𝓝 (0 : T)).HasBasis (0 < ·) fun r ↦ {f : T | p f < r} :=
    htop ▸ @NormedAddGroup.nhds_zero_basis_norm_lt T p.toSeminormedAddGroup
  refine not_exists_mem_nhds_zero_forall_exists_constHom_mul_mem ht hmax hu_unit
    ⟨{f : T | p f < 1}, hbasis.mem_of_mem one_pos, fun V hV ↦ ?_⟩
  obtain ⟨ε, hε, hεV⟩ := hbasis.mem_iff.mp hV
  have hC1 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  refine ⟨Metric.ball (0 : R) (ε / max C 1), Metric.ball_mem_nhds 0 (div_pos hε hC1),
    fun c hc f hf ↦ hεV ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hc
  have hφc : constHom hT c = φ c := Subtype.ext ((coe_constHom hT c).trans (hφ c).symm)
  rw [Set.mem_ofPred_eq, hφc]
  calc p (φ c * f) ≤ C * ‖c‖ * p f := hsmul c f
    _ ≤ max C 1 * ‖c‖ * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg c))
        (le_of_lt hf) (apply_nonneg p f) (by positivity)
    _ < ε := by simpa using (lt_div_iff₀' hC1).mp hc

/-- **No scalar-bounded group seminorm represents the Gauss topology when `ι` is nonempty and the
radii have no maximum.** Over a nontrivial ultrametric normed ring `R` with a unit `u` of norm
`< 1`, if `ι` is nonempty and every radius `ρ i` is strictly dominated by another radius `ρ j`, then
no additive group seminorm on `T` in which scalar multiplication is bounded by `C * ‖c‖` induces the
Gauss topology for any coefficientwise `R`-action. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le [Nontrivial R] [SMul R T]
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1)
    (hsmul : ∀ (c : R) (f : T), ((c • f : T) : R⟦X⟧) = c • (f : R⟦X⟧)) :
    ¬ ∃ (p : AddGroupSeminorm T) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace = t ∧
      ∀ (c : R) (f : T), p (c • f) ≤ C * ‖c‖ * p f := by
  rintro ⟨p, C, htop, hle⟩
  refine not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le ht hmax hu_unit
    (coe_constHom hT) ⟨p, C, htop, fun c f ↦ ?_⟩
  have hmul : constHom hT c * f = c • f := Subtype.ext <| by
    rw [Subring.coe_mul, coe_constHom, hsmul, PowerSeries.smul_eq_C_mul]
  simpa only [hmul] using hle c f

end TopologicalInducing

/-- Any cofinal subfamily of radii induces the full Gauss uniformity `uniformSpace hT`. -/
theorem comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius {κ : Type*} {σ : κ → ι}
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    UniformSpace.comap (restrictSubfamily hT σ)
      (inferInstanceAs (UniformSpace (∀ k, IsRestricted.subring (R := R) (ρ (σ k))))) =
      uniformSpace hT := by
  let : UniformSpace T := uniformSpace hT
  exact (isUniformInducing_restrictSubfamily (isUniformInducing_restrictFamily_uniformSpace hT)
    hσ).comap_uniformSpace

/-- **Sequence independence of the Gauss uniformity.** Any two cofinal subfamilies of radii induce
the exact same uniformity on `T`. -/
theorem comap_restrictSubfamily_eq {κ₁ κ₂ : Type*} {σ₁ : κ₁ → ι} {σ₂ : κ₂ → ι}
    (hσ₁ : ∀ i, ∃ k, ρ i ≤ ρ (σ₁ k)) (hσ₂ : ∀ i, ∃ k, ρ i ≤ ρ (σ₂ k)) :
    UniformSpace.comap (restrictSubfamily hT σ₁)
      (inferInstanceAs (UniformSpace (∀ k, IsRestricted.subring (R := R) (ρ (σ₁ k))))) =
    UniformSpace.comap (restrictSubfamily hT σ₂)
      (inferInstanceAs (UniformSpace (∀ k, IsRestricted.subring (R := R) (ρ (σ₂ k))))) :=
  (comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius hT hσ₁).trans
    (comap_restrictSubfamily_eq_uniformSpace_of_cofinal_radius hT hσ₂).symm

end Family

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {ι : Type*} [Nonempty ι] {ρ : ι → ℝ} [∀ i, Fact (0 < ρ i)]
  {T : Subring K⟦X⟧} {hT : ∀ f : K⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
  [t : TopologicalSpace T] (ht : Topology.IsInducing (restrictFamily hT))
include ht

/-- Over a nontrivially normed ultrametric field, when `ι` is nonempty and the radii have no
maximum, no zero-neighborhood in `T` is bounded in the sense of `TauCeti.Huber.IsBounded`. -/
theorem not_isBounded_of_mem_nhds_zero_of_nontriviallyNormedField (hmax : ∀ i, ∃ j, ρ i < ρ j)
    {U : Set T} (hU : U ∈ 𝓝 (0 : T)) : ¬ TauCeti.Huber.IsBounded U :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_isBounded_of_mem_nhds_zero ht hmax ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩ hU

/-- Over a nontrivially normed ultrametric field, when `ι` is nonempty and the radii have no
maximum, no single ring seminorm induces the Gauss topology on `T`. -/
theorem not_exists_ringSeminorm_toTopologicalSpace_eq_of_nontriviallyNormedField
    (hmax : ∀ i, ∃ j, ρ i < ρ j) :
    ¬ ∃ p : RingSeminorm T,
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace = t :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_ringSeminorm_toTopologicalSpace_eq ht hmax ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

/-- Over a nontrivially normed ultrametric field, when `ι` is nonempty and the radii have no
maximum, for any constant inclusion `φ : K → T`, no additive group seminorm on `T` in which left
multiplication by `φ c` is bounded by `C * ‖c‖` induces the Gauss topology. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le_of_nontriviallyNormedField
    (hmax : ∀ i, ∃ j, ρ i < ρ j) {φ : K → T} (hφ : ∀ c, (φ c : K⟦X⟧) = PowerSeries.C c) :
    ¬ ∃ (p : AddGroupSeminorm T) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace = t ∧
      ∀ (c : K) (f : T), p (φ c * f) ≤ C * ‖c‖ * p f :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_mul_le ht hmax
    ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩ hφ

/-- Over a nontrivially normed ultrametric field `K`, when `ι` is nonempty and the radii have no
maximum, no additive group seminorm on `T` in which scalar multiplication is bounded by `C * ‖c‖`
induces the Gauss topology for any coefficientwise `K`-action. -/
theorem not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le_of_nontriviallyNormedField
    [SMul K T] (hmax : ∀ i, ∃ j, ρ i < ρ j)
    (hsmul : ∀ (c : K) (f : T), ((c • f : T) : K⟦X⟧) = c • (f : K⟦X⟧)) :
    ¬ ∃ (p : AddGroupSeminorm T) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace = t ∧
      ∀ (c : K) (f : T), p (c • f) ≤ C * ‖c‖ * p f :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le ht hmax
    ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩ hsmul

/-- Over a nontrivially normed ultrametric field `K`, when `ι` is nonempty and the radii have no
maximum, `T` with its Gauss topology is not normable as a `K`-vector space for any coefficientwise
`K`-module structure. -/
theorem not_isNormableSpace [Module K T] (hmax : ∀ i, ∃ j, ρ i < ρ j)
    (hsmul : ∀ (c : K) (f : T), ((c • f : T) : K⟦X⟧) = c • (f : K⟦X⟧)) :
    ¬ IsNormableSpace K T := by
  intro hn
  obtain ⟨p, hp⟩ := hn.withSeminorms'
  exact not_exists_addGroupSeminorm_toTopologicalSpace_eq_and_smul_le_of_nontriviallyNormedField
    ht hmax hsmul
    ⟨p.toAddGroupSeminorm, 1, ciInf_unique.symm.trans hp.topologicalSpace_eq_iInf.symm,
      fun c f ↦ by simpa only [AddGroupSeminorm.toFun_eq_coe, one_mul] using (p.smul' c f).le⟩

end NontriviallyNormedField

section Compatible

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

/-- The subring of **compatible restricted series** along a monotone family of positive radii
`r : κ → ℝ`: families `(g k)` of series restricted at `r k` intertwined by radius restriction
`restrictedRadiusHom` whenever `m ≤ n`. -/
noncomputable def compatibleSubring {κ : Type*} [Preorder κ] {r : κ → ℝ}
    [∀ k, Fact (0 < r k)] (hr : Monotone r) :
    Subring (∀ k, IsRestricted.subring (R := R) (r k)) where
  carrier := {g | ∀ ⦃m n : κ⦄ (h : m ≤ n),
    TauCeti.PowerSeries.restrictedRadiusHom (Fact.out : 0 < r m).le (hr h) (g n) = g m}
  one_mem' _ _ _ := map_one _
  mul_mem' {a b} ha hb m n h := by rw [Pi.mul_apply, map_mul, ha h, hb h, Pi.mul_apply]
  zero_mem' _ _ _ := map_zero _
  add_mem' {a b} ha hb m n h := by rw [Pi.add_apply, map_add, ha h, hb h, Pi.add_apply]
  neg_mem' {a} ha m n h := by rw [Pi.neg_apply, map_neg, ha h, Pi.neg_apply]

/-- Membership in `compatibleSubring` is compatibility with radius restriction for all `m ≤ n`. -/
@[simp]
theorem mem_compatibleSubring {κ : Type*} [Preorder κ] {r : κ → ℝ} [∀ k, Fact (0 < r k)]
    {hr : Monotone r} {g : ∀ k, IsRestricted.subring (R := R) (r k)} :
    g ∈ compatibleSubring (R := R) hr ↔ ∀ ⦃m n : κ⦄ (h : m ≤ n),
      TauCeti.PowerSeries.restrictedRadiusHom (Fact.out : 0 < r m).le (hr h) (g n) = g m :=
  Iff.rfl

/-- The underlying set of `compatibleSubring` consists of families intertwined by radius
restriction. -/
theorem coe_compatibleSubring {κ : Type*} [Preorder κ] {r : κ → ℝ} [∀ k, Fact (0 < r k)]
    (hr : Monotone r) :
    (compatibleSubring (R := R) hr : Set (∀ k, IsRestricted.subring (R := R) (r k))) =
      {g | ∀ ⦃m n : κ⦄ (h : m ≤ n),
        TauCeti.PowerSeries.restrictedRadiusHom (Fact.out : 0 < r m).le (hr h) (g n) = g m} := by
  ext g
  exact mem_compatibleSubring

/-- Over a directed index preorder (such as `ℕ`), a family of restricted series is compatible with
radius restrictions if and only if all components have the same underlying formal power series. -/
theorem mem_compatibleSubring_iff_coe_eq {κ : Type*} [Preorder κ] [IsDirectedOrder κ]
    {r : κ → ℝ} [∀ k, Fact (0 < r k)] {hr : Monotone r}
    {g : ∀ k, IsRestricted.subring (R := R) (r k)} :
    g ∈ compatibleSubring (R := R) hr ↔ ∀ m n : κ, (g m : R⟦X⟧) = (g n : R⟦X⟧) := by
  refine ⟨fun hg m n ↦ ?_, fun hg m n h ↦ Subtype.ext (by simp [hg n m])⟩
  obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
  have hm := congrArg Subtype.val (hg hmk)
  have hn := congrArg Subtype.val (hg hnk)
  simp only [TauCeti.PowerSeries.coe_restrictedRadiusHom] at hm hn
  exact hm.symm.trans hn

/-- Compatible restricted series form a closed subset of the product of closed-disc algebras. -/
theorem isClosed_compatibleSubring {κ : Type*} [Preorder κ] {r : κ → ℝ}
    [∀ k, Fact (0 < r k)] (hr : Monotone r) :
    IsClosed (compatibleSubring (R := R) hr : Set (∀ k, IsRestricted.subring (R := R) (r k))) := by
  rw [coe_compatibleSubring]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦ ?_
  exact isClosed_eq
    ((TauCeti.PowerSeries.continuous_restrictedRadiusHom (Fact.out : 0 < r m).le (hr h)).comp
      (continuous_apply n))
    (continuous_apply m)

instance {κ : Type*} [Preorder κ] {r : κ → ℝ} [∀ k, Fact (0 < r k)] (hr : Monotone r)
    [CompleteSpace R] : CompleteSpace (compatibleSubring (R := R) hr) :=
  (isClosed_compatibleSubring hr).isComplete.completeSpace_coe

variable {ι : Type*} {ρ : ι → ℝ} {T : Subring R⟦X⟧}
  (hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i))

/-- Restricting a series in `T` along a radius-monotone subfamily of positive radii yields a
compatible family of restricted series. -/
theorem restrictSubfamily_mem_compatibleSubring {κ : Type*} [Preorder κ] {σ : κ → ι}
    [∀ k, Fact (0 < ρ (σ k))] (hr : Monotone fun k ↦ ρ (σ k)) (f : T) :
    restrictSubfamily hT σ f ∈ compatibleSubring (R := R) hr :=
  fun _ _ _ ↦ Subtype.ext (by simp)

/-- Over a directed index preorder (such as `ℕ`), the image of `T` along a monotone cofinal
subfamily of positive radii dominating nonnegative radii `ρ` is the subring of compatible
restricted series. -/
theorem range_restrictSubfamily_eq_compatibleSubring {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] {σ : κ → ι} [∀ k, Fact (0 < ρ (σ k))] (hρ : ∀ i, 0 ≤ ρ i)
    (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    Set.range (restrictSubfamily hT σ) =
      (compatibleSubring (R := R) hr : Set (∀ k, IsRestricted.subring (R := R) (ρ (σ k)))) := by
  ext g
  rw [range_restrictSubfamily hT hρ hσ, SetLike.mem_coe, mem_compatibleSubring_iff_coe_eq]
  simp only [Set.mem_ofPred_eq, PowerSeries.ext_iff]

/-- **Projective-limit ring isomorphism.** Along any monotone cofinal subfamily of positive radii
dominating nonnegative radii `ρ`, indexed by a nonempty directed preorder (in particular, along a
monotone sequence of radii), `T` is isomorphic as a ring to the subring of compatible restricted
series. -/
noncomputable def compatibleRingEquiv {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    {σ : κ → ι} [∀ k, Fact (0 < ρ (σ k))] (hρ : ∀ i, 0 ≤ ρ i)
    (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    T ≃+* compatibleSubring (R := R) hr :=
  RingEquiv.ofBijective
    ((restrictSubfamily hT σ).codRestrict (compatibleSubring (R := R) hr)
      (restrictSubfamily_mem_compatibleSubring hT hr))
    ⟨RingHom.injective_codRestrict.mpr (restrictSubfamily_injective hT σ), fun ⟨g, hg⟩ ↦ by
      have hmem : g ∈ Set.range (restrictSubfamily hT σ) := by
        rwa [range_restrictSubfamily_eq_compatibleSubring hT hρ hr hσ]
      obtain ⟨f, rfl⟩ := hmem
      exact ⟨f, rfl⟩⟩

/-- Each component of `compatibleRingEquiv` is closed-disc restriction at that stage. -/
@[simp]
theorem coe_compatibleRingEquiv_apply {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    {σ : κ → ι} [∀ k, Fact (0 < ρ (σ k))] (hρ : ∀ i, 0 ≤ ρ i)
    (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k))
    (f : T) (k : κ) :
    (compatibleRingEquiv hT hρ hr hσ f : ∀ k, IsRestricted.subring (R := R) (ρ (σ k))) k =
      restrict hT (σ k) f :=
  (rfl)

/-- Restricting the series reconstructed from a compatible family `g` at stage `k` recovers
`g k`. -/
@[simp]
theorem restrict_compatibleRingEquiv_symm {κ : Type*} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] {σ : κ → ι} [∀ k, Fact (0 < ρ (σ k))] (hρ : ∀ i, 0 ≤ ρ i)
    (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k))
    (g : compatibleSubring (R := R) hr) (k : κ) :
    restrict hT (σ k) ((compatibleRingEquiv hT hρ hr hσ).symm g) = g.val k := by
  simpa only [coe_compatibleRingEquiv_apply] using
    congrFun (congrArg Subtype.val ((compatibleRingEquiv hT hρ hr hσ).apply_symm_apply g)) k

/-- The underlying formal power series of the element reconstructed from a compatible family `g`
agrees with `g k` at every stage `k`. -/
theorem coe_compatibleRingEquiv_symm {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    {σ : κ → ι} [∀ k, Fact (0 < ρ (σ k))] (hρ : ∀ i, 0 ≤ ρ i)
    (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k))
    (g : compatibleSubring (R := R) hr) (k : κ) :
    (((compatibleRingEquiv hT hρ hr hσ).symm g : T) : R⟦X⟧) = (g.val k : R⟦X⟧) := by
  rw [← coe_restrict hT (σ k), restrict_compatibleRingEquiv_symm]

/-- **Independence of the monotone cofinal family.** Compatible restricted-series families along
two monotone cofinal subfamilies of positive radii dominating nonnegative radii `ρ` (indexed by
nonempty directed preorders) define the same element of `T` if and only if they have the same
underlying formal power series. -/
theorem compatibleRingEquiv_symm_eq_iff {κ₁ κ₂ : Type*} [Preorder κ₁] [IsDirectedOrder κ₁]
    [Nonempty κ₁] [Preorder κ₂] [IsDirectedOrder κ₂] [Nonempty κ₂]
    {σ₁ : κ₁ → ι} {σ₂ : κ₂ → ι} [∀ k, Fact (0 < ρ (σ₁ k))] [∀ k, Fact (0 < ρ (σ₂ k))]
    (hρ : ∀ i, 0 ≤ ρ i)
    (hr₁ : Monotone fun k ↦ ρ (σ₁ k)) (hσ₁ : ∀ i, ∃ k, ρ i ≤ ρ (σ₁ k))
    (hr₂ : Monotone fun k ↦ ρ (σ₂ k)) (hσ₂ : ∀ i, ∃ k, ρ i ≤ ρ (σ₂ k))
    (g₁ : compatibleSubring (R := R) hr₁) (g₂ : compatibleSubring (R := R) hr₂)
    (k₁ : κ₁) (k₂ : κ₂) :
    (compatibleRingEquiv hT hρ hr₁ hσ₁).symm g₁ = (compatibleRingEquiv hT hρ hr₂ hσ₂).symm g₂ ↔
      (g₁.val k₁ : R⟦X⟧) = (g₂.val k₂ : R⟦X⟧) := by
  rw [Subtype.ext_iff, coe_compatibleRingEquiv_symm hT hρ hr₁ hσ₁ g₁ k₁,
    coe_compatibleRingEquiv_symm hT hρ hr₂ hσ₂ g₂ k₂]

variable [∀ i, Fact (0 < ρ i)]

/-- **Projective-limit uniform equivalence.** Along any monotone cofinal family of radii indexed by
a nonempty directed preorder, `T` with its Gauss uniformity is uniformly equivalent to the closed
subring of compatible restricted series. -/
noncomputable def compatibleUniformEquiv {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
    [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT)) {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k))
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    T ≃ᵤ compatibleSubring (R := R) hr :=
  (compatibleRingEquiv hT (fun i ↦ (Fact.out : 0 < ρ i).le) hr
    hσ).toEquiv.toUniformEquivOfIsUniformInducing <| by
    rw [← isUniformEmbedding_subtypeVal.isUniformInducing.of_comp_iff]
    have hcomp : Subtype.val ∘
        (compatibleRingEquiv hT (fun i ↦ (Fact.out : 0 < ρ i).le) hr hσ).toEquiv =
        restrictSubfamily hT σ := by
      funext f k
      simp only [Function.comp_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
        coe_compatibleRingEquiv_apply, restrictSubfamily_apply]
    rw [hcomp]
    exact isUniformInducing_restrictSubfamily hu hσ

/-- `compatibleUniformEquiv` applies on elements as `compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_apply {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
    [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT)) {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k))
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) (f : T) :
    compatibleUniformEquiv hu hr hσ f =
      compatibleRingEquiv hT (fun i ↦ (Fact.out : 0 < ρ i).le) hr hσ f :=
  (rfl)

/-- The inverse of `compatibleUniformEquiv` applies on elements as the inverse of
`compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_symm_apply {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
    [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT)) {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k))
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) (g : compatibleSubring (R := R) hr) :
    (compatibleUniformEquiv hu hr hσ).symm g =
      (compatibleRingEquiv hT (fun i ↦ (Fact.out : 0 < ρ i).le) hr hσ).symm g :=
  (rfl)

end Compatible

end TauCeti.PowerSeries.GaussFamily

namespace TauCeti.PowerSeries.GaussFamily

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {ι : Type*} {ρ : ι → ℝ}
  [∀ i, Fact (0 < ρ i)] {T : Subring R⟦X⟧}
  {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
  [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT))
include hu

/-- An unconditional product converges in `T` exactly when its restriction to the closed disc of
every radius `ρ i` converges. -/
theorem hasProd_iff {κ : Type*} {f : κ → T} {g : T} :
    HasProd f g ↔ ∀ i, HasProd (fun j ↦ restrict hT i (f j)) (restrict hT i g) := by
  simp only [HasProd, SummationFilter.unconditional_filter, tendsto_iff hu, map_prod]

/-- A family in `T` is unconditionally multipliable exactly when its restriction to the closed disc
of every radius `ρ i` is multipliable. -/
theorem multipliable_iff {κ : Type*} {f : κ → T} :
    Multipliable f ↔ ∀ i, Multipliable fun j ↦ restrict hT i (f j) := by
  refine ⟨fun ⟨g, hg⟩ ↦ fun i ↦ ⟨_, (hasProd_iff hu).mp hg i⟩, fun h ↦ ?_⟩
  rcases isEmpty_or_nonempty ι with hι | _
  · exact ⟨1, (hasProd_iff hu).mpr fun i ↦ (hι.false i).elim⟩
  choose g hg using h
  have hmem : g ∈ Set.range (restrictFamily hT) := by
    rw [range_restrictFamily]
    intro i₁ i₂ n
    have hc (i : ι) : Tendsto (fun s : Finset κ ↦ coeff n ((∏ j ∈ s, f j : T) : R⟦X⟧))
        atTop (𝓝 (coeff n (g i : R⟦X⟧))) := by
      have hni := (TauCeti.PowerSeries.uniformContinuous_coeff (R := R) (c := ρ i) n).continuous
      have hgi := hg i
      rw [HasProd, SummationFilter.unconditional_filter] at hgi
      simpa only [Function.comp_def, ← map_prod, coe_restrict] using
        (hni.tendsto (g i)).comp hgi
    exact tendsto_nhds_unique (hc i₁) (hc i₂)
  obtain ⟨f₀, hf₀⟩ := hmem
  exact ⟨f₀, (hasProd_iff hu).mpr fun i ↦ by rw [← restrictFamily_apply, hf₀]; exact hg i⟩

/-- Restriction to the closed disc of a radius `ρ i` commutes with convergent infinite products. -/
theorem restrict_tprod {κ : Type*} {f : κ → T} (hf : Multipliable f) (i : ι) :
    restrict hT i (∏' j, f j) = ∏' j, restrict hT i (f j) :=
  (((hasProd_iff hu).mp hf.hasProd i).tprod_eq).symm

/-- For a nonempty family of radii, taking constant coefficients commutes with `HasProd` in `T`. -/
theorem hasProd_constantCoeff [Nonempty ι] {κ : Type*} {f : κ → T} {g : T} (hf : HasProd f g) :
    HasProd (fun j ↦ constantCoeff (f j : R⟦X⟧)) (constantCoeff (g : R⟦X⟧)) := by
  have hcont : Continuous (constantCoeff.comp T.subtype) := by
    simpa only [RingHom.coe_comp, Function.comp_def, Subring.coe_subtype,
      coeff_zero_eq_constantCoeff] using (uniformContinuous_coeff hu 0).continuous
  exact hf.map (constantCoeff.comp T.subtype) hcont

/-- For a nonempty family of radii, the constant coefficient of a convergent infinite product in
`T` is the infinite product of the constant coefficients. -/
theorem constantCoeff_tprod [Nonempty ι] {κ : Type*} {f : κ → T} (hf : Multipliable f) :
    constantCoeff ((∏' j, f j : T) : R⟦X⟧) = ∏' j, constantCoeff (f j : R⟦X⟧) :=
  (hasProd_constantCoeff hu hf.hasProd).tprod_eq.symm

/-- If a `HasProd` limit converges in `T`, then the partial products converge in the Gauss norm at
every nonnegative radius `s` dominated by some family radius `ρ i`. -/
theorem tendsto_gaussNorm_sub_prod {κ : Type*} {f : κ → T} {g : T} (hf : HasProd f g)
    {s : ℝ} (hs : 0 ≤ s) {i : ι} (hi : s ≤ ρ i) :
    Tendsto (fun t : Finset κ ↦ ((g : R⟦X⟧) - ∏ j ∈ t, (f j : R⟦X⟧)).gaussNorm norm s)
      atTop (𝓝 0) := by
  have := isUniformAddGroup hu
  have h0 : Tendsto (fun t : Finset κ ↦ g - ∏ j ∈ t, f j) atTop (𝓝 0) := by
    simpa only [sub_self, SummationFilter.unconditional_filter] using
      (tendsto_const_nhds (x := g)).sub hf
  have hlim : Tendsto (fun t : Finset κ ↦ ‖restrict hT i (g - ∏ j ∈ t, f j)‖) atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero] using ((tendsto_iff hu).mp h0 i).norm
  have hsub (t : Finset κ) :
      (g : R⟦X⟧) - ∏ j ∈ t, (f j : R⟦X⟧) = ((g - ∏ j ∈ t, f j : T) : R⟦X⟧) := by
    simp [AddSubgroupClass.coe_sub]
  simp_rw [hsub]
  refine squeeze_zero (fun _ ↦ PowerSeries.gaussNorm_nonneg norm s _ norm_nonneg) (fun t ↦ ?_) hlim
  rw [norm_restrict]
  exact TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le norm_nonneg hs hi
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted ((hT _).mp (g - ∏ j ∈ t, f j).property i))

end NormedCommRing

end TauCeti.PowerSeries.GaussFamily
