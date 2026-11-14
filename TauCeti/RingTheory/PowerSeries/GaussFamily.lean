/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The Gauss topology of a family of radii

Let `R` be an ultrametric normed ring, `ρ : ι → ℝ` a family of positive radii, and `T` the
subring of power series that are restricted at every radius `ρ i`. Such subrings include the
series on an open disc, where the radii are those below the boundary, and the entire series,
where they are all positive radii. This file develops the topology on `T` given by the Gauss
norms at all the radii `ρ i` once, so that each of these algebras is a specialization.

The subring is described by a membership condition `hT`, and its uniformity by the hypothesis
that restriction to the closed discs of all radii is uniformly inducing. Under these hypotheses,
convergence is convergence in each Gauss norm, and it may be tested at any family of radii that
dominates `ρ`. The resulting uniform ring is a topological ring in which polynomial truncations
converge. When `ι` is nonempty, restriction is a uniform embedding whose image consists of the
families with the same formal coefficients at every radius. That image is closed, so the
algebra is Hausdorff and is complete when `R` is complete.

## Main definitions

* `TauCeti.PowerSeries.GaussFamily.restrictFamily`: restriction of `T` to the closed discs of
  all the radii, and `TauCeti.PowerSeries.GaussFamily.restrictSubfamily` along a subfamily.
* `TauCeti.PowerSeries.GaussFamily.uniformSpace`: the uniformity induced by that restriction.
* `TauCeti.PowerSeries.GaussFamily.compatibleSubring`: the closed subring of compatible
  restricted series along a monotone family of positive radii, with ring and uniform equivalences
  `TauCeti.PowerSeries.GaussFamily.compatibleRingEquiv` and
  `TauCeti.PowerSeries.GaussFamily.compatibleUniformEquiv`.

## Main results

* `TauCeti.PowerSeries.GaussFamily.uniformSpace_eq_comap_of_cofinal_radius` and
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
* `TauCeti.PowerSeries.GaussFamily.isTopologicalRing`, `TauCeti.PowerSeries.GaussFamily.t2Space`
  and `TauCeti.PowerSeries.GaussFamily.completeSpace`: the ring structure, separation and
  completeness of the Gauss topology.
* `TauCeti.PowerSeries.GaussFamily.not_exists_ringSeminorm` and
  `TauCeti.PowerSeries.GaussFamily.not_exists_addGroupSeminorm_constHom_mul_le`: when the radii
  have no maximum, no single ring seminorm or scalar-bounded additive group seminorm on `T`
  induces the Gauss topology over a nontrivial ultrametric normed ring with a unit of norm `< 1`.
-/

public section

open Filter PowerSeries
open scoped Topology Uniformity

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

/-- Any nonempty subfamily of closed-disc restrictions determines a series in `T`. -/
theorem restrictSubfamily_injective {κ : Type*} [Nonempty κ] (σ : κ → ι) :
    Function.Injective (restrictSubfamily hT σ) := by
  intro f g h
  exact Subtype.ext (congrArg (fun h ↦ (h (Classical.arbitrary κ) : R⟦X⟧)) h)

/-- The family of closed-disc restrictions determines a series in `T`. -/
theorem restrictFamily_injective [Nonempty ι] : Function.Injective (restrictFamily hT) :=
  restrictSubfamily_injective hT id

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
      exact (g i).2
    · funext i
      exact Subtype.ext (heq i).symm

/-- Along a cofinal subfamily of nonnegative radii, the restriction image consists of families with
index-independent formal coefficients. -/
theorem range_restrictSubfamily {κ : Type*} {σ : κ → ι} (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    Set.range (restrictSubfamily hT σ) =
      {g | ∀ k l : κ, ∀ n : ℕ, coeff n (g k : R⟦X⟧) = coeff n (g l : R⟦X⟧)} := by
  ext g
  refine ⟨?_, fun hg ↦ ?_⟩
  · rintro ⟨f, rfl⟩
    intro k l n
    simp only [restrictSubfamily_apply, coe_restrict]
  · rcases isEmpty_or_nonempty κ with hκ | hκ
    · exact ⟨0, funext fun k ↦ (hκ.false k).elim⟩
    let k₀ := Classical.arbitrary κ
    have heq (k) : (g k : R⟦X⟧) = (g k₀ : R⟦X⟧) := PowerSeries.ext (hg k k₀)
    refine ⟨⟨(g k₀ : R⟦X⟧), (hT _).mpr fun i ↦ ?_⟩, ?_⟩
    · obtain ⟨k, hk⟩ := hσ i
      rw [← heq k]
      exact TauCeti.MvPowerSeries.isRestricted_of_le (g k).2 (fun _ : Unit ↦ hρ i) (fun _ ↦ hk)
    · funext k
      exact Subtype.ext (heq k).symm

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
  rw [range_restrictSubfamily hT hρ hσ]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun k ↦ isClosed_iInter fun l ↦ isClosed_iInter fun n ↦ ?_
  have h (j : κ) : Continuous fun g : (∀ k, IsRestricted.subring (R := R) (ρ (σ k))) ↦
      coeff n (g j : R⟦X⟧) :=
    (TauCeti.PowerSeries.uniformContinuous_coeff n).continuous.comp (continuous_apply j)
  exact isClosed_eq (h k) (h l)

private theorem norm_restrict_monomial (i : ι) (m : ℕ) (a : R) :
    ‖restrict hT i ⟨monomial m a, (hT _).mpr fun j ↦ isRestricted_monomial (ρ j) m a⟩‖ =
      ‖a‖ * ρ i ^ m := by
  have hr : 0 < ρ i := Fact.out
  rw [TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict,
    TauCeti.PowerSeries.gaussNorm_eq_of_forall_le (s := m) fun n ↦ ?_]
  · simp [coeff_monomial_same]
  · rcases eq_or_ne n m with rfl | hne
    · rfl
    · simp only [coeff_monomial, hne, ↓reduceIte, norm_zero, zero_mul]
      positivity

private theorem continuous_constHom_of_isInducing [TopologicalSpace T]
    (hind : Topology.IsInducing (restrictFamily hT)) : Continuous (constHom hT) := by
  rw [hind.continuous_iff, continuous_pi_iff]
  intro i
  let ψ : R →+ IsRestricted.subring (R := R) (ρ i) :=
    ((restrict hT i).comp (constHom hT)).toAddMonoidHom
  refine continuous_of_continuousAt_zero ψ (Metric.continuousAt_iff.mpr fun ε hε ↦ ⟨ε, hε, ?_⟩)
  intro c hc
  have hψc : ψ c = ⟨PowerSeries.C c, isRestricted_C (ρ i) c⟩ := Subtype.ext (by simp [ψ])
  simpa [dist_zero_right, hψc, TauCeti.PowerSeries.norm_C] using hc

private theorem exists_norm_restrict_lt_imp_mem_of_isInducing [Nonempty ι] [TopologicalSpace T]
    (hind : Topology.IsInducing (restrictFamily hT)) {U : Set T} (hU : U ∈ 𝓝 0) :
    ∃ i₀ : ι, ∃ δ > 0, ∀ f : T, ‖restrict hT i₀ f‖ < δ → f ∈ U := by
  rw [hind.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨s, t, ht, hstV⟩ := hV
  choose ε hεpos hεt using fun i ↦ Metric.mem_nhds_iff.mp (ht i)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨Classical.arbitrary ι, 1, one_pos, fun f _ ↦ hVU (hstV ?_)⟩
    simp
  · obtain ⟨i₀, _, hi₀max⟩ := s.exists_max_image ρ hs
    let δ : ℝ := s.inf' hs ε
    have hδpos : 0 < δ := (Finset.lt_inf'_iff hs).mpr fun i _ ↦ hεpos i
    refine ⟨i₀, δ, hδpos, fun f hf ↦ hVU (hstV fun i hi ↦ hεt i ?_)⟩
    rw [Metric.mem_ball, Pi.zero_apply, dist_zero_right, restrictFamily_apply]
    have hle : ‖restrict hT i f‖ ≤ ‖restrict hT i₀ f‖ := by
      rw [TauCeti.PowerSeries.norm_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm,
        coe_restrict, coe_restrict]
      exact TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le norm_nonneg (Fact.out : 0 < ρ i).le
        (hi₀max i hi) (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted ((hT _).mp f.2 i₀))
    exact (hle.trans_lt hf).trans_le (Finset.inf'_le ε hi)

private theorem not_exists_addGroupSeminorm_of_isInducing [Nonempty ι] [Nontrivial R]
    (p : AddGroupSeminorm T)
    (hind : @Topology.IsInducing _ _
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace _ (restrictFamily hT))
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (u : Rˣ) (hu1 : ‖(u : R)‖ < 1)
    (hsmall : ∀ ε > 0, ∃ q : ℕ, ∀ f : T, p f < 1 → p (constHom hT ((u : R) ^ (q + 1)) * f) < ε) :
    False := by
  let : SeminormedAddCommGroup T := p.toSeminormedAddCommGroup
  obtain ⟨i₀, δ, hδ, hi₀⟩ := exists_norm_restrict_lt_imp_mem_of_isInducing hT hind
    (Metric.ball_mem_nhds (0 : T) one_pos)
  obtain ⟨i₁, hi₀₁⟩ := hmax i₀
  have hc₁ : Continuous fun f : T ↦ ‖restrict hT i₁ f‖ :=
    continuous_norm.comp ((continuous_apply i₁).comp hind.continuous)
  obtain ⟨ε, hε, hε₁⟩ := Metric.mem_nhds_iff.mp
    ((hc₁.isOpen_preimage _ isOpen_Iio).mem_nhds (by simp : ‖restrict hT i₁ (0 : T)‖ < 1))
  obtain ⟨q, hq⟩ := hsmall ε hε
  let M : ℝ := ‖((u⁻¹ : Rˣ) : R)‖
  have hM : 0 < M := Units.norm_pos u⁻¹
  have hr₀ : 0 < ρ i₀ := Fact.out
  have hr₁ : 0 < ρ i₁ := Fact.out
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M ^ (q + 2) / δ) ((one_lt_div hr₀).mpr hi₀₁)
  have hgap : (M ^ (q + 1) * (ρ i₁)⁻¹ ^ n) * M < δ * (ρ i₀)⁻¹ ^ n := by
    have hring : M ^ (q + 1) * (ρ i₁ ^ n)⁻¹ * M * ρ i₀ ^ n =
        (M ^ (q + 2) * ρ i₀ ^ n) / ρ i₁ ^ n := by ring
    rw [div_lt_iff₀ hδ, div_pow, div_mul_eq_mul_div, lt_div_iff₀ (pow_pos hr₀ n)] at hn
    rw [inv_pow, inv_pow, ← div_eq_mul_inv (b := ρ i₀ ^ n), lt_div_iff₀ (pow_pos hr₀ n), hring,
      div_lt_iff₀ (pow_pos hr₁ n)]
    linarith
  obtain ⟨z, hz₁, hz₀⟩ := u.exists_lt_norm_zpow_lt hu1 (by positivity) hgap
  let a : R := ((u ^ z : Rˣ) : R)
  let g : T := ⟨monomial n a, (hT _).mpr fun j ↦ isRestricted_monomial (ρ j) n a⟩
  have hnorm (x : T) : ‖x‖ = p x := rfl
  have hgN : p g < 1 := by
    have hball := hi₀ g <| by
      rw [norm_restrict_monomial, ← lt_div_iff₀ (pow_pos hr₀ n), div_eq_mul_inv, ← inv_pow]
      exact hz₀
    rwa [Metric.mem_ball, dist_zero_right, hnorm] at hball
  let c : R := (u : R) ^ (q + 1)
  have hcg₁ : ‖restrict hT i₁ (constHom hT c * g)‖ < 1 := by
    refine hε₁ (Metric.mem_ball.mpr ?_)
    rw [dist_zero_right, hnorm]
    exact hq g hgN
  have hcg_eq : constHom hT c * g = ⟨monomial n (c * a),
      (hT _).mpr fun j ↦ isRestricted_monomial (ρ j) n (c * a)⟩ :=
    Subtype.ext (by ext d; simp [g, coeff_C_mul, coeff_monomial])
  have hca_gt : (ρ i₁)⁻¹ ^ n < ‖c * a‖ :=
    lt_of_mul_lt_mul_left (hz₁.trans_le (u.norm_le_pow_inv_mul_norm_pow_mul (q + 1) a))
      (by positivity : (0 : ℝ) ≤ M ^ (q + 1))
  have hcg_ge : 1 < ‖restrict hT i₁ (constHom hT c * g)‖ := by
    rw [hcg_eq, norm_restrict_monomial, ← inv_lt_iff_one_lt_mul₀ (pow_pos hr₁ n), ← inv_pow]
    exact hca_gt
  exact hcg₁.not_gt hcg_ge

private theorem not_exists_ringSeminorm_of_isInducing [Nonempty ι] [Nontrivial R]
    (p : RingSeminorm T)
    (hind : @Topology.IsInducing _ _
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace _ (restrictFamily hT))
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (u : Rˣ) (hu1 : ‖(u : R)‖ < 1) : False := by
  let : SeminormedRing T := p.toSeminormedRing
  have hnorm (x : T) : ‖x‖ = p x := rfl
  refine not_exists_addGroupSeminorm_of_isInducing hT p.toAddGroupSeminorm hind hmax u hu1
    fun ε hε ↦ ?_
  have hu_tend : Tendsto (fun q : ℕ ↦ (u : R) ^ (q + 1)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun q ↦ by simpa using norm_pow_le' (u : R) q.succ_pos)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu1).comp (tendsto_add_atTop_nat 1))
  have hN_tend : Tendsto (fun q : ℕ ↦ constHom hT ((u : R) ^ (q + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      ((continuous_constHom_of_isInducing hT hind).tendsto 0).comp hu_tend
  obtain ⟨q, hq⟩ :=
    ((tendsto_iff_norm_sub_tendsto_zero.mp hN_tend).eventually (Iio_mem_nhds hε)).exists
  refine ⟨q, fun f hf ↦ ?_⟩
  have hcq : p (constHom hT ((u : R) ^ (q + 1))) < ε := by rwa [sub_zero, hnorm] at hq
  calc p (constHom hT ((u : R) ^ (q + 1)) * f)
      ≤ p (constHom hT ((u : R) ^ (q + 1))) * p f := map_mul_le_mul p _ _
    _ ≤ p (constHom hT ((u : R) ^ (q + 1))) * 1 :=
        mul_le_mul_of_nonneg_left hf.le (apply_nonneg p _)
    _ < ε := by simpa using hcq

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

/-- Constant inclusion `constHom` is continuous for the Gauss topology on `T`. -/
theorem continuous_constHom : Continuous (constHom hT) :=
  continuous_constHom_of_isInducing hT hu.isInducing

/-- A map into `T` is uniformly continuous exactly when each restriction is. -/
theorem uniformContinuous_iff {X : Type*} [UniformSpace X] {f : X → T} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x ↦ restrict hT i (f x) := by
  rw [hu.uniformContinuous_iff, uniformContinuous_pi]
  rfl

/-- The Gauss uniformity is compatible with addition. -/
theorem isUniformAddGroup : IsUniformAddGroup T :=
  hu.isUniformAddGroup (restrictFamily hT)

/-- The Gauss topology makes `T` a topological ring. -/
theorem isTopologicalRing : IsTopologicalRing T :=
  have := isUniformAddGroup hu
  { continuous_mul := (hu.isInducing.continuousMul (restrictFamily hT)).continuous_mul }

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

/-- Every zero-neighborhood for the Gauss topology contains a single closed-disc Gauss ball:
because radius restriction is contractive, the largest radius among finitely many closed-disc
conditions controls all of them. -/
theorem exists_norm_restrict_lt_imp_mem {U : Set T} (hU : U ∈ 𝓝 0) :
    ∃ i₀ : ι, ∃ δ > 0, ∀ f : T, ‖restrict hT i₀ f‖ < δ → f ∈ U :=
  exists_norm_restrict_lt_imp_mem_of_isInducing hT hu.isInducing hU

/-- **No single ring seminorm represents the Gauss topology when the radii have no maximum.**
Over a nontrivial ultrametric normed ring with a unit `u` of norm `< 1` (in particular, over any
nontrivially normed ultrametric field), if every radius `ρ i` is strictly dominated by another
radius `ρ j`, then no ring seminorm on `T` induces its Gauss topology. -/
theorem not_exists_ringSeminorm [Nontrivial R] (hmax : ∀ i, ∃ j, ρ i < ρ j)
    (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ p : RingSeminorm T,
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace = UniformSpace.toTopologicalSpace := by
  rintro ⟨p, htop⟩
  obtain ⟨u, hu1⟩ := hu_unit
  have hind : @Topology.IsInducing _ _
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace _ (restrictFamily hT) :=
    htop ▸ hu.isInducing
  exact not_exists_ringSeminorm_of_isInducing hT p hind hmax u hu1

/-- **No scalar-bounded group seminorm represents the Gauss topology when the radii have no
maximum.** Over a nontrivial ultrametric normed ring with a unit `u` of norm `< 1`, no additive
group seminorm `p` on `T` in which left multiplication by `constHom hT c` is bounded by `C * ‖c‖`
induces the Gauss topology. In particular, over a nontrivially normed ultrametric field `K`, no
Banach-space norm compatible with coefficientwise scalar multiplication represents the Gauss
topology. -/
theorem not_exists_addGroupSeminorm_constHom_mul_le [Nontrivial R]
    (hmax : ∀ i, ∃ j, ρ i < ρ j) (hu_unit : ∃ u : Rˣ, ‖(u : R)‖ < 1) :
    ¬ ∃ (p : AddGroupSeminorm T) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : R) (f : T), p (constHom hT c * f) ≤ C * ‖c‖ * p f := by
  rintro ⟨p, C, htop, hsmul⟩
  obtain ⟨u, hu1⟩ := hu_unit
  have hind : @Topology.IsInducing _ _
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace _ (restrictFamily hT) :=
    htop ▸ hu.isInducing
  refine not_exists_addGroupSeminorm_of_isInducing hT p hind hmax u hu1 fun ε hε ↦ ?_
  have hC1 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  obtain ⟨q, hq⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu1).comp
    (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (div_pos hε hC1))).exists
  refine ⟨q, fun f hf ↦ ?_⟩
  have hcq : ‖(u : R) ^ (q + 1)‖ ≤ ‖(u : R)‖ ^ (q + 1) := norm_pow_le' (u : R) q.succ_pos
  calc p (constHom hT ((u : R) ^ (q + 1)) * f)
      ≤ C * ‖(u : R) ^ (q + 1)‖ * p f := hsmul _ f
    _ ≤ max C 1 * ‖(u : R)‖ ^ (q + 1) * 1 := by
        refine mul_le_mul (mul_le_mul (le_max_left C 1) hcq (norm_nonneg _) hC1.le) hf.le
          (apply_nonneg p f) (by positivity)
    _ < ε := by simpa using (lt_div_iff₀' hC1).mp hq

end Inducing

/-- Any cofinal subfamily of radii induces the full Gauss uniformity `uniformSpace hT`. -/
theorem uniformSpace_eq_comap_of_cofinal_radius {κ : Type*} {σ : κ → ι}
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
  (uniformSpace_eq_comap_of_cofinal_radius hT hσ₁).trans
    (uniformSpace_eq_comap_of_cofinal_radius hT hσ₂).symm

end Family

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {ι : Type*} [Nonempty ι] {ρ : ι → ℝ} [∀ i, Fact (0 < ρ i)]
  {T : Subring K⟦X⟧} {hT : ∀ f : K⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
  [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT))
include hu

/-- Over a nontrivially normed ultrametric field, no single ring seminorm induces the Gauss
topology when the radii have no maximum. -/
theorem not_exists_ringSeminorm_of_nontriviallyNormedField (hmax : ∀ i, ∃ j, ρ i < ρ j) :
    ¬ ∃ p : RingSeminorm T,
      p.toSeminormedRing.toUniformSpace.toTopologicalSpace = UniformSpace.toTopologicalSpace :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_ringSeminorm hu hmax ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

/-- Over a nontrivially normed ultrametric field, no additive group seminorm on `T` in which left
multiplication by `constHom hT c` is bounded by `C * ‖c‖` induces the Gauss topology when the radii
have no maximum. -/
theorem not_exists_addGroupSeminorm_constHom_mul_le_of_nontriviallyNormedField
    (hmax : ∀ i, ∃ j, ρ i < ρ j) :
    ¬ ∃ (p : AddGroupSeminorm T) (C : ℝ),
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace =
        UniformSpace.toTopologicalSpace ∧
      ∀ (c : K) (f : T), p (constHom hT c * f) ≤ C * ‖c‖ * p f :=
  let ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K
  not_exists_addGroupSeminorm_constHom_mul_le hu hmax ⟨Units.mk0 x (norm_pos_iff.mp hx0), hx1⟩

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
@[simp]
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

variable [∀ i, Fact (0 < ρ i)]

/-- **Projective-limit ring isomorphism.** Along any monotone cofinal family of radii indexed by a
nonempty directed preorder (in particular, along a monotone sequence of radii), `T` is isomorphic
as a ring to the subring of compatible restricted series. -/
noncomputable def compatibleRingEquiv {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    T ≃+* compatibleSubring (R := R) hr :=
  RingEquiv.ofBijective
    ((restrictSubfamily hT σ).codRestrict (compatibleSubring (R := R) hr)
      (restrictSubfamily_mem_compatibleSubring hT hr))
    ⟨fun f g h ↦ restrictSubfamily_injective hT σ (congrArg Subtype.val h), fun ⟨g, hg⟩ ↦ by
      have hmem : g ∈ Set.range (restrictSubfamily hT σ) := by
        rwa [range_restrictSubfamily_eq_compatibleSubring hT (fun i ↦ (Fact.out : 0 < ρ i).le)
          hr hσ]
      obtain ⟨f, rfl⟩ := hmem
      exact ⟨f, rfl⟩⟩

/-- Each component of `compatibleRingEquiv` is closed-disc restriction at that stage. -/
@[simp]
theorem coe_compatibleRingEquiv_apply {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k))
    (f : T) (k : κ) :
    (compatibleRingEquiv hT hr hσ f : ∀ k, IsRestricted.subring (R := R) (ρ (σ k))) k =
      restrict hT (σ k) f :=
  (rfl)

/-- Restricting the series reconstructed from a compatible family `g` at stage `k` recovers
`g k`. -/
@[simp]
theorem restrict_symm_compatibleRingEquiv {κ : Type*} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k))
    (g : compatibleSubring (R := R) hr) (k : κ) :
    restrict hT (σ k) ((compatibleRingEquiv hT hr hσ).symm g) = g.1 k := by
  simpa only [coe_compatibleRingEquiv_apply] using
    congrFun (congrArg Subtype.val ((compatibleRingEquiv hT hr hσ).apply_symm_apply g)) k

/-- The underlying formal power series of the element reconstructed from a compatible family `g`
agrees with `g k` at every stage `k`. -/
theorem coe_symm_compatibleRingEquiv {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k)) (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k))
    (g : compatibleSubring (R := R) hr) (k : κ) :
    (((compatibleRingEquiv hT hr hσ).symm g : T) : R⟦X⟧) = (g.1 k : R⟦X⟧) := by
  rw [← coe_restrict hT (σ k), restrict_symm_compatibleRingEquiv]

/-- **Independence of the monotone cofinal family.** Compatible restricted-series families along
two monotone cofinal subfamilies define the same element of `T` if and only if they have the same
underlying formal power series. -/
theorem compatibleRingEquiv_symm_eq_iff {κ₁ κ₂ : Type*} [Preorder κ₁] [IsDirectedOrder κ₁]
    [Nonempty κ₁] [Preorder κ₂] [IsDirectedOrder κ₂] [Nonempty κ₂]
    {σ₁ : κ₁ → ι} {σ₂ : κ₂ → ι}
    (hr₁ : Monotone fun k ↦ ρ (σ₁ k)) (hσ₁ : ∀ i, ∃ k, ρ i ≤ ρ (σ₁ k))
    (hr₂ : Monotone fun k ↦ ρ (σ₂ k)) (hσ₂ : ∀ i, ∃ k, ρ i ≤ ρ (σ₂ k))
    (g₁ : compatibleSubring (R := R) hr₁) (g₂ : compatibleSubring (R := R) hr₂)
    (k₁ : κ₁) (k₂ : κ₂) :
    (compatibleRingEquiv hT hr₁ hσ₁).symm g₁ = (compatibleRingEquiv hT hr₂ hσ₂).symm g₂ ↔
      (g₁.1 k₁ : R⟦X⟧) = (g₂.1 k₂ : R⟦X⟧) := by
  rw [Subtype.ext_iff, coe_symm_compatibleRingEquiv hT hr₁ hσ₁ g₁ k₁,
    coe_symm_compatibleRingEquiv hT hr₂ hσ₂ g₂ k₂]

/-- **Projective-limit uniform equivalence.** Along any monotone cofinal family of radii indexed by
a nonempty directed preorder, `T` with its Gauss uniformity is uniformly equivalent to the closed
subring of compatible restricted series. -/
noncomputable def compatibleUniformEquiv {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
    [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT)) {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k))
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) :
    T ≃ᵤ compatibleSubring (R := R) hr :=
  (compatibleRingEquiv hT hr hσ).toEquiv.toUniformEquivOfIsUniformInducing <|
    (IsUniformInducing.mk (f := Subtype.val) rfl).of_comp_iff.mp
      (isUniformInducing_restrictSubfamily hu hσ)

/-- `compatibleUniformEquiv` applies on elements as `compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_apply {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
    [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT)) {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k))
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) (f : T) :
    compatibleUniformEquiv hu hr hσ f = compatibleRingEquiv hT hr hσ f :=
  (rfl)

/-- The inverse of `compatibleUniformEquiv` applies on elements as the inverse of
`compatibleRingEquiv`. -/
@[simp]
theorem compatibleUniformEquiv_symm_apply {hT : ∀ f : R⟦X⟧, f ∈ T ↔ ∀ i, f.IsRestricted (ρ i)}
    [UniformSpace T] (hu : IsUniformInducing (restrictFamily hT)) {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {σ : κ → ι} (hr : Monotone fun k ↦ ρ (σ k))
    (hσ : ∀ i, ∃ k, ρ i ≤ ρ (σ k)) (g : compatibleSubring (R := R) hr) :
    (compatibleUniformEquiv hu hr hσ).symm g = (compatibleRingEquiv hT hr hσ).symm g :=
  (rfl)

end Compatible

end TauCeti.PowerSeries.GaussFamily
