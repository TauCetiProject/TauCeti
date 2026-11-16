/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CCHypersurface.Regular
public import TauCeti.MeasureTheory.OptimalTransport.Brenier

/-!
# Regular sources for quadratic optimal transport

Brenier's theorem (`TauCeti/MeasureTheory/OptimalTransport/Brenier.lean`) holds whenever the source
law `μ` on a finite-dimensional real inner product space `E` is **`c - c`-regular**
(`TauCeti.IsCCRegular μ`), strictly generalizing absolute continuity with respect to additive Haar
measure (e.g. atomless singular measures on `ℝ`, or product Cantor measures on `ℝ²`).

This module proves strict convexity of the quadratic transport cost in the target for
`c - c`-regular sources, and the converse / sharp characterization of Gangbo–McCann (1996) and
Ambrosio–Gigli (2013, Theorem 1.26): a `P₂` probability law `μ` is `c - c`-regular iff for every
`P₂` target `ν`, every quadratic optimal coupling is induced by a transport map (note uniqueness
*alone* holds trivially for Dirac masses).

## Main statements

* `TauCeti.IsCCRegular.transportCost_smul_add_smul_lt` — strict convexity of the quadratic transport
  cost in the target for a `c - c`-regular source.
* `TauCeti.exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular`,
  `TauCeti.isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan`, and its existence
  and uniqueness counterpart — **Ambrosio–Gigli Theorem 1.26** in `MemLp` form.
* In `TauCeti.WassersteinSpace`: `isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan` and
  `isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling`
  — **Ambrosio–Gigli Theorem 1.26** on `WassersteinSpace 2 E`.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113–161.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.25 and Theorem 1.26.
* C. Villani, *Topics in Optimal Transportation*, GSM 58, AMS, 2003, §2.1.3 and §2.4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace

namespace TauCeti

section StrictConvexity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- **Strict convexity of the quadratic transport cost in the target for `c - c`-regular sources.**
Whenever `μ` is a `c - c`-regular probability measure and `ν₀ ≠ ν₁` have finite quadratic transport
cost from `μ`, any nontrivial convex combination `a • ν₀ + b • ν₁` (`a, b ≠ 0`, `a + b = 1`) has
strictly smaller transport cost than the convex combination of the two costs. -/
theorem IsCCRegular.transportCost_smul_add_smul_lt [IsProbabilityMeasure μ] (hμ : IsCCRegular μ)
    {ν₀ ν₁ : Measure E} {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfin₀ : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₀ ≠ ∞)
    (hfin₁ : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₁ ≠ ∞)
    (hne : ν₀ ≠ ν₁) :
    transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ (a • ν₀ + b • ν₁) <
      a * transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₀ +
        b * transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν₁ := by
  let c : E × E → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)
  have hc := (continuous_ofReal_norm_sub_sq_div_two (F := E)).lowerSemicontinuous
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin₀
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin₁
  obtain ⟨π₀, hπ₀⟩ := exists_isOptimalCoupling μ ν₀ hc
  obtain ⟨π₁, hπ₁⟩ := exists_isOptimalCoupling μ ν₁ hc
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
  have hbtop : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have hfin_mix : transportCost c μ (a • ν₀ + b • ν₁) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hatop hfin₀, ENNReal.mul_ne_top hbtop hfin₁⟩) <| by
      simpa only [← add_smul, hab, one_smul, transportCost_smul hatop, transportCost_smul hbtop]
        using transportCost_add_le c (a • μ) (b • μ) (a • ν₀) (b • ν₁)
  exact TauCeti.transportCost_smul_add_smul_lt hab ha hb hπ₀ hπ₁ (fun π hπ =>
    let ⟨_, _, _, _, _, hgraph⟩ := hπ.exists_eq_graphPlan_gradient hμ hfin_mix
    ⟨_, (measurable_gradient _).aemeasurable, hgraph⟩) hne

end StrictConvexity

private theorem mem_subdifferential_norm_sq_div_two_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ψ : E → ℝ} {T : E → E}
    (hT : ∀ x z, ψ x + inner ℝ (z - x) (T x) ≤ ψ z) (x : E) :
    x + T x ∈ subdifferential (innerₗ E) (fun z => ((‖z‖ ^ 2 / 2 + ψ z : ℝ) : EReal)) x := by
  refine (mem_subdifferential_iff _).2 ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, fun z => ?_⟩
  rw [innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_add_right, inner_sub_left,
    real_inner_self_eq_norm_sq]
  have hsq : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _; rw [norm_sub_sq_real] at hsq; linarith [hT x z]

private theorem ne_graphPlan_of_smul_graphPlan_add {E : Type*} [MeasurableSpace E]
    [MeasurableEq E] {μ : Measure E} [IsProbabilityMeasure μ] {B : Set E}
    (hμB : μ B ≠ 0) {S₁ S₂ : E → E} (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (hBne : ∀ x ∈ B, S₁ x ≠ S₂ x) (T : E → E) :
    (2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ ≠ graphPlan T μ := fun hEq => by
  obtain ⟨T', μ', hT', hT'eq⟩ : ∃ (T' : E → E) (μ' : Measure E),
      AEMeasurable T' μ' ∧ graphPlan T μ = graphPlan T' μ' := by
    by_cases hT : AEMeasurable T μ
    · exact ⟨T, μ, hT, rfl⟩
    · have : Nonempty E := nonempty_of_isProbabilityMeasure μ
      let z₀ : E × E := Classical.ofNonempty
      refine ⟨fun _ => z₀.2, Measure.dirac z₀.1, measurable_const.aemeasurable, ?_⟩
      rw [graphPlan_def, Measure.map_of_not_aemeasurable_of_ne_zero
        (fun h => hT (by simpa [Function.comp_def] using measurable_snd.comp_aemeasurable h))
        (IsProbabilityMeasure.ne_zero μ), graphPlan_dirac measurable_const.aemeasurable]
  have heq {S : E → E} (hS : Measurable S) (hle : (2⁻¹ : ℝ≥0∞) • graphPlan S μ ≤ graphPlan T μ) :
      graphPlan S μ = graphPlan T' μ := by
    simpa [fst_graphPlan hS.aemeasurable] using eq_graphPlan_of_absolutelyContinuous hT' <|
      (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)).trans <|
        Measure.absolutelyContinuous_of_le (hle.trans_eq hT'eq)
  have hae : S₁ =ᵐ[μ] S₂ := (graphPlan_eq_graphPlan_iff hS₁.aemeasurable hS₂.aemeasurable).1 <|
    (heq hS₁ ((Measure.le_add_right le_rfl).trans_eq hEq)).trans
      (heq hS₂ ((Measure.le_add_left le_rfl).trans_eq hEq)).symm
  exact hμB (measure_mono_null (fun x hx => hBne x hx) (ae_iff.1 hae))

section SharpCharacterization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Converse splitting construction for non-regular sources (Ambrosio–Gigli Theorem 1.26,
necessity).** If a probability measure `μ` of finite second moment on a finite-dimensional real
inner product space `E` is *not* `c - c`-regular, then there exist a probability measure `ν` on `E`
with `MemLp id 2 ν` and a quadratic optimal coupling `π` between `μ` and `ν` that is not of the form
`graphPlan T μ` for any map `T : E → E`. -/
theorem exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular {μ : Measure E}
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hnot : ¬ IsCCRegular μ) :
    ∃ (ν : Measure E) (_ : IsProbabilityMeasure ν) (_ : MemLp id 2 ν) (π : Measure (E × E)),
      IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ∧
        ∀ T : E → E, π ≠ graphPlan T μ := by
  have : MeasurableEq E := ⟨isClosed_diagonal.measurableSet⟩
  simp only [isCCRegular_def, not_forall] at hnot; obtain ⟨s, hs, hμs⟩ := hnot
  obtain ⟨N, hμB⟩ : ∃ N : ℕ, μ (s ∩ closedBall 0 N) ≠ 0 := by
    by_contra! hall
    exact hμs ((Metric.iUnion_inter_closedBall_nat s 0).symm ▸ measure_iUnion_null hall)
  obtain ⟨K, ψ, T₁, T₂, -, -, hT₁m, hT₂m, hT₁s, hT₂s, hT₁n, hT₂n, hTne⟩ :=
    hs.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne (N : ℝ)
  let S₁ : E → E := fun x => x + T₁ x; let S₂ : E → E := fun x => x + T₂ x
  have hS₁m : Measurable S₁ := measurable_id.add hT₁m
  have hS₂m : Measurable S₂ := measurable_id.add hT₂m
  have hlp {T : E → E} (hTm : Measurable T) (hTn : ∀ x, ‖T x‖ ≤ K) :
      MemLp id 2 (μ.map (fun x => x + T x)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (measurable_id.add hTm).aemeasurable).2
      (hμ2.add (MemLp.of_bound hTm.aestronglyMeasurable K (.of_forall hTn)))
  let ν : Measure E := (2⁻¹ : ℝ≥0∞) • μ.map S₁ + (2⁻¹ : ℝ≥0∞) • μ.map S₂
  have hν2 : MemLp id 2 ν :=
    ((hlp hT₁m hT₁n).smul_measure (ENNReal.inv_ne_top.2 two_ne_zero)).add_measure
      ((hlp hT₂m hT₂n).smul_measure (ENNReal.inv_ne_top.2 two_ne_zero))
  have hπ : IsCoupling ((2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ) μ ν := by
    have h := ((isCoupling_graphPlan_map (μ := μ) hS₁m.aemeasurable).smul (2⁻¹ : ℝ≥0∞)).add
      ((isCoupling_graphPlan_map (μ := μ) hS₂m.aemeasurable).smul (2⁻¹ : ℝ≥0∞))
    rwa [← add_smul, ENNReal.inv_two_add_inv_two, one_smul] at h
  have hsub {T : E → E} (hTm : Measurable T) (hTs : ∀ x z, ψ x + inner ℝ (z - x) (T x) ≤ ψ z) :
      ∀ᵐ z ∂(2⁻¹ : ℝ≥0∞) • graphPlan (fun x => x + T x) μ,
        z.2 ∈ subdifferential (innerₗ E) (fun w => ((‖w‖ ^ 2 / 2 + ψ w : ℝ) : EReal)) z.1 :=
    Measure.ae_smul_measure ((ae_snd_eq_graphPlan (measurable_id.add hTm).aemeasurable).mono
      fun z hz => hz ▸ mem_subdifferential_norm_sq_div_two_add hTs z.1) _
  exact ⟨ν, ⟨by simp [ν, smul_eq_mul, ENNReal.inv_two_add_inv_two]⟩, hν2, _,
    hπ.isOptimalCoupling_of_ae_mem_subdifferential hμ2 hν2
      (ae_add_measure_iff.2 ⟨hsub hT₁m hT₁s, hsub hT₂m hT₂s⟩),
    ne_graphPlan_of_smul_graphPlan_add hμB hS₁m hS₂m
      (fun x hx hEq => hTne x hx (add_left_cancel hEq))⟩

/-- **Ambrosio–Gigli Theorem 1.26 (determinism of all optimal plans).** Let `μ` be a probability
measure with `MemLp id 2 μ` on a finite-dimensional real inner product space `E`. Then `μ` is
`c - c`-regular if and only if for every probability measure `ν` on `E` with `MemLp id 2 ν`, every
optimal quadratic coupling between `μ` and `ν` is induced by a transport map. -/
theorem isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan {μ : Measure E}
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) :
    IsCCRegular μ ↔
      ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν →
        ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν →
          ∃ T : E → E, π = graphPlan T μ := by
  refine ⟨fun hμ ν _ hν2 π hπ => ?_, fun hall => by_contra fun hnot => ?_⟩
  · have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
      rw [← hπ.lintegral_eq, hπ.toIsCoupling.lintegral_norm_sub_sq_div_two hμ2 hν2]
      exact ENNReal.ofReal_ne_top
    exact let ⟨_, _, _, _, _, hgraph⟩ := hπ.exists_eq_graphPlan_gradient hμ hfin; ⟨_, hgraph⟩
  · obtain ⟨ν, hνp, hν2, π, hπ, hne⟩ :=
      exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular hμ2 hnot
    exact let ⟨T, hT⟩ := @hall ν hνp hν2 π hπ; hne T hT

/-- **Ambrosio–Gigli Theorem 1.26 (existence of a unique, map-induced optimal plan).** Let `μ` be a
probability measure with `MemLp id 2 μ` on a finite-dimensional real inner product space `E`. Then
`μ` is `c - c`-regular if and only if for every probability measure `ν` on `E` with `MemLp id 2 ν`,
there exists an optimal transport map `T : E → E` from `μ` to `ν` whose graph plan `graphPlan T μ`
is the unique optimal quadratic coupling between `μ` and `ν`. -/
theorem
  isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling
    {μ : Measure E} [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) :
    IsCCRegular μ ↔
      ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν →
        ∃ T : E → E,
          IsKantorovichOptimalTransportMap
            (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν T ∧
          ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ↔
            π = graphPlan T μ := by
  refine ⟨fun hμ ν _ hν2 => ?_, fun hall =>
    (isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan hμ2).2
      fun ν _ hν2 π hπ => let ⟨T, _, hiff⟩ := hall ν hν2; ⟨T, (hiff π).1 hπ⟩⟩
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ :=
    ne_top_of_le_ne_top ((isCoupling_prod μ ν).lintegral_norm_sub_sq_div_two hμ2 hν2 ▸
      ENNReal.ofReal_ne_top) (transportCost_le_lintegral (isCoupling_prod μ ν) _)
  exact let ⟨_, _, _, _, _, hT, hiff, _⟩ := exists_isKantorovichOptimalTransportMap_gradient hμ hfin
    ⟨_, hT, hiff⟩

namespace WassersteinSpace

/-- **Ambrosio–Gigli Theorem 1.26 on `WassersteinSpace 2 E` (determinism form).** A quadratic
Wasserstein law `μ : WassersteinSpace 2 E` has `c - c`-regular underlying measure iff for every
target `ν : WassersteinSpace 2 E`, every optimal quadratic coupling is induced by a transport
map. -/
theorem isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan (μ : WassersteinSpace 2 E) :
    IsCCRegular ((μ : ProbabilityMeasure E) : Measure E) ↔
      ∀ (ν : WassersteinSpace 2 E) (π : Measure (E × E)),
        IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
          ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
        ∃ T : E → E, π = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan μ.hasFiniteMoment.memLp_id]
  refine ⟨fun h ν π hπ => h _ ν.hasFiniteMoment.memLp_id π hπ, fun h ν _ hν2 π hπ => ?_⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hmk := h (WassersteinSpace.mk νP (hasFiniteMoment_of_memLp_id hν2)) π
  rw [WassersteinSpace.coe_mk] at hmk; exact hmk hπ

/-- **Ambrosio–Gigli Theorem 1.26 on `WassersteinSpace 2 E` (existence and uniqueness form).** A
quadratic Wasserstein law `μ : WassersteinSpace 2 E` has `c - c`-regular underlying measure iff for
every target `ν : WassersteinSpace 2 E`, there exists an optimal transport map `T` whose graph plan
is the unique optimal quadratic coupling between `μ` and `ν`. -/
theorem isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling
    (μ : WassersteinSpace 2 E) :
    IsCCRegular ((μ : ProbabilityMeasure E) : Measure E) ↔
      ∀ ν : WassersteinSpace 2 E,
        ∃ T : E → E,
          IsKantorovichOptimalTransportMap
            (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
            ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) T ∧
          ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
            ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) ↔
            π = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [
  isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling
    μ.hasFiniteMoment.memLp_id]
  refine ⟨fun h ν => h _ ν.hasFiniteMoment.memLp_id, fun h ν _ hν2 => ?_⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hmk := h (WassersteinSpace.mk νP (hasFiniteMoment_of_memLp_id hν2))
  rw [WassersteinSpace.coe_mk] at hmk; exact hmk

end WassersteinSpace

end SharpCharacterization

end TauCeti
