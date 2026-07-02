module

public import TauCeti.Probability.DeFinetti.DirectingMeasureCoord
public import TauCeti.Probability.Exchangeability.Cylinder
public import TauCeti.Probability.Exchangeability.ConditionallyIID
public import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.DeFinetti.CommonEnding

/-!
# Block-product factorisation of the conditional expectation

Given that the selected coordinates of a contractable process are conditionally independent over the
tail σ-algebra, the conditional expectation of a block-indicator product factors as a product of the
directing measure on the coordinate sets:
```
μ[blockIndicatorProd X k C | tailProcess X] =ᵐ fun ω => ∏ i, (directingMeasure μ X ω).real (C i).
```
This chains Mathlib's `iCondIndepFun_iff_condExp_inter_preimage_eq_mul` (conditional independence ⟺
product of indicator conditional expectations) with
`Contractable.directingMeasure_ae_eq_condExp_coord` (each coordinate's conditional law is the
directing measure). It is the conditional-expectation core of the de Finetti common ending.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- **Block-product factorisation of the conditional expectation.** If the selected coordinates
`fun i => X (k i)` are conditionally independent given the tail, then the conditional expectation of
the block-indicator product factors as `∏ i, (directingMeasure μ X ·).real (C i)`. -/
theorem condExp_blockIndicatorProd_ae_eq_prod [StandardBorelSpace Ω] [StandardBorelSpace α]
    [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) (hTail : tailProcess X ≤ mΩ)
    {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} (hC : ∀ i, MeasurableSet (C i))
    (hCI : iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
      (tailProcess X) hTail (fun i => X (k i)) μ) :
    μ[blockIndicatorProd X k C | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (directingMeasure μ X ω).real (C i) := by
  -- The CI factorisation on the full selection `S = univ`, sets `C`.
  have hfac := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (fun _ : Fin m => (inferInstance : MeasurableSpace α)) (fun i => X (k i))
    (fun i => hX_meas (k i))).1 hCI Finset.univ (sets := C) (fun i _ => hC i)
  -- The intersection over the selection is the block cylinder.
  have hcyl : ⋂ i ∈ (Finset.univ : Finset (Fin m)), X (k i) ⁻¹' C i = blockCylinder X k C := by
    ext ω; simp [mem_blockCylinder, Set.mem_iInter, Set.mem_preimage]
  rw [hcyl] at hfac
  -- Goal LHS = `μ⟦blockCylinder X k C | tail⟧`, the block-indicator conditional expectation.
  rw [blockIndicatorProd_eq_indicator]
  refine hfac.trans ?_
  -- Each factor is the directing measure on `C i`, by the per-coordinate conditional law (brick A).
  have hfactor : ∀ i, (μ⟦X (k i) ⁻¹' C i | tailProcess X⟧)
      =ᵐ[μ] fun ω => (directingMeasure μ X ω).real (C i) := by
    intro i
    have hind : (X (k i) ⁻¹' C i).indicator (fun ω => (1 : ℝ))
        = Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X (k i) := by
      funext ω; by_cases h : X (k i) ω ∈ C i <;> simp [Set.indicator, Set.mem_preimage, h]
    rw [hind]
    exact (hX.directingMeasure_ae_eq_condExp_coord hX_meas hTail (k i) (hC i)).symm
  have key : ∀ᵐ ω ∂μ, ∀ i, (μ⟦X (k i) ⁻¹' C i | tailProcess X⟧) ω
      = (directingMeasure μ X ω).real (C i) := ae_all_iff.mpr hfactor
  filter_upwards [key] with ω hω
  rw [Finset.prod_apply]
  exact Finset.prod_congr rfl fun i _ => hω i

/-- **Block law of a rectangle as a directing-measure mixture** (given tail conditional
independence). The block law of the rectangle `∏ᵢ C i` is the `μ`-average of the directing-measure
product `∏ i, directingMeasure μ X ω (C i)`. -/
theorem blockLaw_eq_lintegral_prod_directingMeasure [StandardBorelSpace Ω] [StandardBorelSpace α]
    [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) (hTail : tailProcess X ≤ mΩ)
    {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} (hC : ∀ i, MeasurableSet (C i))
    (hCI : iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
      (tailProcess X) hTail (fun i => X (k i)) μ) :
    blockLaw μ X k (Set.univ.pi C) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (C i) ∂μ := by
  classical
  haveI : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  set g : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (C i) with hg
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_directingMeasure_coe hTail (hC i)).ennreal_toReal
  have hg_bound : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    have hval : g ω = ∏ i, ((directingMeasure μ X ω) (C i)).toReal := by
      simp only [hg, measureReal_def]
    rw [hval, Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
    refine Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  have hg_int : Integrable g μ :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ hg_bound)
  have hbl : (blockLaw μ X k (Set.univ.pi C)).toReal = ∫ ω, g ω ∂μ := by
    rw [← integral_blockIndicatorProd (fun i => (hX_meas (k i)).aemeasurable) hC,
      ← integral_condExp hTail]
    exact integral_congr_ae (condExp_blockIndicatorProd_ae_eq_prod hX hX_meas hTail hC hCI)
  have hbl_ne : blockLaw μ X k (Set.univ.pi C) ≠ ⊤ := by
    rw [blockLaw_blockCylinder X (fun i => (hX_meas (k i)).aemeasurable) hC]
    exact measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hbl_ne, hbl,
    ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ fun ω =>
      Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine lintegral_congr fun ω => ?_
  simp only [hg, measureReal_def]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **de Finetti reduces to conditional independence over the tail.** If every finite injective
selection of coordinates of a contractable process is conditionally independent given the tail
σ-algebra, then the process is conditionally i.i.d., with directing measure the tail conditional
law `directingProbabilityMeasure μ X`. -/
theorem conditionallyIID_of_iCondIndepFun_tailProcess [StandardBorelSpace Ω] [StandardBorelSpace α]
    [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) (hTail : tailProcess X ≤ mΩ)
    (hCI : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
        (tailProcess X) hTail (fun i => X (k i)) μ) :
    ConditionallyIID μ X := by
  refine conditionallyIID_of_directing_forall_rectangles
    (measurable_directingProbabilityMeasure (μ := μ) hTail) ?_
  intro m k hk B hB
  rw [blockLaw_eq_lintegral_prod_directingMeasure hX hX_meas hTail hB (hCI m k hk)]
  refine lintegral_congr fun ω => ?_
  simp only [directingProbabilityMeasure_toMeasure]

end Probability

end TauCeti
