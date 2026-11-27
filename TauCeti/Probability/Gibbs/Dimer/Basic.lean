/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Matching.Dimer
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.BigOperators.Field
import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift

/-!
# Dimer Boltzmann laws and dimer Gibbs measures

Let `G` be a simple graph and `w` a positive weight on its edges. For a finite set `F` of edges
and a configuration `ω : G.edgeSet → Bool`, the weight of `ω` on `F` is
`w(ω ∩ F) = ∏_{e ∈ F, ω e = true} w e` (`SimpleGraph.dimerWeight`).

* The **dimer Boltzmann law** `γ^w_F(· | ω)` (`SimpleGraph.dimerBoltzmann`) is the probability
  measure on the completion set `Ω_F(ω)` of `ω` (the dimer configurations agreeing with `ω` off
  `F`) with masses proportional to `w(ω' ∩ F)`. It depends on `ω` only off `F`
  (`SimpleGraph.dimerBoltzmann_congr`), is a probability measure when `ω` is a dimer configuration
  (`SimpleGraph.isProbabilityMeasure_dimerBoltzmann`) and is uniform on `Ω_F(ω)` for `w ≡ 1`
  (`SimpleGraph.dimerBoltzmann_one`). These are the kernels of the dimer specification. Its
  masses and the partition function are finite sums, over the configurations `η` on `F`, of
  functions of the gluing of `η` to `ω` off `F`
  (`SimpleGraph.dimerBoltzmann_apply_eq_sum_updateFinset`,
  `SimpleGraph.dimerPartitionFunction_eq_sum_updateFinset`), and it is carried by dimer
  configurations (`SimpleGraph.dimerBoltzmann_setOf_not_isDimerConfiguration`). If `E` contains
  every edge sharing a vertex with an edge of `F`, then for dimer configurations `ω`, `η` it gives
  the cylinder `[ω]_E` the mass `w(ω ∩ F) / Z^w_F(η)` when `η` agrees with `ω` on `E ∖ F`, and
  `0` otherwise (`SimpleGraph.dimerBoltzmann_setOf_forall_mem_eq`). The laws are consistent:
  for `Λ ⊆ Δ`, `∫ γ^w_Λ(A | ω'') dγ^w_Δ(ω'' | ω) = γ^w_Δ(A | ω)`
  (`SimpleGraph.lintegral_dimerBoltzmann_dimerBoltzmann`), since resampling `Λ` changes neither
  the weight on `Δ ∖ Λ` nor the partition function of `Λ`.
* A measure `μ` on configurations is **dimer Gibbs** for `w` (`SimpleGraph.IsDimerGibbs`) when it
  is a probability measure, the configurations that are not dimer configurations are `μ`-null,
  and for dimer configurations `ω`, `ω'` agreeing off a finite set `F`, and every finite `E`
  containing the edges that share a vertex with an edge of `F`, the cylinder identity
  `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E` holds, `[ω]_E` being the cylinder of the
  configurations agreeing with `ω` on `E`. This form needs no conditional probability. Summed
  over the completion set `Ω_F(ω)`, the cylinder identities give
  `w(ω ∩ F) / Z^w_F(ω) · μ[ω]_{E ∖ F} = μ[ω]_E`
  (`SimpleGraph.IsDimerGibbs.ofReal_mul_measure_setOf_forall_mem_notMem_eq`). Separately, for
  dimer configurations `Z^w_F(ω)` only depends on `ω` near `F`
  (`SimpleGraph.dimerPartitionFunction_congr_of_isDimerConfiguration`).

**Gauge invariance.** Replacing `w(uv)` by `w(uv) g(u) g(v)` for a positive `g`
(`SimpleGraph.gaugeWeight`) multiplies `w(ω ∩ F)` by the product of `g` over the vertices covered
by the edges of `F` of value `true` (`SimpleGraph.dimerWeight_gaugeWeight`). For dimer
configurations agreeing off `F` these vertices are the same: they are the endpoints of edges of
`F` that are not covered by an edge outside `F` (`SimpleGraph.dimerCoveredVertices_eq`). So the
Boltzmann laws (`SimpleGraph.dimerBoltzmann_gaugeWeight`) and the dimer Gibbs measures
(`SimpleGraph.isDimerGibbs_gaugeWeight_iff`) do not change: weights are not determined by the
specification.

## References

* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  Section 2.2.1.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Section 5.1.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.4.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Weights -/

/-- The weight `w(ω ∩ F)` of a configuration `ω` on a finite set `F` of edges: the product of `w`
over the edges of `F` of value `true`. -/
def dimerWeight (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) : ℝ :=
  ∏ e ∈ F with ω e = true, w e

theorem dimerWeight_def (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerWeight w F ω = ∏ e ∈ F with ω e = true, w e :=
  (rfl)

theorem dimerWeight_pos {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) (F : Finset G.edgeSet)
    (ω : G.edgeSet → Bool) : 0 < G.dimerWeight w F ω :=
  Finset.prod_pos fun e _ => hw e

@[simp]
theorem dimerWeight_one (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerWeight 1 F ω = 1 :=
  Finset.prod_const_one

/-- The weight on `F` of a configuration depends only on its values on `F`. -/
theorem dimerWeight_congr (w : G.edgeSet → ℝ) {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool}
    (h : ∀ e ∈ F, ω e = ω' e) : G.dimerWeight w F ω = G.dimerWeight w F ω' := by
  simp only [dimerWeight_def]
  exact Finset.prod_congr (Finset.filter_congr fun e he => by rw [h e he]) fun _ _ => rfl

/-- The weight on `F` of the gluing of a configuration `η` on `F` to `ω` off `F` does not depend
on `ω`. -/
theorem dimerWeight_updateFinset_congr [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    (F : Finset G.edgeSet) (ω₁ ω₂ : G.edgeSet → Bool) (η : F → Bool) :
    G.dimerWeight w F (updateFinset ω₁ F η) = G.dimerWeight w F (updateFinset ω₂ F η) :=
  dimerWeight_congr w fun e he => by
    rw [updateFinset_apply_of_mem he, updateFinset_apply_of_mem he]

/-- For `Λ ⊆ Δ`, the weight on `Δ` is the product of the weights on `Λ` and on `Δ ∖ Λ`. -/
theorem dimerWeight_eq_mul_sdiff [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    {Λ Δ : Finset G.edgeSet} (h : Λ ⊆ Δ) (ω : G.edgeSet → Bool) :
    G.dimerWeight w Δ ω = G.dimerWeight w Λ ω * G.dimerWeight w (Δ \ Λ) ω := by
  simp only [dimerWeight_def, Finset.prod_filter]
  rw [mul_comm, Finset.prod_sdiff h]

/-- The weight on a finite set `F` is a measurable function of the configuration. -/
theorem measurable_dimerWeight (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) :
    Measurable (G.dimerWeight w F) := by
  simp_rw [funext (dimerWeight_def w F), Finset.prod_filter]
  exact Finset.measurable_prod _ fun e _ => Measurable.ite
    (measurableSet_eq_fun (measurable_pi_apply e) measurable_const) measurable_const
    measurable_const

/-! ### The dimer Boltzmann law -/

variable (G) in
/-- The partition function `Z^w_F(ω)`: the total weight `∑ w(ω' ∩ F)` of the completion set
`Ω_F(ω)`. -/
def dimerPartitionFunction (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    ℝ :=
  ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, G.dimerWeight w F ω'

theorem dimerPartitionFunction_def (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.edgeSet → Bool) :
    G.dimerPartitionFunction w F ω =
      ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, G.dimerWeight w F ω' :=
  (rfl)

/-- The partition function of `F` at `ω` depends on `ω` only off `F`. -/
theorem dimerPartitionFunction_congr (w : G.edgeSet → ℝ) {F : Finset G.edgeSet}
    {ω₁ ω₂ : G.edgeSet → Bool} (h : ∀ e ∉ F, ω₁ e = ω₂ e) :
    G.dimerPartitionFunction w F ω₁ = G.dimerPartitionFunction w F ω₂ := by
  simp only [dimerPartitionFunction_def, dimerCompletionSet_congr h]

variable (G) in
/-- **The dimer Boltzmann law** `γ^w_F(· | ω)`: the measure on the completion set `Ω_F(ω)` with
masses `w(ω' ∩ F) / Z^w_F(ω)` (Kenyon–Okounkov–Sheffield, *Dimers and amoebae*, §2.2.1). -/
def dimerBoltzmann (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    Measure (G.edgeSet → Bool) :=
  ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
    ENNReal.ofReal (G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω) • Measure.dirac ω'

theorem dimerBoltzmann_def (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerBoltzmann w F ω = ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
      ENNReal.ofReal (G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω) •
        Measure.dirac ω' :=
  (rfl)

/-- The Boltzmann law `γ^w_F(· | ω)` depends on `ω` only off `F`. -/
theorem dimerBoltzmann_congr (w : G.edgeSet → ℝ) {F : Finset G.edgeSet}
    {ω₁ ω₂ : G.edgeSet → Bool} (h : ∀ e ∉ F, ω₁ e = ω₂ e) :
    G.dimerBoltzmann w F ω₁ = G.dimerBoltzmann w F ω₂ := by
  have h' := dimerCompletionSet_congr h
  simp only [dimerBoltzmann_def, dimerPartitionFunction_def]
  congr 1 <;> simp only [h']

theorem dimerPartitionFunction_pos {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    0 < G.dimerPartitionFunction w F ω :=
  Finset.sum_pos (fun ω' _ => dimerWeight_pos hw F ω')
    ⟨ω, (Finite.mem_toFinset _).2 (mem_dimerCompletionSet_self hω)⟩

/-- For a positive weight and a dimer configuration `ω`, the Boltzmann masses
`w(ω' ∩ F) / Z^w_F(ω)`, `ω' ∈ Ω_F(ω)`, sum to `1`. -/
theorem sum_dimerWeight_div_dimerPartitionFunction {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
      G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω = 1 := by
  rw [← Finset.sum_div]
  exact div_self (dimerPartitionFunction_pos hw F hω).ne'

/-- The mass of a measurable set `s` under `γ^w_F(· | ω)` is the normalized weight of the members
of the completion set in `s`. -/
theorem dimerBoltzmann_apply (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool)
    {s : Set (G.edgeSet → Bool)} (hs : MeasurableSet s) :
    G.dimerBoltzmann w F ω s = ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
      s.indicator (fun _ => ENNReal.ofReal
        (G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω)) ω' := by
  rw [dimerBoltzmann_def, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul, ← indicator_const_mul]
  simp only [Pi.one_apply, mul_one]

/-- For a positive weight and a dimer configuration `ω`, `γ^w_F(· | ω)` is a probability
measure. -/
theorem isProbabilityMeasure_dimerBoltzmann {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    IsProbabilityMeasure (G.dimerBoltzmann w F ω) := by
  constructor
  have hZ := dimerPartitionFunction_pos hw F hω
  rw [dimerBoltzmann_apply w F ω MeasurableSet.univ]
  simp only [indicator_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ω' _ => div_nonneg (dimerWeight_pos hw F ω').le hZ.le,
    sum_dimerWeight_div_dimerPartitionFunction hw F hω, ENNReal.ofReal_one]

/-- For `w ≡ 1` the Boltzmann law is uniform on the completion set. -/
theorem dimerBoltzmann_one (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerBoltzmann 1 F ω = ((G.finite_dimerCompletionSet F ω).toFinset.card : ℝ≥0∞)⁻¹ •
      ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, Measure.dirac ω' := by
  rw [dimerBoltzmann_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [dimerWeight_one, dimerPartitionFunction_def]
  simp only [dimerWeight_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [one_div, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 (Finset.card_pos.2 ⟨ω', ‹_›⟩)),
    ENNReal.ofReal_natCast]

/-! ### Sums over configurations on `F` -/

/-- **The Boltzmann masses as a sum over configurations on `F`.** The mass of a measurable set `s`
under `γ^w_F(· | ω)` is the sum, over the configurations `η` on `F` whose gluing `ω_η` to `ω` off
`F` is a dimer configuration, of `w(ω_η ∩ F) / Z^w_F(ω)` times `1_s(ω_η)`. -/
theorem dimerBoltzmann_apply_eq_sum_updateFinset [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) {s : Set (G.edgeSet → Bool)}
    (hs : MeasurableSet s)
    [DecidablePred fun η : F → Bool => G.IsDimerConfiguration (updateFinset ω F η)] :
    G.dimerBoltzmann w F ω s = ∑ η with G.IsDimerConfiguration (updateFinset ω F η),
      s.indicator (fun _ => ENNReal.ofReal (G.dimerWeight w F (updateFinset ω F η) /
        G.dimerPartitionFunction w F ω)) (updateFinset ω F η) := by
  rw [dimerBoltzmann_apply w F ω hs, sum_dimerCompletionSet_eq_sum_updateFinset]

/-- The partition function as a sum over configurations on `F`. -/
theorem dimerPartitionFunction_eq_sum_updateFinset [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    (F : Finset G.edgeSet) (ω : G.edgeSet → Bool)
    [DecidablePred fun η : F → Bool => G.IsDimerConfiguration (updateFinset ω F η)] :
    G.dimerPartitionFunction w F ω = ∑ η with G.IsDimerConfiguration (updateFinset ω F η),
      G.dimerWeight w F (updateFinset ω F η) := by
  rw [dimerPartitionFunction_def, sum_dimerCompletionSet_eq_sum_updateFinset]

/-- **Locality of the partition function.** For dimer configurations `ω₁`, `ω₂` agreeing on the
edges outside `F` that share a vertex with an edge of `F`, `Z^w_F(ω₁) = Z^w_F(ω₂)`: their
completion sets have the same restrictions to `F`. -/
theorem dimerPartitionFunction_congr_of_isDimerConfiguration (w : G.edgeSet → ℝ)
    (F : Finset G.edgeSet)
    {ω₁ ω₂ : G.edgeSet → Bool} (h₁ : G.IsDimerConfiguration ω₁) (h₂ : G.IsDimerConfiguration ω₂)
    (hF : ∀ e ∉ F, (∃ f ∈ F, ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ω₁ e = ω₂ e) :
    G.dimerPartitionFunction w F ω₁ = G.dimerPartitionFunction w F ω₂ := by
  classical
  rw [dimerPartitionFunction_eq_sum_updateFinset, dimerPartitionFunction_eq_sum_updateFinset]
  exact Finset.sum_congr
    (Finset.filter_congr fun η _ => isDimerConfiguration_updateFinset_congr h₁ h₂ hF η)
    fun η _ => dimerWeight_updateFinset_congr w F ω₁ ω₂ η

/-! ### Support -/

/-- On a locally finite graph with countably many edges, the dimer configurations form a
measurable set. -/
theorem measurableSet_setOf_isDimerConfiguration [G.LocallyFinite] [Countable G.edgeSet] :
    MeasurableSet {ω : G.edgeSet → Bool | G.IsDimerConfiguration ω} :=
  isClosed_setOf_isDimerConfiguration.measurableSet

/-- The Boltzmann law `γ^w_F(· | ω)` is carried by dimer configurations. -/
theorem dimerBoltzmann_setOf_not_isDimerConfiguration [G.LocallyFinite] [Countable G.edgeSet]
    (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerBoltzmann w F ω {ω' | ¬ G.IsDimerConfiguration ω'} = 0 := by
  have h := dimerBoltzmann_apply w F ω measurableSet_setOf_isDimerConfiguration.compl
  rw [compl_ofPred] at h
  rw [h]
  refine Finset.sum_eq_zero fun ω' hω' => indicator_of_notMem ?_ _
  simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
  simpa using hω'.1

/-! ### Cylinders -/

/-- **The Boltzmann mass of a cylinder.** Let `E` contain every edge sharing a vertex with an edge
of `F`. For dimer configurations `ω` and `η`, `γ^w_F(· | η)` gives the cylinder `[ω]_E` the mass
`w(ω ∩ F) / Z^w_F(η)` if `η` agrees with `ω` on `E ∖ F`, and `0` otherwise. -/
theorem dimerBoltzmann_setOf_forall_mem_eq (w : G.edgeSet → ℝ) {F E : Finset G.edgeSet}
    (hE : ∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E)
    {ω η : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) (hη : G.IsDimerConfiguration η) :
    G.dimerBoltzmann w F η {ζ | ∀ e ∈ E, ζ e = ω e} =
      {ζ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → ζ e = ω e}.indicator
        (fun _ => ENNReal.ofReal (G.dimerWeight w F ω / G.dimerPartitionFunction w F η)) η := by
  have hmeas : MeasurableSet {ζ : G.edgeSet → Bool | ∀ e ∈ E, ζ e = ω e} :=
    SymbolicDynamics.FullShift.measurableSet_cylinder E ω
  rw [dimerBoltzmann_apply w F η hmeas]
  by_cases hηω : ∀ e ∈ E, e ∉ F → η e = ω e
  · rw [indicator_of_mem (by exact hηω)]
    -- the gluing of `ω` on `F` to `η` off `F` is a dimer configuration
    have himg := image_restrict_dimerCompletionSet_eq hη hω fun e he ⟨f, hf, v, hve, hvf⟩ =>
      hηω e (hE f hf e ⟨v, hvf, hve⟩) he
    obtain ⟨ω', hω', hr⟩ : F.restrict ω ∈ F.restrict '' G.dimerCompletionSet F η :=
      himg ▸ ⟨ω, mem_dimerCompletionSet_self hω, rfl⟩
    have hω'F (e : G.edgeSet) (he : e ∈ F) : ω' e = ω e := congrFun hr ⟨e, he⟩
    have hmem : ω' ∈ {ζ : G.edgeSet → Bool | ∀ e ∈ E, ζ e = ω e} := fun e he => by
      by_cases hF : e ∈ F
      · exact hω'F e hF
      · exact ((mem_dimerCompletionSet.1 hω').2 e hF).trans (hηω e he hF)
    rw [Finset.sum_eq_single_of_mem ω' ((Finite.mem_toFinset _).2 hω')]
    · rw [indicator_of_mem hmem, dimerWeight_congr w hω'F]
    · intro ζ hζ hne
      refine indicator_of_notMem (fun hζE => hne (funext fun e => ?_)) _
      rw [Finite.mem_toFinset] at hζ
      by_cases hF : e ∈ F
      · exact (hζE e (hE e hF e ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩)).trans
          (hω'F e hF).symm
      · exact ((mem_dimerCompletionSet.1 hζ).2 e hF).trans
          ((mem_dimerCompletionSet.1 hω').2 e hF).symm
  · rw [indicator_of_notMem (by exact hηω)]
    refine Finset.sum_eq_zero fun ζ hζ => indicator_of_notMem (fun hζE => hηω ?_) _
    rw [Finite.mem_toFinset] at hζ
    intro e he hF
    rw [← (mem_dimerCompletionSet.1 hζ).2 e hF]
    exact hζE e he

/-! ### Consistency -/

/-- The Boltzmann law integrates a function as the weighted sum of its values on the completion
set. -/
theorem lintegral_dimerBoltzmann [Countable G.edgeSet] (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.edgeSet → Bool) (f : (G.edgeSet → Bool) → ℝ≥0∞) :
    ∫⁻ ω', f ω' ∂G.dimerBoltzmann w F ω = ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
      ENNReal.ofReal (G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω) * f ω' := by
  rw [dimerBoltzmann_def, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- For `Λ ⊆ Δ` and `ω'` in the completion set of `ω` at `Δ`, resampling `Λ` inside the Boltzmann
law of `Δ` gives back the Boltzmann mass of `ω'`:
`∑_{ω'' ∈ Ω_Λ(ω')} γ^w_Δ({ω''} | ω) γ^w_Λ({ω'} | ω'') = γ^w_Δ({ω'} | ω)`. -/
private theorem sum_dimerCompletionSet_mul_eq {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    {Λ Δ : Finset G.edgeSet} (h : Λ ⊆ Δ) (ω : G.edgeSet → Bool) {ω' : G.edgeSet → Bool}
    (hω' : G.IsDimerConfiguration ω') :
    ∑ ω'' ∈ (G.finite_dimerCompletionSet Λ ω').toFinset,
        ENNReal.ofReal (G.dimerWeight w Δ ω'' / G.dimerPartitionFunction w Δ ω) *
          ENNReal.ofReal (G.dimerWeight w Λ ω' / G.dimerPartitionFunction w Λ ω'') =
      ENNReal.ofReal (G.dimerWeight w Δ ω' / G.dimerPartitionFunction w Δ ω) := by
  classical
  set ZΔ := G.dimerPartitionFunction w Δ ω
  set K := G.dimerWeight w (Δ \ Λ) ω'
  set a := G.dimerWeight w Λ ω'
  have hZΛ := dimerPartitionFunction_pos hw Λ hω'
  have hZΔ : 0 ≤ ZΔ := by
    simp only [ZΔ, dimerPartitionFunction_def]
    exact Finset.sum_nonneg fun _ _ => (dimerWeight_pos hw Δ _).le
  have hc : 0 ≤ K / ZΔ * (a / G.dimerPartitionFunction w Λ ω') :=
    mul_nonneg (div_nonneg (dimerWeight_pos hw _ _).le hZΔ)
      (div_nonneg (dimerWeight_pos hw _ _).le hZΛ.le)
  calc ∑ ω'' ∈ (G.finite_dimerCompletionSet Λ ω').toFinset,
        ENNReal.ofReal (G.dimerWeight w Δ ω'' / ZΔ) *
          ENNReal.ofReal (a / G.dimerPartitionFunction w Λ ω'')
      = ∑ ω'' ∈ (G.finite_dimerCompletionSet Λ ω').toFinset,
          ENNReal.ofReal (G.dimerWeight w Λ ω'' *
            (K / ZΔ * (a / G.dimerPartitionFunction w Λ ω'))) := by
        refine Finset.sum_congr rfl fun ω'' hω'' => ?_
        simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω''
        rw [← ENNReal.ofReal_mul (div_nonneg (dimerWeight_pos hw _ _).le hZΔ),
          dimerPartitionFunction_congr w hω''.2, dimerWeight_eq_mul_sdiff w h,
          dimerWeight_congr w (F := Δ \ Λ) (ω' := ω') fun e he =>
            hω''.2 e (Finset.mem_sdiff.1 he).2]
        congr 1
        ring
    _ = ENNReal.ofReal (G.dimerPartitionFunction w Λ ω' *
          (K / ZΔ * (a / G.dimerPartitionFunction w Λ ω'))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun ω'' _ =>
            mul_nonneg (dimerWeight_pos hw _ _).le hc, ← Finset.sum_mul,
          dimerPartitionFunction_def]
    _ = ENNReal.ofReal (G.dimerWeight w Δ ω' / ZΔ) := by
        rw [dimerWeight_eq_mul_sdiff w h]
        congr 1
        simp only [K, a]
        field_simp

/-- **Consistency of the Boltzmann laws.** For `Λ ⊆ Δ`, resampling `Λ` from `γ^w_Λ` inside a
configuration drawn from `γ^w_Δ(· | ω)` gives `γ^w_Δ(· | ω)` back:
`∫ γ^w_Λ(A | ω'') dγ^w_Δ(ω'' | ω) = γ^w_Δ(A | ω)`. -/
theorem lintegral_dimerBoltzmann_dimerBoltzmann [Countable G.edgeSet] {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) {Λ Δ : Finset G.edgeSet} (h : Λ ⊆ Δ) (ω : G.edgeSet → Bool)
    {A : Set (G.edgeSet → Bool)} (hA : MeasurableSet A) :
    ∫⁻ ω'', G.dimerBoltzmann w Λ ω'' A ∂G.dimerBoltzmann w Δ ω = G.dimerBoltzmann w Δ ω A := by
  rw [lintegral_dimerBoltzmann, dimerBoltzmann_apply w Δ ω hA]
  simp_rw [dimerBoltzmann_apply w Λ _ hA, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := (G.finite_dimerCompletionSet Δ ω).toFinset)
    (s' := fun ω' => (G.finite_dimerCompletionSet Λ ω').toFinset) ?_]
  · refine Finset.sum_congr rfl fun ω' hω' => ?_
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
    by_cases hA' : ω' ∈ A
    · simp only [indicator_of_mem hA']
      exact sum_dimerCompletionSet_mul_eq hw h ω hω'.1
    · simp [indicator_of_notMem hA']
  · intro ω'' ω'
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, fun e he => (h4 e he).symm⟩, h3,
        fun e he => (h4 e fun hΛ => he (h hΛ)).trans (h2 e he)⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, fun e he => (h2 e fun hΛ => he (h hΛ)).trans (h4 e he)⟩, h3,
        fun e he => (h2 e he).symm⟩

/-! ### Dimer Gibbs measures -/

variable (G) in
/-- **Dimer Gibbs measures** in cylinder form: `μ` is a probability measure on configurations, the
configurations that are not dimer configurations are `μ`-null, and for dimer configurations `ω`,
`ω'` agreeing off a finite set `F` of edges and every finite `E` containing each edge that shares
a vertex with an edge of `F`, `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E`, where `[ω]_E` is the
cylinder of the configurations agreeing with `ω` on `E`. -/
def IsDimerGibbs (w : G.edgeSet → ℝ) (μ : Measure (G.edgeSet → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧ μ {ω | ¬ G.IsDimerConfiguration ω} = 0 ∧
    ∀ (F E : Finset G.edgeSet) (ω ω' : G.edgeSet → Bool),
      G.IsDimerConfiguration ω → G.IsDimerConfiguration ω' → (∀ e ∉ F, ω e = ω' e) →
      (∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E) →
      ENNReal.ofReal (G.dimerWeight w F ω') * μ {η | ∀ e ∈ E, η e = ω e} =
        ENNReal.ofReal (G.dimerWeight w F ω) * μ {η | ∀ e ∈ E, η e = ω' e}

theorem isDimerGibbs_iff {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)} :
    G.IsDimerGibbs w μ ↔ IsProbabilityMeasure μ ∧ μ {ω | ¬ G.IsDimerConfiguration ω} = 0 ∧
      ∀ (F E : Finset G.edgeSet) (ω ω' : G.edgeSet → Bool),
        G.IsDimerConfiguration ω → G.IsDimerConfiguration ω' → (∀ e ∉ F, ω e = ω' e) →
        (∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E) →
        ENNReal.ofReal (G.dimerWeight w F ω') * μ {η | ∀ e ∈ E, η e = ω e} =
          ENNReal.ofReal (G.dimerWeight w F ω) * μ {η | ∀ e ∈ E, η e = ω' e} :=
  Iff.rfl

theorem IsDimerGibbs.isProbabilityMeasure {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)}
    (h : G.IsDimerGibbs w μ) : IsProbabilityMeasure μ :=
  h.1

theorem IsDimerGibbs.measure_setOf_not_isDimerConfiguration {w : G.edgeSet → ℝ}
    {μ : Measure (G.edgeSet → Bool)} (h : G.IsDimerGibbs w μ) :
    μ {ω | ¬ G.IsDimerConfiguration ω} = 0 :=
  h.2.1

/-- A dimer Gibbs measure is carried by dimer configurations. -/
theorem IsDimerGibbs.ae_isDimerConfiguration {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)}
    (h : G.IsDimerGibbs w μ) : ∀ᵐ ω ∂μ, G.IsDimerConfiguration ω :=
  ae_iff.2 h.measure_setOf_not_isDimerConfiguration

/-- The cylinder identity `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E` of a dimer Gibbs measure. -/
theorem IsDimerGibbs.cylinder {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)}
    (h : G.IsDimerGibbs w μ) {F E : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool}
    (hω : G.IsDimerConfiguration ω) (hω' : G.IsDimerConfiguration ω')
    (hF : ∀ e ∉ F, ω e = ω' e)
    (hE : ∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E) :
    ENNReal.ofReal (G.dimerWeight w F ω') * μ {η | ∀ e ∈ E, η e = ω e} =
      ENNReal.ofReal (G.dimerWeight w F ω) * μ {η | ∀ e ∈ E, η e = ω' e} :=
  h.2.2 F E ω ω' hω hω' hF hE

/-- **The cylinder identities, summed over a completion set.** Let `μ` be dimer Gibbs for a
positive `w`, `ω` a dimer configuration and `E` a finite set containing every edge sharing a vertex
with an edge of `F`. Then `w(ω ∩ F) / Z^w_F(ω) · μ[ω]_{E ∖ F} = μ[ω]_E`. -/
theorem IsDimerGibbs.ofReal_mul_measure_setOf_forall_mem_notMem_eq {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) {μ : Measure (G.edgeSet → Bool)} (hμ : G.IsDimerGibbs w μ)
    {F E : Finset G.edgeSet}
    (hE : ∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E)
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    ENNReal.ofReal (G.dimerWeight w F ω / G.dimerPartitionFunction w F ω) *
        μ {η | ∀ e ∈ E, e ∉ F → η e = ω e} = μ {η | ∀ e ∈ E, η e = ω e} := by
  classical
  have hZ := dimerPartitionFunction_pos hw F hω
  have hFE (e : G.edgeSet) (he : e ∈ F) : e ∈ E :=
    hE e he e ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩
  -- up to a null set, `[ω]_{E ∖ F}` is the disjoint union of the `[ω']_E`, `ω' ∈ Ω_F(ω)`
  have hsplit : μ {η | ∀ e ∈ E, e ∉ F → η e = ω e} =
      ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, μ {η | ∀ e ∈ E, η e = ω' e} := by
    rw [← measure_biUnion_finset
      (f := fun ω' : G.edgeSet → Bool => {η : G.edgeSet → Bool | ∀ e ∈ E, η e = ω' e}) ?_
      fun ω' _ => by
        convert SymbolicDynamics.FullShift.measurableSet_cylinder E ω' using 1
        ext η
        exact SymbolicDynamics.FullShift.mem_cylinder.symm]
    · refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
      filter_upwards [hμ.ae_isDimerConfiguration] with η hη
      simp only [mem_ofPred_eq, mem_iUnion, exists_prop, Finite.mem_toFinset]
      constructor
      · intro hηE
        obtain ⟨ω', hω', hr⟩ : F.restrict η ∈ F.restrict '' G.dimerCompletionSet F ω :=
          image_restrict_dimerCompletionSet_eq hη hω (fun e he ⟨f, hf, v, hve, hvf⟩ =>
            hηE e (hE f hf e ⟨v, hvf, hve⟩) he) ▸ ⟨η, mem_dimerCompletionSet_self hη, rfl⟩
        refine ⟨ω', hω', fun e he => ?_⟩
        by_cases heF : e ∈ F
        · exact (congrFun hr ⟨e, heF⟩).symm
        · exact (hηE e he heF).trans ((mem_dimerCompletionSet.1 hω').2 e heF).symm
      · rintro ⟨ω', hω', hηE⟩ e he heF
        exact (hηE e he).trans ((mem_dimerCompletionSet.1 hω').2 e heF)
    · intro ω₁ h₁ ω₂ h₂ hne
      simp only [Finset.mem_coe, Finite.mem_toFinset, mem_dimerCompletionSet] at h₁ h₂
      refine Set.disjoint_left.2 fun η hη₁ hη₂ => hne (funext fun e => ?_)
      by_cases heF : e ∈ F
      · exact (hη₁ e (hFE e heF)).symm.trans (hη₂ e (hFE e heF))
      · exact (h₁.2 e heF).trans (h₂.2 e heF).symm
  -- each `[ω']_E` has mass `w(ω' ∩ F) / w(ω ∩ F) · μ[ω]_E`
  have hcyl (ω' : G.edgeSet → Bool) (hω' : ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset) :
      ENNReal.ofReal (G.dimerWeight w F ω / G.dimerPartitionFunction w F ω) *
          μ {η | ∀ e ∈ E, η e = ω' e} =
        ENNReal.ofReal (G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω) *
          μ {η | ∀ e ∈ E, η e = ω e} := by
    rw [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
    rw [div_eq_inv_mul, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hZ.le),
      ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), mul_assoc, mul_assoc,
      hμ.cylinder hω hω'.1 (fun e he => (hω'.2 e he).symm) hE]
  rw [hsplit, Finset.mul_sum, Finset.sum_congr rfl hcyl, ← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg fun ω' _ => div_nonneg (dimerWeight_pos hw F ω').le hZ.le,
    sum_dimerWeight_div_dimerPartitionFunction hw F hω, ENNReal.ofReal_one, one_mul]

/-! ### Gauge invariance -/

variable (G) in
/-- The gauge transform `w(uv) g(u) g(v)` of an edge weight `w` by a vertex function `g`. -/
def gaugeWeight (w : G.edgeSet → ℝ) (g : V → ℝ) (e : G.edgeSet) : ℝ :=
  w e * Sym2.mul ((e : Sym2 V).map g)

theorem gaugeWeight_apply (w : G.edgeSet → ℝ) (g : V → ℝ) (e : G.edgeSet) :
    G.gaugeWeight w g e = w e * Sym2.mul ((e : Sym2 V).map g) :=
  (rfl)

/-- The gauge transform of a positive weight by a positive vertex function is positive. -/
theorem gaugeWeight_pos {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) {g : V → ℝ} (hg : ∀ v, 0 < g v)
    (e : G.edgeSet) : 0 < G.gaugeWeight w g e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v => exact mul_pos (hw _) (by simpa using mul_pos (hg u) (hg v))

/-- **The gauge factor.** For a dimer configuration, the gauge transform multiplies `w(ω ∩ F)` by
the product of `g` over the vertices covered by the edges of `F` of value `true`. -/
theorem dimerWeight_gaugeWeight [DecidableEq V] (w : G.edgeSet → ℝ) (g : V → ℝ)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    G.dimerWeight (G.gaugeWeight w g) F ω =
      G.dimerWeight w F ω * ∏ v ∈ G.dimerCoveredVertices F ω, g v := by
  simp_rw [dimerWeight_def, gaugeWeight_apply]
  rw [Finset.prod_mul_distrib, dimerCoveredVertices_def, Finset.prod_biUnion]
  · congr 1
    refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := (mem_edgeSet G).1 he |>.ne
      simp [Sym2.toFinset_mk_eq, Finset.prod_pair huv]
  · intro e he e' he' hee'
    simp only [Finset.coe_filter, mem_ofPred_eq] at he he'
    refine Finset.disjoint_left.2 fun v hv hv' => hee' ?_
    rw [Sym2.mem_toFinset] at hv hv'
    obtain ⟨_, _, huniq⟩ := isDimerConfiguration_iff.1 hω v
    exact (huniq e ⟨he.2, hv⟩).trans (huniq e' ⟨he'.2, hv'⟩).symm

/-- For dimer configurations `ω` and `ω' ∈ Ω_F(ω)`, the gauge transform multiplies `w(ω' ∩ F)` by
the product of `g` over the vertices covered by the edges of `F` of value `true` under `ω`: the
gauge factor is the same across the completion set. -/
theorem dimerWeight_gaugeWeight_of_mem_dimerCompletionSet [DecidableEq V] (w : G.edgeSet → ℝ)
    (g : V → ℝ) {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool}
    (hω : G.IsDimerConfiguration ω) (hω' : ω' ∈ G.dimerCompletionSet F ω) :
    G.dimerWeight (G.gaugeWeight w g) F ω' =
      G.dimerWeight w F ω' * ∏ v ∈ G.dimerCoveredVertices F ω, g v := by
  rw [mem_dimerCompletionSet] at hω'
  rw [dimerWeight_gaugeWeight w g F hω'.1, dimerCoveredVertices_eq hω'.1 hω hω'.2]

/-- **Gauge invariance of the Boltzmann laws.** For a positive `g`, the gauge transform of the
weight has the same Boltzmann laws `γ^w_F(· | ω)`. -/
theorem dimerBoltzmann_gaugeWeight (w : G.edgeSet → ℝ) {g : V → ℝ} (hg : ∀ v, 0 < g v)
    (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerBoltzmann (G.gaugeWeight w g) F ω = G.dimerBoltzmann w F ω := by
  classical
  obtain h | ⟨ω₀, hω₀ω⟩ := (G.dimerCompletionSet F ω).eq_empty_or_nonempty
  · simp only [dimerBoltzmann_def, (G.finite_dimerCompletionSet F ω).toFinset_eq_empty.2 h,
      Finset.sum_empty]
  obtain ⟨hω₀, hω₀ω⟩ := mem_dimerCompletionSet.1 hω₀ω
  simp only [dimerBoltzmann_congr _ fun e he => (hω₀ω e he).symm]
  set c := ∏ v ∈ G.dimerCoveredVertices F ω₀, g v
  have hc : 0 < c := Finset.prod_pos fun v _ => hg v
  have hweight : ∀ ω' ∈ (G.finite_dimerCompletionSet F ω₀).toFinset,
      G.dimerWeight (G.gaugeWeight w g) F ω' = G.dimerWeight w F ω' * c := fun ω' hω' =>
    dimerWeight_gaugeWeight_of_mem_dimerCompletionSet w g hω₀ ((Finite.mem_toFinset _).1 hω')
  have hZ : G.dimerPartitionFunction (G.gaugeWeight w g) F ω₀ =
      G.dimerPartitionFunction w F ω₀ * c := by
    rw [dimerPartitionFunction_def, dimerPartitionFunction_def, Finset.sum_mul]
    exact Finset.sum_congr rfl hweight
  rw [dimerBoltzmann_def, dimerBoltzmann_def]
  refine Finset.sum_congr rfl fun ω' hω' => ?_
  rw [hweight ω' hω', hZ, mul_div_mul_right _ _ hc.ne']

/-- **Gauge invariance of dimer Gibbs measures.** For a positive `g`, a measure is dimer Gibbs for
the gauge transform of `w` exactly when it is dimer Gibbs for `w`. -/
theorem isDimerGibbs_gaugeWeight_iff {w : G.edgeSet → ℝ} {g : V → ℝ} (hg : ∀ v, 0 < g v)
    {μ : Measure (G.edgeSet → Bool)} :
    G.IsDimerGibbs (G.gaugeWeight w g) μ ↔ G.IsDimerGibbs w μ := by
  classical
  refine and_congr_right fun _ => and_congr_right fun _ => forall₄_congr fun F E ω ω' => ?_
  refine forall₄_congr fun hω hω' h _ => ?_
  set c := ∏ v ∈ G.dimerCoveredVertices F ω, g v
  have hc : 0 < c := Finset.prod_pos fun v _ => hg v
  rw [dimerWeight_gaugeWeight_of_mem_dimerCompletionSet w g hω (mem_dimerCompletionSet_self hω),
    dimerWeight_gaugeWeight_of_mem_dimerCompletionSet w g hω
      (mem_dimerCompletionSet.2 ⟨hω', fun e he => (h e he).symm⟩),
    ENNReal.ofReal_mul' hc.le, ENNReal.ofReal_mul' hc.le, mul_right_comm _ (ENNReal.ofReal c),
    mul_right_comm _ (ENNReal.ofReal c),
    ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top]

end SimpleGraph
