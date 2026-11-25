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
  (`SimpleGraph.dimerBoltzmann_one`). These are the kernels of the dimer specification.
* A measure `μ` on configurations is **dimer Gibbs** for `w` (`SimpleGraph.IsDimerGibbs`) when it
  is a probability measure, the configurations that are not dimer configurations are `μ`-null,
  and for dimer configurations `ω`, `ω'` agreeing off a finite set `F`, and every finite `E`
  containing the edges that share a vertex with an edge of `F`, the cylinder identity
  `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E` holds, `[ω]_E` being the cylinder of the
  configurations agreeing with `ω` on `E`. This form needs no conditional probability.

**Gauge invariance.** Replacing `w(uv)` by `w(uv) g(u) g(v)` for a positive `g`
(`SimpleGraph.gaugeWeight`) multiplies `w(ω ∩ F)` by the product of `g` over the vertices covered
by the edges of `F` of value `true` (`SimpleGraph.dimerWeight_gaugeWeight`). For dimer
configurations agreeing off `F` these vertices are the same: they are the endpoints of edges of
`F` that are not covered by an edge outside `F` (`SimpleGraph.dimerCoveredVertices_eq`). So the
Boltzmann laws (`SimpleGraph.dimerBoltzmann_gaugeWeight`) and the dimer Gibbs measures
(`SimpleGraph.isDimerGibbs_gaugeWeight_iff`) do not change: weights are not determined by the
specification.

## References

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

/-! ### The dimer Boltzmann law -/

variable (G) in
/-- The partition function `Z^w_F(ω)`: the total weight `∑ w(ω' ∩ F)` of the completion set
`Ω_F(ω)`. -/
def dimerPartitionFunction (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    ℝ :=
  ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, G.dimerWeight w F ω'

variable (G) in
/-- **The dimer Boltzmann law** `γ^w_F(· | ω)`: the measure on the completion set `Ω_F(ω)` with
masses `w(ω' ∩ F) / Z^w_F(ω)`. -/
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
  simp only [dimerBoltzmann_def, dimerPartitionFunction]
  congr 1 <;> simp only [h']

theorem dimerPartitionFunction_pos {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    0 < G.dimerPartitionFunction w F ω :=
  Finset.sum_pos (fun ω' _ => dimerWeight_pos hw F ω')
    ⟨ω, (Finite.mem_toFinset _).2 (mem_dimerCompletionSet_self hω)⟩

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
    ← Finset.sum_div]
  change ENNReal.ofReal (G.dimerPartitionFunction w F ω / _) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

/-- For `w ≡ 1` the Boltzmann law is uniform on the completion set. -/
theorem dimerBoltzmann_one (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerBoltzmann 1 F ω = ((G.finite_dimerCompletionSet F ω).toFinset.card : ℝ≥0∞)⁻¹ •
      ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, Measure.dirac ω' := by
  rw [dimerBoltzmann_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [dimerWeight_one, dimerPartitionFunction]
  simp only [dimerWeight_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [one_div, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 (Finset.card_pos.2 ⟨ω', ‹_›⟩)),
    ENNReal.ofReal_natCast]

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

/-! ### Gauge invariance -/

variable (G) in
/-- The vertices covered by the edges of `F` of value `true` under `ω`. -/
def dimerCoveredVertices [DecidableEq V] (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    Finset V :=
  (F.filter fun e => ω e = true).biUnion fun e => (e : Sym2 V).toFinset

theorem mem_dimerCoveredVertices [DecidableEq V] {F : Finset G.edgeSet} {ω : G.edgeSet → Bool}
    {v : V} : v ∈ G.dimerCoveredVertices F ω ↔ ∃ e ∈ F, ω e = true ∧ v ∈ (e : Sym2 V) := by
  simp [dimerCoveredVertices, and_assoc]

/-- For a dimer configuration, a vertex is covered by an edge of `F` of value `true` exactly when
it is an endpoint of an edge of `F` and not covered by an edge outside `F`. -/
private theorem mem_dimerCoveredVertices_iff [DecidableEq V] {F : Finset G.edgeSet}
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) {v : V} :
    v ∈ G.dimerCoveredVertices F ω ↔
      (∃ f ∈ F, v ∈ (f : Sym2 V)) ∧ ∀ e ∉ F, ω e = true → v ∉ (e : Sym2 V) := by
  rw [mem_dimerCoveredVertices]
  obtain ⟨e₀, he₀, huniq⟩ := isDimerConfiguration_iff.1 hω v
  constructor
  · rintro ⟨e, heF, hωe, hve⟩
    refine ⟨⟨e, heF, hve⟩, fun e' he'F hωe' hve' => he'F ?_⟩
    rw [huniq e' ⟨hωe', hve'⟩, ← huniq e ⟨hωe, hve⟩]
    exact heF
  · rintro ⟨-, hout⟩
    by_cases h : e₀ ∈ F
    · exact ⟨e₀, h, he₀⟩
    · exact absurd he₀.2 (hout e₀ h he₀.1)

/-- **The covered vertices are determined off `F`.** Two dimer configurations agreeing off `F`
cover the same vertices by edges of `F`. -/
theorem dimerCoveredVertices_eq [DecidableEq V] {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool}
    (hω : G.IsDimerConfiguration ω) (hω' : G.IsDimerConfiguration ω')
    (h : ∀ e ∉ F, ω e = ω' e) : G.dimerCoveredVertices F ω = G.dimerCoveredVertices F ω' := by
  ext v
  rw [mem_dimerCoveredVertices_iff hω, mem_dimerCoveredVertices_iff hω']
  exact and_congr_right fun _ => forall₂_congr fun e he => by rw [h e he]

variable (G) in
/-- The gauge transform `w(uv) g(u) g(v)` of an edge weight `w` by a vertex function `g`. -/
def gaugeWeight (w : G.edgeSet → ℝ) (g : V → ℝ) (e : G.edgeSet) : ℝ :=
  w e * Sym2.lift ⟨fun u v => g u * g v, fun _ _ => mul_comm _ _⟩ (e : Sym2 V)

theorem gaugeWeight_apply (w : G.edgeSet → ℝ) (g : V → ℝ) (e : G.edgeSet) :
    G.gaugeWeight w g e =
      w e * Sym2.lift ⟨fun u v => g u * g v, fun _ _ => mul_comm _ _⟩ (e : Sym2 V) :=
  (rfl)

/-- **The gauge factor.** For a dimer configuration, the gauge transform multiplies `w(ω ∩ F)` by
the product of `g` over the vertices covered by the edges of `F` of value `true`. -/
theorem dimerWeight_gaugeWeight [DecidableEq V] (w : G.edgeSet → ℝ) (g : V → ℝ)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    G.dimerWeight (G.gaugeWeight w g) F ω =
      G.dimerWeight w F ω * ∏ v ∈ G.dimerCoveredVertices F ω, g v := by
  simp_rw [dimerWeight_def, gaugeWeight_apply]
  rw [Finset.prod_mul_distrib, dimerCoveredVertices,
    Finset.prod_biUnion]
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

/-- **Gauge invariance of the Boltzmann laws.** For a dimer configuration `ω` and a positive `g`,
the gauge transform of the weight has the same Boltzmann law `γ^w_F(· | ω)`. -/
theorem dimerBoltzmann_gaugeWeight (w : G.edgeSet → ℝ) {g : V → ℝ} (hg : ∀ v, 0 < g v)
    (F : Finset G.edgeSet) {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    G.dimerBoltzmann (G.gaugeWeight w g) F ω = G.dimerBoltzmann w F ω := by
  classical
  set c := ∏ v ∈ G.dimerCoveredVertices F ω, g v
  have hc : 0 < c := Finset.prod_pos fun v _ => hg v
  have hweight : ∀ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
      G.dimerWeight (G.gaugeWeight w g) F ω' = G.dimerWeight w F ω' * c := by
    intro ω' hω'
    rw [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
    rw [dimerWeight_gaugeWeight w g F hω'.1,
      dimerCoveredVertices_eq hω'.1 hω fun e he => hω'.2 e he]
  have hZ : G.dimerPartitionFunction (G.gaugeWeight w g) F ω =
      G.dimerPartitionFunction w F ω * c := by
    rw [dimerPartitionFunction, dimerPartitionFunction, Finset.sum_mul]
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
  rw [dimerWeight_gaugeWeight w g F hω, dimerWeight_gaugeWeight w g F hω',
    ← dimerCoveredVertices_eq hω hω' h, ENNReal.ofReal_mul' hc.le, ENNReal.ofReal_mul' hc.le,
    mul_right_comm, mul_right_comm (ENNReal.ofReal (G.dimerWeight w F ω)),
    mul_comm _ (ENNReal.ofReal c), mul_comm _ (ENNReal.ofReal c),
    ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top]

end SimpleGraph
