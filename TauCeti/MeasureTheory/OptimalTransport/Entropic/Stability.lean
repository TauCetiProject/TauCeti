/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.InformationTheory.KullbackLeibler.Variational
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.OptimalTransport.Compactness
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stability of the static Schrödinger problem

Probability marginals and the finite reference measure may vary weakly along an arbitrary
filter. Joint lower semicontinuity of relative entropy and eventual tightness of the marginal
families give the lower bound on optimal values and feasible cluster points. These filter-level
results use a pseudometrizable Borel product. Compactness requires a Hausdorff product;
uniqueness of weak marginal limits requires Hausdorff spaces of marginal probability measures.
On Polish Borel factors, convergent marginal sequences automatically supply tightness and the
results give weakly convergent subsequences. The reference need not be normalized, and the optimal
values may be infinite.

The upper bound requires approximation of each finite-entropy limiting coupling by couplings
with the exact varying marginals and an entropy `limsup` bound, explicit in
`tendsto_schroedingerValue_of_entropy_approximation`. Weak convergence of the data alone does not
supply it. Under the resulting upper bound every weak
cluster point of minimizers is optimal. A finite limiting value then gives uniqueness and
convergence of the full optimizer sequence.
For fixed marginals and reference, the constant sequence of each finite-entropy coupling supplies
the entropy approximation condition.

For the static Schrödinger problem and joint weak lower semicontinuity of entropy, see M. Nutz,
[*Introduction to Entropic Optimal Transport*][nutz], §2 and Lemma 1.3.

[nutz]: https://www.math.columbia.edu/~mnutz/docs/EOT_lecture_notes.pdf
-/

public section

open Filter InformationTheory MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {l : Filter ι} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {Rs : ι → FiniteMeasure (X × Y)} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
  {R : FiniteMeasure (X × Y)}

/-- Entropy approximation of each finite-entropy limiting coupling by plans with the exact moving
marginals gives the upper bound on Schrödinger values along any filter. Only feasibility and the
entropy bound are needed; weak convergence of the approximating plans is not required. -/
theorem limsup_schroedingerValue_le_schroedingerValue_of_entropy_approximation
    (happrox : ∀ π : ProbabilityMeasure (X × Y), IsCoupling π.toMeasure μ.toMeasure ν.toMeasure →
      klDiv π.toMeasure R.toMeasure ≠ ∞ →
      ∃ πs : ι → ProbabilityMeasure (X × Y),
        (∀ᶠ n in l, IsCoupling (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure) ∧
          limsup (fun n ↦ klDiv (πs n).toMeasure (Rs n).toMeasure) l ≤
            klDiv π.toMeasure R.toMeasure) :
    limsup (fun n ↦ schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) l ≤
      schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure := by
  refine le_schroedingerValue fun π hcoup ↦ ?_
  by_cases hfin : klDiv π R.toMeasure = ∞
  · rw [hfin]
    exact le_top
  obtain ⟨πs, hfeas, hcost⟩ := happrox ⟨π, hcoup.isProbabilityMeasure⟩ hcoup hfin
  exact (limsup_le_limsup
    (hfeas.mono fun n hn ↦ schroedingerValue_le_klDiv hn (Rs n).toMeasure)).trans hcost

section Topological

variable [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space (ProbabilityMeasure X)]
  [TopologicalSpace Y] [OpensMeasurableSpace Y] [T2Space (ProbabilityMeasure Y)]
  [TopologicalSpace.PseudoMetrizableSpace (X × Y)] [BorelSpace (X × Y)]

/-- With eventually tight marginal families, the Schrödinger value satisfies the lower
`liminf` bound along any filter. No finite-entropy feasibility hypothesis is needed. -/
theorem schroedingerValue_le_liminf_schroedingerValue_of_isTightMeasureSet [T2Space (X × Y)]
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hR : Tendsto Rs l (𝓝 R)) :
    schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure ≤
      liminf (fun n ↦
        schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) l := by
  classical
  by_contra hcon
  obtain ⟨a, ha₁, ha₂⟩ := exists_between (not_le.mp hcon)
  have hfreq : ∃ᶠ n in l,
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure < a :=
    frequently_lt_of_liminf_lt (h := ha₁)
  have hchoice : ∀ n, ∃ σ : ProbabilityMeasure (X × Y),
      IsCoupling σ.toMeasure (μs n).toMeasure (νs n).toMeasure ∧
        (schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure < a →
          klDiv σ.toMeasure (Rs n).toMeasure < a) := by
    intro n
    by_cases hn : schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure < a
    · obtain ⟨σ, hσ, hσa⟩ := schroedingerValue_lt_iff.mp hn
      exact ⟨⟨σ, hσ.isProbabilityMeasure⟩, hσ, fun _ ↦ hσa⟩
    · exact ⟨(Coupling.prod (μs n) (νs n)).1, (Coupling.prod (μs n) (νs n)).2,
        fun h ↦ absurd h hn⟩
  choose πs hπs hπsa using hchoice
  let lb := l ⊓ 𝓟 {n | schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure < a}
  have : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have hmem : ∀ᶠ n in lb,
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure < a :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hn ↦ hn)
  obtain ⟨l, π, hne, hle, hπ, hcoup⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := lb)
    (by obtain ⟨s, hs, ht⟩ := hμt; exact ⟨s, mem_inf_of_left hs, ht⟩)
    (by obtain ⟨s, hs, ht⟩ := hνt; exact ⟨s, mem_inf_of_left hs, ht⟩)
    (hμ.mono_left inf_le_left) (hν.mono_left inf_le_left) (Eventually.of_forall hπs)
  have := hne
  have hweak := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto π |>.comp hπ).prodMk_nhds
    (hR.mono_left (hle.trans inf_le_left))
  have hent : klDiv π.toMeasure R.toMeasure ≤
      liminf (fun n ↦ klDiv (πs n).toMeasure (Rs n).toMeasure) l :=
    (lowerSemicontinuous_klDiv_finiteMeasure.le_liminf (π.toFiniteMeasure, R)).trans
      hweak.liminf_le_liminf_comp
  have hbd : liminf (fun n ↦ klDiv (πs n).toMeasure (Rs n).toMeasure) l ≤ a :=
    (liminf_le_liminf ((hmem.filter_mono hle).mono fun n hn ↦ (hπsa n hn).le)).trans
      (le_of_eq (liminf_const a))
  exact (not_le.mpr ha₂) ((schroedingerValue_le_klDiv hcoup R.toMeasure).trans (hent.trans hbd))

/-- An eventually feasible family with eventually tight marginals has a feasible weak limit
along a nontrivial refinement. Its entropy is bounded by the `liminf` along that refinement. -/
theorem exists_isCoupling_tendsto_klDiv_le_liminf_of_isTightMeasureSet [T2Space (X × Y)]
    [l.NeBot]
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hR : Tendsto Rs l (𝓝 R)) {πs : ι → ProbabilityMeasure (X × Y)}
    (hπs : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l' : Filter ι) (π : ProbabilityMeasure (X × Y)), l'.NeBot ∧ l' ≤ l ∧
      Tendsto πs l' (𝓝 π) ∧ IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ∧
        klDiv π.toMeasure R.toMeasure ≤
          liminf (fun i ↦ klDiv (πs i).toMeasure (Rs i).toMeasure) l' := by
  obtain ⟨l', π, hne, hle, hπ, hcoup⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    hμt hνt hμ hν hπs
  have := hne
  refine ⟨l', π, hne, hle, hπ, hcoup, ?_⟩
  have hweak := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto π |>.comp hπ).prodMk_nhds
    (hR.mono_left hle)
  exact (lowerSemicontinuous_klDiv_finiteMeasure.le_liminf (π.toFiniteMeasure, R)).trans
    hweak.liminf_le_liminf_comp

/-- Eventual marginal tightness and approximation of each finite-entropy limiting coupling by
couplings of the exact moving marginals imply convergence of Schrödinger values along any filter.
The limiting value may be infinite. -/
theorem tendsto_schroedingerValue_of_entropy_approximation_of_isTightMeasureSet
    [T2Space (X × Y)]
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) (hR : Tendsto Rs l (𝓝 R))
    (happrox : ∀ π : ProbabilityMeasure (X × Y), IsCoupling π.toMeasure μ.toMeasure ν.toMeasure →
      klDiv π.toMeasure R.toMeasure ≠ ∞ →
      ∃ πs : ι → ProbabilityMeasure (X × Y),
        (∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) ∧
          limsup (fun i ↦ klDiv (πs i).toMeasure (Rs i).toMeasure) l ≤
            klDiv π.toMeasure R.toMeasure) :
    Tendsto (fun i ↦ schroedingerValue (Rs i).toMeasure (μs i).toMeasure (νs i).toMeasure) l
      (𝓝 (schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure)) :=
  tendsto_of_le_liminf_of_limsup_le
    (schroedingerValue_le_liminf_schroedingerValue_of_isTightMeasureSet hμt hνt hμ hν hR)
    (limsup_schroedingerValue_le_schroedingerValue_of_entropy_approximation happrox)

/-- Every weak limit of moving entropy minimizers along a nontrivial refinement is optimal
when the moving values have the explicit `limsup` upper bound. No finiteness is needed. -/
theorem isCoupling_klDiv_eq_schroedingerValue_of_tendsto
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hR : Tendsto Rs l (𝓝 R))
    (hval : limsup (fun n ↦
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) l ≤
      schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure)
    {l' : Filter ι} [l'.NeBot] (hle : l' ≤ l)
    {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hfeas : ∀ᶠ n in l', IsCoupling (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hopt : ∀ᶠ n in l', klDiv (πs n).toMeasure (Rs n).toMeasure =
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hπ : Tendsto πs l' (𝓝 π)) :
    IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ∧
      klDiv π.toMeasure R.toMeasure = schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure := by
  have hcoup := isCoupling_of_tendsto hfeas hπ (hμ.mono_left hle) (hν.mono_left hle)
  have hweak := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto π |>.comp hπ).prodMk_nhds
    (hR.mono_left hle)
  have hent : klDiv π.toMeasure R.toMeasure ≤
      liminf (fun n ↦ klDiv (πs n).toMeasure (Rs n).toMeasure) l' :=
    (lowerSemicontinuous_klDiv_finiteMeasure.le_liminf (π.toFiniteMeasure, R)).trans
      hweak.liminf_le_liminf_comp
  rw [liminf_congr hopt] at hent
  exact ⟨hcoup, le_antisymm
    (hent.trans (le_trans liminf_le_limsup ((limsup_le_limsup_of_le hle).trans hval)))
    (schroedingerValue_le_klDiv hcoup R.toMeasure)⟩

/-- Moving entropy minimizers with eventually tight marginals have an optimal weak limit
along a nontrivial refinement under the explicit upper bound on values. The limiting value
may be infinite. -/
theorem exists_isCoupling_klDiv_eq_schroedingerValue_tendsto_of_isTightMeasureSet
    [T2Space (X × Y)] [l.NeBot]
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) (hR : Tendsto Rs l (𝓝 R))
    (hval : limsup (fun i ↦
      schroedingerValue (Rs i).toMeasure (μs i).toMeasure (νs i).toMeasure) l ≤
      schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure) {πs : ι → ProbabilityMeasure (X × Y)}
    (hfeas : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hopt : ∀ᶠ i in l, klDiv (πs i).toMeasure (Rs i).toMeasure =
      schroedingerValue (Rs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l' : Filter ι) (π : ProbabilityMeasure (X × Y)), l'.NeBot ∧ l' ≤ l ∧
      Tendsto πs l' (𝓝 π) ∧ IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ∧
        klDiv π.toMeasure R.toMeasure = schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨l', π, hne, hle, hconv, -⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    hμt hνt hμ hν hfeas
  have := hne
  exact ⟨l', π, hne, hle, hconv,
    isCoupling_klDiv_eq_schroedingerValue_of_tendsto hμ hν hR hval hle
      (hfeas.filter_mono hle) (hopt.filter_mono hle) hconv⟩

end Topological

section Polish

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
  {μs : ℕ → ProbabilityMeasure X} {νs : ℕ → ProbabilityMeasure Y}
  {Rs : ℕ → FiniteMeasure (X × Y)}

/-- The Schrödinger value is weakly lower semicontinuous in both marginals and the finite
reference measure. No finite-entropy feasibility hypothesis is needed. -/
theorem schroedingerValue_le_liminf_schroedingerValue
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hR : Tendsto Rs atTop (𝓝 R)) :
    schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure ≤
      liminf (fun n ↦
        schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) atTop :=
  schroedingerValue_le_liminf_schroedingerValue_of_isTightMeasureSet
    ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hμ⟩
    ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hν⟩ hμ hν hR

/-- A feasible sequence has a feasible weakly convergent subsequence, and the entropy of its
limit is bounded by the `liminf` along that subsequence. The bound concerns the selected
subsequence, not the `liminf` of the original sequence. -/
theorem exists_isCoupling_tendsto_klDiv_le_liminf
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hR : Tendsto Rs atTop (𝓝 R)) {πs : ℕ → ProbabilityMeasure (X × Y)}
    (hπs : ∀ᶠ n in atTop, IsCoupling (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure) :
    ∃ (π : ProbabilityMeasure (X × Y)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (πs ∘ φ) atTop (𝓝 π) ∧ IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ∧
        klDiv π.toMeasure R.toMeasure ≤
          liminf (fun n ↦ klDiv (πs (φ n)).toMeasure (Rs (φ n)).toMeasure) atTop := by
  obtain ⟨l, π, hne, hle, hπ, hcoup, -⟩ :=
    exists_isCoupling_tendsto_klDiv_le_liminf_of_isTightMeasureSet
      ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hμ⟩
      ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hν⟩ hμ hν hR hπs
  have := hne
  obtain ⟨φ, hφ, hconv⟩ := (hπ.mapClusterPt.mono hle).tendsto_subseq
  refine ⟨π, φ, hφ, hconv, hcoup, ?_⟩
  have hweak := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto π |>.comp hconv).prodMk_nhds
    (hR.comp hφ.tendsto_atTop)
  exact (lowerSemicontinuous_klDiv_finiteMeasure.le_liminf (π.toFiniteMeasure, R)).trans
    hweak.liminf_le_liminf_comp

/-- With approximation of each finite-entropy limiting coupling by couplings of the exact moving
marginals, the Schrödinger values converge.
The limiting value may be infinite. -/
theorem tendsto_schroedingerValue_of_entropy_approximation
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hR : Tendsto Rs atTop (𝓝 R))
    (happrox : ∀ π : ProbabilityMeasure (X × Y), IsCoupling π.toMeasure μ.toMeasure ν.toMeasure →
      klDiv π.toMeasure R.toMeasure ≠ ∞ →
      ∃ πs : ℕ → ProbabilityMeasure (X × Y),
        (∀ᶠ n in atTop, IsCoupling (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure) ∧
          limsup (fun n ↦ klDiv (πs n).toMeasure (Rs n).toMeasure) atTop ≤
            klDiv π.toMeasure R.toMeasure) :
    Tendsto (fun n ↦ schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) atTop
      (𝓝 (schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure)) :=
  tendsto_schroedingerValue_of_entropy_approximation_of_isTightMeasureSet
    ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hμ⟩
    ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hν⟩ hμ hν hR happrox

/-- Moving entropy minimizers have an optimal weakly convergent subsequence under the explicit
upper bound on the values. This also covers an infinite limiting value. -/
theorem exists_isCoupling_klDiv_eq_schroedingerValue_tendsto
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hR : Tendsto Rs atTop (𝓝 R))
    (hval : limsup (fun n ↦
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) atTop ≤
      schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure) {πs : ℕ → ProbabilityMeasure (X × Y)}
    (hfeas : ∀ᶠ n in atTop, IsCoupling (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hopt : ∀ᶠ n in atTop, klDiv (πs n).toMeasure (Rs n).toMeasure =
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) :
    ∃ (π : ProbabilityMeasure (X × Y)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (πs ∘ φ) atTop (𝓝 π) ∧
        IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ∧
      klDiv π.toMeasure R.toMeasure = schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨l, π, hne, hle, hconv, hcoup, hπval⟩ :=
    exists_isCoupling_klDiv_eq_schroedingerValue_tendsto_of_isTightMeasureSet
      ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hμ⟩
      ⟨univ, univ_mem, by simpa using isTightMeasureSet_range_of_tendsto hν⟩
      hμ hν hR hval hfeas hopt
  have := hne
  obtain ⟨φ, hφ, hπ⟩ := (hconv.mapClusterPt.mono hle).tendsto_subseq
  exact ⟨π, φ, hφ, hπ, hcoup, hπval⟩

/-- At a finite limiting value, the unique entropy minimizer is the weak limit of the full
sequence of moving minimizers, provided the explicit upper bound on the values holds. -/
theorem tendsto_of_klDiv_eq_schroedingerValue
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hR : Tendsto Rs atTop (𝓝 R))
    (hval : limsup (fun n ↦
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure) atTop ≤
      schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure)
    (hfin : schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure ≠ ∞)
    {πs : ℕ → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hfeas : ∀ᶠ n in atTop, IsCoupling (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hopt : ∀ᶠ n in atTop, klDiv (πs n).toMeasure (Rs n).toMeasure =
      schroedingerValue (Rs n).toMeasure (μs n).toMeasure (νs n).toMeasure)
    (hcoup : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure)
    (hπval : klDiv π.toMeasure R.toMeasure =
      schroedingerValue R.toMeasure μ.toMeasure ν.toMeasure) :
    Tendsto πs atTop (𝓝 π) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨σ, φ, -, hσ, hσc, hσval⟩ := exists_isCoupling_klDiv_eq_schroedingerValue_tendsto
    (hμ.comp hns) (hν.comp hns) (hR.comp hns)
    (hns.limsup_comp_le_limsup.trans hval) (hns.eventually hfeas) (hns.eventually hopt)
  have heq : σ = π := ProbabilityMeasure.toMeasure_injective
    (hσc.eq_of_klDiv_eq_schroedingerValue hcoup hσval hπval hfin)
  exact ⟨φ, heq ▸ hσ⟩

end Polish

end TauCeti
