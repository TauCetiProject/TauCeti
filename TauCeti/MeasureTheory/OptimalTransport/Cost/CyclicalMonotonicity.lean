/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Cyclical monotonicity for transport costs

This file defines finite `c`-cyclical monotonicity for a transport cost with values in an
additive commutative monoid equipped with a comparison relation, which covers both the
extended-nonnegative costs of the primal interface and the real costs of the `c`-transform
interface. The definition is purely cost-theoretic: it does not require a measure, topology, or
duality theory. A certified plan is almost-everywhere concentrated on a cyclically monotone set,
and that set can be taken measurable as soon as the cost and both potentials are measurable.

For a continuous cost, optimality alone already forces cyclical monotonicity, on the topological
support of the plan: if finitely many points of the support could be improved by permuting their
targets, then by continuity so could all points of small neighbourhoods of them, and moving a
little mass from those neighbourhoods to the permuted pairs would lower the total cost. This is
the first step from optimality towards Kantorovich potentials, which are then built on the
support by the Rüschendorf construction. The converse, and the corresponding statements for
discontinuous costs, where concentration on a cyclically monotone set replaces the support,
require additional hypotheses.

## Main statements

* `TauCeti.IsCyclicallyMonotone` — finite `c`-cyclical monotonicity of a set of pairs;
* `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support` — the support of an optimal coupling
  of finite cost for a continuous cost `c : X × Y → ℝ≥0∞` is `c`-cyclically monotone.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, Theorem 2.3.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, in *Modelling and Optimisation
  of Flows on Networks*, Lecture Notes in Math. 2062, Springer 2013, Theorem 1.13; the
  perturbation by a product of normalized restrictions follows its proof.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 5
  (cyclical monotonicity, and Theorem 5.10).
-/
public section

noncomputable section

open Set

namespace TauCeti

universe u v w

variable {X : Type u} {Y : Type v} {M : Type w} [AddCommMonoid M]

section

variable [LE M] {c : X × Y → M}

/-- A set of pairs is `c`-*cyclically monotone* when no finite family of its points can be
improved by permuting the targets: for every finite family `(x i, y i)` in the set and every
permutation `σ`, the diagonal total cost `∑ i, c (x i, y i)` is at most the rearranged total
cost `∑ i, c (x i, y (σ i))`.

This is Villani's finite-family form of the condition. A certified plan is almost-everywhere
concentrated on a `c`-cyclically monotone set — measurably so when the cost and both potentials
are measurable; the converse and any statement about topological support need additional
hypotheses. Infinite costs allow forbidden rearrangements. -/
def IsCyclicallyMonotone (c : X × Y → M) (S : Set (X × Y)) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y), (∀ i, (x i, y i) ∈ S) →
    ∀ σ : Equiv.Perm (Fin n), ∑ i, c (x i, y i) ≤ ∑ i, c (x i, y (σ i))

/-- The defining finite-family inequality for `c`-cyclical monotonicity. -/
theorem isCyclicallyMonotone_iff {S : Set (X × Y)} :
    IsCyclicallyMonotone c S ↔
      ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y), (∀ i, (x i, y i) ∈ S) →
        ∀ σ : Equiv.Perm (Fin n), ∑ i, c (x i, y i) ≤ ∑ i, c (x i, y (σ i)) :=
  Iff.rfl

namespace IsCyclicallyMonotone

/-- Apply cyclical monotonicity to a finite family and a permutation. -/
theorem sum_le {S : Set (X × Y)} (h : IsCyclicallyMonotone c S) (n : ℕ) (x : Fin n → X)
    (y : Fin n → Y) (hmem : ∀ i, (x i, y i) ∈ S) (σ : Equiv.Perm (Fin n)) :
    ∑ i, c (x i, y i) ≤ ∑ i, c (x i, y (σ i)) :=
  isCyclicallyMonotone_iff.1 h n x y hmem σ

/-- Cyclical monotonicity passes to subsets. -/
theorem mono {S S' : Set (X × Y)} (h : IsCyclicallyMonotone c S') (hSS' : S ⊆ S') :
    IsCyclicallyMonotone c S :=
  isCyclicallyMonotone_iff.2 fun n x y hmem σ ↦
    h.sum_le n x y (fun i ↦ hSS' (hmem i)) σ

/-- **The two-point form of cyclical monotonicity.** Swapping the targets of two points of a
`c`-cyclically monotone set does not lower the total cost. -/
theorem add_le_add_swap {S : Set (X × Y)} (h : IsCyclicallyMonotone c S)
    {x₁ x₂ : X} {y₁ y₂ : Y} (h₁ : (x₁, y₁) ∈ S) (h₂ : (x₂, y₂) ∈ S) :
    c (x₁, y₁) + c (x₂, y₂) ≤ c (x₁, y₂) + c (x₂, y₁) := by
  have hmem : ∀ i, (![x₁, x₂] i, ![y₁, y₂] i) ∈ S := by
    intro i
    fin_cases i
    · simpa using h₁
    · simpa using h₂
  have := h.sum_le 2 ![x₁, x₂] ![y₁, y₂] hmem (Equiv.swap 0 1)
  simpa [Fin.sum_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right] using this

end IsCyclicallyMonotone

end

/-- The empty set is cyclically monotone for every cost. -/
@[simp]
theorem isCyclicallyMonotone_empty [Preorder M] (c : X × Y → M) :
    IsCyclicallyMonotone c (∅ : Set (X × Y)) :=
  isCyclicallyMonotone_iff.2 fun n x y hmem σ ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact absurd (hmem ⟨0, hn⟩) (Set.notMem_empty _)

section Support

open MeasureTheory
open scoped ENNReal

variable [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [OpensMeasurableSpace (X × Y)] {c : X × Y → ℝ≥0∞} {π : Measure (X × Y)} {μ : Measure X}
  {ν : Measure Y}

/-- The perturbation behind `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`. If `n`
points of the support of a finite coupling of finite cost can be improved by permuting their
targets, for a continuous cost, then moving a little mass from small neighbourhoods of the points
to the corresponding permuted pairs gives a coupling of the same marginals with smaller cost. -/
private theorem exists_isCoupling_lintegral_lt [IsFiniteMeasure π] (hc : Continuous c)
    (hπ : IsCoupling π μ ν) (hfin : ∫⁻ z, c z ∂π ≠ ∞) {n : ℕ} {x : Fin n → X} {y : Fin n → Y}
    (hmem : ∀ i, (x i, y i) ∈ π.support) (σ : Equiv.Perm (Fin n))
    (hlt : ∑ i, c (x i, y (σ i)) < ∑ i, c (x i, y i)) :
    ∃ π' : Measure (X × Y), IsCoupling π' μ ν ∧ ∫⁻ z, c z ∂π' < ∫⁻ z, c z ∂π := by
  -- Outline: find open neighbourhoods `W i` of the points on which the permuted cost stays
  -- smaller; sample independently from the normalized restrictions `ρ i` of `π` to them; remove
  -- the mass `t • ∑ ρ i` from `π` and put back the laws of the permuted sampled pairs, scaled by
  -- `t`. The marginals do not change, and integrating over the sample shows that the cost drops.
  have hcm : Measurable c := hc.measurable
  -- The permuted and the diagonal total cost of a family of `n` pairs.
  let F : (Fin n → X × Y) → ℝ≥0∞ := fun w ↦ ∑ i, c ((w i).1, (w (σ i)).2)
  let G : (Fin n → X × Y) → ℝ≥0∞ := fun w ↦ ∑ i, c (w i)
  have hFc : Continuous F := continuous_finsetSum _ fun i _ ↦
    hc.comp ((continuous_apply i).fst.prodMk (continuous_apply (σ i)).snd)
  have hGc : Continuous G := continuous_finsetSum _ fun i _ ↦ hc.comp (continuous_apply i)
  have hFm : ∀ i, Measurable fun w : Fin n → X × Y ↦ ((w i).1, (w (σ i)).2) := fun i ↦
    (measurable_pi_apply i).fst.prodMk (measurable_pi_apply (σ i)).snd
  -- The strict inequality persists on a product of open neighbourhoods `W i` of the points.
  obtain ⟨W, hW, hWF⟩ := isOpen_pi_iff'.1 (isOpen_lt hFc hGc) (fun i ↦ (x i, y i)) hlt
  have hWm : ∀ i, MeasurableSet (W i) := fun i ↦ (hW i).1.measurableSet
  have hW0 : ∀ i, π (W i) ≠ 0 := fun i ↦
    ((Measure.mem_support_iff_forall _).1 (hmem i) _ ((hW i).1.mem_nhds (hW i).2)).ne'
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hlt
  -- Sample one point from each normalized restriction `ρ i` of `π` to `W i`, independently.
  let ρ : Fin n → Measure (X × Y) := fun i ↦ (π (W i))⁻¹ • π.restrict (W i)
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i ↦
    ⟨by simp [ρ, ENNReal.inv_mul_cancel (hW0 i) (measure_ne_top π _)]⟩
  let P := Measure.pi ρ
  have hev : ∀ i, MeasurePreserving (Function.eval i) P (ρ i) := measurePreserving_eval ρ
  have hGF : ∀ᵐ w ∂P, F w < G w := by
    have : ∀ᵐ w ∂P, ∀ i, w i ∈ W i := ae_all_iff.2 fun i ↦
      (hev i).quasiMeasurePreserving.ae (Measure.ae_smul_measure (ae_restrict_mem (hWm i)) _)
    filter_upwards [this] with w hw using hWF (Set.mem_univ_pi.2 hw)
  -- The permuted pairs of the sample have the same total marginals as the `ρ i`.
  let τ : Fin n → Measure (X × Y) := fun i ↦ P.map fun w ↦ ((w i).1, (w (σ i)).2)
  have hτ : IsCoupling (Measure.sum τ) (Measure.sum ρ).fst (Measure.sum ρ).snd :=
    isCoupling_sum_map_pi ρ σ
  -- Remove the mass `t • ∑ ρ i` from `π` and put back `t • ∑ τ i`, for `t` so small that
  -- `t • ρ i ≤ n⁻¹ • π` for every `i`.
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_min fun i ↦ π (W i)
  set t : ℝ≥0∞ := π (W j) / n with ht_def
  have ht0 : t ≠ 0 := ENNReal.div_ne_zero.2 ⟨hW0 j, ENNReal.natCast_ne_top n⟩
  have httop : t ≠ ∞ := ENNReal.div_ne_top (measure_ne_top π _) (Nat.cast_ne_zero.2 hn)
  let κ := t • Measure.sum ρ
  have hκ : κ ≤ π := by
    refine Measure.le_iff.2 fun s hs ↦ ?_
    have hterm : ∀ i, t * ρ i s ≤ (n : ℝ≥0∞)⁻¹ * π s := fun i ↦ by
      have hti : t * (π (W i))⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := by
        calc t * (π (W i))⁻¹ ≤ π (W i) / n * (π (W i))⁻¹ := by
              rw [ht_def]
              exact mul_le_mul_left (ENNReal.div_le_div_right (hj i) _) _
          _ = (n : ℝ≥0∞)⁻¹ := by
              rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel (hW0 i)
                (measure_ne_top π _), one_mul]
      calc t * ρ i s = t * (π (W i))⁻¹ * π (s ∩ W i) := by
            simp [ρ, Measure.restrict_apply hs, mul_assoc]
        _ ≤ (n : ℝ≥0∞)⁻¹ * π s := by gcongr; exact Set.inter_subset_left
    calc κ s = ∑ i, t * ρ i s := by
          simp [κ, Finset.mul_sum]
      _ ≤ ∑ _i : Fin n, (n : ℝ≥0∞)⁻¹ * π s := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = π s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn) (ENNReal.natCast_ne_top n), one_mul]
  have : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hκ' : IsCoupling κ κ.fst κ.snd := ⟨rfl, rfl⟩
  have hρ' : IsCoupling κ (t • (Measure.sum ρ).fst) (t • (Measure.sum ρ).snd) :=
    (IsCoupling.mk rfl rfl).smul t
  refine ⟨π - κ + t • Measure.sum τ, hπ.sub_add hκ ?_, ?_⟩
  · rw [hκ'.fst_eq.symm.trans hρ'.fst_eq, hκ'.snd_eq.symm.trans hρ'.snd_eq]
    exact hτ.smul t
  -- Compare the two costs through the sample: `∫ c ∂τ i` and `∫ c ∂ρ i` are integrals over `P`.
  have hlintegral_sum : ∀ ξ : Fin n → Measure (X × Y),
      ∫⁻ z, c z ∂(t • Measure.sum ξ) = t * ∑ i, ∫⁻ z, c z ∂ξ i := fun ξ ↦ by
    rw [lintegral_smul_measure, lintegral_sum_measure, tsum_fintype, smul_eq_mul]
  have hτint : ∑ i, ∫⁻ z, c z ∂τ i = ∫⁻ w, F w ∂P :=
    calc ∑ i, ∫⁻ z, c z ∂τ i = ∑ i, ∫⁻ w, c ((w i).1, (w (σ i)).2) ∂P :=
          Finset.sum_congr rfl fun i _ ↦ lintegral_map hcm (hFm i)
      _ = ∫⁻ w, F w ∂P := (lintegral_finsetSum _ fun i _ ↦ hcm.comp (hFm i)).symm
  have hρint : ∑ i, ∫⁻ z, c z ∂ρ i = ∫⁻ w, G w ∂P :=
    calc ∑ i, ∫⁻ z, c z ∂ρ i = ∑ i, ∫⁻ w, c (w i) ∂P :=
          Finset.sum_congr rfl fun i _ ↦ ((hev i).lintegral_comp hcm).symm
      _ = ∫⁻ w, G w ∂P :=
          (lintegral_finsetSum _ fun i _ ↦ hcm.comp (measurable_pi_apply i)).symm
  have hπeq : ∫⁻ z, c z ∂π = ∫⁻ z, c z ∂(π - κ) + t * ∫⁻ w, G w ∂P := by
    conv_lhs => rw [← Measure.sub_add_cancel_of_le hκ]
    rw [lintegral_add_measure, hlintegral_sum, hρint]
  have hGfin : ∫⁻ w, G w ∂P ≠ ∞ := by
    intro htop
    have hle : t * ∫⁻ w, G w ∂P ≤ ∫⁻ z, c z ∂π := by
      rw [← hρint, ← hlintegral_sum]
      exact lintegral_mono' hκ le_rfl
    rw [htop, ENNReal.mul_top ht0] at hle
    exact hfin (top_le_iff.1 hle)
  have hFG : ∫⁻ w, F w ∂P < ∫⁻ w, G w ∂P :=
    lintegral_strict_mono (IsProbabilityMeasure.ne_zero P)
      (Finset.measurable_sum _ fun i _ ↦ hcm.comp (measurable_pi_apply i)).aemeasurable
      (ne_top_of_le_ne_top hGfin (lintegral_mono_ae (hGF.mono fun _ h ↦ h.le))) hGF
  rw [lintegral_add_measure, hlintegral_sum, hτint, hπeq]
  refine ENNReal.add_lt_add_left ?_ (ENNReal.mul_lt_mul_right ht0 httop hFG)
  exact ne_top_of_le_ne_top hfin (lintegral_mono' Measure.sub_le le_rfl)

/-- **The support of an optimal plan is cyclically monotone** (Gangbo--McCann). For a continuous
cost `c : X × Y → ℝ≥0∞` and finite measures, the topological support of an optimal coupling of
finite total cost is `c`-cyclically monotone.

Finiteness of the optimal cost cannot be dropped: when it is infinite every coupling is optimal.
Continuity is used to spread a violation of cyclical monotonicity at finitely many points of the
support to sets of positive measure; for discontinuous costs the relevant statement is
concentration on some cyclically monotone set rather than a statement about the support. When the
support has full measure (`MeasureTheory.Measure.measure_compl_support`, for instance when `X × Y`
is second countable), the plan is concentrated on this closed set. -/
theorem IsOptimalCoupling.isCyclicallyMonotone_support [IsFiniteMeasure μ]
    (h : IsOptimalCoupling c π μ ν) (hc : Continuous c) (hfin : transportCost c μ ν ≠ ∞) :
    IsCyclicallyMonotone c π.support := by
  have : IsFiniteMeasure π := h.toIsCoupling.isFiniteMeasure
  refine isCyclicallyMonotone_iff.2 fun n x y hmem σ ↦ not_lt.1 fun hlt ↦ ?_
  obtain ⟨π', hπ', hlt'⟩ := exists_isCoupling_lintegral_lt hc h.toIsCoupling
    (h.lintegral_eq ▸ hfin) hmem σ hlt
  exact (h.lintegral_le hπ').not_gt hlt'

end Support

end TauCeti
