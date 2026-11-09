/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Entropic

/-!
# Finite scalar Gromov–Wasserstein barycenters

Fix a finite barycenter carrier with law `μ`, finite input carriers with laws `ν j`, and
probability weights `w`. The variables are a real-valued barycenter kernel `ω` and one coupling
`F j ∈ RealPlans μ (ν j)` per input. The objective is the weighted sum of the unrooted finite
GW objectives, with optional relative entropy penalties against `μ ⊗ ν j`. Thus at exponent
two it regularizes squared distortion, not its square root, and uses no factor of one half.

`exists_isMinOn_finiteGromovWassersteinBarycenterObjective` proves global attainment, including
zero temperature. No bound on the unknown kernel is assumed: clipping it to an interval
containing all input kernel values cannot increase any distortion or change any entropy term.
The clipped problem has compact feasible set. Every coupling with positive weight in a joint
minimizer solves its corresponding entropic GW problem.

These are barycenters of scalar measured kernels with a prescribed finite carrier and law.
The kernel is not required to be a distance matrix, symmetric, or zero on the diagonal. The
result does not optimize the carrier size or its law, assert uniqueness, or assert convergence
of an alternating algorithm. The exponent is finite; there is no essential-supremum objective.

## References

* G. Peyré, M. Cuturi and J. Solomon, *Gromov-Wasserstein averaging of kernel and distance
  matrices*, ICML, PMLR 48 (2016), 2664–2672, for the fixed-law finite barycenter formulation.
* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), for the measured-kernel convention.
-/

public section

noncomputable section

open Set
open scoped BigOperators ENNReal

namespace TauCeti

variable {J ι : Type*} {κ : J → Type*} [Fintype J] [Fintype ι] [∀ j, Fintype (κ j)]

/-- The joint finite scalar GW barycenter objective with fixed barycenter law `μ`.
Each input contributes its `p`-th distortion power plus `ε` times its KL divergence against
`μ ⊗ ν j`, weighted by `w j`. The variables are the kernel and the family of real plans.
The usual regimes are `1 ≤ p < ∞` and `ε ≥ 0`; `ε = 0` is the unregularized problem. -/
def finiteGromovWassersteinBarycenterObjective (p ε : ℝ) (w : PMF J) (μ : PMF ι)
    (ν : ∀ j, PMF (κ j)) (ωY : ∀ j, κ j × κ j → ℝ)
    (x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ)) : ℝ :=
  ∑ j, (w j).toReal * entropicGromovWassersteinObjective p ε μ x.1 (ν j) (ωY j) (x.2 j)

/-- The barycenter objective as a weighted sum of the individual finite objectives. -/
theorem finiteGromovWassersteinBarycenterObjective_def (p ε : ℝ) (w : PMF J) (μ : PMF ι)
    (ν : ∀ j, PMF (κ j)) (ωY : ∀ j, κ j × κ j → ℝ)
    (x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ)) :
    finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY x =
      ∑ j, (w j).toReal *
        entropicGromovWassersteinObjective p ε μ x.1 (ν j) (ωY j) (x.2 j) := (rfl)

/-- At zero temperature this is the weighted sum of unregularized distortion powers. -/
@[simp]
theorem finiteGromovWassersteinBarycenterObjective_zero (p : ℝ) (w : PMF J) (μ : PMF ι)
    (ν : ∀ j, PMF (κ j)) (ωY : ∀ j, κ j × κ j → ℝ)
    (x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ)) :
    finiteGromovWassersteinBarycenterObjective p 0 w μ ν ωY x =
      ∑ j, (w j).toReal * gromovWassersteinObjective p x.1 (ωY j) (x.2 j) := by
  simp [finiteGromovWassersteinBarycenterObjective_def]

/-- The joint objective is continuous in the kernel and all coupling entries. -/
theorem continuous_finiteGromovWassersteinBarycenterObjective {p : ℝ} (hp : 0 ≤ p)
    (ε : ℝ) (w : PMF J) (μ : PMF ι) (ν : ∀ j, PMF (κ j))
    (ωY : ∀ j, κ j × κ j → ℝ) :
    Continuous (finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY) := by
  unfold finiteGromovWassersteinBarycenterObjective
  refine continuous_finsetSum _ fun j _ ↦ continuous_const.mul ?_
  simp_rw [entropicGromovWassersteinObjective_def, gromovWassersteinObjective_def]
  refine Continuous.add ?_ (continuous_const.mul
    ((Matrix.continuous_relEntropy _).comp (by fun_prop)))
  exact continuous_finsetSum _ fun q _ ↦ continuous_finsetSum _ fun q' _ ↦
    (((by fun_prop : Continuous fun x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ) ↦
      dist (x.1 (q.1, q'.1)) (ωY j (q.2, q'.2))).rpow_const
        (fun _ ↦ Or.inr hp)).mul (by fun_prop)).mul (by fun_prop)

/-- Clipping the barycenter kernel leaves entropy penalties unchanged and cannot increase
the joint objective when the input kernels lie in the clipping interval. -/
theorem finiteGromovWassersteinBarycenterObjective_projIcc_le {p a b : ℝ} (hp : 0 ≤ p)
    (hab : a ≤ b) (ε : ℝ) (w : PMF J) (μ : PMF ι) (ν : ∀ j, PMF (κ j))
    (ωY : ∀ j, κ j × κ j → ℝ) (hωY : ∀ j q, ωY j q ∈ Icc a b)
    (ω : ι × ι → ℝ) {F : ∀ j, ι × κ j → ℝ} (hF : ∀ j, F j ∈ RealPlans μ (ν j)) :
    finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY
        (fun q ↦ (projIcc a b hab (ω q) : ℝ), F) ≤
      finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY (ω, F) := by
  unfold finiteGromovWassersteinBarycenterObjective
  refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  rw [entropicGromovWassersteinObjective_def, entropicGromovWassersteinObjective_def]
  exact add_le_add (gromovWassersteinObjective_projIcc_le hp hab ω (ωY j)
    (hωY j) (hF j).1) le_rfl

/-- Global existence with a range guarantee: if all input kernels take values in `[a,b]`,
a minimizing barycenter kernel can be chosen in `[a,b]`. Competitors are unrestricted.
The entropy coefficient can be any real number, since the coupling polytopes are compact. -/
theorem exists_isMinOn_finiteGromovWassersteinBarycenterObjective_of_mem_Icc
    {p a b : ℝ} (hp : 0 ≤ p) (hab : a ≤ b) (ε : ℝ) (w : PMF J) (μ : PMF ι)
    (ν : ∀ j, PMF (κ j)) (ωY : ∀ j, κ j × κ j → ℝ)
    (hωY : ∀ j q, ωY j q ∈ Icc a b) :
    ∃ x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ),
      (∀ q, x.1 q ∈ Icc a b) ∧ (∀ j, x.2 j ∈ RealPlans μ (ν j)) ∧
      IsMinOn (finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY)
        {y | ∀ j, y.2 j ∈ RealPlans μ (ν j)} x := by
  let S : Set (ι × ι → ℝ) := pi univ fun _ ↦ Icc a b
  let T : Set (∀ j, ι × κ j → ℝ) := pi univ fun j ↦ RealPlans μ (ν j)
  have hS : IsCompact S := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hT : IsCompact T := isCompact_univ_pi fun _ ↦ isCompact_realPlans
  have hSne : S.Nonempty := ⟨fun _ ↦ a, fun _ _ ↦ ⟨le_rfl, hab⟩⟩
  have hTne : T.Nonempty := univ_pi_nonempty_iff.2 fun j ↦ realPlans_nonempty μ (ν j)
  obtain ⟨x, hx, hmin⟩ := (hS.prod hT).exists_isMinOn (hSne.prod hTne)
    (continuous_finiteGromovWassersteinBarycenterObjective hp ε w μ ν ωY).continuousOn
  have hxS : ∀ q, x.1 q ∈ Icc a b := fun q ↦ hx.1 q (mem_univ q)
  have hxT : ∀ j, x.2 j ∈ RealPlans μ (ν j) := by simpa [T] using hx.2
  refine ⟨x, hxS, hxT, fun y hy ↦ ?_⟩
  let ω : ι × ι → ℝ := fun q ↦ (projIcc a b hab (y.1 q) : ℝ)
  have hω : ω ∈ S := fun q _ ↦ (projIcc a b hab (y.1 q)).property
  exact (hmin ⟨hω, by simpa [T] using hy⟩).trans
    (finiteGromovWassersteinBarycenterObjective_projIcc_le hp hab ε w μ ν ωY hωY y.1 hy)

/-- Every finite family of real-valued kernels has a fixed-law finite GW barycenter,
with or without the prescribed relative entropy penalties. The barycenter kernel is
unrestricted; boundedness of the finite input family supplies a compact reduction. -/
theorem exists_isMinOn_finiteGromovWassersteinBarycenterObjective {p : ℝ} (hp : 0 ≤ p)
    (ε : ℝ) (w : PMF J) (μ : PMF ι) (ν : ∀ j, PMF (κ j))
    (ωY : ∀ j, κ j × κ j → ℝ) :
    ∃ x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ),
      (∀ j, x.2 j ∈ RealPlans μ (ν j)) ∧
      IsMinOn (finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY)
        {y | ∀ j, y.2 j ∈ RealPlans μ (ν j)} x := by
  obtain ⟨R, hR⟩ := (Set.finite_range fun q : Σ j, κ j × κ j ↦ ωY q.1 q.2).bddAbove
  obtain ⟨L, hL⟩ := (Set.finite_range fun q : Σ j, κ j × κ j ↦ ωY q.1 q.2).bddBelow
  obtain ⟨x, -, hx, hmin⟩ :=
    exists_isMinOn_finiteGromovWassersteinBarycenterObjective_of_mem_Icc hp
      (a := min L R) (b := R) (min_le_right _ _) ε w μ ν ωY
      (fun j q ↦ ⟨(min_le_left _ _).trans (hL ⟨⟨j, q⟩, rfl⟩), hR ⟨⟨j, q⟩, rfl⟩⟩)
  exact ⟨x, hx, hmin⟩

/-- In a joint minimizer, every positive-weight coupling minimizes its own entropic GW
objective for the chosen barycenter kernel. Zero-weight inputs impose no such condition. -/
theorem isMinOn_entropicGromovWassersteinObjective_of_barycenter
    {p ε : ℝ} {w : PMF J} {μ : PMF ι} {ν : ∀ j, PMF (κ j)}
    {ωY : ∀ j, κ j × κ j → ℝ} {x : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ)}
    (hx : ∀ j, x.2 j ∈ RealPlans μ (ν j))
    (hmin : IsMinOn (finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY)
      {y | ∀ j, y.2 j ∈ RealPlans μ (ν j)} x) {j : J} (hj : 0 < (w j).toReal) :
    IsMinOn (entropicGromovWassersteinObjective p ε μ x.1 (ν j) (ωY j))
      (RealPlans μ (ν j)) (x.2 j) := by
  classical
  rw [isMinOn_iff]
  intro g hg
  by_contra! hbad
  let y : (ι × ι → ℝ) × (∀ j, ι × κ j → ℝ) := (x.1, Function.update x.2 j g)
  have hy : ∀ k, y.2 k ∈ RealPlans μ (ν k) := by
    intro k
    by_cases h : k = j
    · subst k; simpa [y] using hg
    · simpa [y, h] using hx k
  have hlt : finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY y <
      finiteGromovWassersteinBarycenterObjective p ε w μ ν ωY x := by
    unfold finiteGromovWassersteinBarycenterObjective
    apply Finset.sum_lt_sum
    · intro k _
      by_cases h : k = j
      · subst k; simpa [y] using (mul_lt_mul_of_pos_left hbad hj).le
      · simp [y, h]
    · exact ⟨j, Finset.mem_univ _, by simpa [y] using mul_lt_mul_of_pos_left hbad hj⟩
  exact (not_lt_of_ge (hmin hy)) hlt

section Measure

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [∀ j, MeasurableSpace (κ j)] [∀ j, MeasurableSingletonClass (κ j)]

omit [Fintype ι] [∀ j, Fintype (κ j)] in
/-- At zero temperature, minimizing the joint finite objective really gives a barycenter
for the generic measured-kernel GW distance: the weighted sum of its `p`-th powers attains
its minimum among all real kernels on the prescribed finite carrier with law `μ`.
No symmetry or metric constraints on the kernels are imposed. -/
theorem exists_isMinOn_sum_gromovWassersteinEDist_rpow [Finite ι] [∀ j, Finite (κ j)]
    {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (w : PMF J) (μ : PMF ι) (ν : ∀ j, PMF (κ j))
    (ωY : ∀ j, κ j × κ j → ℝ) :
    ∃ ω : ι × ι → ℝ, IsMinOn
      (fun η ↦ ∑ j, (w j).toReal *
        (gromovWassersteinEDist p μ.toMeasure η (ν j).toMeasure (ωY j) ^ p.toReal).toReal)
      univ ω := by
  let := Fintype.ofFinite ι
  let (j : J) := Fintype.ofFinite (κ j)
  -- Optimize the couplings separately for each fixed kernel and identify their values
  -- using the finite-to-measure distortion formula.
  have optimal (ω : ι × ι → ℝ) :
      ∃ F : ∀ j, ι × κ j → ℝ, (∀ j, F j ∈ RealPlans μ (ν j)) ∧
        (∀ G, (∀ j, G j ∈ RealPlans μ (ν j)) →
          finiteGromovWassersteinBarycenterObjective p.toReal 0 w μ ν ωY (ω, F) ≤
            finiteGromovWassersteinBarycenterObjective p.toReal 0 w μ ν ωY (ω, G)) ∧
        finiteGromovWassersteinBarycenterObjective p.toReal 0 w μ ν ωY (ω, F) =
          ∑ j, (w j).toReal *
            (gromovWassersteinEDist p μ.toMeasure ω (ν j).toMeasure (ωY j) ^ p.toReal).toReal := by
    choose F hF hFm using fun j ↦
      exists_isMinOn_gromovWassersteinObjective p.toReal μ ω (ν j) (ωY j)
    refine ⟨F, hF, fun G hG ↦ ?_, ?_⟩
    · simp only [finiteGromovWassersteinBarycenterObjective_zero]
      exact Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hFm j (hG j)) ENNReal.toReal_nonneg
    · rw [finiteGromovWassersteinBarycenterObjective_zero]
      congr 1
      funext j
      congr 1
      have heq := (isMinOn_gromovWassersteinObjective_iff hp0 hp (hF j)).1 (hFm j)
      dsimp only
      rw [← TransportMatrix.toRealFun_ofRealFun (hF j),
        TransportMatrix.gromovWassersteinObjective_toRealFun _ _ _ hp0 hp, heq]
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_finiteGromovWassersteinBarycenterObjective
    (p := p.toReal) ENNReal.toReal_nonneg 0 w μ ν ωY
  obtain ⟨F, -, hFmin, hFeq⟩ := optimal x.1
  refine ⟨x.1, isMinOn_iff.2 fun ω _ ↦ ?_⟩
  obtain ⟨G, hG, -, hGeq⟩ := optimal ω
  rw [← hFeq, ← hGeq]
  exact (hFmin x.2 hx).trans (hmin hG)

end Measure

end TauCeti
