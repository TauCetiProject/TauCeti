/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Sinkhorn
public import TauCeti.MeasureTheory.OptimalTransport.ProportionalFitting

/-!
# Iterative proportional fitting on finite spaces is the Sinkhorn iteration

Let `ι` and `κ` be finite types with measurable singletons, let `R` be a finite reference measure
on `ι × κ` and let `μ` and `ν` be finite measures on `ι` and `κ`. Read the masses of the points
as a matrix `K i j = R.real {(i, j)}` and two vectors `a i = μ.real {i}` and `b j = ν.real {j}`.
This file identifies the measure-theoretic iterative proportional fitting
`MeasureTheory.Measure.proportionalFitting R μ ν`, which alternately reweights `R` along each
coordinate by a Radon–Nikodym derivative, with the matrix Sinkhorn iteration of
`TauCeti.Data.Matrix.Sinkhorn`, which alternately rescales the rows and the columns of `K`.

The reweighting of a measure along the first coordinate towards `μ` multiplies the mass of the
point `(i, j)` by `a i` divided by the mass of the row `i`. On a diagonal scaling
`u i * K i j * v j` of `K` this replaces the row factors `u` by the Sinkhorn row update
`K.sinkhornUpdate a v`, and the reweighting along the second coordinate towards `ν` likewise
replaces the column factors `v` by the column update `Kᵀ.sinkhornUpdate b u`. A sweep of
proportional fitting fits the rows first and the columns second, so it ends with the columns
exact, while `Matrix.sinkhornPlan` ends with the rows exact: the iterates of proportional fitting
are the Sinkhorn plans of the transposed problem, started from the constant column factors `1`.

For a strictly positive `K` and strictly positive `a` and `b`, the linear convergence of the
Sinkhorn iteration (`Matrix.tendsto_sinkhornPlan_iterate`) then transfers to proportional fitting.
The limit is identified measure-theoretically: the Sinkhorn–Knopp scaling `u i * K i j * v j` of
`K` with marginals `a` and `b` is the coupling of `μ` and `ν` with density
`exp (log u i + log v j)` against `R`, which is the Schrödinger minimizer by the potential
certificate `TauCeti.IsCoupling.klDiv_eq_schroedingerValue_of_eq_withDensity`. So on finite spaces
with strictly positive masses the iterates of proportional fitting converge, setwise, to the
unique coupling of `μ` and `ν` of least relative entropy against `R`.

## Main statements

* `TauCeti.fitLaw_fst_real_singleton` and `TauCeti.fitLaw_snd_real_singleton`: the two
  half-steps of proportional fitting on a diagonal scaling of `K` are the Sinkhorn row and column
  updates.
* `TauCeti.proportionalFittingStep_real_singleton`: the same for one sweep.
* `TauCeti.proportionalFitting_real_singleton`: the iterates of proportional fitting are the
  transposed Sinkhorn plans `(Kᵀ.sinkhornPlan b a ((Kᵀ.sinkhornStep b a)^[n] 1))ᵀ`.
* `TauCeti.IsCoupling.real_singleton_eq_of_klDiv_eq_schroedingerValue`: the Schrödinger minimizer
  has the masses of any diagonal scaling of `K` by positive factors with marginals `a` and `b`.
* `TauCeti.tendsto_proportionalFitting_apply`: for strictly positive masses, proportional fitting
  converges setwise to the Schrödinger minimizer.

## References

* R. Sinkhorn and P. Knopp, *Concerning nonnegative matrices and doubly stochastic matrices*,
  Pacific J. Math. 21 (1967), 343--348.
* L. Rüschendorf, *Convergence of the iterative proportional fitting procedure*, Ann. Statist. 23
  (1995), 1160–1174, for the procedure on general measurable spaces and its finite case.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Section 4.2, for Sinkhorn's algorithm as alternating marginal projections.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Filter Topology Matrix Measure
open scoped ENNReal

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]
  {π R : Measure (ι × κ)} {μ : Measure ι} {ν : Measure κ}
  {K : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ} {u : ι → ℝ} {v : κ → ℝ}

/-! ### The half-steps on a diagonal scaling -/

omit [Fintype ι] in
/-- The mass of a row of a finite measure on `ι × κ` is the sum of the masses of its points. -/
private theorem map_fst_real_singleton [IsFiniteMeasure π] (i : ι) :
    (π.map Prod.fst).real {i} = ∑ j, π.real {(i, j)} := by
  have h : Prod.fst ⁻¹' {i} = ⋃ j ∈ (Finset.univ : Finset κ), ({(i, j)} : Set (ι × κ)) := by
    ext ⟨i', j⟩
    simp [eq_comm]
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton i), h,
    measureReal_biUnion_finset (fun j _ j' _ hj ↦ by simpa using hj)
      (fun j _ ↦ measurableSet_singleton _)]

omit [Fintype κ] in
/-- The mass of a column of a finite measure on `ι × κ` is the sum of the masses of its points. -/
private theorem map_snd_real_singleton [IsFiniteMeasure π] (j : κ) :
    (π.map Prod.snd).real {j} = ∑ i, π.real {(i, j)} := by
  have h : Prod.snd ⁻¹' {j} = ⋃ i ∈ (Finset.univ : Finset ι), ({(i, j)} : Set (ι × κ)) := by
    ext ⟨i, j'⟩
    simp [eq_comm]
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton j), h,
    measureReal_biUnion_finset (fun i _ i' _ hi ↦ by simpa using hi)
      (fun i _ ↦ measurableSet_singleton _)]

omit [Fintype ι] in
/-- **The row half-step is the Sinkhorn row update.** If the masses of a finite measure `π` on
`ι × κ` are the diagonal scaling `u i * K i j * v j` of `K` by row factors with no zero entry, then
reweighting `π` along the first coordinate towards `μ` gives the diagonal scaling of `K` by the
row factors `K.sinkhornUpdate a v` and the same column factors, where `a i = μ.real {i}`. -/
theorem fitLaw_fst_real_singleton [IsFiniteMeasure π] [IsFiniteMeasure μ]
    (hπ : ∀ i j, π.real {(i, j)} = u i * K i j * v j) (hu : ∀ i, u i ≠ 0)
    (hμ : ∀ i, μ.real {i} = a i) (i : ι) (j : κ) :
    (π.fitLaw Prod.fst μ).real {(i, j)} = K.sinkhornUpdate a v i * K i j * v j := by
  rw [measureReal_def, fitLaw_apply_singleton measurable_fst, ENNReal.toReal_mul,
    ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    map_fst_real_singleton, hμ, hπ, sinkhornUpdate_apply, mulVec_apply_eq_sum]
  have hrow : ∑ j, u i * K i j * v j = u i * ∑ j, K i j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_assoc _ _ _
  simp_rw [hπ, hrow]
  rcases eq_or_ne (∑ j, K i j * v j) 0 with h | h
  · simp [h]
  · field_simp [hu i]

omit [Fintype κ] in
/-- **The column half-step is the Sinkhorn column update.** If the masses of a finite measure `π`
on `ι × κ` are the diagonal scaling `u i * K i j * v j` of `K` by column factors with no zero
entry, then reweighting `π` along the second coordinate towards `ν` gives the diagonal scaling of
`K` by the same row factors and the column factors `Kᵀ.sinkhornUpdate b u`, where
`b j = ν.real {j}`. -/
theorem fitLaw_snd_real_singleton [IsFiniteMeasure π] [IsFiniteMeasure ν]
    (hπ : ∀ i j, π.real {(i, j)} = u i * K i j * v j) (hv : ∀ j, v j ≠ 0)
    (hν : ∀ j, ν.real {j} = b j) (i : ι) (j : κ) :
    (π.fitLaw Prod.snd ν).real {(i, j)} = u i * K i j * Kᵀ.sinkhornUpdate b u j := by
  rw [measureReal_def, fitLaw_apply_singleton measurable_snd, ENNReal.toReal_mul,
    ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    map_snd_real_singleton, hν, hπ, sinkhornUpdate_apply, mulVec_apply_eq_sum]
  have hcol : ∑ i, u i * K i j * v j = (∑ i, K i j * u i) * v j := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [hπ, hcol, transpose_apply]
  rcases eq_or_ne (∑ i, K i j * u i) 0 with h | h
  · simp [h]
  · field_simp [hv j]

/-- **A sweep of proportional fitting is a Sinkhorn sweep.** If the masses of a finite measure `π`
on `ι × κ` are the diagonal scaling `u i * K i j * v j` of `K` by factors with no zero entry, then
one sweep of proportional fitting towards `μ` and `ν` gives the diagonal scaling of `K` by the row
factors `u' = K.sinkhornUpdate a v` and the column factors `Kᵀ.sinkhornUpdate b u'`. -/
theorem proportionalFittingStep_real_singleton [IsFiniteMeasure π] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hπ : ∀ i j, π.real {(i, j)} = u i * K i j * v j) (hu : ∀ i, u i ≠ 0)
    (hv : ∀ j, v j ≠ 0) (hμ : ∀ i, μ.real {i} = a i) (hν : ∀ j, ν.real {j} = b j) (i : ι)
    (j : κ) :
    (π.proportionalFittingStep μ ν).real {(i, j)} =
      K.sinkhornUpdate a v i * K i j * Kᵀ.sinkhornUpdate b (K.sinkhornUpdate a v) j := by
  have := isFiniteMeasure_fitLaw (π := π) (μ := μ) measurable_fst
  rw [proportionalFittingStep_def]
  exact fitLaw_snd_real_singleton (fitLaw_fst_real_singleton hπ hu hμ) hv hν i j

/-! ### The iterates -/

/-- **Proportional fitting on a finite space is the Sinkhorn iteration.** Let the masses of the
points of a finite reference measure `R` on `ι × κ` be the entries of a strictly positive matrix
`K`, and those of finite measures `μ` and `ν` the entries of strictly positive vectors `a` and
`b`. Then the `(n + 1)`-st iterate of proportional fitting towards `μ` and `ν` is the transposed
Sinkhorn plan of `Kᵀ` from the column factors `(Kᵀ.sinkhornStep b a)^[n] 1`: proportional fitting
fits the columns last, so it is the Sinkhorn iteration of the transposed problem, started from the
constant column factors of `R` itself. -/
theorem proportionalFitting_real_singleton [IsFiniteMeasure R] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hR : ∀ i j, R.real {(i, j)} = K i j) (hμ : ∀ i, μ.real {i} = a i)
    (hν : ∀ j, ν.real {j} = b j) (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (n : ℕ) (i : ι) (j : κ) :
    (R.proportionalFitting μ ν (n + 1)).real {(i, j)} =
      (Kᵀ.sinkhornPlan b a ((Kᵀ.sinkhornStep b a)^[n] 1))ᵀ i j := by
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  have hKt : ∀ j i, 0 < Kᵀ j i := fun j i ↦ hK i j
  -- the column factors `w n` of the iteration and its row factors `K.sinkhornUpdate a (w n)`
  set w : ℕ → κ → ℝ := fun n ↦ (Kᵀ.sinkhornStep b a)^[n] 1 with hw
  have hwpos : ∀ n j, 0 < w n j := sinkhornStep_iterate_pos hKt hb ha (fun _ ↦ one_pos)
  have hw_succ : ∀ n, w (n + 1) = Kᵀ.sinkhornUpdate b (K.sinkhornUpdate a (w n)) := fun n ↦ by
    simp only [hw]
    rw [Function.iterate_succ_apply', sinkhornStep_def, transpose_transpose]
  have key : ∀ n i j, (R.proportionalFitting μ ν (n + 1)).real {(i, j)} =
      K.sinkhornUpdate a (w n) i * K i j * w (n + 1) j := by
    intro n
    induction n with
    | zero =>
      rw [zero_add, hw_succ]
      intro i j
      rw [proportionalFitting_succ, proportionalFitting_zero]
      exact proportionalFittingStep_real_singleton (u := 1) (v := 1) (fun i j ↦ by simp [hR])
        (fun _ ↦ one_ne_zero) (fun _ ↦ one_ne_zero) hμ hν i j
    | succ n ih =>
      intro i j
      rw [hw_succ (n + 1), proportionalFitting_succ]
      exact proportionalFittingStep_real_singleton ih
        (fun i ↦ (sinkhornUpdate_pos hK ha (hwpos n) i).ne') (fun j ↦ (hwpos _ j).ne') hμ hν i j
  rw [key, transpose_apply, sinkhornPlan_apply, sinkhornStep_def, transpose_transpose,
    transpose_apply, ← hw_succ]
  ring

/-! ### Convergence to the Schrödinger minimizer -/

/-- **The Schrödinger minimizer on a finite space is the Sinkhorn–Knopp scaling.** Let the masses
of the points of a finite reference measure `R` on `ι × κ` be the entries of a matrix `K`, and
those of finite measures `μ` and `ν` the entries of vectors `a` and `b`. If the diagonal scaling
`u i * K i j * v j` of `K` by strictly positive factors has row sums `a` and column sums `b`, then
every coupling of `μ` and `ν` of least relative entropy against `R` gives the point `(i, j)` the
mass `u i * K i j * v j`. -/
theorem IsCoupling.real_singleton_eq_of_klDiv_eq_schroedingerValue [IsFiniteMeasure R]
    [IsFiniteMeasure μ] (hR : ∀ i j, R.real {(i, j)} = K i j) (hμ : ∀ i, μ.real {i} = a i)
    (hν : ∀ j, ν.real {j} = b j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hrow : ∀ i, ∑ j, u i * K i j * v j = a i) (hcol : ∀ j, ∑ i, u i * K i j * v j = b j)
    (hπ : IsCoupling π μ ν) (hπR : klDiv π R = schroedingerValue R μ ν) (i : ι) (j : κ) :
    π.real {(i, j)} = u i * K i j * v j := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  -- the diagonal scaling as a measure: `R` with density `u i * v j = exp (log u i + log v j)`
  obtain ⟨σ, hσ⟩ : ∃ σ : Measure (ι × κ),
      σ = R.withDensity fun z ↦ ENNReal.ofReal (Real.exp (Real.log (u z.1) + Real.log (v z.2))) :=
    ⟨_, rfl⟩
  have : IsFiniteMeasure σ := by
    rw [hσ]
    exact isFiniteMeasure_withDensity_ofReal HasFiniteIntegral.of_finite
  have hσ_apply : ∀ i j, σ.real {(i, j)} = u i * K i j * v j := fun i j ↦ by
    rw [measureReal_def, hσ, withDensity_apply _ (measurableSet_singleton _),
      lintegral_singleton, ENNReal.toReal_mul, ← measureReal_def, hR,
      Real.exp_add, Real.exp_log (hu i), Real.exp_log (hv j),
      ENNReal.toReal_ofReal (mul_pos (hu i) (hv j)).le]
    ring
  have hσc : IsCoupling σ μ ν := by
    refine ⟨ext_iff_measureReal_singleton.2 fun i ↦ ?_,
      ext_iff_measureReal_singleton.2 fun j ↦ ?_⟩
    · simp_rw [fst, map_fst_real_singleton, hσ_apply, hrow, hμ]
    · simp_rw [snd, map_snd_real_singleton, hσ_apply, hcol, hν]
  have hφ : Measurable fun i ↦ Real.log (u i) := measurable_of_finite _
  have hψ : Measurable fun j ↦ Real.log (v j) := measurable_of_finite _
  have hφi : Integrable (fun i ↦ Real.log (u i)) μ := Integrable.of_finite
  have hψi : Integrable (fun j ↦ Real.log (v j)) ν := Integrable.of_finite
  have hσR : klDiv σ R = schroedingerValue R μ ν :=
    hσc.klDiv_eq_schroedingerValue_of_eq_withDensity (φ := fun i ↦ Real.log (u i))
      (ψ := fun j ↦ Real.log (v j)) hσ hφ hψ hφi hψi
  have hfin : schroedingerValue R μ ν ≠ ∞ := by
    rw [← hσR, hσc.klDiv_eq_ofReal_of_eq_withDensity (φ := fun i ↦ Real.log (u i))
      (ψ := fun j ↦ Real.log (v j)) hσ hφ hψ hφi hψi]
    exact ENNReal.ofReal_ne_top
  rw [hπ.eq_of_klDiv_eq_schroedingerValue hσc hπR hσR hfin, hσ_apply]

omit [Fintype ι] [Fintype κ] in
/-- **Convergence of proportional fitting on a finite space.** Let `R` be a finite reference
measure on `ι × κ` and `μ` a finite measure on `ι`, and let every point have positive mass under
`R`, `μ` and `ν`. If `π` is a coupling of `μ` and `ν` of least relative entropy against `R`, then
the iterates of proportional fitting towards `μ` and `ν` converge to `π` on every set. Such a
coupling exists as soon as `μ` and `ν` have the same total mass
(`TauCeti.exists_isCoupling_klDiv_eq_schroedingerValue`), and it is unique
(`TauCeti.IsCoupling.eq_of_klDiv_eq_schroedingerValue`). -/
theorem tendsto_proportionalFitting_apply [Finite ι] [Finite κ] [IsFiniteMeasure R]
    [IsFiniteMeasure μ] (hR : ∀ z, R {z} ≠ 0) (hμ : ∀ i, μ {i} ≠ 0) (hν : ∀ j, ν {j} ≠ 0)
    (hπ : IsCoupling π μ ν) (hπR : klDiv π R = schroedingerValue R μ ν) (s : Set (ι × κ)) :
    Tendsto (fun n ↦ R.proportionalFitting μ ν n s) atTop (𝓝 (π s)) := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  -- the masses of the points as a matrix and two vectors, all strictly positive
  obtain ⟨K, hK⟩ : ∃ K : Matrix ι κ ℝ, ∀ i j, R.real {(i, j)} = K i j :=
    ⟨of fun i j ↦ R.real {(i, j)}, fun _ _ ↦ rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ι → ℝ, ∀ i, μ.real {i} = a i := ⟨fun i ↦ μ.real {i}, fun _ ↦ rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : κ → ℝ, ∀ j, ν.real {j} = b j := ⟨fun j ↦ ν.real {j}, fun _ ↦ rfl⟩
  have hKpos : ∀ i j, 0 < K i j := fun i j ↦
    hK i j ▸ ENNReal.toReal_pos (hR _) (measure_ne_top _ _)
  have hapos : ∀ i, 0 < a i := fun i ↦ ha i ▸ ENNReal.toReal_pos (hμ i) (measure_ne_top _ _)
  have hbpos : ∀ j, 0 < b j := fun j ↦ hb j ▸ ENNReal.toReal_pos (hν j) (measure_ne_top _ _)
  have hmass : ∑ i, a i = ∑ j, b j := by
    simp_rw [← ha, ← hb]
    rw [sum_measureReal_singleton, sum_measureReal_singleton, Finset.coe_univ, Finset.coe_univ,
      measureReal_def, measureReal_def, hπ.measure_univ_eq]
  obtain ⟨u, v, hu, hv, hrow, hcol⟩ := exists_sinkhorn_scaling hKpos hapos hbpos hmass
  have hπmass := hπ.real_singleton_eq_of_klDiv_eq_schroedingerValue hK ha hb hu hv hrow hcol hπR
  -- convergence on the points, from the convergence of the transposed Sinkhorn plans
  obtain ⟨P, hP⟩ : ∃ P : Matrix ι κ ℝ, ∀ i j, P i j = u i * K i j * v j :=
    ⟨of fun i j ↦ u i * K i j * v j, fun _ _ ↦ rfl⟩
  have hPs : IsDiagonalScaling P K u v := (isDiagonalScaling_def _ _ _ _).2 hP
  have hPm : HasMarginals Pᵀ b a := (hasMarginals_def _ _ _).2
    ⟨fun j ↦ by simp_rw [transpose_apply, hP, hcol],
      fun i ↦ by simp_rw [transpose_apply, hP, hrow]⟩
  have hlim := tendsto_sinkhornPlan_iterate (K := Kᵀ) (fun j i ↦ hKpos i j) hbpos hapos
    hPs.transpose hPm hv hu (u₀ := 1) fun _ ↦ one_pos
  have hpt : ∀ z, Tendsto (fun n ↦ R.proportionalFitting μ ν n {z}) atTop (𝓝 (π {z})) := by
    rintro ⟨i, j⟩
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    have h := (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim j) i)
    rw [← ofReal_measureReal, hπmass, ← hP, ← transpose_apply P]
    refine h.congr fun n ↦ ?_
    rw [Function.comp_apply, ← transpose_apply (Kᵀ.sinkhornPlan b a _) i j,
      ← proportionalFitting_real_singleton hK ha hb hKpos hapos hbpos, ofReal_measureReal]
  -- a set of the finite space `ι × κ` is a finite union of points
  have hsum : ∀ m : Measure (ι × κ), m s = ∑ z ∈ s.toFinite.toFinset, m {z} := fun m ↦ by
    rw [sum_measure_singleton, Set.Finite.coe_toFinset]
  simp_rw [hsum]
  exact tendsto_finsetSum _ fun z _ ↦ hpt z

end TauCeti
