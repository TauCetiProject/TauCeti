module

public import TauCeti.Probability.Exchangeability.Contractability

/-!
# The covariance structure of a contractable L² sequence

This file opens the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), whose first analytic input is the *uniform covariance
structure of a contractable L² sequence* (`contractable_covariance_structure`). It also
supplies the two Layer 3 preliminaries listed before it — "equality of means and integrals
from equal one-dimensional laws" and "equality of pair covariances from equal
two-dimensional laws". The latter appears first in the reusable form
`covariance_eq_of_identDistrib_pair`, then specializes to contractable processes.

For a real-valued contractable sequence, the one- and two-coordinate `IdentDistrib` facts in
`TauCeti.Probability.Exchangeability.Contractability` give the uniform first- and second-moment
structure:

* `Contractable.integral_coord_eq`: all coordinate means agree;
* `Contractable.variance_coord_eq`: all coordinate variances agree;
* `Contractable.covariance_eq_of_ne`: any two off-diagonal covariances agree,
  `cov[X i, X j; μ] = cov[X k, X l; μ]` for `i ≠ j` and `k ≠ l`.

The `IdentDistrib` and moment machinery is Mathlib's (`ProbabilityTheory.IdentDistrib`,
`ProbabilityTheory.covariance`, `ProbabilityTheory.variance`); the contractability input is
the Layer 0 API in `TauCeti.Probability.Exchangeability.Contractability`. No material from
`cameronfreer/exchangeability` is used: the source's L² lane carries the real-valued
statement through block averages, whereas this file records only the elementary
moment-uniformity that seeds it.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Real

variable {X : ℕ → Ω → ℝ}

/-- **Equal covariance from equal pair laws.** If the two-dimensional laws of `(X, Y)` under
`μ` and `(X', Y')` under `ν` agree, then their covariances agree. -/
theorem covariance_eq_of_identDistrib_pair {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} {X Y : Ω → ℝ} {X' Y' : Ω' → ℝ}
    (h : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ ν) :
    cov[X, Y; μ] = cov[X', Y'; ν] := by
  let F : Ω → ℝ × ℝ := fun ω => (X ω, Y ω)
  let G : Ω' → ℝ × ℝ := fun ω => (X' ω, Y' ω)
  calc
    cov[X, Y; μ] = cov[Prod.fst, Prod.snd; μ.map F] := by
      rw [covariance_map measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
        h.aemeasurable_fst]
      rfl
    _ = cov[Prod.fst, Prod.snd; ν.map G] := by rw [h.map_eq]
    _ = cov[X', Y'; ν] := by
      rw [covariance_map measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
        h.aemeasurable_snd]
      rfl

/-- **Equal means from contractability.** For a contractable real-valued process, all
coordinate expectations agree. -/
theorem Contractable.integral_coord_eq (hX : Contractable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) (i j : ℕ) :
    μ[X i] = μ[X j] :=
  (hX.identDistrib_coord hX_meas i j).integral_eq

/-- **Equal variances from contractability.** For a contractable real-valued process, all
coordinate variances agree. -/
theorem Contractable.variance_coord_eq (hX : Contractable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) (i j : ℕ) :
    Var[X i; μ] = Var[X j; μ] :=
  (hX.identDistrib_coord hX_meas i j).variance_eq

/-- **Uniform covariances from contractability.** For a contractable real-valued process with
a.e. measurable coordinates, any two off-diagonal covariances agree:
`cov[X i, X j; μ] = cov[X k, X l; μ]` whenever `i < j` and `k < l`. -/
theorem Contractable.covariance_eq_of_lt (hX : Contractable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) {i j k l : ℕ} (hij : i < j) (hkl : k < l) :
    cov[X i, X j; μ] = cov[X k, X l; μ] := by
  exact covariance_eq_of_identDistrib_pair (hX.identDistrib_pair hX_meas hij hkl)

/-- **Uniform off-diagonal covariances from contractability.** For a contractable real-valued
process with a.e. measurable coordinates, any two off-diagonal covariances agree:
`cov[X i, X j; μ] = cov[X k, X l; μ]` whenever `i ≠ j` and `k ≠ l`. -/
theorem Contractable.covariance_eq_of_ne (hX : Contractable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l) :
    cov[X i, X j; μ] = cov[X k, X l; μ] := by
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · rcases lt_or_gt_of_ne hkl with hkl_lt | hlk_lt
    · exact hX.covariance_eq_of_lt hX_meas hij_lt hkl_lt
    · rw [covariance_comm (X k) (X l)]
      exact hX.covariance_eq_of_lt hX_meas hij_lt hlk_lt
  · rw [covariance_comm (X i) (X j)]
    rcases lt_or_gt_of_ne hkl with hkl_lt | hlk_lt
    · exact hX.covariance_eq_of_lt hX_meas hji_lt hkl_lt
    · rw [covariance_comm (X k) (X l)]
      exact hX.covariance_eq_of_lt hX_meas hji_lt hlk_lt

/-- **The uniform covariance structure of a contractable L² sequence.** A contractable
real-valued process with `L²` coordinates has constant coordinate means and variances, and a
single common off-diagonal covariance: any two unequal-index pairs have equal covariance. This
is the seed of the Layer 3 L² route to de Finetti. -/
theorem contractable_covariance_structure [IsProbabilityMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) :
    (∀ i j, μ[X i] = μ[X j]) ∧ (∀ i j, Var[X i; μ] = Var[X j; μ]) ∧
      (∀ i j k l, i ≠ j → k ≠ l → cov[X i, X j; μ] = cov[X k, X l; μ]) := by
  have hmeas : ∀ n, AEMeasurable (X n) μ := fun n => (hX_L2 n).aestronglyMeasurable.aemeasurable
  exact ⟨fun i j => hX.integral_coord_eq hmeas i j, fun i j => hX.variance_coord_eq hmeas i j,
    fun _ _ _ _ hij hkl => hX.covariance_eq_of_ne hmeas hij hkl⟩

end Real

end Probability

end TauCeti
