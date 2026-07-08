module

public import TauCeti.Probability.Exchangeability.Contractability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# The covariance structure of a contractable L² sequence

This file opens the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), whose first analytic input is the *uniform covariance
structure of a contractable L² sequence* (`contractable_covariance_structure`). It also
supplies the two Layer 3 preliminaries listed before it — "equality of means and integrals
from equal one-dimensional laws" and "equality of pair covariances from equal
two-dimensional laws" — specialized to a contractable process.

For a contractable process the one- and two-coordinate laws are constant along strictly
increasing selections (`Contractable.map_single`, `Contractable.map_pair`). This is packaged
here as `IdentDistrib` facts:

* `Contractable.identDistrib_coord`: every coordinate `X i` is identically distributed to
  every other coordinate `X j`;
* `Contractable.identDistrib_pair`: for `i < j` the pair `(X i, X j)` is identically
  distributed to `(X 0, X 1)`.

For a real-valued sequence these give the uniform first- and second-moment structure:

* `Contractable.integral_coord_eq`: all coordinate means agree;
* `Contractable.variance_coord_eq`: all coordinate variances agree;
* `Contractable.covariance_eq_of_lt`: every off-diagonal covariance `cov[X i, X j; μ]`
  (`i < j`) equals `cov[X 0, X 1; μ]`.

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

section IdentDistrib

variable {α : Type*} [MeasurableSpace α] {X : ℕ → Ω → α}

/-- Evaluating the one-coordinate block law `blockLaw μ X (fun _ => i)` at its single
coordinate recovers the law of `X i`. -/
private theorem map_coordEval_blockLaw (i : ℕ) (hX_meas : ∀ n, AEMeasurable (X n) μ) :
    (blockLaw μ X (fun _ : Fin 1 => i)).map (fun v : Fin 1 → α => v 0) = μ.map (X i) := by
  rw [blockLaw_def, AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply 0).aemeasurable
    (aemeasurable_pi_lambda _ fun _ => hX_meas i)]
  rfl

/-- Evaluating the two-coordinate block law `blockLaw μ X ![i, j]` at its two coordinates
recovers the joint law of `(X i, X j)`. -/
private theorem map_pairEval_blockLaw (i j : ℕ) (hX_meas : ∀ n, AEMeasurable (X n) μ) :
    (blockLaw μ X ![i, j]).map (fun v : Fin 2 → α => (v 0, v 1))
      = μ.map (fun ω => (X i ω, X j ω)) := by
  have hcomp : ((fun v : Fin 2 → α => (v 0, v 1)) ∘ fun ω (l : Fin 2) => X (![i, j] l) ω)
      = fun ω => (X i ω, X j ω) := by
    funext ω
    simp [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [blockLaw_def, AEMeasurable.map_map_of_aemeasurable
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)).aemeasurable
    (aemeasurable_pi_lambda _ fun l => hX_meas (![i, j] l)), hcomp]

/-- **Coordinates of a contractable process are identically distributed.** For a contractable
process `X` with a.e. measurable coordinates, `X i` and `X j` have the same law. -/
theorem Contractable.identDistrib_coord (hX : Contractable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) (i j : ℕ) :
    IdentDistrib (X i) (X j) μ μ where
  aemeasurable_fst := hX_meas i
  aemeasurable_snd := hX_meas j
  map_eq := by
    rw [← map_coordEval_blockLaw i hX_meas, ← map_coordEval_blockLaw j hX_meas,
      hX.map_single (fun _ => i), hX.map_single (fun _ => j)]

/-- **Increasing pairs of a contractable process are identically distributed.** For a
contractable process `X` with a.e. measurable coordinates and `i < j`, the pair `(X i, X j)`
has the same joint law as `(X 0, X 1)`. -/
theorem Contractable.identDistrib_pair (hX : Contractable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) {i j : ℕ} (hij : i < j) :
    IdentDistrib (fun ω => (X i ω, X j ω)) (fun ω => (X 0 ω, X 1 ω)) μ μ where
  aemeasurable_fst := (hX_meas i).prodMk (hX_meas j)
  aemeasurable_snd := (hX_meas 0).prodMk (hX_meas 1)
  map_eq := by
    rw [← map_pairEval_blockLaw i j hX_meas, ← map_pairEval_blockLaw 0 1 hX_meas,
      hX.map_pair hij, hX.map_pair Nat.zero_lt_one]

end IdentDistrib

section Real

variable {X : ℕ → Ω → ℝ}

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
`L²` coordinates, every off-diagonal covariance `cov[X i, X j; μ]` with `i < j` equals the
single covariance `cov[X 0, X 1; μ]`. -/
theorem Contractable.covariance_eq_of_lt [IsProbabilityMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {i j : ℕ} (hij : i < j) :
    cov[X i, X j; μ] = cov[X 0, X 1; μ] := by
  have hmeas : ∀ n, AEMeasurable (X n) μ := fun n => (hX_L2 n).aestronglyMeasurable.aemeasurable
  have hmul : μ[X i * X j] = μ[X 0 * X 1] := by
    have h := (hX.identDistrib_pair hmeas hij).comp (measurable_fst.mul measurable_snd)
    simpa [Function.comp, Pi.mul_apply] using h.integral_eq
  rw [covariance_eq_sub (hX_L2 i) (hX_L2 j), covariance_eq_sub (hX_L2 0) (hX_L2 1), hmul]
  simp only [hX.integral_coord_eq hmeas i 0, hX.integral_coord_eq hmeas j 0,
    hX.integral_coord_eq hmeas 1 0]

/-- **The uniform covariance structure of a contractable L² sequence.** A contractable
real-valued process with `L²` coordinates has constant coordinate means and variances, and a
single common off-diagonal covariance `cov[X 0, X 1; μ]`. This is the seed of the Layer 3 L²
route to de Finetti. -/
theorem contractable_covariance_structure [IsProbabilityMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) :
    (∀ i j, μ[X i] = μ[X j]) ∧ (∀ i j, Var[X i; μ] = Var[X j; μ]) ∧
      (∀ i j, i < j → cov[X i, X j; μ] = cov[X 0, X 1; μ]) := by
  have hmeas : ∀ n, AEMeasurable (X n) μ := fun n => (hX_L2 n).aestronglyMeasurable.aemeasurable
  exact ⟨fun i j => hX.integral_coord_eq hmeas i j, fun i j => hX.variance_coord_eq hmeas i j,
    fun _ _ hij => hX.covariance_eq_of_lt hX_L2 hij⟩

end Real

end Probability

end TauCeti
