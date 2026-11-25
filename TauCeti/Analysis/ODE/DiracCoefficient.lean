/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.Propagator.Holomorphic

/-!
# The Dirac coefficient

For a potential `q : ℝ → ℂ` with `f = Re q`, `g = Im q`, and a spectral parameter `z ∈ ℂ`, the
Dirac system `Ω X' = z X - Q_q X` with `Ω = [[0, 1], [-1, 0]]` and `Q_q = [[g, f], [f, -g]]` has
coefficient `-Ω(z - Q_q(t)) = [[f(t), -z - g(t)], [z - g(t), -f(t)]]` (`TauCeti.diracCoeff`).

It splits as `-z Ω + Ω Q_q(t)` (`TauCeti.diracCoeff_eq_smul_add`), where `-Ω = [[0, -1], [1, 0]]`
is an isometry of `EuclideanSpace ℂ (Fin 2)` and `Ω Q_q(t) = [[f(t), -g(t)], [-g(t), -f(t)]]` is
the coefficient at `z = 0`, which scales every vector by `|q(t)|`
(`TauCeti.norm_toEuclideanCLM_diracCoeff_zero_apply`). Hence in the Euclidean operator norm
`‖-Ω(z - Q_q(t))‖ ≤ |z| + |q(t)|` (`TauCeti.norm_toEuclideanCLM_diracCoeff_le`), and for `q`
integrable on `[a, b]` the propagator of the Dirac coefficient is an entire function of `z`
(`TauCeti.differentiable_propagator_diracCoeff`).
-/

public section

open MeasureTheory Set Matrix

namespace TauCeti

/-- The coefficient `-Ω(z - Q_q(t)) = [[f, -z - g], [z - g, -f]]` of the Dirac system
`Ω X' = z X - Q_q X`, where `Ω = [[0, 1], [-1, 0]]`, `Q_q = [[g, f], [f, -g]]`, `f = Re q` and
`g = Im q`. -/
def diracCoeff (q : ℝ → ℂ) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((q t).re : ℂ), -z - ((q t).im : ℂ); z - ((q t).im : ℂ), -((q t).re : ℂ)]

/-- The entries of the Dirac coefficient. -/
theorem diracCoeff_def (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t =
      !![((q t).re : ℂ), -z - ((q t).im : ℂ); z - ((q t).im : ℂ), -((q t).re : ℂ)] :=
  (rfl)

/-- The top-left entry `Re q(t)` of the Dirac coefficient. -/
@[simp] theorem diracCoeff_apply_zero_zero (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t 0 0 = ((q t).re : ℂ) :=
  (rfl)

/-- The top-right entry `-z - Im q(t)` of the Dirac coefficient. -/
@[simp] theorem diracCoeff_apply_zero_one (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t 0 1 = -z - ((q t).im : ℂ) :=
  (rfl)

/-- The bottom-left entry `z - Im q(t)` of the Dirac coefficient. -/
@[simp] theorem diracCoeff_apply_one_zero (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t 1 0 = z - ((q t).im : ℂ) :=
  (rfl)

/-- The bottom-right entry `-Re q(t)` of the Dirac coefficient. -/
@[simp] theorem diracCoeff_apply_one_one (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t 1 1 = -((q t).re : ℂ) :=
  (rfl)

/-- The Dirac coefficient is `-z Ω` plus its value `Ω Q_q(t)` at `z = 0`. -/
theorem diracCoeff_eq_smul_add (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t = z • !![0, -1; 1, 0] + diracCoeff q 0 t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracCoeff_def] <;> ring

/-- At `z = 0` the Dirac coefficient `Ω Q_q(t)` scales every vector of `ℂ²` by `|q(t)|`. -/
theorem norm_toEuclideanCLM_diracCoeff_zero_apply (q : ℝ → ℂ) (t : ℝ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (diracCoeff q 0 t) v‖ = ‖q t‖ * ‖v‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  simp only [mul_pow, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm]
  simp only [diracCoeff_def, ofLp_toEuclideanCLM, mulVec, dotProduct, Fin.sum_univ_two]
  simp [Complex.normSq_apply]
  ring

/-- **The Dirac coefficient in the Euclidean operator norm.** `‖-Ω(z - Q_q(t))‖ ≤ |z| + |q(t)|`. -/
theorem norm_toEuclideanCLM_diracCoeff_le (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (diracCoeff q z t)‖ ≤ ‖z‖ + ‖q t‖ := by
  rw [diracCoeff_eq_smul_add, map_add, map_smul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h : star !![(0 : ℂ), -1; 1, 0] = !![0, 1; -1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hJ : ‖toEuclideanCLM (𝕜 := ℂ) !![(0 : ℂ), -1; 1, 0]‖ = 1 :=
      CStarRing.norm_of_mem_unitary <| Unitary.map_mem _ <| Unitary.mem_iff.2 <| by
        constructor <;> simp [h, one_fin_two]
    rw [norm_smul, hJ, mul_one]
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v =>
      (norm_toEuclideanCLM_diracCoeff_zero_apply q t v).le

/-- The Dirac coefficient at `z = 0` is real-linear in `q(t)`. -/
private theorem toEuclideanCLM_diracCoeff_zero (q : ℝ → ℂ) (t : ℝ) :
    toEuclideanCLM (𝕜 := ℂ) (diracCoeff q 0 t) =
      ((q t).re : ℂ) • toEuclideanCLM (𝕜 := ℂ) !![1, 0; 0, -1] +
        ((q t).im : ℂ) • toEuclideanCLM (𝕜 := ℂ) !![0, -1; -1, 0] := by
  have h : diracCoeff q 0 t =
      ((q t).re : ℂ) • !![1, 0; 0, -1] + ((q t).im : ℂ) • !![0, -1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h, map_add, map_smul, map_smul]

/-- **The Dirac propagator is entire.** For `q` integrable on `[a, b]` and `s, t ∈ [a, b]`, the
propagator of the Dirac coefficient `r ↦ -Ω(z - Q_q(r))` on `ℂ²` is an entire function of `z`. -/
theorem differentiable_propagator_diracCoeff {q : ℝ → ℂ} {a b s t : ℝ}
    (hq : IntegrableOn q (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Differentiable ℂ fun z : ℂ ↦
      propagator (fun r ↦ toEuclideanCLM (𝕜 := ℂ) (diracCoeff q z r)) t s := by
  have hB : IntegrableOn (fun r ↦ toEuclideanCLM (𝕜 := ℂ) (diracCoeff q 0 r)) (Icc a b) := by
    simp_rw [toEuclideanCLM_diracCoeff_zero]
    exact (hq.re.ofReal.smul_const _).add (hq.im.ofReal.smul_const _)
  convert differentiable_propagator_smul_add (toEuclideanCLM (𝕜 := ℂ) !![(0 : ℂ), -1; 1, 0]) hB
    hs ht using 4 with z r
  rw [diracCoeff_eq_smul_add, map_add, map_smul]

end TauCeti
