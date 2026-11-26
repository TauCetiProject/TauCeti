/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import TauCeti.Analysis.ODE.Propagator.Translate

/-!
# The chain rule and locality of the Dirac fundamental matrix

For a potential `q` and the fundamental matrix `M_q(t, z)` of the Dirac system
`Ω X' = z X - Q_q X` (`TauCeti.diracFundamentalMatrix`):

* **Locality.** `M_q(t, z)` depends only on the values of `q` almost everywhere between `0` and `t`
  (`TauCeti.diracFundamentalMatrix_congr_ae`).
* **The chain rule.** If `q` is integrable on an interval containing `0`, `s` and `t`, then
  `M_q(t, z) = M_{q(s + ·)}(t - s, z) M_q(s, z)` (`TauCeti.diracFundamentalMatrix_eq_mul`): the
  fundamental matrix of the potential translated by `s` carries the solution at time `s` to the
  solution at time `t`.

Both come from the propagator: locality from `TauCeti.propagator_congr_ae`, the chain rule from the
composition law `TauCeti.propagator_comp_propagator` and the translation of time
`TauCeti.propagator_comp_add_right`.

## References

* R. Romanov, *Canonical systems and de Branges spaces*, arXiv:1408.6022, §1.
-/

public section

open MeasureTheory Set Matrix
open scoped Interval

namespace TauCeti

variable {q q' : ℝ → ℂ} {a b s t : ℝ}

/-- **Locality.** The fundamental matrix `M_q(t, z)` depends only on `q` almost everywhere between
`0` and `t`. -/
theorem diracFundamentalMatrix_congr_ae (h : ∀ᵐ u, u ∈ Ι 0 t → q u = q' u) (z : ℂ) :
    diracFundamentalMatrix q t z = diracFundamentalMatrix q' t z := by
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  simp only [toEuclideanCLM_diracFundamentalMatrix]
  refine propagator_congr_ae ?_
  filter_upwards [h] with u hu hmem
  simp [diracCoeff_def, hu hmem]

/-- **The chain rule.** If `q` is integrable on `[a, b]` and `0, s, t ∈ [a, b]`, then
`M_q(t, z) = M_{q(s + ·)}(t - s, z) M_q(s, z)`. -/
theorem diracFundamentalMatrix_eq_mul (hq : IntegrableOn q (Icc a b)) (h0 : 0 ∈ Icc a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (z : ℂ) :
    diracFundamentalMatrix q t z =
      diracFundamentalMatrix (fun u ↦ q (s + u)) (t - s) z * diracFundamentalMatrix q s z := by
  set P := fun u ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z u)
  have hP : IntegrableOn P (Icc a b) := integrableOn_toEuclideanCLM_diracCoeff hq z
  have hshift : (fun u ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      (diracCoeff (fun u ↦ q (s + u)) z u)) = fun u ↦ P (u + s) := by
    ext1 u
    simp only [P, diracCoeff_def, add_comm s u]
  have h0' : (0 : ℝ) ∈ Icc (a - s) (b - s) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : t - s ∈ Icc (a - s) (b - s) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  simp only [map_mul, toEuclideanCLM_diracFundamentalMatrix]
  rw [hshift, propagator_comp_add_right hP h0' ht', sub_add_cancel, zero_add,
    ContinuousLinearMap.mul_def, propagator_comp_propagator hP hs h0 ht]

end TauCeti
