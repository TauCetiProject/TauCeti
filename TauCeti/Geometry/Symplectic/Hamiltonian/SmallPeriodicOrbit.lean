/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
import TauCeti.Analysis.ODE.Yorke
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation

/-!
# One-periodic orbits of small autonomous Hamiltonians on a symplectic vector space

Let `(V, ω)` be a symplectic vector space, `F : V → ℝ` a `C²` function and `K ⊆ V` a bounded set.
This file shows that for `ε` small, depending only on `ω`, `F` and `K`, every `1`-periodic orbit
of the Hamiltonian vector field of `ε F` with values in `K` is constant
(`TauCeti.SymplecticForm.exists_pos_forall_eq_const_of_periodic_hamiltonianVectorField_const_mul`).
The field `ε X_F` is `|ε| L`-Lipschitz on `K`
(`TauCeti.SymplecticForm.exists_forall_lipschitzOnWith_hamiltonianVectorField`), and a
`1`-periodic orbit of a field that is Lipschitz with a small constant along it is constant by
Yorke's period bound (`TauCeti.exists_pos_forall_periodic_eq_const_of_lipschitzOnWith`).

On a closed manifold the corresponding statement is
`exists_pos_forall_periodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`. The statement here is for a symplectic vector
space, the local model of a symplectic manifold.

## References

* J. A. Yorke, *Periods of periodic solutions and the Lipschitz constant*, Proc. Amer. Math. Soc.
  **22** (1969), 509–512.
-/

public section

open Set Function

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {F : V → ℝ} {K : Set V}

/-- **Small autonomous Hamiltonians have only constant `1`-periodic orbits in a bounded set.** For
a `C²` function `F` and a bounded set `K`, there is `ε₀ > 0` such that for `|ε| < ε₀` every
`1`-periodic orbit of the Hamiltonian vector field of `ε F` with values in `K` is constant. -/
theorem exists_pos_forall_eq_const_of_periodic_hamiltonianVectorField_const_mul
    (hF : ContDiff ℝ 2 F) (hK : Bornology.IsBounded K) :
    ∃ ε₀ > (0 : ℝ), ∀ ⦃ε : ℝ⦄, |ε| < ε₀ → ∀ ⦃x : ℝ → V⦄, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ ε * F y) (x t)) t) →
      (∀ t, x t ∈ K) → x = fun _ ↦ x 0 := by
  obtain ⟨L, hL⟩ := ω.exists_forall_lipschitzOnWith_hamiltonianVectorField (H := fun _ ↦ F)
    (hF.comp contDiff_snd) (fun _ ↦ rfl) hK
  obtain ⟨c, hc, hyorke⟩ := exists_pos_forall_periodic_eq_const_of_lipschitzOnWith (E := V)
  refine ⟨c / (L + 1), by positivity, fun ε hε x hper hx hxK ↦ ?_⟩
  -- The field of `ε F` is `ε X_F`, which is `|ε| L`-Lipschitz on `K`, and `|ε| L < c`.
  have hX : ω.hamiltonianVectorField (fun y ↦ ε * F y) = (ε • ·) ∘ ω.hamiltonianVectorField F :=
    funext (ω.hamiltonianVectorField_const_mul ε F)
  have hlip : LipschitzOnWith (‖ε‖₊ * L) (ω.hamiltonianVectorField (fun y ↦ ε * F y))
      (range x) :=
    hX ▸ (lipschitzWith_smul ε).comp_lipschitzOnWith ((hL 0).mono (range_subset_iff.2 hxK))
  refine hyorke _ x _ 1 hper one_pos hx hlip ?_
  have hεL : |ε| * (L + 1) < c := (lt_div_iff₀ (by positivity)).1 hε
  simp only [NNReal.coe_mul, coe_nnNorm, Real.norm_eq_abs, mul_one]
  nlinarith [abs_nonneg ε]

end TauCeti.SymplecticForm
