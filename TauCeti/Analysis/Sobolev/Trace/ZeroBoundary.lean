/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Hyperplane
public import TauCeti.Analysis.Sobolev.W1p.Extension

/-!
# Hyperplane traces of zero-boundary Sobolev functions

A function in `H¹₀(Ω)` extends by zero to a whole-space `H¹` function. Composing that extension
with the whole-space hyperplane trace gives a canonical trace of zero-boundary functions on every
hyperplane. If the hyperplane misses `Ω`, this trace vanishes. In particular, `H¹₀` functions on a
half-space have zero trace on its boundary hyperplane.

This is the flat-model inclusion `H¹₀(Ω) ⊆ ker(trace)`. The reverse inclusion requires a trace
defined on all of `H¹(Ω)` and an approximation argument near the boundary.

## Main declarations

* `TauCeti.W1p0.hyperplaneTrace`: trace after whole-space extension by zero;
* `TauCeti.W1p0.norm_hyperplaneTrace_le`: its norm is at most the `H¹₀` norm;
* `TauCeti.W1p0.hyperplaneTrace_apply_eq_zero_of_forall_not_mem` and
  `TauCeti.W1p0.hyperplaneTrace_eq_zero_of_forall_not_mem`: the trace vanishes when the
  hyperplane misses the domain.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, Section 5.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]
  {Omega : Opens (WithLp 2 (ℝ × E))}

namespace W1p0

/-- The `L²` trace on `{a} × E` of a zero-boundary Sobolev function, obtained by extending the
function by zero to the whole space before taking the whole-space hyperplane trace. -/
def hyperplaneTrace (a : ℝ) :
    W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega 2 →L[ℝ]
      Lp ℝ 2 (volume : Measure E) :=
  (W1p.hyperplaneTrace a).comp
    ((w1p0Submodule (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2).toSubmodule.subtypeL.comp
      (W1p0.extendByZeroL (Omega := Omega) le_top))

/-- Taking the hyperplane trace of a zero-boundary function means taking the whole-space trace of
its extension by zero. -/
@[simp]
theorem hyperplaneTrace_apply (a : ℝ)
    (u : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega 2) :
    hyperplaneTrace (Omega := Omega) a u =
      W1p.hyperplaneTrace a
        (W1p0.extendByZeroL (Omega := Omega) le_top u :
          W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :=
  (rfl)

/-- The trace norm is at most the zero-boundary `H¹` norm. -/
theorem norm_hyperplaneTrace_le (a : ℝ)
    (u : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega 2) :
    ‖hyperplaneTrace (Omega := Omega) a u‖ ≤ ‖u‖ := by
  calc
    ‖hyperplaneTrace (Omega := Omega) a u‖ ≤
        ‖(W1p0.extendByZeroL (Omega := Omega) le_top u :
          W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2)‖ :=
      W1p.norm_hyperplaneTrace_le a _
    _ = ‖W1p0.extendByZeroL (Omega := Omega) le_top u‖ := rfl
    _ = ‖u‖ := W1p0.norm_extendByZeroL le_top u

/-- The operator norm of the zero-boundary hyperplane trace is at most one. -/
theorem opNorm_hyperplaneTrace_le (a : ℝ) :
    ‖hyperplaneTrace (Omega := Omega) a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_hyperplaneTrace_le (Omega := Omega) a u

private theorem hyperplaneTrace_ofTestFunction_eq_zero (a : ℝ)
    (hOmega : ∀ y : E, WithLp.toLp 2 (a, y) ∉ Omega) (phi : 𝓓(Omega, ℝ)) :
    hyperplaneTrace (Omega := Omega) a
        ⟨W1p.ofTestFunctionₗ volume Omega 2 phi, W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩ =
      0 := by
  let psi : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) := TestFunction.monoCLM ℝ phi
  have hext :
      (W1p0.extendByZeroL (Omega := Omega) le_top
          ⟨W1p.ofTestFunctionₗ volume Omega 2 phi,
            W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩ :
        W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) =
        W1p.ofTestFunctionₗ volume ⊤ 2 psi := by
    apply Subtype.ext
    exact (W1p0.coe_extendByZeroL le_top
      ⟨W1p.ofTestFunctionₗ volume Omega 2 phi,
        W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩).trans
      (Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ le_top phi)
  rw [hyperplaneTrace_apply, hext]
  apply Lp.ext
  filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae a psi,
    Lp.coeFn_zero ℝ 2 (volume : Measure E)] with y hy hzero
  rw [hy, hzero]
  have hphi : phi (WithLp.toLp 2 (a, y)) = 0 := phi.zero_on_compl (hOmega y)
  simpa only [psi, TestFunction.monoCLM_apply, le_rfl, le_top, and_self, ↓reduceIte,
    Pi.zero_apply] using hphi

/-- If the hyperplane `{a} × E` misses `Ω`, a zero-boundary Sobolev function on `Ω` has zero trace
there. This is the pointwise form of the flat-model inclusion `H¹₀(Ω) ⊆ ker(trace)`. -/
theorem hyperplaneTrace_apply_eq_zero_of_forall_not_mem (a : ℝ)
    (hOmega : ∀ y : E, WithLp.toLp 2 (a, y) ∉ Omega)
    (u : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega 2) :
    hyperplaneTrace (Omega := Omega) a u = 0 := by
  let T := hyperplaneTrace (Omega := Omega) a
  let s : Set (W1p (volume : Measure (WithLp 2 (ℝ × E))) Omega 2) :=
    Subtype.val '' (T.ker : Set (W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega 2))
  have hs : IsClosed s :=
    ((w1p0Submodule (volume : Measure (WithLp 2 (ℝ × E))) Omega 2).isClosed
      |>.isClosedEmbedding_subtypeVal).isClosedMap _ T.isClosed_ker
  have htest (phi : 𝓓(Omega, ℝ)) : W1p.ofTestFunctionₗ volume Omega 2 phi ∈ s := by
    refine ⟨⟨W1p.ofTestFunctionₗ volume Omega 2 phi,
      W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩, ?_, rfl⟩
    exact hyperplaneTrace_ofTestFunction_eq_zero a hOmega phi
  obtain ⟨v, hv, hvu⟩ :=
    w1p0Submodule_subset_of_isClosed hs htest u.2
  have hv_eq : v = u := Subtype.ext hvu
  have hv_zero : T v = 0 := by
    exact hv
  simpa only [T, hv_eq, zero_apply] using hv_zero

/-- If the hyperplane `{a} × E` misses `Ω`, the hyperplane trace operator on `H¹₀(Ω)` is zero. -/
theorem hyperplaneTrace_eq_zero_of_forall_not_mem (a : ℝ)
    (hOmega : ∀ y : E, WithLp.toLp 2 (a, y) ∉ Omega) :
    hyperplaneTrace (Omega := Omega) a = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  exact hyperplaneTrace_apply_eq_zero_of_forall_not_mem a hOmega u

end W1p0

end TauCeti
