/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Taming is an open condition

Let `E` be a finite-dimensional real normed space and `J` a continuous linear endomorphism of `E`.
A continuous alternating two-form `f` tames `J` when `f(u, J u) > 0` for every `u ≠ 0`. The set of
forms taming `J` is open (`ContinuousAlternatingMap.isOpen_setOf_forall_ne_zero_pos`): by
homogeneity it suffices to test positivity on the unit sphere, which is compact, and evaluation is
jointly continuous in the form and the vector.

For a symplectic form and an almost complex structure `J`, this is the openness of taming
(`TauCeti.SymplecticForm.Tames`) in the form, which makes symplectic orientations locally constant
in continuous families of symplectic forms.

Dually, for continuous bilinear forms `B` and continuous linear endomorphisms `A` of `E`, the
condition `B(u, A u) > 0` for every `u ≠ 0` is open in the pair `(B, A)`
(`TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos`): the map `(B, A) ↦ B(·, A ·)` is
continuous, and positive definite forms form an open set
(`TauCeti.isOpen_setOf_forall_bilinear_apply_self_pos`). For a fixed form, the endomorphisms it
tames form an open set (`TauCeti.isOpen_setOf_forall_endomorphism_pos`). This makes complex
orientations locally constant in continuous families of almost complex structures.
-/

public section

open Filter
open scoped Topology

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The continuous alternating two-forms `f` taming a continuous linear endomorphism `J`, that is
with `f(u, J u) > 0` for every `u ≠ 0`, form an open set. -/
theorem isOpen_setOf_forall_ne_zero_pos (J : E →L[ℝ] E) :
    IsOpen {f : E [⋀^Fin 2]→L[ℝ] ℝ | ∀ u ≠ 0, 0 < f ![u, J u]} := by
  refine isOpen_iff_mem_nhds.2 fun f₀ hf₀ ↦ ?_
  -- Positivity on the compact unit sphere persists near `f₀`.
  have hsphere : ∀ᶠ f in 𝓝 f₀, ∀ u ∈ Metric.sphere (0 : E) 1, 0 < f ![u, J u] := by
    refine (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually fun u hu ↦ ?_
    have hc : ContinuousAt (fun z : (E [⋀^Fin 2]→L[ℝ] ℝ) × E ↦ z.1 ![z.2, J z.2]) (f₀, u) :=
      continuousAt_fst.eval (by fun_prop)
    exact hc.eventually (lt_mem_nhds (hf₀ u (ne_zero_of_mem_unit_sphere ⟨u, hu⟩)))
  filter_upwards [hsphere] with f hf u hu
  -- Rescale `u` to the unit sphere.
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have h := hf (‖u‖⁻¹ • u) (by simp [norm_smul, hn])
  have hsmul : ![‖u‖⁻¹ • u, J (‖u‖⁻¹ • u)] = fun i ↦ ‖u‖⁻¹ • ![u, J u] i := by
    ext i
    fin_cases i <;> simp
  rw [hsmul, f.map_smul_univ, smul_eq_mul, Fin.prod_const] at h
  exact pos_of_mul_pos_right h (by positivity)

end ContinuousAlternatingMap

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The pairs `(B, A)` of a continuous bilinear form and a continuous linear endomorphism of `E`
with `B(u, A u) > 0` for every `u ≠ 0` form an open set. -/
theorem isOpen_setOf_forall_bilinear_apply_endomorphism_pos :
    IsOpen {p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) | ∀ u, u ≠ 0 → 0 < p.1 u (p.2 u)} := by
  -- `(B, A) ↦ B(·, A ·)` is continuous, and positive definite forms form an open set.
  have hc : Continuous fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) ↦
      ((ContinuousLinearMap.compL ℝ E E ℝ).flip p.2).comp p.1 := by fun_prop
  exact isOpen_setOf_forall_bilinear_apply_self_pos.preimage hc

/-- The continuous linear endomorphisms `A` of `E` tamed by a fixed continuous bilinear form `B`,
that is with `B(u, A u) > 0` for every `u ≠ 0`, form an open set. -/
theorem isOpen_setOf_forall_endomorphism_pos (B : E →L[ℝ] E →L[ℝ] ℝ) :
    IsOpen {A : E →L[ℝ] E | ∀ u, u ≠ 0 → 0 < B u (A u)} :=
  isOpen_setOf_forall_bilinear_apply_endomorphism_pos.preimage
    (continuous_const.prodMk continuous_id)

end TauCeti
