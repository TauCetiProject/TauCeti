/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.LinearAlgebra.Orientation.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous families of linear maps transport orientations alike

Let `L x : E → F` be a family of continuous linear maps between real normed spaces, continuous at
`x₀`, whose value at `x₀` is a linear equivalence `f₀`. Near `x₀`, every linear equivalence equal
to `L x` transports an orientation of `E` as `f₀` does
(`Orientation.eventually_map_eq_map_of_continuousAt`): relative to `f₀`, the determinant of `L x`
is `1` at `x₀`, hence positive nearby.

This is the local constancy step behind continuous families of orientations, such as orientations
of vector bundles transported along fibrewise isomorphisms.

## Main results

* `Orientation.eventually_map_eq_map_of_continuousAt`: near `x₀`, the linear equivalences given by
  a continuous family `L` transport an orientation as its value at `x₀` does.
-/

public section

open Filter Module
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ι : Type*} [Fintype ι]

/-- **Orientation transport is locally constant along a continuous family.** Let `L` be a family of
continuous linear maps `E → F`, continuous at `x₀` with value the linear equivalence `f₀` there.
Near `x₀`, every linear equivalence `f` equal to `L x` transports an orientation `c` of `E` as `f₀`
does. Continuity of `L` is needed only when `E` is finite-dimensional: otherwise `ι` is empty, and
any two linear equivalences transport `c` alike. -/
theorem Orientation.eventually_map_eq_map_of_continuousAt {X : Type*} [TopologicalSpace X]
    {x₀ : X} (hι : Fintype.card ι = finrank ℝ E) (c : Orientation ℝ E ι) {f₀ : E ≃L[ℝ] F}
    {L : X → E →L[ℝ] F} (hL : FiniteDimensional ℝ E → ContinuousAt L x₀)
    (hL₀ : L x₀ = f₀) :
    ∀ᶠ x in 𝓝 x₀, ∀ f : E ≃L[ℝ] F, (f : E →L[ℝ] F) = L x →
      Orientation.map ι f.toLinearEquiv c = Orientation.map ι f₀.toLinearEquiv c := by
  rcases isEmpty_or_nonempty ι with hι₀ | hι₀
  · -- With `ι` empty, transport along any self-equivalence of `E` fixes every orientation.
    refine Eventually.of_forall fun x f _ ↦ ?_
    have h := Orientation.map_of_isEmpty (x := c)
      (f := f.toLinearEquiv.trans f₀.toLinearEquiv.symm)
    rw [Orientation.map_trans, ← Orientation.map_symm, Equiv.symm_apply_eq] at h
    exact h
  -- Otherwise `E` is finite-dimensional, and the determinant of `f₀⁻¹ ∘ L x`, which is `1` at
  -- `x₀`, is positive near `x₀`.
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
  let K (x : X) : E →L[ℝ] E := (f₀.symm : F →L[ℝ] E).comp (L x)
  have hK₀ : (K x₀).det = 1 := by
    rw [ContinuousLinearMap.det, show K x₀ = ContinuousLinearMap.id ℝ E by ext v; simp [K, hL₀],
      ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hK : ContinuousAt K x₀ := ContinuousAt.clm_comp continuousAt_const (hL this)
  filter_upwards [(ContinuousLinearMap.continuous_det.continuousAt.comp hK).eventually
    (lt_mem_nhds (hK₀ ▸ one_pos))] with x hx f hf
  refine (Orientation.map_eq_map_iff_det_pos c _ _ hι).mpr ?_
  have hKf : K x = (f.trans f₀.symm : E →L[ℝ] E) := by
    ext v
    simp [K, ← hf]
  rw [Function.comp_apply, hKf] at hx
  simpa [ContinuousLinearMap.det] using hx
