/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Torus integration on continuous boundary functions

`TauCeti.torusIntegralCLM` integrates continuous functions on a product of circles. Its
operator norm is bounded by the product of their circumferences. Thus uniform limits and
parameter power series on the distinguished boundary of a polydisc can be integrated
without choosing extensions of the boundary data to the ambient coordinate space.

Radii may be negative or zero. For complete codomains, the dimension-zero integral is
evaluation. Any zero radius in positive dimension makes the integral zero.
-/

public section

open Complex MeasureTheory Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

private theorem integrable_torusBoundary (c : Fin n → ℂ) (R : Fin n → ℝ)
    (f : C((i : Fin n) → sphere (c i) |R i|, E)) :
    IntegrableOn (fun θ : Fin n → ℝ => (∏ i, (R i : ℂ) * exp (θ i * I) * I) •
      f (fun i => ⟨torusMap c R θ i, circleMap_mem_sphere' (c i) (R i) (θ i)⟩))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi)) := by
  apply Continuous.integrableOn_Icc
  apply Continuous.smul (by fun_prop)
  apply f.continuous.comp
  exact continuous_pi fun i =>
    (((continuous_circleMap (c i) (R i)).comp (continuous_apply i)).subtype_mk _)

/-- Torus integration as a continuous complex linear map on continuous boundary functions.
The radii need not be positive. For an incomplete codomain the integral is zero, following
Mathlib's convention. -/
noncomputable def torusIntegralCLM (c : Fin n → ℂ) (R : Fin n → ℝ) :
    C((i : Fin n) → sphere (c i) |R i|, E) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi),
        (∏ i, (R i : ℂ) * exp (θ i * I) * I) •
          f (fun i => ⟨torusMap c R θ i, circleMap_mem_sphere' (c i) (R i) (θ i)⟩)
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, smul_add]
        exact integral_add (integrable_torusBoundary c R f) (integrable_torusBoundary c R g)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_comm _ a]
        exact integral_smul a _ }
    ((2 * Real.pi) ^ n * ∏ i, |R i|) fun f => by
      -- Extend only to apply Mathlib's existing torus-integral estimate. No continuity
      -- away from the boundary is needed by that estimate.
      let v : ((i : Fin n) → sphere (c i) |R i|) → (Fin n → ℂ) := fun z i => z i
      have hv : Function.Injective v := fun x y h =>
        funext fun i => Subtype.ext (congrFun h i)
      let g := Function.extend v f 0
      have hg : ∀ θ, g (torusMap c R θ) =
          f (fun i => ⟨torusMap c R θ i, circleMap_mem_sphere' (c i) (R i) (θ i)⟩) :=
        fun θ => hv.extend_apply f 0
          (fun i => ⟨torusMap c R θ i, circleMap_mem_sphere' (c i) (R i) (θ i)⟩)
      simpa only [torusIntegral, hg, LinearMap.coe_mk, AddHom.coe_mk] using
        (norm_torusIntegral_le_of_norm_le_const (c := c) (R := R) (f := g) (C := ‖f‖) (by
          intro θ
          rw [hg]
          exact f.norm_coe_le_norm _))

/-- The boundary integral is the usual integral in angular coordinates. -/
theorem torusIntegralCLM_apply (c : Fin n → ℂ) (R : Fin n → ℝ)
    (f : C((i : Fin n) → sphere (c i) |R i|, E)) :
    torusIntegralCLM c R f = ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi),
      (∏ i, (R i : ℂ) * exp (θ i * I) * I) •
        f (fun i => ⟨torusMap c R θ i, circleMap_mem_sphere' (c i) (R i) (θ i)⟩) := (rfl)

/-- An ambient representative of the boundary data has the same torus integral. -/
theorem torusIntegralCLM_eq_torusIntegral (c : Fin n → ℂ) (R : Fin n → ℝ)
    (f : C((i : Fin n) → sphere (c i) |R i|, E)) (g : (Fin n → ℂ) → E)
    (hg : ∀ z, f z = g (fun i => z i)) :
    torusIntegralCLM c R f = ∯ z in T(c, R), g z := by
  simp only [torusIntegralCLM_apply, hg, torusIntegral]

/-- The operator norm is at most the product of the circumferences. -/
theorem norm_torusIntegralCLM_le (c : Fin n → ℂ) (R : Fin n → ℝ) :
    ‖torusIntegralCLM (E := E) c R‖ ≤ (2 * Real.pi) ^ n * ∏ i, |R i| := by
  apply LinearMap.mkContinuous_norm_le
  positivity

/-- A zero radius makes torus integration the zero operator. -/
theorem torusIntegralCLM_eq_zero_of_radius_eq_zero (c : Fin n → ℂ) (R : Fin n → ℝ)
    (i : Fin n) (hi : R i = 0) : torusIntegralCLM (E := E) c R = 0 := by
  have hprod : ∏ j, |R j| = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  apply norm_le_zero_iff.mp
  simpa only [hprod, mul_zero] using norm_torusIntegralCLM_le (E := E) c R

/-- In dimension zero, torus integration evaluates at the unique boundary point. -/
@[simp]
theorem torusIntegralCLM_dim0 [CompleteSpace E] (c : Fin 0 → ℂ) (R : Fin 0 → ℝ)
    (f : C((i : Fin 0) → sphere (c i) |R i|, E)) :
    torusIntegralCLM c R f = f (fun i => Fin.elim0 i) := by
  rw [torusIntegralCLM_eq_torusIntegral c R f (fun _ => f (fun i => Fin.elim0 i))
    (fun _ => congrArg f (Subsingleton.elim _ _)), torusIntegral_dim0]

end TauCeti
