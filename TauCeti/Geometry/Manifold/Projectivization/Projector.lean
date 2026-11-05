/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.LinearAlgebra.Projectivization.Projector

/-!
# The projector embedding of real projective space is a closed analytic embedding

The projector map `Projectivization.projector` sends a line `[x]` of `ℝⁿ⁺¹` to the matrix
`x xᵀ / (xᵀ x)`, and is a homeomorphism from real projective space onto the compact real algebraic
set of symmetric idempotent matrices of trace one (`Projectivization.isClosedEmbedding_projector`).
Here we read it in the matrix entries, as the map `p ↦ (projector p a b)_(a, b)` into
`Fin (n + 1) × Fin (n + 1) → ℝ`, and show that it is a closed analytic embedding for the standard
analytic manifold structure of real projective space.

In homogeneous coordinates the entries `x a * x b / (xᵀ x)` are rational functions with a
denominator which does not vanish on the nonzero vectors, so the map is analytic
(`Projectivization.contMDiff_projector`). On the standard affine open `{x_i ≠ 0}` it has an analytic
left inverse: the `i`-th diagonal entry `A i i` of its value `A` is nonzero, and the inverse chart
at `i` applied to the ratios `A (i.succAbove k) i / A i i` recovers the line
(`Projectivization.affineChart_eq_projector_div`). So its differential is injective
(`Projectivization.isImmersion_projector`), and since projective space is compact it is a closed
analytic embedding (`Projectivization.isSmoothEmbedding_projector`). Together with the
semialgebraicity of the same chart maps in
`TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding`, this exhibits the projector map as a Nash
embedding: analytic and semialgebraic in both directions on every standard affine chart.

## Main results

* `Projectivization.contMDiff_projector`: the projector map is `C^r` for every `r`, including the
  analytic order `ω`.
* `Projectivization.isImmersion_projector`: it is a `C^r` immersion for every `r ≥ 1`.
* `Projectivization.isSmoothEmbedding_projector`: it is a closed `C^r` embedding for every `r ≥ 1`,
  in particular a closed analytic embedding.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §3, p. 464, for the use of this embedding to reduce triangulation of real
projective spaces to the affine case.
-/

public section

open Set Function Topology Manifold
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

variable {n : ℕ}

/-- The projector map of real projective space, read in the matrix entries, is `C^r` for every
`r`; for `r = ω` it is analytic. In homogeneous coordinates its entries are the rational functions
`x a * x b / (xᵀ x)`. -/
theorem contMDiff_projector (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) × Fin (n + 1) → ℝ) r
      fun p : ℙ ℝ (Fin (n + 1) → ℝ) ↦ fun q : Fin (n + 1) × Fin (n + 1) ↦ projector p q.1 q.2 := by
  refine contMDiff_of_contDiffOn_mk (F := fun v q ↦ v q.1 * v q.2 / (v ⬝ᵥ v))
    (contDiffOn_pi.2 fun q ↦ ?_) fun v hv ↦ ?_
  · have hc (k : Fin (n + 1)) : ContDiff ℝ r fun v : Fin (n + 1) → ℝ ↦ v k :=
      contDiff_apply ℝ (fun _ ↦ ℝ) k
    exact ((hc q.1).mul (hc q.2)).contDiffOn.div
      (ContDiff.sum fun k _ ↦ (hc k).mul (hc k)).contDiffOn
      fun v hv ↦ dotProduct_self_eq_zero.not.mpr hv
  · funext q
    rw [projector_mk, rankOneProjector_apply]

/-- **The projector map is an immersion.** The projector map of real projective space, read in
the matrix entries, is a `C^r` immersion for every `r ≥ 1`. Near a point of the affine open
`{x_i ≠ 0}` it has the analytic left inverse sending a matrix `A` with `A i i ≠ 0` to the line with
chart coordinates `A (i.succAbove k) i / A i i` at `i`. -/
theorem isImmersion_projector {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsImmersion 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) × Fin (n + 1) → ℝ) r
      fun p : ℙ ℝ (Fin (n + 1) → ℝ) ↦ fun q : Fin (n + 1) × Fin (n + 1) ↦ projector p q.1 q.2 := by
  rw [isImmersion_iff_forall_isImmersionAt]
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  have hx : projector x i i ≠ 0 := mt projector_apply_self_eq_zero_iff.1 (not_not.2 hi)
  -- The ratios of the entries of the `i`-th column are analytic where `A i i ≠ 0`.
  have hratio : ContDiffAt ℝ 1 (fun a : Fin (n + 1) × Fin (n + 1) → ℝ ↦
      fun k ↦ a (i.succAbove k, i) / a (i, i)) fun q ↦ projector x q.1 q.2 :=
    contDiffAt_pi.2 fun k ↦ (contDiff_apply ℝ (fun _ ↦ ℝ) (i.succAbove k, i)).contDiffAt.div
      (contDiff_apply ℝ (fun _ ↦ ℝ) (i, i)).contDiffAt hx
  exact ((contMDiff_projector r).contMDiffOn (s := univ)).isImmersionAt_of_comp_eventuallyEq_id
    isOpen_univ (mem_univ x) hr
    ((((contMDiff_affineChart_symm i 1).contMDiffAt).comp _
      hratio.contMDiffAt).mdifferentiableAt one_ne_zero)
    (Filter.eventuallyEq_of_mem ((isOpen_affineOpen i).mem_nhds hi) fun p hp ↦ by
      have h := (affineChart i).left_inv (x := p) (by simpa using hp)
      rwa [affineChart_eq_projector_div] at h)

/-- **The projector embedding is a closed analytic embedding.** The projector map of real
projective space, read in the matrix entries, is a `C^r` embedding for every `r ≥ 1`, including the
analytic order `ω`. Its image, the projector locus, is closed, since projective space is
compact. -/
theorem isSmoothEmbedding_projector {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) × Fin (n + 1) → ℝ) r
      fun p : ℙ ℝ (Fin (n + 1) → ℝ) ↦ fun q : Fin (n + 1) × Fin (n + 1) ↦ projector p q.1 q.2 :=
  ⟨isImmersion_projector hr, ((contMDiff_projector r).continuous.isClosedEmbedding
    fun _ _ h ↦ projector_injective (Matrix.ext fun a b ↦ congr_fun h (a, b))).isEmbedding⟩

end Projectivization
