/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone

/-!
# Lagrangian fibrations

Let `σ` be a fiberwise nondegenerate two-form on a manifold `M`. A **Lagrangian fibration**
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianFibration`) is a smooth submersion
`π : M → B` whose fibres are Lagrangian: at every point `x` the vertical space `ker dπ_x`, the
tangent space of the fibre through `x`, is a Lagrangian subspace of `(T_x M, σ_x)`. A **regular
Lagrangian torus fibration** (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
is moreover proper with connected fibres. This is the global setting of the Liouville–Arnold
theorem: for a symplectic form its fibres are tori
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`
in `TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Fibration`), and the torus bundle `T*B / Λ`
of a closed coframe is the model example
(`TauCeti.CotangentBundle.LatticeQuotient.isLagrangianTorusFibration_proj`).

With the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`, the functions pulled
back from the base generate the vertical motions:

* for a Lagrangian fibration `dim M = 2 dim B` (`IsLagrangianFibration.two_mul_finrank`);
* the Hamiltonian vector field of a pulled-back function `g ∘ π` is vertical, tangent to the fibres
  (`IsLagrangianFibration.hamiltonianVectorField_comp_mem_ker_mfderiv`), because `d(g ∘ π)`
  vanishes on `ker dπ`, so `X_(g ∘ π)` lies in the symplectic complement of `ker dπ`, which is
  `ker dπ` itself;
* consequently pulled-back functions Poisson-commute
  (`IsLagrangianFibration.poissonBracket_comp_eq_zero`): the coordinates of a chart of `B`, pulled
  back to `M`, form an involutive family with independent differentials;
* every maximal integral curve of such a vertical field stays in one fibre, so for a proper `π` the
  Hamiltonian vector field of every smooth pulled-back function is complete
  (`IsLagrangianFibration.isCompleteVectorField_hamiltonianVectorField_comp`).

These vertical Hamiltonian flows generate the fibrewise action of `T*B` from which the period
lattice `Λ ⊆ T*B` of the fibration is built; that action is not constructed here.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

variable (hσ J) in
/-- A **Lagrangian fibration** is a smooth submersion `π : M → B` whose fibres are Lagrangian: at
every point the vertical space `ker dπ_x` is a Lagrangian subspace of `(T_x M, σ_x)`. -/
structure IsLagrangianFibration (π : M → B) : Prop where
  /-- The projection of a Lagrangian fibration is a smooth submersion. -/
  isSubmersion : Manifold.IsSubmersion I J ∞ π
  /-- The vertical spaces of a Lagrangian fibration are Lagrangian. -/
  isLagrangian_ker_mfderiv : ∀ x, (hσ.symplecticFormAt x).IsLagrangian (mfderiv I J π x).ker

variable (hσ J) in
/-- A **regular Lagrangian torus fibration** is a proper Lagrangian fibration with connected
fibres. Its fibres are then compact, connected and nonempty, and for a symplectic form each of them
is a torus (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`). -/
structure IsLagrangianTorusFibration (π : M → B) : Prop extends IsLagrangianFibration J hσ π where
  /-- The projection of a regular Lagrangian torus fibration is proper. -/
  isProperMap : IsProperMap π
  /-- The fibres of a regular Lagrangian torus fibration are connected, in particular nonempty. -/
  isConnected_preimage_singleton : ∀ b, IsConnected (π ⁻¹' {b})

namespace IsLagrangianFibration

variable (h : hσ.IsLagrangianFibration J π)
include h

/-- The projection of a Lagrangian fibration is smooth. -/
theorem contMDiff : ContMDiff I J ∞ π :=
  h.isSubmersion.contMDiff

/-- The projection of a Lagrangian fibration is differentiable. -/
theorem mdifferentiableAt (x : M) : MDifferentiableAt I J π x :=
  h.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

/-- The derivative of the projection of a Lagrangian fibration is surjective. -/
theorem surjective_mfderiv (x : M) : Surjective (mfderiv I J π x) :=
  h.isSubmersion.surjective_mfderiv (by simp) x

/-- **A Lagrangian fibration halves the dimension**: the base of a Lagrangian fibration of a
nonempty manifold has half its dimension, `2 dim B = dim M`. -/
theorem two_mul_finrank [FiniteDimensional ℝ E] [Nonempty M] :
    2 * finrank ℝ F = finrank ℝ E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have hL := (h.isLagrangian_ker_mfderiv x).two_mul_finrank
  have hrn := LinearMap.finrank_range_add_finrank_ker (mfderiv I J π x).toLinearMap
  rw [LinearMap.range_eq_top.2 (h.surjective_mfderiv x), finrank_top] at hrn
  -- Both tangent spaces are their model spaces.
  change finrank ℝ F + finrank ℝ (mfderiv I J π x).ker = finrank ℝ E at hrn
  change 2 * finrank ℝ (mfderiv I J π x).ker = finrank ℝ E at hL
  omega

/-- **Hamiltonian vector fields of pulled-back functions are vertical.** If `g` is differentiable
at `π x`, the Hamiltonian vector of `g ∘ π` at `x` is tangent to the fibre: it lies in `ker dπ_x`.
-/
theorem hamiltonianVectorField_comp_mem_ker_mfderiv [FiniteDimensional ℝ E] {g : B → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (π x)) :
    σ.hamiltonianVectorField (g ∘ π) x ∈ (mfderiv I J π x).ker := by
  -- `d(g ∘ π)` vanishes on `ker dπ`, so `X_(g ∘ π)` is `σ`-orthogonal to the Lagrangian `ker dπ`.
  refine SymplecticForm.isCoisotropic_iff_le.1 (h.isLagrangian_ker_mfderiv x).isCoisotropic <|
    SymplecticForm.mem_orthogonal_iff.2 fun v hv ↦ ?_
  have hv' : mfderiv I J π x v = 0 := LinearMap.mem_ker.1 hv
  rw [symplecticFormAt_apply, SmoothBundleForm.eval₂_swap σ x, hσ.eval₂_hamiltonianVectorField,
    mvfderiv_comp_apply x hg (h.mdifferentiableAt x), hv', map_zero, neg_zero]

/-- The projection of a Lagrangian fibration kills the Hamiltonian vector field of a pulled-back
function. -/
theorem mfderiv_hamiltonianVectorField_comp_eq_zero [FiniteDimensional ℝ E] {g : B → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (π x)) :
    mfderiv I J π x (σ.hamiltonianVectorField (g ∘ π) x) = 0 :=
  LinearMap.mem_ker.1 (h.hamiltonianVectorField_comp_mem_ker_mfderiv hg)

/-- **Pulled-back functions Poisson-commute.** For a Lagrangian fibration `π` and functions `g`,
`k` on the base, differentiable at `π x`, the Poisson bracket `{g ∘ π, k ∘ π}` vanishes at `x`. -/
theorem poissonBracket_comp_eq_zero [FiniteDimensional ℝ E] {g k : B → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (π x)) (hk : MDifferentiableAt J 𝓘(ℝ) k (π x)) :
    σ.poissonBracket (g ∘ π) (k ∘ π) x = 0 := by
  rw [hσ.poissonBracket_eq_mvfderiv, mvfderiv_comp_apply x hg (h.mdifferentiableAt x),
    h.mfderiv_hamiltonianVectorField_comp_eq_zero hk, map_zero]

/-- **Vertical Hamiltonian flows stay in their fibre.** Along the maximal integral curve through
`x` of the Hamiltonian vector field of a `C²` pulled-back function `g ∘ π`, the projection `π` is
constant. -/
theorem apply_maximalIntegralCurve_hamiltonianVectorField_comp [FiniteDimensional ℝ E]
    [T2Space M] [BoundarylessManifold I M] [IsManifold J 1 B] {g : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : M} {t : ℝ}
    (ht : t ∈ maximalIntegralCurveInterval (σ.hamiltonianVectorField (g ∘ π)) x) :
    π (maximalIntegralCurve (σ.hamiltonianVectorField (g ∘ π)) x t) = π x := by
  have hv := hσ.contMDiff_hamiltonianVectorField (n := 1) (f := g ∘ π) (by simp)
    (by rw [one_add_one_eq_two]; exact hg.comp (h.contMDiff.of_le (by simp)))
  have h0 := zero_mem_maximalIntegralCurveInterval_of_mem ht
  conv_rhs => rw [← maximalIntegralCurve_zero (v := σ.hamiltonianVectorField (g ∘ π)) (x := x)]
  exact (isMIntegralCurveOn_maximalIntegralCurve hv).apply_eq_of_mfderiv_apply_eq_zero
    isOpen_maximalIntegralCurveInterval isPreconnected_maximalIntegralCurveInterval
    (fun _ _ ↦ h.mdifferentiableAt _)
    (fun _ _ ↦ h.mfderiv_hamiltonianVectorField_comp_eq_zero ((hg _).mdifferentiableAt (by simp)))
    h0 ht

/-- **Vertical Hamiltonian flows of a proper Lagrangian fibration are complete.** If the projection
`π` is proper, the Hamiltonian vector field of every `C²` pulled-back function `g ∘ π` is complete:
its integral curves stay in the compact fibres of `π`. -/
theorem isCompleteVectorField_hamiltonianVectorField_comp [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold J 1 B] (hπ : IsProperMap π) {g : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) :
    IsCompleteVectorField (σ.hamiltonianVectorField (g ∘ π)) :=
  isCompleteVectorField_of_isProperMap
    (hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp)
      (by rw [one_add_one_eq_two]; exact hg.comp (h.contMDiff.of_le (by simp)))) hπ
    fun _ _ ht ↦ h.apply_maximalIntegralCurve_hamiltonianVectorField_comp hg ht

end IsLagrangianFibration

namespace IsLagrangianTorusFibration

variable (h : hσ.IsLagrangianTorusFibration J π)
include h

/-- The fibres of a regular Lagrangian torus fibration are compact. -/
theorem isCompact_preimage_singleton (b : B) : IsCompact (π ⁻¹' {b}) :=
  h.isProperMap.isCompact_preimage isCompact_singleton

/-- The projection of a regular Lagrangian torus fibration is surjective, since its fibres are
connected, hence nonempty. -/
theorem surjective : Surjective π := fun b ↦
  (h.isConnected_preimage_singleton b).nonempty

end IsLagrangianTorusFibration

end TauCeti.SmoothTwoForm.IsNondegenerate
