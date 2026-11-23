/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Topology.FiberBundle.Separation

/-!
# Hamiltonian flows of functions on the base of a cotangent bundle

Let `M` be a manifold with cotangent bundle `π : T*M → M` and canonical symplectic form
`ω = -dλ`. For a function `g` on `M`, the Hamiltonian vector field of `g ∘ π`, with the convention
`ι_X ω = d(g ∘ π)`, is vertical: at a covector `p` over `x` it is the constant vertical vector
`-dg_x` (`TauCeti.CotangentBundle.hamiltonianVectorField_comp_proj`). In the chart at `p`, where
`ω((δq, δp), (δq', δp')) = δp'(δq) - δp(δq')`, the vector `(0, -dg_x)` pairs with `(δq', δp')`
to `dg_x(δq') = d(g ∘ π)(δq', δp')`.

Consequently, the Hamiltonian flow of `g ∘ π` translates each fibre:

`φ_t(x, p) = (x, p - t dg_x)`

(`TauCeti.CotangentBundle.flowOf_hamiltonianVectorField_comp_proj`). The fibre over `x` is
invariant and the flow is complete. This is the cotangent-bundle form of the action of `T*_x M`
on the fibres of a Lagrangian fibration, by which a covector `dg_x` acts through the time-one map
of the Hamiltonian flow of `g ∘ π`; on `T*M` itself the action of `β` is translation by `-β`.

## Main results

* `TauCeti.CotangentBundle.hamiltonianVectorField_comp_proj`: `X_(g ∘ π)(x, p) = (0, -dg_x)`.
* `TauCeti.CotangentBundle.isMIntegralCurve_hamiltonianVectorField_comp_proj`: the curve
  `t ↦ (x, p - t dg_x)` is an integral curve of `X_(g ∘ π)`.
* `TauCeti.CotangentBundle.flowOf_hamiltonianVectorField_comp_proj`: the Hamiltonian flow of
  `g ∘ π` is the fibre translation `(x, p) ↦ (x, p - t dg_x)`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The Hamiltonian vector field of a function on the base is vertical.** At a covector `z`
over `x`, the Hamiltonian vector field of `g ∘ π` for the canonical symplectic form of `T*M` is
the vertical vector `-dg_x`, read in the preferred chart at `z`. -/
theorem hamiltonianVectorField_comp_proj {g : M → ℝ} (z : CotangentBundle I M)
    (hg : MDifferentiableAt I 𝓘(ℝ) g z.proj) :
    (symplecticForm I M).hamiltonianVectorField (g ∘ TotalSpace.proj) z =
      ((0 : E), -mvfderiv I g z.proj) := by
  have hσ := (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate
  -- The vertical vector `-dg_x`, as a tangent vector at `z`.
  let v : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z := ((0 : E), -mvfderiv I g z.proj)
  have hv (w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
      (symplecticForm I M).flat z v w =
        mvfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (g ∘ TotalSpace.proj) z w := by
    rw [SmoothTwoForm.flat_apply, eval₂_symplecticForm,
      mvfderiv_comp_apply z hg ((Bundle.contMDiff_proj (n := 1) _).mdifferentiableAt one_ne_zero),
      Bundle.mfderiv_proj]
    refine (strongDualCotangentSymplecticForm_apply (V := E) v w).trans ?_
    -- Tangent vectors at `z` are elements of the model space `E × (E →L[ℝ] ℝ)`.
    obtain ⟨a, b⟩ := w
    change b 0 - (-mvfderiv I g z.proj) a = mvfderiv I g z.proj a
    rw [map_zero, zero_sub]
    exact neg_neg (mvfderiv I g z.proj a)
  refine ((hσ.isInvertible_flat z).injective ?_).symm
  rw [hσ.flat_hamiltonianVectorField]
  exact ContinuousLinearMap.ext hv

/-- **The vertical lines are integral curves of `X_(g ∘ π)`.** If `g` is differentiable at `x`,
then for every covector `p` over `x` the curve `t ↦ (x, p - t dg_x)` in the fibre over `x` is an
integral curve of the Hamiltonian vector field of `g ∘ π`. -/
theorem isMIntegralCurve_hamiltonianVectorField_comp_proj {g : M → ℝ} {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) (p : TangentSpace I x →L[ℝ] ℝ) :
    IsMIntegralCurve
      (fun t : ℝ ↦ (⟨x, p - t • mvfderiv I g x⟩ : CotangentBundle I M))
      ((symplecticForm I M).hamiltonianVectorField (g ∘ TotalSpace.proj)) := by
  intro t
  let c : ℝ → E →L[ℝ] ℝ := fun t ↦ p - t • mvfderiv I g x
  let dg : E →L[ℝ] ℝ := mvfderiv I g x
  have hc : HasFDerivAt c ((1 : ℝ →L[ℝ] ℝ).smulRight (-dg)) t := by
    refine (((hasFDerivAt_id t).smul_const dg).const_sub p).congr_fderiv ?_
    ext
    simp
  refine (hasMFDerivAt_mk (I := I) x hc.hasMFDerivAt).congr_mfderiv ?_
  rw [hamiltonianVectorField_comp_proj _ hg]
  refine ContinuousLinearMap.ext fun (s : ℝ) ↦ ?_
  -- Tangent vectors along the curve are elements of the model space `E × (E →L[ℝ] ℝ)`.
  change ((0 : E), s • -dg) = s • ((0 : E), -dg)
  simp

variable [T2Space M] [I.Boundaryless]

/-- **The Hamiltonian flow of a function on the base translates the fibres.** For a `C²`
function `g` on `M`, the Hamiltonian flow of `g ∘ π` on `T*M` moves a covector `p` over `x` to
`p - t dg_x` at time `t`. -/
theorem flowOf_hamiltonianVectorField_comp_proj {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (t : ℝ) (z : CotangentBundle I M) :
    flowOf ((symplecticForm I M).hamiltonianVectorField (g ∘ TotalSpace.proj)) t z =
      (⟨z.proj, z.snd - t • mvfderiv I g z.proj⟩ : CotangentBundle I M) := by
  have hσ := (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate
  have hgπ : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) 2 (g ∘ TotalSpace.proj) :=
    hg.comp (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))
  have hγ := isMIntegralCurve_hamiltonianVectorField_comp_proj
    ((hg z.proj).mdifferentiableAt (by simp)) z.snd
  have h := flowOf_eq_of_isMIntegralCurve
    (hσ.contMDiff_hamiltonianVectorField (by simp) (by rw [one_add_one_eq_two]; exact hgπ)) hγ t
  simpa using h

end CotangentBundle

end TauCeti
