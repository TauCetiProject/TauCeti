/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent.Linearized
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.TimeDependentFlow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow

/-!
# The linearized flow of a time-dependent Hamiltonian

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless manifold `M`, and let
`H : ℝ → M → ℝ` be a jointly `C³` time-dependent Hamiltonian, with Hamiltonian vector fields
`X_{H_t}` (`ι_{X_{H_t}} σ = d(H t)`) and time-dependent Hamiltonian flow
`φ_{s,t} = TauCeti.timeDependentFlowOf X_H s t`. For a torsion-free connection `∇` on `TM`, the
linearized Hamiltonian flow `V(t) = dφ_{s,t}(x) v` along the trajectory `t ↦ φ_{s,t}(x)` solves

`D_t V = ∇_V X_{H_t}`,  `V(s) = v`

(`IsNondegenerate.alongCurve_mfderiv_timeDependentFlowOf_hamiltonianVectorField`, with the initial
value `TauCeti.mfderiv_timeDependentFlowOf_self`). The Hamiltonian vector fields of a jointly `C³`
Hamiltonian are jointly `C²` (`IsNondegenerate.contMDiff_hamiltonianVectorField_uncurry`), which is
the regularity the variational equation of a general time-dependent flow
(`CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`) needs. The equation holds wherever
the flow is defined; no completeness is assumed.

Along a one-periodic orbit this is the equation of the linearized return map. Neither closedness
of `σ` nor any property of the orbit is assumed for it. When `σ` is closed, the linearized flow
`Φ(t) = dφ_{0,t}(γ 0) : T_(γ 0) M ≃ T_(γ t) M` along a solution `γ` of the Hamiltonian equation
(`TauCeti.linearizedFlowAlong`) preserves `σ`:
`σ(Φ(t) a, Φ(t) b) = σ(a, b)` (`eval₂_linearizedFlowAlong`), again with no completeness of the
flow. So a unitary trivialization turns the linearized flow into a path of symplectic matrices;
when the orbit is in addition nondegenerate, the Conley–Zehnder index of that path grades the
orbit in Hamiltonian Floer homology, and the equation is the one compared with the asymptotic
operator of the linearized Floer equation at the ends of a Floer cylinder.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.alongCurve_mfderiv_timeDependentFlowOf_hamiltonianVectorField`: the variational
  equation of a time-dependent Hamiltonian flow.
* `eval₂_linearizedFlowAlong`: the linearized Hamiltonian flow along a solution preserves a closed
  two-form.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 1 and 2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
-/

public section

open Bundle CovariantDerivative Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H' M] [T2Space M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {H : ℝ → M → ℝ} {s t : ℝ} {x : M}

/-- **The variational equation of a time-dependent Hamiltonian flow.** For a nondegenerate
two-form `σ`, a jointly `C³` Hamiltonian `H` and a torsion-free connection `∇`, if the
Hamiltonian flow from time `s` is defined at `x` up to time `t`, the linearized flow
`V(u) = dφ_{s,u}(x) v` along the trajectory `u ↦ φ_{s,u}(x)` satisfies
`D_t V = ∇_{V(t)} X_{H_t}` at `t`. -/
theorem alongCurve_mfderiv_timeDependentFlowOf_hamiltonianVectorField (h : σ.IsNondegenerate)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.IsTorsionFree)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 3 (uncurry H))
    (hx : ((s, t), x) ∈ timeDependentFlowDomain fun u ↦ σ.hamiltonianVectorField (H u))
    (v : TangentSpace I x) :
    alongCurve cov
        (fun u ↦ timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s u x)
        (fun u ↦ mfderiv I I
          (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s u) x v) t =
      cov (σ.hamiltonianVectorField (H t))
        (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s t x)
        (mfderiv I I (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s t) x v) :=
  alongCurve_mfderiv_timeDependentFlowOf cov htor
    (h.contMDiff_hamiltonianVectorField_uncurry (n := 2) (by simp) hH) hx v

end TauCeti.SmoothTwoForm.IsNondegenerate

namespace TauCeti.SmoothTwoForm

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H' M] [T2Space M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {H : ℝ → M → ℝ} {X : ℝ → (x : M) → TangentSpace I x}

/-- **The linearized Hamiltonian flow along a solution preserves the form.** Let `σ` be a closed
two-form and `X` a jointly `C²` time-dependent field such that each `X u` is a Hamiltonian vector
field of a `C²` function `H u`. Along a solution `γ` of `X` defined for all time, the linearized
flow `Φ(t) = dφ_{0,t}(γ 0)` satisfies `σ(Φ(t) a, Φ(t) b) = σ(a, b)`. Neither nondegeneracy of `σ`
nor completeness of the flow is needed. -/
theorem eval₂_linearizedFlowAlong (hσ : σ.IsClosed)
    (hXH : ∀ u, σ.IsHamiltonianVectorField (H u) (X u)) (hH : ∀ u, ContMDiff I 𝓘(ℝ) 2 (H u))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {γ : ℝ → M} (hγ : ∀ u, HasMFDerivAt 𝓘(ℝ, ℝ) I γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u))))
    (t : ℝ) (a b : TangentSpace I (γ 0)) :
    σ.eval₂ (γ t) (linearizedFlowAlong (hX.of_le one_le_two) hγ t a)
        (linearizedFlowAlong (hX.of_le one_le_two) hγ t b) =
      σ.eval₂ (γ 0) a b := by
  rw [linearizedFlowAlong_apply, linearizedFlowAlong_apply]
  -- The form is preserved at the point `φ_{0,t}(γ 0)`, which the flow carries to `γ t`.
  have h : ∀ y, timeDependentFlowOf X 0 t (γ 0) = y →
      σ.eval₂ y (mfderiv I I (timeDependentFlowOf X 0 t) (γ 0) a)
        (mfderiv I I (timeDependentFlowOf X 0 t) (γ 0) b) = σ.eval₂ (γ 0) a b := by
    rintro _ rfl
    exact eval₂_mfderiv_timeDependentFlowOf_of_isHamiltonianVectorField (fun u _ ↦ hXH u) hσ
      (fun u _ ↦ hH u) (hX.of_le one_le_two)
      (mem_timeDependentFlowDomain_of_forall_hasMFDerivAt hγ 0 t) a b
  exact h _ (timeDependentFlowOf_eq_of_forall_hasMFDerivAt (hX.of_le one_le_two) hγ 0 t)

/-- **The linearized Hamiltonian flow along the loop of an orbit preserves the form.** Under the
hypotheses of `TauCeti.SmoothTwoForm.eval₂_linearizedFlowAlong`, along the loop of a contractible
`1`-periodic solution `x` the linearized flow satisfies `σ(Φ(t) a, Φ(t) b) = σ(a, b)` for every
`t ∈ [0, 1]`. -/
theorem eval₂_orbitLinearizedFlow (hσ : σ.IsClosed)
    (hXH : ∀ u, σ.IsHamiltonianVectorField (H u) (X u)) (hH : ∀ u, ContMDiff I 𝓘(ℝ) 2 (H u))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (x : contractiblePeriodicSolutions X 1) (t : unitInterval)
    (a b : TangentSpace I (orbitLoop x 0)) :
    σ.eval₂ (orbitLoop x t) (orbitLinearizedFlow (hX.of_le one_le_two) x t a)
        (orbitLinearizedFlow (hX.of_le one_le_two) x t b) =
      σ.eval₂ (orbitLoop x 0) a b := by
  have hx := (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset x.property)).1
  rw [orbitLinearizedFlow_apply, orbitLinearizedFlow_apply]
  -- The general lemma holds at `x t` and `x 0`, which are the points `t` and `0` of the loop.
  have h : ∀ y₁ y₀, x.val t = y₁ → x.val 0 = y₀ → ∀ a b : TangentSpace I (x.val 0),
      σ.eval₂ y₁ (mfderiv I I (timeDependentFlowOf X 0 t) (x.val 0) a)
        (mfderiv I I (timeDependentFlowOf X 0 t) (x.val 0) b) = σ.eval₂ y₀ a b := by
    rintro _ _ rfl rfl a b
    simpa only [linearizedFlowAlong_apply] using eval₂_linearizedFlowAlong hσ hXH hH hX hx t a b
  exact h _ _ (orbitLoop_apply x t).symm (orbitLoop x).source.symm a b

end TauCeti.SmoothTwoForm
