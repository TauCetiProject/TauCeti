/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.TimeDependentFlow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

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
of `σ` nor any property of the orbit is assumed here. When `σ` is moreover closed, the flow
preserves `σ`, so a unitary trivialization turns the linearized flow into a path of symplectic
matrices; when the orbit is in addition nondegenerate, the Conley–Zehnder index of that path grades
the orbit in Hamiltonian Floer homology, and the equation is the one compared with the asymptotic
operator of the linearized Floer equation at the ends of a Floer cylinder.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.alongCurve_mfderiv_timeDependentFlowOf_hamiltonianVectorField`: the variational
  equation of a time-dependent Hamiltonian flow.

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
