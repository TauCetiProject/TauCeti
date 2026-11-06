/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Propagator
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation

/-!
# Nondegenerate orbits and the kernel of the asymptotic operator

Let `x(t) = φ(0, t) x₀` be a one-periodic orbit of a one-periodic time-dependent vector field `v`
on a Banach space `V`, so that `x₀` is a fixed point of the time-one map `φ(0, 1)`. Its
*asymptotic operator* is `A ζ = J_t (ζ' - S_t ζ)` with `S_t = D(v_t)(x(t))`
(`TauCeti.Floer.asymptoticOperator`); for a Hamiltonian field `v_t = X_{H_t}` this is the operator
on loops whose translation-invariant extension `∂s + A` is the linearized Floer operator at the
stationary cylinder over `x`
(`TauCeti.SymplecticForm.floerLinearization_eq_stationaryCylinderOperator`).

The kernel of `A` consists of the solutions `ζ(t) = Ψ(t) ζ(0)` of the linearized equation
`ζ' = S_t ζ`, with `Ψ = dysonSeriesLeft S` its propagator. By the variational equation of the flow,
`Ψ(t)` is the derivative `Dφ(0, t)(x₀)` (`TauCeti.fderiv_timeDependentFlow_eq_dysonSeriesLeft`), so
`Ψ(1)` is the derivative of the time-one map at its fixed point. Consequently the orbit is
nondegenerate, in the sense that `x₀` is a nondegenerate fixed point of `φ(0, 1)`
(`TauCeti.IsNondegenerateFixedPt`), exactly when `A` has no nonzero differentiable one-periodic
kernel element (`TauCeti.Floer.isNondegenerateFixedPt_timeDependentFlow_iff`). The almost
complex structures `J_t` play no role in this statement, since each `J_t` is invertible.

For a jointly `C²` one-periodic Hamiltonian `H` with globally Lipschitz suspended field and its
flow `TauCeti.SymplecticForm.timeDependentHamiltonianFlow`, the linearized field is
`S_t = dX_{H_t}(x(t))`, the propagator is the linearized Hamiltonian flow
(`TauCeti.SymplecticForm.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`) and so a path of
symplectic maps starting at the identity
(`TauCeti.SymplecticForm.apply_dysonSeriesLeft_fderiv_hamiltonianVectorField`), and the
nondegeneracy criterion reads
`TauCeti.SymplecticForm.isNondegenerateFixedPt_timeDependentHamiltonianFlow_iff`. This is the path
whose Conley–Zehnder index grades the orbit in Floer theory.

The target is a vector space with a globally Lipschitz suspended field, the setting of
`TauCeti.timeDependentFlow`; the weighted Sobolev realization of `A` and of `∂s + A`, and their
invertibility on nondegenerate orbits, are not treated here.

## Main results

* `TauCeti.Floer.isNondegenerateFixedPt_timeDependentFlow_iff`: a periodic orbit is nondegenerate
  exactly when its asymptotic operator has trivial one-periodic kernel.
* `TauCeti.SymplecticForm.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`: the linearized
  Hamiltonian flow along an orbit is the propagator of `ζ' = dX_{H_t}(x(t)) ζ`.
* `TauCeti.SymplecticForm.apply_dysonSeriesLeft_fderiv_hamiltonianVectorField`: this propagator
  preserves the symplectic form.
* `TauCeti.SymplecticForm.isNondegenerateFixedPt_timeDependentHamiltonianFlow_iff`: the Hamiltonian
  form of the nondegeneracy criterion.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360.
-/

public section

open Function
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {v : ℝ → V → V} {K : ℝ≥0} (hv : LipschitzWith K (timeDependentSuspension v))
  (hvs : ContDiff ℝ 1 fun p : ℝ × V ↦ v p.1 p.2)

include hvs in
/-- **Nondegenerate orbits are those with injective asymptotic operator.** Let `v` be a jointly
`C¹`, one-periodic time-dependent vector field whose suspension is globally Lipschitz, and let `x`
be a fixed point of its time-one map `φ(0, 1)`. Then `x` is a nondegenerate fixed point exactly
when the asymptotic operator `ζ ↦ J_t (ζ' - S_t ζ)`, for the linearization
`S_t = D(v_t)(φ(0, t) x)` along the orbit, has no nonzero differentiable one-periodic kernel
element. -/
theorem isNondegenerateFixedPt_timeDependentFlow_iff (J : ℝ → AlmostComplexStructure V)
    (hvp : Periodic v 1) {x : V} (hx : IsFixedPt (timeDependentFlow v hv 0 1) x) :
    IsNondegenerateFixedPt 𝓘(ℝ, V) (timeDependentFlow v hv 0 1) x ↔
      ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
        (∀ t, asymptoticOperator J
          (fun t ↦ fderiv ℝ (v t) (timeDependentFlow v hv 0 t x)) ζ t = 0) → ζ = 0 := by
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (v t) (timeDependentFlow v hv 0 t x)
  have hS : S = fun u ↦ fderiv ℝ (v (0 + u)) (timeDependentFlow v hv 0 (0 + u) x) := by
    simp only [S, zero_add]
  have hSc : Continuous S := hS ▸ continuous_fderiv_comp_timeDependentFlow hv hvs 0 x
  have hSp : Periodic S 1 :=
    hS ▸ periodic_fderiv_comp_timeDependentFlow hv hvp 0 (by rwa [zero_add])
  have hΨ : fderiv ℝ (timeDependentFlow v hv 0 1) x = dysonSeriesLeft S 1 := by
    simpa only [zero_add, ← hS] using fderiv_timeDependentFlow_eq_dysonSeriesLeft hv hvs 0 1 x
  have hdiff : DifferentiableAt ℝ (timeDependentFlow v hv 0 1) x := by
    have h := contDiff_timeDependentFlow hv 0 (by simpa using hvs)
    have h1 : ContDiff ℝ 1 (timeDependentFlow v hv 0 1) :=
      h.comp (contDiff_const (c := ((0 : ℝ), (1 : ℝ))).prodMk contDiff_id)
    exact h1.differentiable one_ne_zero x
  -- On a vector space the manifold derivative is the Fréchet derivative, conjugated by
  -- `NormedSpace.fromTangentSpace`, which is the identity map of `V`; `rfl` removes it.
  have hD (w : V) : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (timeDependentFlow v hv 0 1) x w =
      dysonSeriesLeft S 1 w := by
    rw [mfderiv_eq_fderiv, hΨ]
    rfl
  rw [isNondegenerateFixedPt_iff]
  simp only [hx, mdifferentiableAt_iff_differentiableAt.2 hdiff, true_and]
  constructor
  · intro h ζ hζ hζp hker
    have heq := apply_eq_dysonSeriesLeft_apply_of_asymptoticOperator_eq_zero hSc hζ hker
    have h0 : ζ 0 = 0 := h (ζ 0) (by rw [hD, ← heq, ← zero_add (1 : ℝ), hζp 0])
    funext t
    rw [heq t, h0, map_zero, Pi.zero_apply]
  · intro h w hw
    have hζ := h (fun t ↦ dysonSeriesLeft S t w)
      (fun t ↦ (hasDerivAt_dysonSeriesLeft_apply hSc w t).differentiableAt)
      ((periodic_dysonSeriesLeft_apply_iff hSc hSp w).2 ((hD w).symm.trans hw))
      (asymptoticOperator_dysonSeriesLeft_apply_eq_zero hSc w)
    have hw0 : dysonSeriesLeft S 0 w = 0 := congrFun hζ 0
    rw [dysonSeriesLeft_zero] at hw0
    exact hw0

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 2 (uncurry H))

include hH in
/-- **The linearized Hamiltonian flow is the propagator of the linearized Hamiltonian
equation.** For a jointly `C²` time-dependent Hamiltonian whose suspended field is globally
Lipschitz, the derivative at `x` of the evolution `φ(0, t)` is the left Dyson series at time `t`
of `S_u = dX_{H_u}(φ(0, u) x)`. -/
theorem fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft (t : ℝ) (x : V) :
    fderiv ℝ (ω.timeDependentHamiltonianFlow H hX 0 t) x =
      dysonSeriesLeft (fun u ↦ fderiv ℝ (ω.hamiltonianVectorField (H u))
        (ω.timeDependentHamiltonianFlow H hX 0 u x)) t := by
  rw [ω.timeDependentHamiltonianFlow_eq H hX]
  simpa only [zero_add] using fderiv_timeDependentFlow_eq_dysonSeriesLeft
    (v := fun u y ↦ ω.hamiltonianVectorField (H u) y) _
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH) 0 t x

include hH in
/-- **The propagator of the linearized Hamiltonian equation is symplectic.** Along the orbit of a
jointly `C²` time-dependent Hamiltonian with globally Lipschitz suspended field, the propagator of
`ζ' = dX_{H_t}(φ(0, t) x) ζ` preserves `ω`. -/
@[simp]
theorem apply_dysonSeriesLeft_fderiv_hamiltonianVectorField (t : ℝ) (x u w : V) :
    ω (dysonSeriesLeft (fun u ↦ fderiv ℝ (ω.hamiltonianVectorField (H u))
        (ω.timeDependentHamiltonianFlow H hX 0 u x)) t u)
      (dysonSeriesLeft (fun u ↦ fderiv ℝ (ω.hamiltonianVectorField (H u))
        (ω.timeDependentHamiltonianFlow H hX 0 u x)) t w) = ω u w := by
  rw [← ω.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft hX hH,
    ω.apply_fderiv_timeDependentHamiltonianFlow hX hH]

include hH in
/-- **Nondegenerate Hamiltonian orbits are those with injective asymptotic operator.** Let `H` be
a jointly `C²`, one-periodic time-dependent Hamiltonian whose suspended field is globally
Lipschitz, and let `x` be a fixed point of the time-one map of its evolution. Then `x` is a
nondegenerate fixed point exactly when the asymptotic operator `ζ ↦ J_t (ζ' - S_t ζ)` of the
orbit, with `S_t = dX_{H_t}(φ(0, t) x)`, has no nonzero differentiable one-periodic kernel
element. -/
theorem isNondegenerateFixedPt_timeDependentHamiltonianFlow_iff
    (J : ℝ → AlmostComplexStructure V) (hHp : Periodic H 1) {x : V}
    (hx : IsFixedPt (ω.timeDependentHamiltonianFlow H hX 0 1) x) :
    IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) x ↔
      ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
        (∀ t, Floer.asymptoticOperator J (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t))
          (ω.timeDependentHamiltonianFlow H hX 0 t x)) ζ t = 0) → ζ = 0 := by
  rw [ω.timeDependentHamiltonianFlow_eq H hX] at hx ⊢
  exact Floer.isNondegenerateFixedPt_timeDependentFlow_iff
    (v := fun u y ↦ ω.hamiltonianVectorField (H u) y) _
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH) J
    (fun t ↦ funext fun y ↦ by simp only [hHp t]) hx

end SymplecticForm

end TauCeti
