/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Nondegenerate Hamiltonian orbits and the asymptotic operator

Let `(V, ω)` be a finite-dimensional symplectic vector space and `H : ℝ → V → ℝ` a jointly `C²`
Hamiltonian, one-periodic in time, whose Hamiltonian vector field `X_{H_t}` has a globally
Lipschitz suspension, so that it has a global time-dependent flow `φ(s, t)`
(`TauCeti.timeDependentFlow`). A one-periodic orbit is a trajectory `x(t) = φ(0, t) x₀` with
`x₀` fixed by the time-one map `φ(0, 1)`, and it is *nondegenerate* when `x₀` is a nondegenerate
fixed point (`TauCeti.IsNondegenerateFixedPt`): `1` is not an eigenvalue of `Dφ(0, 1)(x₀)`.

The Floer equation on a cylindrical end asymptotic to `x` is governed by the asymptotic operator
`A ζ = J_t (ζ' - S_t ζ)` with `S_t = dX_{H_t}(x(t))` (`TauCeti.Floer.asymptoticOperator`), whose
one-periodic kernel consists of the periodic solutions of `ζ' = S_t ζ`, that is, of the fixed
vectors of the return map `Ψ(1)` of that linear equation. Since `Ψ(t)` is the derivative of the
flow, `Dφ(0, t)(x₀) = Ψ(t)`
(`TauCeti.SymplecticForm.fderiv_timeDependentFlow_hamiltonianVectorField`), a one-periodic orbit
is nondegenerate exactly when its asymptotic operator, for any almost complex structures `J_t`,
has no nonzero one-periodic kernel.

Floer operators on the ends are considered on maps decaying like `e^{-δ s}`, which turns the
asymptotic operator into `A - δ` (`TauCeti.Floer.stationaryCylinderOperator_exp_smul`). Since
the weights `δ` at which `A - δ` has a periodic kernel form a closed set
(`TauCeti.Floer.isClosed_setOf_exists_asymptoticOperator_eq_smul`), at a nondegenerate orbit
`A - δ` still has no periodic kernel for all sufficiently small weights `δ`.

## Main results

* `TauCeti.SymplecticForm.isNondegenerateFixedPt_timeDependentFlow_iff`: a one-periodic orbit is
  nondegenerate exactly when its asymptotic operator is injective on one-periodic loops.
* `TauCeti.SymplecticForm.eventually_eq_zero_of_asymptoticOperator_eq_smul`: at a nondegenerate
  orbit the weighted asymptotic operators `A - δ` are injective on one-periodic loops for all
  weights `δ` near `0`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 1 and 2.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360.
-/

public section

open Function Filter Topology
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
  (hv : LipschitzWith K (timeDependentSuspension fun t ↦ ω.hamiltonianVectorField (H t)))

/-- **Nondegenerate orbits have injective asymptotic operators.** Let `H` be a jointly `C²`
one-periodic Hamiltonian and `x` a fixed point of its time-one map, so that `t ↦ φ(0, t) x` is a
one-periodic orbit. The orbit is nondegenerate exactly when, for any almost complex structures
`J_t`, the asymptotic operator `A ζ = J_t (ζ' - S_t ζ)` with `S_t = dX_{H_t}(φ(0, t) x)` has no
nonzero differentiable one-periodic kernel element. -/
theorem isNondegenerateFixedPt_timeDependentFlow_iff (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : V} (hx : IsFixedPt (timeDependentFlow _ hv 0 1) x)
    (J : ℝ → AlmostComplexStructure V) :
    IsNondegenerateFixedPt 𝓘(ℝ, V) (timeDependentFlow _ hv 0 1) x ↔
      ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
        (∀ t, Floer.asymptoticOperator J (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t))
          (timeDependentFlow _ hv 0 t x)) ζ t = 0) → ζ = 0 := by
  have key := Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_exists_ne_zero_isFixedPt
    (J := J) (continuous_fderiv_hamiltonianVectorField_timeDependentFlow ω hv hH x)
    (periodic_fderiv_hamiltonianVectorField_timeDependentFlow ω hv hHp hx)
  have hd : DifferentiableAt ℝ (timeDependentFlow _ hv 0 1) x :=
    ((contDiff_timeDependentFlow hv 0 (ω.contDiff_hamiltonianVectorField_uncurry hH)).comp
      (by fun_prop : ContDiff ℝ 1 fun y : V ↦ (((0 : ℝ), (1 : ℝ)), y))).differentiable
        one_ne_zero x
  rw [isNondegenerateFixedPt_iff, mfderiv_eq_fderiv,
    fderiv_timeDependentFlow_hamiltonianVectorField ω hv hH]
  constructor
  · rintro ⟨-, -, h⟩ ζ hζ hζp hA
    by_contra hne
    obtain ⟨v, hv₀, hfix⟩ := key.1 ⟨ζ, hζ, hζp, hne, hA⟩
    exact hv₀ (h v hfix)
  · intro h
    refine ⟨hx, mdifferentiableAt_iff_differentiableAt.2 hd, fun v hfix ↦ ?_⟩
    by_contra hv₀
    obtain ⟨ζ, hζ, hζp, hne, hA⟩ := key.2 ⟨v, hv₀, hfix⟩
    exact hne (h ζ hζ hζp hA)

/-- **Small weights preserve nondegeneracy.** At a nondegenerate one-periodic orbit of a jointly
`C²` one-periodic Hamiltonian, and for continuous one-periodic almost complex structures `J_t`,
the weighted asymptotic operator `A - δ` has no nonzero differentiable one-periodic kernel
element for every weight `δ` close enough to `0`. -/
theorem eventually_eq_zero_of_asymptoticOperator_eq_smul (hH : ContDiff ℝ 2 (uncurry H))
    (hHp : Periodic H 1) {x : V}
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (timeDependentFlow _ hv 0 1) x)
    {J : ℝ → AlmostComplexStructure V} (hJc : Continuous J) (hJp : Periodic J 1) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
      (∀ t, Floer.asymptoticOperator J (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t))
        (timeDependentFlow _ hv 0 t x)) ζ t = δ • ζ t) → ζ = 0 := by
  have hx := hnd.isFixedPt
  have hclosed := Floer.isClosed_setOf_exists_asymptoticOperator_eq_smul
    (continuous_fderiv_hamiltonianVectorField_timeDependentFlow ω hv hH x)
    (periodic_fderiv_hamiltonianVectorField_timeDependentFlow ω hv hHp hx) hJc hJp
  have h₀ := (isNondegenerateFixedPt_timeDependentFlow_iff ω hv hH hHp hx J).1 hnd
  refine Eventually.mono (hclosed.isOpen_compl.mem_nhds fun ⟨ζ, hζ, hζp, hne, hA⟩ ↦
    hne (h₀ ζ hζ hζp fun t ↦ by simpa using hA t)) fun δ hδ ζ hζ hζp hA ↦ ?_
  by_contra hne
  exact hδ ⟨ζ, hζ, hζp, hne, hA⟩

end TauCeti.SymplecticForm
