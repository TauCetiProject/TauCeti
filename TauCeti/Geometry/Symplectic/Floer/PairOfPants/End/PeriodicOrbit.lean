/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Homotopy

/-!
# Periodic orbits in positive end charts on a manifold

On an end `q` of the pair of pants `S = ℂ ∖ {0, 1}`, the positive end chart
`φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`) rescales time by `q.endSign = ±1`
and replaces the end Hamiltonian `H_q` by `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`). Using the velocity transformation
`TauCeti.SmoothTwoForm.hasMFDerivAt_comp_endSign_mul` from
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback` and the null-homotopy transport
`TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul_iff` from
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Homotopy`, this file translates `1`-periodic
orbits and contractible `1`-periodic orbits between `H'_q` and `H_q` without importing the
half-cylinder convergence layer.

## Main results

* `TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul`: reading a `1`-periodic orbit of
  `H'_q` with `t ↦ ±t` gives a `1`-periodic orbit of `H_q`.
* `TauCeti.SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`: `x` is a `1`-periodic
  orbit of `H'_q` if and only if `t ↦ x(±t)` is a `1`-periodic orbit of `H_q`.
* `TauCeti.SmoothTwoForm.mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff`: `x` is a
  contractible `1`-periodic orbit of `H'_q` if and only if `t ↦ x(±t)` is a contractible
  `1`-periodic orbit of `H_q`.
-/

public section

open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}

/-- Reading a one-periodic orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the
end gives a one-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
      1) :
    (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
  mem_periodicSolutions.2
    ⟨hasMFDerivAt_comp_endSign_mul (mem_periodicSolutions.1 hx).1,
      periodic_comp_endSign_mul (mem_periodicSolutions.1 hx).2⟩

/-- A curve `x` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only if
`t ↦ x(±t)`, with the sign of the end, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  have hx' : (fun t ↦ (fun r ↦ x (q.endSign * r)) (q.endSign * t)) = x := by
    funext t
    simp only [endSign_mul_endSign_mul]
  have h := mem_periodicSolutions_comp_endSign_mul (ω := ω) (H := positiveEndHamiltonian H)
    (by rwa [positiveEndHamiltonian_positiveEndHamiltonian])
  rwa [hx'] at h

/-- A curve `x` is a contractible `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and
only if `t ↦ x(±t)`, with the sign of the end `q`, is a contractible `1`-periodic orbit of `H_q`. -/
theorem mem_contractiblePeriodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ contractiblePeriodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  rw [mem_contractiblePeriodicSolutions, mem_contractiblePeriodicSolutions,
    mem_periodicSolutions_positiveEndHamiltonian_iff,
    ← exists_nullhomotopic_comp_endSign_mul_iff]

end SmoothTwoForm

end TauCeti
