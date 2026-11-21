/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Homotopy

/-!
# Periodic orbits in positive end charts on a manifold

On an end `q` of the pair of pants `S = ℂ ∖ {0, 1}`, the positive end chart
`φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`) rescales time by `q.endSign = ±1`
and replaces the end Hamiltonian `H_q` by `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`). Using the null-homotopy transport
`TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul_iff` from
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Homotopy`, this file translates Hamiltonian
vector fields, solution curves, `1`-periodic orbits, and contractible `1`-periodic orbits between
`H'_q` and `H_q` without importing the Floer pullback or half-cylinder convergence layers.

## Main results

* `TauCeti.SmoothTwoForm.hamiltonianVectorField_positiveEndHamiltonian_endSign_mul`: at the time
  `±t` of the end, `X_{H'_q(±t)} = ±X_{H_q(t)}`.
* `TauCeti.SmoothTwoForm.hasMFDerivAt_comp_endSign_mul`: reading an integral curve of `H'_q` with
  `t ↦ ±t` gives an integral curve of `H_q`.
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
open scoped Manifold

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}

/-- At the time `±t` of the end, the Hamiltonian vector field of the positive end Hamiltonian
`H'_q` is `±` that of `H_q` at the time `t`: `X_{H'_q(±t)} = ±X_{H_q(t)}`. -/
theorem hamiltonianVectorField_positiveEndHamiltonian_endSign_mul (q : Puncture) (t : ℝ)
    (x : M) :
    ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) x =
      q.endSign • ω.hamiltonianVectorField (H q t) x := by
  rw [← hamiltonianVectorField_const_smul]
  congr 1
  funext y
  rw [positiveEndHamiltonian_apply, endSign_mul_endSign_mul, Pi.smul_apply, smul_eq_mul]

/-- Reading a solution curve of the positive end Hamiltonian `H'_q` with the time `±t` of the end
gives a solution curve of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ) I (fun s ↦ x (q.endSign * s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  -- The velocity `±X_{H'_q(±t)}` of `x` at `±t`, rescaled by the sign of the end, is `X_{H_q(t)}`.
  have h : (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t))
            (x (q.endSign * t))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight q.endSign := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight,
      hamiltonianVectorField_positiveEndHamiltonian_endSign_mul, smul_smul]
  rw [h]
  refine (hx (q.endSign * t)).comp t (hasMFDerivAt_iff_hasFDerivAt.2 ?_)
  exact ((hasDerivAt_id' t).const_mul q.endSign).hasFDerivAt.congr_fderiv
    (ContinuousLinearMap.ext_ring (by simp))

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
