/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Loops of totally real subspaces

Let `E` be a complex normed space. A *loop of maximal totally real subspaces* of `E`
(`TauCeti.TotallyRealLoop`) is a family `Λ : [0, 1] → Submodule ℝ E` with `Λ 0 = Λ 1` of the form
`Λ t = A t L₀`, where `L₀` is maximal totally real and `A` is a continuous path of complex-linear
automorphisms of `E`. This is the usual notion of a continuous loop in the totally real
Grassmannian `GL(n, ℂ) / GL(n, ℝ)`, since paths in that homogeneous space lift to `GL(n, ℂ)`, and
it is how boundary conditions of Cauchy--Riemann operators are given in practice.

## Main declarations

* `TauCeti.TotallyRealLoop`: loops of maximal totally real subspaces.
* `TauCeti.TotallyRealLoop.isMaximalTotallyReal`: every subspace of such a loop is maximal
  totally real.
* `TauCeti.TotallyRealLoop.const`: the constant loop at a maximal totally real subspace.
* `TauCeti.TotallyRealLoop.map`: the pointwise image `t ↦ B t (Λ t)` under a loop `B` of
  complex-linear automorphisms.
* `TauCeti.TotallyRealLoop.rotation`: the half-turn `t ↦ e^{iπt} L₀`, which closes up since
  `-L₀ = L₀`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (loops of totally real subspaces as boundary
  conditions).
-/

public section

open Real
open scoped unitInterval

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A **loop of maximal totally real subspaces** of a complex normed space `E`, parametrized by
the unit interval: a family `Λ t` with `Λ 0 = Λ 1` of the form `Λ t = A t L₀` for a maximal
totally real subspace `L₀` and a continuous path `A` of complex-linear automorphisms. -/
structure TotallyRealLoop where
  /-- The subspace at time `t`. -/
  toFun : I → Submodule ℝ E
  /-- The loop is moved by a continuous frame of complex-linear automorphisms from a maximal
  totally real subspace. -/
  exists_frame : ∃ L₀ : Submodule ℝ E,
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀ ∧
    ∃ A : I → E ≃L[ℂ] E, Continuous (fun t => (A t : E →L[ℂ] E)) ∧
      ∀ t, toFun t = L₀.map (((A t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)
  /-- The loop is closed. -/
  toFun_zero_eq_toFun_one : toFun 0 = toFun 1

namespace TotallyRealLoop

variable {E}

attribute [coe] toFun

instance : CoeFun (TotallyRealLoop E) fun _ => I → Submodule ℝ E := ⟨toFun⟩

@[ext]
theorem ext {Λ Λ' : TotallyRealLoop E} (h : ∀ t, Λ t = Λ' t) : Λ = Λ' := by
  cases Λ
  cases Λ'
  congr
  exact funext h

variable (Λ : TotallyRealLoop E)

/-- Every subspace of a loop of maximal totally real subspaces is maximal totally real. -/
theorem isMaximalTotallyReal (t : I) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) (Λ t) := by
  obtain ⟨L₁, hL₁, A, -, hA⟩ := Λ.exists_frame
  rw [hA t]
  exact hL₁.map_linearEquiv (A t).toLinearEquiv

/-- The constant loop at a maximal totally real subspace. -/
noncomputable def const {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    TotallyRealLoop E where
  toFun _ := L₀
  exists_frame := ⟨L₀, hL₀, fun _ => ContinuousLinearEquiv.refl ℂ E, continuous_const,
    fun _ => (Submodule.map_id L₀).symm⟩
  toFun_zero_eq_toFun_one := rfl

@[simp]
theorem const_apply {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) (t : I) :
    const hL₀ t = L₀ :=
  (rfl)

/-- The pointwise image `t ↦ B t (Λ t)` of a loop of maximal totally real subspaces under a loop
`B` of complex-linear automorphisms. -/
noncomputable def map (B : I → E ≃L[ℂ] E) (hB : Continuous fun t => (B t : E →L[ℂ] E))
    (hB01 : B 0 = B 1) : TotallyRealLoop E where
  toFun t := (Λ t).map (((B t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)
  exists_frame := by
    obtain ⟨L₀, hL₀, A, hA, hΛ⟩ := Λ.exists_frame
    refine ⟨L₀, hL₀, fun t => (A t).trans (B t), ?_, fun t => ?_⟩
    · have h : (fun t => ((A t).trans (B t) : E →L[ℂ] E)) =
          fun t => (B t : E →L[ℂ] E) ∘L (A t : E →L[ℂ] E) := by
        funext t
        ext x
        simp
      rw [h]
      exact hB.clm_comp hA
    · rw [hΛ t, ← Submodule.map_comp]
      rfl
  toFun_zero_eq_toFun_one := by
    rw [Λ.toFun_zero_eq_toFun_one, hB01]

@[simp]
theorem map_apply (B : I → E ≃L[ℂ] E) (hB : Continuous fun t => (B t : E →L[ℂ] E))
    (hB01 : B 0 = B 1) (t : I) :
    Λ.map B hB hB01 t = (Λ t).map (((B t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) :=
  (rfl)

variable [FiniteDimensional ℂ E]

/-- The frame `t ↦ e^{iπt} • id` of `TauCeti.TotallyRealLoop.rotation`. -/
private noncomputable def rotationFrame (t : I) : E ≃L[ℂ] E :=
  (LinearEquiv.smulOfNeZero ℂ E (Complex.exp ((π * t : ℝ) * Complex.I))
    (Complex.exp_ne_zero _)).toContinuousLinearEquiv

private theorem rotationFrame_toLinearEquiv (t : I) :
    (((rotationFrame (E := E) t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
      (LinearMap.lsmul ℂ E (Complex.exp ((π * t : ℝ) * Complex.I))).restrictScalars ℝ := by
  ext x
  simp [rotationFrame]

/-- The loop `t ↦ e^{iπt} L₀`, `t ∈ [0, 1]`, turning a maximal totally real subspace `L₀` through
half a revolution; it closes up because `-L₀ = L₀`. -/
noncomputable def rotation {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    TotallyRealLoop E where
  toFun t := L₀.map
    ((LinearMap.lsmul ℂ E (Complex.exp ((π * t : ℝ) * Complex.I))).restrictScalars ℝ)
  exists_frame := by
    refine ⟨L₀, hL₀, rotationFrame, ?_, fun t => by rw [rotationFrame_toLinearEquiv]⟩
    have h (t : I) : (rotationFrame (E := E) t : E →L[ℂ] E) =
        Complex.exp ((π * t : ℝ) * Complex.I) • ContinuousLinearMap.id ℂ E := by
      ext x
      simp [rotationFrame]
    simp_rw [h]
    fun_prop
  toFun_zero_eq_toFun_one := by
    have h1 :
        (LinearMap.lsmul ℂ E (Complex.exp ((π * (1 : I) : ℝ) * Complex.I))).restrictScalars ℝ =
          -LinearMap.id := by
      ext x
      simp [Complex.exp_pi_mul_I]
    have h0 :
        (LinearMap.lsmul ℂ E (Complex.exp ((π * (0 : I) : ℝ) * Complex.I))).restrictScalars ℝ =
          LinearMap.id := by
      ext x
      simp
    rw [h0, h1, Submodule.map_neg]

@[simp]
theorem rotation_apply {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) (t : I) :
    rotation hL₀ t =
      L₀.map ((LinearMap.lsmul ℂ E (Complex.exp ((π * t : ℝ) * Complex.I))).restrictScalars ℝ) :=
  (rfl)

end TotallyRealLoop

end TauCeti
