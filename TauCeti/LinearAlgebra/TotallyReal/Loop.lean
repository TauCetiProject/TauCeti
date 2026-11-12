/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Loops of totally real subspaces

Let `E` be a complex seminormed space. A *loop of maximal totally real subspaces* of `E`
(`TauCeti.TotallyRealLoop`) is a family `Λ : [0, 1] → Submodule ℝ E` with `Λ 0 = Λ 1` of the form
`Λ t = A t L₀`, where `L₀` is maximal totally real and `A` is a continuous path of complex-linear
automorphisms of `E`. In finite-dimensional normed spaces, this is the usual notion of a
continuous loop in the totally real Grassmannian `GL(n, ℂ) / GL(n, ℝ)`, since paths in that
homogeneous space lift to `GL(n, ℂ)`. Such loops give boundary conditions for Cauchy--Riemann
operators.

## Main declarations

* `TauCeti.TotallyRealLoop`: loops of maximal totally real subspaces.
* `TauCeti.TotallyRealLoop.isMaximalTotallyReal`: every subspace of such a loop is maximal
  totally real.
* `TauCeti.TotallyRealLoop.const`: the constant loop at a maximal totally real subspace.
* `TauCeti.exists_frame_map`: composing a frame with a continuous family of automorphisms gives a
  frame of the image.
* `TauCeti.TotallyRealLoop.map`: the pointwise image `t ↦ B t (Λ t)` under a loop `B` of
  complex-linear automorphisms.
* `TauCeti.TotallyRealLoop.symm`: the loop `t ↦ Λ (1 - t)` traversed backwards.
* `TauCeti.TotallyRealLoop.rotation`: the half-turn `t ↦ e^{iπt} L₀`, which closes up since
  `-L₀ = L₀`.
* `TauCeti.TotallyRealLoop.rotationZPow`: the `k`-fold half-turn `t ↦ e^{iπkt} L₀` for an integer
  `k`, which closes up since `e^{iπk} = ±1`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (loops of totally real subspaces as boundary
  conditions).
-/

public section

open Real
open scoped unitInterval

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

/-- Composing a frame with a continuous family of complex-linear automorphisms gives a frame of
the image: if `Λ x = A x L₀` for a continuous family `A`, then `B x (Λ x) = (B x ∘ A x) L₀`, and
`x ↦ B x ∘ A x` is again continuous. -/
theorem exists_frame_map {X : Type*} [TopologicalSpace X] {Λ : X → Submodule ℝ E}
    (hΛ : ∃ L₀ : Submodule ℝ E,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀ ∧
      ∃ A : X → E ≃L[ℂ] E, Continuous (fun x => (A x : E →L[ℂ] E)) ∧
        ∀ x, Λ x = L₀.map (((A x).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (B : X → E ≃L[ℂ] E) (hB : Continuous fun x => (B x : E →L[ℂ] E)) :
    ∃ L₀ : Submodule ℝ E,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀ ∧
      ∃ A : X → E ≃L[ℂ] E, Continuous (fun x => (A x : E →L[ℂ] E)) ∧
        ∀ x, (Λ x).map (((B x).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
          L₀.map (((A x).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) := by
  obtain ⟨L₀, hL₀, A, hA, hΛ⟩ := hΛ
  refine ⟨L₀, hL₀, fun x => (A x).trans (B x), ?_, fun x => ?_⟩
  · have h : (fun x => ((A x).trans (B x) : E →L[ℂ] E)) =
        fun x => (B x : E →L[ℂ] E) ∘L (A x : E →L[ℂ] E) := by
      funext x
      ext y
      simp
    rw [h]
    exact hB.clm_comp hA
  · rw [hΛ x, ← Submodule.map_comp]
    rfl

variable (E) in
/-- A **loop of maximal totally real subspaces** of a complex seminormed space `E`, parametrized by
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
  exists_frame := exists_frame_map Λ.exists_frame B hB
  toFun_zero_eq_toFun_one := by
    rw [Λ.toFun_zero_eq_toFun_one, hB01]

@[simp]
theorem map_apply (B : I → E ≃L[ℂ] E) (hB : Continuous fun t => (B t : E →L[ℂ] E))
    (hB01 : B 0 = B 1) (t : I) :
    Λ.map B hB hB01 t = (Λ t).map (((B t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) :=
  (rfl)

/-- The reverse `t ↦ Λ (1 - t)` of a loop of maximal totally real subspaces: the same loop
traversed backwards. -/
def symm : TotallyRealLoop E where
  toFun t := Λ (σ t)
  exists_frame := by
    obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
    exact ⟨L₀, hL₀, fun t => A (σ t), hAc.comp unitInterval.continuous_symm, fun t => hA (σ t)⟩
  toFun_zero_eq_toFun_one := by
    simp only [unitInterval.symm_zero, unitInterval.symm_one]
    exact Λ.toFun_zero_eq_toFun_one.symm

@[simp]
theorem symm_apply (t : I) : Λ.symm t = Λ (σ t) :=
  (rfl)

/-- Reversing a loop twice gives the loop back. -/
@[simp]
theorem symm_symm : Λ.symm.symm = Λ :=
  ext fun t => by simp

/-- The frame `t ↦ e^{iat} • id` of the rotations `TauCeti.TotallyRealLoop.rotation` (`a = π`) and
`TauCeti.TotallyRealLoop.rotationZPow` (`a = πk`). -/
private noncomputable def rotationFrame (a : ℝ) (t : I) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (Complex.exp ((a * t : ℝ) * Complex.I)) (Complex.exp_ne_zero _))

private theorem rotationFrame_toLinearEquiv (a : ℝ) (t : I) :
    (((rotationFrame (E := E) a t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
      (LinearMap.lsmul ℂ E (Complex.exp ((a * t : ℝ) * Complex.I))).restrictScalars ℝ := by
  ext x
  simp [rotationFrame]

private theorem continuous_rotationFrame (a : ℝ) :
    Continuous fun t => (rotationFrame (E := E) a t : E →L[ℂ] E) := by
  have h (t : I) : (rotationFrame (E := E) a t : E →L[ℂ] E) =
      Complex.exp ((a * t : ℝ) * Complex.I) • ContinuousLinearMap.id ℂ E := by
    ext x
    simp [rotationFrame]
  simp_rw [h]
  fun_prop

/-- The loop `t ↦ e^{iπt} L₀`, `t ∈ [0, 1]`, turning a maximal totally real subspace `L₀` through
half a revolution; it closes up because `-L₀ = L₀`. -/
noncomputable def rotation {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    TotallyRealLoop E where
  toFun t := L₀.map
    ((LinearMap.lsmul ℂ E (Complex.exp ((π * t : ℝ) * Complex.I))).restrictScalars ℝ)
  exists_frame := by
    exact ⟨L₀, hL₀, rotationFrame π, continuous_rotationFrame π,
      fun t => by rw [rotationFrame_toLinearEquiv]⟩
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

/-- The loop `t ↦ e^{iπkt} L₀`, `t ∈ [0, 1]`, turning a maximal totally real subspace `L₀` through
`k` half revolutions, for an integer `k`; it closes up because `e^{iπk} = ±1` and `-L₀ = L₀`. For
`k = 1` it is the half-turn `TauCeti.TotallyRealLoop.rotation`
(`TauCeti.TotallyRealLoop.rotationZPow_one`). On the unit circle `θ = 2πt`, this is the loop
`θ ↦ e^{ikθ/2} L₀`. -/
noncomputable def rotationZPow {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) (k : ℤ) :
    TotallyRealLoop E where
  toFun t := L₀.map
    ((LinearMap.lsmul ℂ E (Complex.exp ((π * k * t : ℝ) * Complex.I))).restrictScalars ℝ)
  exists_frame :=
    ⟨L₀, hL₀, rotationFrame (π * k), continuous_rotationFrame (π * k),
      fun t => by rw [rotationFrame_toLinearEquiv]⟩
  toFun_zero_eq_toFun_one := by
    have h0 :
        (LinearMap.lsmul ℂ E (Complex.exp ((π * k * (0 : I) : ℝ) * Complex.I))).restrictScalars ℝ =
          LinearMap.id := by
      ext x
      simp
    -- `e^{iπk} = (-1) ^ k` acts as `±1`.
    have hk : Complex.exp ((π * k * (1 : I) : ℝ) * Complex.I) = (-1) ^ k := by
      rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      push_cast
      ring_nf
    rw [h0, hk, Submodule.map_id]
    rcases Int.even_or_odd k with he | ho
    · rw [he.neg_one_zpow]
      have : (LinearMap.lsmul ℂ E (1 : ℂ)).restrictScalars ℝ = LinearMap.id := by
        ext x
        simp
      rw [this, Submodule.map_id]
    · rw [ho.neg_one_zpow]
      have : (LinearMap.lsmul ℂ E (-1 : ℂ)).restrictScalars ℝ = -LinearMap.id := by
        ext x
        simp
      rw [this, Submodule.map_neg, Submodule.map_id]

@[simp]
theorem rotationZPow_apply {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) (k : ℤ)
    (t : I) :
    rotationZPow hL₀ k t = L₀.map
      ((LinearMap.lsmul ℂ E (Complex.exp ((π * k * t : ℝ) * Complex.I))).restrictScalars ℝ) :=
  (rfl)

/-- The single half-turn is the half-turn `TauCeti.TotallyRealLoop.rotation`. -/
@[simp]
theorem rotationZPow_one {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    rotationZPow hL₀ 1 = rotation hL₀ :=
  ext fun t => by simp

/-- Zero half-turns give the constant loop. -/
@[simp]
theorem rotationZPow_zero {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    rotationZPow hL₀ 0 = const hL₀ :=
  ext fun t => by
    have : (LinearMap.lsmul ℂ E (1 : ℂ)).restrictScalars ℝ = LinearMap.id := by
      ext x
      simp
    simp [this]

end TotallyRealLoop

end TauCeti
