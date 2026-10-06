/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.LinearAlgebra.TotallyReal.Loop
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Phase
public import TauCeti.Topology.Circle.Degree

/-!
# The Maslov index of a loop of totally real subspaces

Let `E` be a finite-dimensional complex normed space and `Λ` a loop of maximal totally real
subspaces of `E` (`TauCeti.TotallyRealLoop`): a family `Λ : [0, 1] → Submodule ℝ E` with
`Λ 0 = Λ 1` of the form `Λ t = A t L₀`, where `L₀` is maximal totally real and `A` is a continuous
path of complex-linear automorphisms of `E`.

Its **Maslov index** `μ(Λ)` (`TauCeti.TotallyRealLoop.maslovIndex`) is the degree
(`Circle.degree`) of the loop of Maslov phases `t ↦ ρ(Λ 0, Λ t)` of the circle, read as a path
(`TauCeti.TotallyRealLoop.maslovPhasePath`), where
`ρ(L₀, A L₀) = det A / conj (det A)` is `TauCeti.IsMaximalTotallyReal.maslovPhase`.

* It does not depend on the reference subspace: for any maximal totally real `L₀` the phases
  `ρ(L₀, Λ t)` differ from `ρ(Λ 0, Λ t)` by the constant factor `ρ(L₀, Λ 0)`, so `μ(Λ)` is the
  degree of `t ↦ ρ(L₀, Λ t)` (`TauCeti.TotallyRealLoop.maslovIndex_eq_degree`), and every
  continuous angle function `θ` of it satisfies `θ 1 - θ 0 = 2π μ(Λ)`
  (`TauCeti.TotallyRealLoop.sub_eq_maslovIndex_mul`).
* It counts half-turns of the determinant of a frame: if `Λ t = A t L₀` and
  `det (A t) = |det (A t)| e^{i φ t}` with `φ` continuous, then `φ 1 - φ 0 = π μ(Λ)`
  (`TauCeti.TotallyRealLoop.sub_eq_maslovIndex_mul_pi`).
* It is invariant under homotopies of loops given by continuous two-parameter frames
  (`TauCeti.TotallyRealLoop.maslovIndex_eq_of_homotopy`).
* It is normalized: the half-turn `t ↦ e^{iπt} L₀`, which closes up since `-L₀ = L₀`, has Maslov
  index `n = dim_ℂ E` (`TauCeti.TotallyRealLoop.maslovIndex_rotation`); for `E = ℂ` and `L₀ = ℝ`
  this is the loop `e^{iπt} ℝ` of Maslov index one. The constant loop has Maslov index zero
  (`TauCeti.TotallyRealLoop.maslovIndex_const`).

The boundary Maslov index of a bundle pair, which enters the Riemann--Roch formula for
Cauchy--Riemann operators with totally real boundary conditions, is the Maslov index of the loop of
boundary subspaces in a trivialization.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (the Maslov index of a loop of totally real
  subspaces and the boundary Maslov index of a bundle pair).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Section 2.3 (the Maslov index
  of loops of Lagrangian subspaces as the degree of `det² : Λ(n) → S¹`).
-/

public section

open Module Real
open scoped ComplexConjugate unitInterval

namespace TauCeti

namespace TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (Λ : TotallyRealLoop E)

/-- Along a loop of maximal totally real subspaces, the Maslov phase relative to any fixed maximal
totally real subspace varies continuously. -/
theorem continuous_maslovPhase {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    Continuous fun t => hL₀.maslovPhase (Λ.isMaximalTotallyReal t) := by
  obtain ⟨L₁, hL₁, A, hAc, hA⟩ := Λ.exists_frame
  have hphase (t : I) : hL₀.maslovPhase (Λ.isMaximalTotallyReal t) =
      hL₀.maslovPhase hL₁ * (LinearMap.det ((A t).toLinearEquiv : E →ₗ[ℂ] E) /
        conj (LinearMap.det ((A t).toLinearEquiv : E →ₗ[ℂ] E))) := by
    rw [← hL₀.maslovPhase_mul_maslovPhase hL₁ (Λ.isMaximalTotallyReal t),
      hL₁.maslovPhase_congr (Λ.isMaximalTotallyReal t)
        (hL₁.map_linearEquiv (A t).toLinearEquiv) (hA t),
      IsMaximalTotallyReal.maslovPhase_map]
  simp_rw [hphase]
  exact continuous_const.mul (continuous_det_div_conj A hAc)

/-- The loop of Maslov phases `t ↦ ρ(Λ 0, Λ t)`, as a loop in the circle based at `1`. -/
noncomputable def maslovPhasePath : Path (1 : Circle) 1 where
  toFun t := ⟨(Λ.isMaximalTotallyReal 0).maslovPhase (Λ.isMaximalTotallyReal t),
    mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
  continuous_toFun :=
    (Λ.continuous_maslovPhase (Λ.isMaximalTotallyReal 0)).subtype_mk _
  source' := Circle.ext (IsMaximalTotallyReal.maslovPhase_self _)
  target' := Circle.ext <| by
    simp only [Circle.coe_one]
    rw [(Λ.isMaximalTotallyReal 0).maslovPhase_congr (Λ.isMaximalTotallyReal 1)
      (Λ.isMaximalTotallyReal 0) Λ.toFun_zero_eq_toFun_one.symm,
      IsMaximalTotallyReal.maslovPhase_self]

/-- The Maslov phase of `Λ t` relative to `Λ 0`, read as a complex number. -/
@[simp]
theorem maslovPhasePath_apply (t : I) :
    (Λ.maslovPhasePath t : ℂ) = (Λ.isMaximalTotallyReal 0).maslovPhase (Λ.isMaximalTotallyReal t) :=
  (rfl)

/-- The **Maslov index** of a loop of maximal totally real subspaces: the degree of its loop of
Maslov phases `t ↦ ρ(Λ 0, Λ t)` in the circle. -/
noncomputable def maslovIndex : ℤ :=
  Circle.degree Λ.maslovPhasePath

/-- The Maslov index read off a continuous angle function of the Maslov phases relative to an
arbitrary maximal totally real reference subspace `L₀`: if `e^{i θ t} = ρ(L₀, Λ t)`, then
`θ 1 - θ 0 = 2π μ(Λ)`. -/
theorem sub_eq_maslovIndex_mul {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    {θ : I → ℝ} (hθ : Continuous θ)
    (h : ∀ t, Complex.exp (θ t * Complex.I) = hL₀.maslovPhase (Λ.isMaximalTotallyReal t)) :
    θ 1 - θ 0 = Λ.maslovIndex * (2 * π) := by
  -- Changing the reference from `L₀` to `Λ 0` multiplies all phases by `ρ(Λ 0, L₀)`.
  set c : Circle := ⟨(Λ.isMaximalTotallyReal 0).maslovPhase hL₀,
    mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
  have hlift (t : I) : Circle.exp (Complex.arg c + θ t) = Λ.maslovPhasePath t := by
    rw [Circle.exp_add, Circle.exp_arg]
    refine Circle.ext ?_
    rw [Circle.coe_mul, Circle.coe_exp, h t]
    exact (Λ.isMaximalTotallyReal 0).maslovPhase_mul_maslovPhase hL₀ _
  have := Circle.sub_eq_degree_mul Λ.maslovPhasePath (continuous_const.add hθ) hlift
  rw [maslovIndex, ← this]
  simp

/-- The Maslov index is determined by any one continuous angle function of the Maslov phases
relative to a maximal totally real reference subspace. -/
theorem maslovIndex_eq_of_sub_eq {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    {θ : I → ℝ} (hθ : Continuous θ)
    (h : ∀ t, Complex.exp (θ t * Complex.I) = hL₀.maslovPhase (Λ.isMaximalTotallyReal t))
    {n : ℤ} (hn : θ 1 - θ 0 = n * (2 * π)) : Λ.maslovIndex = n := by
  have h' := (Λ.sub_eq_maslovIndex_mul hL₀ hθ h).symm.trans hn
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) h'

/-- The Maslov index is the degree of the loop of Maslov phases `t ↦ ρ(L₀, Λ t)` relative to any
maximal totally real reference subspace `L₀`. -/
theorem maslovIndex_eq_degree {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    {x : Circle} (γ : Path x x) (hγ : ∀ t, (γ t : ℂ) = hL₀.maslovPhase (Λ.isMaximalTotallyReal t)) :
    Λ.maslovIndex = Circle.degree γ := by
  obtain ⟨θ, hθ, -⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ.toContinuousMap
    (Complex.arg x) (by simp [Circle.exp_arg])
  have hθγ (t : I) : Circle.exp (θ t) = γ t := congr_fun hθ t
  refine Λ.maslovIndex_eq_of_sub_eq hL₀ θ.continuous (fun t => ?_)
    (Circle.sub_eq_degree_mul γ θ.continuous hθγ)
  rw [← Circle.coe_exp, hθγ, hγ]

/-- **Homotopy invariance of the Maslov index.** Let `A (s, t)` be a continuous two-parameter
family of complex-linear automorphisms and `L₀` a maximal totally real subspace such that every
`t ↦ A (s, t) L₀` is a closed loop. Then the loops `Λ₀ t = A (0, t) L₀` and `Λ₁ t = A (1, t) L₀`
have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopy (Λ₀ Λ₁ : TotallyRealLoop E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    (A : I × I → E ≃L[ℂ] E) (hA : Continuous fun p => (A p : E →L[ℂ] E))
    (h₀ : ∀ t, Λ₀ t = L₀.map (((A (0, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (h₁ : ∀ t, Λ₁ t = L₀.map (((A (1, t)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ))
    (hA01 : ∀ s, L₀.map (((A (s, 0)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) =
      L₀.map (((A (s, 1)).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)) :
    Λ₀.maslovIndex = Λ₁.maslovIndex := by
  -- The homotopy of Maslov phases `ρ(L₀, A (s, t) L₀) = det A (s, t) / conj (det A (s, t))`.
  let F : C(I × I, Circle) :=
    ⟨fun p => ⟨hL₀.maslovPhase (hL₀.map_linearEquiv (A p).toLinearEquiv),
      mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩, by
      simp_rw [IsMaximalTotallyReal.maslovPhase_map]
      exact (continuous_det_div_conj A hA).subtype_mk _⟩
  have hF (s : I) : F (s, 0) = F (s, 1) :=
    Circle.ext (hL₀.maslovPhase_congr _ _ (hA01 s))
  let γ (s : I) : Path (F (s, 0)) (F (s, 0)) :=
    { toFun := fun t => F (s, t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := (hF s).symm }
  have hμ₀ : Λ₀.maslovIndex = Circle.degree (γ 0) :=
    Λ₀.maslovIndex_eq_degree hL₀ (γ 0) fun t => hL₀.maslovPhase_congr _ _ (h₀ t).symm
  have hμ₁ : Λ₁.maslovIndex = Circle.degree (γ 1) :=
    Λ₁.maslovIndex_eq_degree hL₀ (γ 1) fun t => hL₀.maslovPhase_congr _ _ (h₁ t).symm
  rw [hμ₀, hμ₁]
  exact Circle.degree_eq_of_homotopy (γ 0) (γ 1) F (fun _ => rfl) (fun _ => rfl) hF

/-- The Maslov index counts half-turns of the determinant of a frame: if `Λ t = A t L₀` and
`det (A t) = |det (A t)| e^{i φ t}` with `φ` continuous, then `φ 1 - φ 0 = π μ(Λ)`. -/
theorem sub_eq_maslovIndex_mul_pi {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    (A : I → E ≃ₗ[ℂ] E) (hA : ∀ t, Λ t = L₀.map ((A t : E →ₗ[ℂ] E).restrictScalars ℝ))
    {φ : I → ℝ} (hφ : Continuous φ)
    (h : ∀ t, LinearMap.det (A t : E →ₗ[ℂ] E) =
      ‖LinearMap.det (A t : E →ₗ[ℂ] E)‖ * Complex.exp (φ t * Complex.I)) :
    φ 1 - φ 0 = Λ.maslovIndex * π := by
  have hphase (t : I) : Complex.exp ((2 * φ t : ℝ) * Complex.I) =
      hL₀.maslovPhase (Λ.isMaximalTotallyReal t) := by
    rw [hL₀.maslovPhase_congr (Λ.isMaximalTotallyReal t) (hL₀.map_linearEquiv (A t)) (hA t),
      IsMaximalTotallyReal.maslovPhase_map, h t]
    have hr : ((‖LinearMap.det (A t : E →ₗ[ℂ] E)‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, norm_ne_zero_iff, ← LinearEquiv.coe_det]
      exact (LinearEquiv.det (A t)).ne_zero
    simp [← Complex.exp_conj, mul_div_mul_left _ _ hr, ← Complex.exp_sub]
    ring_nf
  have := Λ.sub_eq_maslovIndex_mul hL₀ (θ := fun t => 2 * φ t) (by fun_prop) hphase
  linarith

/-- The constant loop has Maslov index zero. -/
@[simp]
theorem maslovIndex_const {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    (const hL₀).maslovIndex = 0 :=
  (const hL₀).maslovIndex_eq_of_sub_eq hL₀ (θ := fun _ => 0) continuous_const
    (fun t => by
      rw [hL₀.maslovPhase_congr ((const hL₀).isMaximalTotallyReal t) hL₀ (const_apply hL₀ t)]
      simp)
    (by simp)

/-- **Normalization of the Maslov index.** The half-turn `t ↦ e^{iπt} L₀` of a maximal totally
real subspace of an `n`-dimensional complex space has Maslov index `n`. -/
@[simp]
theorem maslovIndex_rotation {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    (rotation hL₀).maslovIndex = finrank ℂ E := by
  -- The frame `t ↦ e^{iπt} • id` has determinant `e^{iπnt}`.
  let A (t : I) : E ≃ₗ[ℂ] E := LinearEquiv.smulOfNeZero ℂ E
    (Complex.exp ((π * t : ℝ) * Complex.I)) (Complex.exp_ne_zero _)
  have hA (t : I) :
      (A t : E →ₗ[ℂ] E) = Complex.exp ((π * t : ℝ) * Complex.I) • LinearMap.id := by
    ext x
    simp [A]
  have key := (rotation hL₀).sub_eq_maslovIndex_mul_pi hL₀ A
    (fun t => by
      have hlsmul : LinearMap.lsmul ℂ E (Complex.exp ((π * t : ℝ) * Complex.I)) =
          Complex.exp ((π * t : ℝ) * Complex.I) • LinearMap.id := by
        ext x
        simp
      rw [rotation_apply, hA, hlsmul])
    (φ := fun t => finrank ℂ E * (π * t)) (by fun_prop) (fun t => by
      rw [hA, LinearMap.det_smul, LinearMap.det_id, mul_one, norm_pow,
        Complex.norm_exp_ofReal_mul_I]
      simp [← Complex.exp_nat_mul]
      ring_nf)
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, sub_zero] at key
  exact_mod_cast (mul_right_cancel₀ hπ key).symm

end TotallyRealLoop

end TauCeti
