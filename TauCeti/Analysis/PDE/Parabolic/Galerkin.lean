/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Inhomogeneous
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.InnerProductSpace.GelfandTriple
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Galerkin approximations of autonomous parabolic equations

Let `ι : V → H` embed an energy space into a real pivot Hilbert space, and let
`A : V → V*` be a bounded linear operator. For a finite-dimensional real inner product space
`F` and a continuous linear map `e : F → V` whose composite with `ι` is injective, the
Galerkin equation is

`⟪ι(e c'(t)), ι(e v)⟫ + A(e c(t))(e v) = f(t)(e v)` for every `v : F`.

For continuous `f : ℝ → V*`, this equation has a unique global `C¹` solution for any initial
coordinate vector. No symmetry or coercivity of `A` is needed for this existence result.
Injectivity into the pivot space makes the finite-dimensional mass operator invertible.
Mathlib's `ContinuousLinearMap.bilinearComp` restricts the forms, and
`InnerProductSpace.continuousLinearMapOfBilin` represents them as operators.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, Theorem 1.
-/

public section

noncomputable section

open InnerProductSpace
open scoped InnerProductSpace

namespace TauCeti.PDE

variable {V H F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Existence and uniqueness of Galerkin approximations.** For a bounded autonomous energy
operator, continuous forcing and a finite-dimensional trial map injective into the pivot space,
the projected parabolic equation has a unique global `C¹` solution with prescribed value at
any time `t₀`. The coordinates need not be orthonormal in the pivot space. -/
theorem existsUnique_galerkinSolution (ι : V →L[ℝ] H) (A : V →L[ℝ] StrongDual ℝ V)
    (e : F →L[ℝ] V) (he : Function.Injective (ι.comp e)) {f : ℝ → StrongDual ℝ V}
    (hf : Continuous f) (x : F) (t₀ : ℝ) :
    ∃! c : ℝ → F, c t₀ = x ∧ ContDiff ℝ 1 c ∧ ∀ t v,
      ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + A (e (c t)) (e v) = f t (e v) := by
  -- Represent the restricted mass and energy forms by operators on the coordinate space.
  let j := ι.comp e
  let M := continuousLinearMapOfBilin (j.gelfandDual.comp j)
  let D := continuousLinearMapOfBilin (A.bilinearComp e e)
  let R : StrongDual ℝ V →L[ℝ] F :=
    (toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ F V ℝ).flip e)
  have hM (z v : F) : ⟪M z, v⟫_ℝ = ⟪j z, j v⟫_ℝ := by
    simp [M]
  have hD (z v : F) : ⟪D z, v⟫_ℝ = A (e z) (e v) := by
    simp [D]
  have hR (g : StrongDual ℝ V) (v : F) : ⟪R g, v⟫_ℝ = g (e v) := by
    simp [R]
  -- Testing the mass operator on its argument proves injectivity; finite dimension gives an
  -- inverse, without any coercivity assumption on the energy form.
  have hMinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).2 fun z hz ↦ ?_
    have hjz : j z = 0 := by
      have hnorm : ‖j z‖ ^ 2 = 0 := by
        simpa [hz, real_inner_self_eq_norm_sq] using (hM z z).symm
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    exact he (by simpa only [map_zero] using hjz)
  let Q : F ≃L[ℝ] F :=
    (LinearEquiv.ofInjectiveEndo M.toLinearMap hMinj).toContinuousLinearEquiv
  have hQ (z : F) : Q z = M z := by
    simp [Q]
  let B : F →L[ℝ] F := -(Q.symm.toContinuousLinearMap.comp D)
  let g : ℝ → F := fun t ↦ Q.symm (R (f t))
  have hg : Continuous g := Q.symm.continuous.comp (R.continuous.comp hf)
  have hEq (z d : F) (t : ℝ) :
      (∀ v, ⟪ι (e d), ι (e v)⟫_ℝ + A (e z) (e v) = f t (e v)) ↔
        d = B z + g t := by
    constructor
    · intro h
      have hmass : Q d = R (f t) - D z := by
        apply ext_inner_right ℝ
        intro v
        simp only [hQ, hM, inner_sub_left, hR, hD]
        exact eq_sub_of_add_eq (h v)
      have := congrArg Q.symm hmass
      simpa [B, g, map_sub, sub_eq_add_neg, add_comm] using this
    · rintro rfl
      have hmass : M (B z + g t) = R (f t) - D z := by
        rw [← hQ]
        simp [B, g, sub_eq_add_neg, add_comm]
      intro v
      have hv := congrArg (fun w : F ↦ ⟪w, v⟫_ℝ) hmass
      simp only [hM, inner_sub_left, hR, hD] at hv
      exact (eq_sub_iff_add_eq).1 hv
  -- Solve the reduced ODE, then transfer both its equation and its uniqueness back.
  obtain ⟨c, hc, huniq⟩ := B.existsUnique_hasDerivAt_add hg x t₀
  have hderiv : deriv c = fun t ↦ B (c t) + g t := by
    funext t
    exact (hc.2 t).deriv
  have hc1 : ContDiff ℝ 1 c := contDiff_one_iff_deriv.2
    ⟨fun t ↦ (hc.2 t).differentiableAt,
      hderiv ▸ (B.continuous.comp
        (continuous_iff_continuousAt.2 fun t ↦ (hc.2 t).continuousAt)).add hg⟩
  refine ⟨c, ⟨hc.1, hc1, fun t ↦ (hEq _ _ t).2 ((hc.2 t).deriv)⟩, ?_⟩
  intro d hd
  apply huniq d
  refine ⟨hd.1, fun t ↦ ?_⟩
  rw [← (hEq (d t) (deriv d t) t).1 (hd.2.2 t)]
  exact (hd.2.1.differentiable one_ne_zero t).hasDerivAt

end TauCeti.PDE
