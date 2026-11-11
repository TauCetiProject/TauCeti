/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Path

import Mathlib.Topology.Subpath

/-!
# Concatenation and base-point invariance of the Maslov index of loops

Let `E` be a finite-dimensional complex normed space. This file proves the two loop-level facts
behind the boundary formula for the Maslov index of a bundle pair over a surface with several
boundary circles, and behind the composition axiom for gluing surfaces along boundary circles.

* **Concatenation.** Two loops `Λ`, `Γ` of maximal totally real subspaces with the same base
  subspace `Λ 0 = Γ 0` concatenate to a loop `Λ ⬝ Γ` (`TauCeti.TotallyRealLoop.trans`), and
  `μ(Λ ⬝ Γ) = μ(Λ) + μ(Γ)` (`TauCeti.TotallyRealLoop.maslovIndex_trans`). In particular
  `μ(Λ ⬝ Λ⁻¹) = 0` (`TauCeti.TotallyRealLoop.maslovIndex_trans_symm`).
* **Base-point invariance.** The loop `Λ` read from the time `s` onwards, that is `Λ` on `[s, 1]`
  followed by `Λ` on `[0, s]` (`TauCeti.TotallyRealLoop.shift`), has the same Maslov index as `Λ`
  (`TauCeti.TotallyRealLoop.maslovIndex_shift`). So the Maslov index of a boundary circle does not
  depend on where the parametrization of the circle starts.

Invariance under free homotopies through loops, where the base subspace moves during the
homotopy, is `TauCeti.TotallyRealLoop.maslovIndex_eq_of_homotopy`: its hypothesis only asks each
intermediate family `t ↦ A (s, t) L₀` to be closed.

Paths are cut into pieces with `TauCeti.TotallyRealPath.subpath`, the restriction of a path to the
segment between two times, and a path with equal endpoints is read as a loop with
`TauCeti.TotallyRealPath.toTotallyRealLoop`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (the Maslov index of a loop of totally real
  subspaces, Theorem C.3.5 (composition) and Theorem C.3.6 (the loop formula)).
-/

public section

open Real
open scoped unitInterval

namespace TauCeti

namespace TotallyRealPath

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

/-- The restriction of a path of maximal totally real subspaces to the segment from time `a` to
time `b`, reparametrized by `[0, 1]`: `t ↦ Λ ((1 - t) a + t b)`. -/
def subpath (Λ : TotallyRealPath E) (a b : I) : TotallyRealPath E where
  toFun t := Λ (Set.Icc.convexComb a b t)
  exists_frame := by
    obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
    exact ⟨L₀, hL₀, fun t => A (Set.Icc.convexComb a b t),
      hAc.comp (Set.Icc.continuous_convexComb a b), fun t => hA (Set.Icc.convexComb a b t)⟩

theorem subpath_apply (Λ : TotallyRealPath E) (a b t : I) :
    Λ.subpath a b t = Λ (Set.Icc.convexComb a b t) :=
  (rfl)

/-- The restriction of a path to `[a, b]` starts at `Λ a`. -/
@[simp]
theorem subpath_zero (Λ : TotallyRealPath E) (a b : I) : Λ.subpath a b 0 = Λ a :=
  congrArg Λ (Set.Icc.convexComb_zero a b)

/-- The restriction of a path to `[a, b]` ends at `Λ b`. -/
@[simp]
theorem subpath_one (Λ : TotallyRealPath E) (a b : I) : Λ.subpath a b 1 = Λ b :=
  congrArg Λ (Set.Icc.convexComb_one a b)

/-- A path of maximal totally real subspaces whose endpoints agree, read as a loop. -/
def toTotallyRealLoop (Λ : TotallyRealPath E) (h : Λ 0 = Λ 1) : TotallyRealLoop E :=
  ⟨Λ.toFun, Λ.exists_frame, h⟩

@[simp]
theorem toTotallyRealLoop_apply (Λ : TotallyRealPath E) (h : Λ 0 = Λ 1) (t : I) :
    Λ.toTotallyRealLoop h t = Λ t :=
  (rfl)

/-- Reading a loop as a path and back gives the loop. -/
@[simp]
theorem _root_.TauCeti.TotallyRealLoop.toTotallyRealPath_toTotallyRealLoop
    (Λ : TotallyRealLoop E) :
    Λ.toTotallyRealPath.toTotallyRealLoop (by simpa using Λ.toFun_zero_eq_toFun_one) = Λ :=
  TotallyRealLoop.ext fun t => by simp

/-- Reading a closed path as a loop and back gives the path. -/
@[simp]
theorem toTotallyRealLoop_toTotallyRealPath (Λ : TotallyRealPath E) (h : Λ 0 = Λ 1) :
    (Λ.toTotallyRealLoop h).toTotallyRealPath = Λ :=
  ext fun t => by simp

end

end TotallyRealPath

namespace TotallyRealLoop

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

/-- The concatenation of two loops of maximal totally real subspaces with the same base subspace
`Λ 0 = Γ 0`: it runs through `Λ` and then through `Γ`, each at double speed, as
`TauCeti.TotallyRealPath.trans` does. -/
noncomputable def trans (Λ Γ : TotallyRealLoop E) (h : Λ 0 = Γ 0) : TotallyRealLoop E :=
  TotallyRealPath.toTotallyRealLoop
    (Λ.toTotallyRealPath.trans Γ.toTotallyRealPath
      (by simpa using Λ.toFun_zero_eq_toFun_one.symm.trans h))
    (by simpa [h] using Γ.toFun_zero_eq_toFun_one)

/-- The concatenation of loops is the concatenation of the underlying paths. -/
@[simp]
theorem toTotallyRealPath_trans (Λ Γ : TotallyRealLoop E) (h : Λ 0 = Γ 0) :
    (Λ.trans Γ h).toTotallyRealPath =
      Λ.toTotallyRealPath.trans Γ.toTotallyRealPath
        (by simpa using Λ.toFun_zero_eq_toFun_one.symm.trans h) := by
  simp [trans]

/-- The concatenation is `Λ` at double speed on `[0, 1 / 2]` and `Γ` at double speed after. -/
theorem trans_apply (Λ Γ : TotallyRealLoop E) (h : Λ 0 = Γ 0) (t : I) :
    Λ.trans Γ h t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        Λ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      else Γ ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
  simp only [trans, TotallyRealPath.toTotallyRealLoop_apply, TotallyRealPath.trans_apply,
    toTotallyRealPath_apply]

/-- The concatenation of two loops is based at their common base subspace. -/
@[simp]
theorem trans_zero (Λ Γ : TotallyRealLoop E) (h : Λ 0 = Γ 0) : Λ.trans Γ h 0 = Λ 0 := by
  simp [trans]

/-- The loop `Λ` read from time `s` onwards: `Λ` on `[s, 1]` followed by `Λ` on `[0, s]`, each
piece reparametrized at double speed. It is based at `Λ s`. -/
noncomputable def shift (Λ : TotallyRealLoop E) (s : I) : TotallyRealLoop E :=
  TotallyRealPath.toTotallyRealLoop
    ((Λ.toTotallyRealPath.subpath s 1).trans (Λ.toTotallyRealPath.subpath 0 s)
      (by simpa using Λ.toFun_zero_eq_toFun_one.symm))
    (by simp)

/-- The loop `Λ` read from time `s` onwards is based at `Λ s`. -/
@[simp]
theorem shift_zero (Λ : TotallyRealLoop E) (s : I) : Λ.shift s 0 = Λ s := by
  simp [shift]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The Maslov index is the degree of the loop of Maslov phases `t ↦ ρ(Λ 0, Λ t)`. -/
private theorem maslovIndex_eq_degree_maslovPhasePath (Λ : TotallyRealLoop E) :
    Λ.maslovIndex = Circle.degree Λ.maslovPhasePath :=
  Λ.maslovIndex_eq_degree (Λ.isMaximalTotallyReal 0) Λ.maslovPhasePath fun t =>
    maslovPhasePath_apply Λ t

/-- **Concatenation of loops adds Maslov indices:** for loops `Λ`, `Γ` with the same base
subspace, `μ(Λ ⬝ Γ) = μ(Λ) + μ(Γ)`. -/
@[simp]
theorem maslovIndex_trans (Λ Γ : TotallyRealLoop E) (h : Λ 0 = Γ 0) :
    (Λ.trans Γ h).maslovIndex = Λ.maslovIndex + Γ.maslovIndex := by
  -- Read all phases relative to the common base subspace `Λ 0 = Γ 0`.
  rw [(Λ.trans Γ h).maslovIndex_eq_degree (Λ.isMaximalTotallyReal 0)
    (Λ.maslovPhasePath.trans Γ.maslovPhasePath) fun t => ?_, Circle.degree_trans,
    maslovIndex_eq_degree_maslovPhasePath, maslovIndex_eq_degree_maslovPhasePath]
  rw [Path.trans_apply]
  split_ifs with ht
  · rw [maslovPhasePath_apply]
    exact (Λ.isMaximalTotallyReal 0).maslovPhase_congr _ _
      (by simp only [trans_apply, ht, ↓reduceDIte])
  · rw [maslovPhasePath_apply]
    exact (IsMaximalTotallyReal.maslovPhase_congr_left _ (Λ.isMaximalTotallyReal 0) _
      h.symm).trans
      (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (by simp only [trans_apply, ht, ↓reduceDIte]))

/-- A loop followed by its reverse has Maslov index zero. -/
theorem maslovIndex_trans_symm (Λ : TotallyRealLoop E) :
    (Λ.trans Λ.symm (by simpa using Λ.toFun_zero_eq_toFun_one)).maslovIndex = 0 := by
  simp

/-- **Base-point invariance of the Maslov index:** the loop `Λ` read from any time `s` onwards
has the same Maslov index as `Λ`. -/
@[simp]
theorem maslovIndex_shift (Λ : TotallyRealLoop E) (s : I) :
    (Λ.shift s).maslovIndex = Λ.maslovIndex := by
  have hL := Λ.isMaximalTotallyReal 0
  -- A continuous angle function `θ` of `t ↦ ρ(Λ 0, Λ t)`.
  obtain ⟨θ, hθ', -⟩ := Circle.isCoveringMap_exp.exists_path_lifts Λ.maslovPhasePath.toContinuousMap
    0 (by simp)
  have hθ (t : I) : Circle.exp (θ t) = Λ.maslovPhasePath t := congr_fun hθ' t
  -- The phases of the two pieces of the shifted loop, as paths in the circle.
  let γ₁ := (Λ.maslovPhasePath.subpath s 1).cast rfl Λ.maslovPhasePath.target.symm
  let γ₂ := (Λ.maslovPhasePath.subpath 0 s).cast Λ.maslovPhasePath.source.symm rfl
  have h₁ : Circle.angleChange γ₁ = θ 1 - θ s := by
    rw [Circle.angleChange_eq_sub γ₁ (θ := fun t => θ (Set.Icc.convexComb s 1 t))
      (θ.continuous.comp (Set.Icc.continuous_convexComb s 1)) fun t => hθ _]
    simp only [Set.Icc.convexComb_zero, Set.Icc.convexComb_one]
  have h₂ : Circle.angleChange γ₂ = θ s - θ 0 := by
    rw [Circle.angleChange_eq_sub γ₂ (θ := fun t => θ (Set.Icc.convexComb 0 s t))
      (θ.continuous.comp (Set.Icc.continuous_convexComb 0 s)) fun t => hθ _]
    simp only [Set.Icc.convexComb_zero, Set.Icc.convexComb_one]
  have hshift : (Λ.shift s).maslovIndex = Circle.degree (γ₁.trans γ₂) := by
    refine (Λ.shift s).maslovIndex_eq_degree hL (γ₁.trans γ₂) fun t => ?_
    rw [Path.trans_apply]
    split_ifs with ht <;>
    · rw [Path.cast_coe, Path.subpath, Path.coe_mk_mk, Function.comp_apply, maslovPhasePath_apply]
      exact hL.maslovPhase_congr _ _ (by
        simp only [shift, TotallyRealPath.toTotallyRealLoop_apply, TotallyRealPath.trans_apply, ht,
          ↓reduceDIte, TotallyRealPath.subpath_apply, toTotallyRealPath_apply])
  have hdeg := Circle.angleChange_eq_degree_mul (γ₁.trans γ₂)
  rw [Circle.angleChange_trans, h₁, h₂, ← hshift] at hdeg
  have hμ := Circle.sub_eq_degree_mul Λ.maslovPhasePath θ.continuous hθ
  rw [← maslovIndex_eq_degree_maslovPhasePath] at hμ
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  exact_mod_cast mul_right_cancel₀ h2π (by linarith : ((Λ.shift s).maslovIndex : ℝ) * (2 * π) =
    Λ.maslovIndex * (2 * π))

end TotallyRealLoop

end TauCeti
