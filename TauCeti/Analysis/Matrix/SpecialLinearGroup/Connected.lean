/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Path connectedness of the complex special linear group

`Matrix.SpecialLinearGroup n ℂ` is path connected for every finite index type `n`
(`Matrix.SpecialLinearGroup.instPathConnectedSpace`). For `|n| ≤ 1` it is a subsingleton
(`Matrix.SpecialLinearGroup.subsingleton_of_subsingleton`); for `|n| ≥ 2`,
`Matrix.SpecialLinearGroup.diagonal_transvection_induction'` reduces connectivity to affine paths of
elementary transvections and exponential paths `t ↦ diag2n hij (exp (t • log c)) _` of two-entry
determinant-one diagonal matrices.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222, 2015,
  Proposition 1.14.
-/

public section

noncomputable section

open scoped unitInterval
open Matrix Topology

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem joined_one_transvection {i j : n} (hij : i ≠ j) (a : ℂ) :
    Joined (1 : SpecialLinearGroup n ℂ) (transvection hij a) := by
  have hcont : Continuous fun t : I => (1 : Matrix n n ℂ) + single i j ((t : ℝ) • a) := by
    have hlin : (fun t : I => (1 : Matrix n n ℂ) + single i j ((t : ℝ) • a)) =
        fun t : I => (1 : Matrix n n ℂ) + ((t : ℝ) • a) • single i j (1 : ℂ) := by
      ext; simp [smul_single]
    have ha : Continuous fun t : I => (t : ℝ) • a := continuous_subtypeVal.smul continuous_const
    exact hlin ▸ continuous_const.add (ha.smul continuous_const)
  refine ⟨{
    toFun := fun t => transvection hij ((t : ℝ) • a)
    continuous_toFun := (hcont.subtype_mk fun t => ?_).congr fun t =>
      Subtype.ext (transvection_coe hij ((t : ℝ) • a)).symm
    source' := Subtype.ext (by simp)
    target' := Subtype.ext (by simp) }⟩
  rw [← transvection_coe hij]; exact (transvection hij ((t : ℝ) • a)).property

private theorem joined_one_diag2n {i j : n} (hij : i ≠ j) {c : ℂ} (hc : c ≠ 0) :
    Joined (1 : SpecialLinearGroup n ℂ) (diag2n hij c hc) := by
  let z : ℂ := Complex.log c
  have hval : Continuous (Subtype.val : I → ℝ) := continuous_subtypeVal
  let M : I → Matrix n n ℂ := fun t => diagonal fun k =>
    if k = i then Complex.exp ((t : ℝ) • z)
    else if k = j then Complex.exp (-((t : ℝ) • z)) else 1
  have hM_eq : ∀ t : I, M t = (diag2n hij (Complex.exp ((t : ℝ) • z))
      (Complex.exp_ne_zero _) : Matrix n n ℂ) := fun t => by
    ext; simp [M, diag2n_coe, Complex.exp_neg]
  have hcont : Continuous M := Continuous.matrix_diagonal <| continuous_pi fun k => by
    by_cases hki : k = i
    · simp only [hki, ↓reduceIte]; exact Complex.continuous_exp.comp (hval.smul continuous_const)
    · simp only [hki, ↓reduceIte]
      by_cases hkj : k = j
      · simp only [hkj, ↓reduceIte]
        exact Complex.continuous_exp.comp (hval.smul continuous_const).neg
      · simp only [hkj, ↓reduceIte]; exact continuous_const
  refine ⟨{
    toFun := fun t => diag2n hij (Complex.exp ((t : ℝ) • z)) (Complex.exp_ne_zero _)
    continuous_toFun := (hcont.subtype_mk fun t => hM_eq t ▸ (diag2n hij _ _).property).congr
      fun t => Subtype.ext (hM_eq t)
    source' := Subtype.ext (by ext; simp [diag2n_coe, Matrix.one_apply, Matrix.diagonal_apply])
    target' := Subtype.ext (by simp [z, diag2n_coe, Complex.exp_log hc]) }⟩

/-- **The complex special linear group is path connected**, including in sizes zero and one. -/
instance instPathConnectedSpace : PathConnectedSpace (SpecialLinearGroup n ℂ) := by
  rcases subsingleton_or_nontrivial n with _ | _
  · exact PathConnectedSpace.mk ⟨1⟩ fun x y => Subsingleton.elim x y ▸ Joined.refl x
  · have h1 : ∀ M : SpecialLinearGroup n ℂ, Joined 1 M := fun M =>
      diagonal_transvection_induction' (Joined 1) M
        (fun _ _ hij _ hc => joined_one_diag2n hij hc)
        (fun _ _ hij a => joined_one_transvection hij a)
        fun _ _ ha hb => one_mul (1 : SpecialLinearGroup n ℂ) ▸ ha.mul hb
    exact PathConnectedSpace.mk ⟨1⟩ fun x y => (h1 x).symm.trans (h1 y)

end Matrix.SpecialLinearGroup
