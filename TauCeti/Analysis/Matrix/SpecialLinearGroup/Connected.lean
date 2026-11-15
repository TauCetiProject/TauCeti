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

The complex special linear group `SpecialLinearGroup n ℂ` is path connected for every finite index
type `n`, including in sizes zero and one (`Matrix.SpecialLinearGroup.instPathConnectedSpace`).

When `n` has at most one element, `SpecialLinearGroup n ℂ` is a subsingleton (`det [[c]] = c = 1`).
When `n` has at least two elements, `Matrix.SpecialLinearGroup.diagonal_transvection_induction'`
reduces path connectivity to two explicit families of one-parameter paths from `1`:

* elementary transvections `t ↦ transvection hij ((t : ℝ) • a)`, affine in the off-diagonal entry;
* two-entry determinant-one diagonal matrices `diag2n hij c hc`, joined to `1` along
  `t ↦ diag2n hij (exp ((t : ℝ) • log c)) _`.

Products of elements joined to `1` remain joined to `1` by pointwise multiplication of paths.

## Main results

* `Matrix.SpecialLinearGroup.instSubsingletonOfSubsingleton`: `SL(n, R)` is a subsingleton when `n`
  has at most one element.
* `Matrix.SpecialLinearGroup.instPathConnectedSpace`: `PathConnectedSpace (SpecialLinearGroup n ℂ)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Springer GTM 222,
  2015, Proposition 1.14.
-/

public section

noncomputable section

open scoped unitInterval
open Matrix Topology

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In size zero or one, the determinant-one condition forces every matrix in `SL(n, R)` to equal
`1`. -/
instance instSubsingletonOfSubsingleton {R : Type*} [CommRing R] [Subsingleton n] :
    Subsingleton (SpecialLinearGroup n R) :=
  ⟨fun A B => Subtype.ext <| by
    rcases isEmpty_or_nonempty n with hempty | ⟨⟨i₀⟩⟩
    · have := hempty
      exact Subsingleton.elim _ _
    · let : Unique n := uniqueOfSubsingleton i₀
      ext i j
      rw [Subsingleton.elim i default, Subsingleton.elim j default]
      have hA : (A : Matrix n n R) default default = 1 := by
        simpa [Matrix.det_unique] using A.2
      have hB : (B : Matrix n n R) default default = 1 := by
        simpa [Matrix.det_unique] using B.2
      rw [hA, hB]⟩

/-- Every elementary complex transvection is joined to `1` in `SL(n, ℂ)` by scaling its parameter
along `[0, 1]`. -/
private theorem joined_one_transvection {i j : n} (hij : i ≠ j) (a : ℂ) :
    Joined (1 : SpecialLinearGroup n ℂ) (transvection hij a) := by
  have hval : Continuous (Subtype.val : I → ℝ) := continuous_subtype_val
  have hcont : Continuous fun t : I =>
      (1 : Matrix n n ℂ) + single i j ((t : ℝ) • a) := by
    have hlin : (fun t : I => (1 : Matrix n n ℂ) + single i j ((t : ℝ) • a)) =
        fun t : I => (1 : Matrix n n ℂ) + ((t : ℝ) • a) • single i j (1 : ℂ) := by
      ext t p q
      simp [smul_single]
    rw [hlin]
    have ha : Continuous fun t : I => ((t : ℝ) • a : ℂ) := hval.smul continuous_const
    exact continuous_const.add (ha.smul continuous_const)
  refine ⟨{
    toFun := fun t => transvection hij ((t : ℝ) • a)
    continuous_toFun := (hcont.subtype_mk fun t => ?_).congr fun t =>
      Subtype.ext (transvection_coe hij ((t : ℝ) • a)).symm
    source' := Subtype.ext (by simp)
    target' := Subtype.ext (by simp) }⟩
  rw [← transvection_coe hij]
  exact (transvection hij ((t : ℝ) • a)).2

/-- Every two-entry determinant-one diagonal matrix `diag2n hij c hc` in `SL(n, ℂ)` is joined to
`1` along an exponential path through `Complex.log c`. -/
private theorem joined_one_diag2n {i j : n} (hij : i ≠ j) {c : ℂ} (hc : c ≠ 0) :
    Joined (1 : SpecialLinearGroup n ℂ) (diag2n hij c hc) := by
  let z : ℂ := Complex.log c
  have hval : Continuous (Subtype.val : I → ℝ) := continuous_subtype_val
  let M : I → Matrix n n ℂ := fun t => diagonal fun k =>
    if k = i then Complex.exp ((t : ℝ) • z)
    else if k = j then Complex.exp (-((t : ℝ) • z)) else 1
  have hM_eq : ∀ t : I, M t = (diag2n hij (Complex.exp ((t : ℝ) • z))
      (Complex.exp_ne_zero _) : Matrix n n ℂ) := fun t => by
    ext p q
    simp [M, diag2n_coe, Complex.exp_neg]
  have hcont : Continuous M := by
    refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
    by_cases hki : k = i
    · simp only [hki, ↓reduceIte]
      exact Complex.continuous_exp.comp (hval.smul continuous_const)
    · simp only [hki, ↓reduceIte]
      by_cases hkj : k = j
      · simp only [hkj, ↓reduceIte]
        exact Complex.continuous_exp.comp (hval.smul continuous_const).neg
      · simp only [hkj, ↓reduceIte]
        exact continuous_const
  refine ⟨{
    toFun := fun t => diag2n hij (Complex.exp ((t : ℝ) • z)) (Complex.exp_ne_zero _)
    continuous_toFun := (hcont.subtype_mk fun t => ?_).congr fun t => Subtype.ext (hM_eq t)
    source' := Subtype.ext <| by
      ext p q
      simp [diag2n_coe, Matrix.one_apply, Matrix.diagonal_apply]
    target' := Subtype.ext (by simp [z, diag2n_coe, Complex.exp_log hc]) }⟩
  rw [hM_eq t]
  exact (diag2n hij (Complex.exp ((t : ℝ) • z)) (Complex.exp_ne_zero _)).2

/-- **The complex special linear group is path connected**, including in sizes zero and one. -/
instance instPathConnectedSpace : PathConnectedSpace (SpecialLinearGroup n ℂ) := by
  rcases subsingleton_or_nontrivial n with hn | hn
  · exact PathConnectedSpace.mk ⟨1⟩ fun x y => Subsingleton.elim x y ▸ Joined.refl x
  · have h1 : ∀ M : SpecialLinearGroup n ℂ, Joined 1 M := fun M =>
      diagonal_transvection_induction' (Joined 1) M
        (fun _ _ hij _ hc => joined_one_diag2n hij hc)
        (fun _ _ hij a => joined_one_transvection hij a)
        (fun A B ⟨p⟩ ⟨q⟩ => ⟨{
          toFun := fun t => p t * q t
          continuous_toFun := p.continuous.mul q.continuous
          source' := by simp
          target' := by simp }⟩)
    exact PathConnectedSpace.mk ⟨1⟩ fun x y => (h1 x).symm.trans (h1 y)

end Matrix.SpecialLinearGroup
