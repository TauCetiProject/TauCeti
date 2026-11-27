/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.Shallow.Basic
public import TauCeti.Topology.ContinuousMap.CompactConvergence.Dense
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import TauCeti.Algebra.Polynomial.Eval.OnSet

/-!
# The obstruction from polynomial activations

If the activation is polynomial of degree at most `d`, then every network restricts to a
polynomial of degree at most `d` along each line, regardless of the width. On a unit segment the
monomial `t ↦ t^(d+1)` stays a positive uniform distance from all such polynomials, giving the
necessity of nonpolynomial activations for universal approximation in a nontrivial space.

See Allan Pinkus, *Approximation theory of the MLP model in neural networks*, Acta Numerica 8
(1999), the necessity argument after Theorem 3.1.
-/

public section

open Polynomial Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- With a polynomial activation of degree at most `d`, the restriction of any network along
`t ↦ t • v` is a polynomial of degree at most `d`. -/
theorem ShallowNet.exists_polynomial_eval_smul {m d : ℕ} (N : ShallowNet E m)
    {p : ℝ[X]} (hp : p.natDegree ≤ d) (v : E) :
    ∃ q : ℝ[X], q.natDegree ≤ d ∧ ∀ t : ℝ, N.eval (fun u => p.eval u) (t • v) = q.eval t := by
  let a i := C ⟪N.weight i, v⟫ * X + C (N.bias i)
  let q i := C (N.coeff i) * p.comp (a i)
  refine ⟨(∑ i, q i) + C N.outBias, ?_, fun t => ?_⟩
  · rw [natDegree_add_C]
    refine natDegree_sum_le_of_forall_le _ q fun i _ => ?_
    have ha : (a i).natDegree ≤ 1 := by
      simpa [a] using natDegree_C_mul_X_pow_le ⟪N.weight i, v⟫ 1
    calc
      (q i).natDegree ≤ (p.comp (a i)).natDegree := natDegree_C_mul_le _ _
      _ ≤ p.natDegree * (a i).natDegree := natDegree_comp_le
      _ ≤ d := by simpa using Nat.mul_le_mul hp ha
  · simp only [ShallowNet.eval_apply, q, a, eval_add, eval_finsetSum, eval_C, eval_mul, eval_comp,
      eval_X, real_inner_smul_right, mul_comm t]

/-- The monomial of degree `d + 1` has a positive uniform gap from the restrictions to the
unit interval of networks using a polynomial activation of degree at most `d`. -/
theorem exists_pos_forall_exists_le_abs_sub_shallowNetFunctions_smul {p : ℝ[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (v : E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ shallowNetFunctions (fun u => p.eval u) E,
      ∃ t ∈ Icc (0 : ℝ) 1, ε ≤ |t ^ (d + 1) - g (t • v)| := by
  let I := Icc (0 : ℝ) 1
  let S := (degreeLT ℝ (d + 1)).map (toContinuousMapOnAlgHom I).toLinearMap
  let f := ((X : ℝ[X]) ^ (d + 1)).toContinuousMapOn I
  have hS : IsClosed (S : Set C(I, ℝ)) := Submodule.isClosed_of_finiteDimensional S
  have hf : f ∉ S := by
    rintro ⟨q, hq, hqf⟩
    have hI : I.Infinite := Icc_infinite (by norm_num)
    have heq : q = (X : ℝ[X]) ^ (d + 1) := by
      apply evalOn_injective hI
      funext t
      simpa [f] using congrFun (congrArg DFunLike.coe hqf) t
    simp [heq, mem_degreeLT] at hq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl f hf
  refine ⟨ε, hε, fun g hg => ?_⟩
  obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hg
  obtain ⟨q, hq, heval⟩ := N.exists_polynomial_eval_smul hp v
  have hqS : q.toContinuousMapOn I ∈ S := by
    refine ⟨q, mem_degreeLT.mpr (q.degree_le_natDegree.trans_lt ?_), rfl⟩
    exact_mod_cast Nat.lt_succ_of_le hq
  by_contra! h
  have hdist : dist (q.toContinuousMapOn I) f < ε :=
    (ContinuousMap.dist_lt_iff hε).mpr fun t => by
      have ht := h t t.property
      rw [heval] at ht
      simpa [f, Real.dist_eq, abs_sub_comm] using ht
  exact hball hdist hqS

/-- A polynomial activation cannot give uniform approximation on all compact sets of a
nontrivial real inner product space. -/
theorem not_denseOnCompacts_shallowNetFunctions_of_polynomial [Nontrivial E] {σ : ℝ → ℝ}
    {p : ℝ[X]} (hσ : ∀ t, σ t = p.eval t) : ¬ DenseOnCompacts (shallowNetFunctions σ E) := by
  have hσ' : σ = fun t => p.eval t := _root_.funext hσ
  subst σ
  intro hdense
  obtain ⟨v, hv⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℝ) (E := E) (r := 1) zero_le_one
  have hv₁ : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  obtain ⟨ε, hε, hgap⟩ :=
    exists_pos_forall_exists_le_abs_sub_shallowNetFunctions_smul (le_refl p.natDegree) v
  have hline : Continuous (fun t : ℝ => t • v) := by fun_prop
  have hf : Continuous (fun x : E => ⟪v, x⟫ ^ (p.natDegree + 1)) := by fun_prop
  obtain ⟨g, hg, hdist⟩ := denseOnCompacts_iff.mp hdense
    (isCompact_Icc.image hline) hf.continuousOn hε
  obtain ⟨t, ht, hle⟩ := hgap g hg
  have hlt := hdist (t • v) (mem_image_of_mem _ ht)
  simp only [Real.dist_eq, real_inner_smul_right, real_inner_self_eq_norm_sq, hv₁, one_pow,
    mul_one] at hlt
  exact hle.not_gt hlt

/-- On a trivial input space the output bias suffices for approximation, for every activation. -/
theorem denseOnCompacts_shallowNetFunctions_of_subsingleton [Subsingleton E] (σ : ℝ → ℝ) :
    DenseOnCompacts (shallowNetFunctions σ E) := by
  refine denseOnCompacts_iff.mpr fun K _ f _ ε hε =>
    ⟨Function.const E (f 0), const_mem_shallowNetFunctions (f 0), fun x _ => ?_⟩
  simpa [Subsingleton.elim x 0] using hε

end TauCeti
