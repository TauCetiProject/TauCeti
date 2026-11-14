/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Derivative

/-!
# Differentiation of Nash germs

Every scalar directional derivative of a Nash germ is again a Nash germ. In particular
all coordinate partial derivatives are Nash, including on the singular locus of any
chosen polynomial relation for the original function. The derivative is the native
Fréchet derivative evaluated at a fixed vector.

Analyticity follows from analyticity of the Fréchet derivative. Semialgebraicity of
its graph follows from the difference-quotient limit formula, without choosing a
polynomial relation or excluding its discriminant locus. The local Nash graph
criterion then gives a polynomial relation for the derivative on a full neighborhood.

Iterating, every iterated derivative of a Nash germ evaluated at fixed directions is again a
Nash germ (`TauCeti.IsNashAt.iteratedFDeriv_apply`), as are scalar iterated derivatives along
lines (`TauCeti.IsNashAt.iteratedDeriv_add_smul`) and in a distinguished coordinate
(`TauCeti.IsNashAt.iteratedDeriv_sumElim`). This lets one describe the order of vanishing of a
Nash germ, for instance the multiplicity of a root along a line, through its successive
derivatives.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 8.1 (Nash functions).
-/

public section

open Filter Metric Set Topology

namespace TauCeti

/-- Differentiation in any fixed direction preserves Nash germs. This applies at every
point of the germ, not just where a chosen algebraic relation has a simple root. -/
theorem IsNashAt.fderiv_apply {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (v : σ → ℝ) : IsNashAt (fun y ↦ fderiv ℝ f y v) x := by
  obtain ⟨_, U, hUo, hxU, _, hG⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hf
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hUo.mem_nhds hxU) hf.analyticAt.eventually_analyticAt)
  have hsemi := isSemialgebraic_ball x r
  have hgraph := hG.mono hsemi (fun y hy ↦ (hB hy).1)
  refine isNashAt_iff_exists_isSemialgebraicOn.mpr ⟨?_, ball x r, isOpen_ball,
    mem_ball_self hr, hsemi, hgraph.fderiv_apply isOpen_ball ?_ v⟩
  · exact ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hf.analyticAt.fderiv
  · exact fun y hy ↦ (hB hy).2.differentiableWithinAt

/-- The `n`-th derivative of a Nash germ, evaluated at fixed directions `m`, is a Nash germ. -/
theorem IsNashAt.iteratedFDeriv_apply {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (n : ℕ) (m : Fin n → σ → ℝ) :
    IsNashAt (fun y ↦ iteratedFDeriv ℝ n f y m) x := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    refine ((ih (Fin.tail m)).fderiv_apply (m 0)).congr ?_
    filter_upwards [hf.analyticAt.eventually_analyticAt] with y hy
    obtain ⟨U, hU, hfU⟩ := hy.exists_mem_nhds_analyticOnNhd
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
      ((hfU.iteratedFDeriv n) y (mem_of_mem_nhds hU)).differentiableAt
    rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply hd]

/-- For any direction `v`, the `n`-th scalar iterated derivative of a Nash germ along the line
`t ↦ y + t • v` at `t = 0` is again a Nash germ. -/
theorem IsNashAt.iteratedDeriv_add_smul {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (v : σ → ℝ) (n : ℕ) :
    IsNashAt (fun y ↦ iteratedDeriv n (fun t : ℝ ↦ f (y + t • v)) 0) x := by
  induction n generalizing f with
  | zero => simpa using hf
  | succ n ih =>
    refine (ih (hf.fderiv_apply v)).congr ?_
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hf.analyticAt.eventually_analyticAt
    filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
    have hderiv : deriv (fun t : ℝ ↦ f (y + t • v)) =ᶠ[𝓝 0]
        fun t : ℝ ↦ fderiv ℝ f (y + t • v) v := by
      have hmem : {t : ℝ | y + t • v ∈ ball x r} ∈ 𝓝 0 := by
        have hcont : Continuous (fun t : ℝ ↦ y + t • v) := by fun_prop
        refine (hcont.tendsto 0).eventually (isOpen_ball.mem_nhds ?_)
        simpa using (mem_ball.1 hy).trans (half_lt_self hr)
      filter_upwards [hmem] with t ht
      have hd : HasDerivAt (fun s : ℝ ↦ y + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add y
      exact ((hball ht).differentiableAt.hasFDerivAt.comp_hasDerivAt t hd).deriv
    rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq n]

/-- For a Nash germ `f` on `σ ⊕ Unit → ℝ`, the `n`-th iterated derivative in the last variable
`y ↦ iteratedDeriv n (fun t ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ t))) (y (Sum.inr ()))` is again
a Nash germ. -/
theorem IsNashAt.iteratedDeriv_sumElim {σ : Type*} [Fintype σ] {f : (σ ⊕ Unit → ℝ) → ℝ}
    {x : σ ⊕ Unit → ℝ} (hf : IsNashAt f x) (n : ℕ) :
    IsNashAt (fun y ↦
      iteratedDeriv n (fun t ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ t))) (y (Sum.inr ()))) x := by
  refine (hf.iteratedDeriv_add_smul (Sum.elim 0 (fun _ ↦ 1)) n).congr (.of_forall fun y ↦ ?_)
  have hline (s : ℝ) :
      y + s • Sum.elim (0 : σ → ℝ) (fun _ : Unit ↦ (1 : ℝ)) =
        Sum.elim (y ∘ Sum.inl) (fun _ ↦ s + y (Sum.inr ())) := by
    ext (i | _) <;> simp [add_comm]
  simp_rw [hline]
  simpa using congrFun (iteratedDeriv_comp_add_const (n := n)
    (f := fun t ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ t))) (s := y (Sum.inr ()))) 0

end TauCeti
