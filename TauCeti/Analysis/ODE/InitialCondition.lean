/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.GlobalSolution
public import TauCeti.Analysis.ODE.SmoothParameter

/-!
# Smooth dependence of an ODE solution on its initial condition

Picard iteration produces a solution of `γ' = v ∘ γ` continuously, indeed Lipschitzly, in the
initial condition. It says nothing about differentiability: the contraction argument is metric.
This file upgrades continuity to smoothness of the same order as the field, jointly in the initial
condition and in time. The local argument first gives this near time `0`. The flow law then
propagates the result to every time, at every finite order: for a fixed initial condition, the set
of times where the solution is smooth is both open and closed.

The mechanism is a change of variables that turns the initial condition into a *parameter* of a
new equation, so that `ODE.exists_contDiffOn_picard_solution` applies. Writing a
solution through `x` as `t ↦ x + u (t / ε)`, the curve `u` solves

`u' s = ε • v (x + u s)`, `u 0 = 0`

on the fixed time interval `[0, 1]`, with `(x, ε)` a parameter and the initial state `0` fixed.
At `ε = 0` that field vanishes identically, which is exactly the degeneracy hypothesis of the
parameterized Picard theorem, and the solution at the base parameter is the constant curve `0`.
Evaluating the resulting smooth family of paths at the endpoint `s = 1` — a continuous linear
map on the path space — produces `x + u 1`, which `ODE_solution_unique` identifies with
the value of the global solution at time `ε`. Both the initial condition and the time are
therefore smooth directions.

## Main results

* `ODE.contDiffAt_globalSolution`: the global solution of a globally Lipschitz field that is
  locally `C^(n+1)` is jointly `C^(n+1)` near time `0`, for `n` finite or infinite.
* `ODE.contDiff_globalSolution`: the global solution is `C^(n+1)` jointly in its initial condition
  and time, for `n` finite or infinite.
* `ODE.contDiff_globalSolution_apply`: every time-`t` map is `C^(n+1)`.

The local smoothness theorem needs smoothness of the field only near the initial point.
It therefore also applies to globally Lipschitz extensions that are not smooth away from that
point. This is the input to local flows of locally smooth fields on Banach spaces.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

universe u

namespace ODE

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Time rescaling.** A curve solving the field `v` sped up by the factor `ε` on the unit
interval reaches, at time `1`, the value of the global solution at time `ε`. Only right
derivatives are required, which is the form in which the parameterized Picard theorem delivers
its solutions. -/
private theorem eq_globalSolution_of_smul [CompleteSpace E] (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (x : E) (ε : ℝ) {u : ℝ → E} (hu₀ : u 0 = x)
    (hu : ContinuousOn u (Icc 0 1))
    (hu' : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u (ε • v (u s)) (Ici s) s) :
    u 1 = globalSolution v hv x ε := by
  have hflow : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ globalSolution v hv x (ε * r))
      (ε • v (globalSolution v hv x (ε * s))) s := fun s ↦ by
    simpa [Function.comp_def, mul_comm] using
      (hasDerivAt_globalSolution v hv x (ε * s)).scomp s ((hasDerivAt_id s).const_mul ε)
  have heq := ODE_solution_unique (v := fun _ z ↦ ε • v z) (K := ‖ε‖₊ * K)
    (a := 0) (b := 1) (f := u) (g := fun r ↦ globalSolution v hv x (ε * r))
    (fun _ ↦ (lipschitzWith_smul ε).comp hv) hu hu'
    (((continuous_globalSolution_apply v hv x).comp
      (continuous_const.mul continuous_id)).continuousOn)
    (fun s _ ↦ (hflow s).hasDerivWithinAt)
    (by simp [hu₀])
  simpa using heq (right_mem_Icc.2 zero_le_one)

section

variable [CompleteSpace E]

/-- **The global solution of a globally Lipschitz field depends smoothly on time and on its
initial condition** near time `0`, provided the field is smooth near the initial point.
No smoothness of the field away from that neighbourhood is required. -/
theorem contDiffAt_globalSolution {n : ℕ∞} (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    {a : E} {s : Set E} (hvs : ContDiffOn ℝ (n + 1) v s) (hs : s ∈ nhds a) :
    ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) (a, 0) := by
  -- Keep every Picard path in the local smoothness domain of the field.
  let S : Set ((E × ℝ) × E) := (fun q ↦ q.1.1 + q.2) ⁻¹' interior s
  have hS : IsOpen S := isOpen_interior.preimage (by fun_prop)
  have hbase : ((a, (0 : ℝ)), (0 : E)) ∈ S := by
    simpa [S] using mem_interior_iff_mem_nhds.mpr hs
  have hf : ContDiffOn ℝ (n + 1)
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) S :=
    contDiff_fst.snd.contDiffOn.smul
      (hvs.comp (contDiff_fst.fst.add contDiff_snd).contDiffOn
        (fun _ hq ↦ interior_subset hq))
  have hzero : ∀ᶠ y in nhds (0 : E),
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) (((a, (0 : ℝ))), y) = 0 :=
    .of_forall fun y ↦ zero_smul ℝ _
  obtain ⟨γ, U, hU, hp₀U, hγU, -, hprop⟩ :=
    exists_contDiffOn_picard_solution
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) (a, (0 : ℝ)) (0 : E)
      hS hbase hf hzero
  have hγ : ContDiffAt ℝ (n + 1) γ (a, 0) := hγU.contDiffAt (hU.mem_nhds hp₀U)
  have hsmooth : ContDiffAt ℝ (n + 1)
      (fun p : E × ℝ ↦ p.1 + γ p ⟨1, by norm_num⟩) (a, 0) := by
    have := ((ContinuousMap.evalCLM (R := ℝ) (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)).contDiff
      (n := n + 1)).comp_contDiffAt (a, (0 : ℝ)) hγ
    exact contDiffAt_fst.add (by simpa [Function.comp_def] using this)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hp₀U] with p hpU
  have hp := (hprop p hpU).2
  obtain ⟨hpicard, -, hright⟩ := hp
  -- The rescaled solution starts at `p.1` and moves with speed `p.2 • v`.
  have hbase : γ p ⟨0, by norm_num⟩ = 0 := by simpa using hpicard ⟨0, by norm_num⟩
  have hcont : ContinuousOn (fun s : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one s)) (Icc 0 1) :=
    Continuous.continuousOn (by fun_prop)
  have hderiv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one r))
        (p.2 • v (p.1 + γ p (projIcc 0 1 zero_le_one s))) (Ici s) s :=
    fun s hs ↦ (hright s hs).const_add p.1
  have := eq_globalSolution_of_smul v hv p.1 p.2
    (u := fun s : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one s))
    (by simpa [projIcc_left] using congrArg (fun w : E ↦ p.1 + w) hbase) hcont hderiv
  simpa [projIcc_right] using this.symm

/-- The flow law propagates joint smoothness of the global solution from `(a, s)` and from
`(globalSolution v hv a s, t - s)` to `(a, t)`. -/
private theorem contDiffAt_globalSolution_of_contDiffAt_sub {n : ℕ} (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : E) {s t : ℝ}
    (hs : ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) (a, s))
    (hout : ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2)
      (globalSolution v hv a s, t - s)) :
    ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) (a, t) := by
  have hfixed : ContDiffAt ℝ (n + 1) (fun x ↦ globalSolution v hv x s) a :=
    hs.comp a (contDiffAt_id.prodMk contDiffAt_const)
  have hinner : ContDiffAt ℝ (n + 1)
      (fun p : E × ℝ ↦ (globalSolution v hv p.1 s, p.2 - s)) (a, t) :=
    (hfixed.comp (a, t) contDiffAt_fst).prodMk (contDiffAt_snd.sub contDiffAt_const)
  apply (hout.comp (a, t) hinner).congr_of_eventuallyEq
  filter_upwards [] with p
  dsimp only [Function.comp_apply]
  rw [← globalSolution_add]
  congr 2
  ring

/-- The finite-order case of `contDiff_globalSolution`: for a globally Lipschitz `C^(n+1)` vector
field `v` and natural `n`, the global solution is jointly `C^(n+1)` in the initial condition and
time. -/
private theorem contDiff_globalSolution_of_nat {n : ℕ} (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ (n + 1) v) :
    ContDiff ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) := by
  let G : E × ℝ → E := fun p ↦ globalSolution v hv p.1 p.2
  -- For a fixed initial condition, the times at which `G` is `C^(n+1)` form a nonempty clopen
  -- subset of `ℝ`; the flow law propagates smoothness locally, including at limit points.
  have hlocal (a : E) : ContDiffAt ℝ (n + 1) G (a, 0) := by
    exact_mod_cast contDiffAt_globalSolution (n := (n : ℕ∞)) v hv
      (by exact_mod_cast hvs.contDiffOn) (univ_mem : Set.univ ∈ nhds a)
  have hfinite : (n + 1 : ℕ∞) ≠ ∞ := by simp
  apply contDiff_iff_contDiffAt.2
  rintro ⟨a, t⟩
  let S : Set ℝ := {s | ContDiffAt ℝ (n + 1) G (a, s)}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have houter : ∀ᶠ u in nhds s,
        ContDiffAt ℝ (n + 1) G (globalSolution v hv a s, u - s) := by
      have hevent := (hlocal (globalSolution v hv a s)).eventually hfinite
      have htend : Tendsto (fun u : ℝ ↦ (globalSolution v hv a s, u - s)) (nhds s)
          (nhds (globalSolution v hv a s, 0)) := by
        have hconst : ContinuousAt (fun _ : ℝ ↦ globalSolution v hv a s) s := continuousAt_const
        have hsub : ContinuousAt (fun u : ℝ ↦ u - s) s :=
          continuousAt_id.sub continuousAt_const
        have htend' := hconst.prodMk hsub
        simpa only [ContinuousAt, sub_self] using htend'
      exact htend.eventually hevent
    exact houter.mono fun u hu ↦ contDiffAt_globalSolution_of_contDiffAt_sub v hv a hs hu
  have hclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro s hs
    have houter : ∀ᶠ u in nhds s,
        ContDiffAt ℝ (n + 1) G (globalSolution v hv a u, s - u) := by
      have hevent := (hlocal (globalSolution v hv a s)).eventually hfinite
      have htend : Tendsto (fun u ↦ (globalSolution v hv a u, s - u)) (nhds s)
          (nhds (globalSolution v hv a s, 0)) := by
        have hsub : ContinuousAt (fun u : ℝ ↦ s - u) s :=
          continuousAt_const.sub continuousAt_id
        have htend' := (continuous_globalSolution_apply v hv a).continuousAt.prodMk hsub
        simpa only [ContinuousAt, sub_self] using htend'
      exact htend.eventually hevent
    obtain ⟨u, hu⟩ := (mem_closure_iff_nhds').1 hs _ houter
    exact contDiffAt_globalSolution_of_contDiffAt_sub v hv a u.property hu
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, hlocal a⟩
  have ht : t ∈ S := by
    rw [hSuniv]
    exact Set.mem_univ t
  exact ht

/-- **The global solution of a globally Lipschitz `C^(n+1)` field is `C^(n+1)` jointly in its
initial condition and time.**

For every positive regularity order, finite or infinite, the global solution has the same joint
regularity as the vector field. -/
theorem contDiff_globalSolution {n : ℕ∞} (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) :
    ContDiff ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) := by
  -- It suffices to treat finite orders: a `C^∞` field is `C^(k+1)` for every `k`.
  suffices H : ∀ n : ℕ, ContDiff ℝ (n + 1) v →
      ContDiff ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) by
    induction n using ENat.recTopCoe with
    | top =>
      have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ∞ := by
        rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
      rw [htop] at hvs ⊢
      exact contDiff_infty.2 fun k ↦ (H k (hvs.of_le (by exact_mod_cast le_top))).of_le
        (by exact_mod_cast le_self_add)
    | coe k => exact_mod_cast H k (by exact_mod_cast hvs)
  exact fun _ ↦ contDiff_globalSolution_of_nat v hv

/-- At every fixed time, the global solution of a globally Lipschitz `C^(n+1)` field is a
`C^(n+1)` function of its initial condition. -/
theorem contDiff_globalSolution_apply {n : ℕ∞} (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (t : ℝ) :
    ContDiff ℝ (n + 1) fun x ↦ globalSolution v hv x t :=
  (contDiff_globalSolution v hv hvs).comp (contDiff_id.prodMk contDiff_const)

end

end ODE

end
