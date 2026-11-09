/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.HittingTime

/-!
# Transitions between transverse sections and conjugacy of return germs

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold. A local transverse
section through a point `q` is a level of a function `g`, `C¹` at `q`, with `dg_q (v q) ≠ 0`. If the
flow carries `p` to `q` at time `T`, the transition `TauCeti.flowTransition v g T p` flows each
point near `p` for its hitting time `TauCeti.flowHittingTime v g T p` into the section through `q`.

This file proves that these germs compose as the flow does. Hitting times add along a trajectory
(`TauCeti.flowHittingTime_add_flowHittingTime_eventuallyEq`): flowing from near `p` to the section
through `q` and then on to a section through `r = flowOf v T' q` is the transition from `p` to the
section through `r` at time `T + T'` (`TauCeti.flowTransition_comp_eventuallyEq`). The time-`0`
transition to the section through `p` is the identity on that section
(`TauCeti.eventually_flowTransition_zero`), so the transition from the section through `p` to the
section through `q` is invertible on these sections, with inverse the reverse transition at time
`-T` (`TauCeti.eventually_flowTransition_neg_flowTransition`,
`TauCeti.eventually_flowTransition_flowTransition_neg`). A transition is also constant along the
trajectory through its base point (`TauCeti.eventually_flowTransition_flowOf`).

If moreover `p` returns to itself at time `T₀`, then `flowTransition v g T₀ p` is a local return
branch of the section through `p`, and likewise at `q`. The transition `h` from the section through
`p` to that through `q` conjugates these return germs: `h ∘ P_p = P_q ∘ h` near `p`
(`TauCeti.flowTransition_semiconj_eventuallyEq`), so `P_q = h ∘ P_p ∘ h⁻¹` on the section through
`q` (`TauCeti.eventually_flowTransition_eq_conj`). The `k`-fold iterate of the return branch at
time `T₀` is the return branch at time `k * T₀` (`TauCeti.flowTransition_iterate_eventuallyEq`), and
`h` conjugates every iterate (`TauCeti.flowTransition_comp_iterate_eventuallyEq`). Hence
the return germs of a periodic orbit at different sections and base points are locally conjugate,
which makes their fixed-point and derivative data independent of these choices.

None of these statements assumes that `T₀` is the least period or that the return branch is the
first return to the section.

## Main results

* `TauCeti.flowHittingTime_add_flowHittingTime_eventuallyEq`: hitting times add.
* `TauCeti.flowTransition_comp_eventuallyEq`: transitions compose.
* `TauCeti.eventually_flowTransition_flowOf`: a transition is constant along the trajectory
  through its base point.
* `TauCeti.eventually_flowTransition_neg_flowTransition`,
  `TauCeti.eventually_flowTransition_flowTransition_neg`: the reverse transition is the inverse of
  the transition between two sections.
* `TauCeti.flowTransition_semiconj_eventuallyEq`, `TauCeti.eventually_flowTransition_eq_conj`:
  transitions conjugate return germs.
* `TauCeti.flowTransition_iterate_eventuallyEq`,
  `TauCeti.flowTransition_comp_iterate_eventuallyEq`: iterates of return germs.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §1
  (the Poincaré maps of a closed orbit at different sections are conjugate).
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g g' : M → ℝ} {T T' T₀ : ℝ} {p q r : M}

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
include hv

section Composition

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hg : ContMDiffAt I 𝓘(ℝ) 1 g q)
  (hgv : mvfderiv I g q (v q) ≠ 0) (hT' : (T', q) ∈ flowDomain v) (hr : flowOf v T' q = r)
  (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' r) (hg'v : mvfderiv I g' r (v r) ≠ 0)
include hT hq hg hgv hT' hr hg' hg'v

/-- **Hitting times add along a trajectory.** If the flow carries `p` to `q` at time `T` and `q` to
`r` at time `T'`, then for `z` near `p`, the hitting time of a section through `q` plus the
hitting time from there of a section through `r` is the hitting time of the section through `r`
at time `T + T'`. -/
theorem flowHittingTime_add_flowHittingTime_eventuallyEq :
    (fun z ↦ flowHittingTime v g T p z + flowHittingTime v g' T' q (flowTransition v g T p z))
      =ᶠ[𝓝 p] flowHittingTime v g' (T + T') p := by
  subst hq hr
  obtain ⟨hTT', hflow⟩ := flowOf_add hv hT hT'
  have hh := continuousAt_flowTransition hv hT hg hgv
  have hcont : ContinuousAt
      (fun z ↦ flowHittingTime v g T p z +
        flowHittingTime v g' T' (flowOf v T p) (flowTransition v g T p z)) p :=
    (continuousAt_flowHittingTime hv hT hg hgv).add
      ((continuousAt_flowHittingTime hv hT' hg' hg'v).comp_of_eq hh (flowTransition_self ..))
  have hh' : Tendsto (flowTransition v g T p) (𝓝 p) (𝓝 (flowOf v T p)) := by
    simpa only [flowTransition_self] using hh.tendsto
  refine eventuallyEq_flowHittingTime hv hTT' (hflow ▸ hg') (hflow ▸ hg'v) hcont
    (by simp) ?_
  filter_upwards [eventually_flowHittingTime hv hT hg hgv,
    hh'.eventually (eventually_flowHittingTime hv hT' hg' hg'v)] with z hz hz'
  rw [flowTransition_apply] at hz' ⊢
  rw [← (flowOf_add hv hz.1 hz'.1).2, hz'.2, hflow]

/-- **Transitions compose.** If the flow carries `p` to `q` at time `T` and `q` to `r` at time
`T'`, then the transition from near `p` to a section through `q`, followed by the transition from
near `q` to a section through `r`, is near `p` the transition to the section through `r` at time
`T + T'`. -/
theorem flowTransition_comp_eventuallyEq :
    flowTransition v g' T' q ∘ flowTransition v g T p =ᶠ[𝓝 p] flowTransition v g' (T + T') p := by
  have hh' := (continuousAt_flowTransition hv hT (by rwa [hq]) (by rwa [hq])).tendsto
  rw [flowTransition_self, hq] at hh'
  filter_upwards [flowHittingTime_add_flowHittingTime_eventuallyEq hv hT hq hg hgv hT' hr hg' hg'v,
    eventually_flowHittingTime hv hT (by rwa [hq]) (by rwa [hq]),
    hh'.eventually (eventually_flowHittingTime hv hT' (by rwa [hr]) (by rwa [hr]))]
    with z hadd hz hz'
  rw [comp_apply, flowTransition_apply v g' T' q, flowTransition_apply v g' (T + T') p, ← hadd]
  rw [flowTransition_apply v g T p] at hz' ⊢
  exact (flowOf_add hv hz.1 hz'.1).2

end Composition

/-- **The time-`0` transition fixes its section.** For a section through `p` transverse to `v`,
the transition at time `0` to this section is the identity on the section near `p`. -/
theorem eventually_flowTransition_zero (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (v p) ≠ 0) :
    ∀ᶠ z in 𝓝 p, g z = g p → flowTransition v g 0 p z = z := by
  have h0 := flowOf_zero hv p
  have hpair : Tendsto (fun z : M ↦ ((0 : ℝ), z)) (𝓝 p) (𝓝 (0, p)) :=
    (continuous_const.prodMk continuous_id).tendsto p
  filter_upwards [hpair.eventually (eventually_eq_flowHittingTime_iff hv (mem_flowDomain_zero hv p)
    (by rwa [h0]) (by rwa [h0]))] with z hz hzg
  have htime : 0 = flowHittingTime v g 0 p z := hz.1 (by rw [flowOf_zero hv, h0, hzg])
  rw [flowTransition_apply, ← htime, flowOf_zero hv]

/-- **A transition is constant along the trajectory through `p`.** For `s` near `0`, the point
`flowOf v s p` is carried to `flowOf v T p`, its hitting time being `T - s`. -/
theorem eventually_flowTransition_flowOf (hT : (T, p) ∈ flowDomain v)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
    (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), flowTransition v g T p (flowOf v s p) = flowOf v T p := by
  have hγ : Tendsto (fun s ↦ flowOf v s p) (𝓝 0) (𝓝 p) := by
    simpa only [flowOf_zero hv p] using
      (mdifferentiableAt_flowOf hv (mem_flowDomain_zero hv p)).continuousAt.tendsto
  have hsub : Tendsto (fun s : ℝ ↦ T - s) (𝓝 0) (𝓝 T) := by
    simpa only [sub_zero, id_eq] using
      (tendsto_const_nhds (x := T)).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
  have hpair : Tendsto (fun s ↦ (T - s, flowOf v s p)) (𝓝 0) (𝓝 (T, p)) := hsub.prodMk_nhds hγ
  have hzero : Tendsto (fun s : ℝ ↦ (s, p)) (𝓝 0) (𝓝 (0, p)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [hpair.eventually ((isOpen_flowDomain hv).mem_nhds hT),
    hzero.eventually ((isOpen_flowDomain hv).mem_nhds (mem_flowDomain_zero hv p)),
    hpair.eventually (eventually_eq_flowHittingTime_iff hv hT hg hgv)] with s hsT hs hiff
  have hflow : flowOf v (T - s) (flowOf v s p) = flowOf v T p := by
    rw [(flowOf_add hv hs hsT).2, add_sub_cancel]
  rw [flowTransition_apply, ← hiff.1 (by rw [hflow]), hflow]

section Inverse

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0) (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q)
  (hg'v : mvfderiv I g' q (v q) ≠ 0)
include hT hq hg hgv hg' hg'v

/-- **The reverse transition is a left inverse.** If the flow carries `p` to `q` at time `T`, the
transition from the section through `p` to a section through `q`, followed by the reverse
transition at time `-T` back to the section through `p`, is the identity on the section through
`p` near `p`. -/
theorem eventually_flowTransition_neg_flowTransition :
    ∀ᶠ z in 𝓝 p, g z = g p → flowTransition v g (-T) q (flowTransition v g' T p z) = z := by
  subst hq
  have hneg := neg_mem_flowDomain_flowOf hv hT
  have hback := flowOf_neg_flowOf hv hT
  have hcomp := flowTransition_comp_eventuallyEq hv hT rfl hg' hg'v hneg hback hg hgv
  rw [add_neg_cancel] at hcomp
  filter_upwards [hcomp, eventually_flowTransition_zero hv hg hgv] with z hz hz0 hzg
  exact hz.trans (hz0 hzg)

/-- **The reverse transition is a right inverse.** If the flow carries `p` to `q` at time `T`, the
reverse transition at time `-T` from the section through `q` to a section through `p`, followed by
the transition back to the section through `q`, is the identity on the section through `q`
near `q`. -/
theorem eventually_flowTransition_flowTransition_neg :
    ∀ᶠ w in 𝓝 q, g' w = g' q → flowTransition v g' T p (flowTransition v g (-T) q w) = w := by
  subst hq
  have hneg := neg_mem_flowDomain_flowOf hv hT
  have hback := flowOf_neg_flowOf hv hT
  simpa only [neg_neg] using
    eventually_flowTransition_neg_flowTransition hv hneg hback hg' hg'v hg hgv

end Inverse

section Return

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hP : (T₀, p) ∈ flowDomain v)
  (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0)
  (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0)

include hP hp hg hgv in
/-- **Iterates of a return germ.** If `p` returns to itself at time `T₀`, then for `k ≠ 0` the
`k`-fold iterate of the return branch at time `T₀` of a section through `p` is near `p` the return
branch at time `k * T₀`. -/
theorem flowTransition_iterate_eventuallyEq {k : ℕ} (hk : k ≠ 0) :
    (flowTransition v g T₀ p)^[k] =ᶠ[𝓝 p] flowTransition v g (k * T₀) p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  clear hk
  induction k with
  | zero =>
    simp only [zero_add, iterate_one, Nat.cast_one, one_mul]
    rfl
  | succ k ih =>
    obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp (k + 1)
    have hmul : ((k + 1 + 1 : ℕ) : ℝ) * T₀ = ((k + 1 : ℕ) : ℝ) * T₀ + T₀ := by
      push_cast
      ring
    rw [iterate_succ', hmul]
    exact (ih.fun_comp _).trans <|
      flowTransition_comp_eventuallyEq hv hkP hkp hg hgv hP hp hg hgv

include hT hq hP hp hg hgv hg' hg'v

/-- **Transitions conjugate return germs.** If the flow carries `p` to `q` at time `T` and `p`
returns to itself at time `T₀`, then the transition `h` from a section through `p` to a section
through `q` intertwines the return branches `P_p` and `P_q` at time `T₀` of these sections:
`h ∘ P_p = P_q ∘ h` near `p`. -/
theorem flowTransition_semiconj_eventuallyEq :
    flowTransition v g' T p ∘ flowTransition v g T₀ p =ᶠ[𝓝 p]
      flowTransition v g' T₀ q ∘ flowTransition v g' T p := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  refine (flowTransition_comp_eventuallyEq hv hP hp hg hgv hT hq hg' hg'v).trans ?_
  rw [add_comm]
  exact (flowTransition_comp_eventuallyEq hv hT hq hg' hg'v hQ hq' hg' hg'v).symm

/-- **Return germs at different sections are conjugate.** If the flow carries `p` to `q` at time
`T` and `p` returns to itself at time `T₀`, then on the section through `q` near `q`, the return
branch `P_q` at time `T₀` is `h ∘ P_p ∘ h⁻¹`, where `h` is the transition from the section through
`p` to that through `q`, `h⁻¹` is the reverse transition and `P_p` is the return branch of the
section through `p`. -/
theorem eventually_flowTransition_eq_conj :
    ∀ᶠ w in 𝓝 q, g' w = g' q → flowTransition v g' T₀ q w =
      flowTransition v g' T p (flowTransition v g T₀ p (flowTransition v g (-T) q w)) := by
  have hback : flowOf v (-T) q = p := hq ▸ flowOf_neg_flowOf hv hT
  have hk := (continuousAt_flowTransition hv (hq ▸ neg_mem_flowDomain_flowOf hv hT)
    (by rwa [hback]) (by rwa [hback])).tendsto
  rw [flowTransition_self, hback] at hk
  filter_upwards [eventually_flowTransition_flowTransition_neg hv hT hq hg hgv hg' hg'v,
    hk.eventually (flowTransition_semiconj_eventuallyEq hv hT hq hP hp hg hgv hg' hg'v)]
    with w hw hconj hwg
  rw [← comp_apply (f := flowTransition v g' T p), hconj, comp_apply, hw hwg]

/-- **Transitions conjugate the iterates of return germs.** If the flow carries `p` to `q` at time
`T` and `p` returns to itself at time `T₀`, then for every `k` the transition `h` from a section
through `p` to a section through `q` satisfies `h ∘ P_p^[k] = P_q^[k] ∘ h` near `p`, where `P_p`
and `P_q` are the return branches at time `T₀` of these sections. -/
theorem flowTransition_comp_iterate_eventuallyEq (k : ℕ) :
    flowTransition v g' T p ∘ (flowTransition v g T₀ p)^[k] =ᶠ[𝓝 p]
      (flowTransition v g' T₀ q)^[k] ∘ flowTransition v g' T p := by
  rcases eq_or_ne k 0 with rfl | hk
  · rfl
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
  have hh := (continuousAt_flowTransition hv hT (by rwa [hq]) (by rwa [hq])).tendsto
  rw [flowTransition_self, hq] at hh
  exact ((flowTransition_iterate_eventuallyEq hv hP hp hg hgv hk).fun_comp _).trans <|
    (flowTransition_semiconj_eventuallyEq hv hT hq hkP hkp hg hgv hg' hg'v).trans <|
      ((flowTransition_iterate_eventuallyEq hv hQ hq' hg' hg'v hk).comp_tendsto hh).symm

end Return

end TauCeti
