/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Transition
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import TauCeti.LinearAlgebra.Charpoly.Comp

/-!
# Derivatives of return germs

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold, and let `p` be a point
returning to itself at time `T₀`. For a function `g` with `dg_p (v p) ≠ 0`, whose level through `p`
is a local section transverse to `v`, the return branch `P_p = TauCeti.flowTransition v g T₀ p`
flows every point near `p` back into that section. This file studies its derivative
`DP_p : T_p M → T_p M` at `p`.

The derivative of a transition kills the field (`TauCeti.mfderiv_flowTransition_apply_eq_zero`),
since a transition is constant along flow lines, and lands in the kernel of the derivative of the
function cutting out the target section (`TauCeti.mvfderiv_comp_mfderiv_flowTransition`). For a
return branch, `DP_p` is therefore zero on the line spanned by `v p` and maps the tangent space
`ker dg_p` of the section into itself; there it is the derivative of the return map of the section,
the normal return derivative. As `T_p M = ker dg_p ⊕ ℝ v p`, the characteristic polynomial of
`DP_p` is `X` times that of the normal return derivative, so the two have the same nonzero
eigenvalues, and `1` is an eigenvalue of one exactly when it is an eigenvalue of the other.

Derivatives of transitions compose as the transitions do (`TauCeti.mfderiv_flowTransition_comp`).
If the flow carries `p` to `q` at time `T`, the transition `h` from the section through `p` to a
section through `q` therefore intertwines the derivatives of the return branches,
`Dh ∘ DP_p = DP_q ∘ Dh` (`TauCeti.mfderiv_flowTransition_semiconj`). The derivative
`Dh` is not invertible, as it kills `v p`, so this does not by itself conjugate `DP_p` to `DP_q`.
The reverse transition `h'` repairs this: `Dh' ∘ Dh` and `Dh ∘ Dh'` are the derivatives of the
time-`0` transitions onto the two sections, which `DP_p` and `DP_q` absorb. Hence
`DP_p = Dh' ∘ (DP_q ∘ Dh)` and `DP_q = (DP_q ∘ Dh) ∘ Dh'`, so the two derivatives have the same
characteristic polynomial (`TauCeti.charpoly_mfderiv_flowTransition_eq`), by
`LinearMap.charpoly_comp_comm`. This is the linear content of the conjugacy
`P_q = h ∘ P_p ∘ h⁻¹` of `TauCeti.eventually_flowTransition_eq_conj`: the spectrum of the return
derivative, and in particular the test whether `1` is an eigenvalue
(`TauCeti.hasEigenvalue_mfderiv_flowTransition_iff`), depend neither on the section nor on the
base point on the orbit. Since the `k`-fold iterate of a return branch is the return branch at time
`k * T₀`, the same holds for every iterate (`TauCeti.charpoly_mfderiv_iterate_flowTransition_eq`).

As in `TauCeti.Geometry.Manifold.Flow.Transition`, `T₀` need not be the least period, and the
return branch need not be the first return to the section.

## Main results

* `TauCeti.mfderiv_flowTransition_apply_eq_zero`: the derivative of a transition kills the field.
* `TauCeti.mvfderiv_comp_mfderiv_flowTransition`: the derivative of a transition lands in the
  tangent space of the target section.
* `TauCeti.mfderiv_flowTransition_comp`: derivatives of transitions compose.
* `TauCeti.mfderiv_flowTransition_semiconj`: transitions intertwine the derivatives of
  return germs.
* `TauCeti.charpoly_mfderiv_flowTransition_eq`: the characteristic polynomial of the derivative of
  a return germ is independent of the section and the base point.
* `TauCeti.hasEigenvalue_mfderiv_flowTransition_iff`: so are its eigenvalues.
* `TauCeti.charpoly_mfderiv_iterate_flowTransition_eq`: the same for every iterate.

## References

* G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, AMS Graduate Studies in
  Mathematics 140, 2012, §12.2 (the Poincaré map and its derivative; Theorem 12.4).
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

section Transition

variable (hT : (T, p) ∈ flowDomain v) (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hT hg hgv

/-- A transition is constant along the trajectory through `p`: for `s` near `0`, the point
`flowOf v s p` is carried to `flowOf v T p`, its hitting time being `T - s`. -/
theorem eventually_flowTransition_flowOf :
    ∀ᶠ s in 𝓝 (0 : ℝ), flowTransition v g T p (flowOf v s p) = flowOf v T p := by
  have hγ : Tendsto (fun s ↦ flowOf v s p) (𝓝 0) (𝓝 p) := by
    simpa only [id_eq, flowOf_zero hv p] using
      (contMDiffAt_flowOf_comp le_rfl hv (contMDiffAt_id (x := (0 : ℝ))) contMDiffAt_const
        (mem_flowDomain_zero hv p)).continuousAt.tendsto
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

/-- **The derivative of a transition kills the field.** The transition to a section through
`flowOf v T p` is constant along the trajectory through `p`, so its derivative at `p` vanishes on
the field `v p`. -/
theorem mfderiv_flowTransition_apply_eq_zero :
    mfderiv I I (flowTransition v g T p) p (v p) = 0 := by
  have hγ : MDifferentiableAt 𝓘(ℝ) I (fun s ↦ flowOf v s p) 0 :=
    (contMDiffAt_flowOf_comp le_rfl hv (contMDiffAt_id (x := (0 : ℝ))) contMDiffAt_const
      (mem_flowDomain_zero hv p)).mdifferentiableAt one_ne_zero
  have hh : MDifferentiableAt I I (flowTransition v g T p) p :=
    (contMDiffAt_flowTransition le_rfl hv hT hg hgv).mdifferentiableAt one_ne_zero
  have hconst : flowTransition v g T p ∘ (fun s ↦ flowOf v s p) =ᶠ[𝓝 0]
      fun _ ↦ flowOf v T p :=
    eventually_flowTransition_flowOf hv hT hg hgv
  -- The tangent spaces at `x` and at `p` are both the model space, so this equation is well
  -- typed; it holds by substituting `x = p`.
  have hvp : ∀ x, x = p → v x = v p := by
    rintro x rfl
    rfl
  -- The velocity of the trajectory at time `0` is `v p`.
  have hvel : mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s p) 0 (1 : ℝ) = v p :=
    Manifold.curveVelocity_apply.symm.trans <|
      (curveVelocity_flowOf hv (mem_flowDomain_zero hv p)).trans (hvp _ (flowOf_zero hv p))
  have hzero : mfderiv 𝓘(ℝ) I (flowTransition v g T p ∘ fun s ↦ flowOf v s p) 0 (1 : ℝ) = 0 := by
    rw [hconst.mfderiv_eq, mfderiv_const]
    rfl
  exact ((congrArg (mfderiv I I (flowTransition v g T p) p) hvel).symm.trans
    (mfderiv_comp_apply_of_eq (0 : ℝ) hh hγ (flowOf_zero hv p) (1 : ℝ)).symm).trans hzero

/-- **The derivative of a transition lands in the tangent space of the section.** The transition
carries a neighbourhood of `p` into the level of `g` through `flowOf v T p`, so the derivative of
`g` vanishes on the range of the derivative of the transition. -/
theorem mvfderiv_comp_mfderiv_flowTransition :
    mvfderiv I g (flowOf v T p) ∘L mfderiv I I (flowTransition v g T p) p = 0 := by
  have hh : MDifferentiableAt I I (flowTransition v g T p) p :=
    (contMDiffAt_flowTransition le_rfl hv hT hg hgv).mdifferentiableAt one_ne_zero
  have hconst : g ∘ flowTransition v g T p =ᶠ[𝓝 p] fun _ ↦ g (flowOf v T p) := by
    filter_upwards [eventually_flowHittingTime hv hT hg hgv] with z hz
    rw [comp_apply, flowTransition_apply]
    exact hz.2
  ext w
  have hzero : mvfderiv I (g ∘ flowTransition v g T p) p w = 0 := by
    simp [mvfderiv, hconst.mfderiv_eq]
  exact (mvfderiv_comp_apply_of_eq p (hg.mdifferentiableAt one_ne_zero) hh
    (flowTransition_self ..) w).symm.trans hzero

end Transition

/-- **Derivatives of transitions compose.** If the flow carries `p` to `q` at time `T` and `q` to
`r` at time `T'`, then the derivative at `p` of the transition to a section through `q`, followed
by the derivative at `q` of the transition to a section through `r`, is the derivative at `p` of
the transition to the section through `r` at time `T + T'`. -/
theorem mfderiv_flowTransition_comp (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g q) (hgv : mvfderiv I g q (v q) ≠ 0)
    (hT' : (T', q) ∈ flowDomain v) (hr : flowOf v T' q = r) (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' r)
    (hg'v : mvfderiv I g' r (v r) ≠ 0) :
    mfderiv I I (flowTransition v g' T' q) q ∘L mfderiv I I (flowTransition v g T p) p =
      mfderiv I I (flowTransition v g' (T + T') p) p := by
  have hh : MDifferentiableAt I I (flowTransition v g T p) p :=
    (contMDiffAt_flowTransition le_rfl hv hT (by rwa [hq]) (by rwa [hq])).mdifferentiableAt
      one_ne_zero
  have hh' : MDifferentiableAt I I (flowTransition v g' T' q) q :=
    (contMDiffAt_flowTransition le_rfl hv hT' (by rwa [hr]) (by rwa [hr])).mdifferentiableAt
      one_ne_zero
  ext w
  have hcomp := flowTransition_comp_eventuallyEq hv hT hq hg hgv hT' hr hg' hg'v
  exact (mfderiv_comp_apply_of_eq p hh' hh (by rw [flowTransition_self, hq]) w).symm.trans
    (DFunLike.congr_fun hcomp.mfderiv_eq w)

section Return

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hP : (T₀, p) ∈ flowDomain v)
  (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0)
  (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0)
include hT hq hP hp hg hgv hg' hg'v

/-- **Transitions intertwine the derivatives of return germs.** If the flow carries `p` to `q` at
time `T` and `p` returns to itself at time `T₀`, then the derivative `Dh` of the transition from a
section through `p` to a section through `q` satisfies `Dh ∘ DP_p = DP_q ∘ Dh`, where `P_p` and
`P_q` are the return branches at time `T₀` of these sections. -/
theorem mfderiv_flowTransition_semiconj :
    mfderiv I I (flowTransition v g' T p) p ∘L mfderiv I I (flowTransition v g T₀ p) p =
      mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' T p) p := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  rw [mfderiv_flowTransition_comp hv hP hp hg hgv hT hq hg' hg'v,
    mfderiv_flowTransition_comp hv hT hq hg' hg'v hQ hq' hg' hg'v, add_comm]

/-- **The characteristic polynomial of a return derivative is independent of the section and of
the base point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time
`T₀`, then the derivatives at `p` and at `q` of the return branches at time `T₀` of sections
through `p` and through `q` have the same characteristic polynomial. Taking `q = p` and `T = 0`,
two sections through the same point give return derivatives with the same characteristic
polynomial. -/
theorem charpoly_mfderiv_flowTransition_eq :
    (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap.charpoly =
      (mfderiv I I (flowTransition v g' T₀ q) q).toLinearMap.charpoly := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  have hback : flowOf v (-T) q = p := hq ▸ flowOf_neg_flowOf hv hT
  have hTback : (-T, q) ∈ flowDomain v := hq ▸ neg_mem_flowDomain_flowOf hv hT
  -- Write `A`, `B` for the two return derivatives, `h` for the derivative of the transition from
  -- `p` to `q` and `h'` for that of the reverse transition. Then `h' ∘ h` is the derivative of the
  -- time-`0` transition onto the section through `p`, which `A` absorbs on the left, and likewise
  -- `h ∘ h'` onto the section through `q`, absorbed by `B` on the right.
  have hh'h : mfderiv I I (flowTransition v g (-T) q) q ∘L
      mfderiv I I (flowTransition v g' T p) p = mfderiv I I (flowTransition v g 0 p) p := by
    rw [mfderiv_flowTransition_comp hv hT hq hg' hg'v hTback hback hg hgv, add_neg_cancel]
  have hA : mfderiv I I (flowTransition v g 0 p) p ∘L mfderiv I I (flowTransition v g T₀ p) p =
      mfderiv I I (flowTransition v g T₀ p) p := by
    rw [mfderiv_flowTransition_comp hv hP hp hg hgv (mem_flowDomain_zero hv p) (flowOf_zero hv p)
      hg hgv, add_zero]
  have hhh' : mfderiv I I (flowTransition v g' T p) p ∘L
      mfderiv I I (flowTransition v g (-T) q) q = mfderiv I I (flowTransition v g' 0 q) q := by
    rw [mfderiv_flowTransition_comp hv hTback hback hg hgv hT hq hg' hg'v, neg_add_cancel]
  have hB : mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' 0 q) q =
      mfderiv I I (flowTransition v g' T₀ q) q := by
    rw [mfderiv_flowTransition_comp hv (mem_flowDomain_zero hv q) (flowOf_zero hv q) hg' hg'v hQ
      hq' hg' hg'v, zero_add]
  have hAeq : mfderiv I I (flowTransition v g T₀ p) p =
      mfderiv I I (flowTransition v g (-T) q) q ∘L
        (mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' T p) p) := by
    refine hA.symm.trans <| (congrArg (fun L ↦ L ∘L mfderiv I I (flowTransition v g T₀ p) p)
      hh'h.symm).trans <| (ContinuousLinearMap.comp_assoc _ _ _).trans ?_
    exact congrArg (fun L ↦ mfderiv I I (flowTransition v g (-T) q) q ∘L L)
      (mfderiv_flowTransition_semiconj hv hT hq hP hp hg hgv hg' hg'v)
  have hBeq : mfderiv I I (flowTransition v g' T₀ q) q =
      (mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' T p) p) ∘L
        mfderiv I I (flowTransition v g (-T) q) q := by
    refine hB.symm.trans <| (congrArg (fun L ↦ mfderiv I I (flowTransition v g' T₀ q) q ∘L L)
      hhh'.symm).trans ?_
    exact (ContinuousLinearMap.comp_assoc _ _ _).symm
  exact (congrArg (fun L ↦ L.toLinearMap.charpoly) hAeq).trans <|
    (LinearMap.charpoly_comp_comm _ _ rfl).trans
      (congrArg (fun L ↦ L.toLinearMap.charpoly) hBeq).symm

/-- **The eigenvalues of a return derivative are independent of the section and of the base
point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time `T₀`, then
`μ` is an eigenvalue of the derivative at `p` of the return branch of a section through `p` exactly
when it is one at `q` for a section through `q`. For `μ = 1` this is the nondegeneracy test of
the closed orbit. -/
theorem hasEigenvalue_mfderiv_flowTransition_iff (μ : ℝ) :
    Module.End.HasEigenvalue (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap μ ↔
      Module.End.HasEigenvalue (mfderiv I I (flowTransition v g' T₀ q) q).toLinearMap μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_mfderiv_flowTransition_eq hv hT hq hP hp hg hgv hg' hg'v]

/-- **The same holds for every iterate.** If the flow carries `p` to `q` at time `T` and `p`
returns to itself at time `T₀`, then for every `k` the derivatives at `p` and at `q` of the
`k`-fold iterates of the return branches at time `T₀` of sections through `p` and through `q`
have the same characteristic polynomial. -/
theorem charpoly_mfderiv_iterate_flowTransition_eq (k : ℕ) :
    (mfderiv I I (flowTransition v g T₀ p)^[k] p).toLinearMap.charpoly =
      (mfderiv I I (flowTransition v g' T₀ q)^[k] q).toLinearMap.charpoly := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [iterate_zero, mfderiv_id]
    -- Both sides are the characteristic polynomial of the identity of the model space `E`.
    rfl
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
  rw [(flowTransition_iterate_eventuallyEq hv hP hp hg hgv hk).mfderiv_eq,
    (flowTransition_iterate_eventuallyEq hv hQ hq' hg' hg'v hk).mfderiv_eq]
  exact charpoly_mfderiv_flowTransition_eq hv hT hq hkP hkp hg hgv hg' hg'v

end Return

end TauCeti
