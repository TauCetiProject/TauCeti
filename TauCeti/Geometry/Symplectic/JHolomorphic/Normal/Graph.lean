/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Model
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Geometry.Symplectic.JHolomorphic.ComplexDifferentiable

/-!
# Curves of the normal model that project injectively are graphs

Let `C` be an embedded pseudoholomorphic curve in an almost complex four-manifold, with real normal
Cauchy–Riemann operator `D_C s = ∂bar s + ν s + μ conj s` in a holomorphic chart of `C` and a
unitary frame of its normal line. The normal model is the total space `ℂ × ℂ` with the almost
complex structure `J_N` of `TauCeti.normalModelStructure`, and a section `s` has `J_N`-holomorphic
graph exactly when `s` is differentiable and `D_C s = 0`
(`TauCeti.isJHolomorphicAt_graph_normalModelStructure_iff`). This file proves the converse
description of `J_N`-holomorphic curves: a `J_N`-holomorphic curve whose projection to the base is
injective is, after reparametrization, the graph of a solution of `D_C s = 0`.

Let `u : ℂ → ℂ × ℂ` be `J_N`-holomorphic on an open set `U`, for the standard structure on the
source, and write `f y = (u y).1` for its projection to the base. Then:

* `f` is holomorphic (`TauCeti.IsJHolomorphicAt.differentiableAt_fst_of_normalModelStructure`,
  `TauCeti.IsJHolomorphicOn.differentiableOn_fst_of_normalModelStructure`), so where `f` is
  injective on `U` it is a biholomorphism from `U` onto the open set `f '' U`
  (`DifferentiableOn.toOpenPartialHomeomorph`);
* if `g` is a holomorphic local section of `f`, with `f (g w) = w` near `z`, then the normal
  component `w ↦ (u (g w)).2` of `u ∘ g` has `J_N`-holomorphic graph at `z`
  (`TauCeti.isJHolomorphicAt_graph_snd_comp_normalModelStructure`);
* hence, if the normal component of `u` factors through the base, `(u y).2 = v (f y)` on `U`, then
  the graph of `v` is `J_N`-holomorphic at the image `f y` of every point `y ∈ U` where the complex
  derivative of `f` does not vanish
  (`TauCeti.isJHolomorphicAt_graph_normalModelStructure_of_deriv_ne_zero`), and so at every point of
  `f '' U` when `f` is injective on `U`; there `v` is moreover as regular as `u`
  (`TauCeti.contDiffAt_of_isJHolomorphicOn_normalModelStructure_of_deriv_ne_zero`);
* when `f` is injective on `U` such a `v` exists, so that `u y = (f y, v (f y))` on `U` with
  `D_C v = 0` on `f '' U`
  (`TauCeti.exists_forall_eq_and_isJHolomorphicAt_graph_normalModelStructure`); conversely
  `u = (f, v ∘ f)` is `J_N`-holomorphic on `U` as soon as `f` is holomorphic there and the graph of
  `v` is `J_N`-holomorphic on `f '' U`
  (`TauCeti.isJHolomorphicOn_normalModelStructure_iff_of_injOn`).

In Taubes's analysis of Seiberg–Witten solutions concentrating along `C`, the rescaled limit is a
`J_N`-holomorphic cycle in the normal bundle of `C`. When `C` enters with multiplicity one the
projection of the limiting component to `C` has degree one, hence is injective, and the results
above identify that component with the graph of a section `v` in the kernel of `D_C`. A point
`(x, 0)` of the component, as produced by a zero of the Seiberg–Witten section converging to
`x ∈ C`, gives `v x = 0`. Both are local statements in a chart of `C` and a frame of `N_C`; the
assembly over the whole curve needs `N_C` as an almost complex manifold, which is not treated here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

namespace TauCeti

open Complex Function Set
open scoped Topology

variable {ν μ : ℂ → ℂ} {u : ℂ → ℂ × ℂ}

/-- The projection to the base of a curve that is `J_N`-holomorphic at `y`, for the standard
structure on the source, is complex differentiable at `y`. -/
theorem IsJHolomorphicAt.differentiableAt_fst_of_normalModelStructure {y : ℂ}
    (hu : IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u y) :
    DifferentiableAt ℂ (fun y ↦ (u y).1) y :=
  isConstStructureJHolomorphicAt_ofComplexModule_iff.1
    ((isJHolomorphicAt_constStructure_iff _ _ _ _).1 hu.fst_of_normalModelStructure)

/-- The projection to the base of a curve that is `J_N`-holomorphic on an open set `U`, for the
standard structure on the source, is holomorphic on `U`. -/
theorem IsJHolomorphicOn.differentiableOn_fst_of_normalModelStructure {U : Set ℂ}
    (hu : IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u U) (hU : IsOpen U) :
    DifferentiableOn ℂ (fun y ↦ (u y).1) U := fun _ hy ↦
  ((hu.isJHolomorphicWithinAt hy).isJHolomorphicAt_of_mem_nhds
    (hU.mem_nhds hy)).differentiableAt_fst_of_normalModelStructure.differentiableWithinAt

/-- **Reparametrization by a holomorphic section of the base.** Let `u` be `J_N`-holomorphic at
`g z`, for a map `g` complex differentiable at `z` with `(u (g w)).1 = w` for `w` near `z`. Then
`u ∘ g` is the graph of its normal component near `z`, and this graph is `J_N`-holomorphic at `z`:
the normal component solves `∂bar s + ν s + μ conj s = 0` at `z`
(`TauCeti.isJHolomorphicAt_graph_normalModelStructure_iff`). -/
theorem isJHolomorphicAt_graph_snd_comp_normalModelStructure {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z)
    (hu : IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u (g z))
    (hsec : ∀ᶠ w in 𝓝 z, (u (g w)).1 = w) :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) (fun w ↦ (w, (u (g w)).2)) z := by
  have hcomp := hu.comp ((isJHolomorphicAt_constStructure_iff _ _ _ _).2
    hg.isConstStructureJHolomorphicAt_ofComplexModule)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hsec] with w hw
  exact Prod.ext hw.symm rfl

/-- Near the image of a point `y ∈ U` where the projection `f = (u ·).1` has nonzero complex
derivative, a holomorphic local inverse `g` of `f` exhibits `u ∘ g` as the graph of `v`. -/
private theorem exists_analyticAt_and_eventually_eq_of_deriv_ne_zero {U : Set ℂ} {v : ℂ → ℂ}
    (hU : IsOpen U)
    (hu : IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u U)
    (hv : ∀ y ∈ U, (u y).2 = v (u y).1) {y : ℂ} (hy : y ∈ U)
    (hderiv : deriv (fun y ↦ (u y).1) y ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (u y).1 ∧ g (u y).1 = y ∧
      ∀ᶠ w in 𝓝 (u y).1, (u (g w)).1 = w ∧ v w = (u (g w)).2 := by
  have hf := (hu.differentiableOn_fst_of_normalModelStructure hU).analyticAt (hU.mem_nhds hy)
  have hs := hf.hasStrictDerivAt
  have hgy : hs.localInverse _ _ _ hderiv (u y).1 = y :=
    (hs.eventually_left_inverse hderiv).self_of_nhds
  have hgU : ∀ᶠ w in 𝓝 (u y).1, hs.localInverse _ _ _ hderiv w ∈ U :=
    (HasStrictDerivAt.hasDerivAt (hs.to_localInverse hderiv)).continuousAt.preimage_mem_nhds
      (by rw [hgy]; exact hU.mem_nhds hy)
  refine ⟨_, hf.analyticAt_localInverse hderiv, hgy, ?_⟩
  filter_upwards [hgU, hs.eventually_right_inverse hderiv] with w hwU hw
  refine ⟨hw, ?_⟩
  rw [hv _ hwU]
  exact congrArg v hw.symm

/-- **Curves are graphs over regular points of their projection.** Let `u` be `J_N`-holomorphic on
an open set `U` and let its normal component factor through its projection `f = (u ·).1` to the
base, `(u y).2 = v (f y)` on `U`. Then at the image `f y` of every point `y ∈ U` where the complex
derivative of `f` does not vanish, the graph of `v` is `J_N`-holomorphic: `v` is differentiable at
`f y` and solves `∂bar v + ν v + μ conj v = 0` there
(`TauCeti.isJHolomorphicAt_graph_normalModelStructure_iff`). -/
theorem isJHolomorphicAt_graph_normalModelStructure_of_deriv_ne_zero {U : Set ℂ} {v : ℂ → ℂ}
    (hU : IsOpen U)
    (hu : IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u U)
    (hv : ∀ y ∈ U, (u y).2 = v (u y).1) {y : ℂ} (hy : y ∈ U)
    (hderiv : deriv (fun y ↦ (u y).1) y ≠ 0) :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) (fun z ↦ (z, v z)) (u y).1 := by
  obtain ⟨g, hg, hgy, hgv⟩ :=
    exists_analyticAt_and_eventually_eq_of_deriv_ne_zero hU hu hv hy hderiv
  have hugy := (hu.isJHolomorphicWithinAt hy).isJHolomorphicAt_of_mem_nhds (hU.mem_nhds hy)
  rw [← hgy] at hugy
  -- near `(u y).1`, the graph of `v` is the graph of the normal component of `u ∘ g`
  refine (isJHolomorphicAt_graph_snd_comp_normalModelStructure hg.differentiableAt hugy
    (hgv.mono fun _ h ↦ h.1)).congr_of_eventuallyEq ?_
  filter_upwards [hgv] with w hw
  rw [hw.2]

/-- **Regularity of the section.** In the situation of
`TauCeti.isJHolomorphicAt_graph_normalModelStructure_of_deriv_ne_zero`, the section `v` is as
regular at `f y` as the curve `u` is at `y`: if `u` is `C^n` at `y`, then `v` is `C^n` at `f y`. -/
theorem contDiffAt_of_isJHolomorphicOn_normalModelStructure_of_deriv_ne_zero {U : Set ℂ}
    {v : ℂ → ℂ} {n : WithTop ℕ∞} (hU : IsOpen U)
    (hu : IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u U)
    (hv : ∀ y ∈ U, (u y).2 = v (u y).1) {y : ℂ} (hy : y ∈ U)
    (hderiv : deriv (fun y ↦ (u y).1) y ≠ 0) (hu' : ContDiffAt ℝ n u y) :
    ContDiffAt ℝ n v (u y).1 := by
  obtain ⟨g, hg, hgy, hgv⟩ :=
    exists_analyticAt_and_eventually_eq_of_deriv_ne_zero hU hu hv hy hderiv
  rw [← hgy] at hu'
  -- near `(u y).1`, the section `v` is the normal component of `u ∘ g`
  refine (contDiffAt_snd.comp _ (hu'.comp _
    (hg.contDiffAt.restrict_scalars ℝ))).congr_of_eventuallyEq ?_
  filter_upwards [hgv] with w hw
  exact hw.2

/-- **Characterization of curves with injective projection.** Let `u` have projection
`f = (u ·).1` injective on an open set `U`, and normal component `(u y).2 = v (f y)` on `U`. Then
`u` is `J_N`-holomorphic on `U` exactly when `f` is holomorphic on `U` and the graph of `v` is
`J_N`-holomorphic at every point of `f '' U`, that is, when `f` is a biholomorphism onto `f '' U`
and `v` solves `∂bar v + ν v + μ conj v = 0` there. -/
theorem isJHolomorphicOn_normalModelStructure_iff_of_injOn {U : Set ℂ} {v : ℂ → ℂ}
    (hU : IsOpen U) (hinj : InjOn (fun y ↦ (u y).1) U) (hv : ∀ y ∈ U, (u y).2 = v (u y).1) :
    IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
        (normalModelStructure ν μ) u U ↔
      DifferentiableOn ℂ (fun y ↦ (u y).1) U ∧
        ∀ z ∈ (fun y ↦ (u y).1) '' U,
          IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
            (normalModelStructure ν μ) (fun z ↦ (z, v z)) z := by
  constructor
  · intro hu
    have hf := hu.differentiableOn_fst_of_normalModelStructure hU
    refine ⟨hf, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact isJHolomorphicAt_graph_normalModelStructure_of_deriv_ne_zero hU hu hv hy
      (deriv_ne_zero_of_injOn hf hU hinj hy)
  · rintro ⟨hf, hgraph⟩
    refine (isJHolomorphicOn_iff _ _ _ _).2 fun y hy ↦ ?_
    -- near `y`, the curve `u` is the graph of `v` composed with the holomorphic projection
    have hfy :=
      ((hf y hy).differentiableAt (hU.mem_nhds hy)).isConstStructureJHolomorphicAt_ofComplexModule
    have hcomp := IsJHolomorphicAt.comp (f := fun y ↦ (u y).1) (x := y)
      (hgraph _ (mem_image_of_mem _ hy)) ((isJHolomorphicAt_constStructure_iff _ _ _ _).2 hfy)
    refine (hcomp.congr_of_eventuallyEq ?_).isJHolomorphicWithinAt
    filter_upwards [hU.mem_nhds hy] with y' hy'
    exact Prod.ext rfl (hv y' hy')

/-- **Curves with injective projection are graphs.** Let `u` be `J_N`-holomorphic on an open set
`U`, with projection `f = (u ·).1` to the base injective on `U`, so that `f` is a biholomorphism
from `U` onto the open set `f '' U`. Then `u` is the graph of a section `v` over `f '' U`,
`u y = (f y, v (f y))` on `U`, and the graph of `v` is `J_N`-holomorphic at every point of `f '' U`:
`v` is differentiable there and solves `∂bar v + ν v + μ conj v = 0`
(`TauCeti.isJHolomorphicAt_graph_normalModelStructure_iff`). -/
theorem exists_forall_eq_and_isJHolomorphicAt_graph_normalModelStructure {U : Set ℂ}
    (hU : IsOpen U)
    (hu : IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (normalModelStructure ν μ) u U)
    (hinj : InjOn (fun y ↦ (u y).1) U) :
    ∃ v : ℂ → ℂ, (∀ y ∈ U, u y = ((u y).1, v (u y).1)) ∧
      ∀ z ∈ (fun y ↦ (u y).1) '' U,
        IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
          (normalModelStructure ν μ) (fun z ↦ (z, v z)) z := by
  -- the section reads off the normal component at the unique preimage in `U`
  have hv : ∀ y ∈ U, (u y).2 = (u (invFunOn (fun y ↦ (u y).1) U (u y).1)).2 := fun y hy ↦ by
    rw [hinj.leftInvOn_invFunOn hy]
  exact ⟨_, fun y hy ↦ Prod.ext rfl (hv y hy),
    ((isJHolomorphicOn_normalModelStructure_iff_of_injOn
      (v := fun z ↦ (u (invFunOn (fun y ↦ (u y).1) U z)).2) hU hinj hv).1 hu).2⟩

end TauCeti
