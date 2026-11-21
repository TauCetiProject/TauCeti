/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.PontryaginThom.Independence
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.ContMDiff.PartialDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Topology.Compactness.Normed

/-!
# Independence of the Pontryagin–Thom collapse from a smooth tube

Let `τ₀, τ₁ : S × V → M` be framed tubes around the same map `f : S → M`
(`TauCeti.IsFramedTube`), with `S` a compact boundaryless manifold and `V` a real normed space.
The collapse of `τ₁` is homotopic to that of `τ₀` as soon as the transition from `τ₁` to `τ₀`
has, along the core, a fibre derivative homotopic to the identity through linear automorphisms
(`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic`). This file supplies that fibre
derivative for smooth tubes.

At a point `(x, 0)` of the core both tubes pass through `f x`. The **transition fibre
derivative** (`TauCeti.transitionFDeriv`) is the normal part of `dτ₀⁻¹ ∘ dτ₁` on the fibre:

`transitionFDeriv I J τ₀ τ₁ x = pr₂ ∘ (dτ₀_(x,0))⁻¹ ∘ dτ₁_(x,0) ∘ ι₂ : V →L[ℝ] V`.

It measures how the framing of the normal bundle of `f` carried by `τ₁` reads in the framing
carried by `τ₀`: it is the identity when the tubes coincide (`TauCeti.transitionFDeriv_self`),
and for two local diffeomorphisms agreeing on the core it is invertible, with inverse the
transition fibre derivative in the other direction
(`TauCeti.transitionFDeriv_comp_transitionFDeriv`, `TauCeti.isInvertible_transitionFDeriv`).

If `τ₀` is a `C¹` local diffeomorphism and `τ₁` is `C¹`, the transition `τ₀⁻¹ ∘ τ₁` is a `C¹` map
near the zero section (`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`). Its normal coordinate has a
jointly continuous derivative in the fibre direction
(`ContMDiffOn.continuousOn_iteratedFDeriv_partial`), and that derivative along the core is
`transitionFDeriv` (`TauCeti.transitionFDeriv_eq_fderiv`). So the transition from `τ₁` to `τ₀`
has fibre derivative `transitionFDeriv I J τ₀ τ₁` along the core
(`TauCeti.hasTransitionFDeriv_transitionFDeriv`), which is continuous in the point of the core
(`TauCeti.continuous_transitionFDeriv`); when both tubes are local diffeomorphisms it is a
continuous family of linear automorphisms (`TauCeti.exists_continuous_units_transitionFDeriv`).
Hence:

* two such tubes whose transition fibre derivative is homotopic to the identity through linear
  automorphisms have homotopic collapses
  (`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv`), also as maps
  onto `Sᵏ` for `V = ℝᵏ`
  (`TauCeti.IsFramedTube.pontryaginThomSphereMap_homotopic_of_transitionFDeriv`);
* in particular two smooth tubes inducing the same framing of the normal bundle, that is with
  transition fibre derivative the identity, have homotopic collapses
  (`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv_eq_id`).

## Main declarations

* `TauCeti.transitionFDeriv I J τ₀ τ₁ x`: the fibre derivative of the transition from `τ₁` to
  `τ₀` at the core point `(x, 0)`.
* `TauCeti.transitionFDeriv_apply`: its formula from the differentials of the tubes.
* `TauCeti.isInvertible_transitionFDeriv`: it is invertible for local diffeomorphisms agreeing on
  the core.
* `TauCeti.transitionFDeriv_eq_fderiv`: it is the derivative along the fibre of the normal
  coordinate of any transition `φ` with `τ₁ = τ₀ ∘ φ` near the core point.
* `TauCeti.hasTransitionFDeriv_transitionFDeriv`: for smooth tubes it is the fibre derivative of
  the transition along the core, uniformly in the point of the core.
* `TauCeti.continuous_transitionFDeriv`: it depends continuously on the point of the core.
* `TauCeti.exists_continuous_units_transitionFDeriv`: for two smooth local diffeomorphic tubes it
  lifts to a continuous map into the linear automorphisms of `V`.
* `TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv`: smooth tubes
  whose transition fibre derivative is homotopic to the identity have homotopic collapses.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5 (uniqueness of tubular neighbourhoods).
-/

public section

open Function Set Topology Metric
open scoped Manifold

namespace TauCeti

variable {E H S F G M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace S] [ChartedSpace H S]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace G M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {n : WithTop ℕ∞}

/-- The normal part `pr₂ ∘ d₀⁻¹ ∘ d₁ ∘ ι₂ : V →L[ℝ] V` of two linear maps `d₀, d₁ : E × V →L[ℝ] F`
on the fibre `V`. -/
private noncomputable def fiberPart (d₀ d₁ : E × V →L[ℝ] F) : V →L[ℝ] V :=
  ContinuousLinearMap.snd ℝ E V ∘L d₀.inverse ∘L d₁ ∘L ContinuousLinearMap.inr ℝ E V

private theorem fiberPart_comp {d₀ : E × V →L[ℝ] F} (hd : d₀.IsInvertible)
    (T : E × V →L[ℝ] E × V) :
    fiberPart d₀ (d₀ ∘L T) = ContinuousLinearMap.snd ℝ E V ∘L T ∘L ContinuousLinearMap.inr ℝ E V :=
  ContinuousLinearMap.ext fun v ↦ by simp [fiberPart, hd.inverse_apply_self]

/-- Two invertible linear maps `d₀, d₁ : E × V →L[ℝ] F` agreeing on the base `E` have mutually
inverse normal parts. -/
private theorem fiberPart_comp_fiberPart {d₀ d₁ : E × V →L[ℝ] F} (h₀ : d₀.IsInvertible)
    (h₁ : d₁.IsInvertible) (h : ∀ u, d₀ (u, 0) = d₁ (u, 0)) :
    fiberPart d₀ d₁ ∘L fiberPart d₁ d₀ = ContinuousLinearMap.id ℝ V :=
  ContinuousLinearMap.ext fun v ↦ by
    -- Write `w = d₁⁻¹ (d₀ (0, v))`; removing its base part, `d₁ (0, w.2) = d₀ ((0, v) - (w.1, 0))`.
    have hw : d₁ (0, (d₁.inverse (d₀ (0, v))).2) =
        d₀ ((0, v) - ((d₁.inverse (d₀ (0, v))).1, 0)) := by
      rw [map_sub, h, eq_sub_iff_add_eq, ← map_add, Prod.mk_add_mk, zero_add, add_zero, Prod.mk.eta,
        h₁.self_apply_inverse]
    simp [fiberPart, hw, h₀.inverse_apply_self]

variable (I J) in
/-- The **transition fibre derivative** of two tubes `τ₀, τ₁ : S × V → M` at the core point
`(x, 0)`: the normal part `pr₂ ∘ (dτ₀_(x,0))⁻¹ ∘ dτ₁_(x,0) ∘ ι₂ : V →L[ℝ] V` of the derivative of
the transition `τ₀⁻¹ ∘ τ₁` on the fibre `V`, where `pr₂ : E × V → V` and `ι₂ : V → E × V` are the
projection and the inclusion of the fibre in the tangent space `E × V` of `S × V`. It is
meaningful when `τ₀ (x, 0) = τ₁ (x, 0)`, as for two framed tubes around the same map, and
`dτ₀_(x,0)` is invertible, as for a local diffeomorphism `τ₀`. -/
noncomputable def transitionFDeriv (τ₀ τ₁ : S × V → M) (x : S) : V →L[ℝ] V :=
  fiberPart (E := E) (F := F) (mfderiv (I.prod 𝓘(ℝ, V)) J τ₀ (x, 0))
    (mfderiv (I.prod 𝓘(ℝ, V)) J τ₁ (x, 0))

variable (I J) in
/-- The transition fibre derivative applied to `v` is the normal coordinate of
`(dτ₀_(x,0))⁻¹ (dτ₁_(x,0) (0, v))`. -/
theorem transitionFDeriv_apply (τ₀ τ₁ : S × V → M) (x : S) (v : V) :
    transitionFDeriv I J τ₀ τ₁ x v =
      ((mfderiv (I.prod 𝓘(ℝ, V)) J τ₀ (x, 0)).inverse
        (mfderiv (I.prod 𝓘(ℝ, V)) J τ₁ (x, 0) (0, v))).2 := by
  rw [transitionFDeriv]
  rfl

/-- **The transition fibre derivative is the fibre derivative of the transition.** If `τ₀` is a
local diffeomorphism at the core point `(x, 0)` and `τ₁ = τ₀ ∘ φ` near `(x, 0)`, for a map `φ`
fixing `(x, 0)` and differentiable there, then `transitionFDeriv I J τ₀ τ₁ x` is the derivative
at `0` of the normal coordinate `w ↦ (φ (x, w)).2` of `φ` along the fibre. -/
theorem transitionFDeriv_eq_fderiv {τ₀ τ₁ : S × V → M} {x : S} (hn : n ≠ 0)
    (hτ₀ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, V)) J n τ₀ (x, 0)) {φ : S × V → S × V}
    (hφ : MDifferentiableAt (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) φ (x, 0))
    (hφx : φ (x, 0) = (x, 0)) (heq : τ₁ =ᶠ[𝓝 (x, 0)] τ₀ ∘ φ) :
    transitionFDeriv I J τ₀ τ₁ x = fderiv ℝ (fun w ↦ (φ (x, w)).2) 0 := by
  -- Tangent spaces are the model spaces by definition; read the differentials there.
  let d₀ : E × V →L[ℝ] F := mfderiv (I.prod 𝓘(ℝ, V)) J τ₀ (x, 0)
  let dφ : E × V →L[ℝ] E × V := mfderiv (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) φ (x, 0)
  have hτ₀D : HasMFDerivAt (I.prod 𝓘(ℝ, V)) J τ₀ (φ (x, 0)) d₀ := by
    rw [hφx]
    exact (hτ₀.mdifferentiableAt hn).hasMFDerivAt
  have hinv : d₀.IsInvertible := hτ₀.isInvertible_mfderiv hn
  -- The chain rule gives `dτ₁ = dτ₀ ∘ dφ` at `(x, 0)`.
  let d₁ : E × V →L[ℝ] F := mfderiv (I.prod 𝓘(ℝ, V)) J τ₁ (x, 0)
  have hτ₁ : d₁ = d₀ ∘L dφ :=
    ((hτ₀D.comp (x, 0) hφ.hasMFDerivAt).congr_of_eventuallyEq_abuse heq).mfderiv
  -- The normal coordinate of `φ` along the fibre has derivative `pr₂ ∘ dφ ∘ ι₂` at `0`.
  have hslice : HasMFDerivAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V)) (fun w : V ↦ (x, w)) 0
      (ContinuousLinearMap.inr ℝ E V) :=
    (hasMFDerivAt_const x (0 : V)).prodMk (hasMFDerivAt_id (0 : V))
  have hd : HasFDerivAt (fun w ↦ (φ (x, w)).2)
      (ContinuousLinearMap.snd ℝ E V ∘L dφ ∘L ContinuousLinearMap.inr ℝ E V) 0 :=
    ((hasMFDerivAt_snd _).comp (0 : V) (hφ.hasMFDerivAt.comp (0 : V) hslice)).hasFDerivAt
  calc transitionFDeriv I J τ₀ τ₁ x = fiberPart d₀ (d₀ ∘L dφ) := congrArg (fiberPart d₀) hτ₁
    _ = ContinuousLinearMap.snd ℝ E V ∘L dφ ∘L ContinuousLinearMap.inr ℝ E V :=
      fiberPart_comp hinv dφ
    _ = fderiv ℝ (fun w ↦ (φ (x, w)).2) 0 := hd.fderiv.symm

/-- The transition fibre derivative of a local diffeomorphism to itself is the identity. -/
theorem transitionFDeriv_self {τ : S × V → M} {x : S} (hn : n ≠ 0)
    (hτ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, V)) J n τ (x, 0)) :
    transitionFDeriv I J τ τ x = ContinuousLinearMap.id ℝ V := by
  refine (transitionFDeriv_eq_fderiv (τ₁ := τ) (φ := id) hn hτ mdifferentiableAt_id rfl
    (Filter.Eventually.of_forall fun _ ↦ rfl)).trans ?_
  exact (hasFDerivAt_id (0 : V)).fderiv

/-- **The transition fibre derivatives in both directions are mutually inverse.** If `τ₀` and `τ₁`
are local diffeomorphisms at the core point `(x, 0)` and agree on the core near `x`, as two framed
tubes around the same map do, then `transitionFDeriv I J τ₁ τ₀ x` is a right inverse of
`transitionFDeriv I J τ₀ τ₁ x`. -/
theorem transitionFDeriv_comp_transitionFDeriv {τ₀ τ₁ : S × V → M} {x : S} (hn : n ≠ 0)
    (hτ₀ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, V)) J n τ₀ (x, 0))
    (hτ₁ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, V)) J n τ₁ (x, 0))
    (hcore : (fun y ↦ τ₁ (y, 0)) =ᶠ[𝓝 x] fun y ↦ τ₀ (y, 0)) :
    transitionFDeriv I J τ₀ τ₁ x ∘L transitionFDeriv I J τ₁ τ₀ x = ContinuousLinearMap.id ℝ V := by
  -- Both tubes restrict to the same map on the core, so by the chain rule their differentials
  -- agree on the base `E`.
  have hz : HasMFDerivAt I (I.prod 𝓘(ℝ, V)) (fun y ↦ (y, (0 : V))) x
      (ContinuousLinearMap.inl ℝ E V) :=
    (hasMFDerivAt_id x).prodMk (hasMFDerivAt_const (0 : V) x)
  have hbase : mfderiv (I.prod 𝓘(ℝ, V)) J τ₀ (x, 0) ∘L ContinuousLinearMap.inl ℝ E V =
      mfderiv (I.prod 𝓘(ℝ, V)) J τ₁ (x, 0) ∘L ContinuousLinearMap.inl ℝ E V :=
    ((hτ₀.mdifferentiableAt hn).hasMFDerivAt.comp x hz).mfderiv.symm.trans
      (((hτ₁.mdifferentiableAt hn).hasMFDerivAt.comp x hz).congr_of_eventuallyEq_abuse
        hcore.symm).mfderiv
  exact fiberPart_comp_fiberPart (hτ₀.isInvertible_mfderiv hn) (hτ₁.isInvertible_mfderiv hn)
    fun u ↦ congrArg (fun L : E →L[ℝ] F ↦ L u) hbase

/-- The transition fibre derivative of two local diffeomorphisms at the core point `(x, 0)` which
agree on the core near `x` is invertible, with inverse `transitionFDeriv I J τ₁ τ₀ x`. -/
theorem isInvertible_transitionFDeriv {τ₀ τ₁ : S × V → M} {x : S} (hn : n ≠ 0)
    (hτ₀ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, V)) J n τ₀ (x, 0))
    (hτ₁ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, V)) J n τ₁ (x, 0))
    (hcore : (fun y ↦ τ₁ (y, 0)) =ᶠ[𝓝 x] fun y ↦ τ₀ (y, 0)) :
    (transitionFDeriv I J τ₀ τ₁ x).IsInvertible :=
  .of_inverse (transitionFDeriv_comp_transitionFDeriv hn hτ₀ hτ₁ hcore)
    (transitionFDeriv_comp_transitionFDeriv hn hτ₁ hτ₀ hcore.symm)

/-! ### The transition between two smooth tubes -/

section Transition

variable [I.Boundaryless] [CompactSpace S] [IsManifold I n S] {f : S → M} {τ₀ τ₁ : S × V → M}

/-- Near the zero section, a tube `τ₁` reads in a local diffeomorphism `τ₀` around the same map
through a transition `φ`, which fixes the zero section and is `C^n` there, and whose normal
coordinate has a jointly continuous derivative in the fibre direction, equal along the core to the
transition fibre derivative. -/
private theorem exists_transition [Nonempty S] (hn : 1 ≤ n) (h₀ : IsFramedTube f τ₀)
    (h₁ : IsFramedTube f τ₁) (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₀)
    (hτ₁ : ContMDiff (I.prod 𝓘(ℝ, V)) J n τ₁) :
    ∃ r > 0, ∃ φ : S × V → S × V, (∀ x (v : V), ‖v‖ < r → τ₁ (x, v) = τ₀ (φ (x, v))) ∧
      (∀ x, φ (x, 0) = (x, 0)) ∧
      (∀ x (v : V), ‖v‖ < r → ContMDiffAt (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) n φ (x, v)) ∧
      (∀ x, fderiv ℝ (fun w ↦ (φ (x, w)).2) 0 = transitionFDeriv I J τ₀ τ₁ x) ∧
      ContinuousOn (fun p : S × V ↦ fderiv ℝ (fun w ↦ (φ (p.1, w)).2) p.2)
        (univ ×ˢ ball (0 : V) r) := by
  have hcore (x : S) : τ₁ (x, 0) = τ₀ (x, 0) := by rw [h₁.apply_zero, h₀.apply_zero]
  -- The tube `τ₁` meets the open range of `τ₀` on a uniform neighbourhood of the zero section.
  obtain ⟨r, hr, hmem⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (v : V) (x : S) ↦ τ₁ (x, v) ∈ range τ₀) fun x _ ↦
      (hτ₀.isOpen_range.preimage (h₁.isOpenEmbedding.continuous.comp continuous_swap)).mem_nhds
        (by simp [hcore])
  have hinj : InjOn τ₀ univ := h₀.isOpenEmbedding.injective.injOn
  have hinv := (isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ.1 hτ₀).contMDiffOn_invFunOn
    isOpen_univ hinj
  rw [image_univ] at hinv
  have hφs (x : S) (v : V) (hv : ‖v‖ < r) :
      ContMDiffAt (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) n (invFunOn τ₀ univ ∘ τ₁) (x, v) :=
    (hinv.contMDiffAt (hτ₀.isOpen_range.mem_nhds (hmem hv x (mem_univ x)))).comp _ (hτ₁ _)
  have hφ (x : S) (v : V) (hv : ‖v‖ < r) : τ₁ (x, v) = τ₀ ((invFunOn τ₀ univ ∘ τ₁) (x, v)) := by
    obtain ⟨p, hp⟩ := hmem hv x (mem_univ x)
    exact (invFunOn_eq ⟨p, mem_univ p, hp⟩).symm
  have hφ0 (x : S) : (invFunOn τ₀ univ ∘ τ₁) (x, 0) = (x, 0) := by
    rw [comp_apply, hcore]
    exact hinj.leftInvOn_invFunOn (mem_univ _)
  refine ⟨r, hr, invFunOn τ₀ univ ∘ τ₁, hφ, hφ0, hφs, fun x ↦ ?_, ?_⟩
  · -- Along the core the fibre derivative is the transition fibre derivative, since
    -- `τ₁ = τ₀ ∘ φ` on the neighbourhood `S × B(0, r)` of `(x, 0)`.
    have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
    refine (transitionFDeriv_eq_fderiv hn0 (hτ₀ (x, 0))
      ((hφs x 0 (by simpa using hr)).mdifferentiableAt hn0) (hφ0 x) ?_).symm
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (ball_mem_nhds (0 : V) hr)]
      with p hp
    exact hφ p.1 p.2 (mem_ball_zero_iff.1 hp)
  -- With the fibre as first factor, the normal coordinate of `φ` is `C^n` on the open set
  -- `B(0, r) × S`, so its first partial derivative is jointly continuous there.
  have hΨ : ContMDiffOn (𝓘(ℝ, V).prod I) 𝓘(ℝ, V) n
      (fun q : V × S ↦ ((invFunOn τ₀ univ ∘ τ₁) (q.2, q.1)).2)
      (ball (0 : V) r ×ˢ univ) := fun q hq ↦
    (contMDiffAt_snd.comp q ((hφs q.2 q.1 (mem_ball_zero_iff.1 hq.1)).comp q
      (contMDiffAt_snd.prodMk contMDiffAt_fst))).contMDiffWithinAt
  have hcont := (hΨ.continuousOn_iteratedFDeriv_partial (isOpen_ball.prod isOpen_univ)
    (k := 1) (by exact_mod_cast hn)).comp (s := univ ×ˢ ball (0 : V) r)
      continuous_swap.continuousOn fun p hp ↦ ⟨hp.2, hp.1⟩
  refine ((continuousMultilinearCurryFin1 ℝ V V).continuous.comp_continuousOn hcont).congr
    fun p _ ↦ ContinuousLinearMap.ext fun w ↦ ?_
  simp

/-- **The transition between smooth tubes has a fibre derivative along the core.** Let `τ₀` and
`τ₁` be framed tubes around the same map `f : S → M`, from a compact boundaryless manifold `S`,
with `τ₀` a `C^n` local diffeomorphism and `τ₁` a `C^n` map, `n ≥ 1`. Then near the core,
`τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))` uniformly in `x`, for `A = transitionFDeriv I J τ₀ τ₁`. -/
theorem hasTransitionFDeriv_transitionFDeriv (hn : 1 ≤ n) (h₀ : IsFramedTube f τ₀)
    (h₁ : IsFramedTube f τ₁) (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₀)
    (hτ₁ : ContMDiff (I.prod 𝓘(ℝ, V)) J n τ₁) :
    HasTransitionFDeriv τ₀ τ₁ (transitionFDeriv I J τ₀ τ₁) := by
  cases isEmpty_or_nonempty S
  · exact fun _ _ ↦ ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
  obtain ⟨r, hr, φ, hφ, hφ0, hφs, hD, hDc⟩ := exists_transition hn h₀ h₁ hτ₀ hτ₁
  rw [← funext hD]
  refine HasTransitionFDeriv.of_hasFDerivAt hr hφ (fun x ↦ by rw [hφ0]) (fun x v hv ↦ ?_) hDc
  have hslice : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V) n (fun w ↦ (φ (x, w)).2) v :=
    contMDiffAt_snd.comp v ((hφs x v hv).comp v (contMDiffAt_const.prodMk contMDiffAt_id))
  exact (hslice.contDiffAt.differentiableAt (zero_lt_one.trans_le hn).ne').hasFDerivAt

/-- **The transition fibre derivative of smooth tubes is continuous** along the core, under the
hypotheses of `TauCeti.hasTransitionFDeriv_transitionFDeriv`. -/
theorem continuous_transitionFDeriv (hn : 1 ≤ n) (h₀ : IsFramedTube f τ₀)
    (h₁ : IsFramedTube f τ₁) (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₀)
    (hτ₁ : ContMDiff (I.prod 𝓘(ℝ, V)) J n τ₁) :
    Continuous (transitionFDeriv I J τ₀ τ₁) := by
  cases isEmpty_or_nonempty S
  · exact continuous_of_discreteTopology
  obtain ⟨r, hr, φ, -, -, -, hD, hDc⟩ := exists_transition hn h₀ h₁ hτ₀ hτ₁
  rw [← funext hD]
  exact hDc.comp_continuous (Continuous.prodMk_left 0) fun x ↦ ⟨mem_univ x, mem_ball_self hr⟩

/-- **The transition fibre derivative of smooth tubes is a continuous family of linear
automorphisms.** If `τ₀` and `τ₁` are framed tubes around the same map `f : S → M`, from a compact
boundaryless manifold `S`, and both are `C^n` local diffeomorphisms, `n ≥ 1`, then
`transitionFDeriv I J τ₀ τ₁` lifts to a continuous map into the units of `V →L[ℝ] V`; this
supplies the endpoint of the homotopy in
`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv`. -/
theorem exists_continuous_units_transitionFDeriv (hn : 1 ≤ n) (h₀ : IsFramedTube f τ₀)
    (h₁ : IsFramedTube f τ₁) (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₀)
    (hτ₁ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₁) :
    ∃ A : S → (V →L[ℝ] V)ˣ, Continuous A ∧
      ∀ x, (A x : V →L[ℝ] V) = transitionFDeriv I J τ₀ τ₁ x := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hcore (x : S) : (fun y ↦ τ₁ (y, 0)) =ᶠ[𝓝 x] fun y ↦ τ₀ (y, 0) :=
    Filter.Eventually.of_forall fun y ↦ (h₁.apply_zero y).trans (h₀.apply_zero y).symm
  -- The inverse is the transition fibre derivative in the other direction.
  refine ⟨fun x ↦ ⟨transitionFDeriv I J τ₀ τ₁ x, transitionFDeriv I J τ₁ τ₀ x,
    transitionFDeriv_comp_transitionFDeriv hn0 (hτ₀ _) (hτ₁ _) (hcore x),
    transitionFDeriv_comp_transitionFDeriv hn0 (hτ₁ _) (hτ₀ _) (hcore x).symm⟩,
    Units.continuous_iff.2 ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · exact continuous_transitionFDeriv hn h₀ h₁ hτ₀ hτ₁.contMDiff
  · exact continuous_transitionFDeriv hn h₁ h₀ hτ₁ hτ₀.contMDiff

end Transition

/-! ### Independence of the smooth tube -/

variable [I.Boundaryless] [CompactSpace S] [IsManifold I n S] [T2Space M]
  {f : S → M} {τ₀ τ₁ : S × V → M}

/-- **Independence of the Pontryagin–Thom collapse from a smooth tube.** Let `τ₀` and `τ₁` be
framed tubes around the same map `f : S → M`, from a compact boundaryless manifold `S` into a
Hausdorff manifold `M`, with `τ₀` a `C^n` local diffeomorphism and `τ₁` a `C^n` map, `n ≥ 1`.
If their transition fibre derivative is homotopic to the identity through a homotopy `B` of linear
automorphisms of `V`, their collapses are homotopic. -/
theorem IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv
    (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀) (hn : 1 ≤ n)
    (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₀) (hτ₁ : ContMDiff (I.prod 𝓘(ℝ, V)) J n τ₁)
    {B : unitInterval × S → (V →L[ℝ] V)ˣ} (hB : Continuous B)
    (hB₀ : ∀ x, (B (0, x) : V →L[ℝ] V) = transitionFDeriv I J τ₀ τ₁ x)
    (hB₁ : ∀ x, B (1, x) = 1) :
    (pontryaginThomCollapseMap h₁.isOpenEmbedding).Homotopic
      (pontryaginThomCollapseMap h₀.isOpenEmbedding) := by
  refine h₁.pontryaginThomCollapseMap_homotopic h₀ hB ?_ hB₁
  simpa only [hB₀] using hasTransitionFDeriv_transitionFDeriv hn h₀ h₁ hτ₀ hτ₁

/-- **Smooth tubes inducing the same framing have homotopic collapses.** If the transition fibre
derivative of two framed tubes around the same map, `τ₀` a `C^n` local diffeomorphism and `τ₁` a
`C^n` map with `n ≥ 1`, is the identity along the whole core, their collapses are homotopic. -/
theorem IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv_eq_id
    (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀) (hn : 1 ≤ n)
    (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, V)) J n τ₀) (hτ₁ : ContMDiff (I.prod 𝓘(ℝ, V)) J n τ₁)
    (hid : ∀ x, transitionFDeriv I J τ₀ τ₁ x = ContinuousLinearMap.id ℝ V) :
    (pontryaginThomCollapseMap h₁.isOpenEmbedding).Homotopic
      (pontryaginThomCollapseMap h₀.isOpenEmbedding) :=
  h₁.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv h₀ hn hτ₀ hτ₁ continuous_const
    (fun x ↦ (hid x).symm) fun _ ↦ rfl

/-- **Independence of the collapse onto the sphere from a smooth tube.** For `V = ℝᵏ`, two framed
tubes as in `TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_of_transitionFDeriv`, whose
transition fibre derivative is homotopic to the identity through linear automorphisms, have
homotopic collapses onto `Sᵏ`. -/
theorem IsFramedTube.pontryaginThomSphereMap_homotopic_of_transitionFDeriv {k : ℕ}
    {τ₀ τ₁ : S × (Fin k → ℝ) → M} (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀) (hn : 1 ≤ n)
    (hτ₀ : IsLocalDiffeomorph (I.prod 𝓘(ℝ, Fin k → ℝ)) J n τ₀)
    (hτ₁ : ContMDiff (I.prod 𝓘(ℝ, Fin k → ℝ)) J n τ₁)
    {B : unitInterval × S → ((Fin k → ℝ) →L[ℝ] (Fin k → ℝ))ˣ} (hB : Continuous B)
    (hB₀ : ∀ x, (B (0, x) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) = transitionFDeriv I J τ₀ τ₁ x)
    (hB₁ : ∀ x, B (1, x) = 1) (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (pontryaginThomSphereMap h₁.isOpenEmbedding s₀).Homotopic
      (pontryaginThomSphereMap h₀.isOpenEmbedding s₀) := by
  refine h₁.pontryaginThomSphereMap_homotopic h₀ hB ?_ hB₁ s₀
  simpa only [hB₀] using hasTransitionFDeriv_transitionFDeriv hn h₀ h₁ hτ₀ hτ₁

end TauCeti
