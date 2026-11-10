/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
public import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Orientations of unstable manifolds, transported by the flow

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f`, and `x` a critical point of index `k`. The integral Morse complex counts
trajectories with signs, and those signs are read off orientations of the unstable manifolds
`W^u(x)`, chosen independently at each critical point. Such an orientation must be compatible with
the flow: the derivative of each time-`t` map carries the orientation of the tangent space of
`W^u(x)` at `y` to the orientation at the image of `y`. This file constructs these orientations.

A **flow-equivariant parametrization** of `W^u(x)`
(`TauCeti.IsAdaptedPseudoGradient.UnstableParametrization`) is an injective immersion `P : L → M`
of a vector space of dimension `k` onto `W^u(x)` which carries the scaling `v ↦ e^t • v` to the
time-`t` map of the flow. One exists at every critical point
(`TauCeti.IsAdaptedPseudoGradient.exists_unstableParametrization`): it is the parametrization of the
stable manifold of `x` for the reversed field `-X` read off a Morse chart, in which the flow is
linear. The derivative of `P` at `v` is an isomorphism of `L` onto the tangent space of `W^u(x)` at
`P v`, the span of the tangent cone `TauCeti.mtangentConeAt`
(`TauCeti.IsAdaptedPseudoGradient.UnstableParametrization.span_mtangentConeAt_eq_range_mfderiv`).
So an orientation of `L` orients every tangent space of `W^u(x)`
(`TauCeti.IsAdaptedPseudoGradient.UnstableParametrization.orientation`).

Differentiating the equivariance, the derivative of the time-`t` map sends `dP_v u` to
`dP_{e^t v} (e^t u)`
(`TauCeti.IsAdaptedPseudoGradient.UnstableParametrization.mfderiv_flow_mfderiv`).
Hence it maps the tangent spaces of `W^u(x)` onto one another
(`TauCeti.IsAdaptedPseudoGradient.unstableTangentFlowEquiv`), and since the scaling by `e^t > 0`
preserves orientations, it preserves the induced orientations. Every orientation of the tangent
space of `W^u(x)` at `x` therefore extends to a flow-invariant orientation of all the tangent spaces
of `W^u(x)` (`TauCeti.IsAdaptedPseudoGradient.exists_orientation_unstableSet`). No orientation of
`M` is involved.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.UnstableParametrization`: flow-equivariant parametrizations of
  unstable manifolds, and `TauCeti.IsAdaptedPseudoGradient.exists_unstableParametrization`, their
  existence.
* `TauCeti.IsAdaptedPseudoGradient.unstableTangentFlowEquiv`: the derivative of the time-`t` map of
  the flow, as an isomorphism between tangent spaces of `W^u(x)`.
* `TauCeti.IsAdaptedPseudoGradient.UnstableParametrization.orientation`: the orientation of the
  tangent spaces of `W^u(x)` induced by an orientation of the parameter space.
* `TauCeti.IsAdaptedPseudoGradient.UnstableParametrization.map_orientation_unstableTangentFlowEquiv`
  : it is invariant under the flow.
* `TauCeti.IsAdaptedPseudoGradient.UnstableParametrization.orientation_neg`: reversing the
  orientation of the parameter space reverses it.
* `TauCeti.IsAdaptedPseudoGradient.exists_orientation_unstableSet`: every orientation of `W^u(x)`
  at `x` extends to a flow-invariant orientation of `W^u(x)`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2, where orientations of the descending manifolds orient the
  spaces of trajectories and define the signs of the integral Morse differential.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 (the parametrization of stable manifolds through a Morse chart, in which the flow is
  linear).
-/

public section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M}

namespace IsAdaptedPseudoGradient

/-- A **flow-equivariant parametrization of the unstable manifold** `W^u(x)` of a critical point
`x` by a real vector space `L`: an injective immersion `L → M` onto `W^u(x)`, with `L` of dimension
the Morse index of `x`, which carries the scaling `v ↦ e^t • v` of `L` to the time-`t` map of the
flow. -/
structure UnstableParametrization (hX : IsAdaptedPseudoGradient f X) (x : M) (L : Type*)
    [NormedAddCommGroup L] [NormedSpace ℝ L] where
  /-- The parametrization itself. -/
  toFun : L → M
  isImmersion : IsImmersion 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ toFun
  injective : Injective toFun
  range_eq : range toFun = hX.flow.unstableSet x
  finrank_eq : Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f x
  flow_apply : ∀ (t : ℝ) (v : L), hX.flow t (toFun v) = toFun (Real.exp t • v)

variable (hX : IsAdaptedPseudoGradient f X)

namespace UnstableParametrization

variable {hX} {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  (P : hX.UnstableParametrization x L)

instance : CoeFun (hX.UnstableParametrization x L) (fun _ ↦ L → M) :=
  ⟨toFun⟩

/-- Two parametrizations with the same underlying map are equal. -/
@[ext]
theorem ext {Q : hX.UnstableParametrization x L} (h : ∀ v, P v = Q v) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

/-- The parametrization takes values in the unstable manifold. -/
theorem mem_unstableSet (v : L) : P v ∈ hX.flow.unstableSet x :=
  P.range_eq ▸ mem_range_self v

/-- The parametrization sends `0` to the critical point: `P 0` is a rest point of the flow lying on
`W^u(x)`, so its constant backward orbit converges to `x`. -/
theorem map_zero : P 0 = x := by
  have hfix : ∀ t, hX.flow t (P 0) = P 0 := fun t ↦ by
    rw [P.flow_apply, smul_zero]
  have h := Flow.mem_unstableSet.1 (P.mem_unstableSet 0)
  simp only [hfix] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- The derivative of the parametrization is injective. -/
theorem mfderiv_injective (v : L) : Injective (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P v) :=
  P.isImmersion.mfderiv_injective (by simp) v

/-- **The tangent space of the unstable manifold.** At `P v`, the tangent space of `W^u(x)` is the
image of the derivative of the parametrization at `v`. -/
theorem span_mtangentConeAt_eq_range_mfderiv (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (v : L) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) (P v)) =
      LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P v).toLinearMap := by
  -- The image of the derivative is tangent to `W^u(x)`, and both spaces have dimension `ind x`.
  have hle : @LE.le (Submodule ℝ E) _
      (LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P v).toLinearMap)
      (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) (P v))) := by
    rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span (R := ℝ) (M := E) (mfderiv_apply_mem_mtangentConeAt
      (mdifferentiableAt_of_mfderiv_injective (P.mfderiv_injective v))
      (Eventually.of_forall P.mem_unstableSet) u)
  refine (Submodule.eq_of_le_of_finrank_eq (K := ℝ) (V := E) hle ?_).symm
  exact (LinearMap.finrank_range_of_inj (P.mfderiv_injective v)).trans (P.finrank_eq.trans
    (hX.finrank_span_mtangentConeAt_unstableSet hf hx (P.mem_unstableSet v)).symm)

/-- **The flow acts on tangent vectors of `W^u(x)` through the parametrization.** The derivative of
the time-`t` map of the flow sends `dP_v u` to `dP_{e^t v} (e^t u)`. -/
theorem mfderiv_flow_mfderiv (t : ℝ) (v u : L) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) (P v) (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P v u) =
      mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P (Real.exp t • v) (Real.exp t • u) := by
  have hP (w : L) : MDifferentiableAt 𝓘(ℝ, L) 𝓘(ℝ, E) P w :=
    mdifferentiableAt_of_mfderiv_injective (P.mfderiv_injective w)
  have hcomp : hX.flow t ∘ P = P ∘ fun w : L ↦ Real.exp t • w := funext (P.flow_apply t)
  have hs : MDifferentiableAt 𝓘(ℝ, L) 𝓘(ℝ, L) (fun w : L ↦ Real.exp t • w) v :=
    (contDiff_const_smul (n := 1) (Real.exp t)).contMDiff.mdifferentiableAt one_ne_zero
  have h1 := mfderiv_comp_apply (I' := 𝓘(ℝ, E)) v
    ((hX.contMDiff_flow_apply t).mdifferentiableAt (by simp)) (hP v) u
  have h2 := mfderiv_comp_apply (I' := 𝓘(ℝ, L)) v (hP (Real.exp t • v)) hs u
  have hsd : mfderiv 𝓘(ℝ, L) 𝓘(ℝ, L) (fun w : L ↦ Real.exp t • w) v u = Real.exp t • u := by
    have h : HasMFDerivAt 𝓘(ℝ, L) 𝓘(ℝ, L) (fun w : L ↦ Real.exp t • w) v
        (Real.exp t • ContinuousLinearMap.id ℝ L) :=
      ((hasFDerivAt_id (𝕜 := ℝ) v).const_smul (Real.exp t)).hasMFDerivAt
    -- The tangent spaces of `L` are `L` itself, so this is the evaluation of `e^t • id`.
    rw [h.mfderiv]
    rfl
  rw [hcomp] at h1
  rw [← h1, h2, hsd]

end UnstableParametrization

/-- **Flow-equivariant parametrizations of unstable manifolds exist.** At a critical point `x` of a
Morse function, `W^u(x)` has a flow-equivariant parametrization by a subspace of the model space.
It is the parametrization of the stable manifold of `x` for the reversed pseudo-gradient `-X`,
read off a Morse chart (`TauCeti.IsAdaptedPseudoGradient.exists_stableParam`). -/
theorem exists_unstableParametrization (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E, Nonempty (hX.UnstableParametrization x L) := by
  obtain ⟨φ, δ, hemb, hrange, -, -, hsmul⟩ := (hX.neg hf).exists_stableParam
    (hf.neg.contMDiff.mdifferentiable (by simp)) (mfderiv_neg_eq_zero_iff.2 hx)
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have hL := φ.finrank_stableSubspace_add_manifoldMorseIndex
  refine ⟨φ.stableSubspace, ⟨⟨(hX.neg hf).stableParam φ δ, hemb.isImmersion,
    hemb.isEmbedding.injective, ?_, by omega, fun t v ↦ ?_⟩⟩⟩
  · rw [hrange, hX.unstableSet_eq_stableSet_neg hf]
  · -- The flow of `-X` at time `-t` is the flow of `X` at time `t`.
    have h := hsmul v (-t)
    rw [neg_neg, hX.neg_flow hf, Flow.reverse_apply, neg_neg] at h
    exact h.symm

/-- **The flow preserves the tangent spaces of an unstable manifold.** The derivative of the
time-`t` map of the flow at a point `y` of `W^u(x)` maps the tangent space of `W^u(x)` at `y` onto
its tangent space at the image point. -/
theorem map_mfderiv_flow_span_mtangentConeAt_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (t : ℝ) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y)).map
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y).toLinearMap =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) (hX.flow t y)) := by
  obtain ⟨L, ⟨P⟩⟩ := hX.exists_unstableParametrization hf hx
  obtain ⟨v, rfl⟩ : y ∈ range P := P.range_eq ▸ hy
  -- Through `P`, the derivative of the flow is the derivative of `P` after a positive scaling.
  rw [P.span_mtangentConeAt_eq_range_mfderiv hf hx]
  conv_rhs => rw [P.flow_apply, P.span_mtangentConeAt_eq_range_mfderiv hf hx]
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨Real.exp t • u, (P.mfderiv_flow_mfderiv t v u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨(Real.exp t)⁻¹ • u, rfl⟩, ?_⟩
    exact (P.mfderiv_flow_mfderiv t v _).trans (congrArg (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P _)
      (smul_inv_smul₀ (Real.exp_pos t).ne' u))

/-- The derivative of the time-`t` map of the flow, as an isomorphism from the tangent space of
`W^u(x)` at `y` to its tangent space at the image point. -/
noncomputable def unstableTangentFlowEquiv (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (t : ℝ) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) ≃ₗ[ℝ]
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) (hX.flow t y)) :=
  (Submodule.equivMapOfInjective _ (hX.injective_mfderiv_flow t y) _).trans
    (LinearEquiv.ofEq _ _ (hX.map_mfderiv_flow_span_mtangentConeAt_unstableSet hf hx t hy))

/-- The isomorphism `unstableTangentFlowEquiv` is the derivative of the time-`t` map of the flow. -/
@[simp]
theorem coe_unstableTangentFlowEquiv_apply (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (t : ℝ) {y : M} (hy : y ∈ hX.flow.unstableSet x)
    (w : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y)) :
    (hX.unstableTangentFlowEquiv hf hx t hy w : E) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y (w : E) :=
  (rfl)

namespace UnstableParametrization

variable {hX} {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  (P : hX.UnstableParametrization x L) (hf : IsMorse 𝓘(ℝ, E) f)
  (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)

/-- The parameter `invFun P y` of a point `y` of `W^u(x)` is sent to `y`. -/
private theorem apply_invFun {y : M} (hy : y ∈ hX.flow.unstableSet x) : P (invFun P y) = y :=
  invFun_eq (P.range_eq ▸ hy : y ∈ range P)

/-- The derivative of `P` at the parameter of a point `y` of `W^u(x)`, as an isomorphism of `L`
onto the tangent space of `W^u(x)` at `y`. -/
noncomputable def tangentEquiv {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    L ≃ₗ[ℝ] Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) :=
  (LinearEquiv.ofInjective (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P (invFun P y)).toLinearMap
    (P.mfderiv_injective _)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [← P.span_mtangentConeAt_eq_range_mfderiv hf hx, P.apply_invFun hy]))

/-- At `y = P v`, the isomorphism `P.tangentEquiv` is the derivative of `P` at `v`. -/
theorem coe_tangentEquiv_apply {y : M} (hy : y ∈ hX.flow.unstableSet x) {v : L} (hv : P v = y)
    (u : L) : (P.tangentEquiv hf hx hy u : E) = mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P v u := by
  subst hv
  -- The parameter of `P v` is `v`, since `P` is injective. The tangent spaces of `M` at all
  -- points are `E`, and `show E from` makes the function of the parameter non-dependent.
  exact congrArg (fun w ↦ (show E from mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) P w u))
    (leftInverse_invFun P.injective v)

variable {ι : Type*}

/-- **The orientation of the unstable manifold induced by a parametrization.** An orientation `o`
of the parameter space `L` orients the tangent space of `W^u(x)` at each of its points `y`, by
transporting `o` along the derivative of `P` at the parameter of `y`. -/
noncomputable def orientation (o : Orientation ℝ L ι) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    Orientation ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y)) ι :=
  Orientation.map ι (P.tangentEquiv hf hx hy) o

theorem orientation_def (o : Orientation ℝ L ι) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    P.orientation hf hx o hy = Orientation.map ι (P.tangentEquiv hf hx hy) o :=
  (rfl)

/-- Reversing the orientation of the parameter space reverses the induced orientation of the
unstable manifold. -/
@[simp]
theorem orientation_neg (o : Orientation ℝ L ι) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    P.orientation hf hx (-o) hy = -P.orientation hf hx o hy :=
  Orientation.map_neg _ o

/-- **The induced orientation of the unstable manifold is invariant under the flow.** The
derivative of the time-`t` map of the flow carries the orientation of the tangent space of `W^u(x)`
at `y` to its orientation at the image point. Through `P`, this derivative is the derivative of `P`
after the scaling by the positive number `e^t`, which preserves orientations. -/
theorem map_orientation_unstableTangentFlowEquiv [Finite ι] (o : Orientation ℝ L ι) (t : ℝ)
    {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    Orientation.map ι (hX.unstableTangentFlowEquiv hf hx t hy) (P.orientation hf hx o hy) =
      P.orientation hf hx o (Flow.isInvariant_unstableSet hX.flow x t hy) := by
  set u := Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  obtain ⟨v, rfl⟩ : y ∈ range P := P.range_eq ▸ hy
  have he : (P.tangentEquiv hf hx hy).trans (hX.unstableTangentFlowEquiv hf hx t hy) =
      (LinearEquiv.smulOfUnit u).trans
        (P.tangentEquiv hf hx (Flow.isInvariant_unstableSet hX.flow x t hy)) := by
    ext w
    simp only [LinearEquiv.trans_apply, coe_unstableTangentFlowEquiv_apply,
      P.coe_tangentEquiv_apply hf hx hy rfl,
      P.coe_tangentEquiv_apply hf hx _ (P.flow_apply t v).symm, P.mfderiv_flow_mfderiv]
    -- Both sides apply `dP_{e^t v}` to `e^t • w`, the scaling read in `L` and in its tangent
    -- space `TangentSpace 𝓘(ℝ, L) (e^t • v)`, which is `L` itself.
    rfl
  rw [orientation_def, orientation_def, ← Orientation.map_trans, he, Orientation.map_trans,
    Orientation.map_smulOfUnit_of_pos u (Real.exp_pos t)]

end UnstableParametrization

/-- **Orientations of unstable manifolds.** Every orientation `o₀` of the tangent space of `W^u(x)`
at a critical point `x` of a Morse function extends to an orientation of the tangent spaces of
`W^u(x)` at all of its points which is invariant under the flow: the derivative of each time-`t`
map carries the orientation at `y` to the orientation at the image of `y`. -/
theorem exists_orientation_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) {ι : Type*} [Finite ι]
    (o₀ : Orientation ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) x)) ι) :
    ∃ o : ∀ y ∈ hX.flow.unstableSet x,
        Orientation ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y)) ι,
      o x (hX.self_mem_unstableSet hx) = o₀ ∧
      ∀ (t : ℝ) (y : M) (hy : y ∈ hX.flow.unstableSet x),
        Orientation.map ι (hX.unstableTangentFlowEquiv hf hx t hy) (o y hy) =
          o (hX.flow t y) (Flow.isInvariant_unstableSet hX.flow x t hy) := by
  obtain ⟨L, ⟨P⟩⟩ := hX.exists_unstableParametrization hf hx
  set e := P.tangentEquiv hf hx (hX.self_mem_unstableSet hx)
  refine ⟨fun y hy ↦ P.orientation hf hx (Orientation.map ι e.symm o₀) hy, ?_,
    fun t y hy ↦ P.map_orientation_unstableTangentFlowEquiv hf hx _ t hy⟩
  dsimp only
  rw [UnstableParametrization.orientation_def, ← Orientation.map_trans,
    LinearEquiv.symm_trans_self, Orientation.map_refl, Equiv.refl_apply]

end IsAdaptedPseudoGradient

end TauCeti
