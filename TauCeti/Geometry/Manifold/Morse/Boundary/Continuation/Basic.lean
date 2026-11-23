/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ContinuationPotential
public import TauCeti.Geometry.Manifold.Morse.ConstantContinuation
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Prod

/-!
# The mod-two continuation map

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`. A continuation from
`f₀` to `f₁` is realized by a vector field `V` on `M × ℝ` whose time component is positive in the
open slab `M × (0, 1)`, such as the negative gradient of the continuation potential
`C h(t) + f_t(x)` (`TauCeti.continuationPotential`) for a large constant `C`. The critical points
of that potential in the slab are the points `(p, 0)` and `(q, 1)` for critical points `p` of `f₀`
and `q` of `f₁`, of indices `ind p + 1` and `ind q`. The **continuation map** from the mod-two
Morse chains of `f₀` to those of `f₁` sends `p` to the sum of the critical points `q` of `f₁` with
`ind q = ind p`, each weighted by the number of trajectories of `V` from `(p, 0)` to `(q, 1)` modulo
two; these are the trajectories that are rigid up to translation.

A trajectory from `(p, 0)` to `(q, 1)` is recorded by its point on the middle level `t = 1 / 2`
(`TauCeti.morseContinuationSlice`): the set of `x : M` through which, at time `0`, passes an
integral curve of `V` tending to `(p, 0)` at `-∞` and to `(q, 1)` at `+∞`. When the time component
of `V` is positive on this level, every such trajectory crosses it at exactly one time
(`IsMIntegralCurve.existsUnique_snd_eq`): the time component can cross the level only upwards.
So, up to translation of time, each trajectory passes through the level at time `0` in exactly one
way. When `V` is moreover `C¹`, so that an integral curve is determined by any one of
its points, the slice stands for the unparametrized trajectories. The coefficient
`TauCeti.morseContinuationCoeff` is the number of points of the slice modulo two when the indices
agree, and `0` otherwise, and `TauCeti.morseContinuationMap` is its linear extension.

The definitions take no hypothesis on `V`, so that they make sense for every field. They are the
counts of the continuation map only when the slice is finite, as it is between critical points of
equal index for smooth continuation fields between Morse–Smale pseudo-gradients satisfying the
transversality condition for continuations
(`TauCeti.IsTransverseContinuation.finite_morseContinuationSlice`). On an infinite slice the count
is a junk value, since `Set.ncard` is `0` on infinite sets.
That the continuation map is a chain map, which needs the compactification and gluing of the
one-dimensional continuation trajectory spaces, is not proved here.

**Continuation fields.** The fields of interest are the positive parameter fields of a
continuation from `X₀` to `X₁` (`TauCeti.IsContinuationField X₀ X₁ C V`): in the open slab their
time component is `C t (1 - t²)`, the negative gradient of the base potential
`TauCeti.intervalBasePotential C`, and their space component is `X₀` near `t = 0` and `X₁` near
`t = 1`. The constant continuation field is one, and so is the rescaled negative gradient of a
large-constant continuation potential (`TauCeti.isContinuationField_continuationRescaling_smul`),
whose trajectories are those of the gradient itself up to increasing changes of time
(`IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_continuationRescaling_smul`). Let `X₀` and
`X₁` be pseudo-gradients adapted to Morse functions `f₀` and `f₁`, and `C > 0`. Along an integral
curve `γ` of such a field which meets the open slab:

* the time component is a translate of the base trajectory `q = TauCeti.intervalBaseOrbit C`
  (`TauCeti.exists_snd_eq_intervalBaseOrbit`), so `γ` stays in the open slab
  and runs from `t = 0` to `t = 1`;
* near `-∞` the space component is an orbit of the flow of `X₀`, and near `+∞` one of `X₁`
  (`TauCeti.IsContinuationField.eventually_atBot_eqOn_flow`,
  `TauCeti.IsContinuationField.eventually_atTop_eqOn_flow`);
* hence `γ` tends to `(p, 0)` at `-∞` exactly when its space component eventually lies in the
  unstable manifold `W^u(p)` of `X₀`, and to `(q, 1)` at `+∞` exactly when it eventually lies in the
  stable manifold `W^s(q)` of `X₁` (`TauCeti.IsContinuationField.tendsto_atBot_iff`,
  `TauCeti.IsContinuationField.tendsto_atTop_iff`), and such critical points `p` and `q` exist
  (`TauCeti.IsContinuationField.exists_tendsto_atBot`,
  `TauCeti.IsContinuationField.exists_tendsto_atTop`).

So the points of the middle level through which an integral curve passes are covered by the slices
of the pairs of critical points (`TauCeti.IsContinuationField.iUnion_morseContinuationSlice`), and
a point lies in the slice of `(p, q)` exactly when its trajectory enters the slab along `W^u(p)`
and leaves it along `W^s(q)` (`TauCeti.IsContinuationField.mem_morseContinuationSlice_iff`). This
is the form in which the transversality condition for continuations compares the two end
manifolds. For a `C¹` field the slices of distinct pairs are disjoint
(`TauCeti.disjoint_morseContinuationSlice`).

For the constant path `f_t = f`, with a Morse–Smale pseudo-gradient `X` adapted to `f`, the
continuation field is the product field `(X x, C t (1 - t²))`
(`TauCeti.constantContinuationField`). Between critical points of equal index its only
trajectories run from `(p, 0)` to `(p, 1)`, and they are the translates of `s ↦ (p, q_C(s))`
(`IsMorseSmale.isMIntegralCurve_constantContinuationField_and_tendsto_iff_of_le` in the namespace
`TauCeti.IsAdaptedPseudoGradient`). So its slice from `p` to `p` is `{p}` and its other slices
between critical points of equal index are empty, and **the continuation map of a constant path
is the identity**
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseContinuationMap_constantContinuationField`).

## Main declarations

* `TauCeti.morseContinuationSlice`: the points on the level `t = 1 / 2` of the trajectories from
  `(p, 0)` to `(q, 1)`.
* `TauCeti.morseContinuationCoeff`: the coefficient of `q` in the continuation of `p`.
* `TauCeti.morseContinuationMap`: the mod-two continuation map.
* `TauCeti.IsContinuationField`: the positive parameter fields of a continuation.
* `TauCeti.isContinuationField_constantContinuationField` and
  `TauCeti.isContinuationField_continuationRescaling_smul`: the constant continuation field and
  the rescaled continuation field of a large-constant potential are continuation fields.
* `TauCeti.disjoint_morseContinuationSlice`: the slices of distinct pairs are disjoint.
* `TauCeti.exists_snd_eq_intervalBaseOrbit`: for any field whose time component in the open slab
  is `C t (1 - t²)`, the time component of a trajectory through the slab is a translate of the
  base trajectory.

In the namespace `TauCeti.IsContinuationField`:

* `snd_mem_Ioo`: a trajectory through the slab stays in it.
* `eventually_atBot_eqOn_flow`, `eventually_atTop_eqOn_flow`: near its ends a trajectory through
  the slab follows the flows of `X₀` and `X₁`.
* `tendsto_atBot_iff`, `tendsto_atTop_iff`, `exists_tendsto_atBot`, `exists_tendsto_atTop`: its
  limits are critical points of `f₀` at `t = 0` and of `f₁` at `t = 1`, read off the unstable and
  stable manifolds.
* `mem_morseContinuationSlice_iff`, `iUnion_morseContinuationSlice`: the slices in terms of the end
  dynamics, and the middle level as their union.

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseContinuationSlice_constantContinuationField_self`,
  `morseContinuationSlice_constantContinuationField_eq_empty`: the slices of a constant path.
* `morseContinuationCoeff_constantContinuationField`: its coefficients form the identity matrix.
* `morseContinuationMap_constantContinuationField`: its continuation map is the identity.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map) and §4, Exercise 1 (the
  continuation map of a constant path is the identity).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

section Definitions

variable {f₀ f₁ : M → ℝ} {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-- The points on the level `t = 1 / 2` of the trajectories of a vector field `V` on `M × ℝ` from
`(p, 0)` to `(q, 1)`: the points `x` such that an integral curve of `V` through `(x, 1 / 2)` at
time `0` tends to `(p, 0)` at `-∞` and to `(q, 1)` at `+∞`. When the time component of `V` is
positive on this level, every such trajectory crosses it exactly once
(`IsMIntegralCurve.existsUnique_snd_eq`); when `V` is moreover `C¹`, the set stands for the
unparametrized trajectories. -/
def morseContinuationSlice (V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) (p q : M) :
    Set M :=
  {x | ∃ γ : ℝ → M × ℝ, IsMIntegralCurve γ V ∧ γ 0 = (x, 1 / 2) ∧
    Tendsto γ atBot (𝓝 (p, 0)) ∧ Tendsto γ atTop (𝓝 (q, 1))}

/-- Membership in the middle-level slice of the continuation trajectories. -/
@[simp]
theorem mem_morseContinuationSlice {p q x : M} :
    x ∈ morseContinuationSlice V p q ↔
      ∃ γ : ℝ → M × ℝ, IsMIntegralCurve γ V ∧ γ 0 = (x, 1 / 2) ∧
        Tendsto γ atBot (𝓝 (p, 0)) ∧ Tendsto γ atTop (𝓝 (q, 1)) :=
  Iff.rfl

variable (f₀ f₁ V) in
/-- The coefficient of the critical point `q` of `f₁` in the continuation of the critical point
`p` of `f₀` along the field `V` on `M × ℝ`: the number of trajectories of `V` from `(p, 0)` to
`(q, 1)`, read on the level `t = 1 / 2`, modulo two when `ind p = ind q`, and `0` otherwise. It is
the trajectory count only when the slice `TauCeti.morseContinuationSlice V p q` is finite; an
infinite slice contributes `0`. -/
noncomputable def morseContinuationCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) : ZMod 2 :=
  if manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q then
    (morseContinuationSlice V p q).ncard
  else 0

/-- Between critical points of equal index, the continuation coefficient is the number of points
of the middle-level slice modulo two. -/
theorem morseContinuationCoeff_eq_ncard {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    morseContinuationCoeff f₀ f₁ V p q = ((morseContinuationSlice V p q).ncard : ZMod 2) := by
  simp [morseContinuationCoeff, hind]

/-- The continuation coefficient vanishes between critical points of different index: the
continuation map preserves the Morse index. -/
@[simp]
theorem morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    morseContinuationCoeff f₀ f₁ V p q = 0 := by
  simp [morseContinuationCoeff, hind]

/-- A nonzero continuation coefficient joins critical points of equal index. -/
theorem manifoldMorseIndex_eq_of_morseContinuationCoeff_ne_zero {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hpq : morseContinuationCoeff f₀ f₁ V p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q := by
  by_contra hind
  exact hpq (morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hind)

variable [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (f₀) in
/-- **The mod-two continuation map** along a vector field `V` on `M × ℝ`, from the mod-two Morse
chains of `f₀` to those of the Morse function `f₁`. It sends a critical point `p` of `f₀` to the
sum of the critical points `q` of `f₁` with `ind q = ind p`, each weighted by the number of
trajectories of `V` from `(p, 0)` to `(q, 1)` modulo two. -/
noncomputable def morseContinuationMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (morseContinuationCoeff f₀ f₁ V p) (toFinite _)

/-- The coefficient of `q` in the continuation of a chain `c` is the sum over the critical points
`p` of `c p` times the continuation coefficient `morseContinuationCoeff`. -/
theorem morseContinuationMap_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    morseContinuationMap f₀ hf₁ V c q =
      c.sum fun p a ↦ a * morseContinuationCoeff f₀ f₁ V p q := by
  simp [morseContinuationMap, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the continuation of `a • p` is `a` times the continuation
coefficient `morseContinuationCoeff`. -/
@[simp]
theorem morseContinuationMap_single_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) (a : ZMod 2) :
    morseContinuationMap f₀ hf₁ V (Finsupp.single p a) q =
      a * morseContinuationCoeff f₀ f₁ V p q := by
  rw [morseContinuationMap_apply, Finsupp.sum_single_index (zero_mul _)]

/-- A **continuation field** from `X₀` to `X₁` at rate `C`: a vector field `V` on `M × ℝ` whose time
component in the open slab `M × (0, 1)` is `C t (1 - t²)`, the negative gradient of the base
potential `TauCeti.intervalBasePotential C`, and whose space component is `X₀` near `t = 0` and
`X₁` near `t = 1`, at every point `x` at once. For `C > 0` the time component is positive in the
slab, so every trajectory crosses it upwards, while near its two ends the trajectories follow
`X₀` and `X₁`. The field outside the open slab plays no role.

The constant continuation field `(X x, C t (1 - t²))` is a continuation field from `X` to `X`
(`TauCeti.isContinuationField_constantContinuationField`). So is the rescaling `λ • W` of a field
`W` with time component `C t (1 - t²) - ∂ₜ f`, such as the negative gradient of the large-constant
continuation potential `C h(t) + f(x, t)` for a metric `dt² + g_t`, when the space component of `W`
is `X₀` near `t = 0` and `X₁` near `t = 1`
(`TauCeti.isContinuationField_continuationRescaling_smul`). -/
structure IsContinuationField (X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x) (C : ℝ)
    (V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) : Prop where
  /-- In the open slab, the time component is `C t (1 - t²)`. -/
  snd_eq : ∀ z : M × ℝ, z.2 ∈ Ioo 0 1 → (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2)
  /-- Near `t = 0`, the space component is `X₀`. -/
  eventually_fst_eq_left : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, (V (x, t) : E × ℝ).1 = X₀ x
  /-- Near `t = 1`, the space component is `X₁`. -/
  eventually_fst_eq_right : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x, (V (x, t) : E × ℝ).1 = X₁ x

end Definitions

/-! ### Continuation fields -/

section ContinuationField

variable {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-- **The constant continuation field is a continuation field** from `X` to `X`. -/
theorem isContinuationField_constantContinuationField (X : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (C : ℝ) : IsContinuationField X X C (constantContinuationField X C) where
  snd_eq z _ := constantContinuationField_snd X C z
  eventually_fst_eq_left := .of_forall fun t x ↦ constantContinuationField_fst X C (x, t)
  eventually_fst_eq_right := .of_forall fun t x ↦ constantContinuationField_fst X C (x, t)

/-- **The rescaled continuation field is a continuation field.** Let `f` be a function on `M × ℝ`,
independent of the time for `t < δ` and for `t > 1 - δ`, with `∂ₜ f ≠ C t (1 - t²)` in the open
slab, and let `W` be a vector field on `M × ℝ` whose time component is `C t (1 - t²) - ∂ₜ f` in the
open slab, as for the negative gradient of the continuation potential `C h(t) + f(x, t)` for any
metric `dt² + g_t`. If the space component of `W` is `X₀` near `t = 0` and `X₁` near `t = 1`, then
the rescaled field `λ • W`, for the factor `λ = C t (1 - t²) / (C t (1 - t²) - ∂ₜ f)` of
`TauCeti.continuationRescaling`, is a continuation field from `X₀` to `X₁`: rescaling makes the
time component `C t (1 - t²)` and leaves `W` unchanged near the ends, where `λ = 1`. -/
theorem isContinuationField_continuationRescaling_smul {f : M × ℝ → ℝ} {δ : ℝ}
    {W : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z} (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hne : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t ≠ C * t * (1 - t ^ 2))
    (hW : ∀ z : M × ℝ, z.2 ∈ Ioo 0 1 →
      (W z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hW₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, (W (x, t) : E × ℝ).1 = X₀ x)
    (hW₁ : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ x, (W (x, t) : E × ℝ).1 = X₁ x) :
    IsContinuationField X₀ X₁ C fun z ↦ continuationRescaling C f z • W z where
  snd_eq z hz := by
    -- The tangent space of `M × ℝ` is the product `E × ℝ`, on which the scalar action acts
    -- componentwise; the dependent tangent space types block a rewrite with `Prod.smul_snd`.
    calc _ = continuationRescaling C f z * (W z : E × ℝ).2 := rfl
      _ = C * z.2 * (1 - z.2 ^ 2) := by
        rw [hW z hz]
        exact continuationRescaling_mul_sub (.inl (hne z.1 z.2 hz))
  eventually_fst_eq_left := by
    filter_upwards [hW₀, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ x
    -- As for the time component, the scalar action on the tangent space of `M × ℝ` is read on the
    -- product `E × ℝ`, where it acts componentwise; `Prod.smul_fst` does not rewrite through the
    -- dependent tangent space type.
    change continuationRescaling C f (x, t) • (W (x, t) : E × ℝ).1 = X₀ x
    rw [continuationRescaling_eq_one hf₀ hf₁ fun h ↦ (not_le.2 htδ) h.1, one_smul, ht x]
  eventually_fst_eq_right := by
    filter_upwards [hW₁, nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : 1 - δ < 1))]
      with t ht htδ x
    -- The scalar action is read componentwise on `E × ℝ`, as above.
    change continuationRescaling C f (x, t) • (W (x, t) : E × ℝ).1 = X₁ x
    rw [continuationRescaling_eq_one hf₀ hf₁ fun h ↦ (not_le.2 htδ) h.2, one_smul, ht x]

end ContinuationField

/-! ### The continuation map of a constant path -/

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ} {p q : M}

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- Under the Morse–Smale condition, for `C > 0`, a critical point `p` and a point `q` with
`ind p ≤ ind q`, a point `x` lies on the middle level of a trajectory of the constant continuation
field from `(p, 0)` to `(q, 1)` exactly when `q = p` and `x = p`. -/
theorem mem_morseContinuationSlice_constantContinuationField_iff (hC : 0 < C)
    (hp : p ∈ criticalPoints 𝓘(ℝ, E) f)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ manifoldMorseIndex 𝓘(ℝ, E) f q) {x : M} :
    x ∈ morseContinuationSlice (constantContinuationField X C) p q ↔ q = p ∧ x = p := by
  have hiff := fun γ ↦
    h.isMIntegralCurve_constantContinuationField_and_tendsto_iff_of_le (γ := γ) hf hC hp hind
  constructor
  · rintro ⟨γ, hγ, hγ0, hγp, hγq⟩
    obtain ⟨hqp, τ, rfl⟩ := (hiff γ).1 ⟨hγ, hγp, hγq⟩
    exact ⟨hqp, (congrArg Prod.fst hγ0).symm⟩
  · rintro ⟨hqp, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
    obtain ⟨hγ, hγp, hγq⟩ := (hiff _).2 ⟨hqp, τ, rfl⟩
    exact ⟨_, hγ, by simp [hτ], hγp, hγq⟩

/-- **The slice of a constant path from a critical point to itself** is that point: for `C > 0`,
the only trajectory of the constant continuation field from `(p, 0)` to `(p, 1)` is
`s ↦ (p, q_C(s))`, up to translation, and it crosses the middle level at `(p, 1 / 2)`. -/
theorem morseContinuationSlice_constantContinuationField_self (hC : 0 < C)
    (hp : p ∈ criticalPoints 𝓘(ℝ, E) f) :
    morseContinuationSlice (constantContinuationField X C) p p = {p} := by
  ext x
  simp [h.mem_morseContinuationSlice_constantContinuationField_iff hf hC hp le_rfl]

/-- **The other slices of a constant path are empty**: for `C > 0`, there is no trajectory of the
constant continuation field from `(p, 0)` to `(q, 1)` for a critical point `p` and a point
`q ≠ p` with `ind p ≤ ind q`. -/
theorem morseContinuationSlice_constantContinuationField_eq_empty (hC : 0 < C)
    (hp : p ∈ criticalPoints 𝓘(ℝ, E) f)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ manifoldMorseIndex 𝓘(ℝ, E) f q) (hqp : q ≠ p) :
    morseContinuationSlice (constantContinuationField X C) p q = ∅ := by
  ext x
  simp [h.mem_morseContinuationSlice_constantContinuationField_iff hf hC hp hind, hqp]

open scoped Classical in
/-- **The continuation coefficients of a constant path form the identity matrix**: for `C > 0`,
the coefficient of `q` in the continuation of `p` along the constant continuation field is `1` if
`q = p` and `0` otherwise. -/
theorem morseContinuationCoeff_constantContinuationField (hC : 0 < C)
    (p q : criticalPoints 𝓘(ℝ, E) f) :
    morseContinuationCoeff f f (constantContinuationField X C) p q = if q = p then 1 else 0 := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q
  · rw [morseContinuationCoeff_eq_ncard hind]
    by_cases hqp : q = p
    · subst hqp
      simp [h.morseContinuationSlice_constantContinuationField_self hf hC q.property]
    · simp [h.morseContinuationSlice_constantContinuationField_eq_empty hf hC p.property hind.le
        (Subtype.coe_injective.ne hqp), hqp]
  · have hqp : q ≠ p := by
      rintro rfl
      exact hind rfl
    simp [morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hind, hqp]

/-- **The continuation map of a constant path is the identity** (Hutchings, §4, Exercise 1):
under the Morse–Smale condition, for `C > 0`, the mod-two continuation map along the constant
continuation field `(X x, C t (1 - t²))` is the identity of the mod-two Morse chains of `f`. -/
theorem morseContinuationMap_constantContinuationField (hC : 0 < C) :
    morseContinuationMap f hf (constantContinuationField X C) = LinearMap.id := by
  ext p q
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
    morseContinuationMap_single_apply, one_mul,
    h.morseContinuationCoeff_constantContinuationField hf hC, LinearMap.id_apply]
  classical
  rw [Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

end IsAdaptedPseudoGradient.IsMorseSmale

/-! ### Trajectories of continuation fields -/

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- **The time component of a trajectory through the slab is a translate of `q`.** For `C ≠ 0`,
along an integral curve of a field on `M × ℝ` whose time component in the open slab is
`C t (1 - t²)`, and which meets the open slab, the time component is `s ↦ q(s + τ)` for the base
trajectory `q = TauCeti.intervalBaseOrbit C` and a shift `τ`. -/
theorem exists_snd_eq_intervalBaseOrbit {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
    {γ : ℝ → M × ℝ} {s₀ : ℝ}
    (hsnd : ∀ z : M × ℝ, z.2 ∈ Ioo 0 1 → (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2))
    (hγ : IsMIntegralCurve γ V) (h₀ : (γ s₀).2 ∈ Ioo 0 1) (hC : C ≠ 0) :
    ∃ τ, ∀ s, (γ s).2 = intervalBaseOrbit C (s + τ) := by
  have hd := hγ.hasDerivAt_snd
  obtain ⟨τ, hτ⟩ := exists_eq_intervalBaseOrbit_of_hasDerivAt hC
    (continuous_iff_continuousAt.2 fun s ↦ (hd s).continuousAt)
    (fun s hs ↦ (hd s).congr_deriv (hsnd (γ s) hs)) h₀
  exact ⟨τ, congrFun hτ⟩

namespace IsContinuationField

variable {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z} {γ : ℝ → M × ℝ} {s₀ : ℝ}

section Time

variable (hV : IsContinuationField X₀ X₁ C V) (hγ : IsMIntegralCurve γ V)
  (h₀ : (γ s₀).2 ∈ Ioo 0 1)
include hV hγ h₀

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- **A trajectory meeting the open slab stays in it.** -/
theorem snd_mem_Ioo (hC : C ≠ 0) (s : ℝ) : (γ s).2 ∈ Ioo 0 1 := by
  obtain ⟨τ, hτ⟩ := exists_snd_eq_intervalBaseOrbit hV.snd_eq hγ h₀ hC
  rw [hτ]
  exact intervalBaseOrbit_mem_Ioo C _

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- For `C > 0`, the time component of a trajectory through the slab tends to `0` from above at
`-∞`. -/
theorem tendsto_snd_atBot (hC : 0 < C) : Tendsto (fun s ↦ (γ s).2) atBot (𝓝[>] 0) := by
  obtain ⟨τ, hτ⟩ := exists_snd_eq_intervalBaseOrbit hV.snd_eq hγ h₀ hC.ne'
  refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall fun s ↦ (hV.snd_mem_Ioo hγ h₀ hC.ne' s).1⟩
  rw [funext hτ]
  exact (tendsto_intervalBaseOrbit_atBot hC).comp (tendsto_atBot_add_const_right _ τ tendsto_id)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- For `C > 0`, the time component of a trajectory through the slab tends to `1` from below at
`+∞`. -/
theorem tendsto_snd_atTop (hC : 0 < C) : Tendsto (fun s ↦ (γ s).2) atTop (𝓝[<] 1) := by
  obtain ⟨τ, hτ⟩ := exists_snd_eq_intervalBaseOrbit hV.snd_eq hγ h₀ hC.ne'
  refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall fun s ↦ (hV.snd_mem_Ioo hγ h₀ hC.ne' s).2⟩
  rw [funext hτ]
  exact (tendsto_intervalBaseOrbit_atTop hC).comp (tendsto_atTop_add_const_right _ τ tendsto_id)

end Time

section Ends

variable (hV : IsContinuationField X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C) (hγ : IsMIntegralCurve γ V)
  (h₀ : (γ s₀).2 ∈ Ioo 0 1)

include hV hX₀ hC hγ h₀ in
/-- **Near `-∞` a trajectory through the slab follows `X₀`.** For `C > 0`, along an integral curve
`γ` of a continuation field which meets the open slab, for every sufficiently negative time `a`
the space component of `γ` is, up to time `a`, the orbit of `(γ a).1` under the flow of `X₀`. -/
theorem eventually_atBot_eqOn_flow :
    ∀ᶠ a in atBot, EqOn (fun s ↦ (γ s).1) (fun s ↦ hX₀.flow (s - a) (γ a).1) (Iic a) := by
  obtain ⟨b, hb⟩ := eventually_atBot.1
    ((hV.tendsto_snd_atBot hγ h₀ hC).eventually hV.eventually_fst_eq_left)
  have hc : IsMIntegralCurveOn (fun s ↦ (γ s).1) X₀ (Iio b) :=
    (hγ.isMIntegralCurveOn _).map_of_mfderiv_eq (f := Prod.fst) (fun _ _ ↦ mdifferentiableAt_fst)
      fun s hs ↦ by rw [mfderiv_fst]; exact hb s (le_of_lt hs) (γ s).1
  filter_upwards [eventually_lt_atBot b] with a hab
  exact hX₀.eqOn_flow_of_isMIntegralCurveOn_Iio hc hab

include hV hX₁ hC hγ h₀ in
/-- **Near `+∞` a trajectory through the slab follows `X₁`.** For `C > 0`, along an integral curve
`γ` of a continuation field which meets the open slab, for every sufficiently large time `b` the
space component of `γ` is, from time `b` on, the orbit of `(γ b).1` under the flow of `X₁`. -/
theorem eventually_atTop_eqOn_flow :
    ∀ᶠ b in atTop, EqOn (fun s ↦ (γ s).1) (fun s ↦ hX₁.flow (s - b) (γ b).1) (Ici b) := by
  obtain ⟨a, ha⟩ := eventually_atTop.1
    ((hV.tendsto_snd_atTop hγ h₀ hC).eventually hV.eventually_fst_eq_right)
  have hc : IsMIntegralCurveOn (fun s ↦ (γ s).1) X₁ (Ioi a) :=
    (hγ.isMIntegralCurveOn _).map_of_mfderiv_eq (f := Prod.fst) (fun _ _ ↦ mdifferentiableAt_fst)
      fun s hs ↦ by rw [mfderiv_fst]; exact ha s (le_of_lt hs) (γ s).1
  filter_upwards [eventually_gt_atTop a] with b hab
  exact hX₁.eqOn_flow_of_isMIntegralCurveOn_Ioi hc hab

include hV hX₀ hC hγ h₀ in
/-- **The backward limit of a trajectory through the slab.** For `C > 0`, an integral curve `γ`
of a continuation field from `X₀` which meets the open slab tends to `(p, 0)` at `-∞` exactly when
its space component eventually lies in the unstable manifold of `p` for the flow of `X₀`. -/
theorem tendsto_atBot_iff {p : M} :
    Tendsto γ atBot (𝓝 (p, 0)) ↔ ∀ᶠ a in atBot, (γ a).1 ∈ hX₀.flow.unstableSet p := by
  have hsnd := (hV.tendsto_snd_atBot hγ h₀ hC).mono_right nhdsWithin_le_nhds
  -- Up to a time `a`, the space component is the orbit of `(γ a).1`, shifted by `a`.
  have hev := hV.eventually_atBot_eqOn_flow hX₀ hC hγ h₀
  rw [nhds_prod_eq, tendsto_prod_iff']
  refine ⟨fun h ↦ hev.mono fun a ha ↦
    (Flow.tendsto_atBot_iff_mem_unstableSet_of_eqOn ha).1 h.1, fun h ↦ ⟨?_, hsnd⟩⟩
  obtain ⟨a, ha, hmem⟩ := (hev.and h).exists
  exact (Flow.tendsto_atBot_iff_mem_unstableSet_of_eqOn ha).2 hmem

include hV hX₁ hC hγ h₀ in
/-- **The forward limit of a trajectory through the slab.** For `C > 0`, an integral curve `γ`
of a continuation field to `X₁` which meets the open slab tends to `(q, 1)` at `+∞` exactly when
its space component eventually lies in the stable manifold of `q` for the flow of `X₁`. -/
theorem tendsto_atTop_iff {q : M} :
    Tendsto γ atTop (𝓝 (q, 1)) ↔ ∀ᶠ b in atTop, (γ b).1 ∈ hX₁.flow.stableSet q := by
  have hsnd := (hV.tendsto_snd_atTop hγ h₀ hC).mono_right nhdsWithin_le_nhds
  -- From a time `b` on, the space component is the orbit of `(γ b).1`, shifted by `b`.
  have hev := hV.eventually_atTop_eqOn_flow hX₁ hC hγ h₀
  rw [nhds_prod_eq, tendsto_prod_iff']
  refine ⟨fun h ↦ hev.mono fun b hb ↦
    (Flow.tendsto_atTop_iff_mem_stableSet_of_eqOn hb).1 h.1, fun h ↦ ⟨?_, hsnd⟩⟩
  obtain ⟨b, hb, hmem⟩ := (hev.and h).exists
  exact (Flow.tendsto_atTop_iff_mem_stableSet_of_eqOn hb).2 hmem

include hV hX₀ hC hγ h₀ in
/-- **A trajectory through the slab comes from a critical point of `f₀`.** For `C > 0` and a Morse
function `f₀`, an integral curve of a continuation field from a pseudo-gradient `X₀` adapted to
`f₀` which meets the open slab tends at `-∞` to `(p, 0)` for a critical point `p` of `f₀`. -/
theorem exists_tendsto_atBot (hf₀ : IsMorse 𝓘(ℝ, E) f₀) :
    ∃ p ∈ criticalPoints 𝓘(ℝ, E) f₀, Tendsto γ atBot (𝓝 (p, 0)) := by
  obtain ⟨a, ha⟩ := (hV.eventually_atBot_eqOn_flow hX₀ hC hγ h₀).exists
  obtain ⟨p, hp, hlim⟩ := hX₀.exists_tendsto_atBot hf₀ (γ a).1
  refine ⟨p, mem_criticalPoints_iff_mfderiv_eq_zero.2 hp,
    (hV.tendsto_atBot_iff hX₀ hC hγ h₀).2 ?_⟩
  -- Up to time `a`, the space component runs along the orbit of `(γ a).1`, which lies in `W^u(p)`.
  filter_upwards [Iic_mem_atBot a] with s hs
  have hγs : (γ s).1 = hX₀.flow (s - a) (γ a).1 := ha hs
  rw [hγs, Flow.apply_mem_unstableSet_iff]
  exact Flow.mem_unstableSet.2 hlim

include hV hX₁ hC hγ h₀ in
/-- **A trajectory through the slab goes to a critical point of `f₁`.** For `C > 0` and a Morse
function `f₁`, an integral curve of a continuation field to a pseudo-gradient `X₁` adapted to `f₁`
which meets the open slab tends at `+∞` to `(q, 1)` for a critical point `q` of `f₁`. -/
theorem exists_tendsto_atTop (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    ∃ q ∈ criticalPoints 𝓘(ℝ, E) f₁, Tendsto γ atTop (𝓝 (q, 1)) := by
  obtain ⟨b, hb⟩ := (hV.eventually_atTop_eqOn_flow hX₁ hC hγ h₀).exists
  obtain ⟨q, hq, hlim⟩ := hX₁.exists_tendsto_atTop hf₁ (γ b).1
  refine ⟨q, mem_criticalPoints_iff_mfderiv_eq_zero.2 hq,
    (hV.tendsto_atTop_iff hX₁ hC hγ h₀).2 ?_⟩
  -- From time `b` on, the space component runs along the orbit of `(γ b).1`, which lies in
  -- `W^s(q)`.
  filter_upwards [Ici_mem_atTop b] with s hs
  have hγs : (γ s).1 = hX₁.flow (s - b) (γ b).1 := hb hs
  rw [hγs, Flow.apply_mem_stableSet_iff]
  exact Flow.mem_stableSet.2 hlim

end Ends

section Slice

variable (hV : IsContinuationField X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C)
include hV hX₀ hX₁ hC

/-- **The slices in terms of the end dynamics.** For `C > 0`, a point `x` lies on the middle level
of a trajectory of a continuation field from `(p, 0)` to `(q, 1)` exactly when an integral curve
through `(x, 1 / 2)` eventually lies, near `-∞`, in the unstable manifold of `p` for `X₀`, and,
near `+∞`, in the stable manifold of `q` for `X₁`. -/
theorem mem_morseContinuationSlice_iff {x : M} :
    x ∈ morseContinuationSlice V p q ↔
      ∃ γ : ℝ → M × ℝ, IsMIntegralCurve γ V ∧ γ 0 = (x, 1 / 2) ∧
        (∀ᶠ a in atBot, (γ a).1 ∈ hX₀.flow.unstableSet p) ∧
          ∀ᶠ b in atTop, (γ b).1 ∈ hX₁.flow.stableSet q := by
  refine exists_congr fun γ ↦ and_congr_right fun hγ ↦ and_congr_right fun hγ0 ↦ ?_
  have h₀ : (γ 0).2 ∈ Ioo 0 1 := by rw [hγ0]; norm_num
  rw [hV.tendsto_atBot_iff hX₀ hC hγ h₀, hV.tendsto_atTop_iff hX₁ hC hγ h₀]

/-- **The middle level is covered by the slices.** For `C > 0` and Morse functions `f₀` and `f₁`,
the points `x` with an integral curve of a continuation field through `(x, 1 / 2)` are exactly the
points of the slices `TauCeti.morseContinuationSlice V p q` of the pairs of critical points `p` of
`f₀` and `q` of `f₁`: every trajectory through the slab runs between such critical points. -/
theorem iUnion_morseContinuationSlice (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f₀, ⋃ q ∈ criticalPoints 𝓘(ℝ, E) f₁,
        morseContinuationSlice V p q =
      {x | ∃ γ : ℝ → M × ℝ, IsMIntegralCurve γ V ∧ γ 0 = (x, 1 / 2)} := by
  ext x
  simp only [mem_iUnion, mem_morseContinuationSlice, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨p, -, q, -, γ, hγ, hγ0, -⟩
    exact ⟨γ, hγ, hγ0⟩
  · rintro ⟨γ, hγ, hγ0⟩
    have h₀ : (γ 0).2 ∈ Ioo 0 1 := by rw [hγ0]; norm_num
    obtain ⟨p, hp, hpγ⟩ := hV.exists_tendsto_atBot hX₀ hC hγ h₀ hf₀
    obtain ⟨q, hq, hqγ⟩ := hV.exists_tendsto_atTop hX₁ hC hγ h₀ hf₁
    exact ⟨p, hp, q, hq, γ, hγ, hγ0, hpγ, hqγ⟩

end Slice

end IsContinuationField

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
/-- **The slices of distinct pairs are disjoint** for a `C¹` vector field `V` on `M × ℝ`: through a
point of the middle level passes a single integral curve, which has a single limit at each end. -/
theorem disjoint_morseContinuationSlice [IsManifold 𝓘(ℝ, E) 1 M]
    {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
    (hV : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent 1
      fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
    {p q p' q' : M} (h : (p, q) ≠ (p', q')) :
    Disjoint (morseContinuationSlice V p q) (morseContinuationSlice V p' q') := by
  refine Set.disjoint_left.2 fun x ⟨γ, hγ, hγ0, hp, hq⟩ ⟨γ', hγ', hγ'0, hp', hq'⟩ ↦ h ?_
  obtain rfl := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hV hγ hγ'
    (hγ0.trans hγ'0.symm)
  have h₁ : (p, (0 : ℝ)) = (p', 0) := tendsto_nhds_unique hp hp'
  have h₂ : (q, (1 : ℝ)) = (q', 1) := tendsto_nhds_unique hq hq'
  simp only [Prod.mk.injEq] at h₁ h₂ ⊢
  exact ⟨h₁.1, h₂.1⟩

end TauCeti
