/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ConstantContinuation

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
counts of the continuation map only when the slice is finite, as it is expected to be for admissible
fields under the transversality condition for continuations; that finiteness theorem is not proved
here. On an infinite slice the count is a junk value, since `Set.ncard` is `0` on infinite sets.
That the continuation map is a chain map, which needs the compactification and gluing of the
one-dimensional continuation trajectory spaces, is not proved here.

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

end Definitions

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

end TauCeti
