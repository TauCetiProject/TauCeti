/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TriangleBase
public import TauCeti.Geometry.Manifold.Morse.Boundary.Commutation
import TauCeti.Data.Set.Card
import TauCeti.Geometry.Manifold.IntegralCurve.Prod

/-!
# The mod-two triangle homotopy of a composition of continuations

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them. Continuations `f₀ ⇝ f₁`, `f₁ ⇝ f₂` and
`f₀ ⇝ f₂` along fields `V₀₁`, `V₁₂` and `V₀₂` on `M × ℝ` give mod-two continuation maps
`F₀₁`, `F₁₂` and `F₀₂` (`TauCeti.morseContinuationMap`). The composite `F₁₂ ∘ F₀₁` and the direct
map `F₀₂` are compared through a field `W` on `M × ℝ²` over the ordered triangle
`0 ≤ v ≤ u ≤ 1` (`TauCeti.triangleBase`). Its base component is the field `(a(u), a(v))` of the
ordered-triangle base, with `a(t) = C t (1 - t²)`, and its three faces carry the three
continuations: the edge `v = 0` carries `V₀₁`, the edge `u = 1` carries `V₁₂`, and the diagonal
`u = v` carries `V₀₂`. The statements below use no relation between `W` and the three fields, so
they take all four as independent fields. The vertices `(p, (0, 0))`, `(q, (1, 0))` and
`(r, (1, 1))`, for critical points `p` of `f₀`, `q` of `f₁` and `r` of `f₂`, are critical points of
index `ind p + 2`, `ind q + 1` and `ind r`.

**The triangle homotopy.** When the base component of `W` is the field of the ordered-triangle
base, a trajectory of `W` from `(p, (0, 0))` to `(r, (1, 1))` runs over a source-to-sink orbit of
the base, whose coordinates are two translates of one increasing orbit of
the interval base; so `u + v` increases from `0` to `2` along it, and the trajectory is recorded by
its point on the level `u + v = 1` of the triangle (`TauCeti.morseTriangleSlice`). These
trajectories are rigid up to translation when `ind r = ind p + 1`, and the homotopy
`H = TauCeti.morseTriangleMap f₀ hf₂ W`, of degree `+1`, counts them modulo two
(`TauCeti.morseTriangleCoeff`). As for the continuation map, the definitions take no hypothesis on
`W`; they are the trajectory counts only when the slices are finite, which is expected for
admissible fields under the transversality condition, and is not proved here.

**The ends of the one-dimensional triangle trajectory spaces.** When `ind r = ind p`, the
trajectories of `W` from `(p, (0, 0))` to `(r, (1, 1))` are expected to form a one-dimensional
space with four kinds of ends:

* breaking at the source (`TauCeti.morseSourceBrokenTriangleSet`): a trajectory of `X₀` from `p`
  to a critical point `p'` of index `ind p - 1`, followed by a triangle trajectory from `p'` to `r`;
* breaking at the target (`TauCeti.morseTargetBrokenTriangleSet`): a triangle trajectory from `p`
  to a critical point `r'` of index `ind p + 1`, followed by a trajectory of `X₂` from `r'` to `r`;
* breaking at the corner `(1, 0)` (`TauCeti.morseCornerBrokenTriangleSet`), the limit of the base
  orbits whose orbit parameter tends to `∞`: a continuation trajectory of `V₀₁` from `(p, 0)` to
  `(q', 1)` followed by one of `V₁₂` from `(q', 0)` to `(r, 1)`;
* the diagonal, the base orbit of orbit parameter `0`: a continuation trajectory of `V₀₂` from
  `(p, 0)` to `(r, 1)`.

When the slices are finite, these four sets count the `r`-coefficients of `H ∘ ∂₀`, `∂₂ ∘ H`,
`F₁₂ ∘ F₀₁` and `F₀₂` applied to `p`. So the triangle identity `∂₂ ∘ H + H ∘ ∂₀ = F₁₂ ∘ F₀₁ + F₀₂`
holds exactly when, between any two critical points of equal index, the four kinds of ends are
evenly many in total (`TauCeti.morseBoundary_comp_morseTriangleMap_add_eq_iff`). This is the
algebraic half of the composition theorem for continuation maps; the geometric half, that these
four sets are the ends of compact one-dimensional manifolds with boundary, needs the
compactification and gluing of the triangle trajectory spaces and is not proved here.

**The chain homotopy.** The homotopy raises the Morse index by one, so it restricts to maps from
the chains of index `i` to those of index `j`, zero unless `j = i + 1`
(`TauCeti.morseTriangleMapAt`). When `F₀₁` and `F₁₂` are chain maps and the triangle identity
holds, `F₀₂` is a chain map as well
(`TauCeti.morseBoundary_comp_morseContinuationMap_of_morseBoundary_comp_morseTriangleMap_add_eq`),
and the graded homotopy is a chain homotopy from the composite continuation morphism to the direct
one (`TauCeti.morseTriangleHomotopy`). By `Homotopy.homologyMap_eq`, the composite and the direct
continuation then induce the same map on mod-two Morse homology.

**Product fields.** The homotopy of a product field `(X x, Y b)` on `M × ℝ²`, for a Morse–Smale
pseudo-gradient `X` adapted to `f`, vanishes
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseTriangleMap_prodVectorField`): its trajectories
project to trajectories of `X`, which lower the index. With the constant continuation field on the
three faces, whose continuation maps are the identity
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseContinuationMap_constantContinuationField`),
the triangle identity then reads `0 = id ∘ id + id`, which holds over `ZMod 2`.

## Main declarations

* `TauCeti.morseTriangleSlice`: the points on the level `u + v = 1` of the triangle trajectories
  from `(p, (0, 0))` to `(r, (1, 1))`.
* `TauCeti.morseTriangleCoeff`, `TauCeti.morseTriangleMap`: the coefficients of the triangle
  homotopy, and the homotopy.
* `TauCeti.morseSourceBrokenTriangleSet`, `TauCeti.morseTargetBrokenTriangleSet`,
  `TauCeti.morseCornerBrokenTriangleSet`: the broken triangle trajectories.
* `TauCeti.morseTriangleMap_morseBoundary_single_apply`,
  `TauCeti.morseBoundary_morseTriangleMap_single_apply`,
  `TauCeti.morseContinuationMap_morseContinuationMap_single_apply`: the coefficients of `H ∘ ∂₀`,
  `∂₂ ∘ H` and `F₁₂ ∘ F₀₁` count broken triangle trajectories modulo two.
* `TauCeti.morseBoundary_comp_morseTriangleMap_add_eq_iff`: the triangle identity holds exactly
  when the ends of the triangle trajectory spaces are evenly many.
* `TauCeti.morseTriangleMapAt`: the triangle homotopy between the chains of index `i` and `j`.
* `TauCeti.morseTriangleHomotopy`: the chain homotopy from the composite continuation morphism to
  the direct one.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2, Lemma 4.3 (the composition of continuation maps is
  chain homotopic to the continuation map of the concatenated path).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open CategoryTheory Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

section Definitions

variable {f₀ f₂ : M → ℝ}
  {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}

/-- The points on the level `u + v = 1` of the ordered triangle `0 ≤ v ≤ u ≤ 1` of the
trajectories of a vector field `W` on `M × ℝ²` from `(p, (0, 0))` to `(r, (1, 1))`: the points
`z = (x, (u, v))` with `(u, v)` in the triangle and `u + v = 1` such that an integral curve of `W`
through `z` at time `0` tends to `(p, (0, 0))` at `-∞` and to `(r, (1, 1))` at `+∞`. When the base
component of `W` is the field of the ordered-triangle base, `u + v` increases along every such
trajectory, so it crosses this level once. -/
def morseTriangleSlice
    (W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z)
    (p r : M) : Set (M × WithLp 2 (ℝ × ℝ)) :=
  {z | z.2 ∈ triangleBase ∧ z.2.fst + z.2.snd = 1 ∧
    ∃ γ : ℝ → M × WithLp 2 (ℝ × ℝ), IsMIntegralCurve γ W ∧ γ 0 = z ∧
      Tendsto γ atBot (𝓝 (p, WithLp.toLp 2 (0, 0))) ∧
        Tendsto γ atTop (𝓝 (r, WithLp.toLp 2 (1, 1)))}

/-- Membership in the slice of the triangle trajectories. -/
@[simp]
theorem mem_morseTriangleSlice {p r : M} {z : M × WithLp 2 (ℝ × ℝ)} :
    z ∈ morseTriangleSlice W p r ↔
      z.2 ∈ triangleBase ∧ z.2.fst + z.2.snd = 1 ∧
        ∃ γ : ℝ → M × WithLp 2 (ℝ × ℝ), IsMIntegralCurve γ W ∧ γ 0 = z ∧
          Tendsto γ atBot (𝓝 (p, WithLp.toLp 2 (0, 0))) ∧
            Tendsto γ atTop (𝓝 (r, WithLp.toLp 2 (1, 1))) :=
  Iff.rfl

variable (f₀ f₂ W) in
/-- The coefficient of the critical point `r` of `f₂` in the triangle homotopy of the critical
point `p` of `f₀` along the field `W` on `M × ℝ²`: the number of trajectories of `W` from
`(p, (0, 0))` to `(r, (1, 1))` over the ordered triangle, read on the level `u + v = 1`, modulo two
when `ind r = ind p + 1`, and `0` otherwise. It is the trajectory count only when the slice
`TauCeti.morseTriangleSlice W p r` is finite; an infinite slice contributes `0`. -/
noncomputable def morseTriangleCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂) : ZMod 2 :=
  if manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 then
    (morseTriangleSlice W p r).ncard
  else 0

/-- When `ind r = ind p + 1`, the coefficient of the triangle homotopy is the number of points of
the slice modulo two. -/
theorem morseTriangleCoeff_eq_ncard {p : criticalPoints 𝓘(ℝ, E) f₀}
    {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    morseTriangleCoeff f₀ f₂ W p r = ((morseTriangleSlice W p r).ncard : ZMod 2) := by
  simp [morseTriangleCoeff, hind]

/-- The coefficient of the triangle homotopy vanishes unless `ind r = ind p + 1`: the homotopy
raises the Morse index by one. -/
@[simp]
theorem morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one
    {p : criticalPoints 𝓘(ℝ, E) f₀} {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₂ r ≠ manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    morseTriangleCoeff f₀ f₂ W p r = 0 := by
  simp [morseTriangleCoeff, hind]

/-- A nonzero coefficient of the triangle homotopy joins `p` to a critical point of index
`ind p + 1`. -/
theorem manifoldMorseIndex_eq_add_one_of_morseTriangleCoeff_ne_zero
    {p : criticalPoints 𝓘(ℝ, E) f₀} {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hpr : morseTriangleCoeff f₀ f₂ W p r ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 := by
  by_contra hind
  exact hpr (morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind)

variable [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (f₀) in
/-- **The mod-two triangle homotopy** along a vector field `W` on `M × ℝ²`, from the mod-two Morse
chains of `f₀` to those of the Morse function `f₂`. It sends a critical point `p` of `f₀` to the
sum of the critical points `r` of `f₂` with `ind r = ind p + 1`, each weighted by the number of
trajectories of `W` from `(p, (0, 0))` to `(r, (1, 1))` over the ordered triangle modulo two. As for
`morseTriangleCoeff`, this is the trajectory count only when the slice `morseTriangleSlice W p r`
is finite; an infinite slice contributes `0`. -/
noncomputable def morseTriangleMap (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z) :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) :=
  haveI := hf₂.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (morseTriangleCoeff f₀ f₂ W p) (toFinite _)

/-- The coefficient of `r` in the triangle homotopy of a chain `c` is the sum over the critical
points `p` of `c p` times the coefficient `morseTriangleCoeff`. -/
theorem morseTriangleMap_apply (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) (r : criticalPoints 𝓘(ℝ, E) f₂) :
    morseTriangleMap f₀ hf₂ W c r = c.sum fun p a ↦ a * morseTriangleCoeff f₀ f₂ W p r := by
  simp [morseTriangleMap, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `r` in the triangle homotopy of `a • p` is `a` times the coefficient
`morseTriangleCoeff`. -/
@[simp]
theorem morseTriangleMap_single_apply (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂) (a : ZMod 2) :
    morseTriangleMap f₀ hf₂ W (Finsupp.single p a) r = a * morseTriangleCoeff f₀ f₂ W p r := by
  rw [morseTriangleMap_apply, Finsupp.sum_single_index (zero_mul _)]

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}
  {V₀₁ V₁₂ V₀₂ : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-! ### Broken triangle trajectories -/

section BrokenSets

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₂ : IsAdaptedPseudoGradient f₂ X₂)

variable (f₂ W) in
/-- The triangle trajectories from `p` to `r` broken at the source: triples `(p', z₁, z₂)` of a
critical point `p'` of `f₀` whose Morse index lies one below those of `p` and of `r`, a point `z₁`
on the middle-level slice of the trajectories of `X₀` from `p` to `p'`, and a point `z₂` on the
level `u + v = 1` of the triangle trajectories of `W` from `(p', (0, 0))` to `(r, (1, 1))`. -/
def morseSourceBrokenTriangleSet (p r : M) :
    Set (criticalPoints 𝓘(ℝ, E) f₀ × M × (M × WithLp 2 (ℝ × ℝ))) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ morseTriangleSlice W x.1 r}

/-- Membership in the set of triangle trajectories broken at the source. -/
@[simp]
theorem mem_morseSourceBrokenTriangleSet {p r : M}
    {x : criticalPoints 𝓘(ℝ, E) f₀ × M × (M × WithLp 2 (ℝ × ℝ))} :
    x ∈ morseSourceBrokenTriangleSet f₂ W hX₀ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
          x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ morseTriangleSlice W x.1 r :=
  Iff.rfl

variable (f₀ W) in
/-- The triangle trajectories from `p` to `r` broken at the target: triples `(r', z₁, z₂)` of a
critical point `r'` of `f₂` whose Morse index lies one above those of `p` and of `r`, a point `z₁`
on the level `u + v = 1` of the triangle trajectories of `W` from `(p, (0, 0))` to `(r', (1, 1))`,
and a point `z₂` on the middle-level slice of the trajectories of `X₂` from `r'` to `r`. -/
def morseTargetBrokenTriangleSet (p r : M) :
    Set (criticalPoints 𝓘(ℝ, E) f₂ × (M × WithLp 2 (ℝ × ℝ)) × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 ∧
    x.2.1 ∈ morseTriangleSlice W p x.1 ∧ x.2.2 ∈ hX₂.morseTrajectorySlice x.1 r}

/-- Membership in the set of triangle trajectories broken at the target. -/
@[simp]
theorem mem_morseTargetBrokenTriangleSet {p r : M}
    {x : criticalPoints 𝓘(ℝ, E) f₂ × (M × WithLp 2 (ℝ × ℝ)) × M} :
    x ∈ morseTargetBrokenTriangleSet f₀ W hX₂ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 ∧
          x.2.1 ∈ morseTriangleSlice W p x.1 ∧ x.2.2 ∈ hX₂.morseTrajectorySlice x.1 r :=
  Iff.rfl

variable (f₀ f₁ f₂ V₀₁ V₁₂) in
/-- The triangle trajectories from `p` to `r` broken at the corner `(1, 0)` of the triangle:
triples `(q', z₁, z₂)` of a critical point `q'` of `f₁` whose Morse index equals those of `p` and
of `r`, a point `z₁` on the middle level of the continuation trajectories of `V₀₁` from `(p, 0)` to
`(q', 1)`, and a point `z₂` on the middle level of those of `V₁₂` from `(q', 0)` to `(r, 1)`. -/
def morseCornerBrokenTriangleSet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f₁ × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
    x.2.1 ∈ morseContinuationSlice V₀₁ p x.1 ∧ x.2.2 ∈ morseContinuationSlice V₁₂ x.1 r}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Membership in the set of triangle trajectories broken at the corner. -/
@[simp]
theorem mem_morseCornerBrokenTriangleSet {p r : M} {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M} :
    x ∈ morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
          x.2.1 ∈ morseContinuationSlice V₀₁ p x.1 ∧ x.2.2 ∈ morseContinuationSlice V₁₂ x.1 r :=
  Iff.rfl

end BrokenSets

/-! ### Counting broken triangle trajectories -/

section Count

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (h₁ : hX₁.IsMorseSmale)
  (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

include h₀ hf₀ in
/-- **Finitely many triangle trajectories broken at the source**, when the triangle slices into
`r` from critical points of index `ind r - 1` are finite. -/
theorem finite_morseSourceBrokenTriangleSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hW : ∀ p' : criticalPoints 𝓘(ℝ, E) f₀,
      manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1 →
        (morseTriangleSlice W p' r).Finite) :
    (morseSourceBrokenTriangleSet f₂ W hX₀ p r).Finite := by
  have := hf₀.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀) hW

include h₂ hf₂ in
/-- **Finitely many triangle trajectories broken at the target**, when the triangle slices out of
`p` to critical points of index `ind p + 1` are finite. -/
theorem finite_morseTargetBrokenTriangleSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hW : ∀ r' : criticalPoints 𝓘(ℝ, E) f₂,
      manifoldMorseIndex 𝓘(ℝ, E) f₂ r' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseTriangleSlice W p r').Finite) :
    (morseTargetBrokenTriangleSet f₀ W hX₂ p r).Finite := by
  have := hf₂.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem hW fun _ ↦ h₂.finite_morseTrajectorySlice hf₂

omit [FiniteDimensional ℝ E] [T2Space M] in
include hf₁ in
/-- **Finitely many triangle trajectories broken at the corner**, when the continuation slices of
`V₀₁` out of `p` and those of `V₁₂` into `r` between critical points of equal index are finite. -/
theorem finite_morseCornerBrokenTriangleSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hV₀₁ : ∀ q' : criticalPoints 𝓘(ℝ, E) f₁,
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q' →
        (morseContinuationSlice V₀₁ p q').Finite)
    (hV₁₂ : ∀ q' : criticalPoints 𝓘(ℝ, E) f₁,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
        (morseContinuationSlice V₁₂ q' r).Finite) :
    (morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).Finite := by
  have := hf₁.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem hV₀₁ hV₁₂

include h₀ in
/-- **`H ∘ ∂₀` counts triangle trajectories broken at the source.** When they are finitely many,
the `r`-coefficient of the triangle homotopy of the Morse boundary of `p` is the number of triangle
trajectories from `p` to `r` broken at the source, modulo two. -/
theorem morseTriangleMap_morseBoundary_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂) (hfin : (morseSourceBrokenTriangleSet f₂ W hX₀ p r).Finite) :
    morseTriangleMap f₀ hf₂ W (h₀.morseBoundary hf₀ (Finsupp.single p 1)) r =
      ((morseSourceBrokenTriangleSet f₂ W hX₀ p r).ncard : ZMod 2) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [morseTriangleMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    morseSourceBrokenTriangleSet]
  -- Sort the broken trajectories by their intermediate critical point `p'`. The index conditions
  -- and slice families are named because unification cannot read them off `hfin`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun p' : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (Q := fun p' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (morseTriangleSlice W · r)) (fun p' hind ↦ ?_)
    (fun p' hind ↦ ?_) (fun _ ↦ morseTriangleCoeff_eq_ncard)
    (fun _ ↦ morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one) hfin).symm
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_ncard hf₀ hind]
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₀ hind]

include h₂ in
/-- **`∂₂ ∘ H` counts triangle trajectories broken at the target.** When they are finitely many,
the `r`-coefficient of the Morse boundary of the triangle homotopy of `p` is the number of triangle
trajectories from `p` to `r` broken at the target, modulo two. -/
theorem morseBoundary_morseTriangleMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂) (hfin : (morseTargetBrokenTriangleSet f₀ W hX₂ p r).Finite) :
    h₂.morseBoundary hf₂ (morseTriangleMap f₀ hf₂ W (Finsupp.single p 1)) r =
      ((morseTargetBrokenTriangleSet f₀ W hX₂ p r).ncard : ZMod 2) := by
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, morseTargetBrokenTriangleSet]
  -- Sort the broken trajectories by their intermediate critical point `r'`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun r' : criticalPoints 𝓘(ℝ, E) f₂ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₂ r' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1)
    (Q := fun r' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₂ r' = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1)
    (A := (morseTriangleSlice W p ·)) (B := (hX₂.morseTrajectorySlice · r)) (fun r' hind ↦ ?_)
    (fun r' hind ↦ ?_) (fun _ ↦ h₂.morseBoundaryCoeff_eq_ncard hf₂)
    (fun _ ↦ h₂.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₂) hfin).symm
  · rw [morseTriangleMap_single_apply, one_mul, morseTriangleCoeff_eq_ncard hind]
  · rw [morseTriangleMap_single_apply, one_mul,
      morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **`F₁₂ ∘ F₀₁` counts triangle trajectories broken at the corner.** When they are finitely
many, the `r`-coefficient of the composite of the continuation maps along `V₀₁` and `V₁₂` applied to
`p` is the number of pairs of a continuation trajectory of `V₀₁` from `p` and one of `V₁₂` into `r`
through a common critical point of `f₁`, modulo two. -/
theorem morseContinuationMap_morseContinuationMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hfin : (morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).Finite) :
    morseContinuationMap f₁ hf₂ V₁₂ (morseContinuationMap f₀ hf₁ V₀₁ (Finsupp.single p 1)) r =
      ((morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).ncard : ZMod 2) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [morseContinuationMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    morseCornerBrokenTriangleSet]
  -- Sort the broken trajectories by their intermediate critical point `q'`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun q' : criticalPoints 𝓘(ℝ, E) f₁ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q')
    (Q := fun q' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (A := (morseContinuationSlice V₀₁ p ·)) (B := (morseContinuationSlice V₁₂ · r))
    (fun q' hind ↦ ?_) (fun q' hind ↦ ?_) (fun _ ↦ morseContinuationCoeff_eq_ncard)
    (fun _ ↦ morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne) hfin).symm
  · rw [morseContinuationMap_single_apply, one_mul, morseContinuationCoeff_eq_ncard hind]
  · rw [morseContinuationMap_single_apply, one_mul,
      morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hind]

include h₀ hf₀ h₂ in
/-- The triangle identity at the coefficient of `r` in the image of `p`: under the finiteness
hypotheses of `TauCeti.morseBoundary_comp_morseTriangleMap_add_eq_iff`, it holds exactly when the
ends of the triangle trajectory spaces from `p` to `r` are evenly many, or the indices differ. -/
private theorem morseTriangle_single_apply_eq_iff
    (hW : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseTriangleSlice W p r).Finite)
    (hV₀₁ : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (morseContinuationSlice V₀₁ p q).Finite)
    (hV₁₂ : ∀ (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
        (morseContinuationSlice V₁₂ q r).Finite)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂) :
    (h₂.morseBoundary hf₂ (morseTriangleMap f₀ hf₂ W (Finsupp.single p 1)) r +
      morseTriangleMap f₀ hf₂ W (h₀.morseBoundary hf₀ (Finsupp.single p 1)) r =
      morseContinuationMap f₁ hf₂ V₁₂ (morseContinuationMap f₀ hf₁ V₀₁ (Finsupp.single p 1)) r +
        morseContinuationMap f₀ hf₂ V₀₂ (Finsupp.single p 1) r) ↔
    (manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      Even ((morseSourceBrokenTriangleSet f₂ W hX₀ p r).ncard +
        (morseTargetBrokenTriangleSet f₀ W hX₂ p r).ncard +
          (morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).ncard +
            (morseContinuationSlice V₀₂ p r).ncard)) := by
  rw [morseBoundary_morseTriangleMap_single_apply h₂ hf₂ p r
      (finite_morseTargetBrokenTriangleSet h₂ hf₂ p r (hW p)),
    morseTriangleMap_morseBoundary_single_apply h₀ hf₀ hf₂ p r
      (finite_morseSourceBrokenTriangleSet h₀ hf₀ p r (hW · r)),
    morseContinuationMap_morseContinuationMap_single_apply hf₁ hf₂ p r
      (finite_morseCornerBrokenTriangleSet hf₁ p r (hV₀₁ p) (hV₁₂ · r)),
    morseContinuationMap_single_apply, one_mul]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  · rw [morseContinuationCoeff_eq_ncard hind, ← CharTwo.add_eq_zero,
      ← ZMod.natCast_eq_zero_iff_even]
    simp only [hind, forall_const]
    push_cast
    convert Iff.rfl using 2
    ring
  · -- Between critical points of different index all four counts vanish.
    have hS : morseSourceBrokenTriangleSet f₂ W hX₀ p r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseSourceBrokenTriangleSet] at hx; omega)
    have hT : morseTargetBrokenTriangleSet f₀ W hX₂ p r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseTargetBrokenTriangleSet] at hx; omega)
    have hK : morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseCornerBrokenTriangleSet] at hx; omega)
    simp [hS, hT, hK, hind]

include h₀ hf₀ h₂ in
/-- **The triangle identity holds exactly when the ends of the triangle trajectory spaces come in
pairs.** When the triangle slices between critical points whose indices differ by one and the
continuation slices of `V₀₁` and `V₁₂` between critical points of equal index are finite, the
mod-two triangle homotopy `H` satisfies `∂₂ ∘ H + H ∘ ∂₀ = F₁₂ ∘ F₀₁ + F₀₂` exactly when, between
any critical point `p` of `f₀` and any critical point `r` of `f₂` of the same index, the triangle
trajectories broken at the source, at the target and at the corner, together with the continuation
trajectories of `V₀₂` along the diagonal, are evenly many in total. -/
theorem morseBoundary_comp_morseTriangleMap_add_eq_iff
    (hW : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseTriangleSlice W p r).Finite)
    (hV₀₁ : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (morseContinuationSlice V₀₁ p q).Finite)
    (hV₁₂ : ∀ (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
        (morseContinuationSlice V₁₂ q r).Finite) :
    h₂.morseBoundary hf₂ ∘ₗ morseTriangleMap f₀ hf₂ W +
        morseTriangleMap f₀ hf₂ W ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂ ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
          Even ((morseSourceBrokenTriangleSet f₂ W hX₀ p r).ncard +
            (morseTargetBrokenTriangleSet f₀ W hX₂ p r).ncard +
              (morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).ncard +
                (morseContinuationSlice V₀₂ p r).ncard) := by
  -- Compare the two sides coefficientwise.
  simp_rw [← morseTriangle_single_apply_eq_iff h₀ hf₀ hf₁ h₂ hf₂ hW hV₀₁ hV₁₂]
  constructor
  · intro h0 p r
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- Over `ZMod 2`, both maps send `a • p` to `a` times their value at `p`.
    have := h0 p r
    rw [← Finsupp.smul_single_one]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul, this]

end Count

/-! ### The graded triangle homotopy and the chain homotopy -/

section Graded

variable (f₀) in
/-- **The graded mod-two triangle homotopy.** The `ZMod 2`-linear map from the free module on the
critical points of `f₀` of index `i` to the free module on the critical points of `f₂` of index `j`
sending `p` to the sum of the critical points `r`, each weighted by the number of triangle
trajectories of `W` from `(p, (0, 0))` to `(r, (1, 1))` modulo two. As for `morseTriangleCoeff`,
this is the trajectory count only when the slice `morseTriangleSlice W p r` is finite; an infinite
slice contributes `0`. It is the restriction of `morseTriangleMap`, and it vanishes unless
`j = i + 1` (`TauCeti.morseTriangleMapAt_eq_zero`). -/
noncomputable def morseTriangleMapAt (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z)
    (i j : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2) →ₗ[ZMod 2]
      ({r : criticalPoints 𝓘(ℝ, E) f₂ // manifoldMorseIndex 𝓘(ℝ, E) f₂ r = j} →₀ ZMod 2) :=
  Finsupp.lsubtypeDomain {r : criticalPoints 𝓘(ℝ, E) f₂ | manifoldMorseIndex 𝓘(ℝ, E) f₂ r = j} ∘ₗ
    morseTriangleMap f₀ hf₂ W ∘ₗ Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val

variable (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `r` in the graded triangle homotopy of a chain `c` is the sum over the
critical points `p` of index `i` of `c p` times the coefficient `morseTriangleCoeff`. -/
theorem morseTriangleMapAt_apply {i j : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2)
    (r : {r : criticalPoints 𝓘(ℝ, E) f₂ // manifoldMorseIndex 𝓘(ℝ, E) f₂ r = j}) :
    morseTriangleMapAt f₀ hf₂ W i j c r = c.sum fun p a ↦ a * morseTriangleCoeff f₀ f₂ W p r := by
  rw [morseTriangleMapAt, LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.lmapDomain_apply,
    morseTriangleMap_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `r` in the graded triangle homotopy of `a • p` is `a` times the coefficient
`morseTriangleCoeff`. -/
@[simp]
theorem morseTriangleMapAt_single_apply {i j : ℕ}
    (p : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i}) (a : ZMod 2)
    (r : {r : criticalPoints 𝓘(ℝ, E) f₂ // manifoldMorseIndex 𝓘(ℝ, E) f₂ r = j}) :
    morseTriangleMapAt f₀ hf₂ W i j (Finsupp.single p a) r =
      a * morseTriangleCoeff f₀ f₂ W p r := by
  rw [morseTriangleMapAt_apply, Finsupp.sum_single_index (zero_mul _)]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded triangle homotopy raises the index by one**: from the chains of index `i` to
those of index `j` it vanishes unless `j = i + 1`. -/
theorem morseTriangleMapAt_eq_zero {i j : ℕ} (hij : j ≠ i + 1) :
    morseTriangleMapAt f₀ hf₂ W i j = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
  rw [morseTriangleMapAt_single_apply, morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one
    (by rw [p.property, r.property]; exact hij), mul_zero, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded and total triangle homotopies agree.** Including the chains of index `i` and of
index `i + 1` into all Morse chains intertwines the graded triangle homotopy with the total one
`morseTriangleMap`: the triangle homotopy of a chain of index `i` is a chain of index `i + 1`. -/
@[simp]
theorem mapDomain_morseTriangleMapAt {i : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2) :
    (morseTriangleMapAt f₀ hf₂ W i (i + 1) c).mapDomain Subtype.val =
      morseTriangleMap f₀ hf₂ W (c.mapDomain Subtype.val) := by
  ext r
  by_cases hr : manifoldMorseIndex 𝓘(ℝ, E) f₂ r = i + 1
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨r, hr⟩
  · -- Outside index `i + 1` both sides vanish: the left side by support, the right side because
    -- every coefficient of the triangle homotopy from index `i` to `r` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨q, hq⟩ ↦ hr (hq ▸ q.property),
      morseTriangleMap_apply,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul .., Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one (by grind), mul_zero]

end Graded

section Homotopy

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (h₁ : hX₁.IsMorseSmale)
  (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

include h₀ hf₀ h₁ hf₁ h₂ hf₂ in
/-- **The direct continuation is a chain map when the composite is and the triangle identity
holds.** If the continuation maps `F₀₁` and `F₁₂` commute with the Morse boundaries and the triangle
homotopy `H` satisfies `∂₂ ∘ H + H ∘ ∂₀ = F₁₂ ∘ F₀₁ + F₀₂`, then `F₀₂` commutes with the Morse
boundaries. -/
theorem morseBoundary_comp_morseContinuationMap_of_morseBoundary_comp_morseTriangleMap_add_eq
    (hcomm₀₁ : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ =
      morseContinuationMap f₀ hf₁ V₀₁ ∘ₗ h₀.morseBoundary hf₀)
    (hcomm₁₂ : h₂.morseBoundary hf₂ ∘ₗ morseContinuationMap f₁ hf₂ V₁₂ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ h₁.morseBoundary hf₁)
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseTriangleMap f₀ hf₂ W +
        morseTriangleMap f₀ hf₂ W ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) :
    h₂.morseBoundary hf₂ ∘ₗ morseContinuationMap f₀ hf₂ V₀₂ =
      morseContinuationMap f₀ hf₂ V₀₂ ∘ₗ h₀.morseBoundary hf₀ := by
  -- Solve the triangle identity for `F₀₂` and use `∂ ∘ ∂ = 0` on both sides.
  have hF : ∀ c, morseContinuationMap f₀ hf₂ V₀₂ c =
      h₂.morseBoundary hf₂ (morseTriangleMap f₀ hf₂ W c) +
        morseTriangleMap f₀ hf₂ W (h₀.morseBoundary hf₀ c) -
          morseContinuationMap f₁ hf₂ V₁₂ (morseContinuationMap f₀ hf₁ V₀₁ c) := fun c ↦ by
    have := LinearMap.congr_fun hH c
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at this
    rw [this, add_sub_cancel_left]
  refine LinearMap.ext fun c ↦ ?_
  have h01 := LinearMap.congr_fun hcomm₀₁ c
  have h12 := LinearMap.congr_fun hcomm₁₂ (morseContinuationMap f₀ hf₁ V₀₁ c)
  simp only [LinearMap.comp_apply] at h01 h12 ⊢
  rw [hF, hF, map_sub, map_add, h₂.morseBoundary_morseBoundary, h₀.morseBoundary_morseBoundary,
    map_zero, h12, h01, zero_add, add_zero]

include h₀ hf₀ hf₁ h₂ hf₂ in
/-- The graded triangle identity in degree `0`, where there is no boundary out of the chains. -/
private theorem morseContinuationMapAt_comp_morseContinuationMapAt_zero
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseTriangleMap f₀ hf₂ W +
        morseTriangleMap f₀ hf₂ W ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) :
    morseContinuationMapAt f₁ hf₂ V₁₂ 0 ∘ₗ morseContinuationMapAt f₀ hf₁ V₀₁ 0 =
      h₂.morseBoundaryAt hf₂ 0 ∘ₗ morseTriangleMapAt f₀ hf₂ W 0 1 +
        morseContinuationMapAt f₀ hf₂ V₀₂ 0 := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hH (Finsupp.single p.val 1)
  have h0 := h₀.morseBoundary_mapDomain_eq_zero_of_index_zero hf₀ (Finsupp.single p 1)
  simp only [Finsupp.mapDomain_single] at h0
  simp only [LinearMap.add_apply, LinearMap.comp_apply, h0, map_zero, add_zero] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, mapDomain_morseContinuationMapAt, h₂.mapDomain_morseBoundaryAt hf₂,
    mapDomain_morseTriangleMapAt, Finsupp.mapDomain_single, this, add_assoc,
    ZModModule.add_self, add_zero]

include h₀ hf₀ hf₁ h₂ hf₂ in
/-- The graded triangle identity in degree `n + 1`. -/
private theorem morseContinuationMapAt_comp_morseContinuationMapAt_succ
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseTriangleMap f₀ hf₂ W +
        morseTriangleMap f₀ hf₂ W ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) (n : ℕ) :
    morseContinuationMapAt f₁ hf₂ V₁₂ (n + 1) ∘ₗ morseContinuationMapAt f₀ hf₁ V₀₁ (n + 1) =
      morseTriangleMapAt f₀ hf₂ W n (n + 1) ∘ₗ h₀.morseBoundaryAt hf₀ n +
        h₂.morseBoundaryAt hf₂ (n + 1) ∘ₗ morseTriangleMapAt f₀ hf₂ W (n + 1) (n + 2) +
          morseContinuationMapAt f₀ hf₂ V₀₂ (n + 1) := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hH (Finsupp.single p.val 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, mapDomain_morseContinuationMapAt, h₂.mapDomain_morseBoundaryAt hf₂,
    h₀.mapDomain_morseBoundaryAt hf₀, mapDomain_morseTriangleMapAt, Finsupp.mapDomain_single]
  rw [add_comm (morseTriangleMap f₀ hf₂ W _), this, add_assoc, ZModModule.add_self,
    add_zero]

/-- **The triangle homotopy.** When the continuation maps `F₀₁` and `F₁₂` commute with the Morse
boundaries and the mod-two triangle homotopy `H` of `W` satisfies
`∂₂ ∘ H + H ∘ ∂₀ = F₁₂ ∘ F₀₁ + F₀₂`, the graded triangle homotopy is a chain homotopy from the
composite of the continuation morphisms of `F₀₁` and `F₁₂` to the continuation morphism of `F₀₂`.
So the composite and the direct continuation induce the same map on mod-two Morse homology
(`Homotopy.homologyMap_eq`). -/
noncomputable def morseTriangleHomotopy
    (hcomm₀₁ : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ =
      morseContinuationMap f₀ hf₁ V₀₁ ∘ₗ h₀.morseBoundary hf₀)
    (hcomm₁₂ : h₂.morseBoundary hf₂ ∘ₗ morseContinuationMap f₁ hf₂ V₁₂ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ h₁.morseBoundary hf₁)
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseTriangleMap f₀ hf₂ W +
        morseTriangleMap f₀ hf₂ W ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) :
    Homotopy
      (morseContinuationHom h₀ hf₀ h₁ hf₁ hcomm₀₁ ≫ morseContinuationHom h₁ hf₁ h₂ hf₂ hcomm₁₂)
      (morseContinuationHom h₀ hf₀ h₂ hf₂
        (morseBoundary_comp_morseContinuationMap_of_morseBoundary_comp_morseTriangleMap_add_eq
          h₀ hf₀ h₁ hf₁ h₂ hf₂ hcomm₀₁ hcomm₁₂ hH)) where
  hom i j := ModuleCat.ofHom (morseTriangleMapAt f₀ hf₂ W i j)
  zero i j hij := by
    rw [morseTriangleMapAt_eq_zero hf₂ fun h ↦ hij (by simp [h]), ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  comm i := by
    -- The components `ModuleCat.ofHom (morseTriangleMapAt ...)` have source and target
    -- `ModuleCat.of (ZMod 2) (... →₀ ZMod 2)`, while `dNext` and `prevD` expect the terms
    -- `(morseComplex _).X i` of the Morse complexes; these agree only up to unfolding
    -- `morseComplex` (`IsAdaptedPseudoGradient.IsMorseSmale.morseComplex_X`), so plain `rw`
    -- cannot match them and `erw` is needed.
    rcases i with _ | n
    · erw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      rw [zero_add, h₂.morseComplex_d hf₂, HomologicalComplex.comp_f, morseContinuationHom_f,
        morseContinuationHom_f, morseContinuationHom_f]
      -- The terms of the Morse complexes are not syntactically the free modules on which the
      -- graded maps act, so compare the underlying linear maps.
      apply ModuleCat.hom_ext
      exact
        morseContinuationMapAt_comp_morseContinuationMapAt_zero h₀ hf₀ hf₁ h₂ hf₂ hH
    · erw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      rw [h₀.morseComplex_d hf₀, h₂.morseComplex_d hf₂, HomologicalComplex.comp_f,
        morseContinuationHom_f, morseContinuationHom_f, morseContinuationHom_f]
      apply ModuleCat.hom_ext
      exact
        morseContinuationMapAt_comp_morseContinuationMapAt_succ h₀ hf₀ hf₁ h₂ hf₂ hH n

/-- The components of the triangle homotopy are the graded triangle homotopies. -/
@[simp]
theorem morseTriangleHomotopy_hom
    (hcomm₀₁ : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ =
      morseContinuationMap f₀ hf₁ V₀₁ ∘ₗ h₀.morseBoundary hf₀)
    (hcomm₁₂ : h₂.morseBoundary hf₂ ∘ₗ morseContinuationMap f₁ hf₂ V₁₂ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ h₁.morseBoundary hf₁)
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseTriangleMap f₀ hf₂ W +
        morseTriangleMap f₀ hf₂ W ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) (i j : ℕ) :
    (morseTriangleHomotopy h₀ hf₀ h₁ hf₁ h₂ hf₂ hcomm₀₁ hcomm₁₂ hH).hom i j =
      ModuleCat.ofHom (morseTriangleMapAt f₀ hf₂ W i j) :=
  (rfl)

end Homotopy

/-! ### Product fields -/

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Product fields have no triangle trajectories raising the index.** Under the Morse–Smale
condition, for every field `Y` on `ℝ²`, the product field `(X x, Y b)` on `M × ℝ²` has no
trajectory from `(p, (0, 0))` to `(r, (1, 1))` when `ind p < ind r`: its space component is a
trajectory of `X` from `p` to `r`, which lowers the index. -/
theorem morseTriangleSlice_prodVectorField_eq_empty
    (Y : (b : WithLp 2 (ℝ × ℝ)) → TangentSpace 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) b) {p r : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p < manifoldMorseIndex 𝓘(ℝ, E) f r) :
    morseTriangleSlice (Manifold.prodVectorField X Y) p r = ∅ := by
  refine eq_empty_of_forall_notMem fun z ⟨_, _, γ, hγ, _, hp, hr⟩ ↦ ?_
  have hpr : p ≠ r := by rintro rfl; exact hind.false
  obtain ⟨hy, -⟩ := hX.mem_unstableSet_inter_stableSet_of_isMIntegralCurve
    (Manifold.isMIntegralCurve_prodVectorField_iff.1 hγ).1
    ((continuous_fst.tendsto _).comp hp) ((continuous_fst.tendsto _).comp hr)
  exact (h.manifoldMorseIndex_lt hf hpr ⟨_, hy⟩).not_gt hind

include h hf in
/-- **The triangle homotopy of a product field vanishes.** Under the Morse–Smale condition, for
every field `Y` on `ℝ²`, the mod-two triangle homotopy of the product field `(X x, Y b)` on
`M × ℝ²` is zero. -/
@[simp]
theorem morseTriangleMap_prodVectorField
    (Y : (b : WithLp 2 (ℝ × ℝ)) → TangentSpace 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) b) :
    morseTriangleMap f hf (Manifold.prodVectorField X Y) = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
  rw [morseTriangleMap_single_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f r = manifoldMorseIndex 𝓘(ℝ, E) f p + 1
  · rw [morseTriangleCoeff_eq_ncard hind,
      h.morseTriangleSlice_prodVectorField_eq_empty hf Y (by omega), ncard_empty, Nat.cast_zero,
      mul_zero]
  · rw [morseTriangleCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind, mul_zero]

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
