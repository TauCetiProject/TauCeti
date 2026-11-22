/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TriangleBase
public import TauCeti.Geometry.Manifold.Morse.Boundary.DegreeOneHomotopy
import TauCeti.Data.Set.Card

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
`H = TauCeti.morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W)`, of degree `+1`, counts them modulo
two. As for the continuation map, the definitions take no hypothesis on `W`; they are the
trajectory counts only when the slices are finite, which is expected for admissible fields under
the transversality condition, and is not proved here.

**The ends of the one-dimensional triangle trajectory spaces.** When `ind r = ind p`, the
trajectories of `W` from `(p, (0, 0))` to `(r, (1, 1))` are expected to form a one-dimensional
space with four kinds of ends:

* breaking at the source (`TauCeti.morseSourceBrokenDegreeOneSet` of the triangle slices): a
  trajectory of `X₀` from `p` to a critical point `p'` of index `ind p - 1`, followed by a triangle
  trajectory from `p'` to `r`;
* breaking at the target (`TauCeti.morseTargetBrokenDegreeOneSet` of the triangle slices): a
  triangle trajectory from `p` to a critical point `r'` of index `ind p + 1`, followed by a
  trajectory of `X₂` from `r'` to `r`;
* breaking at the corner `(1, 0)` (`TauCeti.morseCornerBrokenTriangleSet`), the limit of the base
  orbits whose orbit parameter tends to `∞`: a continuation trajectory of `V₀₁` from `(p, 0)` to
  `(q', 1)` followed by one of `V₁₂` from `(q', 0)` to `(r, 1)`;
* the diagonal, the base orbit of orbit parameter `0`: a continuation trajectory of `V₀₂` from
  `(p, 0)` to `(r, 1)`.

When the slices are finite, these four sets count the `r`-coefficients of `H ∘ ∂₀`, `∂₂ ∘ H`,
`F₁₂ ∘ F₀₁` and `F₀₂` applied to `p`. So the triangle identity `∂₂ ∘ H + H ∘ ∂₀ = F₁₂ ∘ F₀₁ + F₀₂`
holds exactly when, between any two critical points of equal index, the four kinds of ends are
evenly many in total (`TauCeti.morseBoundary_comp_morseDegreeOneMap_morseTriangleSlice_add_eq_iff`).
This is the algebraic half of the composition theorem for continuation maps; the geometric half,
that these four sets are the ends of compact one-dimensional manifolds with boundary, needs the
compactification and gluing of the triangle trajectory spaces and is not proved here.

**The chain homotopy.** When `F₀₁` and `F₁₂` are chain maps and the triangle identity holds,
`F₀₂` is a chain map as well (`LinearMap.comp_eq_comp_of_comp_add_comp_eq_add`), and the graded
homotopy (`TauCeti.morseDegreeOneMapAt`) is a chain homotopy from the composite continuation
morphism to the direct one (`TauCeti.morseTriangleHomotopy`). By `Homotopy.homologyMap_eq`, the
composite and the direct continuation then induce the same map on mod-two Morse homology.

**Product fields.** The homotopy of a product field `(X x, Y b)` on `M × ℝ²`, for a Morse–Smale
pseudo-gradient `X` adapted to `f`, vanishes
(`morseDegreeOneMap_morseTriangleSlice_prodVectorField`, in the namespace
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`): its trajectories project to trajectories of `X`,
which lower the index. With the constant
continuation field on the three faces, whose continuation maps are the identity
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseContinuationMap_constantContinuationField`),
the triangle identity then reads `0 = id ∘ id + id`, which holds over `ZMod 2`.

## Main declarations

* `TauCeti.morseTriangleSlice`: the points on the level `u + v = 1` of the triangle trajectories
  from `(p, (0, 0))` to `(r, (1, 1))`.
* `TauCeti.morseCornerBrokenTriangleSet`: the triangle trajectories broken at the corner.
* `TauCeti.morseContinuationMap_morseContinuationMap_single_apply`: the coefficients of
  `F₁₂ ∘ F₀₁` count triangle trajectories broken at the corner modulo two.
* `TauCeti.morseBoundary_comp_morseDegreeOneMap_morseTriangleSlice_add_eq_iff`: the triangle
  identity holds exactly when the ends of the triangle trajectory spaces are evenly many.
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

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}
  {V₀₁ V₁₂ V₀₂ : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-! ### Triangle trajectories broken at the corner -/

section Corner

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

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

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

end Corner

/-! ### The triangle identity and the chain homotopy -/

section Homotopy

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (h₁ : hX₁.IsMorseSmale)
  (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

include h₀ hf₀ h₂ in
/-- **The triangle identity holds exactly when the ends of the triangle trajectory spaces come in
pairs.** When the triangle slices between critical points whose indices differ by one and the
continuation slices of `V₀₁` and `V₁₂` between critical points of equal index are finite, the
mod-two triangle homotopy `H` satisfies `∂₂ ∘ H + H ∘ ∂₀ = F₁₂ ∘ F₀₁ + F₀₂` exactly when, between
any critical point `p` of `f₀` and any critical point `r` of `f₂` of the same index, the triangle
trajectories broken at the source, at the target and at the corner, together with the continuation
trajectories of `V₀₂` along the diagonal, are evenly many in total. -/
theorem morseBoundary_comp_morseDegreeOneMap_morseTriangleSlice_add_eq_iff
    (hW : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₂ r = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseTriangleSlice W p r).Finite)
    (hV₀₁ : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (morseContinuationSlice V₀₁ p q).Finite)
    (hV₁₂ : ∀ (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
        (morseContinuationSlice V₁₂ q r).Finite) :
    h₂.morseBoundary hf₂ ∘ₗ morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W) +
        morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W) ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂ ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
          Even ((morseSourceBrokenDegreeOneSet f₂ (morseTriangleSlice W) hX₀ p r).ncard +
            (morseTargetBrokenDegreeOneSet f₀ (morseTriangleSlice W) hX₂ p r).ncard +
              (morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).ncard +
                (morseContinuationSlice V₀₂ p r).ncard) := by
  -- The corner and the diagonal count the further ends.
  rw [morseBoundary_comp_morseDegreeOneMap_add_eq_iff h₀ hf₀ h₂ hf₂ hW (N := fun p r ↦
    (morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r).ncard +
      (morseContinuationSlice V₀₂ p r).ncard) fun p r ↦ ?_]
  · simp only [add_assoc]
  rw [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.add_apply,
    morseContinuationMap_morseContinuationMap_single_apply hf₁ hf₂ p r
      (finite_morseCornerBrokenTriangleSet hf₁ p r (hV₀₁ p) (hV₁₂ · r)),
    morseContinuationMap_single_apply, one_mul]
  split_ifs with hind
  · rw [morseContinuationCoeff_eq_ncard hind, Nat.cast_add]
  · -- Between critical points of different index there are no corner-broken trajectories.
    have hK : morseCornerBrokenTriangleSet f₀ f₁ f₂ V₀₁ V₁₂ p r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseCornerBrokenTriangleSet] at hx; omega)
    rw [hK, ncard_empty, Nat.cast_zero, zero_add,
      morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hind]

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
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W) +
        morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W) ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) :
    Homotopy
      (morseContinuationHom h₀ hf₀ h₁ hf₁ hcomm₀₁ ≫ morseContinuationHom h₁ hf₁ h₂ hf₂ hcomm₁₂)
      (morseContinuationHom h₀ hf₀ h₂ hf₂
        (LinearMap.comp_eq_comp_of_comp_add_comp_eq_add (h₀.morseBoundary_comp_morseBoundary hf₀)
          (h₂.morseBoundary_comp_morseBoundary hf₂)
          (LinearMap.comp_comp_eq_comp_comp_of_comp_eq hcomm₁₂.symm hcomm₀₁) hH)) :=
  morseDegreeOneHomotopy h₀ hf₀ h₂ hf₂ _
    (φAt := fun n ↦ morseContinuationMapAt f₁ hf₂ V₁₂ n ∘ₗ morseContinuationMapAt f₀ hf₁ V₀₁ n)
    (fun n ↦ by
      rw [HomologicalComplex.comp_f, morseContinuationHom_f, morseContinuationHom_f]
      exact (ModuleCat.ofHom_comp _ _).symm)
    (fun _ _ ↦ by
      rw [LinearMap.comp_apply, mapDomain_morseContinuationMapAt, mapDomain_morseContinuationMapAt,
        LinearMap.comp_apply])
    (LinearMap.comp_comp_eq_comp_comp_of_comp_eq hcomm₁₂.symm hcomm₀₁) hH

/-- The components of the triangle homotopy are the graded triangle homotopies. -/
@[simp]
theorem morseTriangleHomotopy_hom
    (hcomm₀₁ : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ =
      morseContinuationMap f₀ hf₁ V₀₁ ∘ₗ h₀.morseBoundary hf₀)
    (hcomm₁₂ : h₂.morseBoundary hf₂ ∘ₗ morseContinuationMap f₁ hf₂ V₁₂ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ h₁.morseBoundary hf₁)
    (hH : h₂.morseBoundary hf₂ ∘ₗ morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W) +
        morseDegreeOneMap f₀ hf₂ (morseTriangleSlice W) ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₁ hf₂ V₁₂ ∘ₗ morseContinuationMap f₀ hf₁ V₀₁ +
        morseContinuationMap f₀ hf₂ V₀₂) (i j : ℕ) :
    (morseTriangleHomotopy h₀ hf₀ h₁ hf₁ h₂ hf₂ hcomm₀₁ hcomm₁₂ hH).hom i j =
      ModuleCat.ofHom (morseDegreeOneMapAt f₀ hf₂ (morseTriangleSlice W) i j) :=
  morseDegreeOneHomotopy_hom h₀ hf₀ h₂ hf₂ _ _ _ _ hH i j

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
    morseTriangleSlice (Manifold.prodVectorField X Y) p r = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, _, _, hγ, _, hp, hr⟩ ↦
    (h.manifoldMorseIndex_le_of_isMIntegralCurve_prodVectorField hf hγ hp hr).not_gt hind

include h hf in
/-- **The triangle homotopy of a product field vanishes.** Under the Morse–Smale condition, for
every field `Y` on `ℝ²`, the mod-two triangle homotopy of the product field `(X x, Y b)` on
`M × ℝ²` is zero. -/
@[simp]
theorem morseDegreeOneMap_morseTriangleSlice_prodVectorField
    (Y : (b : WithLp 2 (ℝ × ℝ)) → TangentSpace 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) b) :
    morseDegreeOneMap f hf (morseTriangleSlice (Manifold.prodVectorField X Y)) = 0 :=
  morseDegreeOneMap_eq_zero_of_slice_eq_empty hf fun _ _ hind ↦
    h.morseTriangleSlice_prodVectorField_eq_empty hf Y (by omega)

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
