/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Commutation
import TauCeti.Data.Set.Card
import TauCeti.Geometry.Manifold.IntegralCurve.Prod

/-!
# The mod-two digon homotopy of a family of continuations

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them. Two continuations from `f₀` to `f₁` with the same
ends, along fields `V 0` and `V 1` on `M × ℝ`, give mod-two continuation maps `F⁰` and `F¹`
(`TauCeti.morseContinuationMap`). When the two continuations are homotopic with fixed ends, they are
joined by a family of fields `V λ` on `M × ℝ`, for `λ ∈ [0, 1]`; for instance the continuation
fields of a homotopy of paths `f_t^λ` with fixed endpoint germs. This one-parameter family of
continuations is the *digon* with vertices `f₀` and `f₁` and edges `V 0` and `V 1`. The statements
below use no relation between the fields `V λ` and the pseudo-gradients, so they take the family
`V : ℝ → (fields on M × ℝ)` as arbitrary data, of which only the parameters `λ ∈ [0, 1]` are read.

**The digon homotopy.** A *digon trajectory* from `p` to `q` is a pair `(λ, γ)` of a parameter
`λ ∈ [0, 1]` and a trajectory `γ` of `V λ` from `(p, 0)` to `(q, 1)`. For a generic family these
form a space of dimension `ind p - ind q + 1`: the dimension of the continuation trajectories of a
single field, plus one for the parameter. They are recorded by the parameter and the point of `γ` on
the middle level `t = 1 / 2` (`TauCeti.morseDigonSlice`). They are rigid when
`ind q = ind p + 1`: such trajectories, of continuation index `-1`, appear only at isolated
parameters. The homotopy `K = TauCeti.morseDigonMap f₀ hf₁ V`, of degree `+1`, counts them modulo
two (`TauCeti.morseDigonCoeff`). As for the continuation map, the definitions take no hypothesis on
`V`; they are the trajectory counts only when the slices are finite, which is expected for
admissible families under the parametrized transversality condition, and is not proved here.

**The ends of the one-dimensional digon trajectory spaces.** When `ind p = ind q`, the digon
trajectories from `p` to `q` are expected to form a one-dimensional space with four kinds of ends:

* breaking at the source (`TauCeti.morseSourceBrokenDigonSet`): a trajectory of `X₀` from `p` to a
  critical point `p'` of index `ind p - 1`, followed by a digon trajectory from `p'` to `q`;
* breaking at the target (`TauCeti.morseTargetBrokenDigonSet`): a digon trajectory from `p` to a
  critical point `q'` of index `ind p + 1`, followed by a trajectory of `X₁` from `q'` to `q`;
* the edge `λ = 0`: a continuation trajectory of `V 0` from `(p, 0)` to `(q, 1)`;
* the edge `λ = 1`: a continuation trajectory of `V 1` from `(p, 0)` to `(q, 1)`.

When the slices are finite, these four sets count the `q`-coefficients of `K ∘ ∂₀`, `∂₁ ∘ K`, `F⁰`
and `F¹` applied to `p`. So the digon identity `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹` holds exactly when,
between any two critical points of equal index, the four kinds of ends are evenly many in total
(`TauCeti.morseBoundary_comp_morseDigonMap_add_eq_iff`). This is the algebraic half of the
independence of the continuation map from the choice of path within its homotopy class; the
geometric half, that these four sets are the ends of compact one-dimensional manifolds with
boundary, needs the compactification and gluing of the parametrized continuation trajectory spaces
and is not proved here.

**The chain homotopy.** The homotopy raises the Morse index by one, so it restricts to maps from
the chains of index `i` to those of index `j`, zero unless `j = i + 1`
(`TauCeti.morseDigonMapAt`). When `F⁰` is a chain map and the digon identity holds, `F¹` is a chain
map as well
(`TauCeti.morseBoundary_comp_morseContinuationMap_of_morseBoundary_comp_morseDigonMap_add_eq`), and
the graded homotopy is a chain homotopy from the continuation morphism of `V 0` to that of `V 1`
(`TauCeti.morseDigonHomotopy`). By `Homotopy.homologyMap_eq`, the two continuations then induce the
same map on mod-two Morse homology. Together with the triangle homotopy
(`TauCeti.morseTriangleHomotopy`) this is what makes a reverse path an inverse up to homotopy: the
composite with the reverse continuation is homotopic to the constant path, whose continuation map
is the identity.

**Product families.** The homotopy of a family of product fields `(X x, Y λ t)` on `M × ℝ`, for a
Morse–Smale pseudo-gradient `X` adapted to `f`, vanishes
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseDigonMap_prodVectorField`): their trajectories
project to trajectories of `X`, which lower the index. For the constant family of constant
continuation fields, whose continuation maps are the identity, the digon identity then reads
`0 = id + id`, which holds over `ZMod 2`
(`morseBoundary_comp_morseDigonMap_add_eq_constantContinuationField`, in the namespace
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`).

## Main declarations

* `TauCeti.morseDigonSlice`: the parameters and middle-level points of the digon trajectories from
  `p` to `q`.
* `TauCeti.morseDigonCoeff`, `TauCeti.morseDigonMap`: the coefficients of the digon homotopy, and
  the homotopy.
* `TauCeti.morseSourceBrokenDigonSet`, `TauCeti.morseTargetBrokenDigonSet`: the broken digon
  trajectories.
* `TauCeti.morseDigonMap_morseBoundary_single_apply`,
  `TauCeti.morseBoundary_morseDigonMap_single_apply`: the coefficients of `K ∘ ∂₀` and `∂₁ ∘ K`
  count broken digon trajectories modulo two.
* `TauCeti.morseBoundary_comp_morseDigonMap_add_eq_iff`: the digon identity holds exactly when the
  ends of the digon trajectory spaces are evenly many.
* `TauCeti.morseDigonMapAt`: the digon homotopy between the chains of index `i` and `j`.
* `TauCeti.morseDigonHomotopy`: the chain homotopy between the continuation morphisms of the two
  edges.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (homotopic paths of Morse data give chain
  homotopic continuation maps, by counting index `-1` trajectories in the family).
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

variable {f₀ f₁ : M → ℝ} {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-- The digon trajectories of a family `V` of vector fields on `M × ℝ` from `p` to `q`, recorded by
their parameter and their point on the middle level: the pairs `(λ, x)` with `λ ∈ [0, 1]` and `x`
on the middle level `t = 1 / 2` of a trajectory of `V λ` from `(p, 0)` to `(q, 1)`. -/
def morseDigonSlice (V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) (p q : M) :
    Set (ℝ × M) :=
  {y | y.1 ∈ Icc 0 1 ∧ y.2 ∈ morseContinuationSlice (V y.1) p q}

/-- Membership in the slice of the digon trajectories. -/
@[simp]
theorem mem_morseDigonSlice {p q : M} {y : ℝ × M} :
    y ∈ morseDigonSlice V p q ↔ y.1 ∈ Icc 0 1 ∧ y.2 ∈ morseContinuationSlice (V y.1) p q :=
  Iff.rfl

variable (f₀ f₁ V) in
/-- The coefficient of the critical point `q` of `f₁` in the digon homotopy of the critical point
`p` of `f₀` along the family `V` of fields on `M × ℝ`: the number of pairs of a parameter
`λ ∈ [0, 1]` and a trajectory of `V λ` from `(p, 0)` to `(q, 1)`, read on the level `t = 1 / 2`,
modulo two when `ind q = ind p + 1`, and `0` otherwise. It is the trajectory count only when the
slice `TauCeti.morseDigonSlice V p q` is finite; an infinite slice contributes `0`. -/
noncomputable def morseDigonCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) : ZMod 2 :=
  if manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 then
    (morseDigonSlice V p q).ncard
  else 0

/-- When `ind q = ind p + 1`, the coefficient of the digon homotopy is the number of points of the
slice modulo two. -/
theorem morseDigonCoeff_eq_ncard {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    morseDigonCoeff f₀ f₁ V p q = ((morseDigonSlice V p q).ncard : ZMod 2) := by
  simp [morseDigonCoeff, hind]

/-- The coefficient of the digon homotopy vanishes unless `ind q = ind p + 1`: the homotopy raises
the Morse index by one. -/
@[simp]
theorem morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q ≠ manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    morseDigonCoeff f₀ f₁ V p q = 0 := by
  simp [morseDigonCoeff, hind]

/-- A nonzero coefficient of the digon homotopy joins `p` to a critical point of index
`ind p + 1`. -/
theorem manifoldMorseIndex_eq_add_one_of_morseDigonCoeff_ne_zero
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : morseDigonCoeff f₀ f₁ V p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 := by
  by_contra hind
  exact hpq (morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind)

variable [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (f₀) in
/-- **The mod-two digon homotopy** along a family `V` of vector fields on `M × ℝ`, from the mod-two
Morse chains of `f₀` to those of the Morse function `f₁`. It sends a critical point `p` of `f₀` to
the sum of the critical points `q` of `f₁` with `ind q = ind p + 1`, each weighted by the number of
pairs of a parameter `λ ∈ [0, 1]` and a trajectory of `V λ` from `(p, 0)` to `(q, 1)` modulo two. As
for `morseDigonCoeff`, this is the trajectory count only when the slice `morseDigonSlice V p q` is
finite; an infinite slice contributes `0`. -/
noncomputable def morseDigonMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (morseDigonCoeff f₀ f₁ V p) (toFinite _)

/-- The coefficient of `q` in the digon homotopy of a chain `c` is the sum over the critical points
`p` of `c p` times the coefficient `morseDigonCoeff`. -/
theorem morseDigonMap_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    morseDigonMap f₀ hf₁ V c q = c.sum fun p a ↦ a * morseDigonCoeff f₀ f₁ V p q := by
  simp [morseDigonMap, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the digon homotopy of `a • p` is `a` times the coefficient
`morseDigonCoeff`. -/
@[simp]
theorem morseDigonMap_single_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) (a : ZMod 2) :
    morseDigonMap f₀ hf₁ V (Finsupp.single p a) q = a * morseDigonCoeff f₀ f₁ V p q := by
  rw [morseDigonMap_apply, Finsupp.sum_single_index (zero_mul _)]

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-! ### Broken digon trajectories -/

section BrokenSets

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)

variable (f₁ V) in
/-- The digon trajectories from `p` to `q` broken at the source: triples `(p', z₁, y₂)` of a
critical point `p'` of `f₀` whose Morse index lies one below those of `p` and of `q`, a point `z₁`
on the middle-level slice of the trajectories of `X₀` from `p` to `p'`, and a pair `y₂` of a
parameter `λ ∈ [0, 1]` and a point on the middle level of the trajectories of `V λ` from `(p', 0)`
to `(q, 1)`. -/
def morseSourceBrokenDigonSet (p q : M) :
    Set (criticalPoints 𝓘(ℝ, E) f₀ × M × (ℝ × M)) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ morseDigonSlice V x.1 q}

/-- Membership in the set of digon trajectories broken at the source. -/
@[simp]
theorem mem_morseSourceBrokenDigonSet {p q : M}
    {x : criticalPoints 𝓘(ℝ, E) f₀ × M × (ℝ × M)} :
    x ∈ morseSourceBrokenDigonSet f₁ V hX₀ p q ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
          x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ morseDigonSlice V x.1 q :=
  Iff.rfl

variable (f₀ V) in
/-- The digon trajectories from `p` to `q` broken at the target: triples `(q', y₁, z₂)` of a
critical point `q'` of `f₁` whose Morse index lies one above those of `p` and of `q`, a pair `y₁`
of a parameter `λ ∈ [0, 1]` and a point on the middle level of the trajectories of `V λ` from
`(p, 0)` to `(q', 1)`, and a point `z₂` on the middle-level slice of the trajectories of `X₁` from
`q'` to `q`. -/
def morseTargetBrokenDigonSet (p q : M) :
    Set (criticalPoints 𝓘(ℝ, E) f₁ × (ℝ × M) × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
    x.2.1 ∈ morseDigonSlice V p x.1 ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 q}

/-- Membership in the set of digon trajectories broken at the target. -/
@[simp]
theorem mem_morseTargetBrokenDigonSet {p q : M}
    {x : criticalPoints 𝓘(ℝ, E) f₁ × (ℝ × M) × M} :
    x ∈ morseTargetBrokenDigonSet f₀ V hX₁ p q ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
          x.2.1 ∈ morseDigonSlice V p x.1 ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 q :=
  Iff.rfl

end BrokenSets

/-! ### Counting broken digon trajectories -/

section Count

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

include h₀ hf₀ in
/-- **Finitely many digon trajectories broken at the source**, when the digon slices into `q` from
critical points of index `ind q - 1` are finite. -/
theorem finite_morseSourceBrokenDigonSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hV : ∀ p' : criticalPoints 𝓘(ℝ, E) f₀,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1 →
        (morseDigonSlice V p' q).Finite) :
    (morseSourceBrokenDigonSet f₁ V hX₀ p q).Finite := by
  have := hf₀.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀) hV

include h₁ hf₁ in
/-- **Finitely many digon trajectories broken at the target**, when the digon slices out of `p` to
critical points of index `ind p + 1` are finite. -/
theorem finite_morseTargetBrokenDigonSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hV : ∀ q' : criticalPoints 𝓘(ℝ, E) f₁,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseDigonSlice V p q').Finite) :
    (morseTargetBrokenDigonSet f₀ V hX₁ p q).Finite := by
  have := hf₁.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem hV fun _ ↦ h₁.finite_morseTrajectorySlice hf₁

include h₀ in
/-- **`K ∘ ∂₀` counts digon trajectories broken at the source.** When they are finitely many, the
`q`-coefficient of the digon homotopy of the Morse boundary of `p` is the number of digon
trajectories from `p` to `q` broken at the source, modulo two. -/
theorem morseDigonMap_morseBoundary_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (hfin : (morseSourceBrokenDigonSet f₁ V hX₀ p q).Finite) :
    morseDigonMap f₀ hf₁ V (h₀.morseBoundary hf₀ (Finsupp.single p 1)) q =
      ((morseSourceBrokenDigonSet f₁ V hX₀ p q).ncard : ZMod 2) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [morseDigonMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    morseSourceBrokenDigonSet]
  -- Sort the broken trajectories by their intermediate critical point `p'`. The index conditions
  -- and slice families are named because unification cannot read them off `hfin`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun p' : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (Q := fun p' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (morseDigonSlice V · q)) (fun p' hind ↦ ?_)
    (fun p' hind ↦ ?_) (fun _ ↦ morseDigonCoeff_eq_ncard)
    (fun _ ↦ morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one) hfin).symm
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_ncard hf₀ hind]
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₀ hind]

include h₁ in
/-- **`∂₁ ∘ K` counts digon trajectories broken at the target.** When they are finitely many, the
`q`-coefficient of the Morse boundary of the digon homotopy of `p` is the number of digon
trajectories from `p` to `q` broken at the target, modulo two. -/
theorem morseBoundary_morseDigonMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (hfin : (morseTargetBrokenDigonSet f₀ V hX₁ p q).Finite) :
    h₁.morseBoundary hf₁ (morseDigonMap f₀ hf₁ V (Finsupp.single p 1)) q =
      ((morseTargetBrokenDigonSet f₀ V hX₁ p q).ncard : ZMod 2) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, morseTargetBrokenDigonSet]
  -- Sort the broken trajectories by their intermediate critical point `q'`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun q' : criticalPoints 𝓘(ℝ, E) f₁ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1)
    (Q := fun q' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)
    (A := (morseDigonSlice V p ·)) (B := (hX₁.morseTrajectorySlice · q)) (fun q' hind ↦ ?_)
    (fun q' hind ↦ ?_) (fun _ ↦ h₁.morseBoundaryCoeff_eq_ncard hf₁)
    (fun _ ↦ h₁.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₁) hfin).symm
  · rw [morseDigonMap_single_apply, one_mul, morseDigonCoeff_eq_ncard hind]
  · rw [morseDigonMap_single_apply, one_mul,
      morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind]

include h₀ hf₀ h₁ in
/-- The digon identity at the coefficient of `q` in the image of `p`: under the finiteness
hypothesis of `TauCeti.morseBoundary_comp_morseDigonMap_add_eq_iff`, it holds exactly when the ends
of the digon trajectory spaces from `p` to `q` are evenly many, or the indices differ. -/
private theorem morseDigon_single_apply_eq_iff
    (hV : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseDigonSlice V p q).Finite)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    (h₁.morseBoundary hf₁ (morseDigonMap f₀ hf₁ V (Finsupp.single p 1)) q +
      morseDigonMap f₀ hf₁ V (h₀.morseBoundary hf₀ (Finsupp.single p 1)) q =
      morseContinuationMap f₀ hf₁ (V 0) (Finsupp.single p 1) q +
        morseContinuationMap f₀ hf₁ (V 1) (Finsupp.single p 1) q) ↔
    (manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
      Even ((morseSourceBrokenDigonSet f₁ V hX₀ p q).ncard +
        (morseTargetBrokenDigonSet f₀ V hX₁ p q).ncard +
          (morseContinuationSlice (V 0) p q).ncard +
            (morseContinuationSlice (V 1) p q).ncard)) := by
  rw [morseBoundary_morseDigonMap_single_apply h₁ hf₁ p q
      (finite_morseTargetBrokenDigonSet h₁ hf₁ p q (hV p)),
    morseDigonMap_morseBoundary_single_apply h₀ hf₀ hf₁ p q
      (finite_morseSourceBrokenDigonSet h₀ hf₀ p q (hV · q)),
    morseContinuationMap_single_apply, morseContinuationMap_single_apply, one_mul, one_mul]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [morseContinuationCoeff_eq_ncard hind, morseContinuationCoeff_eq_ncard hind,
      ← CharTwo.add_eq_zero, ← ZMod.natCast_eq_zero_iff_even]
    simp only [hind, forall_const]
    push_cast
    convert Iff.rfl using 2
    ring
  · -- Between critical points of different index all four counts vanish.
    have hS : morseSourceBrokenDigonSet f₁ V hX₀ p q = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseSourceBrokenDigonSet] at hx; omega)
    have hT : morseTargetBrokenDigonSet f₀ V hX₁ p q = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseTargetBrokenDigonSet] at hx; omega)
    simp [hS, hT, hind]

include h₀ hf₀ h₁ in
/-- **The digon identity holds exactly when the ends of the digon trajectory spaces come in
pairs.** When the digon slices between critical points whose indices differ by one are finite, the
mod-two digon homotopy `K` of the family `V` satisfies `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹`, for the
continuation maps `F⁰` and `F¹` along `V 0` and `V 1`, exactly when, between any critical point `p`
of `f₀` and any critical point `q` of `f₁` of the same index, the digon trajectories broken at the
source and at the target, together with the continuation trajectories of `V 0` and of `V 1` on the
two edges, are evenly many in total. -/
theorem morseBoundary_comp_morseDigonMap_add_eq_iff
    (hV : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseDigonSlice V p q).Finite) :
    h₁.morseBoundary hf₁ ∘ₗ morseDigonMap f₀ hf₁ V +
        morseDigonMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
          Even ((morseSourceBrokenDigonSet f₁ V hX₀ p q).ncard +
            (morseTargetBrokenDigonSet f₀ V hX₁ p q).ncard +
              (morseContinuationSlice (V 0) p q).ncard +
                (morseContinuationSlice (V 1) p q).ncard) := by
  -- Compare the two sides coefficientwise.
  simp_rw [← morseDigon_single_apply_eq_iff h₀ hf₀ h₁ hf₁ hV]
  constructor
  · intro h0 p q
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) q
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
    -- Over `ZMod 2`, both maps send `a • p` to `a` times their value at `p`.
    have := h0 p q
    rw [← Finsupp.smul_single_one]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul, this]

end Count

/-! ### The graded digon homotopy and the chain homotopy -/

section Graded

variable (f₀) in
/-- **The graded mod-two digon homotopy.** The `ZMod 2`-linear map from the free module on the
critical points of `f₀` of index `i` to the free module on the critical points of `f₁` of index `j`
sending `p` to the sum of the critical points `q`, each weighted by the number of digon trajectories
of the family `V` from `p` to `q` modulo two. As for `morseDigonCoeff`, this is the trajectory count
only when the slice `morseDigonSlice V p q` is finite; an infinite slice contributes `0`. It is the
restriction of `morseDigonMap`, and it vanishes unless `j = i + 1`
(`TauCeti.morseDigonMapAt_eq_zero`). -/
noncomputable def morseDigonMapAt (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) (i j : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2) →ₗ[ZMod 2]
      ({q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j} →₀ ZMod 2) :=
  Finsupp.lsubtypeDomain {q : criticalPoints 𝓘(ℝ, E) f₁ | manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j} ∘ₗ
    morseDigonMap f₀ hf₁ V ∘ₗ Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded digon homotopy of a chain `c` is the sum over the critical
points `p` of index `i` of `c p` times the coefficient `morseDigonCoeff`. -/
theorem morseDigonMapAt_apply {i j : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j}) :
    morseDigonMapAt f₀ hf₁ V i j c q = c.sum fun p a ↦ a * morseDigonCoeff f₀ f₁ V p q := by
  rw [morseDigonMapAt, LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.lmapDomain_apply,
    morseDigonMap_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded digon homotopy of `a • p` is `a` times the coefficient
`morseDigonCoeff`. -/
@[simp]
theorem morseDigonMapAt_single_apply {i j : ℕ}
    (p : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i}) (a : ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j}) :
    morseDigonMapAt f₀ hf₁ V i j (Finsupp.single p a) q = a * morseDigonCoeff f₀ f₁ V p q := by
  rw [morseDigonMapAt_apply, Finsupp.sum_single_index (zero_mul _)]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded digon homotopy raises the index by one**: from the chains of index `i` to those of
index `j` it vanishes unless `j = i + 1`. -/
theorem morseDigonMapAt_eq_zero {i j : ℕ} (hij : j ≠ i + 1) :
    morseDigonMapAt f₀ hf₁ V i j = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [morseDigonMapAt_single_apply, morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one
    (by rw [p.property, q.property]; exact hij), mul_zero, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded and total digon homotopies agree.** Including the chains of index `i` and of index
`i + 1` into all Morse chains intertwines the graded digon homotopy with the total one
`morseDigonMap`: the digon homotopy of a chain of index `i` is a chain of index `i + 1`. -/
@[simp]
theorem mapDomain_morseDigonMapAt {i : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2) :
    (morseDigonMapAt f₀ hf₁ V i (i + 1) c).mapDomain Subtype.val =
      morseDigonMap f₀ hf₁ V (c.mapDomain Subtype.val) := by
  ext q
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = i + 1
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨q, hq⟩
  · -- Outside index `i + 1` both sides vanish: the left side by support, the right side because
    -- every coefficient of the digon homotopy from index `i` to `q` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨r, hr⟩ ↦ hq (hr ▸ r.property),
      morseDigonMap_apply,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul .., Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one (by grind), mul_zero]

end Graded

section Homotopy

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

include h₀ hf₀ h₁ hf₁ in
/-- **The continuation along the second edge is a chain map when the first is and the digon
identity holds.** If the continuation map `F⁰` along `V 0` commutes with the Morse boundaries and
the digon homotopy `K` satisfies `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹`, then the continuation map `F¹` along
`V 1` commutes with the Morse boundaries. -/
theorem morseBoundary_comp_morseContinuationMap_of_morseBoundary_comp_morseDigonMap_add_eq
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ (V 0) =
      morseContinuationMap f₀ hf₁ (V 0) ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDigonMap f₀ hf₁ V +
        morseDigonMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) :
    h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ (V 1) =
      morseContinuationMap f₀ hf₁ (V 1) ∘ₗ h₀.morseBoundary hf₀ := by
  -- Solve the digon identity for `F¹` and use `∂ ∘ ∂ = 0` on both sides.
  have hF : ∀ c, morseContinuationMap f₀ hf₁ (V 1) c =
      h₁.morseBoundary hf₁ (morseDigonMap f₀ hf₁ V c) +
        morseDigonMap f₀ hf₁ V (h₀.morseBoundary hf₀ c) -
          morseContinuationMap f₀ hf₁ (V 0) c := fun c ↦ by
    have := LinearMap.congr_fun hK c
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at this
    rw [this, add_sub_cancel_left]
  refine LinearMap.ext fun c ↦ ?_
  have h0 := LinearMap.congr_fun hcomm c
  simp only [LinearMap.comp_apply] at h0 ⊢
  rw [hF, hF, map_sub, map_add, h₁.morseBoundary_morseBoundary, h₀.morseBoundary_morseBoundary,
    map_zero, h0, zero_add, add_zero]

include h₀ hf₀ h₁ hf₁ in
/-- The graded digon identity in degree `0`, where there is no boundary out of the chains. -/
private theorem morseContinuationMapAt_zero_eq_morseBoundaryAt_comp_morseDigonMapAt_add
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDigonMap f₀ hf₁ V +
        morseDigonMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) :
    morseContinuationMapAt f₀ hf₁ (V 0) 0 =
      h₁.morseBoundaryAt hf₁ 0 ∘ₗ morseDigonMapAt f₀ hf₁ V 0 1 +
        morseContinuationMapAt f₀ hf₁ (V 1) 0 := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hK (Finsupp.single p.val 1)
  have h0 := h₀.morseBoundary_mapDomain_eq_zero_of_index_zero hf₀ (Finsupp.single p 1)
  simp only [Finsupp.mapDomain_single] at h0
  simp only [LinearMap.add_apply, LinearMap.comp_apply, h0, map_zero, add_zero] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, mapDomain_morseContinuationMapAt, h₁.mapDomain_morseBoundaryAt hf₁,
    mapDomain_morseDigonMapAt, Finsupp.mapDomain_single, this, add_assoc,
    ZModModule.add_self, add_zero]

include h₀ hf₀ h₁ hf₁ in
/-- The graded digon identity in degree `n + 1`. -/
private theorem morseContinuationMapAt_succ_eq_morseDigonMapAt_comp_morseBoundaryAt_add
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDigonMap f₀ hf₁ V +
        morseDigonMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) (n : ℕ) :
    morseContinuationMapAt f₀ hf₁ (V 0) (n + 1) =
      morseDigonMapAt f₀ hf₁ V n (n + 1) ∘ₗ h₀.morseBoundaryAt hf₀ n +
        h₁.morseBoundaryAt hf₁ (n + 1) ∘ₗ morseDigonMapAt f₀ hf₁ V (n + 1) (n + 2) +
          morseContinuationMapAt f₀ hf₁ (V 1) (n + 1) := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hK (Finsupp.single p.val 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, mapDomain_morseContinuationMapAt, h₁.mapDomain_morseBoundaryAt hf₁,
    h₀.mapDomain_morseBoundaryAt hf₀, mapDomain_morseDigonMapAt, Finsupp.mapDomain_single]
  rw [add_comm (morseDigonMap f₀ hf₁ V _), this, add_assoc, ZModModule.add_self, add_zero]

/-- **The digon homotopy.** When the continuation map `F⁰` along `V 0` commutes with the Morse
boundaries and the mod-two digon homotopy `K` of the family `V` satisfies
`∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹`, the graded digon homotopy is a chain homotopy from the continuation
morphism of `V 0` to that of `V 1`. So the two continuations induce the same map on mod-two Morse
homology (`Homotopy.homologyMap_eq`). -/
noncomputable def morseDigonHomotopy
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ (V 0) =
      morseContinuationMap f₀ hf₁ (V 0) ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDigonMap f₀ hf₁ V +
        morseDigonMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) :
    Homotopy (morseContinuationHom h₀ hf₀ h₁ hf₁ hcomm)
      (morseContinuationHom h₀ hf₀ h₁ hf₁
        (morseBoundary_comp_morseContinuationMap_of_morseBoundary_comp_morseDigonMap_add_eq
          h₀ hf₀ h₁ hf₁ hcomm hK)) where
  hom i j := ModuleCat.ofHom (morseDigonMapAt f₀ hf₁ V i j)
  zero i j hij := by
    rw [morseDigonMapAt_eq_zero hf₁ fun h ↦ hij (by simp [h]), ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  comm i := by
    -- The components `ModuleCat.ofHom (morseDigonMapAt ...)` have source and target
    -- `ModuleCat.of (ZMod 2) (... →₀ ZMod 2)`, while `dNext` and `prevD` expect the terms
    -- `(morseComplex _).X i` of the Morse complexes; these agree only up to unfolding
    -- `morseComplex` (`IsAdaptedPseudoGradient.IsMorseSmale.morseComplex_X`), so plain `rw`
    -- cannot match them and `erw` is needed.
    rcases i with _ | n
    · erw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      rw [zero_add, h₁.morseComplex_d hf₁, morseContinuationHom_f, morseContinuationHom_f]
      -- The terms of the Morse complexes are not syntactically the free modules on which the
      -- graded maps act, so compare the underlying linear maps.
      apply ModuleCat.hom_ext
      exact morseContinuationMapAt_zero_eq_morseBoundaryAt_comp_morseDigonMapAt_add
        h₀ hf₀ h₁ hf₁ hK
    · erw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      rw [h₀.morseComplex_d hf₀, h₁.morseComplex_d hf₁, morseContinuationHom_f,
        morseContinuationHom_f]
      apply ModuleCat.hom_ext
      exact morseContinuationMapAt_succ_eq_morseDigonMapAt_comp_morseBoundaryAt_add
        h₀ hf₀ h₁ hf₁ hK n

/-- The components of the digon homotopy are the graded digon homotopies. -/
@[simp]
theorem morseDigonHomotopy_hom
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ (V 0) =
      morseContinuationMap f₀ hf₁ (V 0) ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDigonMap f₀ hf₁ V +
        morseDigonMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) (i j : ℕ) :
    (morseDigonHomotopy h₀ hf₀ h₁ hf₁ hcomm hK).hom i j =
      ModuleCat.ofHom (morseDigonMapAt f₀ hf₁ V i j) :=
  (rfl)

end Homotopy

/-! ### Product families -/

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Product families have no digon trajectories raising the index.** Under the Morse–Smale
condition, for every family `Y` of fields on `ℝ`, the family of product fields `(X x, Y λ t)` on
`M × ℝ` has no digon trajectory from `p` to `q` when `ind p < ind q`: the space component of each
trajectory is a trajectory of `X` from `p` to `q`, which lowers the index. -/
theorem morseDigonSlice_prodVectorField_eq_empty
    (Y : ℝ → (t : ℝ) → TangentSpace 𝓘(ℝ) t) {p q : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p < manifoldMorseIndex 𝓘(ℝ, E) f q) :
    morseDigonSlice (fun l ↦ Manifold.prodVectorField X (Y l)) p q = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy ↦ ?_
  obtain ⟨γ, hγ, -, hp, hq⟩ := mem_morseContinuationSlice.1 hy.2
  have hpq : p ≠ q := by rintro rfl; exact hind.false
  obtain ⟨hy, -⟩ := hX.mem_unstableSet_inter_stableSet_of_isMIntegralCurve
    (Manifold.isMIntegralCurve_prodVectorField_iff.1 hγ).1
    ((continuous_fst.tendsto _).comp hp) ((continuous_fst.tendsto _).comp hq)
  exact (h.manifoldMorseIndex_lt hf hpq ⟨_, hy⟩).not_gt hind

include h hf in
/-- **The digon homotopy of a product family vanishes.** Under the Morse–Smale condition, for every
family `Y` of fields on `ℝ`, the mod-two digon homotopy of the family of product fields
`(X x, Y λ t)` on `M × ℝ` is zero. -/
@[simp]
theorem morseDigonMap_prodVectorField (Y : ℝ → (t : ℝ) → TangentSpace 𝓘(ℝ) t) :
    morseDigonMap f hf (fun l ↦ Manifold.prodVectorField X (Y l)) = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [morseDigonMap_single_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f p + 1
  · rw [morseDigonCoeff_eq_ncard hind,
      h.morseDigonSlice_prodVectorField_eq_empty hf Y (by omega), ncard_empty, Nat.cast_zero,
      mul_zero]
  · rw [morseDigonCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind, mul_zero]

include h in
/-- **The digon identity for the constant family of constant paths.** Under the Morse–Smale
condition, for `C > 0`, the constant family of constant continuation fields `(X x, C t (1 - t²))`
satisfies the digon identity `∂ ∘ K + K ∘ ∂ = F⁰ + F¹`: its digon homotopy `K` vanishes, as for
every product family, and both edges have the identity as continuation map, so the identity reads
`0 = id + id`, which holds over `ZMod 2`. -/
theorem morseBoundary_comp_morseDigonMap_add_eq_constantContinuationField {C : ℝ} (hC : 0 < C) :
    h.morseBoundary hf ∘ₗ morseDigonMap f hf (fun _ ↦ constantContinuationField X C) +
        morseDigonMap f hf (fun _ ↦ constantContinuationField X C) ∘ₗ h.morseBoundary hf =
      morseContinuationMap f hf (constantContinuationField X C) +
        morseContinuationMap f hf (constantContinuationField X C) := by
  have hK : morseDigonMap f hf (fun _ ↦ constantContinuationField X C) = 0 := by
    simp only [constantContinuationField_def]
    exact h.morseDigonMap_prodVectorField hf _
  rw [hK, h.morseContinuationMap_constantContinuationField hf hC, LinearMap.comp_zero,
    LinearMap.zero_comp, add_zero]
  refine LinearMap.ext fun c ↦ ?_
  rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.id_apply, ZModModule.add_self]

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
