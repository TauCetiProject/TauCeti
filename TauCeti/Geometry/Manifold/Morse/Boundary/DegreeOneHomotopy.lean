/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.Defs
public import TauCeti.Geometry.Manifold.Morse.Boundary.Commutation
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Data.Set.Card
import TauCeti.Geometry.Manifold.IntegralCurve.Prod

/-!
# Mod-two chain homotopies counting trajectories of index `-1`

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them. The chain homotopies between continuation
morphisms of mod-two Morse complexes count rigid trajectories of index `-1` in a one-parameter
family: trajectories over the ordered triangle for the composition of continuations
(`TauCeti.morseTriangleHomotopy`), and trajectories of a family of continuation fields for homotopic
continuations (`TauCeti.morseDigonHomotopy`). Each kind of trajectory from `p` to `q` is recorded
by a set `S p q` of points on a level hypersurface, its *slice*. This file develops, for an
arbitrary slice family `S : M → M → Set α`, the part of the argument that does not depend on what
the slices are.

**The degree-one map.** The map `K = TauCeti.morseDegreeOneMap f₀ hf₁ S` sends a critical point `p`
of `f₀` to the sum of the critical points `q` of `f₁` with `ind q = ind p + 1`, each weighted by the
number of points of `S p q` modulo two (`TauCeti.morseDegreeOneCoeff`). The definitions take no
hypothesis on `S`; they are trajectory counts only when the slices are finite.

**Broken trajectories.** A trajectory of index `-1` can break at the source, into a trajectory of
`X₀` from `p` to a critical point `p'` of index `ind p - 1` followed by a point of `S p' q`
(`TauCeti.morseSourceBrokenDegreeOneSet`), or at the target, into a point of `S p q'` followed by a
trajectory of `X₁` from `q'` to `q` (`TauCeti.morseTargetBrokenDegreeOneSet`). When these are
finitely many they count the `q`-coefficients of `K ∘ ∂₀` and `∂₁ ∘ K` applied to `p`. So
`∂₁ ∘ K + K ∘ ∂₀ = G` holds, for a map `G` counting `N p q` further ends between critical points
of equal index, exactly when between any two critical points of equal index the broken trajectories
and the further ends are evenly many in total
(`TauCeti.morseBoundary_comp_morseDegreeOneMap_add_eq_iff`).

**The chain homotopy.** The degree-one map raises the Morse index by one, so it restricts to maps
from the chains of index `i` to those of index `j`, zero unless `j = i + 1`
(`TauCeti.morseDegreeOneMapAt`). When `∂₁ ∘ K + K ∘ ∂₀ = Φ + F` for a total map `Φ` underlying a
morphism `φ` of Morse complexes and the continuation map `F` along a field `V`, the map `F`
commutes with the Morse boundaries (`LinearMap.comp_eq_comp_of_comp_add_comp_eq_add`), and the
graded degree-one map is a chain homotopy from `φ` to the continuation morphism of `V`
(`TauCeti.morseDegreeOneHomotopy`).

**Product fields.** Under the Morse–Smale condition, the Morse index does not rise along the space
component of a trajectory of a product field `(X x, Y b)`
(`manifoldMorseIndex_le_of_isMIntegralCurve_prodVectorField`, in the namespace
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`).
The degree-one map vanishes when the slices between critical points whose indices differ by one are
empty (`TauCeti.morseDegreeOneMap_eq_zero_of_slice_eq_empty`).

## Main declarations

* `TauCeti.morseDegreeOneCoeff`, `TauCeti.morseDegreeOneMap`: the coefficients of the degree-one
  map of a slice family, and the map.
* `TauCeti.morseSourceBrokenDegreeOneSet`, `TauCeti.morseTargetBrokenDegreeOneSet`: the broken
  trajectories at the source and at the target.
* `TauCeti.morseBoundary_comp_morseDegreeOneMap_add_eq_iff`: `∂₁ ∘ K + K ∘ ∂₀ = G` exactly when the
  ends are evenly many.
* `TauCeti.morseDegreeOneMapAt`: the degree-one map between the chains of index `i` and `j`.
* `TauCeti.morseDegreeOneHomotopy`: the chain homotopy from a morphism of Morse complexes to a
  continuation morphism.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (chain homotopies between continuation maps count index
  `-1` trajectories in a one-parameter family).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open CategoryTheory Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {α : Type*}

section Definitions

variable {f₀ f₁ : M → ℝ} {S : M → M → Set α}

variable (f₀ f₁ S) in
/-- The coefficient of the critical point `q` of `f₁` in the degree-one map of the slice family
`S` at the critical point `p` of `f₀`: the number of points of `S p q` modulo two when
`ind q = ind p + 1`, and `0` otherwise. It is a trajectory count only when the slice `S p q` is
finite; an infinite slice contributes `0`. -/
noncomputable def morseDegreeOneCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) : ZMod 2 :=
  if manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 then
    (S p q).ncard
  else 0

/-- When `ind q = ind p + 1`, the coefficient of the degree-one map is the number of points of the
slice modulo two. -/
theorem morseDegreeOneCoeff_eq_ncard {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    morseDegreeOneCoeff f₀ f₁ S p q = ((S p q).ncard : ZMod 2) := by
  simp [morseDegreeOneCoeff, hind]

/-- The coefficient of the degree-one map vanishes unless `ind q = ind p + 1`: the map raises the
Morse index by one. -/
@[simp]
theorem morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q ≠ manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1) :
    morseDegreeOneCoeff f₀ f₁ S p q = 0 := by
  simp [morseDegreeOneCoeff, hind]

/-- A nonzero coefficient of the degree-one map joins `p` to a critical point of index
`ind p + 1`. -/
theorem manifoldMorseIndex_eq_add_one_of_morseDegreeOneCoeff_ne_zero
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : morseDegreeOneCoeff f₀ f₁ S p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 := by
  by_contra hind
  exact hpq (morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind)

variable [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (f₀) in
/-- **The mod-two degree-one map** of a slice family `S`, from the mod-two Morse chains of `f₀` to
those of the Morse function `f₁`. It sends a critical point `p` of `f₀` to the sum of the critical
points `q` of `f₁` with `ind q = ind p + 1`, each weighted by the number of points of `S p q` modulo
two. As for `morseDegreeOneCoeff`, an infinite slice contributes `0`. -/
noncomputable def morseDegreeOneMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (S : M → M → Set α) :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (morseDegreeOneCoeff f₀ f₁ S p) (toFinite _)

/-- The coefficient of `q` in the degree-one map of a chain `c` is the sum over the critical points
`p` of `c p` times the coefficient `morseDegreeOneCoeff`. -/
theorem morseDegreeOneMap_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    morseDegreeOneMap f₀ hf₁ S c q = c.sum fun p a ↦ a * morseDegreeOneCoeff f₀ f₁ S p q := by
  simp [morseDegreeOneMap, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the degree-one map of `a • p` is `a` times the coefficient
`morseDegreeOneCoeff`. -/
@[simp]
theorem morseDegreeOneMap_single_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) (a : ZMod 2) :
    morseDegreeOneMap f₀ hf₁ S (Finsupp.single p a) q = a * morseDegreeOneCoeff f₀ f₁ S p q := by
  rw [morseDegreeOneMap_apply, Finsupp.sum_single_index (zero_mul _)]

/-- **The degree-one map of a slice family with no slices raising the index vanishes**: if `S p q`
is empty whenever `ind q = ind p + 1`, the degree-one map of `S` is zero. -/
theorem morseDegreeOneMap_eq_zero_of_slice_eq_empty (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → S p q = ∅) :
    morseDegreeOneMap f₀ hf₁ S = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [morseDegreeOneMap_single_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1
  · rw [morseDegreeOneCoeff_eq_ncard hind, hS p q hind, ncard_empty, Nat.cast_zero, mul_zero]
  · rw [morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind, mul_zero]

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {S : M → M → Set α}

/-! ### Broken trajectories -/

section BrokenSets

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)

variable (f₁ S) in
/-- The trajectories of the slice family `S` from `p` to `q` broken at the source: triples
`(p', z₁, y₂)` of a critical point `p'` of `f₀` whose Morse index lies one below those of `p` and of
`q`, a point `z₁` on the middle-level slice of the trajectories of `X₀` from `p` to `p'`, and a
point `y₂` of the slice `S p' q`. -/
def morseSourceBrokenDegreeOneSet (p q : M) : Set (criticalPoints 𝓘(ℝ, E) f₀ × M × α) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ S x.1 q}

/-- Membership in the set of trajectories broken at the source. -/
@[simp]
theorem mem_morseSourceBrokenDegreeOneSet {p q : M} {x : criticalPoints 𝓘(ℝ, E) f₀ × M × α} :
    x ∈ morseSourceBrokenDegreeOneSet f₁ S hX₀ p q ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
          x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ S x.1 q :=
  Iff.rfl

variable (f₀ S) in
/-- The trajectories of the slice family `S` from `p` to `q` broken at the target: triples
`(q', y₁, z₂)` of a critical point `q'` of `f₁` whose Morse index lies one above those of `p` and of
`q`, a point `y₁` of the slice `S p q'`, and a point `z₂` on the middle-level slice of the
trajectories of `X₁` from `q'` to `q`. -/
def morseTargetBrokenDegreeOneSet (p q : M) : Set (criticalPoints 𝓘(ℝ, E) f₁ × α × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
    x.2.1 ∈ S p x.1 ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 q}

/-- Membership in the set of trajectories broken at the target. -/
@[simp]
theorem mem_morseTargetBrokenDegreeOneSet {p q : M} {x : criticalPoints 𝓘(ℝ, E) f₁ × α × M} :
    x ∈ morseTargetBrokenDegreeOneSet f₀ S hX₁ p q ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
          x.2.1 ∈ S p x.1 ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 q :=
  Iff.rfl

end BrokenSets

/-! ### Counting broken trajectories -/

section Count

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

include h₀ hf₀ in
/-- **Finitely many trajectories broken at the source**, when the slices into `q` from critical
points of index `ind q - 1` are finite. -/
theorem finite_morseSourceBrokenDegreeOneSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hS : ∀ p' : criticalPoints 𝓘(ℝ, E) f₀,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1 → (S p' q).Finite) :
    (morseSourceBrokenDegreeOneSet f₁ S hX₀ p q).Finite := by
  have := hf₀.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀) hS

include h₁ hf₁ in
/-- **Finitely many trajectories broken at the target**, when the slices out of `p` to critical
points of index `ind p + 1` are finite. -/
theorem finite_morseTargetBrokenDegreeOneSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hS : ∀ q' : criticalPoints 𝓘(ℝ, E) f₁,
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → (S p q').Finite) :
    (morseTargetBrokenDegreeOneSet f₀ S hX₁ p q).Finite := by
  have := hf₁.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem hS fun _ ↦ h₁.finite_morseTrajectorySlice hf₁

include h₀ in
/-- **`K ∘ ∂₀` counts trajectories broken at the source.** When they are finitely many, the
`q`-coefficient of the degree-one map of the Morse boundary of `p` is the number of trajectories
from `p` to `q` broken at the source, modulo two. -/
theorem morseDegreeOneMap_morseBoundary_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (hfin : (morseSourceBrokenDegreeOneSet f₁ S hX₀ p q).Finite) :
    morseDegreeOneMap f₀ hf₁ S (h₀.morseBoundary hf₀ (Finsupp.single p 1)) q =
      ((morseSourceBrokenDegreeOneSet f₁ S hX₀ p q).ncard : ZMod 2) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [morseDegreeOneMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    morseSourceBrokenDegreeOneSet]
  -- Sort the broken trajectories by their intermediate critical point `p'`. The index conditions
  -- and slice families are named because unification cannot read them off `hfin`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun p' : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (Q := fun p' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (S · q)) (fun p' hind ↦ ?_)
    (fun p' hind ↦ ?_) (fun _ ↦ morseDegreeOneCoeff_eq_ncard)
    (fun _ ↦ morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one) hfin).symm
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_ncard hf₀ hind]
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₀ hind]

include h₁ in
/-- **`∂₁ ∘ K` counts trajectories broken at the target.** When they are finitely many, the
`q`-coefficient of the Morse boundary of the degree-one map of `p` is the number of trajectories
from `p` to `q` broken at the target, modulo two. -/
theorem morseBoundary_morseDegreeOneMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (hfin : (morseTargetBrokenDegreeOneSet f₀ S hX₁ p q).Finite) :
    h₁.morseBoundary hf₁ (morseDegreeOneMap f₀ hf₁ S (Finsupp.single p 1)) q =
      ((morseTargetBrokenDegreeOneSet f₀ S hX₁ p q).ncard : ZMod 2) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, morseTargetBrokenDegreeOneSet]
  -- Sort the broken trajectories by their intermediate critical point `q'`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun q' : criticalPoints 𝓘(ℝ, E) f₁ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1)
    (Q := fun q' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)
    (A := (S p ·)) (B := (hX₁.morseTrajectorySlice · q)) (fun q' hind ↦ ?_)
    (fun q' hind ↦ ?_) (fun _ ↦ h₁.morseBoundaryCoeff_eq_ncard hf₁)
    (fun _ ↦ h₁.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₁) hfin).symm
  · rw [morseDegreeOneMap_single_apply, one_mul, morseDegreeOneCoeff_eq_ncard hind]
  · rw [morseDegreeOneMap_single_apply, one_mul,
      morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one hind]

include h₀ hf₀ h₁ in
/-- The identity `∂₁ ∘ K + K ∘ ∂₀ = G` at the coefficient of `q` in the image of `p`: under the
hypotheses of `TauCeti.morseBoundary_comp_morseDegreeOneMap_add_eq_iff`, it holds exactly when the
ends from `p` to `q` are evenly many, or the indices differ. -/
private theorem morseDegreeOne_single_apply_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → (S p q).Finite)
    {G : (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2)}
    {N : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → ℕ}
    (hG : ∀ p q, G (Finsupp.single p 1) q =
      if manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q then (N p q : ZMod 2)
      else 0)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    (h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ S +
        morseDegreeOneMap f₀ hf₁ S ∘ₗ h₀.morseBoundary hf₀) (Finsupp.single p 1) q =
      G (Finsupp.single p 1) q ↔
    (manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
      Even ((morseSourceBrokenDegreeOneSet f₁ S hX₀ p q).ncard +
        (morseTargetBrokenDegreeOneSet f₀ S hX₁ p q).ncard + N p q)) := by
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.add_apply,
    morseBoundary_morseDegreeOneMap_single_apply h₁ hf₁ p q
      (finite_morseTargetBrokenDegreeOneSet h₁ hf₁ p q (hS p)),
    morseDegreeOneMap_morseBoundary_single_apply h₀ hf₀ hf₁ p q
      (finite_morseSourceBrokenDegreeOneSet h₀ hf₀ p q (hS · q)), hG]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [ite_eq_left hind, ← CharTwo.add_eq_zero, ← ZMod.natCast_eq_zero_iff_even,
      imp_iff_right hind]
    push_cast
    convert Iff.rfl using 2
    ring
  · -- Between critical points of different index both counts vanish.
    have hsrc : morseSourceBrokenDegreeOneSet f₁ S hX₀ p q = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseSourceBrokenDegreeOneSet] at hx; omega)
    have htgt : morseTargetBrokenDegreeOneSet f₀ S hX₁ p q = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseTargetBrokenDegreeOneSet] at hx; omega)
    simp [hsrc, htgt, hind]

include h₀ hf₀ h₁ in
/-- **The degree-one identity holds exactly when the ends come in pairs.** Let `G` be a map whose
`q`-coefficient at `p` is `N p q` modulo two between critical points of equal index and `0`
otherwise. When the slices `S p q` between critical points whose indices differ by one are finite,
the degree-one map `K` of `S` satisfies `∂₁ ∘ K + K ∘ ∂₀ = G` exactly when, between any critical
point `p` of `f₀` and any critical point `q` of `f₁` of the same index, the trajectories broken at
the source and at the target, together with the `N p q` further ends, are evenly many in total. -/
theorem morseBoundary_comp_morseDegreeOneMap_add_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 → (S p q).Finite)
    {G : (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2)}
    {N : criticalPoints 𝓘(ℝ, E) f₀ → criticalPoints 𝓘(ℝ, E) f₁ → ℕ}
    (hG : ∀ p q, G (Finsupp.single p 1) q =
      if manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q then (N p q : ZMod 2)
      else 0) :
    h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ S +
        morseDegreeOneMap f₀ hf₁ S ∘ₗ h₀.morseBoundary hf₀ = G ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
          Even ((morseSourceBrokenDegreeOneSet f₁ S hX₀ p q).ncard +
            (morseTargetBrokenDegreeOneSet f₀ S hX₁ p q).ncard + N p q) := by
  -- Compare the two sides coefficientwise on each critical point.
  simp_rw [← morseDegreeOne_single_apply_eq_iff h₀ hf₀ h₁ hf₁ hS hG]
  exact ⟨fun h p q ↦ by rw [h], fun h ↦
    Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring <| Finsupp.ext (h p)⟩

end Count

/-! ### The graded degree-one map and the chain homotopy -/

section Graded

variable (f₀) in
/-- **The graded mod-two degree-one map** of a slice family `S`. The `ZMod 2`-linear map from the
free module on the critical points of `f₀` of index `i` to the free module on the critical points
of `f₁` of index `j` sending `p` to the sum of the critical points `q`, each weighted by the number
of points of `S p q` modulo two. As for `morseDegreeOneCoeff`, an infinite slice contributes `0`.
It is the restriction of `morseDegreeOneMap`, and it vanishes unless `j = i + 1`
(`TauCeti.morseDegreeOneMapAt_eq_zero`). -/
noncomputable def morseDegreeOneMapAt (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (S : M → M → Set α) (i j : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2) →ₗ[ZMod 2]
      ({q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j} →₀ ZMod 2) :=
  Finsupp.lsubtypeDomain {q : criticalPoints 𝓘(ℝ, E) f₁ | manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j} ∘ₗ
    morseDegreeOneMap f₀ hf₁ S ∘ₗ Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded degree-one map of a chain `c` is the sum over the critical
points `p` of index `i` of `c p` times the coefficient `morseDegreeOneCoeff`. -/
theorem morseDegreeOneMapAt_apply {i j : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j}) :
    morseDegreeOneMapAt f₀ hf₁ S i j c q =
      c.sum fun p a ↦ a * morseDegreeOneCoeff f₀ f₁ S p.val q.val := by
  rw [morseDegreeOneMapAt, LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.lmapDomain_apply,
    morseDegreeOneMap_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded degree-one map of `a • p` is `a` times the coefficient
`morseDegreeOneCoeff`. -/
@[simp]
theorem morseDegreeOneMapAt_single_apply {i j : ℕ}
    (p : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i}) (a : ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = j}) :
    morseDegreeOneMapAt f₀ hf₁ S i j (Finsupp.single p a) q =
      a * morseDegreeOneCoeff f₀ f₁ S p.val q.val := by
  rw [morseDegreeOneMapAt_apply, Finsupp.sum_single_index (zero_mul _)]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded degree-one map raises the index by one**: from the chains of index `i` to those
of index `j` it vanishes unless `j = i + 1`. -/
theorem morseDegreeOneMapAt_eq_zero {i j : ℕ} (hij : j ≠ i + 1) :
    morseDegreeOneMapAt f₀ hf₁ S i j = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [morseDegreeOneMapAt_single_apply, morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one
    (by rw [p.property, q.property]; exact hij), mul_zero, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded and total degree-one maps agree.** Including the chains of index `i` and of index
`i + 1` into all Morse chains intertwines the graded degree-one map with the total one
`morseDegreeOneMap`: the degree-one map of a chain of index `i` is a chain of index `i + 1`. -/
@[simp]
theorem mapDomain_morseDegreeOneMapAt {i : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = i} →₀ ZMod 2) :
    (morseDegreeOneMapAt f₀ hf₁ S i (i + 1) c).mapDomain Subtype.val =
      morseDegreeOneMap f₀ hf₁ S (c.mapDomain Subtype.val) := by
  ext q
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = i + 1
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨q, hq⟩
  · -- Outside index `i + 1` both sides vanish: the left side by support, the right side because
    -- every coefficient of the degree-one map from index `i` to `q` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨r, hr⟩ ↦ hq (hr ▸ r.property),
      morseDegreeOneMap_apply,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul .., Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [morseDegreeOneCoeff_eq_zero_of_manifoldMorseIndex_ne_add_one (by grind), mul_zero]

end Graded

section Homotopy

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
  {φAt : ∀ n : ℕ,
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = n} →₀ ZMod 2) →ₗ[ZMod 2]
      ({q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = n} →₀ ZMod 2)}
  {Φ : (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2)}

include h₀ hf₀ h₁ hf₁ in
/-- The graded identity `∂₁ ∘ K + K ∘ ∂₀ = Φ + F` in degree `0`, where there is no boundary out of
the chains. -/
private theorem morseDegreeOneMapAt_zero_eq
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ S +
        morseDegreeOneMap f₀ hf₁ S ∘ₗ h₀.morseBoundary hf₀ = Φ + morseContinuationMap f₀ hf₁ V) :
    φAt 0 = h₁.morseBoundaryAt hf₁ 0 ∘ₗ morseDegreeOneMapAt f₀ hf₁ S 0 1 +
      morseContinuationMapAt f₀ hf₁ V 0 := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hK (Finsupp.single p.val 1)
  have h0 := h₀.morseBoundary_mapDomain_eq_zero_of_index_zero hf₀ (Finsupp.single p 1)
  simp only [Finsupp.mapDomain_single] at h0
  simp only [LinearMap.add_apply, LinearMap.comp_apply, h0, map_zero, add_zero] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, hΦ, mapDomain_morseContinuationMapAt, h₁.mapDomain_morseBoundaryAt hf₁,
    mapDomain_morseDegreeOneMapAt, Finsupp.mapDomain_single, this, add_assoc,
    ZModModule.add_self, add_zero]

include h₀ hf₀ h₁ hf₁ in
/-- The graded identity `∂₁ ∘ K + K ∘ ∂₀ = Φ + F` in degree `n + 1`. -/
private theorem morseDegreeOneMapAt_succ_eq
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ S +
        morseDegreeOneMap f₀ hf₁ S ∘ₗ h₀.morseBoundary hf₀ = Φ + morseContinuationMap f₀ hf₁ V)
    (n : ℕ) :
    φAt (n + 1) = morseDegreeOneMapAt f₀ hf₁ S n (n + 1) ∘ₗ h₀.morseBoundaryAt hf₀ n +
      h₁.morseBoundaryAt hf₁ (n + 1) ∘ₗ morseDegreeOneMapAt f₀ hf₁ S (n + 1) (n + 2) +
        morseContinuationMapAt f₀ hf₁ V (n + 1) := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  have := LinearMap.congr_fun hK (Finsupp.single p.val 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at this
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_add, hΦ, mapDomain_morseContinuationMapAt, h₁.mapDomain_morseBoundaryAt hf₁,
    h₀.mapDomain_morseBoundaryAt hf₀, mapDomain_morseDegreeOneMapAt, Finsupp.mapDomain_single]
  rw [add_comm (morseDegreeOneMap f₀ hf₁ S _), this, add_assoc, ZModModule.add_self, add_zero]

/-- **The chain homotopy of a degree-one map.** Let `φ` be a morphism between the mod-two Morse
chain complexes whose component in degree `n` is a graded map `φAt n` restricting a total map `Φ`
that commutes with the Morse boundaries. When the degree-one map `K` of a slice family `S`
satisfies `∂₁ ∘ K + K ∘ ∂₀ = Φ + F` for the continuation map `F` along `V`, the graded degree-one
map is a chain homotopy from `φ` to the continuation morphism of `V`, which is a chain map by
`LinearMap.comp_eq_comp_of_comp_add_comp_eq_add`. -/
noncomputable def morseDegreeOneHomotopy (φ : h₀.morseComplex hf₀ ⟶ h₁.morseComplex hf₁)
    (hφ : ∀ n, φ.f n = ModuleCat.ofHom (φAt n))
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ Φ = Φ ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ S +
        morseDegreeOneMap f₀ hf₁ S ∘ₗ h₀.morseBoundary hf₀ = Φ + morseContinuationMap f₀ hf₁ V) :
    Homotopy φ (morseContinuationHom h₀ hf₀ h₁ hf₁
      (LinearMap.comp_eq_comp_of_comp_add_comp_eq_add (h₀.morseBoundary_comp_morseBoundary hf₀)
        (h₁.morseBoundary_comp_morseBoundary hf₁) hcomm hK)) where
  hom i j := ModuleCat.ofHom (morseDegreeOneMapAt f₀ hf₁ S i j)
  zero i j hij := by
    rw [morseDegreeOneMapAt_eq_zero hf₁ fun h ↦ hij (by simp [h]), ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  comm i := by
    -- The components `ModuleCat.ofHom (morseDegreeOneMapAt ...)` have source and target
    -- `ModuleCat.of (ZMod 2) (... →₀ ZMod 2)`, while `dNext` and `prevD` expect the terms
    -- `(morseComplex _).X i` of the Morse complexes; these agree only up to unfolding
    -- `morseComplex` (`IsAdaptedPseudoGradient.IsMorseSmale.morseComplex_X`), so plain `rw`
    -- cannot match them and `erw` is needed.
    rcases i with _ | n
    · erw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      rw [zero_add, h₁.morseComplex_d hf₁, hφ, morseContinuationHom_f]
      -- The terms of the Morse complexes are not syntactically the free modules on which the
      -- graded maps act, so compare the underlying linear maps.
      apply ModuleCat.hom_ext
      exact morseDegreeOneMapAt_zero_eq h₀ hf₀ h₁ hf₁ hΦ hK
    · erw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      rw [h₀.morseComplex_d hf₀, h₁.morseComplex_d hf₁, hφ, morseContinuationHom_f]
      apply ModuleCat.hom_ext
      exact morseDegreeOneMapAt_succ_eq h₀ hf₀ h₁ hf₁ hΦ hK n

/-- The components of the chain homotopy of a degree-one map are the graded degree-one maps. -/
@[simp]
theorem morseDegreeOneHomotopy_hom (φ : h₀.morseComplex hf₀ ⟶ h₁.morseComplex hf₁)
    (hφ : ∀ n, φ.f n = ModuleCat.ofHom (φAt n))
    (hΦ : ∀ n c, (φAt n c).mapDomain Subtype.val = Φ (c.mapDomain Subtype.val))
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ Φ = Φ ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ S +
        morseDegreeOneMap f₀ hf₁ S ∘ₗ h₀.morseBoundary hf₀ = Φ + morseContinuationMap f₀ hf₁ V)
    (i j : ℕ) :
    (morseDegreeOneHomotopy h₀ hf₀ h₁ hf₁ φ hφ hΦ hcomm hK).hom i j =
      ModuleCat.ofHom (morseDegreeOneMapAt f₀ hf₁ S i j) :=
  (rfl)

end Homotopy

/-! ### Product fields -/

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

include h hf in
/-- **The Morse index does not rise along a trajectory of a product field.** Under the Morse–Smale
condition, if an integral curve of the product field `(X x, Y b)` on `M × N` runs from `(p, b)` to
`(q, b')`, then `ind q ≤ ind p`: its space component is a trajectory of `X` from `p` to `q`. -/
theorem manifoldMorseIndex_le_of_isMIntegralCurve_prodVectorField
    {Y : (b : N) → TangentSpace J b} {γ : ℝ → M × N}
    (hγ : IsMIntegralCurve γ (Manifold.prodVectorField X Y)) {p q : M} {b b' : N}
    (hp : Tendsto γ atBot (𝓝 (p, b))) (hq : Tendsto γ atTop (𝓝 (q, b'))) :
    manifoldMorseIndex 𝓘(ℝ, E) f q ≤ manifoldMorseIndex 𝓘(ℝ, E) f p := by
  rcases eq_or_ne p q with rfl | hpq
  · exact le_rfl
  obtain ⟨hy, -⟩ := hX.mem_unstableSet_inter_stableSet_of_isMIntegralCurve
    (Manifold.isMIntegralCurve_prodVectorField_iff.1 hγ).1
    ((continuous_fst.tendsto _).comp hp) ((continuous_fst.tendsto _).comp hq)
  exact (h.manifoldMorseIndex_lt hf hpq ⟨_, hy⟩).le

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
