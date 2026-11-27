/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
import TauCeti.Data.Set.Card
import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# The mod-two Morse diagonal and the Leibniz rule of the Morse cup product

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them. The Morse cup product counts *Y-shaped flow
lines*: a root half-trajectory of `X₀` coming from a critical point `p` of `f₀` at `-∞`, and two
leaf half-trajectories of `X₁` and `X₂` going to critical points `q` of `f₁` and `r` of `f₂` at
`+∞`, all three meeting at a common vertex. Recording a Y-flow line by its vertex, these are the
points of the *Y-slice* (`TauCeti.IsAdaptedPseudoGradient.morseYSlice`)

`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`.

For generic data this is a manifold of dimension `ind p - ind q - ind r`, so it is finite when
`ind p = ind q + ind r`. The three pseudo-gradients must differ: for a single pseudo-gradient
`X₁ = X₂` the stable manifolds of distinct critical points are disjoint, so the Y-slice is empty
unless `q = r` (`TauCeti.IsAdaptedPseudoGradient.morseYSlice_eq_empty_of_ne`). For a single Morse
function `f` one instead perturbs the three edges on finite time intervals next to the vertex.
Moving the vertex conditions through the flows `Φᵢ` across those intervals turns the edges into
trajectories of the transported pseudo-gradients, adapted to the functions `f ∘ Φᵢ⁻¹`; this is why
three functions are allowed here.

As for the mod-two continuation maps and their homotopies
(`TauCeti.Geometry.Manifold.Morse.Boundary.DegreeOneHomotopy`), this file develops, for an
arbitrary slice family `S : M → M → M → Set α`, the part of the argument that does not depend on
what the slices are.

**The diagonal and the cup product.** The **Morse diagonal**
`Δ = TauCeti.morseDiagonalMap f₀ hf₁ hf₂ S` sends a critical point `p` of `f₀` to the sum of the
tensors `q ⊗ r` of critical points of `f₁` and `f₂` with `ind q + ind r = ind p`, each weighted by
the number of points of `S p q r` modulo two (`TauCeti.morseDiagonalCoeff`). Dualizing it gives the
**cup product** of linear forms on the mod-two Morse chains (`TauCeti.morseCupProduct`),
`a ∪ b = μ ∘ (a ⊗ b) ∘ Δ` for the multiplication `μ` of `ZMod 2`, whose value at `p` is the sum,
over the pairs `(q, r)` with `ind q + ind r = ind p`, of the number of points of `S p q r` modulo
two times `a q * b r`, an infinite slice counting `0` (`TauCeti.morseCupProduct_apply_single`).

**Broken Y-flow lines.** For `ind p = ind q + ind r + 1` the Y-flow lines form a one-dimensional
space, whose ends are the Y-flow lines broken along one of the three edges:

* at the root (`TauCeti.morseRootBrokenDiagonalSet`): a trajectory of `X₀` from `p` to a critical
  point `p'` of index `ind p - 1`, followed by a point of `S p' q r`;
* at the first leaf (`TauCeti.morseFirstLeafBrokenDiagonalSet`): a point of `S p q' r` for a
  critical point `q'` of index `ind q + 1`, followed by a trajectory of `X₁` from `q'` to `q`;
* at the second leaf (`TauCeti.morseSecondLeafBrokenDiagonalSet`): a point of `S p q r'` for a
  critical point `r'` of index `ind r + 1`, followed by a trajectory of `X₂` from `r'` to `r`.

When they are finitely many, they count the `(q, r)`-coefficients of `Δ (∂₀ p)`, of
`(∂₁ ⊗ 1) (Δ p)` and of `(1 ⊗ ∂₂) (Δ p)`. So `Δ` is a chain map,
`Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ`, exactly when the three kinds of broken Y-flow lines are evenly
many in total (`TauCeti.morseDiagonalMap_comp_morseBoundary_eq_iff`). Dually, this is the Leibniz
rule `δ(a ∪ b) = δa ∪ b + a ∪ δb` of the cup product for the coboundary `δa = a ∘ ∂`, for all linear
forms `a` and `b` (`TauCeti.morseCupProduct_comp_morseBoundary_eq_iff`); over `ZMod 2` the Koszul
sign `(-1)^|a|` is `1`. The geometric half, that the broken Y-flow lines are the ends of the
compactified one-dimensional spaces of Y-flow lines and so come in pairs, needs their
compactification and gluing, and is not proved here.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.morseYSlice`: the vertices of the Y-flow lines.
* `TauCeti.IsAdaptedPseudoGradient.morseYSlice_eq_empty_of_ne`: for equal leaf pseudo-gradients
  the Y-slices between distinct leaf critical points are empty.
* `TauCeti.morseDiagonalCoeff`, `TauCeti.morseDiagonalMap`: the coefficients of the Morse diagonal
  of a slice family, and the diagonal.
* `TauCeti.morseCupProduct`: the cup product of linear forms on the Morse chains, with
  `TauCeti.morseCupProduct_apply_single` computing it on a critical point.
* `TauCeti.morseRootBrokenDiagonalSet`, `TauCeti.morseFirstLeafBrokenDiagonalSet`,
  `TauCeti.morseSecondLeafBrokenDiagonalSet`: the broken Y-flow lines.
* `TauCeti.morseDiagonalMap_comp_morseBoundary_eq_iff`: the diagonal is a chain map exactly when the
  broken Y-flow lines are evenly many.
* `TauCeti.morseCupProduct_comp_morseBoundary_eq_iff`: the cup product satisfies the Leibniz rule
  exactly when the diagonal is a chain map.

## References

* K. Fukaya, *Morse homotopy, A∞-category, and Floer homologies*, Proceedings of GARC Workshop on
  Geometry and Topology '93, Seoul National University, 1993 (products by counting flow trees for
  three Morse functions).
* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  arXiv:1611.07916, §§1–5 (perturbed Y-flow lines for a single Morse function).
-/

public section

open Set
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {α : Type*}

/-! ### The Y-slice of three pseudo-gradients -/

namespace IsAdaptedPseudoGradient

section YSlice

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂)

/-- The **Y-slice** from `p` to `q` and `r`: the points of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`. Each is the vertex of a Y-shaped flow line made of a
half-trajectory of `X₀` from `p` at `-∞` and half-trajectories of `X₁` and `X₂` to `q` and `r` at
`+∞`. -/
noncomputable def morseYSlice (p q r : M) : Set M :=
  hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q ∩ hX₂.flow.stableSet r

/-- Membership in the Y-slice. -/
@[simp]
theorem mem_morseYSlice {p q r x : M} :
    x ∈ hX₀.morseYSlice hX₁ hX₂ p q r ↔
      x ∈ hX₀.flow.unstableSet p ∧ x ∈ hX₁.flow.stableSet q ∧ x ∈ hX₂.flow.stableSet r := by
  rw [morseYSlice, mem_inter_iff, mem_inter_iff, and_assoc]

/-- The Y-slice is the intersection `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`. -/
theorem morseYSlice_def (p q r : M) :
    hX₀.morseYSlice hX₁ hX₂ p q r =
      hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q ∩ hX₂.flow.stableSet r :=
  (rfl)

/-- Exchanging the two leaves of a Y-slice. -/
theorem morseYSlice_comm (p q r : M) :
    hX₀.morseYSlice hX₂ hX₁ p r q = hX₀.morseYSlice hX₁ hX₂ p q r := by
  rw [morseYSlice_def, morseYSlice_def, inter_right_comm]

/-- **One pseudo-gradient on both leaves gives no Y-flow lines between distinct critical points.**
The stable manifolds of distinct critical points of `X₁` are disjoint, so the Y-slice with both
leaves on `X₁` is empty unless the two leaf critical points agree. This is why the two leaves of a
Y-flow line must follow different flows. -/
theorem morseYSlice_eq_empty_of_ne {p q r : M} (hqr : q ≠ r) :
    hX₀.morseYSlice hX₁ hX₁ p q r = ∅ :=
  eq_empty_of_forall_notMem fun _ hx ↦
    (Flow.disjoint_stableSet hqr).le_bot ⟨((hX₀.mem_morseYSlice hX₁ hX₁).1 hx).2.1,
      ((hX₀.mem_morseYSlice hX₁ hX₁).1 hx).2.2⟩

end YSlice

end IsAdaptedPseudoGradient

/-! ### The Morse diagonal and the cup product -/

section Definitions

variable {f₀ f₁ f₂ : M → ℝ} {S : M → M → M → Set α}

variable (f₀ f₁ f₂ S) in
/-- The coefficient of `q ⊗ r` in the Morse diagonal of the slice family `S` at `p`, for critical
points `p`, `q` and `r` of `f₀`, `f₁` and `f₂`: the number of points of `S p q r` modulo two when
`ind p = ind q + ind r`, and `0` otherwise. It is a count of Y-flow lines only when the slice
`S p q r` is finite; an infinite slice contributes `0`. -/
noncomputable def morseDiagonalCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) : ZMod 2 :=
  if manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r then
    (S p q r).ncard
  else 0

/-- When `ind p = ind q + ind r`, the coefficient of the Morse diagonal is the number of points of
the slice modulo two. -/
theorem morseDiagonalCoeff_eq_ncard {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    morseDiagonalCoeff f₀ f₁ f₂ S p q r = ((S p q r).ncard : ZMod 2) := by
  simp [morseDiagonalCoeff, hind]

/-- The coefficient of the Morse diagonal vanishes unless `ind p = ind q + ind r`: the diagonal
preserves the total Morse index. -/
@[simp]
theorem morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    morseDiagonalCoeff f₀ f₁ f₂ S p q r = 0 := by
  simp [morseDiagonalCoeff, hind]

variable [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (f₀) in
/-- **The mod-two Morse diagonal** of a slice family `S`, from the mod-two Morse chains of `f₀` to
the tensor product of those of the Morse functions `f₁` and `f₂`. It sends a critical point `p` of
`f₀` to the sum of the tensors `q ⊗ r` with `ind q + ind r = ind p`, each weighted by the number of
points of `S p q r` modulo two. As for `morseDiagonalCoeff`, an infinite slice contributes `0`. -/
noncomputable def morseDiagonalMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (S : M → M → M → Set α) :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2]
      (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) ⊗[ZMod 2] (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  haveI := hf₂.finite_criticalPoints.to_subtype
  (finsuppTensorFinsupp' (ZMod 2) _ _).symm.toLinearMap ∘ₗ
    Finsupp.linearCombination (ZMod 2) fun p ↦
      Finsupp.ofSupportFinite (fun x ↦ morseDiagonalCoeff f₀ f₁ f₂ S p x.1 x.2) (toFinite _)

/-- The coefficient of `q ⊗ r` in the Morse diagonal of a chain `c` is the sum over the critical
points `p` of `c p` times the coefficient `morseDiagonalCoeff`. -/
theorem finsuppTensorFinsupp'_morseDiagonalMap_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hf₂ : IsMorse 𝓘(ℝ, E) f₂) (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' (ZMod 2) _ _ (morseDiagonalMap f₀ hf₁ hf₂ S c) (q, r) =
      c.sum fun p a ↦ a * morseDiagonalCoeff f₀ f₁ f₂ S p q r := by
  simp [morseDiagonalMap, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q ⊗ r` in the Morse diagonal of `a • p` is `a` times the coefficient
`morseDiagonalCoeff`. -/
@[simp]
theorem finsuppTensorFinsupp'_morseDiagonalMap_single_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hf₂ : IsMorse 𝓘(ℝ, E) f₂) (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) (a : ZMod 2) :
    finsuppTensorFinsupp' (ZMod 2) _ _ (morseDiagonalMap f₀ hf₁ hf₂ S (Finsupp.single p a)) (q, r) =
      a * morseDiagonalCoeff f₀ f₁ f₂ S p q r := by
  rw [finsuppTensorFinsupp'_morseDiagonalMap_apply, Finsupp.sum_single_index (zero_mul _)]

variable (f₀) in
/-- **The mod-two Morse cup product** of a slice family `S`: the product of a linear form `a` on
the Morse chains of `f₁` and a linear form `b` on those of `f₂` is the linear form
`a ∪ b = μ ∘ (a ⊗ b) ∘ Δ` on the Morse chains of `f₀`, for the Morse diagonal `Δ` of `S` and the
multiplication `μ` of `ZMod 2`. Its value at a critical point `p` is the sum, over the pairs
`(q, r)` with `ind q + ind r = ind p`, of the number of points of `S p q r` modulo two times
`a q * b r`, an infinite slice counting `0` (`TauCeti.morseCupProduct_apply_single`). It is the
bilinear cup product `LinearMap.cupProduct` along the diagonal. -/
noncomputable def morseCupProduct (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (S : M → M → M → Set α) :
    ((criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2]
      ((criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2]
        ((criticalPoints 𝓘(ℝ, E) f₀ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
  (morseDiagonalMap f₀ hf₁ hf₂ S).cupProduct

/-- The cup product `a ∪ b` is `μ ∘ (a ⊗ b) ∘ Δ`. -/
theorem morseCupProduct_apply (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    morseCupProduct f₀ hf₁ hf₂ S a b =
      LinearMap.mul' (ZMod 2) (ZMod 2) ∘ₗ TensorProduct.map a b ∘ₗ
        morseDiagonalMap f₀ hf₁ hf₂ S :=
  LinearMap.cupProduct_apply _ a b

/-- **The cup product on a critical point.** The value of `a ∪ b` at a critical point `p` of `f₀`
is the sum, over the critical points `q` of `f₁` and `r` of `f₂`, of the coefficient
`morseDiagonalCoeff` times `a q * b r`. -/
theorem morseCupProduct_apply_single [Fintype (criticalPoints 𝓘(ℝ, E) f₁)]
    [Fintype (criticalPoints 𝓘(ℝ, E) f₂)] (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (p : criticalPoints 𝓘(ℝ, E) f₀) :
    morseCupProduct f₀ hf₁ hf₂ S a b (Finsupp.single p 1) =
      ∑ x : criticalPoints 𝓘(ℝ, E) f₁ × criticalPoints 𝓘(ℝ, E) f₂,
        morseDiagonalCoeff f₀ f₁ f₂ S p x.1 x.2 *
          (a (Finsupp.single x.1 1) * b (Finsupp.single x.2 1)) := by
  rw [morseCupProduct, LinearMap.cupProduct_apply_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [finsuppTensorFinsupp'_morseDiagonalMap_single_apply, one_mul]

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {S : M → M → M → Set α}

/-! ### Broken Y-flow lines -/

section BrokenSets

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂)

variable (f₁ f₂ S) in
/-- The Y-flow lines of the slice family `S` from `p` to `q` and `r` broken at the root: triples
`(p', z, y)` of a critical point `p'` of `f₀` with `ind p = ind p' + 1` and
`ind p' = ind q + ind r`, a point `z` on the middle-level slice of the trajectories of `X₀` from
`p` to `p'`, and a point `y` of the slice `S p' q r`. -/
def morseRootBrokenDiagonalSet (p q r : M) : Set (criticalPoints 𝓘(ℝ, E) f₀ × M × α) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
    x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ S x.1 q r}

/-- Membership in the set of Y-flow lines broken at the root. -/
@[simp]
theorem mem_morseRootBrokenDiagonalSet {p q r : M} {x : criticalPoints 𝓘(ℝ, E) f₀ × M × α} :
    x ∈ morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
          x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ S x.1 q r :=
  Iff.rfl

variable (f₀ f₂ S) in
/-- The Y-flow lines of the slice family `S` from `p` to `q` and `r` broken at the first leaf:
triples `(q', y, z)` of a critical point `q'` of `f₁` with `ind p = ind q' + ind r` and
`ind q' = ind q + 1`, a point `y` of the slice `S p q' r`, and a point `z` on the middle-level
slice of the trajectories of `X₁` from `q'` to `q`. -/
def morseFirstLeafBrokenDiagonalSet (p q r : M) : Set (criticalPoints 𝓘(ℝ, E) f₁ × α × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
    x.2.1 ∈ S p x.1 r ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 q}

/-- Membership in the set of Y-flow lines broken at the first leaf. -/
@[simp]
theorem mem_morseFirstLeafBrokenDiagonalSet {p q r : M}
    {x : criticalPoints 𝓘(ℝ, E) f₁ × α × M} :
    x ∈ morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
          x.2.1 ∈ S p x.1 r ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 q :=
  Iff.rfl

variable (f₀ f₁ S) in
/-- The Y-flow lines of the slice family `S` from `p` to `q` and `r` broken at the second leaf:
triples `(r', y, z)` of a critical point `r'` of `f₂` with `ind p = ind q + ind r'` and
`ind r' = ind r + 1`, a point `y` of the slice `S p q r'`, and a point `z` on the middle-level
slice of the trajectories of `X₂` from `r'` to `r`. -/
def morseSecondLeafBrokenDiagonalSet (p q r : M) : Set (criticalPoints 𝓘(ℝ, E) f₂ × α × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 ∧
    x.2.1 ∈ S p q x.1 ∧ x.2.2 ∈ hX₂.morseTrajectorySlice x.1 r}

/-- Membership in the set of Y-flow lines broken at the second leaf. -/
@[simp]
theorem mem_morseSecondLeafBrokenDiagonalSet {p q r : M}
    {x : criticalPoints 𝓘(ℝ, E) f₂ × α × M} :
    x ∈ morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 ∧
          x.2.1 ∈ S p q x.1 ∧ x.2.2 ∈ hX₂.morseTrajectorySlice x.1 r :=
  Iff.rfl

end BrokenSets

/-! ### Counting broken Y-flow lines -/

section Count

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

include h₀ hf₀ in
/-- **Finitely many Y-flow lines broken at the root**, when the slices `S p' q r` with
`ind p' = ind q + ind r` are finite. -/
theorem finite_morseRootBrokenDiagonalSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hS : ∀ p' : criticalPoints 𝓘(ℝ, E) f₀, manifoldMorseIndex 𝓘(ℝ, E) f₀ p' =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r → (S p' q r).Finite) :
    (morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r).Finite := by
  have := hf₀.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀) hS

include h₁ hf₁ in
/-- **Finitely many Y-flow lines broken at the first leaf**, when the slices `S p q' r` with
`ind p = ind q' + ind r` are finite. -/
theorem finite_morseFirstLeafBrokenDiagonalSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hS : ∀ q' : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' + manifoldMorseIndex 𝓘(ℝ, E) f₂ r → (S p q' r).Finite) :
    (morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r).Finite := by
  have := hf₁.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem hS fun _ ↦ h₁.finite_morseTrajectorySlice hf₁

include h₂ hf₂ in
/-- **Finitely many Y-flow lines broken at the second leaf**, when the slices `S p q r'` with
`ind p = ind q + ind r'` are finite. -/
theorem finite_morseSecondLeafBrokenDiagonalSet (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hS : ∀ r' : criticalPoints 𝓘(ℝ, E) f₂, manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r' → (S p q r').Finite) :
    (morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r).Finite := by
  have := hf₂.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem hS fun _ ↦ h₂.finite_morseTrajectorySlice hf₂

include h₀ in
/-- **`Δ ∘ ∂₀` counts Y-flow lines broken at the root.** When they are finitely many, the
`(q, r)`-coefficient of the Morse diagonal of the Morse boundary of `p` is the number of Y-flow
lines from `p` to `q` and `r` broken at the root, modulo two. -/
theorem finsuppTensorFinsupp'_morseDiagonalMap_morseBoundary_single_apply
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hfin : (morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r).Finite) :
    finsuppTensorFinsupp' (ZMod 2) _ _
        (morseDiagonalMap f₀ hf₁ hf₂ S (h₀.morseBoundary hf₀ (Finsupp.single p 1))) (q, r) =
      ((morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r).ncard : ZMod 2) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [finsuppTensorFinsupp'_morseDiagonalMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    morseRootBrokenDiagonalSet]
  -- Sort the broken Y-flow lines by their intermediate critical point `p'`. The index conditions
  -- and slice families are named because unification cannot read them off `hfin`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun p' : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (Q := fun p' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ p' =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (S · q r)) (fun p' hind ↦ ?_)
    (fun p' hind ↦ ?_) (fun _ ↦ morseDiagonalCoeff_eq_ncard)
    (fun _ ↦ morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne) hfin).symm
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_ncard hf₀ hind]
  · rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
      h₀.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₀ hind]

include h₁ in
/-- **`(∂₁ ⊗ 1) ∘ Δ` counts Y-flow lines broken at the first leaf.** When they are finitely many,
the `(q, r)`-coefficient of `(∂₁ ⊗ 1) (Δ p)` is the number of Y-flow lines from `p` to `q` and `r`
broken at the first leaf, modulo two. -/
theorem finsuppTensorFinsupp'_rTensor_morseBoundary_morseDiagonalMap_single_apply
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hfin : (morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r).Finite) :
    finsuppTensorFinsupp' (ZMod 2) _ _ ((h₁.morseBoundary hf₁).rTensor _
        (morseDiagonalMap f₀ hf₁ hf₂ S (Finsupp.single p 1))) (q, r) =
      ((morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r).ncard : ZMod 2) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [finsuppTensorFinsupp'_rTensor_apply, morseFirstLeafBrokenDiagonalSet]
  simp_rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul]
  -- Sort the broken Y-flow lines by their intermediate critical point `q'`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun q' : criticalPoints 𝓘(ℝ, E) f₁ ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (Q := fun q' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)
    (A := (S p · r)) (B := (hX₁.morseTrajectorySlice · q)) (fun q' hind ↦ ?_)
    (fun q' hind ↦ ?_) (fun _ ↦ h₁.morseBoundaryCoeff_eq_ncard hf₁)
    (fun _ ↦ h₁.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₁) hfin).symm
  · rw [finsuppTensorFinsupp'_morseDiagonalMap_single_apply, one_mul,
      morseDiagonalCoeff_eq_ncard hind]
  · rw [finsuppTensorFinsupp'_morseDiagonalMap_single_apply, one_mul,
      morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne hind]

include h₂ in
/-- **`(1 ⊗ ∂₂) ∘ Δ` counts Y-flow lines broken at the second leaf.** When they are finitely many,
the `(q, r)`-coefficient of `(1 ⊗ ∂₂) (Δ p)` is the number of Y-flow lines from `p` to `q` and `r`
broken at the second leaf, modulo two. -/
theorem finsuppTensorFinsupp'_lTensor_morseBoundary_morseDiagonalMap_single_apply
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hfin : (morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r).Finite) :
    finsuppTensorFinsupp' (ZMod 2) _ _ ((h₂.morseBoundary hf₂).lTensor _
        (morseDiagonalMap f₀ hf₁ hf₂ S (Finsupp.single p 1))) (q, r) =
      ((morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r).ncard : ZMod 2) := by
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  rw [finsuppTensorFinsupp'_lTensor_apply, morseSecondLeafBrokenDiagonalSet]
  simp_rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul]
  -- Sort the broken Y-flow lines by their intermediate critical point `r'`.
  refine (natCast_ncard_setOf_and_and_mem_and_mem
    (P := fun r' : criticalPoints 𝓘(ℝ, E) f₂ ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r')
    (Q := fun r' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₂ r' = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1)
    (A := (S p q ·)) (B := (hX₂.morseTrajectorySlice · r)) (fun r' hind ↦ ?_)
    (fun r' hind ↦ ?_) (fun _ ↦ h₂.morseBoundaryCoeff_eq_ncard hf₂)
    (fun _ ↦ h₂.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf₂) hfin).symm
  · rw [finsuppTensorFinsupp'_morseDiagonalMap_single_apply, one_mul,
      morseDiagonalCoeff_eq_ncard hind]
  · rw [finsuppTensorFinsupp'_morseDiagonalMap_single_apply, one_mul,
      morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne hind]

include h₀ hf₀ h₁ h₂ in
/-- The chain-map identity `Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ` at the coefficient of `q ⊗ r` in the
image of `p`: under the hypotheses of `TauCeti.morseDiagonalMap_comp_morseBoundary_eq_iff`, it holds
exactly when the broken Y-flow lines from `p` to `q` and `r` are evenly many, or the indices do not
fit. -/
private theorem morseDiagonal_single_apply_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r → (S p q r).Finite)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' (ZMod 2) _ _
        ((morseDiagonalMap f₀ hf₁ hf₂ S ∘ₗ h₀.morseBoundary hf₀) (Finsupp.single p 1)) (q, r) =
      finsuppTensorFinsupp' (ZMod 2) _ _
        ((((h₁.morseBoundary hf₁).rTensor _ + (h₂.morseBoundary hf₂).lTensor _) ∘ₗ
          morseDiagonalMap f₀ hf₁ hf₂ S) (Finsupp.single p 1)) (q, r) ↔
    (manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 →
      Even ((morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r).ncard +
        (morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r).ncard +
        (morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r).ncard)) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add, Finsupp.add_apply,
    finsuppTensorFinsupp'_morseDiagonalMap_morseBoundary_single_apply h₀ hf₀ hf₁ hf₂ p q r
      (finite_morseRootBrokenDiagonalSet h₀ hf₀ p q r (hS · q r)),
    finsuppTensorFinsupp'_rTensor_morseBoundary_morseDiagonalMap_single_apply h₁ hf₁ hf₂ p q r
      (finite_morseFirstLeafBrokenDiagonalSet h₁ hf₁ p q r (hS p · r)),
    finsuppTensorFinsupp'_lTensor_morseBoundary_morseDiagonalMap_single_apply hf₁ h₂ hf₂ p q r
      (finite_morseSecondLeafBrokenDiagonalSet h₂ hf₂ p q r (hS p q ·))]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1
  · rw [imp_iff_right hind, ← ZMod.natCast_eq_zero_iff_even, ← CharTwo.add_eq_zero]
    push_cast
    convert Iff.rfl using 2
    ring
  · -- When the indices do not fit, there are no broken Y-flow lines of any kind.
    have hroot : morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseRootBrokenDiagonalSet] at hx; omega)
    have hfirst : morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseFirstLeafBrokenDiagonalSet] at hx; omega)
    have hsecond : morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by
        rw [mem_morseSecondLeafBrokenDiagonalSet] at hx; omega)
    simp [hroot, hfirst, hsecond, hind]

include h₀ hf₀ h₁ h₂ in
/-- **The Morse diagonal is a chain map exactly when the broken Y-flow lines come in pairs.** When
the slices `S p q r` with `ind p = ind q + ind r` are finite, the Morse diagonal `Δ` of `S`
satisfies `Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ` exactly when, for all critical points `p`, `q` and `r`
of `f₀`, `f₁` and `f₂` with `ind p = ind q + ind r + 1`, the Y-flow lines from `p` to `q` and `r`
broken at the root, at the first leaf and at the second leaf are evenly many in total. -/
theorem morseDiagonalMap_comp_morseBoundary_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r → (S p q r).Finite) :
    morseDiagonalMap f₀ hf₁ hf₂ S ∘ₗ h₀.morseBoundary hf₀ =
        ((h₁.morseBoundary hf₁).rTensor _ + (h₂.morseBoundary hf₂).lTensor _) ∘ₗ
          morseDiagonalMap f₀ hf₁ hf₂ S ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
        (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 →
        Even ((morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r).ncard +
          (morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r).ncard +
          (morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r).ncard) := by
  -- Compare the two sides coefficientwise on each critical point, through the identification of
  -- the tensor product with functions on pairs of critical points.
  simp_rw [← morseDiagonal_single_apply_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂ hS]
  refine ⟨fun h p q r ↦ by rw [h], fun h ↦ Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring ?_⟩
  exact (finsuppTensorFinsupp' (ZMod 2) _ _).injective (Finsupp.ext fun x ↦ h p x.1 x.2)

end Count

/-! ### The Leibniz rule of the cup product -/

section Leibniz

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

/-- **The cup product satisfies the Leibniz rule exactly when the diagonal is a chain map.** For
every slice family, `δ(a ∪ b) = δa ∪ b + a ∪ δb` for all linear forms `a` and `b` on the Morse
chains, where `δa = a ∘ ∂` is the Morse coboundary, exactly when the Morse diagonal satisfies
`Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ`. Over `ZMod 2` there is no Koszul sign. -/
theorem morseCupProduct_comp_morseBoundary_eq_iff_morseDiagonalMap_comp_morseBoundary_eq :
    (∀ (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2),
        morseCupProduct f₀ hf₁ hf₂ S a b ∘ₗ h₀.morseBoundary hf₀ =
          morseCupProduct f₀ hf₁ hf₂ S (a ∘ₗ h₁.morseBoundary hf₁) b +
            morseCupProduct f₀ hf₁ hf₂ S a (b ∘ₗ h₂.morseBoundary hf₂)) ↔
      morseDiagonalMap f₀ hf₁ hf₂ S ∘ₗ h₀.morseBoundary hf₀ =
        ((h₁.morseBoundary hf₁).rTensor _ + (h₂.morseBoundary hf₂).lTensor _) ∘ₗ
          morseDiagonalMap f₀ hf₁ hf₂ S :=
  LinearMap.cupProduct_comp_eq_iff_comp_eq_rTensor_add_lTensor_comp _ _ _ _

include h₀ hf₀ h₁ h₂ in
/-- **The Leibniz rule of the Morse cup product holds exactly when the broken Y-flow lines come in
pairs.** When the slices `S p q r` with `ind p = ind q + ind r` are finite, the cup product of `S`
satisfies `δ(a ∪ b) = δa ∪ b + a ∪ δb` for all linear forms `a` and `b` on the Morse chains exactly
when, for all critical points `p`, `q` and `r` of `f₀`, `f₁` and `f₂` with
`ind p = ind q + ind r + 1`, the Y-flow lines from `p` to `q` and `r` broken at the root, at the
first leaf and at the second leaf are evenly many in total. -/
theorem morseCupProduct_comp_morseBoundary_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r → (S p q r).Finite) :
    (∀ (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2),
        morseCupProduct f₀ hf₁ hf₂ S a b ∘ₗ h₀.morseBoundary hf₀ =
          morseCupProduct f₀ hf₁ hf₂ S (a ∘ₗ h₁.morseBoundary hf₁) b +
            morseCupProduct f₀ hf₁ hf₂ S a (b ∘ₗ h₂.morseBoundary hf₂)) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
        (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 →
        Even ((morseRootBrokenDiagonalSet f₁ f₂ S hX₀ p q r).ncard +
          (morseFirstLeafBrokenDiagonalSet f₀ f₂ S hX₁ p q r).ncard +
          (morseSecondLeafBrokenDiagonalSet f₀ f₁ S hX₂ p q r).ncard) :=
  (morseCupProduct_comp_morseBoundary_eq_iff_morseDiagonalMap_comp_morseBoundary_eq h₀ hf₀ h₁ hf₁
    h₂ hf₂).trans (morseDiagonalMap_comp_morseBoundary_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂ hS)

end Leibniz

end TauCeti
