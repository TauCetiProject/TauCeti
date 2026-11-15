/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.FiberCount
public import TauCeti.Geometry.Manifold.Complex.FiniteCWType
import TauCeti.Data.Set.Restrict

/-!
# Euler characteristics of branched covers

Let `f : X → Y` be a finite holomorphic map from a compact Riemann surface to a preconnected
Riemann surface, and let `S ⊆ Y` contain every branch value of `f`. By surjectivity `Y` is also
compact, so `X`, `Y`, and the complement in either surface of any finite set all have finite CW
type (`TauCeti.ComplexManifold.instFiniteCWType`, `TauCeti.ComplexManifold.instFiniteCWTypeCompl`).

Deleting `S` from the target and `f⁻¹(S)` from the source leaves a covering map whose fibres all
have `degree f` points. Finite-cover multiplicativity of the Euler characteristic therefore gives

`χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`

whenever `Y \ S` has finite CW type (in particular whenever `S` is finite).

When `S` is finite, adding the count of deleted points
`#f⁻¹(S) + ramificationDegree f = degree f · #S` gives the punctured form of the branched-cover
formula,

`(χ(X \ f⁻¹(S)) + #f⁻¹(S)) + ramificationDegree f = degree f · (χ(Y \ S) + #S)`.

For compact Riemann surfaces deleting a finite set subtracts its cardinality from the Euler
characteristic (`TauCeti.ComplexManifold.eulerChar_compl`), so the two parenthesised sums are
`χ(X)` and `χ(Y)`. Puncturing at `f.branchValues` gives the unconditional topological
Riemann--Hurwitz formula `χ(X) = degree f · χ(Y) - ramificationDegree f`. It uses only the
finite-CW Euler characteristic, local multiplicities and the analytic fibre-sum degree; no
canonical divisor and no Riemann--Roch theorem enters.

## Main results

* `FiniteHolomorphicMap.compactSpace_codomain`, `FiniteHolomorphicMap.finiteCWType_codomain`:
  the preconnected target `Y` is compact and hence has finite CW type.
* `FiniteHolomorphicMap.finiteCWType_compl_of_finite`,
  `FiniteHolomorphicMap.finiteCWType_compl_branchValues`: `Y \ S` (in particular
  `Y \ f.branchValues`) has finite CW type for any finite `S ⊆ Y`.
* `FiniteHolomorphicMap.finiteCWType_compl_preimage`: the punctured source has finite CW type
  when the punctured target does.
* `FiniteHolomorphicMap.eulerChar_compl_preimage`: `χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`.
* `FiniteHolomorphicMap.eulerChar_compl_preimage_add_ncard_add_ramificationDegree`: the punctured
  branched-cover formula for a finite set `S` of punctures containing the branch values.
* `FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree`:
  `χ(X) = degree f · χ(Y) - ramificationDegree f` unconditionally for every finite holomorphic map
  `f : X → Y` from a compact Riemann surface to a preconnected Riemann surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the topological proof of the Riemann--Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic of an `n`-sheeted covering space.
-/

public section

open Set
open scoped Manifold

universe u

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y]
  (f : FiniteHolomorphicMap X Y) {S : Set Y}

/-- If the target punctured at a set containing every branch value has finite CW type, so does
the source punctured at its preimage. -/
theorem finiteCWType_compl_preimage (hS : f.branchValues ⊆ S) [FiniteCWType ↥Sᶜ] :
    FiniteCWType ↥(f ⁻¹' S)ᶜ :=
  (f.isCoveringMap_restrictPreimage_compl hS).finiteCWType fun y ↦
    (Sᶜ.finite_preimage_restrictPreimage_iff.2 (by simpa using f.finite_fiber y)).to_subtype

variable [PreconnectedSpace Y]

section Codomain

include f
omit [T2Space X]

/-- The preconnected codomain of a finite holomorphic map from a compact Riemann surface is
compact, by surjectivity. -/
theorem compactSpace_codomain : CompactSpace Y :=
  ⟨f.surjective.range_eq ▸ isCompact_range f.holomorphic.continuous⟩

/-- The preconnected codomain of a finite holomorphic map from a compact Riemann surface has
finite CW type. -/
theorem finiteCWType_codomain : FiniteCWType Y := by
  have := f.compactSpace_codomain
  exact inferInstance

/-- Deleting a finite set from the preconnected codomain of `f` leaves an open Riemann surface of
finite CW type. -/
theorem finiteCWType_compl_of_finite (hfin : S.Finite) : FiniteCWType ↥Sᶜ := by
  have := f.compactSpace_codomain
  have := hfin.to_subtype
  exact inferInstance

/-- Deleting the branch values from the preconnected codomain of `f` leaves an open Riemann
surface of finite CW type. -/
theorem finiteCWType_compl_branchValues : FiniteCWType ↥f.branchValuesᶜ :=
  f.finiteCWType_compl_of_finite f.finite_branchValues

end Codomain

/-- Deleting the preimage of a finite set containing the branch values from the source leaves an
open Riemann surface of finite CW type. -/
theorem finiteCWType_compl_preimage_of_finite (hfin : S.Finite) (hS : f.branchValues ⊆ S) :
    FiniteCWType ↥(f ⁻¹' S)ᶜ := by
  have := f.finiteCWType_compl_of_finite hfin
  exact f.finiteCWType_compl_preimage hS

/-- **Euler characteristics of a punctured branched cover.** Deleting a set `S` containing every
branch value from the target, and its preimage from the source, multiplies Euler characteristics
by the degree: `χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`, provided `Y \ S` has finite CW type. -/
theorem eulerChar_compl_preimage (hS : f.branchValues ⊆ S) [FiniteCWType ↥Sᶜ] :
    @eulerChar ↥(f ⁻¹' S)ᶜ _ (f.finiteCWType_compl_preimage hS) = degree f * eulerChar ↥Sᶜ :=
  eulerChar_eq_mul_of_isCoveringMap (f.isCoveringMap_restrictPreimage_compl hS)
    (fun y ↦
      (Sᶜ.finite_preimage_restrictPreimage_iff.2 (by simpa using f.finite_fiber y)).to_subtype)
    fun y ↦ by
      rw [Nat.card_coe_set_eq, f.ncard_fiber_restrictPreimage_compl hS]

/-- **The punctured branched-cover formula.** For a finite set `S` containing every branch value,
`(χ(X \ f⁻¹(S)) + #f⁻¹(S)) + ramificationDegree f = degree f · (χ(Y \ S) + #S)`.
For compact Riemann surfaces the parenthesised sums are `χ(X)` and `χ(Y)`, which turns this into
the Riemann--Hurwitz formula. -/
theorem eulerChar_compl_preimage_add_ncard_add_ramificationDegree (hfin : S.Finite)
    (hS : f.branchValues ⊆ S) :
    @eulerChar ↥(f ⁻¹' S)ᶜ _ (f.finiteCWType_compl_preimage_of_finite hfin hS) +
        (f ⁻¹' S).ncard + ramificationDegree f =
      degree f * (@eulerChar ↥Sᶜ _ (f.finiteCWType_compl_of_finite hfin) + S.ncard) := by
  have := f.finiteCWType_compl_of_finite hfin
  have hcount : ((f ⁻¹' S).ncard + ramificationDegree f : ℤ) = degree f * S.ncard := by
    exact_mod_cast f.ncard_preimage_add_ramificationDegree hfin hS
  rw [f.eulerChar_compl_preimage hS]
  linear_combination hcount

/-- **The topological Riemann--Hurwitz formula in Euler-characteristic form.** For any finite
holomorphic map `f : X → Y` from a compact Riemann surface to a preconnected Riemann surface,
`χ(X) = deg f · χ(Y) - R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree :
    eulerChar X = degree f * @eulerChar Y _ f.finiteCWType_codomain - ramificationDegree f := by
  have : CompactSpace Y := f.compactSpace_codomain
  have := (f.finite_branchValues.preimage' fun y _ ↦ f.finite_fiber y).to_subtype
  have := f.finite_branchValues.to_subtype
  have hX := ComplexManifold.eulerChar_compl (f ⁻¹' f.branchValues)
  have hY := ComplexManifold.eulerChar_compl f.branchValues
  linear_combination
    f.eulerChar_compl_preimage_add_ncard_add_ramificationDegree f.finite_branchValues Subset.rfl -
      hX + degree f * hY

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
