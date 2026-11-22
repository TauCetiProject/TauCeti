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
Riemann surface. By surjectivity `Y` is also compact (`FiniteHolomorphicMap.compactSpace_codomain`),
so `X`, `Y`, and the complement in either surface of any finite set all have finite CW type
(`TauCeti.ComplexManifold.instFiniteCWType`, `TauCeti.ComplexManifold.instFiniteCWTypeCompl`).

Deleting a set `S ⊆ Y` containing every branch value of `f` from the target, and `f⁻¹(S)` from the
source, leaves a covering map whose fibres all have `degree f` points. Finite-cover multiplicativity
of the Euler characteristic therefore gives

`χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`

whenever `Y \ S` has finite CW type (in particular whenever `S` is finite).

Puncturing at `S = f.branchValues`, adding the fibre count
`#f⁻¹(S) + ramificationDegree f = degree f · #S`, and substituting
`χ(M \ T) = χ(M) - #T` (`TauCeti.ComplexManifold.eulerChar_compl`) yields the unconditional
topological Riemann--Hurwitz formula `χ(X) = degree f · χ(Y) - ramificationDegree f`. It uses only
the finite-CW Euler characteristic, local multiplicities and the analytic fibre-sum degree; no
canonical divisor and no Riemann--Roch theorem enters. Conversely, applying
`TauCeti.ComplexManifold.eulerChar_compl` again yields the punctured branched-cover formula

`(χ(X \ f⁻¹(S)) + #f⁻¹(S)) + ramificationDegree f = degree f · (χ(Y \ S) + #S)`

for every finite subset `S ⊆ Y`, whether or not `S` contains the branch values.

## Main results

* `FiniteHolomorphicMap.finiteCWType_compl_preimage_of_finite`: `X \ f⁻¹(S)` has finite CW type
  for any finite `S ⊆ Y`.
* `FiniteHolomorphicMap.finiteCWType_codomain`, `FiniteHolomorphicMap.finiteCWType_compl_of_finite`,
  `FiniteHolomorphicMap.finiteCWType_compl_branchValues`: the preconnected target `Y` and `Y \ S`
  (in particular `Y \ f.branchValues`) have finite CW type for any finite `S ⊆ Y`.
* `FiniteHolomorphicMap.finiteCWType_compl_preimage`: the punctured source has finite CW type
  when the punctured target does.
* `FiniteHolomorphicMap.eulerChar_compl_preimage`: `χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`.
* `FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree`:
  `χ(X) = degree f · χ(Y) - ramificationDegree f` unconditionally for every finite holomorphic map
  `f : X → Y` from a compact Riemann surface to a preconnected Riemann surface.
* `FiniteHolomorphicMap.eulerChar_compl_preimage_add_ncard_add_ramificationDegree`: the punctured
  branched-cover formula for any finite set `S` of punctures.

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

section FiniteCWType

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  (f : FiniteHolomorphicMap X Y) {S : Set Y}

/-- Deleting the preimage of a finite set from the compact source leaves an open Riemann surface of
finite CW type. -/
theorem finiteCWType_compl_preimage_of_finite [T2Space X] (hfin : S.Finite) :
    FiniteCWType ↥(f ⁻¹' S)ᶜ :=
  ComplexManifold.finiteCWType_compl 𝓘(ℂ) (hfin.preimage' fun y _ ↦ f.finite_fiber y) one_ne_zero

section Codomain

variable [IsManifold 𝓘(ℂ) 1 Y] [T2Space Y] [PreconnectedSpace Y]

include f

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

end FiniteCWType

section Covering

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

/-- **The topological Riemann--Hurwitz formula in Euler-characteristic form.** For any finite
holomorphic map `f : X → Y` from a compact Riemann surface to a preconnected Riemann surface,
`χ(X) = deg f · χ(Y) - R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree :
    eulerChar X = degree f * @eulerChar Y _ f.finiteCWType_codomain - ramificationDegree f := by
  have : CompactSpace Y := f.compactSpace_codomain
  have := f.finiteCWType_compl_branchValues
  have hcount : ((f ⁻¹' f.branchValues).ncard + ramificationDegree f : ℤ) =
      degree f * f.branchValues.ncard := by
    exact_mod_cast f.ncard_preimage_add_ramificationDegree f.finite_branchValues Subset.rfl
  have := (f.finite_branchValues.preimage' fun y _ ↦ f.finite_fiber y).to_subtype
  have := f.finite_branchValues.to_subtype
  have hX := ComplexManifold.eulerChar_compl (f ⁻¹' f.branchValues)
  have hY := ComplexManifold.eulerChar_compl f.branchValues
  linear_combination f.eulerChar_compl_preimage Subset.rfl + hcount - hX + degree f * hY

/-- **The punctured branched-cover formula.** For any finite set `S ⊆ Y`,
`(χ(X \ f⁻¹(S)) + #f⁻¹(S)) + ramificationDegree f = degree f · (χ(Y \ S) + #S)`.
Because deleting a finite set subtracts its cardinality from the Euler characteristic, both
sides reduce to the unconditional Riemann--Hurwitz formula. -/
theorem eulerChar_compl_preimage_add_ncard_add_ramificationDegree (hfin : S.Finite) :
    @eulerChar ↥(f ⁻¹' S)ᶜ _ (f.finiteCWType_compl_preimage_of_finite hfin) +
        (f ⁻¹' S).ncard + ramificationDegree f =
      degree f * (@eulerChar ↥Sᶜ _ (f.finiteCWType_compl_of_finite hfin) + S.ncard) := by
  have : CompactSpace Y := f.compactSpace_codomain
  have := (hfin.preimage' fun y _ ↦ f.finite_fiber y).to_subtype
  have := hfin.to_subtype
  have hX := ComplexManifold.eulerChar_compl (f ⁻¹' S)
  have hY := ComplexManifold.eulerChar_compl S
  linear_combination
    f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree + hX - degree f * hY

end Covering

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
