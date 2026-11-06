/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Puncture
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.FiberCount
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Data.Set.Restrict

/-!
# Euler characteristics of branched covers

Let `f : X → Y` be a finite holomorphic map from a compact Riemann surface to a
connected Riemann surface, and let `S ⊆ Y` contain every branch value of `f`. Deleting `S` from
the target and `f⁻¹(S)` from the source leaves a covering map whose fibres all have `degree f`
points. Finite-cover multiplicativity of the Euler characteristic therefore gives

`χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`

whenever `Y \ S` has finite CW type; the punctured source then has finite CW type as well.

When `S` is finite, adding the count of deleted points
`#f⁻¹(S) + ramificationDegree f = degree f · #S` gives the punctured form of the branched-cover
formula,

`(χ(X \ f⁻¹(S)) + #f⁻¹(S)) + ramificationDegree f = degree f · (χ(Y \ S) + #S)`.

For surfaces deleting a point lowers the Euler characteristic by one
(`TauCeti.eulerChar_compl_of_finite`), so when `X` and `Y` have finite CW type the two
parenthesised sums are `χ(X)` and `χ(Y)`, and the identity becomes the topological
Riemann–Hurwitz formula `χ(X) = degree f · χ(Y) - ramificationDegree f`. It uses only the
finite-CW Euler characteristic, local multiplicities and the analytic fibre-sum degree; no
canonical divisor and no Riemann–Roch theorem enters.

## Main results

* `FiniteHolomorphicMap.finiteCWType_compl_preimage`: the punctured source has finite CW type
  when the punctured target does.
* `FiniteHolomorphicMap.eulerChar_compl_preimage`: `χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`.
* `FiniteHolomorphicMap.eulerChar_compl_preimage_add_ncard_add_ramificationDegree`: the punctured
  branched-cover formula for a finite set `S` of punctures containing the branch values.
* `FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset`:
  `χ(X) = degree f · χ(Y) - ramificationDegree f`, given finite CW type of `X`, `Y` and `Y \ S`
  for a finite `S` containing the branch values.
* `FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree`: the same,
  puncturing exactly at the branch values.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the topological proof of the Riemann–Hurwitz formula).
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
    ((finite_fiber_restrictPreimage_iff f Sᶜ y).2 (f.finite_fiber y)).to_subtype

variable [PreconnectedSpace Y]

/-- **Euler characteristics of a punctured branched cover.** Deleting a set `S` containing every
branch value from the target, and its preimage from the source, multiplies Euler characteristics
by the degree: `χ(X \ f⁻¹(S)) = degree f · χ(Y \ S)`, provided `Y \ S` has finite CW type. -/
theorem eulerChar_compl_preimage (hS : f.branchValues ⊆ S) [FiniteCWType ↥Sᶜ] :
    haveI := f.finiteCWType_compl_preimage hS
    eulerChar ↥(f ⁻¹' S)ᶜ = degree f * eulerChar ↥Sᶜ :=
  eulerChar_eq_mul_of_isCoveringMap (f.isCoveringMap_restrictPreimage_compl hS)
    (fun y ↦ ((finite_fiber_restrictPreimage_iff f Sᶜ y).2 (f.finite_fiber y)).to_subtype)
    fun y ↦ by
      rw [Nat.card_coe_set_eq, f.ncard_fiber_restrictPreimage_compl hS]

/-- **The punctured branched-cover formula.** For a finite set `S` containing every branch value,
with `Y \ S` of finite CW type,
`(χ(X \ f⁻¹(S)) + #f⁻¹(S)) + ramificationDegree f = degree f · (χ(Y \ S) + #S)`.
For compact surfaces the parenthesised sums are `χ(X)` and `χ(Y)`, which turns this into the
Riemann–Hurwitz formula. -/
theorem eulerChar_compl_preimage_add_ncard_add_ramificationDegree (hfin : S.Finite)
    (hS : f.branchValues ⊆ S) [FiniteCWType ↥Sᶜ] :
    haveI := f.finiteCWType_compl_preimage hS
    eulerChar ↥(f ⁻¹' S)ᶜ + (f ⁻¹' S).ncard + ramificationDegree f =
      degree f * (eulerChar ↥Sᶜ + S.ncard) := by
  have hcount : ((f ⁻¹' S).ncard + ramificationDegree f : ℤ) = degree f * S.ncard := by
    exact_mod_cast f.ncard_preimage_add_ramificationDegree hfin hS
  rw [f.eulerChar_compl_preimage hS]
  linear_combination hcount

variable [FiniteCWType X] [FiniteCWType Y]

/-- **The Euler characteristic of a branched cover.** If `S` is a finite set containing every
branch value of `f` and `X`, `Y` and `Y \ S` have finite CW type, then
`χ(X) = deg f · χ(Y) - R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset (hfin : S.Finite)
    (hS : f.branchValues ⊆ S) [FiniteCWType ↥Sᶜ] :
    eulerChar X = degree f * eulerChar Y - ramificationDegree f := by
  have := f.finiteCWType_compl_preimage hS
  have hX := eulerChar_compl_of_finite (E := ℂ) (hfin.preimage' fun y _ ↦ f.finite_fiber y)
  have hY := eulerChar_compl_of_finite (E := ℂ) (X := Y) hfin
  rw [Complex.finrank_real_complex] at hX hY
  linear_combination f.eulerChar_compl_preimage_add_ncard_add_ramificationDegree hfin hS - hX +
    degree f * hY

/-- **The Euler characteristic of a branched cover**, puncturing at the branch values: if `X`,
`Y` and the complement of the branch values have finite CW type, then
`χ(X) = deg f · χ(Y) - R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree
    [FiniteCWType ↥f.branchValuesᶜ] :
    eulerChar X = degree f * eulerChar Y - ramificationDegree f :=
  f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset f.finite_branchValues
    Subset.rfl

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
