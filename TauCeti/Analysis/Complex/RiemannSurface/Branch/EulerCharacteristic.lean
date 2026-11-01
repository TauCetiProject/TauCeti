/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.FiberCount
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Puncture
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Euler characteristic of a branched cover

Let `f : X → Y` be a finite holomorphic map from a compact connected Riemann surface to a
connected Riemann surface, of degree `d` and total ramification degree `R = ∑ₓ (eₓ - 1)`.
When `X`, `Y` and the complement in `Y` of a finite set containing the branch values have finite
CW type,

```text
χ(X) = d · χ(Y) - R.
```

This is the topological form of the Riemann--Hurwitz formula. It uses only the finite-CW Euler
characteristic, local multiplicities and the analytic fibre-sum degree; no canonical divisor
and no Riemann--Roch theorem enters.

The proof removes a finite set `S` of points of `Y` containing every branch value, together with
its preimage. Over `Y \ S` the map is a `d`-sheeted covering
(`FiniteHolomorphicMap.isCoveringMapOn_iff`, `FiniteHolomorphicMap.card_fiber_eq_degree_iff`), so
`χ(X \ f⁻¹(S)) = d · χ(Y \ S)` by finite-cover multiplicativity
(`TauCeti.eulerChar_eq_mul_of_isCoveringMap`). Removing finitely many points from a surface lowers
the Euler characteristic by their number (`TauCeti.eulerChar_compl_of_finite`), and
`#f⁻¹(S) + R = d · #S` (`FiniteHolomorphicMap.ncard_preimage_add_ramificationDegree`).

The finite-CW-type hypotheses on `X`, `Y` and `Y \ S` are stated as instance arguments; the
punctured source `X \ f⁻¹(S)` inherits finite CW type from the covering. Allowing any finite
`S ⊇ branchValues` lets a caller puncture wherever it can verify finite CW type.

## Main results

* `FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset`:
  `χ(X) = d · χ(Y) - R`, given finite CW type of `Y \ S` for a finite `S ⊇ branchValues`.
* `FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree`: the same,
  puncturing exactly at the branch values.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the Riemann--Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace X] [PreconnectedSpace Y]
  [FiniteCWType X] [FiniteCWType Y]

/-- **The Euler characteristic of a branched cover.** If `S` is a finite set containing every
branch value of `f` and `X`, `Y` and `Y \ S` have finite CW type, then
`χ(X) = deg f · χ(Y) - R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset
    (f : FiniteHolomorphicMap X Y) {S : Set Y} (hS : S.Finite) (hbranch : f.branchValues ⊆ S)
    [FiniteCWType ↥Sᶜ] :
    eulerChar X = degree f * eulerChar Y - ramificationDegree f := by
  -- Over `Y \ S` the map is a covering with finite fibres of cardinality `degree f`.
  have hp : IsCoveringMap (Sᶜ.restrictPreimage f) :=
    ((f.isCoveringMapOn_iff _).2 (compl_subset_compl.2 hbranch)).isCoveringMap_restrictPreimage
  have himage (y : ↥Sᶜ) :
      (↑) '' (Sᶜ.restrictPreimage f ⁻¹' {y}) = f ⁻¹' {(y : Y)} := by
    rw [image_val_preimage_restrictPreimage, image_singleton]
  have hfin (y : ↥Sᶜ) : Finite ↥(Sᶜ.restrictPreimage f ⁻¹' {y}) :=
    (Finite.of_finite_image (himage y ▸ f.finite_fiber y) Subtype.val_injective.injOn).to_subtype
  have hcard (y : ↥Sᶜ) : Nat.card ↥(Sᶜ.restrictPreimage f ⁻¹' {y}) = degree f := by
    rw [Nat.card_coe_set_eq, ← ncard_image_of_injective _ Subtype.val_injective, himage,
      ncard_eq_toFinset_card _ (f.finite_fiber y)]
    exact (f.card_fiber_eq_degree_iff y).2 fun hy ↦ y.2 (hbranch hy)
  have hcover := eulerChar_eq_mul_of_isCoveringMap hp hfin hcard
  -- Removing `S` and its preimage changes the Euler characteristics by their cardinalities.
  have := hp.finiteCWType hfin
  let e : ↥(f ⁻¹' S)ᶜ ≃ₜ ↥(f ⁻¹' Sᶜ) := Homeomorph.setCongr preimage_compl.symm
  have := e.finiteCWType
  have hX := eulerChar_compl_of_finite (E := ℂ) (hS.preimage' fun y _ ↦ f.finite_fiber y)
  have hY := eulerChar_compl_of_finite (E := ℂ) (X := Y) hS
  rw [Complex.finrank_real_complex, e.eulerChar_eq] at hX
  rw [Complex.finrank_real_complex] at hY
  have hcount : ((f ⁻¹' S).ncard : ℤ) + ramificationDegree f = degree f * S.ncard :=
    mod_cast f.ncard_preimage_add_ramificationDegree hS hbranch
  linear_combination hcover - hX + degree f * hY + hcount

/-- **The Euler characteristic of a branched cover**, puncturing at the branch values: if `X`,
`Y` and the complement of the branch values have finite CW type, then
`χ(X) = deg f · χ(Y) - R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree
    (f : FiniteHolomorphicMap X Y) [FiniteCWType ↥f.branchValuesᶜ] :
    eulerChar X = degree f * eulerChar Y - ramificationDegree f :=
  f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset f.finite_branchValues
    Subset.rfl

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
