/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers

/-!
# Total-space dimension of models over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`, and let `M` be a model over `R` of a
scheme `C` over `K`. Since `M` is flat over `R`, its special fibre is no larger than its generic
fibre (`TauCeti.Model.relativeDimensionLE_toBase` in `Fibers.lean`): if `C` has relative dimension
at most `d` over `K`, then `M` has relative dimension at most `d` over `R`, its total space has
Krull dimension at most `d + 1`, and every point of its total space has codimension at most `d + 1`.
No excellence or catenarity hypothesis on `R` is needed.

## Main results

* `TauCeti.Model.topologicalKrullDim_total_le` and `TauCeti.Model.coheight_le`: if
  `RelativeDimensionLE d toK`, then `topologicalKrullDim M.total ≤ d + 1` and every point of
  `M.total` has codimension at most `d + 1`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- If `C` has relative dimension at most `d` over `K`, then the total space of any model `M` of
`C` over `R` has Krull dimension at most `d + 1`. -/
theorem topologicalKrullDim_total_le (M : Model R K C toK) {d : ℕ} [RelativeDimensionLE d toK] :
    topologicalKrullDim M.total ≤ (d + 1 : ℕ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  refine (topologicalKrullDim_le_add_of_relativeDimensionLE (d := d) M.toBase).trans_eq ?_
  have hSpec : topologicalKrullDim (Spec (.of R)) = ringKrullDim R :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R
  rw [hSpec, _root_.IsDiscreteValuationRing.ringKrullDim_eq_one R, Nat.cast_add, Nat.cast_one,
    add_comm]

/-- Every point of the total space of a model of `C` has codimension at most `d + 1` when `C` has
relative dimension at most `d` over `K`. -/
theorem coheight_le (M : Model R K C toK) {d : ℕ} [RelativeDimensionLE d toK] (x : M.total) :
    Order.coheight x ≤ d + 1 := by
  exact_mod_cast (coheight_le_topologicalKrullDim x).trans (M.topologicalKrullDim_total_le (d := d))

end Model

end TauCeti
