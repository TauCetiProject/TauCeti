/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero

/-!
# `Pic⁰` under extension of the base field

The degree of a line bundle does not change under an extension `K/k` of the base field
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback`). Consequently a line-bundle
class on a proper curve lies in `Pic⁰` exactly when its pullback to the base change `X_K` lies in
`Pic⁰ X_K`: `Pic⁰ X` is the preimage of `Pic⁰ X_K` under pullback. No smoothness is assumed.

## Main results

* `LineBundleClass.pullback_mem_picZero_iff` and `LineBundleClass.comap_picZero`: `Pic⁰` is
  compatible with extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry

universe u

namespace LineBundleClass

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IsIntegral X] [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [Fact (∀ y : X, coheight y ≤ 1)] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  [IsIntegral Y] [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]
  [Fact (∀ y : Y, coheight y ≤ 1)] [IsProper (Y ↘ Spec (.of K))]
  [FiniteDimensional K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)]

include H in
/-- **`Pic⁰` is compatible with extension of the base field.** Let `X` be a proper integral curve
over `k` whose codimension-one local rings are discrete valuation rings and whose `H¹(X, 𝒪_X)` is
finite-dimensional, and let `Y = X_K` be its base change to a field extension `K`, satisfying the
same hypotheses over `K`. A line-bundle class on `X` has degree zero exactly when its pullback to
`X_K` does. -/
theorem pullback_mem_picZero_iff {a : Additive (LineBundleClass X)} :
    Additive.ofMul (pullback g a.toMul) ∈ picZero K Y ↔ a ∈ picZero k X := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  rw [mem_picZero_iff, mem_picZero_iff, toMul_ofMul, eulerDegree_pullback H]

include H in
/-- `Pic⁰ X` is the preimage of `Pic⁰ X_K` under pullback of line-bundle classes along the base
change `X_K ⟶ X` to a field extension `K`, for curves `X` and `X_K` as in
`LineBundleClass.pullback_mem_picZero_iff`. -/
theorem comap_picZero :
    (picZero K Y).comap (pullbackHom g).toAdditive = picZero k X := by
  ext a
  rw [AddSubgroup.mem_comap, MonoidHom.toAdditive_apply_apply, pullbackHom_apply]
  exact pullback_mem_picZero_iff H

end LineBundleClass

end TauCeti.AlgebraicGeometry
