/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.BelyiPair
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Place
public import TauCeti.FieldTheory.FunctionField.Belyi.Bundled
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The algebraic function field of an analytic Belyi pair

* `TauCeti.AnalyticBelyiPair.toAlgebraicBelyiPair` gives the meromorphic function field of an
  analytic Belyi pair as an algebraic Belyi pair over `ℂ`. The three-point branch condition
  uses `MeromorphicFunction.place_surjective` and `MeromorphicFunction.ramificationIdx_place`.
* `TauCeti.AnalyticBelyiPair.toAlgebraicBelyiPair_algebraMap` identifies the algebra map
  with `MeromorphicFunction.comap` via `MeromorphicFunction.ratFuncEquiv`.
* `TauCeti.AnalyticBelyiPair.finrank_toAlgebraicBelyiPair` identifies the two degrees using
  `MeromorphicFunction.finrank_ratFunc_eq_degree`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, CUP, 2012, Remark 1.94 and Corollary 1.93(iv).
-/

public noncomputable section

open OnePoint

namespace TauCeti
namespace RiemannSurface

/-- Under the identification of the places of `ℂ(t)` with the points of the sphere, the three
marked places correspond to the three marked points. -/
@[simp]
theorem MeromorphicFunction.map_place_mem_zeroOneInfty_iff {y : OnePoint ℂ} :
    (MeromorphicFunction.place y).map MeromorphicFunction.ratFuncEquiv.symm ∈
      Place.zeroOneInfty ℂ ↔ y ∈ ThricePuncturedSphere.marked := by
  cases y with
  | infty =>
    simp only [MeromorphicFunction.map_place_infty, Place.infty_mem_zeroOneInfty,
      ThricePuncturedSphere.mem_marked, or_true]
  | coe a =>
    simp only [MeromorphicFunction.map_place_coe,
      Place.adicOfIrreducible_X_sub_C_mem_zeroOneInfty_iff, ThricePuncturedSphere.mem_marked,
      OnePoint.coe_eq_coe, OnePoint.coe_ne_infty, or_false]

end RiemannSurface

namespace AnalyticBelyiPair

open RiemannSurface RiemannSurface.MeromorphicFunction

/-- The algebraic Belyi pair associated to an analytic Belyi pair. Its field is the field of
meromorphic functions on the surface and its `ℂ(t)`-algebra structure is pullback along `β`. -/
def toAlgebraicBelyiPair (P : AnalyticBelyiPair.{0}) : AlgebraicBelyiPair ℂ :=
  letI := ((comapₐ P.β P.β.holomorphic P.β.nonconstant).comp
    ratFuncEquiv.toAlgHom).toRingHom.toAlgebra
  haveI := isScalarTower_ratFunc P.β rfl
  haveI := finiteDimensional_ratFunc P.β rfl
  { carrier := MeromorphicFunction P.X
    isAlgebraicBelyiPair := ⟨isIntegrallyClosedIn_of_isAlgClosed,
      fun {Q} hQ ↦ (place_surjective Q).elim fun x hx ↦
        have hrestrict := restrict_place P.β rfl x
        have hval : P.β x ∉ P.β.branchValues := fun hy ↦
          have hmarked := ThricePuncturedSphere.mem_marked.mpr (P.branchValues_subset hy)
          have hplace := map_place_mem_zeroOneInfty_iff.mpr hmarked
          hQ (hx ▸ hrestrict.symm ▸ hplace)
        hx ▸ (ramificationIdx_place P.β rfl x).trans
          ((P.β.notMem_branchValues_iff _).mp hval x rfl)⟩ }

/-- The underlying `ℂ`-algebra of the algebraic Belyi pair is the meromorphic function field. -/
def toAlgebraicBelyiPairEquiv (P : AnalyticBelyiPair.{0}) :
    P.toAlgebraicBelyiPair ≃ₐ[ℂ] MeromorphicFunction P.X :=
  AlgEquiv.refl

/-- The rational function field acts on the algebraization by pullback along the analytic map. -/
@[simp]
theorem toAlgebraicBelyiPair_algebraMap (P : AnalyticBelyiPair.{0}) (r : RatFunc ℂ) :
    P.toAlgebraicBelyiPairEquiv (algebraMap (RatFunc ℂ) P.toAlgebraicBelyiPair r) =
      comap P.β P.β.holomorphic P.β.nonconstant (ratFuncEquiv r) :=
  comapₐ_apply _ _ _ _

/-- The inverse identification sends a pulled-back rational function to the corresponding
element of the algebraic Belyi pair. -/
@[simp]
theorem toAlgebraicBelyiPairEquiv_symm_comap (P : AnalyticBelyiPair.{0}) (r : RatFunc ℂ) :
    P.toAlgebraicBelyiPairEquiv.symm (comap P.β P.β.holomorphic P.β.nonconstant (ratFuncEquiv r)) =
      algebraMap (RatFunc ℂ) P.toAlgebraicBelyiPair r :=
  (P.toAlgebraicBelyiPairEquiv.symm_apply_eq).mpr (P.toAlgebraicBelyiPair_algebraMap r).symm

/-- Algebraization preserves the degree of an analytic Belyi pair. -/
@[simp]
theorem finrank_toAlgebraicBelyiPair (P : AnalyticBelyiPair.{0}) :
    Module.finrank (RatFunc ℂ) P.toAlgebraicBelyiPair = degree P.β := by
  let : Algebra (RatFunc ℂ) (MeromorphicFunction P.X) := P.toAlgebraicBelyiPair.algebraRatFunc
  exact finrank_ratFunc_eq_degree P.β rfl

end AnalyticBelyiPair
end TauCeti
