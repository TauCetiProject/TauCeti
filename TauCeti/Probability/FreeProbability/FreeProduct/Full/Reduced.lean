/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Probability.FreeProbability.FreeProduct.Full.Basic
public import TauCeti.Probability.FreeProbability.FreeProduct.Reduced

/-!
# Canonical quotient onto the reduced C⋆-free product and pulled-back vacuum state

Given normalized positive functionals `φ i` on unital complex C⋆-algebras `A i`, the reduced GNS
representation `ReducedFreeProduct.representation φ hφ` extends by continuity to
`FullFreeProduct.reducedRepresentation φ hφ` on `FullFreeProduct A`, whose range is
`ReducedFreeProduct.algebra φ hφ`. Restricting the codomain gives the canonical surjective unital
`⋆`-homomorphism `FullFreeProduct.toReduced φ hφ`, exhibiting every reduced C⋆-free product as a
C⋆-quotient of the full C⋆-free product (`FullFreeProduct.quotientKerToReducedEquiv`) and pulling
the vacuum state and free independence of the factors back to `FullFreeProduct A`
(`FullFreeProduct.state`, `FullFreeProduct.isFreelyIndependent_factor`).
-/

public section

noncomputable section

open LinearAlgebra.FreeProduct

namespace TauCeti.FullFreeProduct

variable {I : Type*} [DecidableEq I] {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)

/-- The reduced GNS representation of `LinearAlgebra.FreeProduct ℂ A` associated to normalized
factor functionals `φ`, extended by continuity to `FullFreeProduct A`. -/
def reducedRepresentation :
    FullFreeProduct A →⋆ₐ[ℂ]
      (ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) :=
  liftRepresentation (ReducedFreeProduct.representation φ hφ)

@[simp]
theorem reducedRepresentation_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    reducedRepresentation φ hφ (ofAlgebraic A x) = ReducedFreeProduct.representation φ hφ x :=
  liftRepresentation_ofAlgebraic (ReducedFreeProduct.representation φ hφ) x

/-- The range of `reducedRepresentation φ hφ` is the reduced C⋆-free product
`ReducedFreeProduct.algebra φ hφ`. -/
theorem range_reducedRepresentation :
    (reducedRepresentation φ hφ).range = ReducedFreeProduct.algebra φ hφ := by
  ext T
  rw [reducedRepresentation, mem_range_liftRepresentation_iff, ReducedFreeProduct.mem_algebra_iff]

/-- The canonical unital `⋆`-homomorphism from `FullFreeProduct A` onto the reduced C⋆-free product
`ReducedFreeProduct.algebra φ hφ` associated to normalized factor functionals `φ`. -/
def toReduced : FullFreeProduct A →⋆ₐ[ℂ] ReducedFreeProduct.algebra φ hφ :=
  (reducedRepresentation φ hφ).codRestrict (ReducedFreeProduct.algebra φ hφ) fun x => by
    rw [← range_reducedRepresentation]
    exact ⟨x, rfl⟩

@[simp]
theorem coe_toReduced (x : FullFreeProduct A) :
    (toReduced φ hφ x :
      ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) =
      reducedRepresentation φ hφ x :=
  (rfl)

@[simp]
theorem toReduced_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    toReduced φ hφ (ofAlgebraic A x) = ReducedFreeProduct.ofAlgebraic φ hφ x := by
  ext
  simp [ReducedFreeProduct.coe_ofAlgebraic]

@[simp]
theorem toReduced_factor (i : I) (a : A i) :
    toReduced φ hφ (factor i a) = ReducedFreeProduct.factor φ hφ i a := by
  simp [factor_apply, ReducedFreeProduct.factor_apply]

/-- The canonical `⋆`-homomorphism `toReduced φ hφ` onto `ReducedFreeProduct.algebra φ hφ` is
surjective: every reduced C⋆-free product is a C⋆-quotient of the full C⋆-free product. -/
theorem toReduced_surjective : Function.Surjective (toReduced φ hφ) := by
  rintro ⟨T, hT⟩
  rw [← range_reducedRepresentation] at hT
  obtain ⟨x, hx⟩ := hT
  exact ⟨x, Subtype.ext hx⟩

theorem ker_toReduced :
    TwoSidedIdeal.ker (toReduced φ hφ) = TwoSidedIdeal.ker (reducedRepresentation φ hφ) :=
  SetLike.ext fun _ => (TwoSidedIdeal.mem_ker (toReduced φ hφ)).trans <|
    Subtype.ext_iff.trans (TwoSidedIdeal.mem_ker (reducedRepresentation φ hφ)).symm

/-- First `⋆`-isomorphism theorem identifying `ReducedFreeProduct.algebra φ hφ` with the
C⋆-quotient of `FullFreeProduct A` by `TwoSidedIdeal.ker (toReduced φ hφ)`. -/
def quotientKerToReducedEquiv :
    FullFreeProduct A ⧸ TwoSidedIdeal.ker (toReduced φ hφ) ≃⋆ₐ[ℂ]
      ReducedFreeProduct.algebra φ hφ :=
  StarAlgHom.quotientKerEquivOfSurjective (toReduced_surjective φ hφ)

@[simp]
theorem quotientKerToReducedEquiv_mk (x : FullFreeProduct A) :
    quotientKerToReducedEquiv φ hφ
      (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (toReduced φ hφ)) x) = toReduced φ hφ x :=
  StarAlgHom.quotientKerEquivOfSurjective_mk (toReduced_surjective φ hφ) x

/-- The vacuum positive functional on `FullFreeProduct A` pulled back along
`reducedRepresentation φ hφ`, agreeing with `ReducedFreeProduct.state φ hφ` along
`toReduced φ hφ`. -/
def state : StarPositiveFunctional (FullFreeProduct A) :=
  (StarPositiveFunctional.ofPositiveLinearMap
    (ContinuousLinearMap.innerPositiveLinearMap ℂ (ReducedFreeProduct.vacuum φ hφ))).comp
    (reducedRepresentation φ hφ)

theorem state_apply_eq_reduced (x : FullFreeProduct A) :
    state φ hφ x = ReducedFreeProduct.state φ hφ (toReduced φ hφ x) := by
  simp [state, ReducedFreeProduct.state_apply]

@[simp]
theorem state_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    state φ hφ (ofAlgebraic A x) = freeProductPositiveFunctional φ hφ x := by
  simp [state_apply_eq_reduced]

@[simp]
theorem state_one : state φ hφ 1 = 1 := by
  rw [← map_one (ofAlgebraic A), state_ofAlgebraic, freeProductPositiveFunctional_one]

@[simp]
theorem state_factor (i : I) (a : A i) : state φ hφ (factor i a) = φ i a := by
  simp [factor_apply]

/-- The canonical factor subalgebras `(factor i).toAlgHom.range` in `FullFreeProduct A` are freely
independent with respect to `FullFreeProduct.state φ hφ`. -/
theorem isFreelyIndependent_factor :
    IsFreelyIndependent (state φ hφ).toLinearMap
      (fun i => (factor (A := A) i).toAlgHom.range) := by
  have h := (isFreelyIndependent_freeProductExpectation
    (fun i => (φ i).toLinearMap) hφ).map (ofAlgebraic A).toAlgHom
    (φ' := (state φ hφ).toLinearMap)
    (by
      ext x
      simp [freeProductPositiveFunctional_apply])
  have hranges : (fun i => (factor (A := A) i).toAlgHom.range) =
      (fun i => ((ι ℂ A i).range).map (ofAlgebraic A).toAlgHom) := by
    funext i
    rw [factor_toAlgHom, AlgHom.range_comp]
  rwa [← hranges] at h

end TauCeti.FullFreeProduct
