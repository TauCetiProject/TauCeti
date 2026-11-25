/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cochain
import Mathlib.RingTheory.Ideal.Int

/-!
# Diagonal classes of homogeneous cocycles

Let `U` be a compact open subgroup of finite index `l` in a topological group `G`, and let `A` be a
smooth discrete `U`-representation over `ℤ` of characteristic two. A homogeneous cocycle `z` of `U`
with values in `A`, included into the total coinduced resolution by
`TopRep.cochainToGradedResolution`, has a diagonal tensor `z ⊗ ⋯ ⊗ z` whose class lies in
`H^{l n}(G, Ind⊗ A)` (`TauCeti.smoothTensorInducedDiagonalClass`). This file shows that this class
depends only on the cohomology class of `z`, and that the zero cochain has class zero. These are the
facts shared by the Evens norms built from the diagonal class.

## Main results

* `TauCeti.smoothTensorInducedDiagonalClass_eq_of_cochainClass_eq`: homogeneous cocycles with the
  same class in `Hⁿ(U, A)` have the same diagonal class.
* `TauCeti.smoothTensorInducedDiagonalClass_cochainToGradedResolution_zero`: the diagonal class of
  the zero cochain is zero, in every degree.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
-/

public section

universe u

namespace TauCeti

open scoped TopRep.GradedResolution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) [U.FiniteIndex]
  [CompactSpace U] [Fintype (G ⧸ U)] (A : SmoothDiscreteTopRep.{0, u, u} ℤ U)
  (hA : ∀ a : A.obj.V, a + a = 0)

/-- **The diagonal class of a homogeneous cocycle depends only on its class.** For coefficients
`A` of characteristic two, homogeneous cocycles with the same class in `Hⁿ(U, A)` have diagonal
tensors with the same class in `H^{l n}(G, Ind⊗ A)`. -/
theorem smoothTensorInducedDiagonalClass_eq_of_cochainClass_eq {n : ℕ}
    (z z' : (TopRep.homogeneousCochains A.obj).X n)
    (hz : ((TopRep.homogeneousCochains A.obj).d n (n + 1)).hom z = 0)
    (hz' : ((TopRep.homogeneousCochains A.obj).d n (n + 1)).hom z' = 0)
    (h : A.obj.cochainClass n z hz = A.obj.cochainClass n z' hz') :
    smoothTensorInducedDiagonalClass.{0, u, u} U hU t A hA
        (A.obj.cochainToGradedResolution n z)
        (A.obj.cochainToGradedResolution_mem n z) (A.obj.cochainToGradedResolution_invariant n z)
        ((A.obj.gradedResolutionDifferential_cochainToGradedResolution_eq_zero_iff n z).2 hz) =
      smoothTensorInducedDiagonalClass.{0, u, u} U hU t A hA
        (A.obj.cochainToGradedResolution n z')
        (A.obj.cochainToGradedResolution_mem n z')
        (A.obj.cochainToGradedResolution_invariant n z')
        ((A.obj.gradedResolutionDifferential_cochainToGradedResolution_eq_zero_iff n z').2
          hz') := by
  cases n with
  | zero =>
    -- In degree zero there are no coboundaries: the class map is injective.
    rw [TopRep.cochainClass_def, TopRep.cochainClass_def] at h
    have hc := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((TopRep.homogeneousCochains A.obj).homologyπ 0)).1 h
    obtain rfl : z = z' := by
      simpa only [HomologicalComplex.iCycles_cyclesMkOfEq] using
        congrArg ((TopRep.homogeneousCochains A.obj).iCycles 0).hom hc
    rfl
  | succ n =>
    -- In positive degree the two cocycles differ by a coboundary.
    let : (Ideal.span {(2 : ℤ)}).IsMaximal :=
      @Int.ideal_span_isMaximal_of_prime 2 ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := (A.obj.cochainClass_eq_cochainClass_iff rfl hz hz').1 h
    apply smoothTensorInducedDiagonalClass_eq_of_sub_eq_d U hU t A hA _ _ _ _ _ _
      (A.obj.cochainToGradedResolution_mem n y) (A.obj.cochainToGradedResolution_invariant n y)
    rw [← map_sub, hy, TopRep.gradedResolutionDifferential_cochainToGradedResolution]

/-- **The diagonal class of the zero cochain is zero**, in every degree, including degree zero:
for coefficients `A` of characteristic two, the diagonal tensor `0 ⊗ ⋯ ⊗ 0` of the zero
homogeneous `n`-cochain has class zero in `H^{l n}(G, Ind⊗ A)`. -/
theorem smoothTensorInducedDiagonalClass_cochainToGradedResolution_zero (n : ℕ) :
    smoothTensorInducedDiagonalClass.{0, u, u} U hU t A hA
        (A.obj.cochainToGradedResolution n 0)
        (A.obj.cochainToGradedResolution_mem n 0) (A.obj.cochainToGradedResolution_invariant n 0)
        ((A.obj.gradedResolutionDifferential_cochainToGradedResolution_eq_zero_iff n 0).2
          (map_zero _)) =
      0 := by
  let : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  rw [smoothTensorInducedDiagonalClass_eq]
  convert TopRep.ResolutionContraction.gradedCohomologyClass_zero.{0, u, u}
    (smoothTensorInducedGradedResolutionContraction U hU t A hA)
    (n := Fintype.card (G ⧸ U) * n) using 1
  simp only [map_zero]
  -- The diagonal tensor of the zero vector vanishes, since one of its factors does.
  congr 1
  exact (PiTensorProduct.tprod ℤ).map_coord_zero (QuotientGroup.mk 1) rfl

end TauCeti
