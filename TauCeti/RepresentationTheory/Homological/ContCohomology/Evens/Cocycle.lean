/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cochain
import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Resolution
import Mathlib.RingTheory.Ideal.Int

/-!
# The tensor norm on canonical homogeneous cocycles

A homogeneous cocycle for a compact open subgroup, with trivial mod-two coefficients, gives
an ambient cohomology class by taking its diagonal tensor in the tensor-induced resolution.
This file supplies that construction directly on Mathlib's homogeneous cochains. Its value
depends only on the input cohomology class, including when that class is zero, and not on the
transversal used to tensor-induce. Multiplication identifies the tensor-induced coefficients with
the ambient trivial coefficients. In degree zero the norm is the identity of `𝔽₂ = H⁰`: a cocycle
with value `a` has norm the degree-zero class of `a ^ |G ⧸ U| = a`
(`OpenSubgroup.tensorNormCocycleClass_eq_degreeZeroClass`).

The construction uses `TauCeti.smoothTensorInducedDiagonalClass` and its change-of-coboundary
theorem. These operate on the total graded resolution; `TopRep.cochainToGradedResolution`
transfers the canonical differential and invariance to that presentation. In degree zero there
are no coboundaries, so cocycles with equal classes are equal. Transversal independence is
`TauCeti.smoothTensorInducedDiagonalClass_trivialF2_changeTransversal`. No choice of a
representative of a cohomology class is made here.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
-/

public section

namespace OpenSubgroup

open TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)] (t : U.toSubgroup.LeftTransversal)

-- Tensor induction uses the direct-sum scalar action of the total resolution, rather than
-- the fallback integer action on its underlying additive group.
private noncomputable local instance : Module ℤ (trivialF2 U.toSubgroup).gradedResolutionModule :=
  @DirectSum.instModule ℤ _ ℕ
    (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).V)
    (fun _ ↦ inferInstance) (fun n ↦ (TopRep.resolutionX (trivialF2 U.toSubgroup) (n + 1)).hV2)

/-- The class of the diagonal tensor of a canonical homogeneous cocycle with trivial `𝔽₂`
coefficients. Its degree is the index times the input degree, and tensor-induced coefficients
are identified with trivial coefficients by multiplication. This is a function on cocycles. -/
noncomputable def tensorNormCocycleClass {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0) :
    continuousCohomology (Fintype.card (G ⧸ U.toSubgroup) * n) (trivialF2 G) :=
  ContinuousCohomology.coeffMap (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' t).hom.hom
    (Fintype.card (G ⧸ U.toSubgroup) * n)
    (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' t
      ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
      (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
      ((trivialF2 U.toSubgroup).cochainToGradedResolution n z)
      ((trivialF2 U.toSubgroup).cochainToGradedResolution_mem n z)
      ((trivialF2 U.toSubgroup).cochainToGradedResolution_invariant n z)
      (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hz, map_zero]))

/-- The tensor norm of a canonical cocycle is the coefficient image of its graded diagonal
class. This equation fixes the representative-level normalization. -/
theorem tensorNormCocycleClass_def {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0) :
    tensorNormCocycleClass U t z hz =
      ContinuousCohomology.coeffMap
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' t).hom.hom
        (Fintype.card (G ⧸ U.toSubgroup) * n)
        (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' t
          ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
          (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
          ((trivialF2 U.toSubgroup).cochainToGradedResolution n z)
          ((trivialF2 U.toSubgroup).cochainToGradedResolution_mem n z)
          ((trivialF2 U.toSubgroup).cochainToGradedResolution_invariant n z)
          (by rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hz, map_zero])) :=
  (rfl)

/-- The tensor norm of a cocycle does not depend on the transversal used to tensor-induce. -/
theorem tensorNormCocycleClass_changeTransversal (s : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0) :
    tensorNormCocycleClass U t z hz = tensorNormCocycleClass U s z hz :=
  smoothTensorInducedDiagonalClass_trivialF2_changeTransversal G U.toSubgroup U.isOpen' s t _ _ _ _

/-- Equal classes have equal tensor norms. The equality is in Mathlib's canonical continuous
cohomology; no graded coboundary witness is required from the caller. -/
theorem tensorNormCocycleClass_eq_of_cochainClass_eq {n : ℕ}
    (z z' : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0)
    (hz' : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z' = 0)
    (h : (trivialF2 U.toSubgroup).cochainClass n z hz =
      (trivialF2 U.toSubgroup).cochainClass n z' hz') :
    tensorNormCocycleClass U t z hz = tensorNormCocycleClass U t z' hz' := by
  cases n with
  | zero =>
    -- In degree zero there are no coboundaries: the class map is injective.
    rw [TopRep.cochainClass_def, TopRep.cochainClass_def] at h
    have hc := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).homologyπ 0)).1 h
    obtain rfl : z = z' := by
      simpa only [HomologicalComplex.iCycles_cyclesMkOfEq] using
        congrArg ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).iCycles 0).hom hc
    rfl
  | succ n =>
    let : (Ideal.span {(2 : ℤ)}).IsMaximal :=
      @Int.ideal_span_isMaximal_of_prime 2 ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := ((trivialF2 U.toSubgroup).cochainClass_eq_cochainClass_iff rfl hz hz').1 h
    rw [tensorNormCocycleClass_def, tensorNormCocycleClass_def]
    congr 1
    apply smoothTensorInducedDiagonalClass_eq_of_sub_eq_d
      U.toSubgroup U.isOpen' t
      ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
      (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
      _ _ _ _ _ _
      ((trivialF2 U.toSubgroup).cochainToGradedResolution_mem n y)
      ((trivialF2 U.toSubgroup).cochainToGradedResolution_invariant n y)
    rw [← map_sub, hy, TopRep.gradedResolutionDifferential_cochainToGradedResolution]

/-- The zero cocycle has zero tensor norm, including in degree zero. -/
@[simp]
theorem tensorNormCocycleClass_zero (n : ℕ) :
    tensorNormCocycleClass U t (0 : (TopRep.homogeneousCochains
      (trivialF2 U.toSubgroup)).X n) (map_zero _) = 0 := by
  have hten : PiTensorProduct.tprod ℤ (fun _ : G ⧸ U.toSubgroup ↦
      (0 : (trivialF2 U.toSubgroup).gradedResolutionModule)) = 0 :=
    (PiTensorProduct.tprod ℤ).map_coord_zero (QuotientGroup.mk 1) rfl
  let : LinearOrder (G ⧸ U.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U.toSubgroup)).injective
  rw [tensorNormCocycleClass_def, smoothTensorInducedDiagonalClass_eq]
  let c := smoothTensorInducedGradedResolutionContraction U.toSubgroup U.isOpen' t
    ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩
    (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U.toSubgroup a)
  have hzero := TopRep.ResolutionContraction.gradedCohomologyClass_zero.{0, u, u}
    c (n := Fintype.card (G ⧸ U.toSubgroup) * n)
  apply Eq.trans (congrArg
    (ContinuousCohomology.coeffMap
      (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' t).hom.hom
      (Fintype.card (G ⧸ U.toSubgroup) * n)) _) (map_zero _)
  convert hzero using 1
  simp only [map_zero, hten]
  rfl

/-- A cocycle representing zero has zero tensor norm. -/
theorem tensorNormCocycleClass_eq_zero_of_cochainClass_eq_zero {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d n (n + 1)).hom z = 0)
    (h : (trivialF2 U.toSubgroup).cochainClass n z hz = 0) :
    tensorNormCocycleClass U t z hz = 0 := by
  rw [← tensorNormCocycleClass_zero U t n]
  apply tensorNormCocycleClass_eq_of_cochainClass_eq U t z 0 hz (map_zero _)
  simpa only [TopRep.cochainClass_zero] using h

/-- **The tensor norm in degree zero is the identity of `𝔽₂`**: a degree-zero cocycle, the
constant function with value `a ∈ 𝔽₂`, has tensor norm the degree-zero class of `a` in
`H⁰(G, 𝔽₂) = 𝔽₂`. The diagonal tensor `a ⊗ ⋯ ⊗ a` has one factor for each coset in `G ⧸ U`, so
it multiplies out to `a ^ |G ⧸ U| = a` in `𝔽₂`. -/
theorem tensorNormCocycleClass_eq_degreeZeroClass
    (z : (TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).X 0)
    (hz : ((TopRep.homogeneousCochains (trivialF2 U.toSubgroup)).d 0 (0 + 1)).hom z = 0) :
    tensorNormCocycleClass U t z hz =
      ContinuousCohomology.degreeZeroClass (trivialF2 G)
        ((trivialF2Equiv G).symm (trivialF2Equiv U.toSubgroup (z.1 1)))
        (fun g ↦ trivialF2_ρ_apply_apply G g _) := by
  have ha : (trivialF2 U.toSubgroup).gradedResolutionProjection
      ((trivialF2 U.toSubgroup).cochainToGradedResolution 0 z) = z.1 1 := by
    rw [TopRep.cochainToGradedResolution_apply, TopRep.gradedResolutionProjection_lof_zero]
  rw [tensorNormCocycleClass_def, Subgroup.smoothTensorInducedDiagonalClass_eq_degreeZeroClass,
    ContinuousCohomology.coeffMap_def]
  refine (ContinuousCohomology.map_degreeZeroClass (ContinuousMonoidHom.id G) _ _ _).trans ?_
  congr 1
  apply (trivialF2Equiv G).injective
  rw [AddEquiv.apply_symm_apply]
  refine (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G U.toSubgroup
    U.isOpen' t _).trans ?_
  rw [Finset.prod_const, ha]
  have hb : ∀ b : ZMod 2, IsIdempotentElem b := by
    unfold IsIdempotentElem
    decide
  exact (hb _).pow_eq (by simp)

end OpenSubgroup
