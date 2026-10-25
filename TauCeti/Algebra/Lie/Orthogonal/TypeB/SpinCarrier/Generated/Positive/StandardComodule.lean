/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule.Quotient
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.StandardComodule

/-!
# Invariant subspaces of the positive type-Bₙ₊₁ spin subgroup

The subcomodules of the positive subgroup's `2^(n+1)`-dimensional spin representation over a
field are precisely the coordinate spans closed under the `n + 1` raising operators. The weight
torus separates the coordinate lines, since the spin weights are pairwise distinct, while a
raising operator sends an exterior basis vector whose weight pairs to `-1` with its simple coroot
to the basis vector of the reflected weight, up to sign. This classification is the flag input
for testing maximality of the positive subgroup among connected solvable subgroups.

The coordinate-span criterion works over every nontrivial commutative ring. The assertion
that every invariant subspace is a coordinate span uses a field. No algebraic closure or
restriction on the characteristic is needed. No validity of the Dynkin type `B (n + 1)` is
needed either: the statements are about the explicit spin weights and their simple reflections.

## Main declarations

* `TauCeti.TypeBSpinCarrier.Generated.Positive.standardComodule`: the spin representation of
  the positive subgroup.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.single_basisReflection_mem`: a subcomodule
  containing a weight vector contains its image under each raising step.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.coordinateSpanIsStable_iff`: a coordinate span is
  invariant exactly when its indices are closed under raising steps.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.exists_subcomodule_iff`: the classification of
  invariant subspaces over a field.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.

The argument is that of `TauCeti.Algebra.Lie.E6.Minuscule.Generated.Positive.StandardComodule`
for the positive E₆ minuscule subgroup, with the type-`B` spin weights and root matrices. Weight
extraction uses `Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.TypeBSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The spin representation of the positive subgroup generated over `R`. -/
@[instance_reducible]
def standardComodule : Comodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R) :=
  GeneralLinear.corestrictStandardComodule R (dimension n)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal n R)).hom

attribute [local instance] standardComodule

/-- The coefficient matrix is the ambient generic matrix modulo the positive subgroup's ideal. -/
theorem coefficientMatrix_basisFun :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra n R)
        (Pi.basisFun R (Fin (dimension n))) =
      (GeneralLinear.genericMatrix R (dimension n)).map
        (CommHopfAlgCat.mkQuotient _ (definingIdeal n R)).hom := by
  let _ := GeneralLinear.standardComodule R (dimension n)
  rw [Comodule.coefficientMatrix_corestrict, GeneralLinear.coefficientMatrix_basisFun]
  ext a b
  simp only [Matrix.map_apply, BialgHom.toCoalgHom_apply]

/-- Restriction to the weight torus splits the spin representation into its weight lines. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict
        (CommHopfAlgCat.commonKernelLift (generator n R) (.inr ())).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (dimension n))) (basisCharacter n) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (CommHopfAlgCat.mkQuotient _ (definingIdeal n R)).hom
    (CommHopfAlgCat.commonKernelLift (generator n R) (.inr ())).hom (basisWeight n)
  rw [← CommHopfAlgCat.hom_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
    generator_inr, generatorCoordinateMap_inr,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

private theorem rootPoint_matrix (i : Fin (n + 1)) (A : Type u) [CommRing A] [Algebra R A]
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R A)) :
    GeneralLinear.pointToGeneralLinear (dimension n)
        (toConv (q.ofConv.comp (generator n R (.inl i)).hom.toAlgHom)) =
      (rootSubgroupPoints n (.inl i) A (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) := by
  have h :=
    pointToGeneralLinear_mapDomain_generatedCoordinateLift_inl_eq_rootSubgroupPoints n R (.inl i) q
  rw [generator_inl, ← generatedCoordinateMap_comp_generatedCoordinateLift]
  simpa only [BialgHom.mapDomain_apply, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    AlgHom.comp_assoc] using h

/-- Every positive subcomodule is stable under each raising-root point. -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (i : Fin (n + 1)) (t : Multiplicative R) {v : Fin (dimension n) → R} (hv : v ∈ N) :
    ((rootSubgroupPoints n (.inl i) R t : Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ v ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm t
  have h := GeneralLinear.quotientStandardComodule_mulVec_mem R (dimension n)
    (definingIdeal n R) (generator n R (.inl i))
    (by simpa only [generator_inl] using
      ((le_definingIdeal_iff n R (definingIdeal n R)).mp le_rfl).1 i) N q hv
  rw [rootPoint_matrix n R i R q, MulEquiv.apply_symm_apply] at h
  exact h

/-- A subcomodule containing a weight vector contains every vector obtained by one raising step:
the basis vector of the simple reflection of a spin weight pairing to `-1` with the coroot. -/
theorem single_basisReflection_mem
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (i : Fin (n + 1)) (a : Fin (dimension n)) (ha : basisWeight n a i = -1)
    (hv : Pi.single a (1 : R) ∈ N) :
    Pi.single (basisReflection n i a) (1 : R) ∈ N := by
  obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inl_exteriorBasis n i _ _ ha
    (signSet_basisReflection n i a).symm
  refine single_mem_of_rep_rootGenerator_eq n R N.toSubmodule (.inl i) (c := c)
    (fun w hw ↦ rootSubgroupPoints_mulVec_mem n R N i _ hw) ?_ hv
  rw [coe_latticeBasis n a, coe_latticeBasis n (basisReflection n i a)]
  exact hc

variable {n R}

private theorem stable_of_raising_closed (s : Set (Fin (dimension n)))
    (hs : ∀ i a, a ∈ s → basisWeight n a i = -1 → basisReflection n i a ∈ s) :
    (Pi.basisFun R (Fin (dimension n))).coordinateSpanIsStable
      (C := coordinateHopfAlgebra n R) s := by
  classical
  let w : Fin (dimension n) → ℤ := fun a ↦ if a ∈ s then 1 else 0
  refine GeneralLinear.coordinateSpanIsStable_of_weightParabolicDefiningHopfIdeal_le (w := w) ?_
    fun a ha b hb ↦ by simp [w, ha, hb]
  rw [le_definingIdeal_iff]
  constructor
  · intro i
    apply GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker
    intro a b hab
    have ha : a ∉ s := by
      intro ha
      by_cases hb : b ∈ s <;> simp [w, ha, hb] at hab
    have hb : b ∈ s := by
      by_contra hb
      simp [w, ha, hb] at hab
    let A := AdditiveGroup.coordinateHopfAlgebra R
    let q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
        (CommAlgCat.of R A) :=
      toConv (AlgHom.id R _)
    have hm := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (dimension n)) A ↦
      (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A) a b) (rootPoint_matrix n R i A q)
    rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear] at hm
    simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, q,
      AlgHom.id_comp, generator_inl] at hm
    have hab' : a ≠ b := fun h ↦ ha (h ▸ hb)
    rw [hm, coe_rootSubgroupPoints_eq_one_add_smul]
    simp [Matrix.add_apply, Matrix.smul_apply, hab', rootIntMatrix_inl_eq_zero_of_ne_basisReflection
      n i (a := a) (b := b) fun hbi h ↦ ha (h.symm ▸ hs i b hb hbi : a ∈ s)]
  · rw [generatorCoordinateMap_inr, GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    exact
      GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal_le_ker_weightTorusCoordinateBialgHom
        w (basisWeight n)

/-- A coordinate span is invariant exactly when its weight indices are closed under raising.
This criterion uses the universal coaction, rather than just the action of rational points. -/
theorem coordinateSpanIsStable_iff [Nontrivial R] (s : Set (Fin (dimension n))) :
    (Pi.basisFun R (Fin (dimension n))).coordinateSpanIsStable
        (C := coordinateHopfAlgebra n R) s ↔
      ∀ i a, a ∈ s → basisWeight n a i = -1 → basisReflection n i a ∈ s := by
  classical
  refine ⟨fun h i a ha hia ↦ ?_, stable_of_raising_closed s⟩
  let N := (Pi.basisFun R (Fin (dimension n))).coordinateSpanSubcomodule s h
  have hv : Pi.single a (1 : R) ∈ N := by
    rw [Module.Basis.mem_coordinateSpanSubcomodule]
    exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin (dimension n)) a⟩
  have hr := single_basisReflection_mem n R N i a hia hv
  rw [Module.Basis.mem_coordinateSpanSubcomodule] at hr
  exact (Pi.basisFun R (Fin (dimension n))).mem_span_image.mp hr (by simp)

variable (n) (k : Type u) [Field k]

/-- Every invariant subspace is the span of exactly those spin weight lines it contains. -/
theorem toSubmodule_eq_span
    (N : Subcomodule k (coordinateHopfAlgebra n k) (Fin (dimension n) → k)) :
    N.toSubmodule = Submodule.span k ((Pi.basisFun k (Fin (dimension n))) ''
      {a | Pi.single a (1 : k) ∈ N}) :=
  Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights
    (CommHopfAlgCat.commonKernelLift (generator n k) (.inr ())).hom.toCoalgHom
    (basisCharacter n) (basisCharacter_injective n) (torusCorestrict_eq_ofWeights n k) N

/-- **Invariant-subspace classification for the positive type-`Bₙ₊₁` spin subgroup.** A
subspace is a subcomodule precisely when it is a coordinate span closed under all `n + 1`
raising operators. -/
theorem exists_subcomodule_iff (W : Submodule k (Fin (dimension n) → k)) :
    (∃ N : Subcomodule k (coordinateHopfAlgebra n k) (Fin (dimension n) → k),
        N.toSubmodule = W) ↔
      ∃ s : Set (Fin (dimension n)),
        (∀ i a, a ∈ s → basisWeight n a i = -1 → basisReflection n i a ∈ s) ∧
        W = Submodule.span k ((Pi.basisFun k (Fin (dimension n))) '' s) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨{a | Pi.single a (1 : k) ∈ N}, ?_, ?_⟩
    · intro i a ha hia
      exact single_basisReflection_mem n k N i a hia ha
    · exact hN.symm.trans (toSubmodule_eq_span n k N)
  · rintro ⟨s, hs, rfl⟩
    exact (Module.Basis.exists_subcomodule_toSubmodule_eq_span_iff_coordinateSpanIsStable
      (Pi.basisFun k (Fin (dimension n))) s).mpr ((coordinateSpanIsStable_iff s).mpr hs)

end

end TauCeti.TypeBSpinCarrier.Generated.Positive
