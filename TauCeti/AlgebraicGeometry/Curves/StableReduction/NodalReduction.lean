/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.BaseChange

/-!
# Nodal reduction of curves

A curve over the fraction field of a discrete valuation ring has nodal reduction when it admits
a proper model whose structure morphism is at worst nodal of relative dimension one. This is the
reduction condition used before unstable components are contracted; it does not impose the
stronger semistability or stability conditions on the special fibre.

The predicate remembers the prescribed generic-fibre identification through `TauCeti.Model`.
It is invariant under isomorphism of that generic fibre. A prestable or smooth proper model is a
witness, and a witness remains one after passage to the chosen place of a finite separable field
extension.

## Main declarations

* `TauCeti.HasNodalReduction`: existence of a proper at-worst-nodal model.
* `TauCeti.HasNodalReduction.of_iso`: invariance under isomorphism of the generic curve.
* `TauCeti.HasNodalReduction.baseChange`: preservation under a chosen finite DVR extension.

## References

* [The Stacks Project, Section 55.18, Semistable reduction](https://stacks.math.columbia.edu/tag/0CDL)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

/-- A curve over the fraction field `K` of a discrete valuation ring `R` has nodal reduction if
it has a proper model over `R` which is at worst nodal of relative dimension one.

This is an existence predicate: the model and its identification with the prescribed generic
fibre are not chosen data. It is deliberately weaker than the prestable, semistable, and stable
family predicates. -/
def HasNodalReduction (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Scheme.{u}) (toK : C ⟶ Spec (.of K)) : Prop :=
  ∃ M : Model R K C toK,
    M.IsProper ∧ AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne M.toBase

/-- The defining characterization of nodal reduction by a proper nodal model. -/
theorem hasNodalReduction_iff (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Scheme.{u}) (toK : C ⟶ Spec (.of K)) :
    HasNodalReduction R K C toK ↔
      ∃ M : Model R K C toK,
        M.IsProper ∧ AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne M.toBase :=
  Iff.rfl

namespace HasNodalReduction

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C D : Scheme.{u}} {toK : C ⟶ Spec (.of K)} {toK' : D ⟶ Spec (.of K)}

/-- A proper at-worst-nodal model witnesses nodal reduction. -/
theorem of_model (M : Model R K C toK) (hproper : M.IsProper)
    (hnodal : AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne M.toBase) :
    HasNodalReduction R K C toK :=
  ⟨M, hproper, hnodal⟩

/-- A prestable model witnesses nodal reduction. -/
theorem of_prestable_model (M : Model R K C toK)
    [AlgebraicGeometry.PrestableFamily M.toBase] : HasNodalReduction R K C toK :=
  of_model M inferInstance
    (AlgebraicGeometry.PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := M.toBase))

/-- A smooth proper relative curve with the prescribed generic fibre has nodal reduction. -/
theorem of_smooth_model (M : Model R K C toK) (hproper : M.IsProper)
    [SmoothOfRelativeDimension 1 M.toBase] : HasNodalReduction R K C toK :=
  of_model M hproper
    (AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne.of_smooth M.toBase)

/-- Nodal reduction is preserved when the prescribed generic curve is replaced by an isomorphic
object over `Spec K`. -/
theorem of_iso (h : HasNodalReduction R K C toK) (e : Over.mk toK ≅ Over.mk toK') :
    HasNodalReduction R K D toK' := by
  rw [hasNodalReduction_iff] at h ⊢
  obtain ⟨M, hproper, hnodal⟩ := h
  let N : Model R K D toK' :=
    { M with genericFiberIso := M.genericFiberIso.trans e }
  exact ⟨N, hproper, hnodal⟩

/-- Isomorphic generic curves have nodal reduction simultaneously. -/
theorem iff_of_iso (e : Over.mk toK ≅ Over.mk toK') :
    HasNodalReduction R K C toK ↔ HasNodalReduction R K D toK' :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Nodal reduction persists after base change to the chosen local ring of a finite separable
extension of the fraction field. -/
theorem baseChange (h : HasNodalReduction R K C toK) (E : FiniteDVRExtension R K) :
    HasNodalReduction E.localRing E.extensionField
      (genericFiber K E.extensionField toK).left
      (genericFiber K E.extensionField toK).hom := by
  rw [hasNodalReduction_iff] at h ⊢
  obtain ⟨M, hproper, hnodal⟩ := h
  refine ⟨M.baseChange E, M.isProper_baseChange E hproper, ?_⟩
  rw [Model.baseChange_toBase]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne)]
  rw [genericFiber_hom]
  exact MorphismProperty.of_isPullback
    (P := @AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne)
    (.of_hasPullback M.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))) hnodal

end HasNodalReduction

end TauCeti
