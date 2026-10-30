/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ULift
public import TauCeti.Algebra.Algebra.ULift
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr

/-!
# Finite Galois levels under universe lifting

A subextension of the separable closure of `K` has a corresponding subextension of the
chosen separable closure of `ULift K`. The latter is the image of the actual lifted field,
not a new choice of a splitting field. Finiteness, degree and the Galois property are
preserved. Conjugating automorphisms through this identification commutes with restriction
from the absolute Galois groups.

These finite-level identifications supply the field and group data for comparing inflated
cocycles across universes. They use the same chosen separable-closure identification as
`RingEquiv.absoluteGaloisGroupCongr`; thus the restriction square compares actual maps,
independently of any Brauer or cohomology comparison.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
-/

public noncomputable section

universe u w

namespace IntermediateField

variable {K : Type u} [Field K] (E : IntermediateField K (SeparableClosure K))

/-- The simultaneous lifted algebra action, matching `AlgEquiv.uliftAutEquiv`.
It is local to avoid enabling the generic lifted-scalar instance on intermediate fields
or their separable closures. -/
local instance uliftSeparableClosureAlgebra : Algebra (ULift.{w} K) (ULift.{w} E) :=
  ULift.algebra' K (ULift.{w} E)

/-- Embed the lifted subextension in the separable closure of the lifted base field,
using the chosen identification of separable closures. -/
def uliftSeparableClosureEmbedding :
    ULift.{w} E →ₐ[ULift.{w} K] SeparableClosure (ULift.{w} K) where
  toRingHom := (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm.toRingHom.comp
    (E.val.toRingHom.comp (ULift.ringEquiv : ULift.{w} E ≃+* E).toRingHom)
  commutes' r := by
    convert (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr_symm_algebraMap
      r.down using 1 <;> rfl

@[simp]
theorem uliftSeparableClosureEmbedding_apply (x : ULift.{w} E) :
    uliftSeparableClosureEmbedding.{u, w} E x =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm
        (x.down : SeparableClosure K) := (rfl)

/-- The image of the lifted subextension inside the chosen separable closure of `ULift K`. -/
def uliftSeparableClosure : IntermediateField (ULift.{w} K) (SeparableClosure (ULift.{w} K)) :=
  (uliftSeparableClosureEmbedding.{u, w} E).fieldRange

/-- The lifted field is isomorphic, over the lifted base, to its image in the separable closure.
For operations requiring synthesis of the source algebra action, such as taking the inverse,
enable Mathlib's `ULift.algebra'` locally. -/
def uliftSeparableClosureEquiv :
    ULift.{w} E ≃ₐ[ULift.{w} K] uliftSeparableClosure.{u, w} E :=
  (uliftSeparableClosureEmbedding.{u, w} E).equivFieldRange

@[simp]
theorem coe_uliftSeparableClosureEquiv (x : ULift.{w} E) :
    (uliftSeparableClosureEquiv.{u, w} E x : SeparableClosure (ULift.{w} K)) =
      uliftSeparableClosureEmbedding.{u, w} E x := (rfl)

/-- The inverse field identification is the chosen separable-closure map on underlying elements. -/
@[simp]
theorem coe_uliftSeparableClosureEquiv_symm (x : uliftSeparableClosure.{u, w} E) :
    ((uliftSeparableClosureEquiv.{u, w} E).symm x).down.val =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr x := by
  apply (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm.injective
  simp [← uliftSeparableClosureEmbedding_apply, ← coe_uliftSeparableClosureEquiv]

/-- Membership in the transported field is tested in the original separable closure. -/
@[simp]
theorem mem_uliftSeparableClosure (x : SeparableClosure (ULift.{w} K)) :
    x ∈ uliftSeparableClosure.{u, w} E ↔
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr x ∈ E := by
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    refine ⟨ULift.up ⟨_, hx⟩, ?_⟩
    simp

/-- Refining a subextension refines its transported image. -/
theorem uliftSeparableClosure_mono {E F : IntermediateField K (SeparableClosure K)}
    (h : E ≤ F) : uliftSeparableClosure.{u, w} E ≤ uliftSeparableClosure.{u, w} F := by
  intro x hx
  exact (F.mem_uliftSeparableClosure x).2 (h ((E.mem_uliftSeparableClosure x).1 hx))

/-- Transport preserves and reflects inclusion of subextensions. -/
@[simp]
theorem uliftSeparableClosure_le_iff {E F : IntermediateField K (SeparableClosure K)} :
    uliftSeparableClosure.{u, w} E ≤ uliftSeparableClosure.{u, w} F ↔ E ≤ F := by
  refine ⟨?_, uliftSeparableClosure_mono⟩
  intro h x hx
  have hmem := h ((E.mem_uliftSeparableClosure
    ((ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm x)).2 (by
      simpa using hx))
  simpa using (F.mem_uliftSeparableClosure _).1 hmem

/-- The degree is unchanged when both the base and subextension are lifted. -/
@[simp]
theorem finrank_uliftSeparableClosure :
    Module.finrank (ULift.{w} K) (uliftSeparableClosure.{u, w} E) =
      Module.finrank K E := by
  apply (Algebra.finrank_eq_of_equiv_equiv
    (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)
    (ULift.ringEquiv.symm.trans (uliftSeparableClosureEquiv.{u, w} E).toRingEquiv) ?_).symm
  apply RingHom.ext
  intro r
  exact ((uliftSeparableClosureEquiv.{u, w} E).commutes (ULift.up r)).symm

/-- A finite subextension remains finite in the larger universe. -/
instance [FiniteDimensional K E] :
    FiniteDimensional (ULift.{w} K) (uliftSeparableClosure.{u, w} E) := by
  apply Module.finite_of_finrank_pos
  rw [finrank_uliftSeparableClosure]
  exact Module.finrank_pos

/-- Normality is preserved when the base and subextension are lifted. -/
instance [Normal K E] : Normal (ULift.{w} K) (uliftSeparableClosure.{u, w} E) := by
  apply Normal.of_equiv_equiv
    (f := (ULift.ringEquiv.symm : K ≃+* ULift.{w} K))
    (g := ULift.ringEquiv.symm.trans (uliftSeparableClosureEquiv.{u, w} E).toRingEquiv)
  apply RingHom.ext
  intro r
  exact ((uliftSeparableClosureEquiv.{u, w} E).commutes (ULift.up r)).symm

/-- The transported normal subextension is Galois: its separability is inherited from
the separable closure. -/
instance [Normal K E] : IsGalois (ULift.{w} K) (uliftSeparableClosure.{u, w} E) where

/-- Identify automorphisms by lifting and then conjugating through the embedding into the
chosen separable closure. No finiteness or normality is needed. -/
def uliftSeparableClosureAutEquiv :
    (E ≃ₐ[K] E) ≃* ((uliftSeparableClosure.{u, w} E) ≃ₐ[ULift.{w} K]
      uliftSeparableClosure.{u, w} E) :=
  AlgEquiv.uliftAutEquiv.trans (AlgEquiv.autCongr (uliftSeparableClosureEquiv.{u, w} E))

@[simp]
theorem uliftSeparableClosureAutEquiv_apply (g : E ≃ₐ[K] E) (x : ULift.{w} E) :
    uliftSeparableClosureAutEquiv.{u, w} E g (uliftSeparableClosureEquiv.{u, w} E x) =
      uliftSeparableClosureEquiv.{u, w} E (ULift.up (g x.down)) := by
  rw [uliftSeparableClosureAutEquiv, MulEquiv.trans_apply, AlgEquiv.autCongr_apply]
  simp

/-- Restriction from the absolute Galois group commutes with simultaneous lifting of the
base and a normal subextension. This is an equality of the actual finite-level maps. -/
theorem uliftSeparableClosureAutEquiv_restrictNormalHom [Normal K E]
    (g : TauCeti.AbsoluteGaloisGroup (ULift.{w} K)) :
    uliftSeparableClosureAutEquiv.{u, w} E
        (AlgEquiv.restrictNormalHom E
          ((ULift.ringEquiv.symm : K ≃+* ULift.{w} K).absoluteGaloisGroupCongr g)) =
      AlgEquiv.restrictNormalHom (uliftSeparableClosure.{u, w} E) g := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (uliftSeparableClosureEquiv.{u, w} E).surjective x
  apply Subtype.val_injective
  rw [uliftSeparableClosureAutEquiv_apply, coe_uliftSeparableClosureEquiv,
    uliftSeparableClosureEmbedding_apply]
  simp only [AlgEquiv.restrictNormalHom_apply,
    RingEquiv.absoluteGaloisGroupCongr_apply, RingEquiv.symm_apply_apply,
    coe_uliftSeparableClosureEquiv, uliftSeparableClosureEmbedding_apply]

/-- The open normal subgroup attached to a finite Galois level is transported by the
same absolute-Galois-group equivalence. The equality also holds for infinite normal levels. -/
theorem fixingSubgroup_uliftSeparableClosure [Normal K E] :
    (uliftSeparableClosure.{u, w} E).fixingSubgroup = E.fixingSubgroup.comap
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).absoluteGaloisGroupCongr.toMonoidHom := by
  rw [← restrictNormalHom_ker, ← E.restrictNormalHom_ker]
  ext g
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
  rw [← uliftSeparableClosureAutEquiv_restrictNormalHom]
  exact (uliftSeparableClosureAutEquiv.{u, w} E).map_eq_one_iff

end IntermediateField
