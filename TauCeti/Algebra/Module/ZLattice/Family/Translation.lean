/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic

/-!
# Fibrewise translation on a family of tori

For a period family `P : Y → (Λ →ₗ[ℤ] E)`, the vector space `E` acts on the total space
`(Y × E)/Λ` of the family of tori by translation along the fibres, `v +ᵥ [y, w] = [y, v + w]`
(`TauCeti.torusFamilyTranslationAddAction`). The action is well defined because translations
of the vector coordinate commute with the period translations. Its orbits are the fibres of the
projection to `Y` (`TauCeti.torusFamilyTranslationAddAction_mem_orbit_iff`), and the stabilizer of
a point is the period lattice `LinearMap.range (P y)` at its base point `y`
(`TauCeti.torusFamilyTranslationAddAction_stabilizer`). Thus on the fibre over `y` this is the
translation action of `E` on the torus `E / LinearMap.range (P y)`, and the fibrewise translation
is how a vector of `E` is added to a point of the family; affine maps of the family are built from
it in `TauCeti.Algebra.Module.ZLattice.Family.AffineAction`.

## Main definitions

* `TauCeti.torusFamilyTranslationAddAction`: the action of `E` on the family by fibrewise
  translation.

## Main results

* `TauCeti.torusFamilyTranslationAddAction_mem_orbit_iff`: the orbits are the fibres.
* `TauCeti.torusFamilyTranslationAddAction_stabilizer`: the stabilizers are the period lattices.
* `TauCeti.continuousVAdd_torusFamilyTranslationAddAction`: the action is jointly continuous for a
  continuous family of periods.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

namespace TauCeti

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] (P : Y → Λ →ₗ[ℤ] E)

/-- Translating the vector coordinate carries period orbits to period orbits. -/
private theorem orbitRel_translate (v : E) (p q : Y × E) :
    letI := periodAddAction P
    AddAction.orbitRel Λ (Y × E) p q →
      AddAction.orbitRel Λ (Y × E) (p.1, v + p.2) (q.1, v + q.2) := by
  let _ := periodAddAction P
  intro hpq
  obtain ⟨l, rfl⟩ := AddAction.mem_orbit_iff.1 (AddAction.orbitRel_apply.1 hpq)
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  exact ⟨l, by simp [add_assoc]⟩

/-- The action of `E` on the family of tori `(Y × E)/Λ` by fibrewise translation,
`v +ᵥ [y, w] = [y, v + w]`. It preserves each fibre, and on the fibre over `y` it is the
translation action of `E` on the torus `E / LinearMap.range (P y)`. -/
@[instance_reducible]
def torusFamilyTranslationAddAction :
    letI := periodAddAction P
    AddAction E (AddAction.orbitRel.Quotient Λ (Y × E)) :=
  letI := periodAddAction P
  { vadd v := Quotient.map (fun p ↦ (p.1, v + p.2)) (orbitRel_translate P v)
    zero_vadd x := by
      induction x using Quotient.inductionOn with
      | h p => exact congrArg (Quotient.mk _) (by simp)
    add_vadd v w x := by
      induction x using Quotient.inductionOn with
      | h p => exact congrArg (Quotient.mk _) (by simp [add_assoc]) }

/-- Fibrewise translation by `v` sends the class of `(y, w)` to the class of `(y, v + w)`. -/
@[simp] theorem torusFamilyTranslationAddAction_vadd_mk (v : E) (p : Y × E) :
    letI := periodAddAction P
    letI := torusFamilyTranslationAddAction P
    v +ᵥ (Quotient.mk _ p : AddAction.orbitRel.Quotient Λ (Y × E)) =
      Quotient.mk _ (p.1, v + p.2) := (rfl)

/-- Fibrewise translation preserves the fibres of the family of tori. -/
@[simp] theorem torusFamilyProjection_vadd (v : E)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyTranslationAddAction P
    torusFamilyProjection P (v +ᵥ x) = torusFamilyProjection P x := by
  induction x using Quotient.inductionOn with
  | h p => simp

/-- **The orbits of fibrewise translation are the fibres** of the family of tori. -/
theorem torusFamilyTranslationAddAction_mem_orbit_iff
    {x x' : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)} :
    letI := torusFamilyTranslationAddAction P
    x' ∈ AddAction.orbit E x ↔ torusFamilyProjection P x' = torusFamilyProjection P x := by
  let _ := periodAddAction P
  let _ := torusFamilyTranslationAddAction P
  refine ⟨fun ⟨v, hv⟩ ↦ by rw [← hv, torusFamilyProjection_vadd], fun h ↦ ?_⟩
  induction x using Quotient.inductionOn with | h p =>
    induction x' using Quotient.inductionOn with | h q =>
      refine ⟨q.2 - p.2, congrArg (Quotient.mk _) (Prod.ext ?_ (sub_add_cancel q.2 p.2))⟩
      simpa using h.symm

/-- **The stabilizer of fibrewise translation is the period lattice** at the base point. -/
theorem torusFamilyTranslationAddAction_stabilizer
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyTranslationAddAction P
    AddAction.stabilizer E x = (LinearMap.range (P (torusFamilyProjection P x))).toAddSubgroup := by
  let _ := periodAddAction P
  let _ := torusFamilyTranslationAddAction P
  induction x using Quotient.inductionOn with | h p =>
    ext v
    rw [AddAction.mem_stabilizer_iff, torusFamilyTranslationAddAction_vadd_mk, Quotient.eq,
      AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff]
    simp

/-- Translating a point of the family by a period at its base point does not move it. -/
@[simp] theorem torusFamilyTranslationAddAction_period_vadd (l : Λ)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyTranslationAddAction P
    P (torusFamilyProjection P x) l +ᵥ x = x := by
  let _ := torusFamilyTranslationAddAction P
  rw [← AddAction.mem_stabilizer_iff, torusFamilyTranslationAddAction_stabilizer]
  exact LinearMap.mem_range_self _ l

/-- Fibrewise translation is jointly continuous when the periods depend continuously on the
parameter. -/
theorem continuousVAdd_torusFamilyTranslationAddAction [TopologicalSpace Y] [TopologicalSpace E]
    [ContinuousAdd E] (hcont : ∀ l, Continuous fun y ↦ P y l) :
    letI := periodAddAction P
    letI := torusFamilyTranslationAddAction P
    ContinuousVAdd E (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyTranslationAddAction P
  have := continuousConstVAdd_periodAddAction P hcont
  -- `E × (Y × E) → E × (Y × E)/Λ` is an open quotient map, so continuity can be checked upstairs.
  refine ⟨(IsOpenQuotientMap.id.prodMap
    AddAction.isOpenQuotientMap_quotientMk).continuous_comp_iff.1 ?_⟩
  exact continuous_quot_mk.comp
    (continuous_snd.fst.prodMk (continuous_fst.add continuous_snd.snd))

end TauCeti
