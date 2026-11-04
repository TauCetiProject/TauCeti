/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.GroupTheory.Subgroup.NormalClosure
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Subgroup presentations from rewritten relators

Let `G = ⟨α | R⟩`, and let `H` be a subgroup of the free group on `α` containing the
normal closure of `R`. A free basis `e : FreeGroup β ≃* H` and right-coset representatives
`T` give a presentation of the image of `H` in `G`: rewrite every `t * r * t⁻¹` in the
basis `e`. The resulting presentation is isomorphic to the actual subgroup of `G`.

`PresentedGroup.subgroupPresentationEquiv` proves this kernel identification, without an
index-two, involutory-generator or finiteness restriction. Its word and generator formulas
record the map into the original presentation. The free basis is an input: this file does
not construct a Schreier basis or a word-rewriting algorithm for a chosen transversal.

## References

* D. L. Johnson, *Presentations of Groups*, second edition, Chapter 9
  (the Reidemeister–Schreier theorem).
-/

public section

namespace PresentedGroup

variable {α β : Type*} (R : Set (FreeGroup α)) (H : Subgroup (FreeGroup α))
  (e : FreeGroup β ≃* H) (T : Set (FreeGroup α))

/-- The conjugates of the original relators by `T`, rewritten in the free basis `e` of `H`.
When `H` contains the original relator kernel and `G = H T`, these are complete relators
for the image of `H` in the presented group. -/
def subgroupRelators : Set (FreeGroup β) :=
  {w | ∃ t ∈ T, ∃ r ∈ R, t * r * t⁻¹ = (e w : FreeGroup α)}

/-- Membership in the rewritten relator family. -/
@[simp]
theorem mem_subgroupRelators (w : FreeGroup β) :
    w ∈ subgroupRelators R H e T ↔
      ∃ t ∈ T, ∃ r ∈ R, t * r * t⁻¹ = (e w : FreeGroup α) := Iff.rfl

/-- The rewritten relators normally generate exactly the kernel of the original quotient
map, restricted to the given free basis of `H`. -/
theorem normalClosure_subgroupRelators
    (hR : Subgroup.normalClosure R ≤ H)
    (hT : ∀ g : FreeGroup α, ∃ h : H, ∃ t ∈ T, (h : FreeGroup α) * t = g) :
    Subgroup.normalClosure (subgroupRelators R H e T) =
      (((mk R).subgroupMap H).comp e.toMonoidHom).ker := by
  rw [← MonoidHom.comap_ker, Subgroup.ker_subgroupMap]
  have hker : (mk R).ker = Subgroup.normalClosure R := by
    ext w
    exact mk_eq_one_iff
  rw [hker, ← H.normalClosure_conjugates_eq_subgroupOf R T hR hT]
  exact Subgroup.comap_normalClosure
    {x : H | ∃ t ∈ T, ∃ r ∈ R, t * r * t⁻¹ = (x : FreeGroup α)} e

/-- The subgroup presentation obtained by rewriting transversal-conjugated relators is
isomorphic to the actual image of `H` in the original presented group.

The input `e` is a proved free basis, not merely a generating family. The representatives
may be redundant: only the factorization `g = h * t` is needed. -/
noncomputable def subgroupPresentationEquiv
    (hR : Subgroup.normalClosure R ≤ H)
    (hT : ∀ g : FreeGroup α, ∃ h : H, ∃ t ∈ T, (h : FreeGroup α) * t = g) :
    PresentedGroup (subgroupRelators R H e T) ≃* H.map (mk R) :=
  (QuotientGroup.quotientMulEquivOfEq (normalClosure_subgroupRelators R H e T hR hT)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (((mk R).subgroupMap_surjective H).comp e.surjective))

/-- On words, the subgroup presentation equivalence is the original quotient map after
inclusion of the chosen free basis. -/
@[simp]
theorem coe_subgroupPresentationEquiv_mk
    (hR : Subgroup.normalClosure R ≤ H)
    (hT : ∀ g : FreeGroup α, ∃ h : H, ∃ t ∈ T, (h : FreeGroup α) * t = g)
    (w : FreeGroup β) :
    (subgroupPresentationEquiv R H e T hR hT (mk _ w) : PresentedGroup R) =
      mk R (e w) := (rfl)

/-- Each new presentation generator maps to the word specified by the free basis. -/
@[simp]
theorem coe_subgroupPresentationEquiv_of
    (hR : Subgroup.normalClosure R ≤ H)
    (hT : ∀ g : FreeGroup α, ∃ h : H, ∃ t ∈ T, (h : FreeGroup α) * t = g)
    (b : β) :
    (subgroupPresentationEquiv R H e T hR hT (of b) : PresentedGroup R) =
      mk R (e (FreeGroup.of b)) :=
  coe_subgroupPresentationEquiv_mk R H e T hR hT _

/-- The inverse dictionary rewrites any word of `H` in its chosen free basis. -/
@[simp]
theorem subgroupPresentationEquiv_symm_subgroupMap
    (hR : Subgroup.normalClosure R ≤ H)
    (hT : ∀ g : FreeGroup α, ∃ h : H, ∃ t ∈ T, (h : FreeGroup α) * t = g)
    (h : H) :
    (subgroupPresentationEquiv R H e T hR hT).symm
      ((mk R).subgroupMap H h) = mk _ (e.symm h) := by
  apply (subgroupPresentationEquiv R H e T hR hT).injective
  apply Subtype.ext
  simp

end PresentedGroup

namespace Subgroup

variable {α β : Type*} {R : Set (FreeGroup α)} (K : Subgroup (PresentedGroup R))
  (e : FreeGroup β ≃* K.comap (PresentedGroup.mk R)) (T : Set (FreeGroup α))

/-- A presentation of the exact subgroup `K` of a presented group, using a free basis of its
preimage and the rewritten transversal-conjugated relators. No assumption that the subgroup
is normal, finite, or of index two is imposed. -/
noncomputable def presentationEquiv
    (hT : ∀ g : FreeGroup α, ∃ h : K.comap (PresentedGroup.mk R),
      ∃ t ∈ T, (h : FreeGroup α) * t = g) :
    PresentedGroup (PresentedGroup.subgroupRelators R (K.comap (PresentedGroup.mk R)) e T) ≃*
      K :=
  (PresentedGroup.subgroupPresentationEquiv R (K.comap (PresentedGroup.mk R)) e T
    (fun w hw ↦ by
      apply mem_comap.mpr
      rw [PresentedGroup.mk_eq_one_iff.mpr hw]
      exact K.one_mem) hT).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective
      (PresentedGroup.mk_surjective R) K))

/-- The subgroup presentation sends a rewritten word to its specified value in the ambient
presented group. -/
@[simp]
theorem coe_presentationEquiv_mk
    (hT : ∀ g : FreeGroup α, ∃ h : K.comap (PresentedGroup.mk R),
      ∃ t ∈ T, (h : FreeGroup α) * t = g) (w : FreeGroup β) :
    (K.presentationEquiv e T hT (PresentedGroup.mk _ w) : PresentedGroup R) =
      PresentedGroup.mk R (e w) := by
  simp only [presentationEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    PresentedGroup.coe_subgroupPresentationEquiv_mk]

/-- The generator dictionary for a subgroup of a presented group. -/
@[simp]
theorem coe_presentationEquiv_of
    (hT : ∀ g : FreeGroup α, ∃ h : K.comap (PresentedGroup.mk R),
      ∃ t ∈ T, (h : FreeGroup α) * t = g) (b : β) :
    (K.presentationEquiv e T hT (PresentedGroup.of b) : PresentedGroup R) =
      PresentedGroup.mk R (e (FreeGroup.of b)) :=
  K.coe_presentationEquiv_mk e T hT _

/-- The inverse of the subgroup presentation rewrites an ambient word in the free basis
of the preimage. -/
@[simp]
theorem presentationEquiv_symm_mk
    (hT : ∀ g : FreeGroup α, ∃ h : K.comap (PresentedGroup.mk R),
      ∃ t ∈ T, (h : FreeGroup α) * t = g)
    (h : K.comap (PresentedGroup.mk R)) :
    (K.presentationEquiv e T hT).symm ⟨PresentedGroup.mk R h, h.property⟩ =
      PresentedGroup.mk _ (e.symm h) := by
  apply (K.presentationEquiv e T hT).injective
  apply Subtype.ext
  simp

end Subgroup
