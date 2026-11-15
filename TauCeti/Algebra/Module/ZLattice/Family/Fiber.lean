/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic

/-!
# The fibres of a period quotient

For a period family `P : Y → (Λ →ₗ[ℤ] E)`, the fibre over `y` of the standard orbit quotient
`(Y × E)/Λ → Y` is canonically homeomorphic to the standard translation quotient
`E / LinearMap.range (P y)`. The map sends `[v]` to `[y, v]` and is independent of any choice of
lattice basis. Its composite with the inclusion of the fibre is a topological embedding.

Only continuity of the periods is needed: neither injectivity nor fullness nor discreteness is
required for this topological identification. In particular it applies to continuous and
holomorphic families of full lattices. Both quotients carry their quotient topologies, and the
fibre carries its subspace topology in the total period quotient.

The quotient topology on the slice `{y} × E` agrees with the subspace topology of the fibre.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori given by period matrices).
-/

public section

open Set Function Topology

namespace TauCeti

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E) (y : Y)

/-- The map from the translation quotient at `y` into the total period quotient,
sending `[v]` to `[y, v]`. -/
def torusFamilyFiberMap :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient (LinearMap.range (P y)) E →
      AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction P
  Quotient.map (fun v ↦ (y, v)) fun v w h ↦ by
    obtain ⟨l, hl⟩ := (AddAction.mem_orbit_iff.mp h)
    obtain ⟨a, ha⟩ := l.2
    apply (mem_orbit_periodAddAction_iff P).2
    refine ⟨rfl, a, ?_⟩
    rw [ha]
    exact eq_sub_iff_add_eq.mpr (by simpa [Submodule.vadd_def, vadd_eq_add, add_comm] using hl)

/-- The inclusion of a fibre sends the class of `v` to the class of `(y, v)`. -/
@[simp] theorem torusFamilyFiberMap_mk (v : E) :
    torusFamilyFiberMap P y (Quotient.mk _ v) = Quotient.mk _ (y, v) := (rfl)

/-- The image of the fibre map lies over `y`. -/
@[simp] theorem torusFamilyProjection_fiberMap
    (z : AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :
    torusFamilyProjection P (torusFamilyFiberMap P y z) = y := by
  induction z using Quotient.inductionOn
  simp

/-- Passing from one period fibre to the total quotient identifies no further points. -/
theorem torusFamilyFiberMap_injective : Injective (torusFamilyFiberMap P y) := by
  intro z w h
  induction z using Quotient.inductionOn with | h v =>
    induction w using Quotient.inductionOn with | h u =>
      obtain ⟨_, a, ha⟩ := (mem_orbit_periodAddAction_iff P).1 (Quotient.exact h)
      apply Quotient.sound
      apply AddAction.mem_orbit_iff.mpr
      exact ⟨⟨P y a, LinearMap.mem_range_self _ a⟩, by
        simpa [Submodule.vadd_def, vadd_eq_add, add_comm] using eq_sub_iff_add_eq.mp ha⟩

/-- The image of the fibre quotient is exactly the set-theoretic fibre of the projection. -/
theorem range_torusFamilyFiberMap :
    range (torusFamilyFiberMap P y) = {z | torusFamilyProjection P z = y} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact torusFamilyProjection_fiberMap P y w
  · induction z using Quotient.inductionOn with | h p =>
      intro hp
      have hy : p.1 = y := by simpa using hp
      exact ⟨Quotient.mk _ p.2, (torusFamilyFiberMap_mk P y p.2).trans
        (congrArg (Quotient.mk _) (Prod.ext hy.symm rfl))⟩

variable [TopologicalSpace Y] [TopologicalSpace E] [ContinuousAdd E]
  (hcont : ∀ l, Continuous fun y ↦ P y l)

/- The proof uses Mathlib's subquotient embedding theorem for an open quotient map, applied to
the invariant slice `{y} × E` of the period action. -/
include hcont in
/-- The quotient topology on a period fibre agrees with its subspace topology in the total
period quotient. -/
theorem isEmbedding_torusFamilyFiberMap : IsEmbedding (torusFamilyFiberMap P y) := by
  let _ := periodAddAction P
  let _ := continuousConstVAdd_periodAddAction P hcont
  refine isEmbedding_of_isOpenQuotientMap_of_isInducing
    (fun v : E ↦ (y, v)) (torusFamilyFiberMap P y)
    (Quotient.mk _) (Quotient.mk _) (funext (torusFamilyFiberMap_mk P y)) ?_
    isQuotientMap_quotient_mk'
    (AddAction.isOpenQuotientMap_quotientMk) (torusFamilyFiberMap_injective P y) ?_
  · exact isInducing_prodMkRight y
  · rintro p ⟨_, ⟨v, rfl⟩, hp⟩
    have hy : y = p.1 := by simpa using congrArg (torusFamilyProjection P) hp
    exact ⟨p.2, Prod.ext hy rfl⟩

/-- The canonical identification of the translation quotient at `y` with the literal fibre
of the total period quotient. It sends `[v]` to `[y, v]` and needs no lattice basis. -/
noncomputable def torusFamilyFiberHomeomorph :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient (LinearMap.range (P y)) E ≃ₜ
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y} :=
  (isEmbedding_torusFamilyFiberMap P y hcont).toHomeomorph.trans
    (Homeomorph.setCongr (range_torusFamilyFiberMap P y))

/-- The fibre homeomorphism is the canonical inclusion on underlying points. -/
@[simp] theorem coe_torusFamilyFiberHomeomorph
    (z : AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :
    (torusFamilyFiberHomeomorph P y hcont z).1 = torusFamilyFiberMap P y z := (rfl)

/-- On representatives, the canonical fibre homeomorphism sends `[v]` to `[y, v]`. -/
@[simp] theorem torusFamilyFiberHomeomorph_mk (v : E) :
    torusFamilyFiberHomeomorph P y hcont (Quotient.mk _ v) =
      ⟨Quotient.mk _ (y, v), torusFamilyProjection_mk P (y, v)⟩ := by
  apply Subtype.ext
  simp

/-- The inverse fibre homeomorphism sends the class of `(y, v)` to the class of `v`. -/
@[simp] theorem torusFamilyFiberHomeomorph_symm_mk (v : E) :
    (torusFamilyFiberHomeomorph P y hcont).symm
      ⟨Quotient.mk _ (y, v), torusFamilyProjection_mk P (y, v)⟩ =
      Quotient.mk _ v := by
  rw [← torusFamilyFiberHomeomorph_mk P y hcont]
  exact Homeomorph.symm_apply_apply _ _

end TauCeti
