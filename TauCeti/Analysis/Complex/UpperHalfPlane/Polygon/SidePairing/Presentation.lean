/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Relations
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Tessellation
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The relator quotient of a side-paired polygon

The side-identification words and finite-vertex cycle words of a side-paired hyperbolic polygon
give a group presented by generators indexed by sides. Evaluating the generators in a group
containing the side-pairing transformations factors through this presented group. For a locally
finite fundamental polygon, this map is surjective. The remaining direction of Poincaré's
presentation theorem is that the displayed relators generate the entire kernel.

An ideal vertex contributes no finite-order relation. At a finite vertex the cycle word is
raised to the order of its cycle transformation, so its image is the identity.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapter 3.
-/

public section

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- The side-identification and finite-vertex cycle relators of a side pairing. -/
def relators : Set (FreeGroup (Fin n)) :=
  range σ.sideRelator ∪
    {w | ∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
      w = σ.cycleWord j ^ orderOf (σ.cycleMap j)}

/-- A word is a relator exactly when it is a side-identification word or a finite-vertex cycle
power. -/
@[simp]
theorem mem_relators_iff {w : FreeGroup (Fin n)} :
    w ∈ σ.relators ↔
      (∃ i, σ.sideRelator i = w) ∨
        (∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
          w = σ.cycleWord j ^ orderOf (σ.cycleMap j)) := by
  simp [relators]

/-- A side-identification word belongs to the relator set. -/
theorem sideRelator_mem_relators (i : Fin n) : σ.sideRelator i ∈ σ.relators :=
  Or.inl ⟨i, rfl⟩

/-- The order relation of a finite vertex belongs to the relator set. -/
theorem cycleWord_pow_mem_relators {j : Fin n} {z : ℍ} (hj : P.vertex j = .inl z) :
    σ.cycleWord j ^ orderOf (σ.cycleMap j) ∈ σ.relators :=
  Or.inr ⟨j, z, hj, rfl⟩

/-- Every displayed relator evaluates to the identity in the projective group. -/
theorem pairingHom_eq_one_of_mem_relators {w : FreeGroup (Fin n)} (hw : w ∈ σ.relators) :
    σ.pairingHom w = 1 := by
  rcases hw with ⟨i, rfl⟩ | ⟨j, z, _, rfl⟩
  · simp
  · simp

/-- The quotient of the free side group by the side and finite-vertex cycle relations. -/
abbrev RelatorQuotient := PresentedGroup σ.relators

/-- Every side-identification word is trivial in the relator quotient. -/
@[simp]
theorem relatorQuotient_sideRelator (i : Fin n) :
    PresentedGroup.mk σ.relators (σ.sideRelator i) = 1 :=
  PresentedGroup.one_of_mem (σ.sideRelator_mem_relators i)

/-- A finite-vertex cycle word has order dividing that of its cycle transformation in the
relator quotient. -/
@[simp]
theorem relatorQuotient_cycleWord_pow {j : Fin n} {z : ℍ}
    (hj : P.vertex j = .inl z) :
    (PresentedGroup.mk σ.relators (σ.cycleWord j)) ^ orderOf (σ.cycleMap j) = 1 := by
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (σ.cycleWord_pow_mem_relators hj)

/-- Evaluation of the side generators as elements of a subgroup containing all the pairing
transformations. -/
def generatorsIn {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ) (i : Fin n) : Γ :=
  ⟨σ.map i, hmap i⟩

@[simp]
theorem coe_generatorsIn {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (i : Fin n) : (σ.generatorsIn hmap i : PSL(2, ℝ)) = σ.map i :=
  by simp [generatorsIn]

/-- Evaluation of side words in a subgroup agrees with evaluation in `PSL(2, ℝ)`. -/
theorem subtype_comp_lift_generatorsIn {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ) :
    Γ.subtype.comp (FreeGroup.lift (σ.generatorsIn hmap)) = σ.pairingHom := by
  ext i
  simp

/-- The side-pairing relators hold in every subgroup containing the pairing transformations. -/
theorem lift_generatorsIn_eq_one_of_mem_relators {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ) {w : FreeGroup (Fin n)} (hw : w ∈ σ.relators) :
    FreeGroup.lift (σ.generatorsIn hmap) w = 1 := by
  apply Γ.subtype_injective
  rw [← MonoidHom.comp_apply, σ.subtype_comp_lift_generatorsIn hmap]
  exact σ.pairingHom_eq_one_of_mem_relators hw

/-- Evaluate the side-pairing relator quotient in a subgroup containing the pairing maps. -/
def relatorQuotientTo {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ) :
    σ.RelatorQuotient →* Γ :=
  PresentedGroup.toGroup (fun _ hw ↦ σ.lift_generatorsIn_eq_one_of_mem_relators hmap hw)

/-- Evaluation of a side generator in the relator quotient is its pairing transformation. -/
@[simp]
theorem relatorQuotientTo_of {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (i : Fin n) : σ.relatorQuotientTo hmap (PresentedGroup.of i) = σ.generatorsIn hmap i :=
  PresentedGroup.toGroup.of _

/-- Evaluation after passing to the relator quotient agrees with evaluation of side words. -/
@[simp]
theorem relatorQuotientTo_mk {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (w : FreeGroup (Fin n)) :
    σ.relatorQuotientTo hmap (PresentedGroup.mk σ.relators w) =
      FreeGroup.lift (σ.generatorsIn hmap) w := by
  exact FreeGroup.lift_unique
    ((σ.relatorQuotientTo hmap).comp (PresentedGroup.mk σ.relators))
    (fun i => by simpa [PresentedGroup.of] using σ.relatorQuotientTo_of hmap i)

/-- The cycle word at a finite vertex has exactly the same order in the relator quotient as
its transformation. Relations at other sides and vertices cannot shorten this order. -/
theorem orderOf_relatorQuotient_cycleWord {j : Fin n} {z : ℍ}
    (hj : P.vertex j = .inl z) :
    orderOf (PresentedGroup.mk σ.relators (σ.cycleWord j)) =
      orderOf (σ.cycleMap j) := by
  let hmap : ∀ i, σ.map i ∈ (⊤ : Subgroup PSL(2, ℝ)) := fun _ => Subgroup.mem_top _
  have heval :
      ((σ.relatorQuotientTo hmap) (PresentedGroup.mk σ.relators (σ.cycleWord j)) :
        PSL(2, ℝ)) = σ.cycleMap j := by
    rw [σ.relatorQuotientTo_mk]
    have h := congrArg (fun f : FreeGroup (Fin n) →* PSL(2, ℝ) ↦ f (σ.cycleWord j))
      (σ.subtype_comp_lift_generatorsIn hmap)
    simpa using h
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_iff_pow_eq_one.mpr (σ.relatorQuotient_cycleWord_pow hj)
  · have h := orderOf_map_dvd (σ.relatorQuotientTo hmap)
      (PresentedGroup.mk σ.relators (σ.cycleWord j))
    have h' : orderOf
        (((σ.relatorQuotientTo hmap) (PresentedGroup.mk σ.relators (σ.cycleWord j))) :
          PSL(2, ℝ)) ∣
        orderOf (PresentedGroup.mk σ.relators (σ.cycleWord j)) := by
      simpa only [Subgroup.orderOf_coe] using h
    rwa [heval] at h'

/-- The relator quotient maps onto the group of a locally finite fundamental polygon. The
kernel equality needed to make this map an isomorphism is the remaining presentation theorem. -/
theorem relatorQuotientTo_surjective {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Surjective (σ.relatorQuotientTo hmap) := by
  have hclosure : Subgroup.closure (range (σ.generatorsIn hmap)) = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure, Subgroup.map_top, Γ.range_subtype]
    have hrange : Γ.subtype '' range (σ.generatorsIn hmap) = range σ.map := by
      ext x
      simp
    rw [hrange]
    exact σ.closure_range_map_eq hmap hlf hdisj
  have hlift : Function.Surjective (FreeGroup.lift (σ.generatorsIn hmap)) :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hclosure
  intro γ
  obtain ⟨w, hw⟩ := hlift γ
  exact ⟨PresentedGroup.mk σ.relators w, by simpa using hw⟩

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
