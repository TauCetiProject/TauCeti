/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import TauCeti.AlgebraicTopology.UniversalCover.Deck

/-!
# Deck transformations of additive quotient maps

For a topological additive commutative group `𝕜` and an additive subgroup `H`, this file
identifies the deck transformations of the quotient map
`QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H`. If `𝕜` is preconnected and `H` is totally
disconnected, every deck transformation is translation by an element of `H`, and these
translations identify the deck group with `Multiplicative H`.

## Main declarations

* `TauCeti.Deck.mem_quotientMk`: a homeomorphism lies in the quotient-map deck group iff it
  moves every point by an element of `H`.
* `TauCeti.Deck.addRightQuotient`: translation by an element of `H` as a deck transformation
  of `QuotientAddGroup.mk' H`.
* `TauCeti.Deck.quotientMulEquiv`: the deck group of `QuotientAddGroup.mk' H` is
  `Multiplicative H` under the connectedness hypotheses.

## References

This supplies the quotient-map deck computation used for the Tau Ceti universal-covers
roadmap, Stage 4 target `π₁(S¹) ≅ ℤ`, via the specialization
`AddCircle p = 𝕜 ⧸ zmultiples p`.
-/

namespace TauCeti

open AddSubgroup

namespace Deck

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  {H : AddSubgroup 𝕜}

omit [IsTopologicalAddGroup 𝕜] in
/-- A homeomorphism of `𝕜` is a deck transformation of `QuotientAddGroup.mk' H` exactly when
it moves every point within `H`. -/
@[simp]
theorem mem_quotientMk {φ : 𝕜 ≃ₜ 𝕜} :
    φ ∈ Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H) ↔ ∀ e, φ e - e ∈ H := by
  rw [mem_iff]
  exact forall_congr' fun e => QuotientAddGroup.eq_iff_sub_mem

/-- Right translation by an element of `H`, as a deck transformation of
`QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H`. -/
def addRightQuotient (a : H) : Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H) :=
  ⟨Homeomorph.addRight (a : 𝕜), mem_quotientMk.2 fun e => by
    simpa only [Homeomorph.coe_addRight, add_sub_cancel_left] using a.2⟩

@[simp]
theorem addRightQuotient_apply (a : H) (e : 𝕜) :
    (addRightQuotient a).1 e = e + (a : 𝕜) :=
  rfl

@[simp]
theorem addRightQuotient_zero : addRightQuotient (0 : H) = 1 := by
  apply Subtype.ext
  ext e
  simp

@[simp]
theorem addRightQuotient_add (a b : H) :
    addRightQuotient (a + b) = addRightQuotient a * addRightQuotient b := by
  apply Subtype.ext
  ext e
  simp only [Subgroup.coe_mul, Homeomorph.mul_apply, addRightQuotient_apply]
  push_cast
  abel

theorem addRightQuotient_injective :
    Function.Injective (addRightQuotient : H → Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H)) := by
  intro _ _ h
  have := congrArg (fun φ : Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H) => φ.1 0) h
  simpa using this

/-- On a preconnected domain with totally disconnected quotient subgroup, a deck transformation
of `QuotientAddGroup.mk' H` is right translation by `φ 0`. -/
theorem quotientMk_eq_add_apply_zero [PreconnectedSpace 𝕜] [TotallyDisconnectedSpace H]
    (φ : Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H)) (e : 𝕜) :
    φ.1 e = e + φ.1 0 := by
  have hmem : ∀ x, φ.1 x - x ∈ H := mem_quotientMk.1 φ.2
  have hcont : Continuous fun x => φ.1 x - x := φ.1.continuous.sub continuous_id
  have key : (⟨φ.1 e - e, hmem e⟩ : H) = ⟨φ.1 0 - 0, hmem 0⟩ :=
    TotallyDisconnectedSpace.eq_of_continuous _ (hcont.subtype_mk hmem) e 0
  have h : φ.1 e - e = φ.1 0 - 0 := congrArg Subtype.val key
  rw [sub_zero, sub_eq_iff_eq_add] at h
  rw [h, add_comm]

private def addRightQuotientHom (H : AddSubgroup 𝕜) :
    Multiplicative H →* Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H) where
  toFun a := addRightQuotient a.toAdd
  map_one' := addRightQuotient_zero
  map_mul' _ _ := addRightQuotient_add _ _

private theorem addRightQuotientHom_apply (a : Multiplicative H) :
    addRightQuotientHom H a = addRightQuotient a.toAdd :=
  rfl

/-- The deck transformation group of a quotient map from a preconnected group by a totally
disconnected subgroup is the group of translations by that subgroup. -/
noncomputable def quotientMulEquiv [PreconnectedSpace 𝕜] [TotallyDisconnectedSpace H] :
    Multiplicative H ≃* Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H) :=
  MulEquiv.ofBijective (addRightQuotientHom H) <| by
    refine ⟨fun a b h => ?_, fun φ => ?_⟩
    · exact Multiplicative.toAdd.injective (addRightQuotient_injective h)
    · refine ⟨Multiplicative.ofAdd ⟨φ.1 0, by simpa using mem_quotientMk.1 φ.2 0⟩, ?_⟩
      apply Subtype.ext
      ext e
      rw [addRightQuotientHom_apply]
      simpa using (quotientMk_eq_add_apply_zero φ e).symm

@[simp]
theorem quotientMulEquiv_apply [PreconnectedSpace 𝕜] [TotallyDisconnectedSpace H]
    (a : Multiplicative H) :
    quotientMulEquiv a = addRightQuotient a.toAdd :=
  rfl

@[simp]
theorem quotientMulEquiv_symm_apply_coe [PreconnectedSpace 𝕜] [TotallyDisconnectedSpace H]
    (φ : Deck (QuotientAddGroup.mk' H : 𝕜 → 𝕜 ⧸ H)) :
    ((quotientMulEquiv.symm φ).toAdd : 𝕜) = φ.1 0 := by
  calc
    ((quotientMulEquiv.symm φ).toAdd : 𝕜) =
        (addRightQuotient (quotientMulEquiv.symm φ).toAdd).1 0 := by simp
    _ = (quotientMulEquiv (quotientMulEquiv.symm φ)).1 0 := by
        rw [quotientMulEquiv_apply]
    _ = φ.1 0 := by rw [MulEquiv.apply_symm_apply]

end Deck

end TauCeti
