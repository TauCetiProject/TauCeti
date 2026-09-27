/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.Sylow

/-!
# The two-by-two wreath product in the symmetric group on four points

The imprimitive action of the cyclic group of order two, wreath itself, permutes four points.
Its faithful image has order eight and index three in `S₄`, hence is a Sylow two-subgroup.
We write the cyclic group as `Multiplicative (ZMod 2)`: its group law is addition modulo two.
-/

public section

open Equiv

namespace TauCeti

/-- The imprimitive action of `C₂ ≀ S₂` on two blocks of two points, transported to `Fin 4`. -/
noncomputable def wreathTwoToPermFour :
    WreathProduct (Multiplicative (ZMod 2)) (Fin 2) →* Perm (Fin 4) :=
  (Fintype.equivFinOfCardEq (α := Fin 2 × ZMod 2) (by decide)).permCongrHom.toMonoidHom.comp
    (WreathProduct.imprimitiveToPerm (D := Multiplicative (ZMod 2)) (ι := Fin 2)
      (Λ := ZMod 2))

/-- The imprimitive action on four points is faithful. -/
theorem wreathTwoToPermFour_injective : Function.Injective wreathTwoToPermFour := by
  let : FaithfulSMul (Multiplicative (ZMod 2)) (ZMod 2) :=
    ⟨fun {a b} h => by
      apply Multiplicative.toAdd.injective
      have h0 := h 0
      -- Unfold the `Multiplicative` action as addition to read its value at zero.
      change a.toAdd + (0 : ZMod 2) = b.toAdd + (0 : ZMod 2) at h0
      simpa using h0⟩
  unfold wreathTwoToPermFour
  exact (Fintype.equivFinOfCardEq (α := Fin 2 × ZMod 2) (by decide)).permCongrHom.injective.comp
    (WreathProduct.imprimitiveToPerm_injective (Multiplicative (ZMod 2)) (Fin 2) (ZMod 2))

private theorem wreathTwoToPermFour_rangeRestrict_bijective :
    Function.Bijective wreathTwoToPermFour.rangeRestrict := by
  constructor
  · intro a b h
    exact wreathTwoToPermFour_injective (congrArg Subtype.val h)
  · rintro ⟨x, ⟨y, rfl⟩⟩
    exact ⟨y, rfl⟩

/-- The image of `C₂ ≀ S₂` in `S₄` has order eight. -/
theorem natCard_range_wreathTwoToPermFour :
    Nat.card wreathTwoToPermFour.range = 8 := by
  have hcard := Nat.card_congr (Equiv.ofBijective _ wreathTwoToPermFour_rangeRestrict_bijective)
  rw [← hcard, WreathProduct.card]
  rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod 2))]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The image of `C₂ ≀ S₂` has index three in `S₄`. -/
@[simp]
theorem index_range_wreathTwoToPermFour : wreathTwoToPermFour.range.index = 3 := by
  have h := wreathTwoToPermFour.range.index_mul_card
  rw [natCard_range_wreathTwoToPermFour, Nat.card_perm, Nat.card_fin] at h
  have h' : wreathTwoToPermFour.range.index * 8 = 24 := by
    simpa [Nat.factorial] using h
  omega

/-- The image of `C₂ ≀ S₂` is a Sylow two-subgroup of `S₄`. -/
noncomputable def wreathTwoSylowFour : Sylow 2 (Perm (Fin 4)) :=
  (IsPGroup.of_card (n := 3) natCard_range_wreathTwoToPermFour).toSylow
    (by rw [index_range_wreathTwoToPermFour]; decide)

@[simp]
theorem wreathTwoSylowFour_toSubgroup :
    (wreathTwoSylowFour : Subgroup (Perm (Fin 4))) = wreathTwoToPermFour.range := by
  simp [wreathTwoSylowFour]

/-- The two-by-two wreath product is canonically isomorphic to its Sylow image in `S₄`. -/
noncomputable def wreathTwoSylowFourEquiv :
    WreathProduct (Multiplicative (ZMod 2)) (Fin 2) ≃* wreathTwoSylowFour := by
  rw [wreathTwoSylowFour_toSubgroup]
  exact MulEquiv.ofBijective wreathTwoToPermFour.rangeRestrict
    wreathTwoToPermFour_rangeRestrict_bijective

/-- The Sylow isomorphism agrees with the imprimitive permutation action. -/
@[simp]
theorem coe_wreathTwoSylowFourEquiv (w :
    WreathProduct (Multiplicative (ZMod 2)) (Fin 2)) :
    (wreathTwoSylowFourEquiv w : Perm (Fin 4)) = wreathTwoToPermFour w := by
  unfold wreathTwoSylowFourEquiv
  -- The subgroup equality identifies the subtype codomain with the action's range.
  cases wreathTwoSylowFour_toSubgroup
  rfl

/-- The Sylow image of the two-by-two wreath product has the transitive-group label `4T3`. -/
theorem transitiveGroupLabel_wreathTwoToPermFour :
    TransitiveGroupLabel (⟨2, by simp⟩ : TransitiveGroupIndex 4)
      wreathTwoToPermFour.range := by
  have hindex : (referenceSubgroup 4 ⟨2, by simp⟩).index = 3 := by
    have h := (referenceSubgroup 4 ⟨2, by simp⟩).index_mul_card
    rw [natCard_referenceSubgroup_four_two, Nat.card_perm, Nat.card_fin] at h
    have h' : (referenceSubgroup 4 ⟨2, by simp⟩).index * 8 = 24 := by
      simpa [Nat.factorial] using h
    omega
  let Q : Sylow 2 (Perm (Fin 4)) :=
    (IsPGroup.of_card (n := 3) natCard_referenceSubgroup_four_two).toSylow
      (by rw [hindex]; decide)
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Perm (Fin 4)) wreathTwoSylowFour Q
  have h := congrArg Sylow.toSubgroup hτ
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
    wreathTwoSylowFour_toSubgroup] at h
  refine (transitiveGroupLabel_iff _ _).2 ⟨τ, ?_⟩
  have hmap :
      (MulAut.conj τ).toMonoidHom =
        MulDistribMulAction.toMonoidEnd (MulAut (Perm (Fin 4))) (Perm (Fin 4))
          (MulAut.conj τ) := by
    ext σ
    rfl
  rw [← hmap] at h
  simpa only [Q, IsPGroup.toSylow_coe, referenceSubgroup_four_two] using h

end TauCeti
