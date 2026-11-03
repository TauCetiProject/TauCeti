/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LeftCoderivation

/-!
# Maps between cofree bicomodules

The cofree `(C, D)`-bicomodule on `M` has carrier `(C ⊗ M) ⊗ D`. A map to the
cogenerators `N` extends uniquely to a map of bicomodules into `(C ⊗ N) ⊗ D`.
The extension first applies the left coproduct and then uses the
cofree right-comodule adjunction. Both coproducts here are ordinary algebraic
coproducts; no completion or infinite summation is involved.

This construction supplies the bar maps underlying morphisms of two-sided
A-infinity modules. The bicomodule convention follows V. Lyubashenko and
O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe uR uC uD uM uN

variable {R : Type uR} {C : Type uC} {D : Type uD}
  {M : Type uM} {N : Type uN}
  [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid D] [Module R D] [Coalgebra R D]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

attribute [local instance] cofree

/-- Extend a map to the cogenerators to a map between cofree bicomodules.
The result is bundled as a right-comodule morphism; its left compatibility is
`leftCoactRTensor_comp_bicofreeLift`. -/
noncomputable def bicofreeLift (F : (C ⊗[R] M) ⊗[R] D →ₗ[R] N) :
    Hom R D ((C ⊗[R] M) ⊗[R] D) ((C ⊗[R] N) ⊗[R] D) :=
  Hom.cofreeLift (F.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M))

/-- The left extension, followed by the right cofree lift, is the bicofree lift. -/
theorem bicofreeLift_toLinearMap (F : (C ⊗[R] M) ⊗[R] D →ₗ[R] N) :
    (bicofreeLift F).toLinearMap =
      (F.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M)).rTensor D ∘ₗ
        cofreeCoact R D (C ⊗[R] M) := by
  simp only [bicofreeLift, Hom.cofreeLift_toLinearMap, cofree_coact, cofreeCoact_def]

/-- The bicofree lift commutes with the left coactions as well as the right coactions. -/
theorem leftCoactRTensor_comp_bicofreeLift
    (F : (C ⊗[R] M) ⊗[R] D →ₗ[R] N) :
    leftCoactRTensor D (leftCofreeCoact R C N) ∘ₗ (bicofreeLift F).toLinearMap =
      ((bicofreeLift F).toLinearMap).lTensor C ∘ₗ
        leftCoactRTensor D (leftCofreeCoact R C M) := by
  have hF : leftCofreeCoact R C N ∘ₗ
      (F.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M)) =
      (F.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M)).lTensor C ∘ₗ
        leftCoactRTensor D (leftCofreeCoact R C M) := by
    rw [← LinearMap.comp_assoc, LinearMap.lTensor_def,
      leftCofreeCoact_comp_map (by simp), LinearMap.comp_assoc,
      leftCofreeCoact_comp_leftCoactRTensor_leftCofreeCoact]
    simp only [← LinearMap.lTensor_def, LinearMap.lTensor_comp, LinearMap.comp_assoc]
  rw [bicofreeLift_toLinearMap, ← LinearMap.comp_assoc,
    leftCoactRTensor_comp_rTensor, hF]
  simpa only [LinearMap.lTensor_def, LinearMap.comp_assoc] using
    assoc_comp_rTensor_comp_cofreeCoact
      (leftCofreeCoact R C M) (LinearMap.id : C →ₗ[R] C)
      (F.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M))

/-- Applying both counits to a bicofree lift recovers its prescribed map to the cogenerators. -/
@[simp]
theorem counit_comp_bicofreeLift (F : (C ⊗[R] M) ⊗[R] D →ₗ[R] N) :
    leftCofreeCounit R C N ∘ₗ (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N) ∘ₗ
        (bicofreeLift F).toLinearMap = F := by
  have h := Hom.rid_comp_lTensor_counit_comp_cofreeLift
    (C := D) (F.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M))
  rw [bicofreeLift, h]
  rw [← LinearMap.comp_assoc, LinearMap.lTensor_def,
    leftCofreeCounit_comp_map (by simp), LinearMap.comp_assoc,
    leftCofreeCounit_comp_leftCoactRTensor_leftCofreeCoact, LinearMap.comp_id]

/-- A right-comodule map that also respects the left coaction is recovered from its
component at the two counits. This is uniqueness for maps into a cofree bicomodule. -/
theorem bicofreeLift_counit_comp
    (f : Hom R D ((C ⊗[R] M) ⊗[R] D) ((C ⊗[R] N) ⊗[R] D))
    (hf : leftCoactRTensor D (leftCofreeCoact R C N) ∘ₗ f.toLinearMap =
      f.toLinearMap.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M)) :
    bicofreeLift (leftCofreeCounit R C N ∘ₗ
      (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N) ∘ₗ f.toLinearMap) = f := by
  let π := (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N)
  have hπ : leftCofreeCoact R C N ∘ₗ (π ∘ₗ f.toLinearMap) =
      (π ∘ₗ f.toLinearMap).lTensor C ∘ₗ
        leftCoactRTensor D (leftCofreeCoact R C M) := by
    have hp := comp_rid_comp_lTensor_eq_lTensor_comp_leftCoactRTensor
      (leftCofreeCoact R C N) (Coalgebra.counit (R := R) (A := D))
    have hp' := congrArg (fun k ↦ k ∘ₗ f.toLinearMap) hp
    simpa only [π, LinearMap.comp_assoc, hf, LinearMap.lTensor_comp] using hp'
  have h := eq_add_of_leftCofreeCoact_comp_eq
    (leftCoactRTensor D (leftCofreeCoact R C M)) LinearMap.id
    (K := 0) (by simpa only [zero_add, LinearMap.lTensor_def] using hπ)
  simp only [LinearMap.comp_zero, zero_add, ← LinearMap.lTensor_def] at h
  have h' := congrArg (Hom.cofreeLift (C := D)) h.symm
  exact h'.trans (Hom.cofreeLift_rid_comp_lTensor_counit_comp f)

/-- Two bicomodule maps into a cofree bicomodule agree if their two-counit components agree. -/
theorem bicofree_ext
    {f g : Hom R D ((C ⊗[R] M) ⊗[R] D) ((C ⊗[R] N) ⊗[R] D)}
    (hf : leftCoactRTensor D (leftCofreeCoact R C N) ∘ₗ f.toLinearMap =
      f.toLinearMap.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M))
    (hg : leftCoactRTensor D (leftCofreeCoact R C N) ∘ₗ g.toLinearMap =
      g.toLinearMap.lTensor C ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M))
    (h : leftCofreeCounit R C N ∘ₗ (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N) ∘ₗ f.toLinearMap =
      leftCofreeCounit R C N ∘ₗ (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N) ∘ₗ g.toLinearMap) : f = g := by
  rw [← bicofreeLift_counit_comp f hf, h, bicofreeLift_counit_comp g hg]

/-- A right-comodule map with a possibly twisted left coaction vanishes if its two-counit
component vanishes. This also detects commutators of differentials and bicomodule maps. -/
theorem Hom.eq_zero_of_bicofree_counit_eq_zero
    (f : Hom R D ((C ⊗[R] M) ⊗[R] D) ((C ⊗[R] N) ⊗[R] D)) (τ : C →ₗ[R] C)
    (hf : leftCoactRTensor D (leftCofreeCoact R C N) ∘ₗ f.toLinearMap =
      TensorProduct.map τ f.toLinearMap ∘ₗ leftCoactRTensor D (leftCofreeCoact R C M))
    (h : leftCofreeCounit R C N ∘ₗ (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N) ∘ₗ f.toLinearMap = 0) : f = 0 := by
  let π := (TensorProduct.rid R (C ⊗[R] N)).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := D)).lTensor (C ⊗[R] N)
  have hπ : leftCofreeCoact R C N ∘ₗ (π ∘ₗ f.toLinearMap) =
      TensorProduct.map τ (π ∘ₗ f.toLinearMap) ∘ₗ
        leftCoactRTensor D (leftCofreeCoact R C M) := by
    have hp := comp_rid_comp_lTensor_eq_lTensor_comp_leftCoactRTensor
      (leftCofreeCoact R C N) (Coalgebra.counit (R := R) (A := D))
    have hp' := congrArg (fun k ↦ k ∘ₗ f.toLinearMap) hp
    simp only [LinearMap.comp_assoc] at hp'
    rw [hf] at hp'
    simp only [← LinearMap.comp_assoc, LinearMap.lTensor_comp_map] at hp'
    simpa only [π, LinearMap.comp_assoc] using hp'
  have hz := eq_add_of_leftCofreeCoact_comp_eq
    (leftCoactRTensor D (leftCofreeCoact R C M)) τ (K := 0) (by simpa using hπ)
  have hc : leftCofreeCounit R C N ∘ₗ π ∘ₗ f.toLinearMap = 0 := h
  rw [hc, TensorProduct.map_zero_right, LinearMap.comp_zero, LinearMap.zero_comp,
    add_zero] at hz
  exact (Hom.eq_zero_iff_counit f).2 hz

end TauCeti.Comodule
