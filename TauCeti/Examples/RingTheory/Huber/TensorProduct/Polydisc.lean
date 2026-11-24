/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Polydisc
public import TauCeti.RingTheory.Huber.TensorProduct.Associator
public import TauCeti.RingTheory.Huber.TensorProduct.Map
public import TauCeti.RingTheory.Huber.TensorProduct.Symmetry
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks for completed tensor products of closed discs

The ring-level disc checks of AdicEtaleGeometry A0.7. Over a Huber ring `A`, both iterated
completed tensor products of three closed discs `A⟨T⟩`, `A⟨S⟩`, `A⟨R⟩` are identified with
`A⟨T, S, R⟩`, coefficients and the three coordinates being pinned in the order `T, S, R`; under
these identifications the associator is the identity of `A⟨T, S, R⟩`
(*three_discs_associator_field*, stated for every Huber ring, so in particular for every complete
nonarchimedean field, and *three_discs_associator* over `ℚ_p`). Under
`A⟨T⟩ ⊗̂_A A⟨T⟩ ≃ A⟨T, S⟩` the symmetry of the completed tensor product is the automorphism
`T ↔ S`, an involution, and over `ℚ_p` it is not the identity: it moves evaluation at
`(T, S) = (0, 1)` to evaluation at `(1, 0)` (*symmetry_and_unit_on_charts*).
-/

public section

open TensorProduct TauCeti.Huber

namespace TauCeti.Examples.CompletedTensorPolydisc

section Generic

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- The closed disc `A⟨T⟩` and the closed polydisc `A⟨T₁, …, Tₙ⟩` over `A`. -/
local notation "D" n => restrictedMvPowerSeriesCompletion n A

/-- The coordinate `Tᵢ` of `A⟨T₁, …, Tₙ⟩`. -/
local notation "V" n => Pair.polydiscVar n A

-- The comparison `A⟨T⟩ ⊗̂_A A⟨S⟩ ≃ A⟨T, S⟩` sends `T ⊗ 1` to `T` and `1 ⊗ S` to `S`.
example :
    CompletedTensor.polydiscEquiv A 1 1 (CompletedTensor.inl A _ _ ((V 1) 0)) = (V 2) 0 ∧
      CompletedTensor.polydiscEquiv A 1 1 (CompletedTensor.inr A _ _ ((V 1) 0)) = (V 2) 1 :=
  ⟨CompletedTensor.polydiscEquiv_inl_polydiscVar A 1 1 0,
    CompletedTensor.polydiscEquiv_inr_polydiscVar A 1 1 0⟩

-- The comparison is a homeomorphism.
example (m n : ℕ) : IsHomeomorph (CompletedTensor.polydiscEquiv A m n) :=
  CompletedTensor.isHomeomorph_polydiscEquiv A m n

/-- `A⟨T⟩ ⊗̂_A A⟨S⟩ ≃ A⟨T, S⟩` lies over `A`. -/
theorem polydiscEquiv_comp_algebraMap (m n : ℕ) :
    ((CompletedTensor.polydiscEquiv A m n :
        CompletedTensor A (D m) (D n) →+* D (m + n))).comp
        (algebraMap A (CompletedTensor A (D m) (D n))) =
      algebraMap A (D (m + n)) := by
  ext a
  simp

/-- The identification `(A⟨T⟩ ⊗̂_A A⟨S⟩) ⊗̂_A A⟨R⟩ ≃ A⟨T, S, R⟩`. -/
noncomputable abbrev leftDiscs :
    CompletedTensor A (CompletedTensor A (D 1) (D 1)) (D 1) ≃+* D 3 :=
  (CompletedTensor.congr (A := A) (CompletedTensor.polydiscEquiv A 1 1) (RingEquiv.refl (D 1))
    (polydiscEquiv_comp_algebraMap A 1 1) (RingHom.ext fun _ ↦ rfl)
    (CompletedTensor.continuous_polydiscEquiv A 1 1)
    (CompletedTensor.continuous_polydiscEquiv_symm A 1 1) (continuous_id.congr fun _ ↦ rfl)
    (continuous_id.congr fun _ ↦ rfl)).trans
    (CompletedTensor.polydiscEquiv A (1 + 1) 1)

/-- The identification `A⟨T⟩ ⊗̂_A (A⟨S⟩ ⊗̂_A A⟨R⟩) ≃ A⟨T, S, R⟩`. -/
noncomputable abbrev rightDiscs :
    CompletedTensor A (D 1) (CompletedTensor A (D 1) (D 1)) ≃+* D 3 :=
  (CompletedTensor.congr (A := A) (RingEquiv.refl (D 1)) (CompletedTensor.polydiscEquiv A 1 1)
    (RingHom.ext fun _ ↦ rfl) (polydiscEquiv_comp_algebraMap A 1 1)
    (continuous_id.congr fun _ ↦ rfl) (continuous_id.congr fun _ ↦ rfl)
    (CompletedTensor.continuous_polydiscEquiv A 1 1)
    (CompletedTensor.continuous_polydiscEquiv_symm A 1 1)).trans
    (CompletedTensor.polydiscEquiv A 1 (1 + 1))

/-- `leftDiscs` fixes the coefficients. -/
theorem leftDiscs_algebraMap (a : A) :
    leftDiscs A (algebraMap A _ a) = algebraMap A (D 3) a := by
  rw [CompletedTensor.algebraMap_eq_inl, RingHom.comp_apply, RingEquiv.trans_apply,
    CompletedTensor.congr_inl, CompletedTensor.polydiscEquiv_algebraMap,
    CompletedTensor.inl_algebraMap]
  erw [CompletedTensor.polydiscEquiv_algebraMap]

/-- `rightDiscs` fixes the coefficients. -/
theorem rightDiscs_algebraMap (a : A) :
    rightDiscs A (algebraMap A _ a) = algebraMap A (D 3) a := by
  rw [CompletedTensor.algebraMap_eq_inl, RingHom.comp_apply, RingEquiv.trans_apply,
    CompletedTensor.congr_inl, RingEquiv.refl_apply, CompletedTensor.inl_algebraMap]
  erw [CompletedTensor.polydiscEquiv_algebraMap]

/-- `leftDiscs` sends `T` to the first coordinate. -/
theorem leftDiscs_T :
    leftDiscs A (CompletedTensor.inl A _ _ (CompletedTensor.inl A _ _ ((V 1) 0))) = (V 3) 0 := by
  simp only [RingEquiv.trans_apply, CompletedTensor.congr_inl,
    CompletedTensor.polydiscEquiv_inl_polydiscVar]
  erw [CompletedTensor.polydiscEquiv_inl_polydiscVar]
  rfl

/-- `leftDiscs` sends `S` to the second coordinate. -/
theorem leftDiscs_S :
    leftDiscs A (CompletedTensor.inl A _ _ (CompletedTensor.inr A _ _ ((V 1) 0))) = (V 3) 1 := by
  simp only [RingEquiv.trans_apply, CompletedTensor.congr_inl,
    CompletedTensor.polydiscEquiv_inr_polydiscVar]
  erw [CompletedTensor.polydiscEquiv_inl_polydiscVar]
  rfl

/-- `leftDiscs` sends `R` to the third coordinate. -/
theorem leftDiscs_R : leftDiscs A (CompletedTensor.inr A _ _ ((V 1) 0)) = (V 3) 2 := by
  simp only [RingEquiv.trans_apply, CompletedTensor.congr_inr, RingEquiv.refl_apply]
  erw [CompletedTensor.polydiscEquiv_inr_polydiscVar]
  rfl

/-- `rightDiscs` sends `T` to the first coordinate. -/
theorem rightDiscs_T : rightDiscs A (CompletedTensor.inl A _ _ ((V 1) 0)) = (V 3) 0 := by
  simp only [RingEquiv.trans_apply, CompletedTensor.congr_inl, RingEquiv.refl_apply]
  erw [CompletedTensor.polydiscEquiv_inl_polydiscVar]
  rfl

/-- `rightDiscs` sends `S` to the second coordinate. -/
theorem rightDiscs_S :
    rightDiscs A (CompletedTensor.inr A _ _ (CompletedTensor.inl A _ _ ((V 1) 0))) = (V 3) 1 := by
  simp only [RingEquiv.trans_apply, CompletedTensor.congr_inr,
    CompletedTensor.polydiscEquiv_inl_polydiscVar]
  erw [CompletedTensor.polydiscEquiv_inr_polydiscVar]
  rfl

/-- `rightDiscs` sends `R` to the third coordinate. -/
theorem rightDiscs_R :
    rightDiscs A (CompletedTensor.inr A _ _ (CompletedTensor.inr A _ _ ((V 1) 0))) = (V 3) 2 := by
  simp only [RingEquiv.trans_apply, CompletedTensor.congr_inr,
    CompletedTensor.polydiscEquiv_inr_polydiscVar]
  erw [CompletedTensor.polydiscEquiv_inr_polydiscVar]
  rfl

/-- The inverse of `leftDiscs` is continuous. -/
theorem continuous_leftDiscs_symm : Continuous (leftDiscs A).symm :=
  (CompletedTensor.continuous_congr_symm ..).comp
    (CompletedTensor.continuous_polydiscEquiv_symm A (1 + 1) 1)

/-- `leftDiscs` is a homeomorphism. -/
theorem isHomeomorph_leftDiscs : IsHomeomorph (leftDiscs A) :=
  (leftDiscs A).toEquiv.isHomeomorph_iff.mpr
    ⟨(CompletedTensor.continuous_polydiscEquiv A (1 + 1) 1).comp
      (CompletedTensor.continuous_congr ..), continuous_leftDiscs_symm A⟩

/-- `rightDiscs` is a homeomorphism. -/
theorem isHomeomorph_rightDiscs : IsHomeomorph (rightDiscs A) :=
  (rightDiscs A).toEquiv.isHomeomorph_iff.mpr
    ⟨(CompletedTensor.continuous_polydiscEquiv A 1 (1 + 1)).comp
      (CompletedTensor.continuous_congr ..),
      (CompletedTensor.continuous_congr_symm ..).comp
        (CompletedTensor.continuous_polydiscEquiv_symm A 1 (1 + 1))⟩

/-- *three_discs_associator_field*: both iterated completed tensor products of three closed
discs are `A⟨T, S, R⟩` by homeomorphic ring isomorphisms fixing the coefficients and sending the
three coordinates to `T, S, R` in this order, and under them the associator is the identity. -/
theorem three_discs_associator_field :
    ∃ (eL : CompletedTensor A (CompletedTensor A (D 1) (D 1)) (D 1) ≃+* D 3)
      (eR : CompletedTensor A (D 1) (CompletedTensor A (D 1) (D 1)) ≃+* D 3),
      IsHomeomorph eL ∧ IsHomeomorph eR ∧
      (∀ a : A, eL (algebraMap A _ a) = algebraMap A (D 3) a) ∧
      eL (CompletedTensor.inl A _ _ (CompletedTensor.inl A _ _ ((V 1) 0))) = (V 3) 0 ∧
      eL (CompletedTensor.inl A _ _ (CompletedTensor.inr A _ _ ((V 1) 0))) = (V 3) 1 ∧
      eL (CompletedTensor.inr A _ _ ((V 1) 0)) = (V 3) 2 ∧
      (∀ a : A, eR (algebraMap A _ a) = algebraMap A (D 3) a) ∧
      eR (CompletedTensor.inl A _ _ ((V 1) 0)) = (V 3) 0 ∧
      eR (CompletedTensor.inr A _ _ (CompletedTensor.inl A _ _ ((V 1) 0))) = (V 3) 1 ∧
      eR (CompletedTensor.inr A _ _ (CompletedTensor.inr A _ _ ((V 1) 0))) = (V 3) 2 ∧
      (eL.symm.trans (CompletedTensor.assoc A (D 1) (D 1) (D 1))).trans eR =
        RingEquiv.refl (D 3) := by
  refine ⟨leftDiscs A, rightDiscs A, isHomeomorph_leftDiscs A, isHomeomorph_rightDiscs A,
    leftDiscs_algebraMap A, leftDiscs_T A, leftDiscs_S A, leftDiscs_R A, rightDiscs_algebraMap A,
    rightDiscs_T A, rightDiscs_S A, rightDiscs_R A, ?_⟩
  -- Both sides are continuous and agree on constants and on the three coordinates.
  apply RingEquiv.toRingHom_injective
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous _ ?_ continuous_id
    (fun a ↦ ?_) fun i ↦ ?_
  · exact ((isHomeomorph_rightDiscs A).continuous.comp
      (CompletedTensor.continuous_assoc A _ _ _)).comp (continuous_leftDiscs_symm A)
  · change rightDiscs A (CompletedTensor.assoc A _ _ _ ((leftDiscs A).symm
      (algebraMap A (D 3) a))) = algebraMap A (D 3) a
    rw [show (leftDiscs A).symm (algebraMap A (D 3) a) = algebraMap A _ a by
        rw [RingEquiv.symm_apply_eq, leftDiscs_algebraMap],
      CompletedTensor.algebraMap_eq_inl, RingHom.comp_apply, CompletedTensor.algebraMap_eq_inl,
      RingHom.comp_apply, CompletedTensor.assoc_inl_inl, CompletedTensor.inl_algebraMap,
      rightDiscs_algebraMap]
  · change rightDiscs A (CompletedTensor.assoc A _ _ _ ((leftDiscs A).symm ((V 3) i))) =
      (V 3) i
    fin_cases i
    · rw [show (leftDiscs A).symm ((V 3) ⟨0, by decide⟩) = _ from
        (RingEquiv.symm_apply_eq _).mpr (leftDiscs_T A).symm, CompletedTensor.assoc_inl_inl,
        rightDiscs_T]
      rfl
    · rw [show (leftDiscs A).symm ((V 3) ⟨1, by decide⟩) = _ from
        (RingEquiv.symm_apply_eq _).mpr (leftDiscs_S A).symm, CompletedTensor.assoc_inl_inr,
        rightDiscs_S]
      rfl
    · rw [show (leftDiscs A).symm ((V 3) ⟨2, by decide⟩) = _ from
        (RingEquiv.symm_apply_eq _).mpr (leftDiscs_R A).symm, CompletedTensor.assoc_inr,
        rightDiscs_R]
      rfl

/-- Under `A⟨T⟩ ⊗̂_A A⟨T⟩ ≃ A⟨T, S⟩`, the symmetry of the completed tensor product. -/
noncomputable abbrev discSwap : (D 2) ≃+* (D 2) :=
  (CompletedTensor.polydiscEquiv A 1 1).symm.trans
    ((CompletedTensor.comm A (D 1) (D 1)).trans (CompletedTensor.polydiscEquiv A 1 1))

/-- The symmetry of `A⟨T, S⟩` is continuous. -/
theorem continuous_discSwap : Continuous (discSwap A) :=
  (CompletedTensor.continuous_polydiscEquiv A 1 1).comp
    ((CompletedTensor.continuous_comm A _ _).comp
      (CompletedTensor.continuous_polydiscEquiv_symm A 1 1))

/-- *symmetry_and_unit_on_charts*: the symmetry sends `T` to `S`. -/
theorem discSwap_zero : discSwap A ((V 2) 0) = (V 2) 1 := by
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
    show ((V 2) 0) = (V 2) (Fin.castAdd 1 0) from rfl,
    CompletedTensor.polydiscEquiv_symm_polydiscVar_castAdd, CompletedTensor.comm_inl,
    CompletedTensor.polydiscEquiv_inr_polydiscVar]
  rfl

/-- *symmetry_and_unit_on_charts*: the symmetry sends `S` to `T`. -/
theorem discSwap_one : discSwap A ((V 2) 1) = (V 2) 0 := by
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
    show ((V 2) 1) = (V 2) (Fin.natAdd 1 (0 : Fin 1)) from rfl,
    CompletedTensor.polydiscEquiv_symm_polydiscVar_natAdd, CompletedTensor.comm_inr,
    CompletedTensor.polydiscEquiv_inl_polydiscVar]
  rfl

/-- The symmetry fixes the coefficients. -/
theorem discSwap_algebraMap (a : A) : discSwap A (algebraMap A (D 2) a) = algebraMap A (D 2) a := by
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
    show algebraMap A (D 2) a = CompletedTensor.polydiscEquiv A 1 1 (algebraMap A _ a) from
      (CompletedTensor.polydiscEquiv_algebraMap A 1 1 a).symm,
    RingEquiv.symm_apply_apply, CompletedTensor.algebraMap_eq_inl, RingHom.comp_apply,
    CompletedTensor.comm_inl, ← RingHom.comp_apply, ← CompletedTensor.inl_comp_algebraMap,
    RingHom.comp_apply, CompletedTensor.inl_algebraMap,
    CompletedTensor.polydiscEquiv_algebraMap]

/-- *symmetry_and_unit_on_charts*: the symmetry is an involution. -/
theorem discSwap_trans_discSwap : (discSwap A).trans (discSwap A) = RingEquiv.refl (D 2) := by
  apply RingEquiv.toRingHom_injective
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous _
    ((continuous_discSwap A).comp (continuous_discSwap A)) continuous_id (fun a ↦ ?_) fun i ↦ ?_
  · change discSwap A (discSwap A (algebraMap A (D 2) a)) = algebraMap A (D 2) a
    rw [discSwap_algebraMap, discSwap_algebraMap]
  · change discSwap A (discSwap A ((V 2) i)) = (V 2) i
    fin_cases i
    · exact (congrArg (discSwap A) (discSwap_zero A)).trans (discSwap_one A)
    · exact (congrArg (discSwap A) (discSwap_one A)).trans (discSwap_zero A)

end Generic

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- *three_discs_associator*: the three-disc check over `ℚ_p`. -/
example :
    ∃ (eL : CompletedTensor ℚ_[p] (CompletedTensor ℚ_[p]
        (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) (restrictedMvPowerSeriesCompletion 1 ℚ_[p]))
        (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) ≃+* restrictedMvPowerSeriesCompletion 3 ℚ_[p])
      (eR : CompletedTensor ℚ_[p] (restrictedMvPowerSeriesCompletion 1 ℚ_[p])
        (CompletedTensor ℚ_[p] (restrictedMvPowerSeriesCompletion 1 ℚ_[p])
          (restrictedMvPowerSeriesCompletion 1 ℚ_[p])) ≃+*
        restrictedMvPowerSeriesCompletion 3 ℚ_[p]),
      IsHomeomorph eL ∧ IsHomeomorph eR ∧
      (∀ a : ℚ_[p], eL (algebraMap ℚ_[p] _ a) = algebraMap ℚ_[p] _ a) ∧
      eL (CompletedTensor.inl ℚ_[p] _ _
        (CompletedTensor.inl ℚ_[p] _ _ (Pair.polydiscVar 1 ℚ_[p] 0))) =
        Pair.polydiscVar 3 ℚ_[p] 0 ∧
      eL (CompletedTensor.inl ℚ_[p] _ _
        (CompletedTensor.inr ℚ_[p] _ _ (Pair.polydiscVar 1 ℚ_[p] 0))) =
        Pair.polydiscVar 3 ℚ_[p] 1 ∧
      eL (CompletedTensor.inr ℚ_[p] _ _ (Pair.polydiscVar 1 ℚ_[p] 0)) =
        Pair.polydiscVar 3 ℚ_[p] 2 ∧
      (∀ a : ℚ_[p], eR (algebraMap ℚ_[p] _ a) = algebraMap ℚ_[p] _ a) ∧
      eR (CompletedTensor.inl ℚ_[p] _ _ (Pair.polydiscVar 1 ℚ_[p] 0)) =
        Pair.polydiscVar 3 ℚ_[p] 0 ∧
      eR (CompletedTensor.inr ℚ_[p] _ _
        (CompletedTensor.inl ℚ_[p] _ _ (Pair.polydiscVar 1 ℚ_[p] 0))) =
        Pair.polydiscVar 3 ℚ_[p] 1 ∧
      eR (CompletedTensor.inr ℚ_[p] _ _
        (CompletedTensor.inr ℚ_[p] _ _ (Pair.polydiscVar 1 ℚ_[p] 0))) =
        Pair.polydiscVar 3 ℚ_[p] 2 ∧
      (eL.symm.trans (CompletedTensor.assoc ℚ_[p] _ _ _)).trans eR = RingEquiv.refl _ :=
  three_discs_associator_field ℚ_[p]

/-- Evaluation of `ℚ_p⟨T, S⟩` at a point `(x, y)` of the closed unit polydisc. -/
noncomputable def evalAt (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    restrictedMvPowerSeriesCompletion 2 ℚ_[p] →+* ℚ_[p] :=
  weightedEvalHomCompletion (φ := RingHom.id ℚ_[p]) (b := ![x, y]) isWeightFamily_one_weight
    continuous_id.continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun i ↦ by
      fin_cases i
      · exact IsPowerBounded.of_norm_le_one hx
      · exact IsPowerBounded.of_norm_le_one hy)

/-- Evaluation at `(x, y)` sends `T` to `x` and `S` to `y`. -/
theorem evalAt_polydiscVar (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : Fin 2) :
    evalAt p x y hx hy (Pair.polydiscVar 2 ℚ_[p] i) = ![x, y] i := by
  rw [evalAt, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- *symmetry_and_unit_on_charts*: over `ℚ_p` the symmetry moves the point `(T, S) = (0, 1)` to
the point `(1, 0)`, so it is not the identity. -/
example :
    ∃ (h0 : ‖(0 : ℚ_[p])‖ ≤ 1) (h1 : ‖(1 : ℚ_[p])‖ ≤ 1),
      (evalAt p 0 1 h0 h1).comp (discSwap ℚ_[p] : _ →+* _) = evalAt p 1 0 h1 h0 ∧
      discSwap ℚ_[p] ≠ RingEquiv.refl _ := by
  have h0 : ‖(0 : ℚ_[p])‖ ≤ 1 := by simp
  have h1 : ‖(1 : ℚ_[p])‖ ≤ 1 := by simp
  have hcomp : (evalAt p 0 1 h0 h1).comp (discSwap ℚ_[p] : _ →+* _) = evalAt p 1 0 h1 h0 := by
    refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous _
      ((continuous_weightedEvalHomCompletion _ _ _).comp (continuous_discSwap ℚ_[p]))
      (continuous_weightedEvalHomCompletion _ _ _) (fun a ↦ ?_) fun i ↦ ?_
    · change evalAt p 0 1 h0 h1 (discSwap ℚ_[p] (algebraMap ℚ_[p] _ a)) =
        evalAt p 1 0 h1 h0 (algebraMap ℚ_[p] _ a)
      rw [discSwap_algebraMap, algebraMap_completion_weightedRestrictedSubring_apply, evalAt,
        evalAt, weightedEvalHomCompletion_coe, weightedEvalHomCompletion_coe,
        weightedEvalHom_weightedC, weightedEvalHom_weightedC]
    · change evalAt p 0 1 h0 h1 (discSwap ℚ_[p] (Pair.polydiscVar 2 ℚ_[p] i)) =
        evalAt p 1 0 h1 h0 (Pair.polydiscVar 2 ℚ_[p] i)
      fin_cases i
      · rw [show Pair.polydiscVar 2 ℚ_[p] ⟨0, by decide⟩ = Pair.polydiscVar 2 ℚ_[p] 0 from rfl,
          discSwap_zero, evalAt_polydiscVar, evalAt_polydiscVar]
        rfl
      · rw [show Pair.polydiscVar 2 ℚ_[p] ⟨1, by decide⟩ = Pair.polydiscVar 2 ℚ_[p] 1 from rfl,
          discSwap_one, evalAt_polydiscVar, evalAt_polydiscVar]
        rfl
  refine ⟨h0, h1, hcomp, fun h ↦ ?_⟩
  have := RingHom.congr_fun hcomp (Pair.polydiscVar 2 ℚ_[p] 0)
  rw [RingHom.comp_apply, h, RingEquiv.coe_toRingHom, RingEquiv.refl_apply, evalAt_polydiscVar,
    evalAt_polydiscVar] at this
  simp at this

end Padic

end TauCeti.Examples.CompletedTensorPolydisc
