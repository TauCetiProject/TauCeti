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

Over a Huber ring `A`, both iterated completed tensor products of three closed discs `A⟨T⟩`,
`A⟨S⟩`, `A⟨R⟩` are identified with `A⟨T, S, R⟩`, coefficients and the three coordinates being
pinned in the order `T, S, R`. Under these identifications the associator is the identity of
`A⟨T, S, R⟩`; this holds for every Huber ring, so in particular for every complete
nonarchimedean field, and is spelled out over `ℚ_p`. Under `A⟨T⟩ ⊗̂_A A⟨T⟩ ≃ A⟨T, S⟩` the symmetry
of the completed tensor product is the automorphism `T ↔ S`, an involution, and over `ℚ_p` it is
not the identity: it moves evaluation at `(T, S) = (0, 1)` to evaluation at `(1, 0)`. Only the
symmetry on the disc chart is checked here; the unit is not.
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

/-- The identification `(A⟨T⟩ ⊗̂_A A⟨S⟩) ⊗̂_A A⟨R⟩ ≃ A⟨T, S, R⟩`. -/
noncomputable def leftDiscs :
    CompletedTensor A (CompletedTensor A (D 1) (D 1)) (D 1) ≃+* D 3 :=
  (CompletedTensor.congr (A := A) (CompletedTensor.polydiscEquiv A 1 1) (RingEquiv.refl (D 1))
    (CompletedTensor.polydiscEquiv_comp_algebraMap A 1 1)
    (by rw [RingEquiv.toRingHom_refl, RingHom.id_comp])
    (CompletedTensor.continuous_polydiscEquiv A 1 1)
    (CompletedTensor.continuous_polydiscEquiv_symm A 1 1)
    (by rw [RingEquiv.coe_refl]; exact continuous_id)
    (by rw [RingEquiv.symm_refl, RingEquiv.coe_refl]; exact continuous_id)).trans
    (CompletedTensor.polydiscEquiv A (1 + 1) 1)

/-- The identification `A⟨T⟩ ⊗̂_A (A⟨S⟩ ⊗̂_A A⟨R⟩) ≃ A⟨T, S, R⟩`. -/
noncomputable def rightDiscs :
    CompletedTensor A (D 1) (CompletedTensor A (D 1) (D 1)) ≃+* D 3 :=
  (CompletedTensor.congr (A := A) (RingEquiv.refl (D 1)) (CompletedTensor.polydiscEquiv A 1 1)
    (by rw [RingEquiv.toRingHom_refl, RingHom.id_comp])
    (CompletedTensor.polydiscEquiv_comp_algebraMap A 1 1)
    (by rw [RingEquiv.coe_refl]; exact continuous_id)
    (by rw [RingEquiv.symm_refl, RingEquiv.coe_refl]; exact continuous_id)
    (CompletedTensor.continuous_polydiscEquiv A 1 1)
    (CompletedTensor.continuous_polydiscEquiv_symm A 1 1)).trans
    (CompletedTensor.polydiscEquiv A 1 (1 + 1))

/-! In the next lemmas the last step is a `polydiscEquiv` lemma for `A⟨T₁, …, T_{1+1+1}⟩`,
applied to a goal about `A⟨T₁, T₂, T₃⟩`: the ranks `1 + 1 + 1` and `3` agree by evaluation, and
so do the indices, e.g. `Fin.castAdd 1 (Fin.castAdd 1 0)` and `0 : Fin 3`. -/

/-- `leftDiscs` fixes the coefficients. -/
theorem leftDiscs_algebraMap (a : A) :
    leftDiscs A (algebraMap A _ a) = algebraMap A (D 3) a := by
  rw [leftDiscs, RingEquiv.trans_apply, ← CompletedTensor.inl_algebraMap,
    CompletedTensor.congr_inl, CompletedTensor.polydiscEquiv_algebraMap,
    CompletedTensor.inl_algebraMap]
  exact CompletedTensor.polydiscEquiv_algebraMap A (1 + 1) 1 a

/-- `rightDiscs` fixes the coefficients. -/
theorem rightDiscs_algebraMap (a : A) :
    rightDiscs A (algebraMap A _ a) = algebraMap A (D 3) a := by
  rw [rightDiscs, RingEquiv.trans_apply, ← CompletedTensor.inl_algebraMap,
    CompletedTensor.congr_inl, RingEquiv.refl_apply, CompletedTensor.inl_algebraMap]
  exact CompletedTensor.polydiscEquiv_algebraMap A 1 (1 + 1) a

/-- `leftDiscs` sends `T` to the first coordinate. -/
theorem leftDiscs_inl_inl_polydiscVar :
    leftDiscs A (CompletedTensor.inl A _ _ (CompletedTensor.inl A _ _ ((V 1) 0))) = (V 3) 0 := by
  rw [leftDiscs, RingEquiv.trans_apply, CompletedTensor.congr_inl,
    CompletedTensor.polydiscEquiv_inl_polydiscVar]
  exact CompletedTensor.polydiscEquiv_inl_polydiscVar A (1 + 1) 1 _

/-- `leftDiscs` sends `S` to the second coordinate. -/
theorem leftDiscs_inl_inr_polydiscVar :
    leftDiscs A (CompletedTensor.inl A _ _ (CompletedTensor.inr A _ _ ((V 1) 0))) = (V 3) 1 := by
  rw [leftDiscs, RingEquiv.trans_apply, CompletedTensor.congr_inl,
    CompletedTensor.polydiscEquiv_inr_polydiscVar]
  exact CompletedTensor.polydiscEquiv_inl_polydiscVar A (1 + 1) 1 _

/-- `leftDiscs` sends `R` to the third coordinate. -/
theorem leftDiscs_inr_polydiscVar :
    leftDiscs A (CompletedTensor.inr A _ _ ((V 1) 0)) = (V 3) 2 := by
  rw [leftDiscs, RingEquiv.trans_apply, CompletedTensor.congr_inr, RingEquiv.refl_apply]
  exact CompletedTensor.polydiscEquiv_inr_polydiscVar A (1 + 1) 1 _

/-- `rightDiscs` sends `T` to the first coordinate. -/
theorem rightDiscs_inl_polydiscVar :
    rightDiscs A (CompletedTensor.inl A _ _ ((V 1) 0)) = (V 3) 0 := by
  rw [rightDiscs, RingEquiv.trans_apply, CompletedTensor.congr_inl, RingEquiv.refl_apply]
  exact CompletedTensor.polydiscEquiv_inl_polydiscVar A 1 (1 + 1) _

/-- `rightDiscs` sends `S` to the second coordinate. -/
theorem rightDiscs_inr_inl_polydiscVar :
    rightDiscs A (CompletedTensor.inr A _ _ (CompletedTensor.inl A _ _ ((V 1) 0))) = (V 3) 1 := by
  rw [rightDiscs, RingEquiv.trans_apply, CompletedTensor.congr_inr,
    CompletedTensor.polydiscEquiv_inl_polydiscVar]
  exact CompletedTensor.polydiscEquiv_inr_polydiscVar A 1 (1 + 1) _

/-- `rightDiscs` sends `R` to the third coordinate. -/
theorem rightDiscs_inr_inr_polydiscVar :
    rightDiscs A (CompletedTensor.inr A _ _ (CompletedTensor.inr A _ _ ((V 1) 0))) = (V 3) 2 := by
  rw [rightDiscs, RingEquiv.trans_apply, CompletedTensor.congr_inr,
    CompletedTensor.polydiscEquiv_inr_polydiscVar]
  exact CompletedTensor.polydiscEquiv_inr_polydiscVar A 1 (1 + 1) _

/-- `leftDiscs` is a homeomorphism. -/
theorem isHomeomorph_leftDiscs : IsHomeomorph (leftDiscs A) :=
  (CompletedTensor.isHomeomorph_polydiscEquiv A (1 + 1) 1).comp
    (CompletedTensor.isHomeomorph_congr ..)

/-- `rightDiscs` is a homeomorphism. -/
theorem isHomeomorph_rightDiscs : IsHomeomorph (rightDiscs A) :=
  (CompletedTensor.isHomeomorph_polydiscEquiv A 1 (1 + 1)).comp
    (CompletedTensor.isHomeomorph_congr ..)

/-- Both iterated completed tensor products of three closed discs are `A⟨T, S, R⟩` by
homeomorphic ring isomorphisms fixing the coefficients and sending the three coordinates to
`T, S, R` in this order, and under them the associator is the identity. -/
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
    leftDiscs_algebraMap A, leftDiscs_inl_inl_polydiscVar A, leftDiscs_inl_inr_polydiscVar A,
    leftDiscs_inr_polydiscVar A, rightDiscs_algebraMap A, rightDiscs_inl_polydiscVar A,
    rightDiscs_inr_inl_polydiscVar A, rightDiscs_inr_inr_polydiscVar A, ?_⟩
  -- Both sides are continuous and agree on constants and on the three coordinates.
  have hL {x y} (h : leftDiscs A y = x) : (leftDiscs A).symm x = y :=
    (RingEquiv.symm_apply_eq _).mpr h.symm
  apply RingEquiv.toRingHom_injective
  refine restrictedMvPowerSeriesCompletion_ringHom_ext ?_ continuous_id (fun a ↦ ?_) fun i ↦ ?_
  · exact ((isHomeomorph_rightDiscs A).continuous.comp
      (CompletedTensor.continuous_assoc A _ _ _)).comp
      ((CompletedTensor.continuous_congr_symm ..).comp
        (CompletedTensor.continuous_polydiscEquiv_symm A (1 + 1) 1))
  all_goals simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.trans_apply, RingEquiv.refl_apply]
  · rw [hL (leftDiscs_algebraMap A a), CompletedTensor.assoc_algebraMap, rightDiscs_algebraMap]
  · fin_cases i
    · rw [Fin.zero_eta, hL (leftDiscs_inl_inl_polydiscVar A), CompletedTensor.assoc_inl_inl,
        rightDiscs_inl_polydiscVar]
    · rw [Fin.mk_one, hL (leftDiscs_inl_inr_polydiscVar A), CompletedTensor.assoc_inl_inr,
        rightDiscs_inr_inl_polydiscVar]
    · simp only [Fin.reduceFinMk]
      rw [hL (leftDiscs_inr_polydiscVar A), CompletedTensor.assoc_inr,
        rightDiscs_inr_inr_polydiscVar]

/-- Under `A⟨T⟩ ⊗̂_A A⟨T⟩ ≃ A⟨T, S⟩`, the symmetry of the completed tensor product. -/
noncomputable def discSwap : (D 2) ≃+* (D 2) :=
  (CompletedTensor.polydiscEquiv A 1 1).symm.trans
    ((CompletedTensor.comm A (D 1) (D 1)).trans (CompletedTensor.polydiscEquiv A 1 1))

/-- The symmetry of `A⟨T, S⟩` is continuous. -/
theorem continuous_discSwap : Continuous (discSwap A) :=
  (CompletedTensor.continuous_polydiscEquiv A 1 1).comp
    ((CompletedTensor.continuous_comm A _ _).comp
      (CompletedTensor.continuous_polydiscEquiv_symm A 1 1))

/-- The symmetry sends `T` to `S`. -/
theorem discSwap_polydiscVar_zero : discSwap A ((V 2) 0) = (V 2) 1 := by
  have h0 : (Fin.castAdd 1 0 : Fin 2) = 0 := by simp
  have h1 : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := by simp
  rw [discSwap, RingEquiv.trans_apply, RingEquiv.trans_apply, ← h0, ← h1,
    CompletedTensor.polydiscEquiv_symm_polydiscVar_castAdd, CompletedTensor.comm_inl,
    CompletedTensor.polydiscEquiv_inr_polydiscVar]

/-- The symmetry sends `S` to `T`. -/
theorem discSwap_polydiscVar_one : discSwap A ((V 2) 1) = (V 2) 0 := by
  have h0 : (Fin.castAdd 1 0 : Fin 2) = 0 := by simp
  have h1 : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := by simp
  rw [discSwap, RingEquiv.trans_apply, RingEquiv.trans_apply, ← h0, ← h1,
    CompletedTensor.polydiscEquiv_symm_polydiscVar_natAdd, CompletedTensor.comm_inr,
    CompletedTensor.polydiscEquiv_inl_polydiscVar]

/-- The symmetry fixes the coefficients. -/
theorem discSwap_algebraMap (a : A) : discSwap A (algebraMap A (D 2) a) = algebraMap A (D 2) a := by
  rw [discSwap, RingEquiv.trans_apply, RingEquiv.trans_apply,
    CompletedTensor.polydiscEquiv_symm_algebraMap, CompletedTensor.comm_algebraMap,
    CompletedTensor.polydiscEquiv_algebraMap]

/-- The symmetry is an involution. -/
theorem discSwap_trans_discSwap : (discSwap A).trans (discSwap A) = RingEquiv.refl (D 2) := by
  apply RingEquiv.toRingHom_injective
  refine restrictedMvPowerSeriesCompletion_ringHom_ext
    ((continuous_discSwap A).comp (continuous_discSwap A)) continuous_id (fun a ↦ ?_) fun i ↦ ?_
  all_goals simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.trans_apply, RingEquiv.refl_apply]
  · rw [discSwap_algebraMap, discSwap_algebraMap]
  · fin_cases i
    · rw [Fin.zero_eta, discSwap_polydiscVar_zero, discSwap_polydiscVar_one]
    · rw [Fin.mk_one, discSwap_polydiscVar_one, discSwap_polydiscVar_zero]

end Generic

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The three-disc check over `ℚ_p`. -/
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

/-- Evaluation at `(x, y)` fixes the coefficients. -/
theorem evalAt_algebraMap (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (a : ℚ_[p]) :
    evalAt p x y hx hy (algebraMap ℚ_[p] (restrictedMvPowerSeriesCompletion 2 ℚ_[p]) a) = a := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, evalAt, weightedEvalHomCompletion_coe,
    weightedEvalHom_weightedC, RingHom.id_apply]

/-- Evaluation at `(x, y)` sends `T` to `x` and `S` to `y`. -/
theorem evalAt_polydiscVar (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : Fin 2) :
    evalAt p x y hx hy (Pair.polydiscVar 2 ℚ_[p] i) = ![x, y] i := by
  rw [evalAt, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- Over `ℚ_p` the symmetry moves the point `(T, S) = (0, 1)` to the point `(1, 0)`, so it is not
the identity. -/
example :
    ∃ (h0 : ‖(0 : ℚ_[p])‖ ≤ 1) (h1 : ‖(1 : ℚ_[p])‖ ≤ 1),
      (evalAt p 0 1 h0 h1).comp (discSwap ℚ_[p] : _ →+* _) = evalAt p 1 0 h1 h0 ∧
      discSwap ℚ_[p] ≠ RingEquiv.refl _ := by
  have h0 : ‖(0 : ℚ_[p])‖ ≤ 1 := by simp
  have h1 : ‖(1 : ℚ_[p])‖ ≤ 1 := by simp
  have hcomp : (evalAt p 0 1 h0 h1).comp (discSwap ℚ_[p] : _ →+* _) = evalAt p 1 0 h1 h0 := by
    refine restrictedMvPowerSeriesCompletion_ringHom_ext
      ((continuous_weightedEvalHomCompletion _ _ _).comp (continuous_discSwap ℚ_[p]))
      (continuous_weightedEvalHomCompletion _ _ _) (fun a ↦ ?_) fun i ↦ ?_
    · rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, discSwap_algebraMap, evalAt_algebraMap,
        evalAt_algebraMap]
    · rw [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      fin_cases i
      · simp [discSwap_polydiscVar_zero, evalAt_polydiscVar]
      · simp [discSwap_polydiscVar_one, evalAt_polydiscVar]
  refine ⟨h0, h1, hcomp, fun h ↦ ?_⟩
  have := RingHom.congr_fun hcomp (Pair.polydiscVar 2 ℚ_[p] 0)
  rw [RingHom.comp_apply, h, RingEquiv.coe_toRingHom, RingEquiv.refl_apply, evalAt_polydiscVar,
    evalAt_polydiscVar] at this
  simp at this

end Padic

end TauCeti.Examples.CompletedTensorPolydisc
