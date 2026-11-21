/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.LightProfinite.Sequence
public import Mathlib.Topology.Connected.Separation

/-!
# A universe-lifted convergent sequence

The finite points and limit point describe the lifted one-point compactification without
exposing its carrier presentation. Successor fixes the limit point.
-/

public section

universe u

open CategoryTheory OnePoint Filter

namespace TauCeti

/-- The convergent sequence, with carrier lifted to the universe of the light profinite site. -/
noncomputable def liftedSequence : LightProfinite.{u} :=
  let e : ULift.{u} (OnePoint ℕ) ≃ₜ OnePoint ℕ := Homeomorph.ulift
  haveI := e.secondCountableTopology
  haveI := e.symm.totallyDisconnectedSpace
  LightProfinite.of (ULift.{u} (OnePoint ℕ))

/-- The underlying one-point compactification of the lifted sequence. -/
noncomputable def liftedSequenceEquiv : liftedSequence.{u} ≃ₜ OnePoint ℕ := Homeomorph.ulift

/-- The finite point of the convergent sequence indexed by `n`. -/
noncomputable def sequencePoint (n : ℕ) : liftedSequence.{u} := ULift.up (n : OnePoint ℕ)

/-- The limit point of the convergent sequence. -/
noncomputable def sequenceInfty : liftedSequence.{u} := ULift.up ∞

@[simp]
lemma liftedSequenceEquiv_apply_point (n : ℕ) :
    liftedSequenceEquiv (sequencePoint.{u} n) = n := by rfl

@[simp]
lemma liftedSequenceEquiv_apply_infty :
    liftedSequenceEquiv sequenceInfty.{u} = ∞ := by rfl

@[simp]
lemma liftedSequenceEquiv_symm_apply_coe (n : ℕ) :
    liftedSequenceEquiv.symm (n : OnePoint ℕ) = sequencePoint.{u} n := by rfl

@[simp]
lemma liftedSequenceEquiv_symm_apply_infty :
    liftedSequenceEquiv.symm ∞ = sequenceInfty.{u} := by rfl

/-- Every point of the sequence is finite or its limit point. -/
lemma liftedSequence_cases {P : liftedSequence.{u} → Prop}
    (hpoint : ∀ n, P (sequencePoint n)) (hinfty : P sequenceInfty) (x) : P x := by
  obtain ⟨x⟩ := x
  induction x using OnePoint.rec with
  | infty => exact hinfty
  | coe n => exact hpoint n

/-- The lifted sequence is also the one-point compactification of the lifted natural numbers. -/
noncomputable def liftedSequenceHomeomorph : liftedSequence.{u} ≃ₜ OnePoint (ULift.{u} ℕ) :=
  liftedSequenceEquiv.trans
    ((Homeomorph.ulift : ULift.{u} ℕ ≃ₜ ℕ).symm.onePointCongr)

@[simp↓]
lemma liftedSequenceHomeomorph_apply_coe (n : ℕ) :
    liftedSequenceHomeomorph (sequencePoint.{u} n) =
      (ULift.up n : ULift.{u} ℕ) := by rfl

@[simp↓]
lemma liftedSequenceHomeomorph_apply_infty :
    liftedSequenceHomeomorph sequenceInfty.{u} = ∞ := by rfl

/-- Successor on the finite terms of the lifted sequence, fixing infinity. -/
noncomputable def natShift : liftedSequence.{u} ⟶ liftedSequence.{u} :=
  ConcreteCategory.ofHom ⟨ULift.map (OnePoint.map Nat.succ), continuous_uliftMap _ (by
    rw [OnePoint.continuous_iff_from_nat]
    have h :=
      (OnePoint.continuous_iff_from_nat (id : OnePoint ℕ → OnePoint ℕ)).mp continuous_id
    simpa [Function.comp_def] using h.comp (tendsto_add_atTop_nat 1))⟩

@[simp↓]
lemma natShift_apply_coe (n : ℕ) :
    natShift (sequencePoint.{u} n) =
      sequencePoint (n + 1) := by rfl

@[simp↓]
lemma natShift_apply_infty :
    natShift sequenceInfty.{u} = sequenceInfty := by rfl

/-- The inclusion of the point at infinity in the lifted sequence. -/
noncomputable def inftyPoint : LightProfinite.of PUnit.{u + 1} ⟶ liftedSequence.{u} :=
  CompHausLike.const _ sequenceInfty

@[simp↓]
lemma inftyPoint_apply (x : LightProfinite.of PUnit.{u + 1}) :
    inftyPoint x = sequenceInfty.{u} := by rfl

@[reassoc (attr := simp)]
lemma inftyPoint_comp_natShift : inftyPoint.{u} ≫ natShift = inftyPoint := by
  ext x
  rfl

end TauCeti
