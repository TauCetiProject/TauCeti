/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Cohomology
public import TauCeti.Algebra.Homology.Contraction.Linear.TensorProduct

/-!
# Contractions of the unperturbed module bar complex

Fix an A-infinity algebra `A`. On `sM ⊗ Tᶜ(sA)`, retain the unary module differential
and the entire algebra bar differential, but omit higher module operations. This gives
the square-zero base differential `dM ⊗ 1 + ε(sM) ⊗ bA`.

A homogeneous special contraction of the underlying module complex extends to a special
contraction for these base bar differentials. Its inclusion, projection and homotopy
are obtained by tensoring with the identity. This is the initial contraction for
homological perturbation by the higher module operations; it is not yet the transferred
A-infinity module structure.

The signs and the perturbation convention follow Keller, *Introduction to A-infinity
algebras and modules*, Section 4, and Gugenheim--Lambe--Stasheff,
*Perturbation theory in differential homological algebra II*.
-/

public section

open scoped TensorProduct

namespace TauCeti.AInfinityRightModule

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (AA : AInfinityAlgebra R A)

/-- The base module bar differential, omitting higher module operations but retaining
all operations of the algebra. The parity operator uses the suspended module grading. -/
noncomputable def baseBarDifferential (G : InternalGrading R M) (d : Module.End R M) :
    Module.End R (M ⊗[R] TensorWords R A) :=
  TensorProduct.map d LinearMap.id +
    TensorProduct.map ((G.shift 1).koszulTwist 1) AA.coaugmentedBarDifferential

/-- The base differential is the sum of the module and signed algebra summands. -/
theorem baseBarDifferential_def (G : InternalGrading R M) (d : Module.End R M) :
    baseBarDifferential AA G d = TensorProduct.map d LinearMap.id +
      TensorProduct.map ((G.shift 1).koszulTwist 1) AA.coaugmentedBarDifferential := (rfl)

/-- The base differential on a pure tensor, with the suspension sign explicit. -/
@[simp]
theorem baseBarDifferential_tmul (G : InternalGrading R M) (d : Module.End R M)
    (x : M) (w : TensorWords R A) :
    baseBarDifferential AA G d (x ⊗ₜ[R] w) = d x ⊗ₜ[R] w +
      (G.shift 1).koszulTwist 1 x ⊗ₜ[R] AA.coaugmentedBarDifferential w := by
  simp [baseBarDifferential]

attribute [local instance] Comodule.cofree

/-- The base differential obeys the signed co-Leibniz law over the full algebra bar
differential, independently of the square-zero law for the module endomorphism. -/
theorem isGradedCoderivationOver_baseBarDifferential (G : InternalGrading R M)
    (d : Module.End R M) :
    Comodule.IsGradedCoderivationOver (barGrading AA G) 1 AA.coaugmentedBarDifferential
      (baseBarDifferential AA G d) := by
  let f := Comodule.Hom.cofreeMap (C := TensorWords R A) d
  let F := (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ f.toLinearMap
  have hf := congrArg Comodule.Hom.toLinearMap
    (Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp f)
  have hf' : F.rTensor (TensorWords R A) ∘ₗ
      (TensorProduct.assoc R M (TensorWords R A) (TensorWords R A)).symm.toLinearMap ∘ₗ
      (TensorWords.deconcatenation R A).lTensor M = d.rTensor (TensorWords R A) := by
    simpa only [F, f, Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact,
      TensorWords.comul_eq_deconcatenation, LinearMap.comp_assoc,
      Comodule.Hom.cofreeMap_toLinearMap] using hf
  have heq : gradedCoderiv AA G F = baseBarDifferential AA G d := by
    rw [gradedCoderiv_def, hf', LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_def,
      baseBarDifferential]
  rw [← heq]
  exact isGradedCoderivationOver_gradedCoderiv G F

/-- The base bar differential squares to zero for any square-zero degree-one module
endomorphism. No field or splitting hypothesis is needed. -/
theorem baseBarDifferential_sq (G : InternalGrading R M) (d : Module.End R M)
    (hd : LinearMap.IsHomogeneous d G.piece G.piece 1) (hsq : d ∘ₗ d = 0) :
    baseBarDifferential AA G d ∘ₗ baseBarDifferential AA G d = 0 := by
  have hd' : LinearMap.IsHomogeneous d (G.shift 1).piece (G.shift 1).piece 1 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hd
  apply TensorProduct.ext'
  intro x w
  have hx : d (d x) = 0 := LinearMap.congr_fun hsq x
  have hw : AA.coaugmentedBarDifferential (AA.coaugmentedBarDifferential w) = 0 :=
    LinearMap.congr_fun AA.coaugmentedBarDifferential_sq w
  have he := hd'.koszulTwist_apply 1 x
  simp only [one_mul, Int.negOnePow_one, Units.val_neg, Units.val_one,
    Int.cast_neg, Int.cast_one, neg_one_smul] at he
  simp only [LinearMap.comp_apply, baseBarDifferential_tmul, map_add,
    LinearMap.zero_apply, hx, hw, he, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    add_zero, zero_add, TensorProduct.neg_tmul]
  simp

/-- The base bar differential has degree one in the total suspended grading. -/
theorem isHomogeneous_baseBarDifferential (G : InternalGrading R M) (d : Module.End R M)
    (hd : LinearMap.IsHomogeneous d G.piece G.piece 1) :
    LinearMap.IsHomogeneous (baseBarDifferential AA G d)
      (barGrading AA G).piece (barGrading AA G).piece 1 := by
  have hd' : LinearMap.IsHomogeneous d (G.shift 1).piece (G.shift 1).piece 1 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hd
  have he : LinearMap.IsHomogeneous ((G.shift 1).koszulTwist 1)
      (G.shift 1).piece (G.shift 1).piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa using (G.shift 1).koszulTwist_mem_piece hx 1
  have hb : LinearMap.IsHomogeneous AA.coaugmentedBarDifferential
      (TensorWords.grading (AA.grading.shift 1)).piece
      (TensorWords.grading (AA.grading.shift 1)).piece 1 := by
    simpa only [TensorWords.grading_piece] using AA.isHomogeneous_coaugmentedBarDifferential
  have hG : barGrading AA G =
      (G.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1)) := by
    ext p
    rw [barGrading_piece]
  rw [hG]
  simpa only [baseBarDifferential, add_zero, zero_add] using
    (hd'.tensorProduct (LinearMap.isHomogeneous_id (R := R)
      (TensorWords.grading (AA.grading.shift 1)).piece)).add (he.tensorProduct hb)

variable {AA} (MM : AInfinityRightModule AA M) {G : InternalGrading R N}
  {dN : Module.End R N} (c : LinearSpecialContraction MM.differential dN)
  (hh : LinearMap.IsHomogeneous c.homotopy MM.grading.piece MM.grading.piece (-1))
  (hi : LinearMap.IsHomogeneous c.incl G.piece MM.grading.piece 0)
  (hp : LinearMap.IsHomogeneous c.proj MM.grading.piece G.piece 0)

/-- A special contraction of the module complex, extended over the fixed algebra bar
coalgebra. These are the unperturbed differentials, not the full module bar differentials. -/
noncomputable def barContraction :
    LinearSpecialContraction
      (baseBarDifferential AA MM.grading MM.differential) (baseBarDifferential AA G dN) :=
  c.tensorRight (MM.grading.shift 1) (G.shift 1) AA.coaugmentedBarDifferential
    (LinearMap.isHomogeneous_shift_piece_iff.2 hh)
    (LinearMap.isHomogeneous_shift_piece_iff.2 hi)
    (LinearMap.isHomogeneous_shift_piece_iff.2 hp)

@[simp]
theorem barContraction_incl :
    (MM.barContraction c hh hi hp).incl = c.incl.rTensor (TensorWords R A) := by
  simp [barContraction]

@[simp]
theorem barContraction_proj :
    (MM.barContraction c hh hi hp).proj = c.proj.rTensor (TensorWords R A) := by
  simp [barContraction]

@[simp]
theorem barContraction_homotopy :
    (MM.barContraction c hh hi hp).homotopy = c.homotopy.rTensor (TensorWords R A) := by
  simp [barContraction]

/-- The source differential of the extended contraction is square-zero. -/
theorem barContraction_source_sq :
    baseBarDifferential AA MM.grading MM.differential ∘ₗ
      baseBarDifferential AA MM.grading MM.differential = 0 :=
  baseBarDifferential_sq AA MM.grading MM.differential MM.isHomogeneous_differential
    MM.differential_comp_self_eq_zero

include c hh hi hp in
/-- The target differential of the extended contraction is square-zero, even if the
caller did not separately supply a square-zero law for the retract. -/
theorem barContraction_target_sq :
    baseBarDifferential AA G dN ∘ₗ baseBarDifferential AA G dN = 0 :=
  (MM.barContraction c hh hi hp).toLinearContraction.dN_comp_dN_eq_zero
    MM.barContraction_source_sq

end TauCeti.AInfinityRightModule
