/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Cohomology

/-!
# Homotopies of A-infinity bimodule morphisms

A homotopy between morphisms over fixed algebras is a degree-minus-one map `H` of their
bar bicomodules with `F - G = b_N H + H b_M`. The right coaction commutes with `H`;
the left coaction commutes with it with the Koszul twist on the left coalgebra factor.
Omitting this twist would incorrectly require odd maps to commute with left inputs.

Homotopies are determined by their two-counit Taylor maps. Their unary components are
chain homotopies, so homotopic bimodule morphisms induce the same map on cohomology.
We provide reversal, concatenation, and composition with bimodule morphisms on both sides.
These are the homotopies used in two-sided bar constructions and bimodule comparisons.

The conventions follow V. Lyubashenko and O. Manzyuk,
*A-infinity-bimodules and Serre A-infinity-functors*, and Getzler--Jones,
*A-infinity algebras and the cyclic bar complex*, Sections 1--2. The interface parallels
`AInfinityRightModuleHom.Homotopy`, with the additional signed left coaction.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.AInfinityBimoduleHom

universe uR uA uB uL uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {L : Type uL} {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {LL : AInfinityBimodule AA BB L} {MM : AInfinityBimodule AA BB M}
  {NN : AInfinityBimodule AA BB N} {PP : AInfinityBimodule AA BB P}

attribute [local instance] Comodule.cofree

open AInfinityBimodule

/-- A homotopy of bimodule morphisms is a degree-minus-one bar bicomodule map whose
commutator with the differentials is the difference of the morphisms. -/
structure Homotopy (f g : AInfinityBimoduleHom MM NN) where
  /-- The underlying right-comodule map. -/
  barHomotopy : Comodule.Hom R (TensorWords R B)
    ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
    ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B)
  /-- Passing the left coalgebra factor contributes its Koszul sign. -/
  leftCoact_comp_barMap :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ barHomotopy.toLinearMap =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist (-1))
        barHomotopy.toLinearMap ∘ₗ Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M)
  /-- The homotopy lowers total suspended degree by one. -/
  isHomogeneous_barHomotopy : LinearMap.IsHomogeneous barHomotopy.toLinearMap
    (barGrading AA BB MM.grading).piece (barGrading AA BB NN.grading).piece (-1)
  /-- The chain homotopy equation on bar bicomodules. -/
  barMap_sub_barMap : f.barMap - g.barMap =
    NN.barDifferential ∘ₗ barHomotopy.toLinearMap +
      barHomotopy.toLinearMap ∘ₗ MM.barDifferential

namespace Homotopy

variable {f g k : AInfinityBimoduleHom MM NN}

/-- The linear map of a bar homotopy. -/
abbrev barMap (h : Homotopy f g) := h.barHomotopy.toLinearMap

/-- The two-counit component of a bar homotopy. -/
def taylor (h : Homotopy f g) :
    (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N :=
  taylorProj R A B N ∘ₗ h.barMap

/-- The Taylor map is obtained by forgetting both output words. -/
theorem taylor_def (h : Homotopy f g) :
    h.taylor = taylorProj R A B N ∘ₗ h.barMap := (rfl)

/-- The signed left coaction and right cofreeness recover the entire bar homotopy. -/
theorem barMap_eq_cofreeLift (h : Homotopy f g) :
    h.barMap = (Comodule.Hom.cofreeLift
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist (-1))
        h.taylor ∘ₗ Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M))).toLinearMap := by
  have e := h.barHomotopy.eq_cofreeLift_of_leftCoact _ h.leftCoact_comp_barMap
  simpa only [taylor_def, taylorProj_def, LinearMap.comp_assoc] using
    congrArg Comodule.Hom.toLinearMap e

/-- Homotopies between fixed morphisms are determined by their Taylor maps. -/
@[ext]
theorem ext {h h' : Homotopy f g} (e : h.taylor = h'.taylor) : h = h' := by
  have he : h.barHomotopy = h'.barHomotopy := by
    apply Comodule.Hom.toLinearMap_injective
    calc
      _ = _ := h.barMap_eq_cofreeLift
      _ = _ := by rw [e]
      _ = _ := h'.barMap_eq_cofreeLift.symm
  cases h
  cases h'
  cases he
  rfl

/-- The Taylor map lowers suspended degree by one. -/
theorem isHomogeneous_taylor (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.taylor (barGrading AA BB MM.grading).piece
      (NN.grading.shift 1).piece (-1) := by
  have hbar := h.isHomogeneous_barHomotopy
  simp only [barGrading_def] at hbar ⊢
  rw [taylor_def, taylorProj_def, Comodule.leftCofreeCounit_def]
  simpa only [LinearMap.comp_assoc, add_zero] using
    ((TensorWords.isHomogeneous_lid_comp_rTensor_counit (AA.grading.shift 1)
      (NN.grading.shift 1)).comp (TensorWords.isHomogeneous_rid_comp_lTensor_counit
        ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (NN.grading.shift 1))
        (BB.grading.shift 1))).comp hbar

/-- The homotopy equation projected to the two cogenerators. -/
theorem taylor_sub_taylor (h : Homotopy f g) :
    f.taylor - g.taylor = NN.taylor ∘ₗ h.barMap + h.taylor ∘ₗ MM.barDifferential := by
  have e := congrArg (fun F ↦ taylorProj R A B N ∘ₗ F) h.barMap_sub_barMap
  simpa only [LinearMap.comp_sub, LinearMap.comp_add, LinearMap.comp_assoc,
    AInfinityBimoduleHom.taylor_def, AInfinityBimodule.taylor_def, taylor_def] using e

/-- The unary component of the homotopy, with both algebra words empty. -/
def linearHomotopy (h : Homotopy f g) : M →ₗ[R] N :=
  h.taylor ∘ₗ (TensorProduct.mk R (TensorWords R A ⊗[R] M) (TensorWords R B)).flip 1 ∘ₗ
    TensorProduct.mk R (TensorWords R A) M 1

@[simp]
theorem linearHomotopy_apply (h : Homotopy f g) (x : M) :
    h.linearHomotopy x = h.taylor ((1 ⊗ₜ x) ⊗ₜ 1) := (rfl)

/-- Empty input words remain empty under a bar homotopy. -/
@[simp]
theorem barMap_one_tmul_tmul_one (h : Homotopy f g) (x : M) :
    h.barMap ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ h.linearHomotopy x) ⊗ₜ 1 := by
  rw [h.barMap_eq_cofreeLift, Comodule.Hom.cofreeLift_toLinearMap]
  simp [Comodule.leftCoactRTensor_def, Comodule.leftCofreeCoact_def,
    TensorWords.comul_eq_deconcatenation, TensorWords.deconcatenation_one]

/-- The unary component lowers the unsuspended degree by one. -/
theorem linearHomotopy_mem_piece (h : Homotopy f g) {p : ℤ} {x : M}
    (hx : x ∈ MM.grading.piece p) : h.linearHomotopy x ∈ NN.grading.piece (p - 1) := by
  have hx' : x ∈ (MM.grading.shift 1).piece (p - 1) := by
    simpa only [InternalGrading.shift_piece, sub_add_cancel] using hx
  have hz := tmul_of_tprod_mem_barGrading AA BB MM.grading 0 0
    (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0) hx'
    (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
  have hh := h.isHomogeneous_taylor.map_mem hz
  simpa [InternalGrading.shift_piece, sub_eq_add_neg, TensorWords.one_eq_of_zero] using hh

/-- The unary component is an ordinary chain homotopy between the linear parts. -/
theorem linearPart_sub_linearPart (h : Homotopy f g) (x : M) :
    f.linearPart x - g.linearPart x =
      NN.differential (h.linearHomotopy x) + h.linearHomotopy (MM.differential x) := by
  have e := LinearMap.congr_fun h.taylor_sub_taylor ((1 ⊗ₜ x) ⊗ₜ 1)
  simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    ← linearPart_apply, barMap_one_tmul_tmul_one, linearHomotopy_apply,
    AInfinityBimodule.barDifferential_one_tmul_tmul_one,
    ← AInfinityBimodule.differential_apply] using e

/-- Homotopic bimodule morphisms induce the same map on unary cohomology. -/
theorem cohomologyMap_eq (h : Homotopy f g) : f.cohomologyMap = g.cohomologyMap := by
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective MM.differential.boundariesInKer c
  rw [Submodule.mkQ_apply, cohomologyMap_mk, cohomologyMap_mk, Submodule.Quotient.eq]
  exact ⟨h.linearHomotopy x, by
    simpa only [Submodule.subtype_apply, Submodule.coe_sub, LinearMap.mem_ker.mp x.2,
      map_zero, add_zero] using (h.linearPart_sub_linearPart x).symm⟩

/-- Homotopic bimodule morphisms are quasi-isomorphisms together. -/
theorem isQuasiIso_iff (h : Homotopy f g) : f.IsQuasiIso ↔ g.IsQuasiIso := by
  rw [isQuasiIso_def, isQuasiIso_def, h.cohomologyMap_eq]

/-- The zero homotopy from a bimodule morphism to itself. -/
def refl (f : AInfinityBimoduleHom MM NN) : Homotopy f f where
  barHomotopy := 0
  leftCoact_comp_barMap := by simp
  isHomogeneous_barHomotopy := LinearMap.isHomogeneous_zero _ _ _
  barMap_sub_barMap := by simp

@[simp]
theorem barMap_refl (f : AInfinityBimoduleHom MM NN) : (refl f).barMap = 0 := (rfl)

@[simp]
theorem taylor_refl (f : AInfinityBimoduleHom MM NN) : (refl f).taylor = 0 := by
  simp only [taylor_def, barMap_refl, LinearMap.comp_zero]

/-- Reverse a bimodule homotopy. -/
def symm (h : Homotopy f g) : Homotopy g f where
  barHomotopy := (-1 : R) • h.barHomotopy
  leftCoact_comp_barMap := by
    simp only [Comodule.Hom.smul_toLinearMap, LinearMap.comp_smul,
      TensorProduct.map_smul_right, LinearMap.smul_comp, h.leftCoact_comp_barMap]
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.smul_toLinearMap]
    exact h.isHomogeneous_barHomotopy.smul (-1 : R)
  barMap_sub_barMap := by
    rw [Comodule.Hom.smul_toLinearMap, LinearMap.comp_smul, LinearMap.smul_comp,
      ← smul_add, ← h.barMap_sub_barMap, neg_one_smul]
    module

@[simp]
theorem barMap_symm (h : Homotopy f g) : h.symm.barMap = -h.barMap := by
  dsimp only [symm, barMap]
  rw [Comodule.Hom.smul_toLinearMap]
  exact neg_one_smul R h.barHomotopy.toLinearMap

@[simp]
theorem taylor_symm (h : Homotopy f g) : h.symm.taylor = -h.taylor := by
  simp only [taylor_def, barMap_symm, LinearMap.comp_neg]

/-- Concatenate two bimodule homotopies. -/
def trans (h : Homotopy f g) (h' : Homotopy g k) : Homotopy f k where
  barHomotopy := h.barHomotopy + h'.barHomotopy
  leftCoact_comp_barMap := by
    simp only [Comodule.Hom.add_toLinearMap, LinearMap.comp_add,
      TensorProduct.map_add_right, LinearMap.add_comp,
      h.leftCoact_comp_barMap, h'.leftCoact_comp_barMap]
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.add_toLinearMap]
    exact h.isHomogeneous_barHomotopy.add h'.isHomogeneous_barHomotopy
  barMap_sub_barMap := by
    rw [Comodule.Hom.add_toLinearMap, LinearMap.comp_add, LinearMap.add_comp]
    calc
      f.barMap - k.barMap = (f.barMap - g.barMap) + (g.barMap - k.barMap) := by module
      _ = (NN.barDifferential ∘ₗ h.barMap + h.barMap ∘ₗ MM.barDifferential) +
          (NN.barDifferential ∘ₗ h'.barMap + h'.barMap ∘ₗ MM.barDifferential) := by
        rw [h.barMap_sub_barMap, h'.barMap_sub_barMap]
      _ = _ := by module

@[simp]
theorem barMap_trans (h : Homotopy f g) (h' : Homotopy g k) :
    (h.trans h').barMap = h.barMap + h'.barMap := (rfl)

@[simp]
theorem taylor_trans (h : Homotopy f g) (h' : Homotopy g k) :
    (h.trans h').taylor = h.taylor + h'.taylor := by
  simp only [taylor_def, barMap_trans, LinearMap.comp_add]

/-- Postcompose a homotopy with a bimodule morphism. -/
def compRight (h : Homotopy f g) (l : AInfinityBimoduleHom NN PP) :
    Homotopy (l.comp f) (l.comp g) where
  barHomotopy := l.barHom.comp h.barHomotopy
  leftCoact_comp_barMap := by
    simp only [Comodule.Hom.comp_toLinearMap]
    rw [← LinearMap.comp_assoc, l.leftCoact_comp_barMap, LinearMap.comp_assoc,
      h.leftCoact_comp_barMap, ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map]
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.comp_toLinearMap]
    simpa only [add_zero] using l.isHomogeneous_barMap.comp h.isHomogeneous_barHomotopy
  barMap_sub_barMap := by
    rw [barMap_comp, barMap_comp, Comodule.Hom.comp_toLinearMap, ← LinearMap.comp_sub,
      h.barMap_sub_barMap]
    simp only [LinearMap.comp_add, ← LinearMap.comp_assoc,
      ← l.barDifferential_comp_barMap]

@[simp]
theorem barMap_compRight (h : Homotopy f g) (l : AInfinityBimoduleHom NN PP) :
    (h.compRight l).barMap = l.barMap ∘ₗ h.barMap := (rfl)

/-- Postcomposition applies the outer morphism's Taylor map after the homotopy. -/
@[simp]
theorem taylor_compRight (h : Homotopy f g) (l : AInfinityBimoduleHom NN PP) :
    (h.compRight l).taylor = l.taylor ∘ₗ h.barMap := by
  simp only [taylor_def, barMap_compRight, AInfinityBimoduleHom.taylor_def,
    LinearMap.comp_assoc]

/-- Precompose a homotopy with a bimodule morphism. -/
def compLeft (h : Homotopy f g) (l : AInfinityBimoduleHom LL MM) :
    Homotopy (f.comp l) (g.comp l) where
  barHomotopy := h.barHomotopy.comp l.barHom
  leftCoact_comp_barMap := by
    simp only [Comodule.Hom.comp_toLinearMap]
    rw [← LinearMap.comp_assoc, h.leftCoact_comp_barMap, LinearMap.comp_assoc,
      l.leftCoact_comp_barMap, ← LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
  isHomogeneous_barHomotopy := by
    rw [Comodule.Hom.comp_toLinearMap]
    simpa only [zero_add] using h.isHomogeneous_barHomotopy.comp l.isHomogeneous_barMap
  barMap_sub_barMap := by
    rw [barMap_comp, barMap_comp, Comodule.Hom.comp_toLinearMap, ← LinearMap.sub_comp,
      h.barMap_sub_barMap]
    simp only [LinearMap.add_comp, LinearMap.comp_assoc, l.barDifferential_comp_barMap]

@[simp]
theorem barMap_compLeft (h : Homotopy f g) (l : AInfinityBimoduleHom LL MM) :
    (h.compLeft l).barMap = h.barMap ∘ₗ l.barMap := (rfl)

/-- Precomposition applies the homotopy's Taylor map after the inner morphism. -/
@[simp]
theorem taylor_compLeft (h : Homotopy f g) (l : AInfinityBimoduleHom LL MM) :
    (h.compLeft l).taylor = h.taylor ∘ₗ l.barMap := by
  simp only [taylor_def, barMap_compLeft, LinearMap.comp_assoc]

end Homotopy

end TauCeti.AInfinityBimoduleHom
