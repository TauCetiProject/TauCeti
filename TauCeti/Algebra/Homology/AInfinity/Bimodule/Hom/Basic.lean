/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Bicofree
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Basic

/-!
# Morphisms of A-infinity bimodules

A morphism over fixed algebras `A` and `B` is a degree-zero map of the two-sided
bar bicomodules commuting with their differentials. It is determined by its
Taylor map, obtained by applying both coalgebra counits. Conversely a degree-zero
Taylor map extends uniquely to a bicomodule map, and it defines a bimodule
morphism precisely when it satisfies the suspended component equation.

`AInfinityBimoduleHom.ofTaylor` supplies this constructor. Identities and
composition are the corresponding bar maps, with their Taylor formulas. These
maps are the algebraic inputs for functorial two-sided bar tensor products.
The interface follows `AInfinityRightModuleHom`; the differential-compatibility
proof reuses `Comodule.Hom.coderivationComm` on the right and cofree uniqueness
on both sides.

The conventions follow V. Lyubashenko and O. Manzyuk,
*A-infinity-bimodules and Serre A-infinity-functors*, and the suspended bar
convention of Getzler--Jones, *A-infinity algebras and the cyclic bar complex*,
Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uM uN uP uQ

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

/-- A morphism of `(A, B)` A-infinity bimodules is a degree-zero map of their bar
bicomodules intertwining the bar differentials. -/
structure AInfinityBimoduleHom (MM : AInfinityBimodule AA BB M)
    (NN : AInfinityBimodule AA BB N) where
  /-- The right-comodule bar map. -/
  barHom : Comodule.Hom R (TensorWords R B)
    ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
    ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B)
  /-- The bar map also respects the left coaction. -/
  leftCoact_comp_barMap :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ barHom.toLinearMap =
      barHom.toLinearMap.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M)
  /-- The bar map preserves suspended degree. -/
  isHomogeneous_barMap : LinearMap.IsHomogeneous barHom.toLinearMap
    (AInfinityBimodule.barGrading AA BB MM.grading).piece
    (AInfinityBimodule.barGrading AA BB NN.grading).piece 0
  /-- The bar map intertwines the differentials. -/
  barDifferential_comp_barMap :
    NN.barDifferential ∘ₗ barHom.toLinearMap = barHom.toLinearMap ∘ₗ MM.barDifferential

namespace AInfinityBimoduleHom

open AInfinityBimodule

variable {MM : AInfinityBimodule AA BB M} {NN : AInfinityBimodule AA BB N}
  {PP : AInfinityBimodule AA BB P}

/-- The linear map of the bar bicomodules. -/
abbrev barMap (f : AInfinityBimoduleHom MM NN) := f.barHom.toLinearMap

/-- The suspended Taylor map of a bimodule morphism, with both output words removed. -/
noncomputable def taylor (f : AInfinityBimoduleHom MM NN) :
    (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N :=
  taylorProj R A B N ∘ₗ f.barMap

/-- The Taylor map is the two-counit component of the bar map. -/
theorem taylor_def (f : AInfinityBimoduleHom MM NN) :
    f.taylor = taylorProj R A B N ∘ₗ f.barMap := (rfl)

/-- A morphism commutes with the bar differentials on elements. -/
@[simp]
theorem barDifferential_barMap (f : AInfinityBimoduleHom MM NN)
    (x : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :
    NN.barDifferential (f.barHom x) = f.barHom (MM.barDifferential x) :=
  LinearMap.congr_fun f.barDifferential_comp_barMap x

/-- The Taylor map of a bimodule morphism preserves suspended degree. -/
theorem isHomogeneous_taylor (f : AInfinityBimoduleHom MM NN) :
    LinearMap.IsHomogeneous f.taylor (barGrading AA BB MM.grading).piece
      (NN.grading.shift 1).piece 0 := by
  have hbar := f.isHomogeneous_barMap
  simp only [barGrading_def] at hbar ⊢
  rw [taylor_def, taylorProj_def, Comodule.leftCofreeCounit_def]
  simpa only [LinearMap.comp_assoc, add_zero] using
    ((TensorWords.isHomogeneous_lid_comp_rTensor_counit (AA.grading.shift 1)
      (NN.grading.shift 1)).comp (TensorWords.isHomogeneous_rid_comp_lTensor_counit
        ((TensorWords.grading (AA.grading.shift 1)).tensorProduct (NN.grading.shift 1))
        (BB.grading.shift 1))).comp hbar

/-- The bar map is recovered by extending the Taylor map to the cofree bicomodule. -/
theorem barMap_eq_bicofreeLift (f : AInfinityBimoduleHom MM NN) :
    f.barMap = (Comodule.bicofreeLift f.taylor).toLinearMap := by
  have h := Comodule.bicofreeLift_counit_comp f.barHom f.leftCoact_comp_barMap
  simpa only [taylor_def, taylorProj_def, LinearMap.comp_assoc] using
    (congrArg Comodule.Hom.toLinearMap h).symm

/-- Bimodule morphisms are determined by their bar maps. -/
theorem barMap_injective : Function.Injective (barMap : AInfinityBimoduleHom MM NN → _) := by
  rintro ⟨f, _, _, _⟩ ⟨g, _, _, _⟩ h
  obtain rfl := Comodule.Hom.toLinearMap_injective h
  rfl

/-- Bimodule morphisms are determined by their Taylor maps. -/
@[ext]
theorem ext {f g : AInfinityBimoduleHom MM NN} (h : f.taylor = g.taylor) : f = g := by
  apply barMap_injective
  rw [barMap_eq_bicofreeLift, barMap_eq_bicofreeLift, h]

/-- The suspended component equation of a bimodule morphism. -/
@[simp]
theorem taylor_comp_barMap (f : AInfinityBimoduleHom MM NN) :
    NN.taylor ∘ₗ f.barMap = f.taylor ∘ₗ MM.barDifferential := by
  simp only [AInfinityBimodule.taylor_def, taylor_def, LinearMap.comp_assoc,
    f.barDifferential_comp_barMap]

/-- For a degree-zero bicomodule map, commutation with the differentials can be checked on
its two-counit component. -/
theorem barDifferential_comp_iff
    (F : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B))
    (hleft : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ F.toLinearMap =
      F.toLinearMap.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M))
    (hF : LinearMap.IsHomogeneous F.toLinearMap (barGrading AA BB MM.grading).piece
      (barGrading AA BB NN.grading).piece 0) :
    NN.barDifferential ∘ₗ F.toLinearMap = F.toLinearMap ∘ₗ MM.barDifferential ↔
      NN.taylor ∘ₗ F.toLinearMap =
        (taylorProj R A B N ∘ₗ F.toLinearMap) ∘ₗ MM.barDifferential := by
  constructor
  · intro h
    simp only [AInfinityBimodule.taylor_def, LinearMap.comp_assoc, h]
  · intro h
    -- The bar carriers only carry additive-monoid instances; the ground ring supplies
    -- the additive inverses needed for the commutator.
    let _ : AddCommGroup ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) :=
      Module.addCommMonoidToAddCommGroup R
    let _ : AddCommGroup
        (TensorWords R A ⊗[R] ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B)) :=
      Module.addCommMonoidToAddCommGroup R
    let K : Comodule.Hom R (TensorWords R B)
        ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
        ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) :=
      Comodule.Hom.coderivationComm
        (N := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B)
        (r := 0) (q := 1) (b := BB.coaugmentedBarDifferential) F
        (barGrading AA BB MM.grading)
        (barGrading AA BB NN.grading) hF MM.barDifferential NN.barDifferential
        MM.isGradedCoderivation_barDifferential NN.isGradedCoderivation_barDifferential
    have hK : K.toLinearMap = NN.barDifferential ∘ₗ F.toLinearMap -
        F.toLinearMap ∘ₗ MM.barDifferential := by
      simp only [K, Comodule.Hom.coderivationComm_toLinearMap, mul_zero,
        Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul]
    -- The right coderivation commutator is already a right-comodule map. On the
    -- left, its two coalgebra-differential terms cancel, leaving a twisted map.
    have hKl : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ K.toLinearMap =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        K.toLinearMap ∘ₗ Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
      let δM := Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M)
      let δN := Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N)
      let τ := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1
      have hDN : δN ∘ₗ NN.barDifferential =
          AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δN +
            TensorProduct.map τ NN.barDifferential ∘ₗ δN := by
        apply LinearMap.ext
        intro x
        exact NN.isLeftGradedCoderivation_barDifferential.coact_apply x
      have hDM : δM ∘ₗ MM.barDifferential =
          AA.coaugmentedBarDifferential.rTensor _ ∘ₗ δM +
            TensorProduct.map τ MM.barDifferential ∘ₗ δM := by
        apply LinearMap.ext
        intro x
        exact MM.isLeftGradedCoderivation_barDifferential.coact_apply x
      dsimp only [δM, δN, τ] at hDN hDM
      rw [hK, ← TensorProduct.mapBilinear_apply, map_sub]
      simp only [TensorProduct.mapBilinear_apply, LinearMap.comp_sub, LinearMap.sub_comp]
      simp only [← LinearMap.comp_assoc, hDN, LinearMap.add_comp]
      simp only [LinearMap.comp_assoc, hleft]
      simp only [← LinearMap.comp_assoc]
      simp only [LinearMap.comp_assoc, hDM, LinearMap.comp_add]
      simp only [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor,
        LinearMap.map_comp_lTensor, LinearMap.lTensor_comp_rTensor,
        LinearMap.lTensor_comp_map]
      abel
    -- Cofreeness on both sides detects this commutator at the two counits.
    have hz : K = 0 := K.eq_zero_of_bicofree_counit_eq_zero _ hKl (by
      have hc : taylorProj R A B N ∘ₗ (NN.barDifferential ∘ₗ F.toLinearMap) =
          taylorProj R A B N ∘ₗ (F.toLinearMap ∘ₗ MM.barDifferential) := by
        simpa only [AInfinityBimodule.taylor_def, LinearMap.comp_assoc] using h
      have hz := sub_eq_zero.mpr hc
      rw [← LinearMap.comp_sub, ← hK] at hz
      simpa only [taylorProj_def, LinearMap.comp_assoc] using hz)
    have hz' := congrArg Comodule.Hom.toLinearMap hz
    simpa only [hK, Comodule.Hom.zero_toLinearMap, sub_eq_zero] using hz'

/-- Extending a degree-zero Taylor map to both cofree factors preserves suspended degree. -/
theorem isHomogeneous_bicofreeLift
    {φ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N}
    (hφ : LinearMap.IsHomogeneous φ (barGrading AA BB MM.grading).piece
      (NN.grading.shift 1).piece 0) :
    LinearMap.IsHomogeneous (Comodule.bicofreeLift φ).toLinearMap
      (barGrading AA BB MM.grading).piece (barGrading AA BB NN.grading).piece 0 := by
  simp only [barGrading_def] at hφ ⊢
  let W := TensorWords.grading (AA.grading.shift 1)
  let V := TensorWords.grading (BB.grading.shift 1)
  let Y := W.tensorProduct (MM.grading.shift 1)
  have hL := isHomogeneous_leftCoact AA BB MM.grading
  simp only [barGrading_def] at hL
  have hR : LinearMap.IsHomogeneous (Comodule.cofreeCoact R (TensorWords R B)
      (TensorWords R A ⊗[R] M)) (Y.tensorProduct V).piece
      ((Y.tensorProduct V).tensorProduct V).piece 0 := by
    rw [Comodule.cofreeCoact_def, LinearMap.lTensor_def,
      TensorWords.comul_eq_deconcatenation]
    simpa only [zero_add] using (InternalGrading.isHomogeneous_assoc_symm Y V V).comp
      ((LinearMap.isHomogeneous_id Y.piece).tensorProduct
        (TensorWords.isHomogeneous_deconcatenation (BB.grading.shift 1)))
  have h := ((((LinearMap.isHomogeneous_id W.piece).tensorProduct hφ).comp hL).tensorProduct
    (LinearMap.isHomogeneous_id V.piece)).comp hR
  simpa only [Comodule.bicofreeLift_toLinearMap, LinearMap.lTensor_def,
    LinearMap.rTensor_def, zero_add, add_zero] using h

/-- Construct a bimodule morphism from a degree-zero Taylor map satisfying the suspended
component equation. The cofree bicomodule construction supplies its entire bar map. -/
noncomputable def ofTaylor
    (φ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N)
    (hφ : LinearMap.IsHomogeneous φ (barGrading AA BB MM.grading).piece
      (NN.grading.shift 1).piece 0)
    (h : NN.taylor ∘ₗ (Comodule.bicofreeLift φ).toLinearMap = φ ∘ₗ MM.barDifferential) :
    AInfinityBimoduleHom MM NN where
  barHom := Comodule.bicofreeLift φ
  leftCoact_comp_barMap := Comodule.leftCoactRTensor_comp_bicofreeLift φ
  isHomogeneous_barMap := isHomogeneous_bicofreeLift hφ
  barDifferential_comp_barMap := (barDifferential_comp_iff _
    (Comodule.leftCoactRTensor_comp_bicofreeLift φ) (isHomogeneous_bicofreeLift hφ)).2 (by
      simpa only [taylorProj_def, LinearMap.comp_assoc,
        Comodule.counit_comp_bicofreeLift] using h)

@[simp]
theorem barMap_ofTaylor (φ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N) (hφ h) :
    (ofTaylor (MM := MM) (NN := NN) φ hφ h).barMap =
      (Comodule.bicofreeLift φ).toLinearMap := (rfl)

@[simp]
theorem taylor_ofTaylor (φ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N) (hφ h) :
    (ofTaylor (MM := MM) (NN := NN) φ hφ h).taylor = φ := by
  simp only [taylor_def, barMap_ofTaylor, taylorProj_def, LinearMap.comp_assoc,
    Comodule.counit_comp_bicofreeLift]

/-- Every bimodule morphism is reconstructed from its Taylor map. -/
@[simp]
theorem ofTaylor_self (f : AInfinityBimoduleHom MM NN) :
    ofTaylor f.taylor f.isHomogeneous_taylor
      (by rw [← f.barMap_eq_bicofreeLift]; exact f.taylor_comp_barMap) = f :=
  ext (taylor_ofTaylor _ _ _)

/-- The identity bimodule morphism. -/
protected noncomputable def id (MM : AInfinityBimodule AA BB M) :
    AInfinityBimoduleHom MM MM where
  barHom := Comodule.Hom.id R (TensorWords R B) _
  leftCoact_comp_barMap := by simp
  isHomogeneous_barMap := LinearMap.isHomogeneous_id _
  barDifferential_comp_barMap := by simp

@[simp]
theorem barMap_id (MM : AInfinityBimodule AA BB M) :
    (AInfinityBimoduleHom.id MM).barMap = LinearMap.id := (rfl)

/-- The identity's Taylor map is the projection onto the bimodule cogenerators. -/
@[simp]
theorem taylor_id (MM : AInfinityBimodule AA BB M) :
    (AInfinityBimoduleHom.id MM).taylor = taylorProj R A B M := by
  simp only [taylor_def, barMap_id, LinearMap.comp_id]

/-- Compose bimodule morphisms by composing their bar maps. -/
noncomputable def comp (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    AInfinityBimoduleHom MM PP where
  barHom := g.barHom.comp f.barHom
  leftCoact_comp_barMap := by
    simp only [Comodule.Hom.comp_toLinearMap]
    rw [← LinearMap.comp_assoc, g.leftCoact_comp_barMap, LinearMap.comp_assoc,
      f.leftCoact_comp_barMap, ← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
  isHomogeneous_barMap := by
    simpa only [Comodule.Hom.comp_toLinearMap, add_zero] using
      g.isHomogeneous_barMap.comp f.isHomogeneous_barMap
  barDifferential_comp_barMap := by
    simp only [Comodule.Hom.comp_toLinearMap]
    rw [← LinearMap.comp_assoc, g.barDifferential_comp_barMap, LinearMap.comp_assoc,
      f.barDifferential_comp_barMap, LinearMap.comp_assoc]

@[simp]
theorem barMap_comp (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    (g.comp f).barMap = g.barMap ∘ₗ f.barMap := (rfl)

/-- The Taylor map of a composite is the outer Taylor map after the inner bar map. -/
@[simp]
theorem taylor_comp (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    (g.comp f).taylor = g.taylor ∘ₗ f.barMap := by
  simp only [taylor_def, barMap_comp, LinearMap.comp_assoc]

@[simp]
theorem comp_id (f : AInfinityBimoduleHom MM NN) :
    f.comp (AInfinityBimoduleHom.id MM) = f := barMap_injective (by simp)

@[simp]
theorem id_comp (f : AInfinityBimoduleHom MM NN) :
    (AInfinityBimoduleHom.id NN).comp f = f := barMap_injective (by simp)

/-- Composition of bimodule morphisms is associative. -/
@[simp]
theorem comp_assoc {Q : Type uQ} [AddCommGroup Q] [Module R Q]
    {QQ : AInfinityBimodule AA BB Q} (h : AInfinityBimoduleHom PP QQ)
    (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  barMap_injective (by simp only [barMap_comp, LinearMap.comp_assoc])

end AInfinityBimoduleHom

end TauCeti
