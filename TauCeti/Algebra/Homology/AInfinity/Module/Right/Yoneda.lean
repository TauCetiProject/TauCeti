/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Free
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Complex
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# The Yoneda map of a right A-infinity module

Let `M` be a right `A∞` module over an `A∞` algebra `A`, and regard `A` as the free right module
of rank one over itself (`TauCeti.AInfinityAlgebra.toRightModule`).  An element `x` of `M` of
degree `p` defines a cochain of degree `p` in the morphism complex `Hom(A, M)`: the morphism of
cofree bar comodules `sA ⊗ Tᶜ(sA) → sM ⊗ Tᶜ(sA)` whose Taylor map inserts `x` in front of the
word and applies the Taylor map of `M`,

`a ⊗ a₁ ⋯ aₙ ↦ (-1)^p b^M(x ⊗ a a₁ ⋯ aₙ)`.

Its arity-one component is right multiplication by `x`, `a ↦ m₂^M(x, a)`, as for the DG Yoneda
map `a ↦ x a` of `TauCeti.dgYonedaIso`.

These cochains form a morphism of cochain complexes from the underlying complex of `M`, with the
unary operation `m₁` as differential, to `Hom(A, M)`; the sign `(-1)^p` is what makes it commute
with the differentials.  Write `ι_x : sA ⊗ Tᶜ(sA) → sM ⊗ Tᶜ(sA)` for `a ⊗ w ↦ x ⊗ a w`.  Expanding
the module bar differential on `x ⊗ a w` according to where its blocks lie, the block consisting
of `x` alone gives `ι_{m₁ x}`, the blocks starting at `x` and running into `a w` give the unsigned
Yoneda cochain of `x`, and the algebra bar differential acting on `a w` is the bar differential of
the free module followed by `ι_x`, with a Koszul sign.  After the Taylor map of `M`, the module
Stasheff equation `taylor ∘ b^M = 0` therefore says that the differential of the unsigned
cochain of `x` is minus the unsigned cochain of `m₁ x`.

The Yoneda lemma for `A∞` modules asserts that this morphism is a quasi-isomorphism when `A` and
`M` are strictly unital.  This file only constructs the morphism, over an arbitrary commutative
ground ring and without unitality assumptions.

## Main definitions

* `TauCeti.AInfinityRightModule.yonedaCochain`: the Yoneda cochain of degree `p` of an element of
  degree `p`.
* `TauCeti.AInfinityRightModule.yonedaComplexHom`: the Yoneda map, as a morphism of cochain
  complexes from the underlying complex of `M` to the morphism complex out of `A`.

## Main results

* `TauCeti.AInfinityRightModule.coe_yonedaCochain` and
  `TauCeti.AInfinityRightModule.taylor_yonedaCochain`: a Yoneda cochain is the cofree lift of its
  Taylor map `a ⊗ w ↦ (-1)^p b^M(x ⊗ a w)`.
* `TauCeti.AInfinityRightModule.yonedaCochain_tmul_one`: its arity-one component is right
  multiplication by the element.
* `TauCeti.AInfinityRightModule.homDifferential_yonedaCochain`: the Yoneda cochains commute
  with the differentials.

## Implementation notes

The underlying complex of `M` has its terms in the universe of `M`, while the terms of the
morphism complex live in the universe of linear maps between bar comodules.  As for the DG
category of right `A∞` modules (`TauCeti.AInfinityRightModuleCat.instDGCategory`), the morphism
of complexes therefore takes the ground ring, the algebra and the module in a single universe;
the degreewise statements carry no universe constraint.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u uR uA uM

attribute [local instance] Comodule.cofree

open TensorWords

namespace AInfinityRightModule

section Cochains

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A} {M : Type uM} [AddCommGroup M] [Module R M]
  (MM : AInfinityRightModule AA M)

/-- The unsigned Taylor map of the Yoneda cochain of `x`: `a ⊗ w ↦ b^M(x ⊗ a w)`. -/
private noncomputable def yonedaTaylor : M →ₗ[R] (A ⊗[R] TensorWords R A) →ₗ[R] M :=
  TensorProduct.curry
    (MM.taylor ∘ₗ (reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A)).lTensor M)

private theorem yonedaTaylor_tmul (x : M) (a : A) (w : TensorWords R A) :
    MM.yonedaTaylor x (a ⊗ₜ[R] w) =
      MM.taylor (x ⊗ₜ[R] reducedInclusion R A (prepend R A a w)) := by
  simp only [yonedaTaylor, TensorProduct.curry_apply, LinearMap.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.lift.tmul]

private theorem yonedaTaylor_eq (x : M) :
    MM.yonedaTaylor x = MM.taylor ∘ₗ TensorProduct.mk R M (TensorWords R A) x ∘ₗ
      reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A) :=
  TensorProduct.ext' fun a w ↦ by
    simp only [yonedaTaylor_tmul, LinearMap.comp_apply, TensorProduct.mk_apply,
      TensorProduct.lift.tmul]

/-- The unsigned Yoneda cochain of `x`: the cofree lift of its Taylor map. -/
private noncomputable def yonedaBar :
    M →ₗ[R] (A ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A :=
  LinearMap.lcomp R (M ⊗[R] TensorWords R A)
      (Comodule.coact (R := R) (C := TensorWords R A) (M := A ⊗[R] TensorWords R A)) ∘ₗ
    LinearMap.rTensorHom (TensorWords R A) ∘ₗ MM.yonedaTaylor

private theorem yonedaBar_eq (x : M) :
    MM.yonedaBar x =
      (Comodule.Hom.cofreeLift (C := TensorWords R A) (MM.yonedaTaylor x)).toLinearMap :=
  (rfl)

private theorem rid_comp_lTensor_counit_comp_yonedaBar (x : M) :
    (TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ MM.yonedaBar x =
      MM.yonedaTaylor x := by
  have h := (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := M)
    (P := A ⊗[R] TensorWords R A)).apply_symm_apply (MM.yonedaTaylor x)
  rwa [Comodule.Hom.cofreeEquiv_symm_apply, Comodule.Hom.cofreeEquiv_apply, ← yonedaBar_eq] at h

private theorem isHomogeneous_yonedaTaylor {p : ℤ} {x : M} (hx : x ∈ MM.grading.piece p) :
    LinearMap.IsHomogeneous (MM.yonedaTaylor x)
      (barGrading AA AA.toRightModule.grading).piece (MM.grading.shift 1).piece p := by
  rw [yonedaTaylor_eq, AInfinityAlgebra.toRightModule_grading]
  have hcat : LinearMap.IsHomogeneous (reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A))
      (barGrading AA AA.grading).piece (TensorWords.grading (AA.grading.shift 1)).piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro q z hz
    rw [barGrading_piece] at hz
    rw [grading_piece, LinearMap.comp_apply]
    exact mem_gradedPiece_of_reducedInclusion
      ((isHomogeneous_lift_prepend (AA.grading.shift 1)).map_mem hz)
  have hx' : x ∈ (MM.grading.shift 1).piece (p - 1) := by
    rwa [InternalGrading.shift_piece, sub_add_cancel]
  have hmk : LinearMap.IsHomogeneous (TensorProduct.mk R M (TensorWords R A) x)
      (TensorWords.grading (AA.grading.shift 1)).piece (barGrading AA MM.grading).piece
      (p - 1) := by
    rw [LinearMap.isHomogeneous_def]
    intro q w hw
    rw [barGrading_piece, TensorProduct.mk_apply, add_comm q]
    exact InternalGrading.tmul_mem_tensorProduct _ _ hx' hw
  have h := MM.isHomogeneous_taylor.comp (hmk.comp hcat)
  rwa [zero_add, sub_add_cancel] at h

private theorem yonedaBar_mem_homCochains {p : ℤ} {x : M} (hx : x ∈ MM.grading.piece p) :
    MM.yonedaBar x ∈ homCochains AA.toRightModule MM p := by
  rw [yonedaBar_eq]
  exact toLinearMap_mem_homCochains _ (AInfinityRightModuleHom.isHomogeneous_cofreeLift
    (MM := AA.toRightModule) (NN := MM) _ (MM.isHomogeneous_yonedaTaylor hx))

/-- The module bar differential after inserting `x` in front of a word: the block ending at `x`
gives `m₁ x`, the blocks running into the word give the unsigned Yoneda cochain of `x`, and the
algebra bar differential of the word is the bar differential of the free module. -/
private theorem barDifferential_comp_mk_comp_concat (x : M) :
    MM.barDifferential ∘ₗ TensorProduct.mk R M (TensorWords R A) x ∘ₗ
        reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A) =
      TensorProduct.mk R M (TensorWords R A) (MM.differential x) ∘ₗ
          reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A) +
        MM.yonedaBar x +
        (TensorProduct.mk R M (TensorWords R A) ((MM.grading.shift 1).koszulTwist 1 x) ∘ₗ
          reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A)) ∘ₗ
            AA.toRightModule.barDifferential := by
  have hb : AA.coaugmentedBarDifferential ∘ₗ reducedInclusion R A ∘ₗ
      TensorProduct.lift (prepend R A) = reducedInclusion R A ∘ₗ
        TensorProduct.lift (prepend R A) ∘ₗ AA.toRightModule.barDifferential := by
    rw [← LinearMap.comp_assoc, AA.coaugmentedBarDifferential_comp_reducedInclusion,
      LinearMap.comp_assoc, AA.lift_prepend_comp_barDifferential_toRightModule]
  -- The cuts of `a w` after `a` are `a` prepended to the cuts of `w`.
  have hcut (a : A) (t : TensorWords R A ⊗[R] TensorWords R A) :
      MM.taylor.rTensor (TensorWords R A)
          ((TensorProduct.assoc R M (TensorWords R A) (TensorWords R A)).symm
            (x ⊗ₜ[R] (reducedInclusion R A ∘ₗ prepend R A a).rTensor (TensorWords R A) t)) =
        (MM.yonedaTaylor x).rTensor (TensorWords R A)
          ((TensorProduct.assoc R A (TensorWords R A) (TensorWords R A)).symm (a ⊗ₜ[R] t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, TensorProduct.assoc_symm_tmul,
        yonedaTaylor_tmul]
    | add t t' ht ht' => simp only [map_add, TensorProduct.tmul_add, ht, ht']
  have hd : MM.differential x = MM.taylor (x ⊗ₜ[R] (1 : TensorWords R A)) := by
    rw [differential_apply, taylor_tmul_one]
  refine TensorProduct.ext' fun a w ↦ ?_
  have hbw := LinearMap.congr_fun hb (a ⊗ₜ[R] w)
  simp only [LinearMap.comp_apply, TensorProduct.lift.tmul] at hbw
  have hΔ := LinearMap.congr_fun (deconcatenation_comp_reducedInclusion_comp_prepend a) w
  simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.mk_apply] at hΔ
  rw [barDifferential_eq, gradedCoderiv_def, yonedaBar_eq, Comodule.Hom.cofreeLift_toLinearMap]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
    TensorProduct.lift.tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    hΔ, TensorProduct.tmul_add, map_add,
    LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul, hbw, Comodule.cofree_coact_tmul, hcut, hd,
    LinearMap.congr_fun (comul_eq_deconcatenation R A)]

/-- The differential of the unsigned Yoneda cochain of `x` is minus the unsigned Yoneda cochain
of `m₁ x`. -/
private theorem homDifferential_yonedaBar {p : ℤ} {x : M} (hx : x ∈ MM.grading.piece p) :
    homDifferential AA.toRightModule MM p ⟨MM.yonedaBar x, MM.yonedaBar_mem_homCochains hx⟩ =
      -⟨MM.yonedaBar (MM.differential x),
        MM.yonedaBar_mem_homCochains (MM.differential_mem_piece hx)⟩ := by
  have hx' : x ∈ (MM.grading.shift 1).piece (p - 1) := by
    rwa [InternalGrading.shift_piece, sub_add_cancel]
  -- The module Stasheff equation `taylor ∘ b^M = 0`, read through the insertion of `x`.
  have hkey := congrArg (MM.taylor ∘ₗ ·) (MM.barDifferential_comp_mk_comp_concat x)
  simp only [LinearMap.comp_add] at hkey
  rw [← LinearMap.comp_assoc _ MM.barDifferential MM.taylor, taylor_comp_barDifferential,
    LinearMap.zero_comp, ← LinearMap.comp_assoc AA.toRightModule.barDifferential _ MM.taylor,
    ← yonedaTaylor_eq, ← yonedaTaylor_eq, InternalGrading.koszulTwist_apply_of_mem _ hx',
    map_smul, LinearMap.smul_comp] at hkey
  apply homCochains.ext_taylor
  rw [homCochains.taylor_homDifferential]
  simp only [NegMemClass.coe_neg, LinearMap.comp_neg, rid_comp_lTensor_counit_comp_yonedaBar]
  have hc : (((1 * (p - 1)).negOnePow : ℤ) : R) = -((p.negOnePow : ℤ) : R) := by
    rw [one_mul, Int.negOnePow_sub, Int.negOnePow_one]
    push_cast
    ring
  rw [hc, neg_smul] at hkey
  rw [eq_neg_iff_add_eq_zero, Units.smul_def, ← Int.cast_smul_eq_zsmul R, hkey]
  abel

/-- The Yoneda cochain of degree `p` attached to an element `x` of `M` of degree `p`: the morphism
of cofree bar comodules `sA ⊗ Tᶜ(sA) → sM ⊗ Tᶜ(sA)` of degree `p` from the free module of rank
one, whose Taylor map inserts `x` in front of the word and applies the Taylor map of `M`, with the
sign `(-1)^p`: `a ⊗ w ↦ (-1)^p b^M(x ⊗ a w)`. -/
noncomputable def yonedaCochain (p : ℤ) :
    MM.grading.piece p →ₗ[R] homCochains AA.toRightModule MM p :=
  p.negOnePow • (MM.yonedaBar ∘ₗ (MM.grading.piece p).subtype).codRestrict _
    fun x ↦ MM.yonedaBar_mem_homCochains x.2

/-- The Yoneda cochain of `x` is `(-1)^p` times the cofree lift of `a ⊗ w ↦ b^M(x ⊗ a w)`. -/
theorem coe_yonedaCochain (p : ℤ) (x : MM.grading.piece p) :
    (MM.yonedaCochain p x : (A ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A) =
      p.negOnePow • (Comodule.Hom.cofreeLift (C := TensorWords R A)
        (MM.taylor ∘ₗ TensorProduct.mk R M (TensorWords R A) x ∘ₗ
          reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A))).toLinearMap := by
  rw [← yonedaTaylor_eq, ← yonedaBar_eq, yonedaCochain, LinearMap.smul_apply,
    Submodule.coe_smul_of_tower, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply]

/-- The Taylor map of the Yoneda cochain of `x` is `a ⊗ w ↦ (-1)^p b^M(x ⊗ a w)`. -/
theorem taylor_yonedaCochain (p : ℤ) (x : MM.grading.piece p) :
    (TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ
          (MM.yonedaCochain p x : (A ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A) =
      p.negOnePow • (MM.taylor ∘ₗ TensorProduct.mk R M (TensorWords R A) x ∘ₗ
        reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A)) := by
  rw [coe_yonedaCochain, ← yonedaTaylor_eq, ← yonedaBar_eq, LinearMap.comp_smul,
    LinearMap.comp_smul, rid_comp_lTensor_counit_comp_yonedaBar]

/-- The Taylor map of the Yoneda cochain of `x` on `a ⊗ w` is `(-1)^p b^M(x ⊗ a w)`. -/
theorem taylor_yonedaCochain_tmul (p : ℤ) (x : MM.grading.piece p) (a : A)
    (w : TensorWords R A) :
    TensorProduct.rid R M ((Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M
        ((MM.yonedaCochain p x : (A ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
          (a ⊗ₜ[R] w))) =
      p.negOnePow • MM.taylor ((x : M) ⊗ₜ[R] reducedInclusion R A (prepend R A a w)) := by
  have h := LinearMap.congr_fun (MM.taylor_yonedaCochain p x) (a ⊗ₜ[R] w)
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    TensorProduct.mk_apply, TensorProduct.lift.tmul] using h

/-- The arity-one component of the Yoneda cochain of `x` is right multiplication by `x`: it sends
`a ⊗ 1` to `m₂^M(x, a) ⊗ 1`. -/
@[simp]
theorem yonedaCochain_tmul_one (p : ℤ) (x : MM.grading.piece p) (a : A) :
    (MM.yonedaCochain p x : (A ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
        (a ⊗ₜ[R] (1 : TensorWords R A)) =
      MM.m 2 x ![a] ⊗ₜ[R] (1 : TensorWords R A) := by
  have hletter : reducedInclusion R A (prepend R A a 1) =
      TensorWords.of R A 1 (PiTensorProduct.tprod R ![a]) := by
    rw [prepend_one, ReducedTensorWords.ofLetter_eq_of_tprod, reducedInclusion_of]
    exact of_tprod_congr R A fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl
  rw [coe_yonedaCochain, LinearMap.smul_apply, Comodule.Hom.cofreeLift_toLinearMap,
    LinearMap.comp_apply, Comodule.cofree_coact_tmul,
    LinearMap.congr_fun (comul_eq_deconcatenation R A), deconcatenation_one,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.lift.tmul,
    hletter, taylor_tmul_of_tprod]
  have hv : (fun i : Fin 1 ↦ AA.grading.koszulTwist (((1 : ℕ) : ℤ) - 1 - i) (![a] i)) = ![a] := by
    funext i
    rw [Fin.fin_one_eq_zero i, Fin.val_zero, Nat.cast_zero, Nat.cast_one, sub_self, sub_zero,
      InternalGrading.koszulTwist_zero, LinearMap.id_apply]
  rw [hv, MM.grading.koszulTwist_apply_of_mem x.2, map_smul, smul_apply,
    ← TensorProduct.smul_tmul', Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_smul,
    ← Int.cast_mul, ← Units.val_mul, Nat.cast_one, one_mul, Int.units_mul_self, Units.val_one,
    Int.cast_one, one_smul]

/-- The Yoneda cochains commute with the differentials: the differential of the Yoneda cochain
of `x` is the Yoneda cochain of `m₁ x`. -/
@[simp]
theorem homDifferential_yonedaCochain (p : ℤ) (x : MM.grading.piece p) :
    homDifferential AA.toRightModule MM p (MM.yonedaCochain p x) =
      MM.yonedaCochain (p + 1) ⟨MM.differential x, MM.differential_mem_piece x.2⟩ := by
  have h := congrArg Subtype.val (MM.homDifferential_yonedaBar x.2)
  simp only [coe_homDifferential, NegMemClass.coe_neg] at h
  have h' : MM.barDifferential ∘ₗ MM.yonedaBar x =
      p.negOnePow • (MM.yonedaBar x ∘ₗ AA.toRightModule.barDifferential) +
        -MM.yonedaBar (MM.differential x) := by
    rw [← h]
    abel
  apply Subtype.ext
  rw [coe_homDifferential, coe_yonedaCochain, coe_yonedaCochain, ← yonedaTaylor_eq,
    ← yonedaTaylor_eq, ← yonedaBar_eq, ← yonedaBar_eq, LinearMap.comp_smul, LinearMap.smul_comp,
    h']
  simp only [smul_add, smul_neg, add_sub_cancel_left, Int.negOnePow_succ, Units.neg_smul]

end Cochains

section Complex

variable {R A M : Type u} [CommRing R] [AddCommGroup A] [Module R A] {AA : AInfinityAlgebra R A}
  [AddCommGroup M] [Module R M] (MM : AInfinityRightModule AA M)

/-- The Yoneda map as a morphism of cochain complexes, from the underlying complex of `M` with
the module differential `m₁` to the morphism complex from the free module of rank one to `M`.
Its component of degree `p` is `TauCeti.AInfinityRightModule.yonedaCochain`. -/
noncomputable def yonedaComplexHom :
    gradedCochainComplex MM.grading.piece MM.differential MM.isHomogeneous_differential
        (fun _ x ↦ LinearMap.congr_fun MM.differential_comp_self_eq_zero x) ⟶
      homComplex AA.toRightModule MM where
  f p := eqToHom (gradedCochainComplex_X p) ≫ ModuleCat.ofHom (MM.yonedaCochain p) ≫
    eqToHom (homComplex_X AA.toRightModule MM p).symm
  comm' := by
    rintro i j (rfl : i + 1 = j)
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    set x := (eqToHom (gradedCochainComplex_X i)).hom y
    have hd := congrArg (fun φ ↦ φ.hom (MM.yonedaCochain i x))
      (homComplex_d AA.toRightModule MM i)
    have key := gradedCochainComplex_d_apply (hdeg := MM.isHomogeneous_differential)
      (hsq := fun _ x ↦ LinearMap.congr_fun MM.differential_comp_self_eq_zero x) i x
    -- The `eqToHom` of `gradedCochainComplex_X` is cancelled by its inverse.
    rw [show (eqToHom (gradedCochainComplex_X i).symm) x = y from
      (eqToIso (gradedCochainComplex_X i)).hom_inv_id_apply y] at key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    -- The `eqToHom`s of `homComplex_X` are identities of definitionally equal modules.
    exact (hd.trans (MM.homDifferential_yonedaCochain i x)).trans
      (congrArg (MM.yonedaCochain (i + 1)) key.symm)

/-- The degree-`p` component of the Yoneda map is the Yoneda cochain of degree `p`. -/
@[simp]
theorem yonedaComplexHom_f (p : ℤ) :
    (MM.yonedaComplexHom).f p = eqToHom (gradedCochainComplex_X p) ≫
      ModuleCat.ofHom (MM.yonedaCochain p) ≫ eqToHom (homComplex_X AA.toRightModule MM p).symm :=
  (rfl)

end Complex

end AInfinityRightModule

end TauCeti
