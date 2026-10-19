/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Graded coderivations over a right comodule

An operator `D` on a right comodule over a coalgebra with operator `b` is a coderivation
over `b` when its coaction satisfies the signed co-Leibniz rule. On a homogeneous left
tensor factor `x`, the term applying `b` to the right factor has the Koszul coefficient
`(-1) ^ (q * |x|)`, where `q` is the twist parameter (the degree of `b` in graded
applications). Homogeneity of `D`, with its own degree, is imposed separately.

The condition is formulated for any right comodule, so it applies to the cofree bar
comodule `sM ⊗ Tᶜ(sA)` without constructing a second comodule API.  An odd homogeneous
coderivation over a square-zero `b` has a square which is a comodule morphism.  This is
the algebraic step needed to read module Stasheff identities from the components of `D²`.
Likewise, the graded commutator of a homogeneous comodule morphism with two coderivations over
the same operator `b` is a comodule morphism. Its counit component therefore detects compatibility
with the differentials when the target is cofree.

The sign convention follows Getzler--Jones, *A-infinity algebras and the cyclic bar
complex*, Sections 1--2, and Keller, *Introduction to A-infinity algebras and modules*,
Sections 3--4.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe uR uC uM

variable {R : Type uR} {C : Type uC} {M : Type uM}
  [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The signed co-Leibniz law for an endomorphism `D` of a right comodule over an operator
`b` on the coalgebra, with twist parameter `q`. Homogeneity (including the degree of `D`)
and square-zero conditions are separate: this predicate records exactly the compatibility
with the coaction. -/
def IsGradedCoderivationOver (G : InternalGrading R M) (q : ℤ)
    (b : C →ₗ[R] C) (D : M →ₗ[R] M) : Prop :=
  coact (R := R) (C := C) (M := M) ∘ₗ D =
    D.rTensor C ∘ₗ coact (R := R) (C := C) (M := M) +
      (b.lTensor M ∘ₗ (G.koszulTwist q).rTensor C) ∘ₗ
        coact (R := R) (C := C) (M := M)

variable {G : InternalGrading R M} {q : ℤ} {b : C →ₗ[R] C} {D : M →ₗ[R] M}

/-- The signed co-Leibniz law evaluated on one comodule element. -/
theorem IsGradedCoderivationOver.coact_apply (h : IsGradedCoderivationOver G q b D)
    (x : M) :
    coact (R := R) (C := C) (M := M) (D x) =
      D.rTensor C (coact (R := R) (C := C) (M := M) x) +
        b.lTensor M ((G.koszulTwist q).rTensor C
          (coact (R := R) (C := C) (M := M) x)) := by
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using
    LinearMap.congr_fun h x

/-- The signed co-Leibniz law can be checked on individual comodule elements. -/
theorem isGradedCoderivationOver_iff_coact_apply :
    IsGradedCoderivationOver G q b D ↔
      ∀ x : M,
        coact (R := R) (C := C) (M := M) (D x) =
          D.rTensor C (coact (R := R) (C := C) (M := M) x) +
            b.lTensor M ((G.koszulTwist q).rTensor C
              (coact (R := R) (C := C) (M := M) x)) := by
  constructor
  · exact IsGradedCoderivationOver.coact_apply
  · intro h
    apply LinearMap.ext
    intro x
    simpa only [IsGradedCoderivationOver, LinearMap.comp_apply, LinearMap.add_apply] using h x

/-- If the coalgebra operator squares to zero and `(-1) ^ (q * r) = -1`, the square of a
degree-`r` comodule coderivation with twist `q` commutes with the coaction. In the bar
construction this makes
`D²` a comodule morphism, so its vanishing can be checked on its cogenerator component. -/
theorem IsGradedCoderivationOver.square_commutes_coact_of_negOnePow_eq_neg_one {r : ℤ}
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) :
    coact (R := R) (C := C) (M := M) ∘ₗ (D ∘ₗ D) =
      (D ∘ₗ D).rTensor C ∘ₗ coact (R := R) (C := C) (M := M) := by
  let ρ := coact (R := R) (C := C) (M := M)
  let T := G.koszulTwist q
  let F := D.rTensor C
  let H := b.lTensor M ∘ₗ T.rTensor C
  have hρ : ρ ∘ₗ D = (F + H) ∘ₗ ρ := h
  have hTF : T ∘ₗ D = (-1 : R) • (D ∘ₗ T) := by
    simpa only [T, hqr] using hD.koszulTwist_comp q
  have hcross : F ∘ₗ H + H ∘ₗ F = 0 := by
    have hcomm : H ∘ₗ F = (-1 : R) • (F ∘ₗ H) := by
      calc
        H ∘ₗ F = b.lTensor M ∘ₗ (T ∘ₗ D).rTensor C := by
          dsimp only [H, F]
          rw [LinearMap.comp_assoc, ← LinearMap.rTensor_comp]
        _ = (-1 : R) • (b.lTensor M ∘ₗ (D ∘ₗ T).rTensor C) := by
          rw [hTF, LinearMap.rTensor_smul, LinearMap.comp_smul]
        _ = (-1 : R) • (F ∘ₗ H) := by
          dsimp only [F, H]
          rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor,
            ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc,
            ← LinearMap.rTensor_comp]
    rw [hcomm]
    module
  have hHsq : H ∘ₗ H = 0 := by
    dsimp only [H]
    rw [← LinearMap.comp_assoc,
      LinearMap.comp_assoc (b.lTensor M) (T.rTensor C) (b.lTensor M),
      LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      ← LinearMap.comp_assoc]
    rw [← LinearMap.lTensor_comp, hb]
    simp
  have hFsq : F ∘ₗ F = (D ∘ₗ D).rTensor C := by
    exact (LinearMap.rTensor_comp C D D).symm
  calc
    ρ ∘ₗ (D ∘ₗ D) = ((F + H) ∘ₗ (F + H)) ∘ₗ ρ := by
      rw [← LinearMap.comp_assoc, hρ, LinearMap.comp_assoc, hρ,
        ← LinearMap.comp_assoc]
    _ = (D ∘ₗ D).rTensor C ∘ₗ ρ := by
      rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add,
        ← add_assoc, add_assoc (F ∘ₗ F), hcross, hHsq, hFsq]
      simp

/-- The square of a degree-one coderivation over a square-zero coalgebra operator
commutes with the coaction. -/
theorem IsGradedCoderivationOver.square_commutes_coact
    (h : IsGradedCoderivationOver G 1 b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece 1)
    (hb : b ∘ₗ b = 0) :
    coact (R := R) (C := C) (M := M) ∘ₗ (D ∘ₗ D) =
      (D ∘ₗ D).rTensor C ∘ₗ coact (R := R) (C := C) (M := M) :=
  h.square_commutes_coact_of_negOnePow_eq_neg_one hD (by norm_num) hb

/-- When `(-1) ^ (q * r) = -1` in the coefficient ring, the square of a degree-`r`
coderivation over a square-zero coalgebra operator is a comodule endomorphism. -/
def IsGradedCoderivationOver.squareHomOfNegOnePowEqNegOne {r : ℤ}
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) : Hom R C M M where
  toLinearMap := D ∘ₗ D
  map_coact := by
    simpa only [LinearMap.rTensor] using
      (h.square_commutes_coact_of_negOnePow_eq_neg_one hD hqr hb).symm

/-- The square of an odd coderivation over a square-zero coalgebra operator is a
comodule endomorphism. -/
def IsGradedCoderivationOver.squareHom
    (h : IsGradedCoderivationOver G 1 b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece 1)
    (hb : b ∘ₗ b = 0) : Hom R C M M :=
  h.squareHomOfNegOnePowEqNegOne hD (by norm_num) hb

/-- The underlying map of the square comodule endomorphism under the sign hypothesis. -/
@[simp]
theorem IsGradedCoderivationOver.squareHomOfNegOnePowEqNegOne_toLinearMap {r : ℤ}
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) :
    (h.squareHomOfNegOnePowEqNegOne hD hqr hb).toLinearMap = D ∘ₗ D := by
  rw [squareHomOfNegOnePowEqNegOne]

/-- The underlying map of the square comodule endomorphism is the square of the
coderivation. -/
@[simp]
theorem IsGradedCoderivationOver.squareHom_toLinearMap
    (h : IsGradedCoderivationOver G 1 b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece 1)
    (hb : b ∘ₗ b = 0) :
    (h.squareHom hD hb).toLinearMap = D ∘ₗ D :=
  by rw [squareHom, squareHomOfNegOnePowEqNegOne_toLinearMap]

section Cofree

variable {N : Type*} [AddCommMonoid N] [Module R N]

attribute [local instance] Comodule.cofree

/-- On a cofree comodule, the square under the sign hypothesis vanishes exactly when its
component obtained by applying the coalgebra counit vanishes.  This is the universal
property that reduces module Stasheff identities to Taylor components. -/
theorem IsGradedCoderivationOver.square_eq_zero_iff_counit_of_negOnePow_eq_neg_one {r : ℤ}
    (G : InternalGrading R (N ⊗[R] C))
    (b : C →ₗ[R] C) (D : (N ⊗[R] C) →ₗ[R] N ⊗[R] C)
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) :
    D ∘ₗ D = 0 ↔
      (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := C)).lTensor N ∘ₗ (D ∘ₗ D) = 0 := by
  let f : Hom R C (N ⊗[R] C) (N ⊗[R] C) :=
    h.squareHomOfNegOnePowEqNegOne hD hqr hb
  constructor
  · intro hsq
    rw [hsq]
    simp
  · intro hc
    have hz : f = 0 := (Hom.eq_zero_iff_counit f).2 (by
      simpa only [f, squareHomOfNegOnePowEqNegOne_toLinearMap] using hc)
    have hlin := congrArg (fun g : Hom R C (N ⊗[R] C) (N ⊗[R] C) => g.toLinearMap) hz
    simpa only [f, squareHomOfNegOnePowEqNegOne_toLinearMap, Hom.zero_toLinearMap] using hlin

/-- For a degree-one coderivation, the square vanishes if and only if its cofree
counit component vanishes. -/
theorem IsGradedCoderivationOver.square_eq_zero_iff_counit
    (G : InternalGrading R (N ⊗[R] C))
    (b : C →ₗ[R] C) (D : (N ⊗[R] C) →ₗ[R] N ⊗[R] C)
    (h : IsGradedCoderivationOver G 1 b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece 1)
    (hb : b ∘ₗ b = 0) :
    D ∘ₗ D = 0 ↔
      (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := C)).lTensor N ∘ₗ (D ∘ₗ D) = 0 :=
  h.square_eq_zero_iff_counit_of_negOnePow_eq_neg_one G b D hD (by norm_num) hb

/-- Two coderivations over the same coalgebra operator on a cofree comodule are equal when their
counit components agree. -/
theorem IsGradedCoderivationOver.eq_of_counit_comp_eq
    (G : InternalGrading R (N ⊗[R] C))
    (b : C →ₗ[R] C) (D E : (N ⊗[R] C) →ₗ[R] N ⊗[R] C)
    (hD : IsGradedCoderivationOver G q b D)
    (hE : IsGradedCoderivationOver G q b E)
    (hcounit :
      (TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := C)).lTensor N ∘ₗ D =
        (TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := C)).lTensor N ∘ₗ E) :
    D = E := by
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
  let _ : AddCommGroup (N ⊗[R] C) := Module.addCommMonoidToAddCommGroup R
  let ρ := coact (R := R) (C := C) (M := N ⊗[R] C)
  have hcomm : ρ ∘ₗ (D - E) = (D - E).rTensor C ∘ₗ ρ := by
    rw [LinearMap.comp_sub, hD, hE, LinearMap.rTensor_sub, LinearMap.sub_comp]
    module
  let f : Hom R C (N ⊗[R] C) (N ⊗[R] C) :=
    { toLinearMap := D - E
      map_coact := by
        simpa only [LinearMap.rTensor] using hcomm.symm }
  have hf_counit :
      (TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := C)).lTensor N ∘ₗ f.toLinearMap = 0 := by
    dsimp only [f]
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hcounit x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub, LinearMap.zero_apply]
    exact sub_eq_zero.mpr h
  have hf : f = 0 := (Hom.eq_zero_iff_counit f).2 hf_counit
  have hsub := congrArg (fun g : Hom R C (N ⊗[R] C) (N ⊗[R] C) ↦ g.toLinearMap) hf
  have : D - E = 0 := by
    simpa only [f, Hom.zero_toLinearMap] using hsub
  exact sub_eq_zero.mp this

end Cofree

namespace Hom

variable {N : Type*} [AddCommGroup N] [Module R N]
  [Comodule R C N]

/-- The graded commutator of a degree-`r` comodule morphism with coderivations over the same
coalgebra operator is a comodule morphism. The two coalgebra terms cancel by Koszul naturality. -/
def coderivationComm {r : ℤ} (f : Hom R C M N) (G : InternalGrading R M) (H : InternalGrading R N)
    (hf : LinearMap.IsHomogeneous f.toLinearMap G.piece H.piece r)
    (D : M →ₗ[R] M) (E : N →ₗ[R] N)
    (hD : IsGradedCoderivationOver G q b D) (hE : IsGradedCoderivationOver H q b E) :
    Hom R C M N where
  toLinearMap := E ∘ₗ f.toLinearMap - (((q * r).negOnePow : ℤ) : R) • (f.toLinearMap ∘ₗ D)
  map_coact := by
    let F := f.toLinearMap.rTensor C
    let ρM := coact (R := R) (C := C) (M := M)
    let ρN := coact (R := R) (C := C) (M := N)
    let TM := b.lTensor M ∘ₗ (G.koszulTwist q).rTensor C
    let TN := b.lTensor N ∘ₗ (H.koszulTwist q).rTensor C
    have hF : F ∘ₗ ρM = ρN ∘ₗ f.toLinearMap := f.map_coact
    have htw : H.koszulTwist q ∘ₗ f.toLinearMap =
        (((q * r).negOnePow : ℤ) : R) • (f.toLinearMap ∘ₗ G.koszulTwist q) :=
      hf.koszulTwist_comp q
    have hcross : TN ∘ₗ F = (((q * r).negOnePow : ℤ) : R) • (F ∘ₗ TM) := by
      refine TensorProduct.ext' fun x c ↦ ?_
      simpa only [TN, TM, F, LinearMap.comp_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, LinearMap.smul_apply, TensorProduct.smul_tmul'] using
        congrArg (fun y ↦ y ⊗ₜ[R] b c) (LinearMap.congr_fun htw x)
    have hleft : ρN ∘ₗ (E ∘ₗ f.toLinearMap) =
        E.rTensor C ∘ₗ F ∘ₗ ρM + TN ∘ₗ F ∘ₗ ρM := by
      rw [← LinearMap.comp_assoc, hE, LinearMap.add_comp]
      dsimp only [TN, ρN, ρM] at hF ⊢
      simp only [LinearMap.comp_assoc, hF]
    have hright : ρN ∘ₗ (f.toLinearMap ∘ₗ D) =
        F ∘ₗ D.rTensor C ∘ₗ ρM + F ∘ₗ TM ∘ₗ ρM := by
      rw [← LinearMap.comp_assoc, ← hF, LinearMap.comp_assoc, hD, LinearMap.comp_add]
    have hcomm : ρN ∘ₗ
        (E ∘ₗ f.toLinearMap - (((q * r).negOnePow : ℤ) : R) • (f.toLinearMap ∘ₗ D)) =
        (E ∘ₗ f.toLinearMap -
          (((q * r).negOnePow : ℤ) : R) • (f.toLinearMap ∘ₗ D)).rTensor C ∘ₗ ρM := by
      have hcross' := congrArg (fun L ↦ L ∘ₗ ρM) hcross
      simp only [LinearMap.smul_comp, LinearMap.comp_assoc] at hcross'
      rw [LinearMap.comp_sub, LinearMap.comp_smul, hleft, hright, hcross']
      simp only [LinearMap.rTensor_sub, LinearMap.rTensor_smul, LinearMap.rTensor_comp,
        LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_assoc]
      module
    exact hcomm.symm

/-- The underlying map of the coderivation commutator is the signed operator commutator. -/
@[simp]
theorem coderivationComm_toLinearMap {r : ℤ} (f : Hom R C M N) (G : InternalGrading R M)
    (H : InternalGrading R N) (hf D E hD hE) :
    (f.coderivationComm (r := r) (q := q) (b := b) G H hf D E hD hE).toLinearMap =
      E ∘ₗ f.toLinearMap - (((q * r).negOnePow : ℤ) : R) • (f.toLinearMap ∘ₗ D) := (rfl)

end Hom

end Comodule

end TauCeti
