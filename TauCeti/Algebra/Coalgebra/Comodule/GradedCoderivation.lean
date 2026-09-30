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

/-- The signed co-Leibniz law, stated as an equality of linear maps. -/
theorem isGradedCoderivationOver_iff :
    IsGradedCoderivationOver G q b D ↔
      coact (R := R) (C := C) (M := M) ∘ₗ D =
        D.rTensor C ∘ₗ coact (R := R) (C := C) (M := M) +
          (b.lTensor M ∘ₗ (G.koszulTwist q).rTensor C) ∘ₗ
            coact (R := R) (C := C) (M := M) :=
  Iff.rfl

/-- The signed co-Leibniz law evaluated on one comodule element. -/
theorem IsGradedCoderivationOver.coact_apply (h : IsGradedCoderivationOver G q b D)
    (x : M) :
    coact (R := R) (C := C) (M := M) (D x) =
      D.rTensor C (coact (R := R) (C := C) (M := M) x) +
        b.lTensor M ((G.koszulTwist q).rTensor C
          (coact (R := R) (C := C) (M := M) x)) := by
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using
    LinearMap.congr_fun h x

/-- If the coalgebra operator squares to zero and `(-1) ^ (q * r) = -1`, the square of a
degree-`r` comodule coderivation with twist `q` commutes with the coaction. In the bar
construction this makes
`D²` a comodule morphism, so its vanishing can be checked on its cogenerator component. -/
theorem IsGradedCoderivationOver.square_commutes_coact_of_odd {r : ℤ}
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
    apply TensorProduct.ext'
    intro x c
    simp only [LinearMap.add_apply, LinearMap.comp_apply, F, H, T,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.zero_apply]
    have hx := LinearMap.congr_fun hTF x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx
    dsimp only [T] at hx ⊢
    rw [hx]
    rw [← TensorProduct.smul_tmul']
    module
  have hHsq : H ∘ₗ H = 0 := by
    apply TensorProduct.ext'
    intro x c
    simp only [LinearMap.comp_apply, H, T, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul]
    have hc := LinearMap.congr_fun hb c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hc
    rw [hc]
    simp
  have hFsq : F ∘ₗ F = (D ∘ₗ D).rTensor C := by
    apply TensorProduct.ext'
    intro x c
    simp only [F, LinearMap.comp_apply, LinearMap.rTensor_tmul]
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
  h.square_commutes_coact_of_odd hD (by norm_num) hb

/-- The square of an odd homogeneous coderivation over a square-zero coalgebra operator
is a comodule endomorphism. -/
def IsGradedCoderivationOver.squareHomOfOdd {r : ℤ}
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) : Hom R C M M where
  toLinearMap := D ∘ₗ D
  map_coact := by
    simpa only [LinearMap.rTensor] using (h.square_commutes_coact_of_odd hD hqr hb).symm

/-- The square of an odd coderivation over a square-zero coalgebra operator is a
comodule endomorphism. -/
def IsGradedCoderivationOver.squareHom
    (h : IsGradedCoderivationOver G 1 b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece 1)
    (hb : b ∘ₗ b = 0) : Hom R C M M :=
  h.squareHomOfOdd hD (by norm_num) hb

/-- The underlying map of the odd square comodule endomorphism. -/
@[simp]
theorem IsGradedCoderivationOver.squareHomOfOdd_toLinearMap {r : ℤ}
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) :
    (h.squareHomOfOdd hD hqr hb).toLinearMap = D ∘ₗ D := by
  rw [squareHomOfOdd]

/-- The underlying map of the square comodule endomorphism is the square of the
coderivation. -/
@[simp]
theorem IsGradedCoderivationOver.squareHom_toLinearMap
    (h : IsGradedCoderivationOver G 1 b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece 1)
    (hb : b ∘ₗ b = 0) :
    (h.squareHom hD hb).toLinearMap = D ∘ₗ D :=
  by rw [squareHom, squareHomOfOdd_toLinearMap]

section Cofree

variable {N : Type*} [AddCommMonoid N] [Module R N]

attribute [local instance] Comodule.cofree

/-- On a cofree comodule, the square of an odd coderivation vanishes exactly when its
component obtained by applying the coalgebra counit vanishes.  This is the universal
property that reduces module Stasheff identities to Taylor components. -/
theorem IsGradedCoderivationOver.square_eq_zero_iff_counit_of_odd {r : ℤ}
    (G : InternalGrading R (N ⊗[R] C))
    (b : C →ₗ[R] C) (D : (N ⊗[R] C) →ₗ[R] N ⊗[R] C)
    (h : IsGradedCoderivationOver G q b D)
    (hD : LinearMap.IsHomogeneous D G.piece G.piece r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1)
    (hb : b ∘ₗ b = 0) :
    D ∘ₗ D = 0 ↔
      (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := C)).lTensor N ∘ₗ (D ∘ₗ D) = 0 := by
  let f : Hom R C (N ⊗[R] C) (N ⊗[R] C) := h.squareHomOfOdd hD hqr hb
  constructor
  · intro hsq
    rw [hsq]
    simp
  · intro hc
    have hz : f = 0 := (Hom.eq_zero_iff_counit f).2 (by
      simpa only [f, squareHomOfOdd_toLinearMap] using hc)
    have hlin := congrArg (fun g : Hom R C (N ⊗[R] C) (N ⊗[R] C) => g.toLinearMap) hz
    simpa only [f, squareHomOfOdd_toLinearMap, Hom.zero_toLinearMap] using hlin

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
  h.square_eq_zero_iff_counit_of_odd G b D hD (by norm_num) hb

end Cofree

end Comodule

end TauCeti
