/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Graded coderivations along a left coaction

`TauCeti.Comodule.IsGradedCoderivationOver` records the signed co-Leibniz law of an operator on a
*right* comodule.  Two-sided bar constructions also carry a *left* coaction: on the cofree
bicomodule `Tᶜ(sA) ⊗ sM ⊗ Tᶜ(sB)` the algebra `A` coacts by deconcatenating the left word.  This
file provides the left-handed counterpart of the co-Leibniz law and of the cofree uniqueness
statements, for an arbitrary linear map `δ : X → C ⊗ X` in the role of the left coaction.

An operator `D` on `X` is a graded coderivation along `δ` over an operator `b` on `C` when

`δ ∘ D = (b ⊗ 1) ∘ δ + (τ ⊗ D) ∘ δ`,

where `τ = G.koszulTwist r` is the Koszul twist of the coalgebra factor by the degree `r` of `D`:
in the second term `D` passes the coalgebra factor `c`, which costs the sign `(-1)^(r * |c|)`.

The cofree left comodule on `P` is `C ⊗ P` with coaction `c ⊗ p ↦ ∑ c₁ ⊗ (c₂ ⊗ p)`.  A map into it
whose coaction has the shape of a coderivation is recovered from its counit component
(`TauCeti.Comodule.eq_add_of_leftCofreeCoact_comp_eq`).  Consequently two coderivations along
`δ` over the same `b` agree after any coaction-compatible map `π` into a cofree left comodule as
soon as their counit components agree, and when `b` is square-zero and the Koszul sign is odd, the
square of a coderivation vanishes after `π` exactly when its counit component does.  Taking `π` to
be the identity of a cofree left comodule gives the left-handed analogue of
`TauCeti.Comodule.IsGradedCoderivationOver.eq_of_counit_comp_eq`; taking `π` to be the projection
of a cofree bicomodule onto its left cofree factor is how these statements are used for two-sided
bar constructions.

## Main definitions

* `TauCeti.Comodule.leftCofreeCoact`: the coaction of the cofree left comodule `C ⊗ P`.
* `TauCeti.Comodule.leftCofreeCounit`: the counit projection `C ⊗ P → P` of the cofree left
  comodule.
* `TauCeti.Comodule.leftCoactRTensor`: a left coaction on `Y`, acting on the left factor of
  `Y ⊗ N`.
* `TauCeti.Comodule.IsLeftGradedCoderivationOver`: the signed co-Leibniz law along a left
  coaction.

## Main results

* `TauCeti.Comodule.eq_add_of_leftCofreeCoact_comp_eq`: a map into a cofree left comodule is
  determined by the coalgebra part of its coaction and its counit component.
* `TauCeti.Comodule.IsLeftGradedCoderivationOver.square_commutes_coact_of_negOnePow_eq_neg_one`: the
  square of an odd coderivation over a square-zero operator commutes with the coaction.
* `TauCeti.Comodule.IsLeftGradedCoderivationOver.comp_eq_comp_of_counit_comp_eq`: coderivations
  over the same operator are determined by their counit components after a compatible map into a
  cofree left comodule.
* `IsLeftGradedCoderivationOver.comp_square_eq_zero_iff_counit_of_negOnePow_eq_neg_one` (in
  `TauCeti.Comodule`): the square-zero law can be checked on the counit component.
* `TauCeti.Comodule.leftCofreeCoact_comp_leftCofreeCoact` and
  `TauCeti.Comodule.leftCofreeCoact_comp_leftCoactRTensor_leftCofreeCoact`: the cofree left
  coaction, and its extension to the cofree bicomodule `(C ⊗ P) ⊗ N`, are coassociative.
* `TauCeti.Comodule.assoc_comp_rTensor_comp_assoc_symm_comp_lTensor_comul`: the extended left
  coaction commutes with the cofree right coaction of a second coalgebra.
* `TauCeti.Comodule.leftCofreeCoact_comp_map` and `TauCeti.Comodule.leftCofreeCoact_comp_rTensor`:
  how the cofree left coaction passes maps compatible with comultiplication and coderivations of
  the coalgebra factor.

These compatibilities are what is needed to check that a map on a cofree bicomodule, assembled
from a map to the cogenerators, satisfies the left co-Leibniz law.

The sign convention follows Getzler--Jones, *A-infinity algebras and the cyclic bar complex*,
Sections 1--2, and Keller, *Introduction to A-infinity algebras and modules*, Sections 3--5.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe uR uC uP uN uX uY

section Semiring

variable {R : Type uR} {C : Type uC} {P : Type uP} {N : Type uN} {Y : Type uY}
  [CommSemiring R] [AddCommMonoid C] [Module R C]
  [AddCommMonoid P] [Module R P] [AddCommMonoid N] [Module R N] [AddCommMonoid Y] [Module R Y]

/-! ### Left coactions extended by a right factor -/

variable (N) in
/-- A left coaction `δ` of `C` on `Y`, extended to `Y ⊗ N` by acting on the left factor:
`y ⊗ n ↦ ∑ y₋₁ ⊗ (y₀ ⊗ n)`.  For `δ` the cofree left coaction of `C ⊗ M`, this is the left
coaction of the cofree bicomodule `(C ⊗ M) ⊗ N`. -/
noncomputable def leftCoactRTensor (δ : Y →ₗ[R] C ⊗[R] Y) :
    Y ⊗[R] N →ₗ[R] C ⊗[R] (Y ⊗[R] N) :=
  (TensorProduct.assoc R C Y N).toLinearMap ∘ₗ δ.rTensor N

/-- The extended left coaction on a pure tensor. -/
@[simp]
theorem leftCoactRTensor_tmul (δ : Y →ₗ[R] C ⊗[R] Y) (y : Y) (n : N) :
    leftCoactRTensor N δ (y ⊗ₜ n) = TensorProduct.assoc R C Y N (δ y ⊗ₜ n) :=
  (rfl)

/-- Contracting the right factor `N` with a linear functional `φ` intertwines the extended left
coaction with the original one.  For `φ` the counit of a coalgebra coacting on the right, this says
that the projection of a cofree bicomodule onto its left cofree factor is a map of left
comodules. -/
theorem comp_rid_comp_lTensor_eq_lTensor_comp_leftCoactRTensor (δ : Y →ₗ[R] C ⊗[R] Y)
    (φ : N →ₗ[R] R) :
    δ ∘ₗ (TensorProduct.rid R Y).toLinearMap ∘ₗ φ.lTensor Y =
      ((TensorProduct.rid R Y).toLinearMap ∘ₗ φ.lTensor Y).lTensor C ∘ₗ
        leftCoactRTensor N δ := by
  refine TensorProduct.ext' fun y n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, map_smul, leftCoactRTensor_tmul]
  induction δ y using TensorProduct.inductionOn with
  | tmul c z => simp [TensorProduct.tmul_smul]
  | add x x' hx hx' => simp only [smul_add, TensorProduct.add_tmul, map_add, hx, hx']

/-- The extended left coaction is the original coaction on the left factor, reassociated. -/
theorem leftCoactRTensor_def (δ : Y →ₗ[R] C ⊗[R] Y) :
    leftCoactRTensor N δ = (TensorProduct.assoc R C Y N).toLinearMap ∘ₗ δ.rTensor N :=
  TensorProduct.ext' fun _ _ ↦ by simp

/-- The extended left coaction commutes with every map acting on the right factor. -/
theorem leftCoactRTensor_comp_lTensor {N' : Type*} [AddCommMonoid N'] [Module R N']
    (δ : Y →ₗ[R] C ⊗[R] Y) (k : N →ₗ[R] N') :
    leftCoactRTensor N' δ ∘ₗ k.lTensor Y = (k.lTensor Y).lTensor C ∘ₗ leftCoactRTensor N δ := by
  refine TensorProduct.ext' fun y n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, leftCoactRTensor_tmul]
  induction δ y using TensorProduct.inductionOn with
  | tmul c z => simp
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

/-- The extended left coaction after a map `g` on the left factor is the original coaction after
`g`, reassociated. -/
theorem leftCoactRTensor_comp_rTensor {X : Type*} [AddCommMonoid X] [Module R X]
    (δ : Y →ₗ[R] C ⊗[R] Y) (g : X →ₗ[R] Y) :
    leftCoactRTensor N δ ∘ₗ g.rTensor N =
      (TensorProduct.assoc R C Y N).toLinearMap ∘ₗ (δ ∘ₗ g).rTensor N := by
  refine TensorProduct.ext' fun x n ↦ ?_
  simp

section Bicomodule

variable {E : Type*} {Y' : Type*} {C' : Type*} [AddCommMonoid E] [Module R E] [Coalgebra R E]
  [AddCommMonoid Y'] [Module R Y'] [AddCommMonoid C'] [Module R C']

/-- The extended left coaction of `Y ⊗ E` commutes with the cofree right coaction
`y ⊗ v ↦ ∑ (y ⊗ v₁) ⊗ v₂` of `E`: lifting `τ ⊗ g` along the cofree right coaction after the left
coaction is lifting `g` along the cofree right coaction and then applying `τ ⊗ -`. -/
theorem assoc_comp_rTensor_comp_assoc_symm_comp_lTensor_comul (δ : Y →ₗ[R] C ⊗[R] Y)
    (τ : C →ₗ[R] C') (g : Y ⊗[R] E →ₗ[R] Y') :
    (TensorProduct.assoc R C' Y' E).toLinearMap ∘ₗ
        (TensorProduct.map τ g ∘ₗ leftCoactRTensor E δ).rTensor E ∘ₗ
          (TensorProduct.assoc R Y E E).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor Y =
      TensorProduct.map τ (g.rTensor E ∘ₗ (TensorProduct.assoc R Y E E).symm.toLinearMap ∘ₗ
          Coalgebra.comul.lTensor Y) ∘ₗ
        leftCoactRTensor E δ := by
  refine TensorProduct.ext' fun y v ↦ ?_
  -- Both sides are the following expression in `δ y` and the comultiplication of `v`.
  let Θ : (C ⊗[R] Y) ⊗[R] (E ⊗[R] E) →ₗ[R] C' ⊗[R] (Y' ⊗[R] E) :=
    (TensorProduct.assoc R C' Y' E).toLinearMap ∘ₗ
      (TensorProduct.map τ g ∘ₗ (TensorProduct.assoc R C Y E).toLinearMap).rTensor E ∘ₗ
        (TensorProduct.assoc R (C ⊗[R] Y) E E).symm.toLinearMap
  have hl : ∀ s : E ⊗[R] E,
      (TensorProduct.assoc R C' Y' E)
          ((TensorProduct.map τ g ∘ₗ leftCoactRTensor E δ).rTensor E
            ((TensorProduct.assoc R Y E E).symm (y ⊗ₜ s))) = Θ (δ y ⊗ₜ s) := by
    intro s
    induction s using TensorProduct.inductionOn with
    | tmul a b => simp [Θ]
    | add x x' hx hx' => simp only [TensorProduct.tmul_add, map_add, hx, hx']
  have hr : ∀ t : C ⊗[R] Y,
      TensorProduct.map τ (g.rTensor E ∘ₗ (TensorProduct.assoc R Y E E).symm.toLinearMap ∘ₗ
          Coalgebra.comul.lTensor Y) (TensorProduct.assoc R C Y E (t ⊗ₜ v)) =
        Θ (t ⊗ₜ Coalgebra.comul v) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c z =>
      simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
        LinearMap.lTensor_tmul]
      induction Coalgebra.comul (R := R) v using TensorProduct.inductionOn with
      | tmul a b => simp [Θ]
      | add x x' hx hx' =>
        simp only [TensorProduct.tmul_add, map_add, hx, hx']
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, leftCoactRTensor_tmul, hr]
  exact hl _

/-- The extended left coaction of `Y ⊗ E`, followed by `b` on the coalgebra factor and the counit
of `E`, and lifted along the cofree right coaction of `E`, is `b` applied after the extended left
coaction. -/
theorem assoc_comp_rTensor_map_counit_comp_assoc_symm_comp_lTensor_comul (δ : Y →ₗ[R] C ⊗[R] Y)
    (b : C →ₗ[R] C') :
    (TensorProduct.assoc R C' Y E).toLinearMap ∘ₗ
        (TensorProduct.map b ((TensorProduct.rid R Y).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := E)).lTensor Y) ∘ₗ leftCoactRTensor E δ).rTensor E ∘ₗ
          (TensorProduct.assoc R Y E E).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor Y =
      b.rTensor (Y ⊗[R] E) ∘ₗ leftCoactRTensor E δ := by
  rw [assoc_comp_rTensor_comp_assoc_symm_comp_lTensor_comul]
  have hid : ((TensorProduct.rid R Y).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := E)).lTensor Y).rTensor E ∘ₗ
        (TensorProduct.assoc R Y E E).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor Y =
      LinearMap.id := by
    refine TensorProduct.ext' fun y v ↦ ?_
    have key : ∀ s : E ⊗[R] E,
        ((TensorProduct.rid R Y).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := E)).lTensor Y).rTensor E
            ((TensorProduct.assoc R Y E E).symm (y ⊗ₜ s)) =
          y ⊗ₜ TensorProduct.lid R E ((Coalgebra.counit (R := R) (A := E)).rTensor E s) := by
      intro s
      induction s using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.smul_tmul]
      | add x x' hx hx' => simp only [TensorProduct.tmul_add, map_add, hx, hx']
    simp [key]
  rw [hid, ← LinearMap.rTensor_def]

end Bicomodule

/-! ### The cofree left comodule -/

variable [Coalgebra R C]

variable (R C P) in
/-- The coaction of the cofree left `C`-comodule `C ⊗ P`: comultiplication on the coalgebra factor
followed by reassociation, `c ⊗ p ↦ ∑ c₁ ⊗ (c₂ ⊗ p)`. -/
noncomputable def leftCofreeCoact : C ⊗[R] P →ₗ[R] C ⊗[R] (C ⊗[R] P) :=
  (TensorProduct.assoc R C C P).toLinearMap ∘ₗ Coalgebra.comul.rTensor P

/-- The cofree left coaction on a pure tensor. -/
@[simp]
theorem leftCofreeCoact_tmul (c : C) (p : P) :
    leftCofreeCoact R C P (c ⊗ₜ p) = TensorProduct.assoc R C C P (Coalgebra.comul c ⊗ₜ p) :=
  (rfl)

variable (R C P) in
/-- The counit projection of the cofree left `C`-comodule `C ⊗ P` onto its cogenerators:
`c ⊗ p ↦ ε(c) • p`. -/
noncomputable def leftCofreeCounit : C ⊗[R] P →ₗ[R] P :=
  (TensorProduct.lid R P).toLinearMap ∘ₗ (Coalgebra.counit (R := R) (A := C)).rTensor P

/-- The cofree counit projection applies the counit to the coalgebra factor and then the left
unitor. -/
theorem leftCofreeCounit_def :
    leftCofreeCounit R C P =
      (TensorProduct.lid R P).toLinearMap ∘ₗ (Coalgebra.counit (R := R) (A := C)).rTensor P :=
  (rfl)

/-- The cofree counit projection on a pure tensor. -/
@[simp]
theorem leftCofreeCounit_tmul (c : C) (p : P) :
    leftCofreeCounit R C P (c ⊗ₜ p) = Coalgebra.counit (R := R) c • p :=
  (rfl)

/-- Applying the counit to the inner coalgebra factor of the cofree left coaction recovers the
original element. -/
@[simp]
theorem lTensor_leftCofreeCounit_comp_leftCofreeCoact :
    (leftCofreeCounit R C P).lTensor C ∘ₗ leftCofreeCoact R C P = LinearMap.id := by
  have hx (x : C ⊗[R] C) (p : P) :
      (leftCofreeCounit R C P).lTensor C (TensorProduct.assoc R C C P (x ⊗ₜ p)) =
        TensorProduct.rid R C ((Coalgebra.counit (R := R) (A := C)).lTensor C x) ⊗ₜ p := by
    induction x using TensorProduct.inductionOn with
    | tmul c d => simp [leftCofreeCounit_def, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  refine TensorProduct.ext' fun c p ↦ ?_
  rw [LinearMap.comp_apply, leftCofreeCoact_tmul, hx, ← LinearMap.comp_apply
    ((Coalgebra.counit (R := R) (A := C)).lTensor C), Coalgebra.lTensor_counit_comp_comul]
  simp

/-- A map `g` into the cofree left comodule `C ⊗ P` whose coaction is `K + (τ ⊗ g) ∘ δ` is
recovered from `K` and from its counit component.  With `K = 0` and `τ = id` this is the uniqueness
half of the universal property of the cofree left comodule; for a coderivation, `K` is the term in
which the coalgebra operator acts. -/
theorem eq_add_of_leftCofreeCoact_comp_eq (δ : Y →ₗ[R] C ⊗[R] Y) (τ : C →ₗ[R] C)
    {g : Y →ₗ[R] C ⊗[R] P} {K : Y →ₗ[R] C ⊗[R] (C ⊗[R] P)}
    (h : leftCofreeCoact R C P ∘ₗ g = K + TensorProduct.map τ g ∘ₗ δ) :
    g = (leftCofreeCounit R C P).lTensor C ∘ₗ K +
        TensorProduct.map τ (leftCofreeCounit R C P ∘ₗ g) ∘ₗ δ := by
  calc
    g = ((leftCofreeCounit R C P).lTensor C ∘ₗ leftCofreeCoact R C P) ∘ₗ g := by
      rw [lTensor_leftCofreeCounit_comp_leftCofreeCoact, LinearMap.id_comp]
    _ = (leftCofreeCounit R C P).lTensor C ∘ₗ K +
        TensorProduct.map τ (leftCofreeCounit R C P ∘ₗ g) ∘ₗ δ := by
      rw [LinearMap.comp_assoc, h, LinearMap.comp_add, ← LinearMap.comp_assoc,
        LinearMap.lTensor_comp_map]

section CofreeLeftComodule

variable {X : Type*} [AddCommMonoid X] [Module R X]

/-- The cofree left coaction is comultiplication followed by reassociation. -/
theorem leftCofreeCoact_def :
    leftCofreeCoact R C P =
      (TensorProduct.assoc R C C P).toLinearMap ∘ₗ Coalgebra.comul.rTensor P :=
  TensorProduct.ext' fun _ _ ↦ by simp

/-- If `τ` is compatible with comultiplication, the cofree left coaction intertwines `τ ⊗ f` with
`τ ⊗ (τ ⊗ f)`. -/
theorem leftCofreeCoact_comp_map {τ : C →ₗ[R] C}
    (hτ : Coalgebra.comul ∘ₗ τ = TensorProduct.map τ τ ∘ₗ Coalgebra.comul) (f : X →ₗ[R] P) :
    leftCofreeCoact R C P ∘ₗ TensorProduct.map τ f =
      TensorProduct.map τ (TensorProduct.map τ f) ∘ₗ leftCofreeCoact R C X := by
  refine TensorProduct.ext' fun c x ↦ ?_
  have hc := LinearMap.congr_fun hτ c
  simp only [LinearMap.comp_apply] at hc
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, leftCofreeCoact_tmul, hc]
  induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

/-- The cofree left coaction of `C ⊗ P` is coassociative. -/
theorem leftCofreeCoact_comp_leftCofreeCoact :
    leftCofreeCoact R C (C ⊗[R] P) ∘ₗ leftCofreeCoact R C P =
      (leftCofreeCoact R C P).lTensor C ∘ₗ leftCofreeCoact R C P := by
  refine TensorProduct.ext' fun c p ↦ ?_
  -- Both sides are `Φ` applied to the two sides of coassociativity, with `Φ` attaching `p`.
  let Φ : C ⊗[R] (C ⊗[R] C) →ₗ[R] C ⊗[R] (C ⊗[R] (C ⊗[R] P)) :=
    (((TensorProduct.mk R C P).flip p).lTensor C).lTensor C
  have hl : ∀ t : C ⊗[R] C, leftCofreeCoact R C (C ⊗[R] P) (TensorProduct.assoc R C C P (t ⊗ₜ p)) =
      Φ (TensorProduct.assoc R C C C (Coalgebra.comul.rTensor C t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.assoc_tmul, leftCofreeCoact_tmul, LinearMap.rTensor_tmul]
      induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
      | tmul x y => simp [Φ]
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  have hr : ∀ t : C ⊗[R] C,
      (leftCofreeCoact R C P).lTensor C (TensorProduct.assoc R C C P (t ⊗ₜ p)) =
      Φ (Coalgebra.comul.lTensor C t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, leftCofreeCoact_tmul]
      induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
      | tmul x y => simp [Φ]
      | add x x' hx hx' =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hx']
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  have h := LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := C)) c
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  simp only [LinearMap.comp_apply, leftCofreeCoact_tmul, hl, hr, h]

/-- If `b` satisfies the co-Leibniz law `Δ ∘ b = (b ⊗ 1) ∘ Δ + (τ ⊗ b) ∘ Δ` on `C`, then `b ⊗ 1`
satisfies the corresponding law for the cofree left coaction of `C ⊗ P`. -/
theorem leftCofreeCoact_comp_rTensor {b τ : C →ₗ[R] C}
    (hb : Coalgebra.comul ∘ₗ b =
      b.rTensor C ∘ₗ Coalgebra.comul + TensorProduct.map τ b ∘ₗ Coalgebra.comul) :
    leftCofreeCoact R C P ∘ₗ b.rTensor P =
      b.rTensor (C ⊗[R] P) ∘ₗ leftCofreeCoact R C P +
        TensorProduct.map τ (b.rTensor P) ∘ₗ leftCofreeCoact R C P := by
  refine TensorProduct.ext' fun c p ↦ ?_
  have hc := LinearMap.congr_fun hb c
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at hc
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    leftCofreeCoact_tmul, hc, TensorProduct.add_tmul, map_add]
  congr 1
  · induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  · induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

/-- If `τ` preserves the counit, the counit projection after `τ ⊗ f` is `f` after the counit
projection. -/
theorem leftCofreeCounit_comp_map {τ : C →ₗ[R] C}
    (hτ : Coalgebra.counit ∘ₗ τ = Coalgebra.counit) (f : X →ₗ[R] P) :
    leftCofreeCounit R C P ∘ₗ TensorProduct.map τ f = f ∘ₗ leftCofreeCounit R C X := by
  refine TensorProduct.ext' fun c x ↦ ?_
  have hc := LinearMap.congr_fun hτ c
  simp only [LinearMap.comp_apply] at hc
  simp [hc]

/-- The extension of the cofree left coaction of `C ⊗ P` by a right factor is a section of the
counit projection. -/
theorem leftCofreeCounit_comp_leftCoactRTensor_leftCofreeCoact :
    leftCofreeCounit R C ((C ⊗[R] P) ⊗[R] N) ∘ₗ leftCoactRTensor N (leftCofreeCoact R C P) =
      LinearMap.id := by
  refine TensorProduct.ext' fun y n ↦ ?_
  induction y using TensorProduct.inductionOn with
  | tmul c p =>
    have key : ∀ t : C ⊗[R] C,
        leftCofreeCounit R C ((C ⊗[R] P) ⊗[R] N)
            (TensorProduct.assoc R C (C ⊗[R] P) N (TensorProduct.assoc R C C P (t ⊗ₜ p) ⊗ₜ n)) =
          (TensorProduct.lid R C ((Coalgebra.counit (R := R) (A := C)).rTensor C t) ⊗ₜ p) ⊗ₜ n := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.smul_tmul']
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
    simp [key]
  | add x x' hx hx' =>
    simp only [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.add_tmul,
      map_add] at hx hx' ⊢
    rw [hx, hx']

/-- On the cofree bicomodule `(C ⊗ P) ⊗ N`, a map `k` on the right factor after a map `τ ⊗ h` on the
left cofree factor intertwines the extended left coactions with `τ ⊗ -`, provided `τ` is
compatible with comultiplication. -/
theorem leftCoactRTensor_comp_lTensor_comp_rTensor_map {P' N' : Type*} [AddCommMonoid P']
    [Module R P'] [AddCommMonoid N'] [Module R N'] {τ : C →ₗ[R] C}
    (hτ : Coalgebra.comul ∘ₗ τ = TensorProduct.map τ τ ∘ₗ Coalgebra.comul) (h : P →ₗ[R] P')
    (k : N →ₗ[R] N') :
    leftCoactRTensor N' (leftCofreeCoact R C P') ∘ₗ
        (k.lTensor (C ⊗[R] P') ∘ₗ (TensorProduct.map τ h).rTensor N) =
      TensorProduct.map τ (k.lTensor (C ⊗[R] P') ∘ₗ (TensorProduct.map τ h).rTensor N) ∘ₗ
        leftCoactRTensor N (leftCofreeCoact R C P) := by
  refine TensorProduct.ext' fun y n ↦ ?_
  induction y using TensorProduct.inductionOn with
  | tmul c p =>
    have hc := LinearMap.congr_fun hτ c
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.map_tmul, leftCoactRTensor_tmul, leftCofreeCoact_tmul, hc]
    induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | add x x' hx hx' =>
    simp only [LinearMap.comp_apply, TensorProduct.add_tmul, map_add] at hx hx' ⊢
    rw [hx, hx']

/-- A coassociative left coaction stays coassociative when extended by a right factor. -/
theorem leftCofreeCoact_comp_leftCoactRTensor {δ : Y →ₗ[R] C ⊗[R] Y}
    (hδ : leftCofreeCoact R C Y ∘ₗ δ = δ.lTensor C ∘ₗ δ) :
    leftCofreeCoact R C (Y ⊗[R] N) ∘ₗ leftCoactRTensor N δ =
      (leftCoactRTensor N δ).lTensor C ∘ₗ leftCoactRTensor N δ := by
  refine TensorProduct.ext' fun y n ↦ ?_
  let Ψ : C ⊗[R] (C ⊗[R] Y) →ₗ[R] C ⊗[R] (C ⊗[R] (Y ⊗[R] N)) :=
    (((TensorProduct.mk R Y N).flip n).lTensor C).lTensor C
  have hl : ∀ t : C ⊗[R] Y,
      leftCofreeCoact R C (Y ⊗[R] N) (TensorProduct.assoc R C Y N (t ⊗ₜ n)) =
        Ψ (leftCofreeCoact R C Y t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c z =>
      simp only [TensorProduct.assoc_tmul, leftCofreeCoact_tmul]
      induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
      | tmul a b => simp [Ψ]
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  have hr : ∀ t : C ⊗[R] Y,
      (leftCoactRTensor N δ).lTensor C (TensorProduct.assoc R C Y N (t ⊗ₜ n)) =
        Ψ (δ.lTensor C t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c z =>
      simp only [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, leftCoactRTensor_tmul]
      induction δ z using TensorProduct.inductionOn with
      | tmul a b => simp [Ψ]
      | add x x' hx hx' =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hx']
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  have h := LinearMap.congr_fun hδ y
  simp only [LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, leftCoactRTensor_tmul, hl, hr, h]

/-- The extension of the cofree left coaction of `C ⊗ P` by a right factor is coassociative. -/
theorem leftCofreeCoact_comp_leftCoactRTensor_leftCofreeCoact :
    leftCofreeCoact R C ((C ⊗[R] P) ⊗[R] N) ∘ₗ leftCoactRTensor N (leftCofreeCoact R C P) =
      (leftCoactRTensor N (leftCofreeCoact R C P)).lTensor C ∘ₗ
        leftCoactRTensor N (leftCofreeCoact R C P) :=
  leftCofreeCoact_comp_leftCoactRTensor leftCofreeCoact_comp_leftCofreeCoact

end CofreeLeftComodule

end Semiring

/-! ### Coderivations along a left coaction -/

variable {R : Type uR} {C : Type uC} {P : Type uP} {X : Type uX}
  [CommRing R] [AddCommMonoid C] [Module R C]
  [AddCommMonoid P] [Module R P] [AddCommMonoid X] [Module R X]

/-- The signed co-Leibniz law for an endomorphism `D` of a module `X` with a left coaction `δ` of
`C`, over an operator `b` on the coalgebra: `δ ∘ D = (b ⊗ 1) ∘ δ + (τ ⊗ D) ∘ δ` with
`τ = G.koszulTwist r`.  The parameter `r` is the degree of `D`, and `τ` records the Koszul sign
`(-1)^(r * |c|)` acquired when `D` passes the coalgebra factor `c`.  Homogeneity of `D` and the
comodule axioms of `δ` are separate conditions. -/
def IsLeftGradedCoderivationOver (δ : X →ₗ[R] C ⊗[R] X) (G : InternalGrading R C) (r : ℤ)
    (b : C →ₗ[R] C) (D : X →ₗ[R] X) : Prop :=
  δ ∘ₗ D = b.rTensor X ∘ₗ δ + TensorProduct.map (G.koszulTwist r) D ∘ₗ δ

variable {δ : X →ₗ[R] C ⊗[R] X} {G : InternalGrading R C} {r : ℤ} {b : C →ₗ[R] C}
  {D E : X →ₗ[R] X}

/-- The left co-Leibniz law evaluated on one element. -/
theorem IsLeftGradedCoderivationOver.coact_apply (h : IsLeftGradedCoderivationOver δ G r b D)
    (x : X) :
    δ (D x) = b.rTensor X (δ x) + TensorProduct.map (G.koszulTwist r) D (δ x) := by
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using LinearMap.congr_fun h x

/-- The left co-Leibniz law can be checked on individual elements. -/
theorem isLeftGradedCoderivationOver_iff_coact_apply :
    IsLeftGradedCoderivationOver δ G r b D ↔
      ∀ x : X, δ (D x) = b.rTensor X (δ x) + TensorProduct.map (G.koszulTwist r) D (δ x) :=
  ⟨IsLeftGradedCoderivationOver.coact_apply, fun h ↦ LinearMap.ext fun x ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.add_apply] using h x⟩

/-- If the coalgebra operator `b` is square-zero and homogeneous of degree `q`, and
`(-1) ^ (r * q) = -1`, then the square of a degree-`r` coderivation along `δ` over `b` commutes
with `δ`: the two cross terms cancel by the Koszul sign, and the twist squares to the identity. -/
theorem IsLeftGradedCoderivationOver.square_commutes_coact_of_negOnePow_eq_neg_one {q : ℤ}
    (h : IsLeftGradedCoderivationOver δ G r b D)
    (hb : LinearMap.IsHomogeneous b G.piece G.piece q)
    (hrq : (((r * q).negOnePow : ℤ) : R) = -1) (hb2 : b ∘ₗ b = 0) :
    δ ∘ₗ (D ∘ₗ D) = (D ∘ₗ D).lTensor C ∘ₗ δ := by
  have hτb : G.koszulTwist r ∘ₗ b = (-1 : R) • (b ∘ₗ G.koszulTwist r) := by
    rw [hb.koszulTwist_comp r, hrq]
  have h' : δ ∘ₗ D = (b.rTensor X + TensorProduct.map (G.koszulTwist r) D) ∘ₗ δ := by
    rw [h, LinearMap.add_comp]
  have hstep : (b.rTensor X + TensorProduct.map (G.koszulTwist r) D) ∘ₗ
      (b.rTensor X + TensorProduct.map (G.koszulTwist r) D) = (D ∘ₗ D).lTensor C := by
    simp only [LinearMap.comp_add, LinearMap.add_comp, ← LinearMap.rTensor_comp, hb2,
      LinearMap.rTensor_zero, LinearMap.rTensor_comp_map, LinearMap.map_comp_rTensor,
      ← TensorProduct.map_comp, hτb, G.koszulTwist_comp_self, zero_add]
    rw [TensorProduct.map_smul_left, LinearMap.lTensor_def]
    module
  rw [← LinearMap.comp_assoc D D δ, h', LinearMap.comp_assoc D δ, h', ← LinearMap.comp_assoc δ,
    hstep]

/-! ### Coderivations into cofree left comodules -/

variable [Coalgebra R C]

variable {π : X →ₗ[R] C ⊗[R] P}

/-- Coderivations along `δ` over the same operator agree after a map `π` into a cofree left
comodule intertwining `δ` with the cofree coaction, as soon as their counit components after `π`
agree.  For `π` the identity of a cofree left comodule this says that a coderivation is determined
by its counit component. -/
theorem IsLeftGradedCoderivationOver.comp_eq_comp_of_counit_comp_eq
    (hπ : leftCofreeCoact R C P ∘ₗ π = π.lTensor C ∘ₗ δ)
    (hD : IsLeftGradedCoderivationOver δ G r b D) (hE : IsLeftGradedCoderivationOver δ G r b E)
    (hcounit : leftCofreeCounit R C P ∘ₗ π ∘ₗ D = leftCofreeCounit R C P ∘ₗ π ∘ₗ E) :
    π ∘ₗ D = π ∘ₗ E := by
  have hcoact {F : X →ₗ[R] X} (hF : IsLeftGradedCoderivationOver δ G r b F) :
      leftCofreeCoact R C P ∘ₗ (π ∘ₗ F) =
        TensorProduct.map b π ∘ₗ δ + TensorProduct.map (G.koszulTwist r) (π ∘ₗ F) ∘ₗ δ := by
    rw [← LinearMap.comp_assoc, hπ, LinearMap.comp_assoc, hF, LinearMap.comp_add,
      ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor,
      LinearMap.lTensor_comp_map]
  rw [eq_add_of_leftCofreeCoact_comp_eq δ _ (hcoact hD), hcounit,
    ← eq_add_of_leftCofreeCoact_comp_eq δ _ (hcoact hE)]

/-- If the coalgebra operator `b` is square-zero and homogeneous of degree `q`, and
`(-1) ^ (r * q) = -1`, then the square of a degree-`r` coderivation along `δ` vanishes after a
coaction-compatible map `π` into a cofree left comodule exactly when its counit component after `π`
vanishes. -/
theorem IsLeftGradedCoderivationOver.comp_square_eq_zero_iff_counit_of_negOnePow_eq_neg_one {q : ℤ}
    (hπ : leftCofreeCoact R C P ∘ₗ π = π.lTensor C ∘ₗ δ)
    (h : IsLeftGradedCoderivationOver δ G r b D)
    (hb : LinearMap.IsHomogeneous b G.piece G.piece q)
    (hrq : (((r * q).negOnePow : ℤ) : R) = -1) (hb2 : b ∘ₗ b = 0) :
    π ∘ₗ (D ∘ₗ D) = 0 ↔ leftCofreeCounit R C P ∘ₗ π ∘ₗ (D ∘ₗ D) = 0 := by
  refine ⟨fun h0 ↦ by rw [h0, LinearMap.comp_zero], fun h0 ↦ ?_⟩
  have hcoact : leftCofreeCoact R C P ∘ₗ (π ∘ₗ (D ∘ₗ D)) =
      0 + TensorProduct.map LinearMap.id (π ∘ₗ (D ∘ₗ D)) ∘ₗ δ := by
    rw [← LinearMap.comp_assoc, hπ, LinearMap.comp_assoc,
      h.square_commutes_coact_of_negOnePow_eq_neg_one hb hrq hb2, ← LinearMap.comp_assoc,
      ← LinearMap.lTensor_comp, zero_add, LinearMap.lTensor_def]
  rw [eq_add_of_leftCofreeCoact_comp_eq δ _ hcoact, LinearMap.comp_zero, zero_add, h0]
  simp

end Comodule

end TauCeti
