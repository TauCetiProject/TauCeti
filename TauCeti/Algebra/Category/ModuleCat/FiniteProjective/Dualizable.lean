/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DualTensorIhom
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Dualizable modules and finite projectivity

An `R`-module is dualizable in the symmetric monoidal category `ModuleCat R` exactly when it
is finite projective. Under the internal-Hom identification, the categorical dual-tensor map
is Mathlib's `dualTensorHom`; invertibility at the module itself supplies a finite dual basis,
and Mathlib's dual-basis criterion yields finite projectivity. Conversely, a finite projective
module has an invertible contraction, so the categorical dual-basis criterion constructs its
dual.

This is the affine algebraic criterion used in comparing finite locally free sheaves with
dualizable quasicoherent sheaves.

A finite projective module also forms an exact pairing with its algebraic dual `Module.Dual R M`
(`ModuleCat.exactPairingDual`), transported from the internal-Hom dual. Its evaluation is
`f ⊗ m ↦ f m`, and its coevaluation is a finite dual basis: under `M ⊗ M^∨ ≅ End M` it is the
identity.

A module identified with the ring has its internal Hom into the unit, which is its dual when it
is finite projective, identified with the ring by evaluation at the element corresponding to `1`
(`ModuleCat.ihomObjUnitIsoOfIsoSelf`).

The dual-basis criterion used here is from Mathlib's `LinearAlgebra.Contraction`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed TauCeti

namespace ModuleCat

universe u

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- A finite projective module is dualizable, with internal Hom into the tensor unit as a
canonical left dual. -/
noncomputable instance hasLeftDualOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] : HasLeftDual M := by
  have h : IsIso ((dualTensorIhom M).app M) :=
    (ModuleCat.isIso_dualTensorIhom_app_iff M M).2 dualTensorHom_bijective
  let hI : IsIso ((dualTensorIhom M).app M) := h
  refine { leftDual := (ihom M).obj (𝟙_ (ModuleCat.{u} R)), exact := ?_ }
  exact exactPairingOfIsIsoDualTensorIhom (Y := M)

/-- A finite projective module also has a right dual in the symmetric monoidal category
`ModuleCat R`. -/
noncomputable instance hasRightDualOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] : HasRightDual M :=
  BraidedCategory.hasRightDualOfHasLeftDual

/-- The chosen left dual of a finite projective module is its internal Hom into the unit. -/
@[simp]
theorem leftDual_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    HasLeftDual.leftDual (Y := M) = (ihom M).obj (𝟙_ (ModuleCat.{u} R)) :=
  rfl

/-- The chosen right dual of a finite projective module is its internal Hom into the unit. -/
@[simp]
theorem rightDual_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    HasRightDual.rightDual (X := M) = (ihom M).obj (𝟙_ (ModuleCat.{u} R)) :=
  rfl

/-- A finite projective module and its algebraic dual `Module.Dual R M` form an exact pairing,
transported from the internal-Hom right dual along `ModuleCat.homLinearEquiv`. Its evaluation is
`f ⊗ m ↦ f m` (`ModuleCat.evaluation_dual_tmul`). -/
noncomputable instance exactPairingDual [Module.Finite R M] [Module.Projective R M] :
    ExactPairing M (ModuleCat.of R (Module.Dual R M)) :=
  exactPairingCongrRight (X := M) (Y' := Mᘁ)
    (ModuleCat.homLinearEquiv.toModuleIso :
      (M ⟶[ModuleCat.{u} R] (𝟙_ (ModuleCat.{u} R))) ≅ ModuleCat.of R (Module.Dual R M)).symm

/-- The evaluation of the algebraic dual is `f ⊗ m ↦ f m`. -/
@[simp]
theorem evaluation_dual_tmul [Module.Finite R M] [Module.Projective R M]
    (f : Module.Dual R M) (m : M) :
    (ε_ M (ModuleCat.of R (Module.Dual R M))).hom (f ⊗ₜ m) = f m := by
  have : IsIso ((dualTensorIhom M).app M) :=
    (ModuleCat.isIso_dualTensorIhom_app_iff M M).2 dualTensorHom_bijective
  have he : @ExactPairing.evaluation _ _ _ _ _ (exactPairingOfIsIsoDualTensorIhom (Y := M)) =
      (ihom.ev M).app (𝟙_ _) := exactPairingOfIsIsoDualTensorIhom_evaluation
  -- Unfold the transported pairing: its evaluation identifies the dual with the internal Hom, then
  -- applies the braiding and the evaluation of the internal-Hom left dual. The right dual is built
  -- from that left dual by braiding, and `simp` cannot unfold these instance definitions.
  change ((ModuleCat.homLinearEquiv.toModuleIso :
      (ihom M).obj (𝟙_ (ModuleCat.{u} R)) ≅ ModuleCat.of R (Module.Dual R M)).inv ▷ M ≫
      (β_ ((ihom M).obj (𝟙_ (ModuleCat.{u} R))) M).hom ≫
      @ExactPairing.evaluation _ _ _ _ _ (exactPairingOfIsIsoDualTensorIhom (Y := M))).hom
      (f ⊗ₜ m) = f m
  rw [he, ModuleCat.ihom_ev_app]
  -- The remaining steps hold by definition: `homLinearEquiv.toModuleIso.inv` turns `f` into the
  -- morphism `ofHom f`, the braiding sends `ofHom f ⊗ m` to `m ⊗ ofHom f`, and the internal-Hom
  -- evaluation sends that to `(ofHom f).hom m = f m`. `simp` stops at the whiskering, whose apply
  -- lemma does not fire through the `ModuleCat.of` carrier of the dual.
  rfl

/-- The coevaluation of the algebraic dual is a finite dual basis: under the identification of
`M ⊗ M^∨` with `End M`, `m ⊗ f ↦ (x ↦ f x • m)`, it is the identity. -/
theorem dualTensorHom_comm_coevaluation_dual [Module.Finite R M] [Module.Projective R M] :
    dualTensorHom R M M (TensorProduct.comm R M (Module.Dual R M)
      ((η_ M (ModuleCat.of R (Module.Dual R M))).hom 1)) = LinearMap.id := by
  ext x
  have h := congrArg (fun φ ↦ (ρ_ M).hom.hom (φ.hom ((1 : R) ⊗ₜ x)))
    (ExactPairing.evaluation_coevaluation M (ModuleCat.of R (Module.Dual R M)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply,
    MonoidalCategory.leftUnitor_hom_apply, one_smul,
    MonoidalCategory.whiskerRight_apply] at h
  refine Eq.trans ?_ h
  generalize (η_ M (ModuleCat.of R (Module.Dual R M))).hom 1 = c
  induction c using TensorProduct.inductionOn with
  | tmul m f =>
    -- The associator and the whiskering act on pure tensors by definition
    -- (`ModuleCat.MonoidalCategory.associator_hom_apply`), but those lemmas do not fire here.
    change _ = (ρ_ M).hom.hom (m ⊗ₜ (ε_ M (ModuleCat.of R (Module.Dual R M))).hom (f ⊗ₜ x))
    rw [evaluation_dual_tmul]
    exact (MonoidalCategory.rightUnitor_hom_apply m (f x)).symm
  | add c c' hc hc' => simp_all [TensorProduct.add_tmul]

/-- A dualizable module is finite projective: its coevaluation gives a finite dual basis. -/
theorem finite_projective_of_hasLeftDual [HasLeftDual M] :
    Module.Finite R M ∧ Module.Projective R M := by
  have h : IsIso ((dualTensorIhom M).app M) := inferInstance
  have hb : Function.Bijective (dualTensorHom R M M) :=
    (ModuleCat.isIso_dualTensorIhom_app_iff M M).1 h
  have hmem : (1 : M →ₗ[R] M) ∈ (dualTensorHom R M M).range := hb.2 1
  exact ⟨Module.Finite.of_one_mem_range_dualTensorHom hmem,
    Module.Projective.of_one_mem_range_dualTensorHom hmem⟩

/-- A module with a right dual is finite projective. -/
theorem finite_projective_of_hasRightDual [HasRightDual M] :
    Module.Finite R M ∧ Module.Projective R M := by
  let _ : HasLeftDual M := BraidedCategory.hasLeftDualOfHasRightDual
  exact ModuleCat.finite_projective_of_hasLeftDual M

/-- An `R`-module is dualizable if and only if it is finite projective. -/
theorem nonempty_hasLeftDual_iff_finite_projective :
    Nonempty (HasLeftDual M) ↔ Module.Finite R M ∧ Module.Projective R M := by
  constructor
  · rintro ⟨h⟩
    let _ : HasLeftDual M := h
    exact ModuleCat.finite_projective_of_hasLeftDual M
  · rintro ⟨hfinite, hproj⟩
    let _ : Module.Finite R M := hfinite
    let _ : Module.Projective R M := hproj
    exact ⟨inferInstance⟩

/-- An `R`-module has a right dual if and only if it is finite projective. -/
theorem nonempty_hasRightDual_iff_finite_projective :
    Nonempty (HasRightDual M) ↔ Module.Finite R M ∧ Module.Projective R M := by
  constructor
  · rintro ⟨h⟩
    let _ : HasRightDual M := h
    exact ModuleCat.finite_projective_of_hasRightDual M
  · rintro ⟨hfinite, hproj⟩
    let _ : Module.Finite R M := hfinite
    let _ : Module.Projective R M := hproj
    exact ⟨inferInstance⟩

/-- A module `A` identified with the ring by `e` has its internal Hom into the unit identified
with the ring: a linear functional `φ` is sent to its value at the element of `A` corresponding to
`1`. When `A` is finite projective, this internal Hom is the right dual `Aᘁ` by definition
(`ModuleCat.rightDual_of_finite_projective`), and also the left dual. -/
noncomputable def ihomObjUnitIsoOfIsoSelf {A : ModuleCat.{u} R} (e : A ≅ ModuleCat.of R R) :
    (ihom A).obj (𝟙_ (ModuleCat.{u} R)) ≅ ModuleCat.of R R :=
  (ModuleCat.homLinearEquiv (S := R) ≪≫ₗ e.symm.toLinearEquiv.dualMap ≪≫ₗ
    LinearMap.ringLmapEquivSelf R R R).toModuleIso

/-- `ModuleCat.ihomObjUnitIsoOfIsoSelf e` evaluates a linear functional at the element
corresponding to `1`. -/
theorem ihomObjUnitIsoOfIsoSelf_hom_apply {A : ModuleCat.{u} R} (e : A ≅ ModuleCat.of R R)
    (φ : A ⟶ ModuleCat.of R R) :
    (ihomObjUnitIsoOfIsoSelf e).hom.hom φ = φ.hom (e.inv.hom 1) :=
  (rfl)

/-- The inverse of `ModuleCat.ihomObjUnitIsoOfIsoSelf e` sends `x` to the linear functional that
multiplies by `x` the scalar corresponding to its argument. -/
theorem ihomObjUnitIsoOfIsoSelf_inv_apply {A : ModuleCat.{u} R} (e : A ≅ ModuleCat.of R R)
    (x : R) (v : A) :
    ((ihomObjUnitIsoOfIsoSelf e).inv.hom x : A ⟶ ModuleCat.of R R).hom v = e.hom.hom v * x :=
  (rfl)

end ModuleCat
