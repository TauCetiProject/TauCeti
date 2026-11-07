/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.StarModuleCat.Basic
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import Mathlib.CategoryTheory.Equivalence

/-!
# Real descent as an equivalence of categories

Complexification, equipped with conjugation on its scalar factor, is an equivalence
from real modules to complex modules with conjugation. Morphisms on the complex side
are complex-linear maps commuting with conjugation; the inverse functor takes fixed
points. No finite-dimensionality or Hermitian pairing is needed.

`TauCeti.complexDescent` has unit `w ↦ 1 ⊗ w` and counit `z ⊗ w ↦ z • w`.
In particular it preserves the chosen real structure, not merely the underlying real
dimension. These functorial comparisons allow real field generators and their
complexifications to be transported without choosing a basis.

The counit is the fixed-point equivalence of
`TauCeti.LinearAlgebra.Complex.Conjugation`; see also Serre, *Linear Representations
of Finite Groups*, §13.2 for real forms.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace TauCeti

/-- Complexification with its canonical conjugation. The carrier is reducible so that
native tensor and fixed-point operations can be used on the functor's objects. -/
noncomputable abbrev complexificationFunctor : ModuleCat.{u} ℝ ⥤ StarModuleCat.{u} ℂ where
  obj W :=
    -- Do not install this on arbitrary tensors: the real factor may have another star.
    let starW : StarAddMonoid (ℂ ⊗[ℝ] W) := {
      star := tmulConj W
      star_involutive := tmulConj_involutive W
      star_add := map_add _ }
    { toModuleCat := ModuleCat.of ℂ (ℂ ⊗[ℝ] W)
      starAddMonoid := starW
      starModule := @StarModule.mk ℂ (ℂ ⊗[ℝ] W) _ starW.toStar _
        (fun z v => (tmulConj W).map_smulₛₗ z v) }
  map f := ⟨f.hom.baseChange ℂ, fun v => (tmulConj_baseChange f.hom v).symm⟩
  map_id W := by ext v; simp
  map_comp f g := by ext v; simp [LinearMap.baseChange_comp]

/-- On pure tensors, conjugation conjugates just the scalar factor. The star instance
is specified explicitly because the tensor carrier can carry other involutions. -/
@[simp] theorem _root_.ModuleCat.star_complexification_tmul (W : ModuleCat.{u} ℝ)
    (z : ℂ) (w : W) :
    @star (complexificationFunctor.obj W) (complexificationFunctor.obj W).starAddMonoid.toStar
      (z ⊗ₜ[ℝ] w) = (starRingEnd ℂ) z ⊗ₜ[ℝ] w :=
  tmulConj_tmul W z w

/-- Complexification acts on the real factor of pure tensors. -/
@[simp] theorem _root_.ModuleCat.complexificationFunctor_map_tmul
    {W W' : ModuleCat.{u} ℝ} (f : W ⟶ W') (z : ℂ) (w : W) :
    (complexificationFunctor.map f).hom (z ⊗ₜ[ℝ] w) = z ⊗ₜ[ℝ] f.hom w :=
  LinearMap.baseChange_tmul _ _ _

/-- The fixed-point real module of a complex module with conjugation. The carrier is
reducible to the native fixed-point submodule. -/
noncomputable abbrev realPointsFunctor : StarModuleCat.{u} ℂ ⥤ ModuleCat.{u} ℝ where
  obj V := ModuleCat.of ℝ (realPoints (starLinearEquiv ℂ (A := V)).toLinearMap)
  map f := ModuleCat.ofHom ((f.hom.restrictScalars ℝ).restrict fun v hv =>
    mem_realPoints.mpr ((f.map_star' v).symm.trans
      (congrArg f.hom (mem_realPoints.mp hv))))

/-- Taking real points restricts a morphism to its fixed vectors. -/
@[simp] theorem StarModuleCat.realPointsFunctor_map_apply
    {V V' : StarModuleCat.{u} ℂ} (f : V ⟶ V') (v : realPointsFunctor.obj V) :
    ((realPointsFunctor.map f).hom v : V') = f.hom v := rfl

/-- A real module is canonically the fixed points of its complexification. -/
noncomputable def _root_.ModuleCat.realPointsComplexificationEquiv (W : ModuleCat.{u} ℝ) :
    W ≃ₗ[ℝ] realPointsFunctor.obj (complexificationFunctor.obj W) :=
  LinearEquiv.ofLinearMap
    ((TensorProduct.mk ℝ ℂ W 1).codRestrict _ (fun w => by
      apply mem_realPoints.mpr
      simpa only [LinearEquiv.coe_coe, starLinearEquiv_apply, TensorProduct.mk_apply, map_one]
        using W.star_complexification_tmul (1 : ℂ) w))
    ((realPart W).comp (Submodule.subtype _))
    (by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      -- The functor's bundled module instances prevent simp from matching comp_apply.
      change (1 : ℂ) ⊗ₜ[ℝ] realPart W (v : ℂ ⊗[ℝ] W) = (v : ℂ ⊗[ℝ] W)
      obtain ⟨w, hw⟩ := (tmulConj_eq_self_iff W (v : ℂ ⊗[ℝ] W)).mp
        (mem_realPoints.mp v.property)
      simp [hw])
    (by ext w; exact realPart_one_tmul W w)

/-- The unit embeds a real vector as a tensor with scalar one. -/
@[simp] theorem _root_.ModuleCat.realPointsComplexificationEquiv_apply
    (W : ModuleCat.{u} ℝ) (w : W) :
    (W.realPointsComplexificationEquiv w : ℂ ⊗[ℝ] W) = 1 ⊗ₜ[ℝ] w := (rfl)

/-- The inverse unit reads off the real part of a fixed tensor. -/
@[simp] theorem _root_.ModuleCat.realPointsComplexificationEquiv_symm_apply
    (W : ModuleCat.{u} ℝ) (v : realPointsFunctor.obj (complexificationFunctor.obj W)) :
    W.realPointsComplexificationEquiv.symm v = realPart W (v : ℂ ⊗[ℝ] W) := (rfl)

-- These typed proofs keep the opaque star-linear equivalence and the chosen tensor star
-- visible to rewriting, rather than leaving proof arguments typed only up to unfolding.
private theorem starLinearEquiv_involutive (V : StarModuleCat.{u} ℂ) :
    Function.Involutive (starLinearEquiv ℂ (A := V)).toLinearMap := star_star

private theorem realPointsEquiv_star (V : StarModuleCat.{u} ℂ)
    (v : complexificationFunctor.obj (realPointsFunctor.obj V)) :
    realPointsEquiv (starLinearEquiv_involutive V)
        (@star _ (complexificationFunctor.obj (realPointsFunctor.obj V)).starAddMonoid.toStar v) =
      star (realPointsEquiv (starLinearEquiv_involutive V) v) :=
  realPointsEquiv_tmulConj (starLinearEquiv_involutive V) v

/-- The fixed-point equivalence is an isomorphism preserving conjugation. -/
noncomputable def StarModuleCat.complexificationRealPointsIso (V : StarModuleCat.{u} ℂ) :
    complexificationFunctor.obj (realPointsFunctor.obj V) ≅ V :=
  StarModuleCat.isoMk
    (realPointsEquiv (starLinearEquiv_involutive V)) (realPointsEquiv_star V)

/-- The counit evaluates a pure tensor by scalar multiplication. -/
@[simp] theorem StarModuleCat.complexificationRealPointsIso_hom_tmul
    (V : StarModuleCat.{u} ℂ) (z : ℂ) (v : realPointsFunctor.obj V) :
    V.complexificationRealPointsIso.hom.hom (z ⊗ₜ[ℝ] v) = z • (v : V) := by
  rw [complexificationRealPointsIso, StarModuleCat.isoMk_hom_hom]
  exact realPointsEquiv_tmul (starLinearEquiv_involutive V) z v

/-- The inverse counit is the inverse of the supplied fixed-point equivalence, so its
real/imaginary decomposition is given by `TauCeti.realPointsEquiv_symm_apply`. -/
@[simp] theorem StarModuleCat.complexificationRealPointsIso_inv_hom
    (V : StarModuleCat.{u} ℂ) :
    V.complexificationRealPointsIso.inv.hom =
      (realPointsEquiv (K := (starLinearEquiv ℂ (A := V)).toLinearMap)
        star_star).symm.toLinearMap := by
  exact StarModuleCat.isoMk_inv_hom _ _

/-- The natural identification of a real module with the real points of its
complexification. -/
noncomputable def complexificationUnitIso :
    𝟭 (ModuleCat.{u} ℝ) ≅ complexificationFunctor ⋙ realPointsFunctor :=
  NatIso.ofComponents
    (fun W => W.realPointsComplexificationEquiv.toModuleIso)
    (fun {W W'} f => by
      ext w
      apply Subtype.ext
      -- The component isomorphisms hide the subtype coercions from simp matching.
      change (W'.realPointsComplexificationEquiv (f.hom w) : ℂ ⊗[ℝ] W') =
        (complexificationFunctor.map f).hom (W.realPointsComplexificationEquiv w)
      rw [W'.realPointsComplexificationEquiv_apply, W.realPointsComplexificationEquiv_apply]
      exact (ModuleCat.complexificationFunctor_map_tmul f 1 w).symm)

@[simp] theorem _root_.ModuleCat.complexificationUnitIso_hom_app_hom (W : ModuleCat.{u} ℝ) :
    (complexificationUnitIso.hom.app W).hom = W.realPointsComplexificationEquiv.toLinearMap :=
  (rfl)

@[simp] theorem _root_.ModuleCat.complexificationUnitIso_inv_app_hom (W : ModuleCat.{u} ℝ) :
    (complexificationUnitIso.inv.app W).hom = W.realPointsComplexificationEquiv.symm.toLinearMap :=
  (rfl)

/-- The natural identification of a conjugate module with the complexification of
its real points. -/
noncomputable def complexificationCounitIso :
    realPointsFunctor ⋙ complexificationFunctor ≅ 𝟭 (StarModuleCat.{u} ℂ) :=
  NatIso.ofComponents StarModuleCat.complexificationRealPointsIso (fun f => by
    apply StarModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul z w =>
      simp only [Functor.comp_map, Functor.id_map, StarModuleCat.hom_comp,
        LinearMap.comp_apply]
      -- Simp cannot match the tensor formulas through the functor's chosen star instance;
      -- rw uses the definitional equality between these bundled module instances.
      rw [ModuleCat.complexificationFunctor_map_tmul (realPointsFunctor.map f) z w,
        StarModuleCat.complexificationRealPointsIso_hom_tmul,
        StarModuleCat.complexificationRealPointsIso_hom_tmul]
      simp
    | add v w hv hw => simp_all)

@[simp] theorem StarModuleCat.complexificationCounitIso_hom_app (V : StarModuleCat.{u} ℂ) :
    complexificationCounitIso.hom.app V = V.complexificationRealPointsIso.hom := (rfl)

@[simp] theorem StarModuleCat.complexificationCounitIso_inv_app (V : StarModuleCat.{u} ℂ) :
    complexificationCounitIso.inv.app V = V.complexificationRealPointsIso.inv := (rfl)

/-- Real modules are equivalent to complex modules equipped with conjugation.
The unit is `w ↦ 1 ⊗ w`, and the counit is `z ⊗ w ↦ z • w`. The equivalence
includes naturality and both triangle identities. -/
-- The dependent unit/counit comparison lemmas below require the functor projections
-- to compute when their types are checked; the equivalence itself is not an abbreviation.
@[expose] noncomputable def complexDescent : ModuleCat.{u} ℝ ≌ StarModuleCat.{u} ℂ where
  functor := complexificationFunctor
  inverse := realPointsFunctor
  unitIso := complexificationUnitIso
  counitIso := complexificationCounitIso
  functor_unitIso_comp W := by
    apply StarModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro z w
    -- Simp cannot match the tensor formulas through the functor's chosen star instance;
    -- rw uses the definitional equality between these bundled module instances.
    rw [StarModuleCat.hom_comp, LinearMap.comp_apply,
      StarModuleCat.complexificationCounitIso_hom_app,
      ModuleCat.complexificationFunctor_map_tmul,
      StarModuleCat.complexificationRealPointsIso_hom_tmul,
      ModuleCat.complexificationUnitIso_hom_app_hom]
    simp [W.realPointsComplexificationEquiv_apply, TensorProduct.smul_tmul']

@[simp] theorem complexDescent_functor :
    complexDescent.functor = complexificationFunctor := rfl

@[simp] theorem complexDescent_inverse :
    complexDescent.inverse = realPointsFunctor := rfl

@[simp] theorem complexDescent_unitIso :
    complexDescent.unitIso = complexificationUnitIso := rfl

@[simp] theorem complexDescent_counitIso :
    complexDescent.counitIso = complexificationCounitIso := rfl

end TauCeti
