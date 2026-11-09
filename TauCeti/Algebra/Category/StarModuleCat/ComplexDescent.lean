/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.StarModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.RealDescent

/-!
# Real descent for native star modules

The generic category `TauCeti.StarModuleCat`, specialized to complex scalars, is equivalent to
`TauCeti.RealStructureModuleCat`: an additive star compatible with complex conjugation is the
same data as an involutive conjugate-linear map. Both comparison functors leave underlying
modules and linear maps unchanged.

Composing this comparison with `TauCeti.RealStructureModuleCat.realDescentEquivalence` gives
real descent for native star modules. In particular, its unit is `w ↦ 1 ⊗ w` and its counit is
`z ⊗ w ↦ z • w`, without a choice of basis or a finite-dimensionality assumption. Naturality and
both triangle identities are inherited from that equivalence, rather than proved a second time.

See Serre, *Linear Representations of Finite Groups*, §13.2 for the real-form construction.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

namespace StarModuleCat

/-- Regard the native star as an involutive conjugate-linear map. -/
abbrev toRealStructure : StarModuleCat.{u} ℂ ⥤ RealStructureModuleCat.{u} where
  obj V := RealStructureModuleCat.of V
  map f := ⟨f.hom, f.map_star'⟩

/-- Install an involutive conjugate-linear map as the native star structure. -/
abbrev ofRealStructure : RealStructureModuleCat.{u} ⥤ StarModuleCat.{u} ℂ where
  obj V :=
    let starV : StarAddMonoid V := {
      star := V.conj
      star_involutive := V.involutive
      star_add := map_add _ }
    { toModuleCat := V.toModuleCat
      starAddMonoid := starV
      starModule := @StarModule.mk ℂ V _ starV.toStar _
        (fun z v => V.conj.map_smulₛₗ z v) }
  map f := ⟨f.hom, f.commutes⟩

@[simp] theorem toRealStructure_map_hom {V W : StarModuleCat.{u} ℂ} (f : V ⟶ W) :
    (toRealStructure.map f).hom = f.hom := rfl

@[simp] theorem ofRealStructure_obj_star (V : RealStructureModuleCat.{u}) (v : V) :
    @star (ofRealStructure.obj V) (ofRealStructure.obj V).starAddMonoid.toStar v = V.conj v :=
  rfl

@[simp] theorem ofRealStructure_map_hom {V W : RealStructureModuleCat.{u}} (f : V ⟶ W) :
    (ofRealStructure.map f).hom = f.hom := rfl

/-- Native complex star modules and modules with an explicit real structure are equivalent.
The unit and counit are the identity on underlying vectors. -/
-- Expose the equivalence so the composite descent carriers compute as tensors and subtypes.
@[expose] noncomputable def realStructureEquivalence :
    StarModuleCat.{u} ℂ ≌ RealStructureModuleCat.{u} where
  functor := toRealStructure
  inverse := ofRealStructure
  unitIso := NatIso.ofComponents
    (fun _ =>
      { hom := ofHom LinearMap.id (fun _ => rfl)
        inv := ofHom LinearMap.id (fun _ => rfl)
        hom_inv_id := by ext v; rfl
        inv_hom_id := by ext v; rfl })
    (fun f => by ext v; rfl)
  counitIso := NatIso.ofComponents
    (fun _ =>
      { hom := ⟨LinearMap.id, fun _ => rfl⟩
        inv := ⟨LinearMap.id, fun _ => rfl⟩
        hom_inv_id := by ext v; rfl
        inv_hom_id := by ext v; rfl })
    (fun f => by ext v; rfl)
  functor_unitIso_comp V := by ext v; rfl

end StarModuleCat

/-- Real descent for native complex star modules, obtained from the canonical real-descent
equivalence by identifying native star with an explicit conjugate-linear involution. -/
-- The dependent tensor formulas below require its functor and inverse to compute.
@[expose] noncomputable def complexDescent : ModuleCat.{u} ℝ ≌ StarModuleCat.{u} ℂ :=
  RealStructureModuleCat.realDescentEquivalence.trans StarModuleCat.realStructureEquivalence.symm

open scoped TensorProduct

/-- The unit embeds a real vector as a tensor with scalar one. -/
@[simp] theorem _root_.ModuleCat.complexDescent_unitIso_hom_apply
    (W : ModuleCat.{u} ℝ) (w : W) :
    dsimp% ((complexDescent.unitIso.hom.app W).hom w).val = 1 ⊗ₜ[ℝ] w := by
  change (RealStructureModuleCat.descentUnit.hom.app W w).val = _
  exact RealStructureModuleCat.descentUnit_hom_apply W w

/-- The counit is the canonical scalar-multiplication map. -/
@[simp] theorem StarModuleCat.complexDescent_counitIso_hom_tmul
    (V : StarModuleCat.{u} ℂ) (z : ℂ)
    (v : realPoints (starLinearEquiv ℂ (A := V)).toLinearMap) :
    dsimp% (complexDescent.counitIso.hom.app V).hom (z ⊗ₜ[ℝ] v) = z • (v : V) := by
  change (RealStructureModuleCat.descentCounit.hom.app
    (StarModuleCat.toRealStructure.obj V)).hom (z ⊗ₜ[ℝ] v) = _
  exact RealStructureModuleCat.descentCounit_hom_tmul (StarModuleCat.toRealStructure.obj V) z v

end TauCeti
