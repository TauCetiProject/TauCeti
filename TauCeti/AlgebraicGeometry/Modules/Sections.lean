/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Local sections as modules over global functions

Restricting global functions to an open equips its sections with a common scalar ring.
Restriction maps are linear over that ring, so differences of restrictions and their
cokernels can be formed as modules, even when the opens have different coordinate rings.
For a scheme over a commutative ring, this action is compatible with that of the base ring
(`AlgebraicGeometry.Scheme.Modules.isScalarTower_sections`). Along a morphism over the base,
`pushforwardSectionsBaseLinearEquiv` identifies sections of a pushforward with those on the
preimage as modules over the base ring.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- Sections over any open are a module over global functions, by restriction of scalars. -/
instance (priority := 900) sectionsGlobalModule (M : X.Modules) (U : X.Opens) :
    Module Γ(X, ⊤) Γ(M, U) :=
  Module.compHom Γ(M, U) (X.presheaf.map U.leTop.op).hom

/-- A global function acts on local sections by its restriction to the open. -/
lemma sectionsGlobal_smul (M : X.Modules) (U : X.Opens)
    (r : Γ(X, ⊤)) (s : Γ(M, U)) :
    r • s = X.presheaf.map U.leTop.op r • s :=
  (rfl)

/-- Restriction of local sections is linear over global functions. -/
def sectionsRestrictionLinear (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    Γ(M, V) →ₗ[Γ(X, ⊤)] Γ(M, U) where
  toFun := M.presheaf.map i.op
  map_add' := map_add _
  map_smul' r s := by
    simp only [sectionsGlobal_smul, RingHom.id_apply, M.map_smul]
    congr 1
    rw [← X.presheaf.map_comp_apply]
    congr 1

@[simp]
lemma sectionsRestrictionLinear_apply (M : X.Modules) {U V : X.Opens}
    (i : U ⟶ V) (s : Γ(M, V)) :
    sectionsRestrictionLinear M i s = M.presheaf.map i.op s :=
  (rfl)

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- For a scheme over a commutative ring `R`, global functions act on local sections compatibly
with `R`, where `R` acts on functions and on sections over `U` through
`Scheme.baseRingToStructurePresheaf`. -/
lemma isScalarTower_sections (M : X.Modules) (U : X.Opens) :
    letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
    letI : Module R Γ(M, U) :=
      Module.compHom Γ(M, U) ((X.baseRingToStructurePresheaf R).app (op U)).hom
    IsScalarTower R Γ(X, ⊤) Γ(M, U) :=
  letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  letI : Module R Γ(M, U) :=
    Module.compHom Γ(M, U) ((X.baseRingToStructurePresheaf R).app (op U)).hom
  .of_algebraMap_smul fun r x ↦ by
    rw [sectionsGlobal_smul, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
      ← (X.baseRingToStructurePresheaf R).naturality U.leTop.op]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    -- `r` acts on sections through `Module.compHom`, by its image in `Γ(X, U)`.
    rfl

variable {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- The sections of a pushforward over an open have the same base-ring module structure as
the sections on its preimage. -/
def pushforwardSectionsBaseLinearEquiv (M : X.Modules) (U : Y.Opens) :
    letI : Module R Γ((pushforward f).obj M, U) := Module.compHom _
      ((Y.baseRingToStructurePresheaf R).app (op U)).hom
    letI : Module R Γ(M, f ⁻¹ᵁ U) := Module.compHom _
      ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U))).hom
    Γ((pushforward f).obj M, U) ≃ₗ[R] Γ(M, f ⁻¹ᵁ U) := by
  let : Module R Γ((pushforward f).obj M, U) := Module.compHom Γ((pushforward f).obj M, U)
    ((Y.baseRingToStructurePresheaf R).app (op U)).hom
  let : Module R Γ(M, f ⁻¹ᵁ U) := Module.compHom Γ(M, f ⁻¹ᵁ U)
    ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U))).hom
  let : Module Γ(X, f ⁻¹ᵁ U) Γ((pushforward f).obj M, U) :=
    inferInstanceAs (Module Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U))
  exact
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r s := by
        -- Pushforward restricts scalars along `f.app U`; the base-ring actions factor through it.
        change f.app U ((Y.baseRingToStructurePresheaf R).app (op U) r) • (s : Γ(M, f ⁻¹ᵁ U)) =
          (X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U)) r • (s : Γ(M, f ⁻¹ᵁ U))
        rw [app_baseRingToStructurePresheaf] }

-- Normalize the implicit section types before registering simp rules: `pushforward_obj_obj`
-- otherwise rewrites their left-hand sides before the section formulas can apply.
@[simp]
lemma pushforwardSectionsBaseLinearEquiv_apply (M : X.Modules) (U : Y.Opens)
    (s : Γ((pushforward f).obj M, U)) :
    dsimp% only [pushforward_obj_obj] (pushforwardSectionsBaseLinearEquiv R f M U s) = s := by
  rfl

@[simp]
lemma pushforwardSectionsBaseLinearEquiv_symm_apply (M : X.Modules) (U : Y.Opens)
    (s : Γ(M, f ⁻¹ᵁ U)) :
    dsimp% only [pushforward_obj_obj] ((pushforwardSectionsBaseLinearEquiv R f M U).symm s) =
      s := by
  rfl

end

end AlgebraicGeometry.Scheme.Modules
