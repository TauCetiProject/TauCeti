/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Algebra structures induced by a scheme over an affine base

For a scheme `X` over `Spec k`, this file records the canonical `k`-algebra structures on the
function field of an integral `X`, on its stalks, and on its residue fields. It also proves that
the base, stalk, and function-field algebra structures form a scalar tower.

## Main definitions and results

* `Scheme.baseRingToFunctionField`: the canonical map from the base ring to the function field.
* `Scheme.globalRationalFunctionsEquivFunctionField`: global rational functions as a module
  over the base ring.
* `Scheme.baseRingToStalk`: the canonical map from the base ring to a stalk.
* `Scheme.fromSpecStalk_comp_over`: the spectrum of a stalk maps to `X` over the affine base.
* `Scheme.specMap_comp_fromSpecStalk_genericPoint_comp_over`: a `k`-algebra map of function fields
  gives a morphism over the affine base between the spectra of the function fields.
* `Scheme.Hom.functionFieldAlgHom`: conversely, the pullback of rational functions along a dominant
  morphism over the affine base is a `k`-algebra map.
* `Scheme.baseStalkResidueFieldIsScalarTower`: compatibility of the base, stalk, and residue-field
  algebra structures.
* `Scheme.baseStalkFunctionFieldIsScalarTower`: compatibility of the base, stalk, and
  function-field algebra structures.
* `Scheme.residueFieldBaseAlgebra_eq_compHom`: the base-ring algebra structure on a residue field
  is the one used by Mathlib's `Scheme.Hom.residueDegree_eq_finrank`.
-/

public section

open _root_.AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

section CommRing

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The canonical map from the base ring of a scheme to its function field. It is the pullback
to global sections followed by the inclusion of global functions into rational functions. -/
def _root_.AlgebraicGeometry.Scheme.baseRingToFunctionField [IsIntegral X] :
    k →+* X.functionField :=
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  (X.germToFunctionField ⊤).hom.comp (Scheme.Modules.baseRingToGlobalSections k X)

/-- The base-ring map to the function field sends a scalar to the rational function induced by
the corresponding global function. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.baseRingToFunctionField_apply [IsIntegral X] (c : k) :
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    Scheme.baseRingToFunctionField k X c =
      X.germToFunctionField ⊤ (Scheme.Modules.baseRingToGlobalSections k X c) := by
  rfl

/-- The base-ring map to the function field factors through the sections over any nonempty open
`U`: pull functions on `Spec k` back to `Γ(X, U)` along the structure morphism, then pass to
rational functions. -/
lemma _root_.AlgebraicGeometry.Scheme.baseRingToFunctionField_eq_comp_appLE [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Scheme.baseRingToFunctionField k X = (X.germToFunctionField U).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U le_top).hom := by
  have h : (X ↘ Spec (.of k)).appLE ⊤ U le_top ≫ X.germToFunctionField U =
      (X ↘ Spec (.of k)).appTop ≫ X.germToFunctionField ⊤ := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    -- What remains compares germs on `(X ↘ Spec k) ⁻¹ᵁ ⊤` and on `⊤`, which are the same open
    -- by definition; rewriting along `Scheme.Hom.preimage_top` would need to transport the
    -- membership proof inside `germ`.
    rfl
  ext c
  rw [Scheme.baseRingToFunctionField_apply, Scheme.Modules.baseRingToGlobalSections_apply]
  exact congr($h ((Scheme.ΓSpecIso (.of k)).inv c)).symm

/-- The function field of an integral scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.functionFieldBaseAlgebra
    [IsIntegral X] : Algebra k X.functionField :=
  (Scheme.baseRingToFunctionField k X).toAlgebra

/-- The canonical map from the base ring of a scheme to its stalk at `x`. -/
def _root_.AlgebraicGeometry.Scheme.baseRingToStalk (x : X) : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (Scheme.Modules.baseRingToGlobalSections k X)

/-- The image of a base-ring element in a stalk is the germ of the corresponding global
function. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.baseRingToStalk_apply (x : X) (c : k) :
    Scheme.baseRingToStalk k X x c =
      X.presheaf.germ ⊤ x trivial (Scheme.Modules.baseRingToGlobalSections k X c) :=
  by simp only [Scheme.baseRingToStalk, RingHom.comp_apply]

/-- Every stalk of a scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.stalkBaseAlgebra (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  (Scheme.baseRingToStalk k X x).toAlgebra

/-- The residue field at a point of a scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.residueFieldBaseAlgebra (x : X) :
    Algebra k (X.residueField x) :=
  ((X.residue x).hom.comp (Scheme.baseRingToStalk k X x)).toAlgebra

/-- The residue field at a point is canonically an algebra over its stalk. -/
instance _root_.AlgebraicGeometry.Scheme.residueFieldStalkAlgebra (x : X) :
    Algebra (X.presheaf.stalk x) (X.residueField x) :=
  (X.residue x).hom.toAlgebra

/-- The algebra map to the function field is the canonical composite from the base ring. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.algebraMap_functionField_eq_baseRingToFunctionField
    [IsIntegral X] : algebraMap k X.functionField = Scheme.baseRingToFunctionField k X :=
  rfl

/-- The algebra map to a stalk is the canonical composite from the base ring. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.algebraMap_stalk_eq_baseRingToStalk (x : X) :
    algebraMap k (X.presheaf.stalk x) = Scheme.baseRingToStalk k X x :=
  rfl

/-- The algebra map to a residue field is the residue of the canonical composite from the base
ring. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk
    (x : X) :
    algebraMap k (X.residueField x) = (X.residue x).hom.comp (Scheme.baseRingToStalk k X x) :=
  rfl

/-- The algebra map from a stalk to its residue field is the residue map. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.algebraMap_stalk_residueField_eq_residue (x : X) :
    algebraMap (X.presheaf.stalk x) (X.residueField x) = (X.residue x).hom :=
  rfl

/-- The canonical maps from the base ring through a stalk to its residue field form a scalar
tower. -/
instance _root_.AlgebraicGeometry.Scheme.baseStalkResidueFieldIsScalarTower (x : X) :
    IsScalarTower k (X.presheaf.stalk x) (X.residueField x) := by
  apply IsScalarTower.of_algebraMap_eq'
  rw [Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk,
    Scheme.algebraMap_stalk_residueField_eq_residue,
    Scheme.algebraMap_stalk_eq_baseRingToStalk]

/-- The residue at `x` of the image of a base ring element in the stalk is the evaluation at `x`
of the corresponding global function: both are the germ at `x` followed by the residue map. -/
lemma _root_.AlgebraicGeometry.Scheme.residue_baseRingToStalk (x : X) (c : k) :
    X.residue x (Scheme.baseRingToStalk k X x c) =
      X.Γevaluation x (Scheme.Modules.baseRingToGlobalSections k X c) := by
  have h : X.presheaf.germ ⊤ x trivial ≫ X.residue x = X.Γevaluation x :=
    X.germ_residue (U := ⊤) x trivial
  simp only [Scheme.baseRingToStalk, RingHom.comp_apply, ← CommRingCat.comp_apply, h]

/-- The base-ring algebra structure on a residue field evaluates at `x` the pullback of a
function on `Spec k` along the structure morphism. This is the algebra structure in Mathlib's
`Scheme.Hom.residueDegree_eq_finrank`, so over a field `finrank k κ(x)` is the residue degree of
the structure morphism at `x`. -/
lemma _root_.AlgebraicGeometry.Scheme.residueFieldBaseAlgebra_eq_compHom (x : X) :
    Scheme.residueFieldBaseAlgebra k X x = Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom) := by
  refine Algebra.algebra_ext _ _ fun c ↦ ?_
  rw [Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk,
    Algebra.compHom_algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.comp_apply, Scheme.residue_baseRingToStalk,
    Scheme.Modules.baseRingToGlobalSections_apply, RingHom.comp_apply, CommRingCat.hom_comp,
    RingHom.comp_apply]

/-- The canonical maps from the base ring through a stalk to the function field form a scalar
tower. -/
instance _root_.AlgebraicGeometry.Scheme.baseStalkFunctionFieldIsScalarTower [IsIntegral X]
    (x : X) : IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq'
  rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField,
    Scheme.algebraMap_stalk_eq_baseRingToStalk]
  ext c
  simp only [Scheme.baseRingToFunctionField, Scheme.baseRingToStalk, RingHom.comp_apply]
  exact (X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) trivial _).symm

/-- The canonical morphism from the spectrum of a stalk to a scheme over `Spec k` is a morphism
over `Spec k`; on rings, its composite with the structure morphism is the algebra map from `k`
to the stalk. -/
theorem _root_.AlgebraicGeometry.Scheme.fromSpecStalk_comp_over (x : X) :
    X.fromSpecStalk x ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x))) := by
  have hbase : X ↘ Spec (.of k) = X.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (Scheme.Modules.baseRingToGlobalSections k X)) := by
    have hring : CommRingCat.ofHom (Scheme.Modules.baseRingToGlobalSections k X) =
        (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop := by
      ext c
      exact Scheme.Modules.baseRingToGlobalSections_apply k X c
    rw [hring, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  rw [hbase, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, Spec.map_inj,
    Scheme.algebraMap_stalk_eq_baseRingToStalk, Scheme.baseRingToStalk,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]

/-- At the generic point of an integral scheme, `fromSpecStalk` is a morphism from the spectrum
of the function field over the affine base. -/
theorem _root_.AlgebraicGeometry.Scheme.fromSpecStalk_genericPoint_comp_over [IsIntegral X] :
    X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  -- Both base-ring maps are the global-sections map followed by a germ at the generic point:
  -- `Scheme.germToFunctionField ⊤` is by definition that germ.
  rw [X.fromSpecStalk_comp_over (k := k), Spec.map_inj,
    Scheme.algebraMap_stalk_eq_baseRingToStalk,
    Scheme.algebraMap_functionField_eq_baseRingToFunctionField, Scheme.baseRingToStalk,
    Scheme.baseRingToFunctionField]

/-- Through the generic points of integral schemes over `Spec k`, `Spec` of a map of function
fields compatible with the `k`-algebra structures is compatible with the structure morphisms to
`Spec k`. -/
theorem _root_.AlgebraicGeometry.Scheme.specMap_comp_fromSpecStalk_genericPoint_comp_over
    {Y Z : Scheme.{u}} [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [IsIntegral Y]
    [IsIntegral Z] (f : Z.functionField ⟶ Y.functionField)
    (hf : ∀ c : k, f (algebraMap k Z.functionField c) = algebraMap k Y.functionField c) :
    (Spec.map f ≫ Z.fromSpecStalk _) ≫ Z ↘ Spec (.of k) =
      Y.fromSpecStalk _ ≫ Y ↘ Spec (.of k) := by
  rw [Category.assoc, Scheme.fromSpecStalk_genericPoint_comp_over,
    Scheme.fromSpecStalk_genericPoint_comp_over, ← Spec.map_comp]
  congr 1
  ext c
  exact hf c

/-- **The pullback of rational functions along a morphism over `Spec k` is `k`-linear**: for a
dominant morphism `f : Y ⟶ Z` of integral schemes over `Spec k`, the pullback `f^*` fixes the
image of `k` in the function fields. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.functionFieldMap_algebraMap {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [IsDominant f] (c : k) :
    f.functionFieldMap (algebraMap k Z.functionField c) = algebraMap k Y.functionField c := by
  have h : CommRingCat.ofHom (algebraMap k Z.functionField) ≫ f.functionFieldMap =
      CommRingCat.ofHom (algebraMap k Y.functionField) := by
    rw [← Spec.map_inj, Spec.map_comp, ← Scheme.fromSpecStalk_genericPoint_comp_over k Z,
      f.SpecMap_functionFieldMap_fromSpecStalk_assoc, comp_over,
      Scheme.fromSpecStalk_genericPoint_comp_over k Y]
  exact congr($h c)

/-- The pullback of rational functions `f^* : k(Z) → k(Y)` along a dominant morphism `f : Y ⟶ Z`
of integral schemes over `Spec k`, as a `k`-algebra homomorphism. -/
def _root_.AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [IsDominant f] : Z.functionField →ₐ[k] Y.functionField where
  toRingHom := f.functionFieldMap.hom
  commutes' := f.functionFieldMap_algebraMap k

/-- The `k`-algebra homomorphism `Scheme.Hom.functionFieldAlgHom` is the pullback of rational
functions. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom_apply {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [IsDominant f] (z : Z.functionField) :
    f.functionFieldAlgHom k z = f.functionFieldMap z :=
  (rfl)

/-- The ring homomorphism underlying `Scheme.Hom.functionFieldAlgHom` is the pullback of rational
functions. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.coe_functionFieldAlgHom {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [IsDominant f] :
    (f.functionFieldAlgHom k : Z.functionField →+* Y.functionField) = f.functionFieldMap.hom :=
  (rfl)

/-- The pullback of rational functions along the identity is the identity `k`-algebra map. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom_id {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [IsIntegral Y] :
    Scheme.Hom.functionFieldAlgHom k (𝟙 Y) = AlgHom.id k Y.functionField :=
  AlgHom.ext fun _ ↦ by simp

/-- The pullback of rational functions along a composite of dominant morphisms over `Spec k` is
the composite of the pullbacks, in the opposite order. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom_comp {Y Z W : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [W.Over (Spec (.of k))] [IsIntegral Y]
    [IsIntegral Z] [IsIntegral W] (f : Y ⟶ Z) (g : Z ⟶ W) [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))] [IsDominant f] [IsDominant g] :
    Scheme.Hom.functionFieldAlgHom k (f ≫ g) =
      (f.functionFieldAlgHom k).comp (g.functionFieldAlgHom k) :=
  AlgHom.ext fun _ ↦ by simp

end CommRing

section RationalFunctions

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X]

/-- Global rational functions are the function field, also as modules over the base ring. -/
def _root_.AlgebraicGeometry.Scheme.globalRationalFunctionsEquivFunctionField :
    Γ(Scheme.rationalFunctions X, ⊤) ≃ₗ[k] X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  exact {
    toFun := Scheme.rationalFunctionsEquiv ⊤
    invFun := (Scheme.rationalFunctionsEquiv ⊤).symm
    left_inv := (Scheme.rationalFunctionsEquiv ⊤).left_inv
    right_inv := (Scheme.rationalFunctionsEquiv ⊤).right_inv
    map_add' := (Scheme.rationalFunctionsEquiv ⊤).map_add
    map_smul' c f := by
      rw [Scheme.Modules.base_smul_globalSections,
        (Scheme.rationalFunctionsEquiv ⊤).map_smul]
      -- The scalar action through global functions is the germ in the function field.
      change X.germToFunctionField ⊤ (Scheme.Modules.baseRingToGlobalSections k X c) *
          Scheme.rationalFunctionsEquiv ⊤ f =
        algebraMap k X.functionField c * Scheme.rationalFunctionsEquiv ⊤ f
      rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField]
      rw [Scheme.baseRingToFunctionField_apply]
  }

/-- The linear equivalence sends a global rational function to its value in the function field. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.globalRationalFunctionsEquivFunctionField_apply
    (f : Γ(Scheme.rationalFunctions X, ⊤)) :
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    Scheme.globalRationalFunctionsEquivFunctionField (k := k) (X := X) f =
      Scheme.rationalFunctionsEquiv ⊤ f := by
  rfl

end RationalFunctions

end

end AlgebraicGeometry

end TauCeti
