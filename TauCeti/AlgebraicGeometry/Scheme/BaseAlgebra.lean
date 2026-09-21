/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.ResidueDegree
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Algebra structures induced by a scheme over an affine base

For a scheme `X` over `Spec k`, this file records the canonical `k`-algebra structures on the
function field of an integral `X`, on its stalks, and on its residue fields. It also proves that
the base, stalk, and function-field algebra structures form a scalar tower.

## Main definitions and results

* `Scheme.baseRingToFunctionField`: the canonical map from the base ring to the function field.
* `Scheme.baseRingToStalk`: the canonical map from the base ring to a stalk.
* `Scheme.baseStalkFunctionFieldIsScalarTower`: compatibility of the base, stalk, and
  function-field algebra structures.
* `Scheme.finrank_residueField_eq_residueDegree`: over a field, the dimension of a residue field
  is the residue degree of the structure morphism.
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

/-- The function field of an integral scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.functionFieldBaseAlgebra
    [IsIntegral X] : Algebra k X.functionField :=
  (Scheme.baseRingToFunctionField k X).toAlgebra

/-- The canonical map from the base ring of a scheme to its stalk at `x`. -/
def _root_.AlgebraicGeometry.Scheme.baseRingToStalk (x : X) : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (Scheme.Modules.baseRingToGlobalSections k X)

/-- Every stalk of a scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.stalkBaseAlgebra (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  (Scheme.baseRingToStalk k X x).toAlgebra

/-- The residue field at a point of a scheme over `Spec k` is canonically a `k`-algebra. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.residueFieldBaseAlgebra (x : X) :
    Algebra k (X.residueField x) :=
  ((X.residue x).hom.comp (Scheme.baseRingToStalk k X x)).toAlgebra

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

/-- The residue at `x` of the image of a base ring element in the stalk is the evaluation at `x`
of the corresponding global function: both are the germ at `x` followed by the residue map. -/
lemma _root_.AlgebraicGeometry.Scheme.residue_baseRingToStalk (x : X) (c : k) :
    X.residue x (Scheme.baseRingToStalk k X x c) =
      X.Γevaluation x (Scheme.Modules.baseRingToGlobalSections k X c) := by
  have h : X.presheaf.germ ⊤ x trivial ≫ X.residue x = X.Γevaluation x :=
    X.germ_residue (U := ⊤) x trivial
  simp only [Scheme.baseRingToStalk, RingHom.comp_apply, ← CommRingCat.comp_apply, h]

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

end CommRing

section Field

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- Over a field, the dimension of a scheme-theoretic residue field is the residue degree of the
structure morphism. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.finrank_residueField_eq_residueDegree (x : X) :
    Module.finrank k (X.residueField x) = (X ↘ Spec (.of k)).residueDegree x := by
  let f := X ↘ Spec (.of k)
  let _ : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [Scheme.Hom.residueDegree]
  let e : k ≃+* (Spec (.of k)).residueField (f x) := RingEquiv.ofBijective
    (((Spec (.of k)).Γevaluation (f x)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    (TauCeti.AlgebraicGeometry.Γevaluation_comp_ΓSpecIso_inv_bijective k (f x))
  refine Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl (X.residueField x)) ?_
  ext c
  simp only [RingHom.algebraMap_toAlgebra, e, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.ofBijective_apply, RingHom.comp_apply,
    RingEquiv.refl_apply]
  rw [Scheme.Γevaluation_naturality_apply, Scheme.residue_baseRingToStalk,
    Scheme.Modules.baseRingToGlobalSections_apply]

end Field

end

end AlgebraicGeometry

end TauCeti
