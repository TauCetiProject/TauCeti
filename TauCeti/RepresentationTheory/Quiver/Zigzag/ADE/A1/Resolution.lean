/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.DualNumbers
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.A1.Basic

/-!
# The periodic resolution for the one-vertex zigzag algebra

The zigzag algebra of the one-vertex graph is the dual numbers.  Transporting the standard
periodic resolution along this algebra equivalence gives an explicit projective resolution of
its residue module:

```text
⋯ ⟶ Z(A₁) --v₀--> Z(A₁) --v₀--> Z(A₁) ⟶ k ⟶ 0.
```

Here `v₀` is the unique volume basis vector.  This file records both the transported
resolution and its intrinsic description in terms of the regular zigzag module and
multiplication by `v₀`.

## Main definitions

* `TauCeti.zigzagA1Residue`: the residue module of the one-vertex zigzag algebra.
* `TauCeti.zigzagA1Proj`: the quotient map from the regular module onto the residue module.
* `TauCeti.zigzagA1ProjectiveResolution`: its periodic projective resolution.
* `TauCeti.zigzagA1ProjectiveResolutionXIso`: the identification of every term with the
  regular module.

## References

* Ruth Stella Huerfano and Mikhail Khovanov, *A category for the adjoint representation*,
  Journal of Algebra 246 (2001), Section 3.
-/

open CategoryTheory DualNumber

open scoped ModuleCat.Algebra

public section

namespace TauCeti

universe u

variable (k : Type u) [CommRing k]

/-- Restriction of scalars from the dual numbers to the one-vertex zigzag algebra. -/
noncomputable abbrev zigzagA1Restriction :
    ModuleCat.{u} (DualNumber k) ⥤
      ModuleCat.{u} (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) :=
  ModuleCat.restrictScalars (zigzagAlgebraEquivA1 k).toRingEquiv.toRingHom

/-! ### The regular and residue modules -/

/-- The regular module of the one-vertex zigzag algebra. -/
noncomputable abbrev zigzagA1Free :
    ModuleCat.{u} (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) :=
  ModuleCat.of _ (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1)))

/-- The residue module of the one-vertex zigzag algebra, obtained from
`k[ε]/(ε)` by change of rings along `TauCeti.zigzagAlgebraEquivA1`. -/
noncomputable abbrev zigzagA1Residue :
    ModuleCat.{u} (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) :=
  (zigzagA1Restriction k).obj (dualNumberResidue k)

/-- The regular dual-number module, restricted to the one-vertex zigzag algebra, is the
regular zigzag module. -/
noncomputable def zigzagA1FreeIso :
    (zigzagA1Restriction k).obj (dualNumberFree k) ≅ zigzagA1Free k :=
  ModuleCat.restrictScalarsIsoOfEquiv (zigzagAlgebraEquivA1 k).toRingEquiv

/-- Right multiplication by the volume element on the regular one-vertex zigzag module. -/
noncomputable def zigzagA1VolumeMul : zigzagA1Free k ⟶ zigzagA1Free k :=
  ModuleCat.ofHom
    (LinearMap.mulRight (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) (zigzagA1Volume k))

/-- The volume endomorphism acts by right multiplication. -/
@[simp]
theorem zigzagA1VolumeMul_apply (x : zigzagA1Free k) :
    (zigzagA1VolumeMul k).hom x = x * zigzagA1Volume k :=
  (rfl)

/-- Transporting multiplication by `ε` gives multiplication by the `A₁` volume. -/
@[reassoc]
theorem zigzagA1FreeIso_naturality :
    (zigzagA1Restriction k).map (dualNumberEpsSmul k) ≫ (zigzagA1FreeIso k).hom =
      (zigzagA1FreeIso k).hom ≫ zigzagA1VolumeMul k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let y : DualNumber k := x
  -- Definitionally, `zigzagA1FreeIso` is `ModuleCat.restrictScalarsIsoOfEquiv`, whose forward
  -- map is the inverse algebra equivalence on elements, and `zigzagA1Restriction` leaves the
  -- underlying map of `dualNumberEpsSmul` unchanged. The Mathlib lemma
  -- `ModuleCat.restrictScalarsIsoOfEquiv_hom_apply` does not rewrite here: it is stated through
  -- `ConcreteCategory.hom` on `DualNumber k`, while `x` lives in the restricted carrier. So we
  -- state the unfolded goal on `y` instead.
  change (zigzagAlgebraEquivA1 k).toRingEquiv.symm
      ((dualNumberEpsSmul k).hom y) =
    (zigzagA1VolumeMul k).hom
      ((zigzagAlgebraEquivA1 k).toRingEquiv.symm y)
  rw [dualNumberEpsSmul_hom, LinearMap.mulLeft_apply, zigzagA1VolumeMul_apply]
  apply (zigzagAlgebraEquivA1 k).injective
  simp [-zigzagAlgebraEquivA1_apply, mul_comm]

/-- The quotient map from the regular one-vertex zigzag module onto its residue module,
transported from `TauCeti.dualNumberProj`. -/
noncomputable def zigzagA1Proj : zigzagA1Free k ⟶ zigzagA1Residue k :=
  (zigzagA1FreeIso k).inv ≫ (zigzagA1Restriction k).map (dualNumberProj k)

/-- The quotient map takes the constant term under the comparison with the dual numbers. -/
@[simp]
theorem zigzagA1Proj_apply (x : zigzagA1Free k) :
    (zigzagA1Proj k).hom x = TrivSqZeroExt.fst (zigzagAlgebraEquivA1 k x) := by
  rw [zigzagA1Proj, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.restrictScalars.map_apply,
    zigzagA1FreeIso, ← dualNumberProj_apply k (zigzagAlgebraEquivA1 k x)]
  exact congrArg (dualNumberProj k) (ModuleCat.restrictScalarsIsoOfEquiv_inv_apply _ x)

/-! ### The periodic resolution -/

/-- The periodic projective resolution of the residue module of the one-vertex zigzag algebra,
obtained by transporting the dual-number resolution across the algebra equivalence. -/
noncomputable def zigzagA1ProjectiveResolution : ProjectiveResolution (zigzagA1Residue k) :=
  (zigzagA1Restriction k).mapProjectiveResolution (dualNumberProjectiveResolution k)

/-- Every term of the transported resolution is the regular one-vertex zigzag module. -/
noncomputable def zigzagA1ProjectiveResolutionXIso (n : ℕ) :
    (zigzagA1ProjectiveResolution k).complex.X n ≅ zigzagA1Free k :=
  (zigzagA1Restriction k).mapIso (dualNumberProjectiveResolutionXIso k n) ≪≫
    zigzagA1FreeIso k

/-- Every differential in the transported resolution is multiplication by the unique volume
basis vector. -/
@[simp]
theorem zigzagA1ProjectiveResolution_complex_d (n : ℕ) :
    (zigzagA1ProjectiveResolution k).complex.d (n + 1) n =
      (zigzagA1ProjectiveResolutionXIso k (n + 1)).hom ≫ zigzagA1VolumeMul k ≫
        (zigzagA1ProjectiveResolutionXIso k n).inv := by
  dsimp only [zigzagA1ProjectiveResolution, Functor.mapProjectiveResolution,
    Functor.mapHomologicalComplex_obj_d, zigzagA1ProjectiveResolutionXIso, Iso.trans_hom,
    Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [dualNumberProjectiveResolution_complex_d, Functor.map_comp, Functor.map_comp,
    Category.assoc, ← zigzagA1FreeIso_naturality_assoc]
  simp

/-- The augmentation of the transported resolution is `TauCeti.zigzagA1Proj`, read through
`TauCeti.zigzagA1ProjectiveResolutionXIso`. -/
@[simp]
theorem zigzagA1ProjectiveResolution_π_f_zero :
    (zigzagA1ProjectiveResolutionXIso k 0).inv ≫ (zigzagA1ProjectiveResolution k).π.f 0 =
      zigzagA1Proj k := by
  dsimp only [zigzagA1ProjectiveResolution, Functor.mapProjectiveResolution,
    zigzagA1ProjectiveResolutionXIso, Iso.trans_inv, Functor.mapIso_inv]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  rw [← Functor.map_comp_assoc, dualNumberProjectiveResolution_π_f_zero]
  simp [zigzagA1Proj]

end TauCeti
