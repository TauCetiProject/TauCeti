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

/-- The unique volume basis vector of the one-vertex zigzag algebra. -/
noncomputable def zigzagA1Volume : zigzagAlgebra k (⊥ : SimpleGraph (Fin 1)) :=
  (zigzagAlgebraEquivA1 k).symm ε

/-- Under the comparison with the dual numbers, the `A₁` volume is `ε`. -/
theorem zigzagAlgebraEquivA1_zigzagA1Volume :
    zigzagAlgebraEquivA1 k (zigzagA1Volume k) = ε :=
  (zigzagAlgebraEquivA1 k).apply_symm_apply ε

/-- The element transported from `ε` is the volume vector in the standard zigzag basis. -/
theorem zigzagA1Volume_eq_basis :
    zigzagA1Volume k =
      zigzagAlgebraBasis k (⊥ : SimpleGraph (Fin 1)) (.inr (.inr 0)) := by
  apply (zigzagAlgebraEquivA1 k).injective
  rw [zigzagAlgebraEquivA1_zigzagA1Volume, zigzagAlgebraEquivA1_apply]
  have h : zigzagComponentProjection k (⊥ : SimpleGraph (Fin 1)) default
      (zigzagAlgebraBasis k (⊥ : SimpleGraph (Fin 1)) (.inr (.inr 0))) =
        zigzagComponentBasis k (⊥ : SimpleGraph (Fin 1)) default
          (.inr (.inr ⟨0, rfl⟩)) := by
    simpa only [zigzagComponentBasisIndexEquiv_inr_inr] using
      (zigzagComponentProjection_zigzagAlgebraBasis
        (G := (⊥ : SimpleGraph (Fin 1))) (k := k) default (.inr (.inr ⟨0, rfl⟩)))
  rw [h, zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr]

/-- The regular dual-number module, restricted to the one-vertex zigzag algebra, is the
regular zigzag module. -/
@[expose]
noncomputable def zigzagA1FreeIso :
    (zigzagA1Restriction k).obj (dualNumberFree k) ≅ zigzagA1Free k :=
  ModuleCat.restrictScalarsIsoOfEquiv (zigzagAlgebraEquivA1 k).toRingEquiv

/-- The forward map in `TauCeti.zigzagA1FreeIso` applies the inverse algebra comparison. -/
@[simp]
theorem zigzagA1FreeIso_hom_apply (x : DualNumber k) :
    (zigzagA1FreeIso k).hom.hom x =
      (zigzagAlgebraEquivA1 k).toRingEquiv.symm x :=
  rfl

/-- Right multiplication by the volume element on the regular one-vertex zigzag module. -/
@[expose]
noncomputable def zigzagA1VolumeMul : zigzagA1Free k ⟶ zigzagA1Free k :=
  ModuleCat.ofHom
    (LinearMap.mulRight (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) (zigzagA1Volume k))

/-- The volume endomorphism acts by right multiplication. -/
@[simp]
theorem zigzagA1VolumeMul_apply (x : zigzagA1Free k) :
    (zigzagA1VolumeMul k).hom x = x * zigzagA1Volume k :=
  rfl

/-- Transporting multiplication by `ε` gives multiplication by the `A₁` volume. -/
@[reassoc]
theorem zigzagA1FreeIso_naturality :
    (zigzagA1Restriction k).map (dualNumberEpsSmul k) ≫ (zigzagA1FreeIso k).hom =
      (zigzagA1FreeIso k).hom ≫ zigzagA1VolumeMul k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let y : DualNumber k := x
  change (zigzagAlgebraEquivA1 k).toRingEquiv.symm
      ((dualNumberEpsSmul k).hom y) =
    (zigzagA1VolumeMul k).hom
      ((zigzagAlgebraEquivA1 k).toRingEquiv.symm y)
  rw [dualNumberEpsSmul_hom, LinearMap.mulLeft_apply, zigzagA1VolumeMul_apply]
  apply (zigzagAlgebraEquivA1 k).injective
  simp [zigzagA1Volume, mul_comm]

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
  change (zigzagA1Restriction k).map
      ((dualNumberProjectiveResolution k).complex.d (n + 1) n) =
    ((zigzagA1Restriction k).mapIso
          (dualNumberProjectiveResolutionXIso k (n + 1))).hom ≫
      (zigzagA1FreeIso k).hom ≫ zigzagA1VolumeMul k ≫
        (zigzagA1FreeIso k).inv ≫
          ((zigzagA1Restriction k).mapIso
            (dualNumberProjectiveResolutionXIso k n)).inv
  rw [dualNumberProjectiveResolution_complex_d, Functor.map_comp, Functor.map_comp]
  simp only [Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← zigzagA1FreeIso_naturality_assoc]
  simp

end TauCeti
